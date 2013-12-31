/*******************************************************************************
 * Copyright (c) 2012 Secure Software Engineering Group at EC SPRIDE.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors: Christian Fritz, Steven Arzt, Siegfried Rasthofer, Eric
 * Bodden, and others.
 ******************************************************************************/
package soot.jimple.infoflow.entryPointCreators;

import java.util.*;
import java.util.Map.Entry;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.IntType;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.javaToJimple.LocalGenerator;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.NopStmt;
import soot.jimple.Stmt;
import soot.jimple.infoflow.data.SootMethodAndClass;
import soot.jimple.infoflow.util.SootMethodRepresentationParser;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JNopStmt;
import soot.jimple.toolkits.scalar.NopEliminator;
import soot.options.Options;

/**
 * class which creates a dummy main method with the entry points according to the Android lifecycles
 * 
 * based on: http://developer.android.com/reference/android/app/Activity.html#ActivityLifecycle
 * and http://developer.android.com/reference/android/app/Service.html
 * and http://developer.android.com/reference/android/content/BroadcastReceiver.html#ReceiverLifecycle
 * and http://developer.android.com/reference/android/content/BroadcastReceiver.html
 * 
 * @author Christian, Steven Arzt
 * 
 */
public class AndroidEntryPointCreator extends BaseEntryPointCreator implements IEntryPointCreator{

    private final Logger logger = LoggerFactory.getLogger(getClass());

	private static final boolean DEBUG = false;
	
	private JimpleBody body;
	private LocalGenerator generator;
	private int conditionCounter;
	private Value intCounter;
	
	private SootClass applicationClass = null;
	private Local applicationLocal = null;
	private Set<SootClass> applicationCallbackClasses = new HashSet<SootClass>();
	
	private List<String> androidClasses;
	private Map<String, List<String>> callbackFunctions;
	private boolean modelAdditionalMethods = false;
	
	/**
	 * Array containing all types of components supported in Android lifecycles
	 */
	private enum ComponentType {
		Application,
		Activity,
		Service,
		BroadcastReceiver,
		ContentProvider,
		Plain
	}
	
	/**
	 * Creates a new instance of the {@link AndroidEntryPointCreator} class.
	 */
	public AndroidEntryPointCreator() {
		this.androidClasses = new ArrayList<String>();
		this.callbackFunctions = new HashMap<String, List<String>>();
	}
	
	/**
	 * Creates a new instance of the {@link AndroidEntryPointCreator} class
	 * and registers a list of classes to be automatically scanned for Android
	 * lifecycle methods
	 * @param androidClasses The list of classes to be automatically scanned for
	 * Android lifecycle methods
	 */
	public AndroidEntryPointCreator(List<String> androidClasses) {
		this.androidClasses = androidClasses;
		this.callbackFunctions = new HashMap<String, List<String>>();
	}
	
	/**
	 * Sets the list of callback functions to be integrated into the Android
	 * lifecycle
	 * @param callbackFunctions The list of callback functions to be integrated
	 * into the Android lifecycle. This is a mapping from the Android element
	 * class (activity, service, etc.) to the list of callback methods for that
	 * element.
	 */
	public void setCallbackFunctions(Map<String, List<String>> callbackFunctions) {
		this.callbackFunctions = callbackFunctions;
	}
	
	/**
	 * Returns the list of callback functions of the Android lifecycle. 
	 * @return callbackFunctions The list of callback functions of the Android lifecycle. 
	 * This is a mapping from the Android element class (activity, service, etc.) to the list 
	 * of callback methods for that element.
	 */
	public Map<String, List<String>> getCallbackFunctions() {
		return callbackFunctions;
	}

	/**
	 * Creates a new dummy main method based only on the Android classes and
	 * the automatic detection of the Android lifecycle methods
	 * @return The generated dummy main method
	 */
	public SootMethod createDummyMain() {
		return createDummyMain(new ArrayList<String>());
	}

	/**
	 *  Soot requires a main method, so we create a dummy method which calls all entry functions. 
	 *  Android's components are detected and treated according to their lifecycles. This
	 *  method automatically resolves the classes containing the given methods.
	 *  
	 * @param methods The list of methods to be called inside the generated dummy main method.
	 * @return the dummyMethod which was created
	 */
	@Override
	protected SootMethod createDummyMainInternal(List<String> methods){
		Map<String, List<String>> classMap =
				SootMethodRepresentationParser.v().parseClassNames(methods, false);
		for (String androidClass : this.androidClasses)
			if (!classMap.containsKey(androidClass))
				classMap.put(androidClass, new ArrayList<String>());
		
		// create new class:
 		body = Jimple.v().newBody();
 		
 		SootMethod mainMethod = createEmptyMainMethod(body);
		
		generator = new LocalGenerator(body);
		
		// add entrypoint calls
		conditionCounter = 0;
		intCounter = generator.generateLocal(IntType.v());

		JAssignStmt assignStmt = new JAssignStmt(intCounter, IntConstant.v(conditionCounter));
		body.getUnits().add(assignStmt);

		// Resolve all requested classes
		for (Entry<String, List<String>> entry : classMap.entrySet())
			Scene.v().forceResolve(entry.getKey(), SootClass.BODIES);
		
		// For some weird reason unknown to anyone except the flying spaghetti
		// monster, the onCreate() methods of content providers run even before
		// the application object's onCreate() is called.
		{
			boolean hasContentProviders = false;
			JNopStmt beforeContentProvidersStmt = new JNopStmt();
			body.getUnits().add(beforeContentProvidersStmt);
			for(String className : classMap.keySet()) {
				SootClass currentClass = Scene.v().getSootClass(className);
				if (getComponentType(currentClass) == ComponentType.ContentProvider) {
					// Create an instance of the content provider
					Local localVal = generateClassConstructor(currentClass, body);
					if (localVal == null) {
						logger.warn("Constructor cannot be generated for {}", currentClass.getName());
						continue;
					}
					localVarsForClasses.put(currentClass.getName(), localVal);
					
					// Conditionally call the onCreate method
					JNopStmt thenStmt = new JNopStmt();
					createIfStmt(thenStmt);
					buildMethodCall(findMethod(currentClass, AndroidEntryPointConstants.CONTENTPROVIDER_ONCREATE),
							body, localVal, generator);
					body.getUnits().add(thenStmt);
					hasContentProviders = true;
				}
			}
			// Jump back to the beginning of this section to overapproximate the
			// order in which the methods are called
			if (hasContentProviders)
				createIfStmt(beforeContentProvidersStmt);
		}
		
		// If we have an application, we need to start it in the very beginning
		for (Entry<String, List<String>> entry : classMap.entrySet()) {
			SootClass currentClass = Scene.v().getSootClass(entry.getKey());
			Collection<SootClass> extendedClasses = Scene.v().getActiveHierarchy().getSuperclassesOf(currentClass);
			for(SootClass sc : extendedClasses)
				if(sc.getName().equals(AndroidEntryPointConstants.APPLICATIONCLASS)) {
					if (applicationClass != null)
						throw new RuntimeException("Multiple application classes in app");
					applicationClass = currentClass;
					applicationCallbackClasses.add(applicationClass);
					
					// Create the application
					applicationLocal = generateClassConstructor(applicationClass, body);
					if (applicationLocal == null) {
						logger.warn("Constructor cannot be generated for application class {}", applicationClass.getName());
						continue;
					}
					localVarsForClasses.put(applicationClass.getName(), applicationLocal);
					
					// Create instances of all application callback classes
					if (callbackFunctions.containsKey(applicationClass.getName())) {
						NopStmt beforeCbCons = new JNopStmt();
						body.getUnits().add(beforeCbCons);
						for (String appCallback : callbackFunctions.get(applicationClass.getName())) {
							JNopStmt thenStmt = new JNopStmt();
							createIfStmt(thenStmt);

							String callbackClass = SootMethodRepresentationParser.v().parseSootMethodString
									(appCallback).getClassName();
							Local l = localVarsForClasses.get(callbackClass);
							if (l == null) {
								SootClass theClass = Scene.v().getSootClass(callbackClass);
								applicationCallbackClasses.add(theClass);
								l = generateClassConstructor(theClass, body,
										Collections.singleton(applicationClass));
								if (l != null)
									localVarsForClasses.put(callbackClass, l);
							}
							
							body.getUnits().add(thenStmt);
						}
						// Jump back to overapproximate the order in which the
						// constructors are called 
						createIfStmt(beforeCbCons);
					}
					
					// Call the onCreate() method
					searchAndBuildMethod(AndroidEntryPointConstants.APPLICATION_ONCREATE,
							applicationClass, entry.getValue(), applicationLocal);
					break;
				}
		}
		
		//prepare outer loop:
		JNopStmt outerStartStmt = new JNopStmt();
		body.getUnits().add(outerStartStmt);
		
		for(Entry<String, List<String>> entry : classMap.entrySet()){
			//no execution order given for all apps:
//			JNopStmt entryExitStmt = new JNopStmt();
//			createIfStmt(entryExitStmt);
			
			SootClass currentClass = Scene.v().getSootClass(entry.getKey());
			currentClass.setApplicationClass();
			JNopStmt endClassStmt = new JNopStmt();

			try {
				ComponentType componentType = getComponentType(currentClass);
		
				// Check if one of the methods is instance. This tells us whether
				// we need to create a constructor invocation or not. Furthermore,
				// we collect references to the corresponding SootMethod objects.
				boolean instanceNeeded = componentType == ComponentType.Activity
						|| componentType == ComponentType.Service
						|| componentType == ComponentType.BroadcastReceiver
						|| componentType == ComponentType.ContentProvider;
				Map<String, SootMethod> plainMethods = new HashMap<String, SootMethod>();
				if (!instanceNeeded)
					for(String method : entry.getValue()){
						SootMethod sm = null;
						
						// Find the method. It may either be implemented directly in the
						// given class or it may be inherited from one of the superclasses.
						if(Scene.v().containsMethod(method))
							sm = Scene.v().getMethod(method);
						else {
							SootMethodAndClass methodAndClass = SootMethodRepresentationParser.v().parseSootMethodString(method);
							if (!Scene.v().containsClass(methodAndClass.getClassName())) {
								logger.warn("Class for entry point {} not found, skipping...", method);
								continue;
							}
							sm = findMethod(Scene.v().getSootClass(methodAndClass.getClassName()),
									methodAndClass.getSubSignature());
							if (sm == null) {
								logger.warn("Method for entry point {} not found in class, skipping...", method);
								continue;
							}
						}
	
						plainMethods.put(method, sm);
						if(!sm.isStatic())
							instanceNeeded = true;
					}
				
				// if we need to call a constructor, we insert the respective Jimple statement here
				if (instanceNeeded && !localVarsForClasses.containsKey(currentClass.getName())){
					Local localVal = generateClassConstructor(currentClass, body);
					if (localVal == null) {
						logger.warn("Constructor cannot be generated for {}", currentClass.getName());
						continue;
					}
					localVarsForClasses.put(currentClass.getName(), localVal);
				}
				Local classLocal = localVarsForClasses.get(entry.getKey());
				
				if (currentClass.getName().equals("nxtvwpsa.dtljjuhwhhk.bgixlckwb"))
					System.out.println("x");
	
				// Generate the lifecycles for the different kinds of Android classes
				switch (componentType) {
				case Activity:
					generateActivityLifecycle(entry.getValue(), currentClass, endClassStmt,
							classLocal);
					break;
				case Service:
					generateServiceLifecycle(entry.getValue(), currentClass, endClassStmt,
							classLocal);
					break;
				case BroadcastReceiver:
					generateBroadcastReceiverLifecycle(entry.getValue(), currentClass, endClassStmt,
							classLocal);
					break;
				case ContentProvider:
					generateContentProviderLifecycle(entry.getValue(), currentClass, endClassStmt,
							classLocal);
					break;
				case Plain:
					// Allow the complete class to be skipped
					createIfStmt(endClassStmt);

					JNopStmt beforeClassStmt = new JNopStmt();
					body.getUnits().add(beforeClassStmt);
					for(SootMethod currentMethod : plainMethods.values()) {
						if (!currentMethod.isStatic() && classLocal == null) {
							logger.warn("Skipping method {} because we have no instance", currentMethod);
							continue;
						}
						
						// Create a conditional call on the current method
						JNopStmt thenStmt = new JNopStmt();
						createIfStmt(thenStmt);
						buildMethodCall(currentMethod, body, classLocal, generator);
						body.getUnits().add(thenStmt);
						
						// Because we don't know the order of the custom statements,
						// we assume that you can loop arbitrarily
						createIfStmt(beforeClassStmt);
					}
					break;
				}
			}
			finally {
				body.getUnits().add(endClassStmt);
//				body.getUnits().add(entryExitStmt);
			}
		}
		
		// Add conditional calls to the application callback methods
		if (applicationLocal != null) {
			Unit beforeAppCallbacks = Jimple.v().newNopStmt();
			body.getUnits().add(beforeAppCallbacks);			
			addApplicationCallbackMethods();
			createIfStmt(beforeAppCallbacks);
		}
		
		createIfStmt(outerStartStmt);
		
		// Add a call to application.onTerminate()
		if (applicationLocal != null)
			searchAndBuildMethod(AndroidEntryPointConstants.APPLICATION_ONTERMINATE,
					applicationClass, classMap.get(applicationClass.getName()), applicationLocal);

		body.getUnits().add(Jimple.v().newReturnVoidStmt());
		
		// Optimize and check the generated main method
		NopEliminator.v().transform(body);
		if (DEBUG || Options.v().validate())
			mainMethod.getActiveBody().validate();
		
		logger.info("Generated main method:\n{}", body);
		return mainMethod;
	}
	
	private Map<SootClass, ComponentType> componentTypeCache = new HashMap<SootClass, ComponentType>();

	/**
	 * Gets the type of component represented by the given Soot class
	 * @param currentClass The class for which to get the component type
	 * @return The component type of the given class
	 */
	private ComponentType getComponentType(SootClass currentClass) {
		if (componentTypeCache.containsKey(currentClass))
			return componentTypeCache.get(currentClass);
		
		// Check the type of this class
		ComponentType ctype = ComponentType.Plain;
		Collection<SootClass> extendedClasses = Scene.v().getActiveHierarchy().getSuperclassesOf(currentClass);
		for(SootClass sc : extendedClasses) {
			if(sc.getName().equals(AndroidEntryPointConstants.APPLICATIONCLASS))
				ctype = ComponentType.Application;
			else if(sc.getName().equals(AndroidEntryPointConstants.ACTIVITYCLASS))
				ctype = ComponentType.Activity;
			else if(sc.getName().equals(AndroidEntryPointConstants.SERVICECLASS))
				ctype = ComponentType.Service;
			else if(sc.getName().equals(AndroidEntryPointConstants.BROADCASTRECEIVERCLASS))
				ctype = ComponentType.BroadcastReceiver;
			else if(sc.getName().equals(AndroidEntryPointConstants.CONTENTPROVIDERCLASS))
				ctype = ComponentType.ContentProvider;
		}
		componentTypeCache.put(currentClass, ctype);
		return ctype; 
	}

	/**
	 * Generates the lifecycle for an Android content provider class
	 * @param entryPoints The list of methods to consider in this class
	 * @param currentClass The class for which to build the content provider
	 * lifecycle
	 * @param endClassStmt The statement to which to jump after completing
	 * the lifecycle
	 * @param classLocal The local referencing an instance of the current class
	 */
	private void generateContentProviderLifecycle
			(List<String> entryPoints,
			SootClass currentClass,
			JNopStmt endClassStmt,
			Local classLocal) {
		// As we don't know the order in which the different Android lifecycles
		// run, we allow for each single one of them to be skipped
		createIfStmt(endClassStmt);

		// ContentProvider.onCreate() runs before everything else, even before
		// Application.onCreate(). We must thus handle it elsewhere.
		// Stmt onCreateStmt = searchAndBuildMethod(AndroidEntryPointConstants.CONTENTPROVIDER_ONCREATE, currentClass, entryPoints, classLocal);
		
		// see: http://developer.android.com/reference/android/content/ContentProvider.html
		//methods
		JNopStmt startWhileStmt = new JNopStmt();
		JNopStmt endWhileStmt = new JNopStmt();
		body.getUnits().add(startWhileStmt);
		boolean hasAdditionalMethods = false;
		if (modelAdditionalMethods) {
			for(SootMethod currentMethod : currentClass.getMethods()){
				if(entryPoints.contains(currentMethod.toString()) && !AndroidEntryPointConstants.getContentproviderLifecycleMethods().contains(currentMethod.getSubSignature())){
					JNopStmt thenStmt = new JNopStmt();
					createIfStmt(thenStmt);
					buildMethodCall(currentMethod, body, classLocal, generator);
					body.getUnits().add(thenStmt);
					hasAdditionalMethods = true;
				}
			}
		}
		addCallbackMethods(currentClass);
		body.getUnits().add(endWhileStmt);
		if (hasAdditionalMethods)
			createIfStmt(startWhileStmt);
		// createIfStmt(onCreateStmt);
	}

	/**
	 * Generates the lifecycle for an Android broadcast receiver class
	 * @param entryPoints The list of methods to consider in this class
	 * @param currentClass The class for which to build the broadcast receiver
	 * lifecycle
	 * @param endClassStmt The statement to which to jump after completing
	 * the lifecycle
	 * @param classLocal The local referencing an instance of the current class
	 */
	private void generateBroadcastReceiverLifecycle
			(List<String> entryPoints,
			SootClass currentClass,
			JNopStmt endClassStmt,
			Local classLocal) {
		// As we don't know the order in which the different Android lifecycles
		// run, we allow for each single one of them to be skipped
		createIfStmt(endClassStmt);

		Stmt onReceiveStmt = searchAndBuildMethod(AndroidEntryPointConstants.BROADCAST_ONRECEIVE, currentClass, entryPoints, classLocal);
		//methods
		JNopStmt startWhileStmt = new JNopStmt();
		JNopStmt endWhileStmt = new JNopStmt();
		body.getUnits().add(startWhileStmt);
		boolean hasAdditionalMethods = false;
		if (modelAdditionalMethods) {
			for(SootMethod currentMethod : currentClass.getMethods()){
				if(entryPoints.contains(currentMethod.toString()) && !AndroidEntryPointConstants.getBroadcastLifecycleMethods().contains(currentMethod.getSubSignature())){
					JNopStmt thenStmt = new JNopStmt();
					createIfStmt(thenStmt);
					buildMethodCall(currentMethod, body, classLocal, generator);
					body.getUnits().add(thenStmt);
					hasAdditionalMethods = true;
				}
			}
		}
		addCallbackMethods(currentClass);
		body.getUnits().add(endWhileStmt);
		if (hasAdditionalMethods)
			createIfStmt(startWhileStmt);
		createIfStmt(onReceiveStmt);
	}

	/**
	 * Generates the lifecycle for an Android service class
	 * @param entryPoints The list of methods to consider in this class
	 * @param currentClass The class for which to build the service lifecycle
	 * @param endClassStmt The statement to which to jump after completing
	 * the lifecycle
	 * @param classLocal The local referencing an instance of the current class
	 */
	private void generateServiceLifecycle
			(List<String> entryPoints,
			SootClass currentClass,
			JNopStmt endClassStmt,
			Local classLocal) {
		// As we don't know the order in which the different Android lifecycles
		// run, we allow for each single one of them to be skipped
//		createIfStmt(endClassStmt);

		// 1. onCreate:
		Stmt onCreateStmt = searchAndBuildMethod(AndroidEntryPointConstants.SERVICE_ONCREATE, currentClass, entryPoints, classLocal);
		
		//service has two different lifecycles:
		//lifecycle1:
		//2. onStart:
		searchAndBuildMethod(AndroidEntryPointConstants.SERVICE_ONSTART1, currentClass, entryPoints, classLocal);
		searchAndBuildMethod(AndroidEntryPointConstants.SERVICE_ONSTART2, currentClass, entryPoints, classLocal);
		//methods: 
		//all other entryPoints of this class:
		JNopStmt startWhileStmt = new JNopStmt();
		JNopStmt endWhileStmt = new JNopStmt();
		body.getUnits().add(startWhileStmt);
		boolean hasAdditionalMethods = false;
		if (modelAdditionalMethods) {
			for(SootMethod currentMethod : currentClass.getMethods()){
				if(entryPoints.contains(currentMethod.toString()) && !AndroidEntryPointConstants.getServiceLifecycleMethods().contains(currentMethod.getSubSignature())){
					JNopStmt thenStmt = new JNopStmt();
					createIfStmt(thenStmt);
					buildMethodCall(currentMethod, body, classLocal, generator);
					body.getUnits().add(thenStmt);
				}
			}
		}
		addCallbackMethods(currentClass);
		body.getUnits().add(endWhileStmt);
		if (hasAdditionalMethods)
			createIfStmt(startWhileStmt);
		
		//lifecycle1 end
		
		//lifecycle2 start
		//onBind:
		searchAndBuildMethod(AndroidEntryPointConstants.SERVICE_ONBIND, currentClass, entryPoints, classLocal);
		
		JNopStmt beforemethodsStmt = new JNopStmt();
		body.getUnits().add(beforemethodsStmt);
		//methods
		JNopStmt startWhile2Stmt = new JNopStmt();
		JNopStmt endWhile2Stmt = new JNopStmt();
		body.getUnits().add(startWhile2Stmt);
		hasAdditionalMethods = false;
		if (modelAdditionalMethods) {
			for(SootMethod currentMethod : currentClass.getMethods()){
				if(entryPoints.contains(currentMethod.toString()) && !AndroidEntryPointConstants.getServiceLifecycleMethods().contains(currentMethod.getSubSignature())){
					JNopStmt thenStmt = new JNopStmt();
					createIfStmt(thenStmt);
					buildMethodCall(currentMethod, body, classLocal, generator);
					body.getUnits().add(thenStmt);
					hasAdditionalMethods = true;
				}
			}
		}
		addCallbackMethods(currentClass);
		body.getUnits().add(endWhile2Stmt);
		if (hasAdditionalMethods)
			createIfStmt(startWhile2Stmt);
		
		//onUnbind:
		Stmt onDestroyStmt = Jimple.v().newNopStmt();
		searchAndBuildMethod(AndroidEntryPointConstants.SERVICE_ONUNBIND, currentClass, entryPoints, classLocal);
		createIfStmt(onDestroyStmt);	// fall through to rebind or go to destroy
		
		//onRebind:
		searchAndBuildMethod(AndroidEntryPointConstants.SERVICE_ONREBIND, currentClass, entryPoints, classLocal);
		createIfStmt(beforemethodsStmt);
		
		//lifecycle2 end
		
		//onDestroy:
		body.getUnits().add(onDestroyStmt);
		searchAndBuildMethod(AndroidEntryPointConstants.SERVICE_ONDESTROY, currentClass, entryPoints, classLocal);
		
		//either begin or end or next class:
		createIfStmt(onCreateStmt);
//		createIfStmt(endClassStmt);
	}

	/**
	 * Generates the lifecycle for an Android activity
	 * @param entryPoints The list of methods to consider in this class
	 * @param currentClass The class for which to build the activity lifecycle
	 * @param endClassStmt The statement to which to jump after completing
	 * the lifecycle
	 * @param classLocal The local referencing an instance of the current class
	 */
	private void generateActivityLifecycle
			(List<String> entryPoints,
			SootClass currentClass,
			JNopStmt endClassStmt,
			Local classLocal) {
		// As we don't know the order in which the different Android lifecycles
		// run, we allow for each single one of them to be skipped
		createIfStmt(endClassStmt);
		
		Set<SootClass> referenceClasses = new HashSet<SootClass>();
		if (applicationClass != null)
			referenceClasses.add(applicationClass);
		for (SootClass callbackClass : this.applicationCallbackClasses)
			referenceClasses.add(callbackClass);
		referenceClasses.add(currentClass);
		
		// 1. onCreate:
		Stmt onCreateStmt = new JNopStmt();
		body.getUnits().add(onCreateStmt);
		{
			Stmt onCreateStmt2 = searchAndBuildMethod
				(AndroidEntryPointConstants.ACTIVITY_ONCREATE, currentClass, entryPoints, classLocal);
			boolean found = addCallbackMethods(applicationClass, referenceClasses,
					AndroidEntryPointConstants.APPLIFECYCLECALLBACK_ONACTIVITYCREATED);
			if (found && onCreateStmt2 != null)
				createIfStmt(onCreateStmt2);
		}
		
		//2. onStart:
		Stmt onStartStmt = new JNopStmt();
		body.getUnits().add(onStartStmt);
		{
			Stmt onStartStmt2 = searchAndBuildMethod
					(AndroidEntryPointConstants.ACTIVITY_ONSTART, currentClass, entryPoints, classLocal);
			boolean found = addCallbackMethods(applicationClass, referenceClasses,
					AndroidEntryPointConstants.APPLIFECYCLECALLBACK_ONACTIVITYSTARTED);
			if (found && onStartStmt2 != null)
				createIfStmt(onStartStmt2);
		}
		searchAndBuildMethod(AndroidEntryPointConstants.ACTIVITY_ONRESTOREINSTANCESTATE, currentClass, entryPoints, classLocal);
		searchAndBuildMethod(AndroidEntryPointConstants.ACTIVITY_ONPOSTCREATE, currentClass, entryPoints, classLocal);
		
		//3. onResume:
		Stmt onResumeStmt = new JNopStmt();
		body.getUnits().add(onResumeStmt);
		{
			Stmt onResumeStmt2 = searchAndBuildMethod
					(AndroidEntryPointConstants.ACTIVITY_ONRESUME, currentClass, entryPoints, classLocal);
			boolean found = addCallbackMethods(applicationClass, referenceClasses,
					AndroidEntryPointConstants.APPLIFECYCLECALLBACK_ONACTIVITYRESUMED);
			if (found && onResumeStmt2 != null)
				createIfStmt(onResumeStmt2);
		}
		searchAndBuildMethod
				(AndroidEntryPointConstants.ACTIVITY_ONPOSTRESUME, currentClass, entryPoints, classLocal);
		
		// Scan for other entryPoints of this class:
		Set<SootMethod> methodsToInvoke = new HashSet<SootMethod>();
		if (modelAdditionalMethods)
			for(SootMethod currentMethod : currentClass.getMethods())
				if(entryPoints.contains(currentMethod.toString())
						&& !AndroidEntryPointConstants.getActivityLifecycleMethods().contains(currentMethod.getSubSignature()))
					methodsToInvoke.add(currentMethod);
		boolean hasCallbacks = this.callbackFunctions.containsKey(currentClass.getName());
	
		if (!methodsToInvoke.isEmpty() || hasCallbacks) {
			JNopStmt startWhileStmt = new JNopStmt();
			JNopStmt endWhileStmt = new JNopStmt();
			body.getUnits().add(startWhileStmt);

			// Add the callbacks
			addCallbackMethods(currentClass);

			// Add the other entry points
			for (SootMethod currentMethod : methodsToInvoke) {
				JNopStmt thenStmt = new JNopStmt();
				createIfStmt(thenStmt);
				buildMethodCall(currentMethod, body, classLocal, generator);
				body.getUnits().add(thenStmt);
			}

			body.getUnits().add(endWhileStmt);
			createIfStmt(startWhileStmt);
		}
				
		//4. onPause:
		Stmt onPause = searchAndBuildMethod(AndroidEntryPointConstants.ACTIVITY_ONPAUSE, currentClass, entryPoints, classLocal);
		boolean hasAppOnPause = addCallbackMethods(applicationClass, referenceClasses,
				AndroidEntryPointConstants.APPLIFECYCLECALLBACK_ONACTIVITYPAUSED);
		if (hasAppOnPause && onPause != null)
			createIfStmt(onPause);
		searchAndBuildMethod(AndroidEntryPointConstants.ACTIVITY_ONCREATEDESCRIPTION, currentClass, entryPoints, classLocal);
		Stmt onSaveInstance = searchAndBuildMethod(AndroidEntryPointConstants.ACTIVITY_ONSAVEINSTANCESTATE, currentClass, entryPoints, classLocal);
		boolean hasAppOnSaveInstance = addCallbackMethods(applicationClass, referenceClasses,
				AndroidEntryPointConstants.APPLIFECYCLECALLBACK_ONACTIVITYSAVEINSTANCESTATE);
		if (hasAppOnSaveInstance && onSaveInstance != null)
			createIfStmt(onSaveInstance);

		//goTo Stop, Resume or Create:
		JNopStmt pauseToStopStmt = new JNopStmt();
		createIfStmt(pauseToStopStmt);
		createIfStmt(onResumeStmt);
		createIfStmt(onCreateStmt);
		
		body.getUnits().add(pauseToStopStmt);
		//5. onStop:
		Stmt onStop = searchAndBuildMethod(AndroidEntryPointConstants.ACTIVITY_ONSTOP, currentClass, entryPoints, classLocal);
		boolean hasAppOnStop = addCallbackMethods(applicationClass, referenceClasses,
				AndroidEntryPointConstants.APPLIFECYCLECALLBACK_ONACTIVITYSTOPPED);
		if (hasAppOnStop && onStop != null)
			createIfStmt(onStop);

		//goTo onDestroy, onRestart or onCreate:
		JNopStmt stopToDestroyStmt = new JNopStmt();
		JNopStmt stopToRestartStmt = new JNopStmt();
		createIfStmt(stopToDestroyStmt);
		createIfStmt(stopToRestartStmt);
		createIfStmt(onCreateStmt);
		
		//6. onRestart:
		body.getUnits().add(stopToRestartStmt);
		searchAndBuildMethod(AndroidEntryPointConstants.ACTIVITY_ONRESTART, currentClass, entryPoints, classLocal);
		createIfStmt(onStartStmt);	// jump to onStart(), fall through to onDestroy()
		
		//7. onDestroy
		body.getUnits().add(stopToDestroyStmt);
		Stmt onDestroy = searchAndBuildMethod(AndroidEntryPointConstants.ACTIVITY_ONDESTROY, currentClass, entryPoints, classLocal);
		boolean hasAppOnDestroy = addCallbackMethods(applicationClass, referenceClasses,
				AndroidEntryPointConstants.APPLIFECYCLECALLBACK_ONACTIVITYDESTROYED);
		if (hasAppOnDestroy && onDestroy != null)
			createIfStmt(onDestroy);

		createIfStmt(endClassStmt);
	}
	
	/**
	 * Adds calls to the callback methods defined in the application class
	 * @param applicationClass The class in which the user-defined application
	 * is implemented
	 * @param applicationLocal The local containing the instance of the
	 * user-defined application
	 */
	private void addApplicationCallbackMethods() {
		if (!this.callbackFunctions.containsKey(applicationClass.getName()))
			return;
		
		// Do not try to generate calls to methods in non-concrete classes
		if (applicationClass.isAbstract())
			return;
		if (applicationClass.isPhantom()) {
			System.err.println("Skipping possible application callbacks in "
					+ "phantom class " + applicationClass);
			return;
		}

		for (String methodSig : this.callbackFunctions.get(applicationClass.getName())) {
			SootMethodAndClass methodAndClass = SootMethodRepresentationParser.v().parseSootMethodString(methodSig);
		
			// We do not consider lifecycle methods which are directly inserted
			// at their respective positions
			if (AndroidEntryPointConstants.getApplicationLifecycleMethods().contains
					(methodAndClass.getSubSignature()))
				continue;
					
			SootMethod method = findMethod(Scene.v().getSootClass(methodAndClass.getClassName()),
					methodAndClass.getSubSignature());
			// If we found no implementation or if the implementation we found
			// is in a system class, we skip it. Note that null methods may
			// happen since all callback interfaces for application callbacks
			// are registered under the name of the application class.
			if (method == null)
				continue;
			if (method.getDeclaringClass().getName().startsWith("android.")
					|| method.getDeclaringClass().getName().startsWith("java."))
				continue;
			
			// Get the local instance of the target class
			Local local = this.localVarsForClasses.get(methodAndClass.getClassName());
			if (local == null) {
				System.err.println("Could not create call to application callback "
						+ method.getSignature() + ". Local was null.");
				continue;
			}

			// Add a conditional call to the method
			JNopStmt thenStmt = new JNopStmt();
			createIfStmt(thenStmt);
			buildMethodCall(method, body, local, generator);	
			body.getUnits().add(thenStmt);
		}
	}

	/**
	 * Generates invocation statements for all callback methods which need to
	 * be invoked during the given class' run cycle.
	 * @param currentClass The class for which we currently build the lifecycle
	 * @return True if a matching callback has been found, otherwise false.
	 */
	private boolean addCallbackMethods(SootClass currentClass) {
		return addCallbackMethods(currentClass, Collections.<SootClass>emptySet(), "");
	}

	/**
	 * Generates invocation statements for all callback methods which need to
	 * be invoked during the given class' run cycle.
	 * @param currentClass The class for which we currently build the lifecycle
	 * @param referenceClasses The classes for which no new instances shall be	
	 * created, but rather existing ones shall be used.
	 * @param callbackSignature An empty string if calls to all callback methods
	 * for the given class shall be generated, otherwise the subsignature of the
	 * only callback method to generate.
	 * @return True if a matching callback has been found, otherwise false.
	 */
	private boolean addCallbackMethods(SootClass currentClass, Set<SootClass> referenceClasses,
			String callbackSignature) {
		// If no callbacks are declared for the current class, there is nothing
		// to be done here
		if (currentClass == null)
			return false;
		if (!this.callbackFunctions.containsKey(currentClass.getName()))
			return false;
		
		// Get all classes in which callback methods are declared
		boolean callbackFound = false;
		Map<SootClass, Set<SootMethod>> callbackClasses = new HashMap<SootClass, Set<SootMethod>>();
		for (String methodSig : this.callbackFunctions.get(currentClass.getName())) {
			// Parse the callback 
			SootMethodAndClass methodAndClass = SootMethodRepresentationParser.v().parseSootMethodString(methodSig);
			if (!callbackSignature.isEmpty() && !callbackSignature.equals(methodAndClass.getSubSignature()))
				continue;
			
			SootClass theClass = Scene.v().getSootClass(methodAndClass.getClassName());
			SootMethod theMethod = findMethod(theClass, methodAndClass.getSubSignature());
			if (theMethod == null) {
//				logger.warn("Could not find callback method {}", methodAndClass.getSignature());
				continue;
			}
			
			// Check that we don't have one of the lifecycle methods as they are
			// treated separately.
			if (getComponentType(theClass) == ComponentType.Activity
						&& AndroidEntryPointConstants.getActivityLifecycleMethods().contains(theMethod.getSubSignature()))
					continue;
			if (getComponentType(theClass) == ComponentType.Service
					&& AndroidEntryPointConstants.getServiceLifecycleMethods().contains(theMethod.getSubSignature()))
				continue;
			if (getComponentType(theClass) == ComponentType.BroadcastReceiver
					&& AndroidEntryPointConstants.getBroadcastLifecycleMethods().contains(theMethod.getSubSignature()))
				continue;
			if (getComponentType(theClass) == ComponentType.ContentProvider
					&& AndroidEntryPointConstants.getContentproviderLifecycleMethods().contains(theMethod.getSubSignature()))
				continue;

			if (callbackClasses.containsKey(theClass))
				callbackClasses.get(theClass).add(theMethod);
			else {
				Set<SootMethod> methods = new HashSet<SootMethod>();
				methods.add(theMethod);
				callbackClasses.put(theClass, methods);				
			}
		}

		// The class for which we are generating the lifecycle always has an
		// instance.
		if (referenceClasses.isEmpty())
			referenceClasses = Collections.singleton(currentClass);
		else {
			referenceClasses = new HashSet<SootClass>(referenceClasses);
			referenceClasses.add(currentClass);
		}

		Stmt beforeCallbacks = Jimple.v().newNopStmt();
		body.getUnits().add(beforeCallbacks);
		for (SootClass callbackClass : callbackClasses.keySet()) {
			// If we already have a parent class that defines this callback, we
			// use it. Otherwise, we create a new one.
			Set<Local> classLocals = new HashSet<Local>();
			for (SootClass parentClass : referenceClasses) {
				Local parentLocal = this.localVarsForClasses.get(parentClass.getName());
				if (isCompatible(parentClass, callbackClass))
					classLocals.add(parentLocal);
			}
			if (classLocals.isEmpty()) {
				// Create a new instance of this class
				// if we need to call a constructor, we insert the respective Jimple statement here
				Local classLocal = generateClassConstructor(callbackClass, body, referenceClasses);
				if (classLocal == null) {
					logger.warn("Constructor cannot be generated for callback class {}", callbackClass.getName());
					continue;
				}
				classLocals.add(classLocal);
			}
			
			// Build the calls to all callback methods in this class
			for (Local classLocal : classLocals) {
				for (SootMethod callbackMethod : callbackClasses.get(callbackClass)) {
					JNopStmt thenStmt = new JNopStmt();
					createIfStmt(thenStmt);
					buildMethodCall(callbackMethod, body, classLocal, generator, referenceClasses);
					body.getUnits().add(thenStmt);
				}
				callbackFound = true;
			}
		}
		// jump back since we don't now the order of the callbacks
		if (callbackFound)
			createIfStmt(beforeCallbacks);
	
		return callbackFound;
	}
	
	private Stmt searchAndBuildMethod(String subsignature, SootClass currentClass, List<String> entryPoints, Local classLocal){
		if (currentClass == null || classLocal == null)
			return null;
		
		SootMethod method = findMethod(currentClass, subsignature);
		if (method == null) {
			logger.warn("Could not find Android entry point method: {}", subsignature);
			return null;
		}
		entryPoints.remove(method.getSignature());
		
		// If the method is in one of the predefined Android classes, it cannot
		// contain custom code, so we do not need to call it
		if (AndroidEntryPointConstants.isLifecycleClass(method.getDeclaringClass().getName()))
			return null;
		
		// If this method is part of the Android framework, we don't need to call it
		if (method.getDeclaringClass().getName().startsWith("android."))
			return null;
		
		assert method.isStatic() || classLocal != null : "Class local was null for non-static method "
				+ method.getSignature();
		
		//write Method
		return buildMethodCall(method, body, classLocal, generator);
	}
	
	private void createIfStmt(Unit target){
		if(target == null){
			return;
		}
		JEqExpr cond = new JEqExpr(intCounter, IntConstant.v(conditionCounter++));
		JIfStmt ifStmt = new JIfStmt(cond, target);
		body.getUnits().add(ifStmt);
	}
	
	/**
	 * Sets whether additional methods which are present in a component, but are
	 * neither lifecycle methods nor callbacks, shall also be modeled in the dummy
	 * main method.
	 * @param modelAdditionalMethods True if additional methods shall be modeled,
	 * otherwise false
	 */
	public void setModelAdditionalMethods(boolean modelAdditionalMethods) {
		this.modelAdditionalMethods = modelAdditionalMethods;
	}
	
	/**
	 * Gets whether additional methods which are present in a component, but are
	 * neither lifecycle methods nor callbacks, shall also be modeled in the dummy
	 * main method.
	 * @return True if additional methods shall be modeled, otherwise false
	 */
	public boolean getModelAdditionalMethods() {
		return this.modelAdditionalMethods;
	}
	
}
