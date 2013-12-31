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
package soot.jimple.infoflow.taintWrappers;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.util.SootMethodRepresentationParser;
import soot.jimple.internal.JAssignStmt;

/**
 * A list of methods is passed which contains signatures of instance methods
 * that taint their base objects if they are called with a tainted parameter.
 * When a base object is tainted, all return values are tainted, too.
 * For static methods, only the return value is assumed to be tainted when
 * the method is called with a tainted parameter value.
 * 
 * @author Christian Fritz, Steven Arzt
 *
 */
public class EasyTaintWrapper extends AbstractTaintWrapper {
    private final Logger logger = LoggerFactory.getLogger(getClass());
	private final Map<String, List<String>> classList;
	private final Map<String, List<String>> excludeList;
	private final Map<String, List<String>> killList;
	private final Set<String> includeList;
	private boolean aggressiveMode = false;
	
	public EasyTaintWrapper(HashMap<String, List<String>> classList){
		this.classList = classList;
		this.excludeList = new HashMap<String, List<String>>();
		this.killList = new HashMap<String, List<String>>();
		this.includeList = new HashSet<String>();
	}
	
	public EasyTaintWrapper(HashMap<String, List<String>> classList,
			HashMap<String, List<String>> excludeList) {
		this.classList = classList;
		this.excludeList = excludeList;
		this.killList = new HashMap<String, List<String>>();
		this.includeList = new HashSet<String>();
	}

	public EasyTaintWrapper(HashMap<String, List<String>> classList,
			HashMap<String, List<String>> excludeList,
			HashMap<String, List<String>> killList) {
		this.classList = classList;
		this.excludeList = excludeList;
		this.killList = killList;
		this.includeList = new HashSet<String>();
	}

    public EasyTaintWrapper(String f) throws IOException{
        this(new File(f));
    }

	public EasyTaintWrapper(File f) throws IOException{
        this(new BufferedReader(new FileReader(f)));
	}

    public EasyTaintWrapper(InputStream is) throws IOException {
        this(new BufferedReader(new InputStreamReader(is)));
    }

    private EasyTaintWrapper(BufferedReader reader) throws IOException {
        try {
        this.includeList = new HashSet<String>();
        String line = reader.readLine();
        List<String> methodList = new LinkedList<String>();
        List<String> excludeList = new LinkedList<String>();
        List<String> killList = new LinkedList<String>();
        while(line != null){
            if (!line.isEmpty() && !line.startsWith("%"))
                if (line.startsWith("~"))
                    excludeList.add(line.substring(1));
                else if (line.startsWith("-"))
                    killList.add(line.substring(1));
                else if (line.startsWith("^"))
                    includeList.add(line.substring(1));
                else
                    methodList.add(line);
            line = reader.readLine();
        }
        this.classList = SootMethodRepresentationParser.v().parseClassNames(methodList, true);
        this.excludeList = SootMethodRepresentationParser.v().parseClassNames(excludeList, true);
        this.killList = SootMethodRepresentationParser.v().parseClassNames(killList, true);
        logger.info("Loaded wrapper entries for {} classes and {} exclusions.", classList.size(), excludeList.size());
        } finally{
            reader.close();
        }
    }


    @Override
	public Set<AccessPath> getTaintsForMethod(Stmt stmt, AccessPath taintedPath) {
		if (!stmt.containsInvokeExpr())
			return Collections.emptySet();
		
		Set<AccessPath> taints = new HashSet<AccessPath>();

		SootMethod method = stmt.getInvokeExpr().getMethod();
		List<String> methodList = getMethodsForClass(method.getDeclaringClass());
		
		// If the callee is a phantom class or has no body, we pass on the taint
		if (method.isPhantom() || !method.hasActiveBody())
			taints.add(taintedPath);

		// If this is not one of the supported classes, we skip it
		boolean isSupported = false;
		for (String supportedClass : this.includeList)
			if (method.getDeclaringClass().getName().startsWith(supportedClass)) {
				isSupported = true;
				break;
			}
		if (!isSupported && !aggressiveMode)
			return Collections.emptySet();

		// For implicit flows, we always taint the return value and the base
		// object on the empty abstraction.
		if (taintedPath.isEmpty()) {
			taints.add(taintedPath);
			if (stmt instanceof DefinitionStmt)
				taints.add(new AccessPath(((DefinitionStmt) stmt).getLeftOp()));
			if (stmt.containsInvokeExpr())
				if (stmt.getInvokeExpr() instanceof InstanceInvokeExpr)
					taints.add(new AccessPath(((InstanceInvokeExpr) stmt.getInvokeExpr()).getBase()));
			return taints;
		}

		// For the moment, we don't implement static taints on wrappers. Pass it on
		// not to break anything
		if(taintedPath.isStaticFieldRef())
			return Collections.singleton(taintedPath);

		if (stmt.getInvokeExpr() instanceof InstanceInvokeExpr) {
			InstanceInvokeExpr iiExpr = (InstanceInvokeExpr) stmt.getInvokeExpr();
			
			if (iiExpr.getBase().equals(taintedPath.getPlainValue())) {
				// If the base object is tainted, we have to check whether we must kill the taint
				List<String> killMethods = this.killList.get(stmt.getInvokeExpr().getMethod().getDeclaringClass().getName());
				if (killMethods != null && killMethods.contains(stmt.getInvokeExpr().getMethod().getSubSignature()))
					return Collections.emptySet();

				// If the base object is tainted, all calls to its methods always return
				// tainted values
				if (stmt instanceof JAssignStmt) {
					AssignStmt assign = (AssignStmt) stmt;
					// Check for exclusions
					List<String> excludedMethods = this.excludeList.get(assign.getInvokeExpr().getMethod().getDeclaringClass().getName());
					if (excludedMethods == null || !excludedMethods.contains
							(assign.getInvokeExpr().getMethod().getSubSignature()))
						taints.add(new AccessPath(assign.getLeftOp()));
				}

				// If the base object is tainted, we pass this taint on
				taints.add(taintedPath);
			}
		}
		
		// Even in aggressive mode, we do not taint base objects based on
		// parameters unless we know what the method is doing
		if (!isSupported)
			return Collections.emptySet();

		//if param is tainted && classList contains classname && if list. contains signature of method -> add propagation
		for (Value param : stmt.getInvokeExpr().getArgs())
			if (param.equals(taintedPath.getPlainValue())) {		
				if(methodList.contains(method.getSubSignature())) {
					// If we call a method on an instance, this instance is assumed to be tainted
					if(stmt.getInvokeExprBox().getValue() instanceof InstanceInvokeExpr) {
						taints.add(new AccessPath(((InstanceInvokeExpr) stmt.getInvokeExprBox().getValue()).getBase()));
						
						// If make sure to also taint the left side of an assignment
						// if the object just got tainted 
						if(stmt instanceof JAssignStmt)
							taints.add(new AccessPath(((JAssignStmt)stmt).getLeftOp()));
					}
					else if (stmt.getInvokeExprBox().getValue() instanceof StaticInvokeExpr)
						if (stmt instanceof JAssignStmt)
							taints.add(new AccessPath(((JAssignStmt)stmt).getLeftOp()));
				}
					
				// The parameter as such stays tainted
				taints.add(taintedPath);
			}
		
		return taints;
	}
	
	private List<String> getMethodsForClass(SootClass c){
		assert c != null;
		
		List<String> methodList = new LinkedList<String>();
		if(classList.containsKey(c.getName())){
			methodList.addAll(classList.get(c.getName()));
		}
		
		if(!c.isInterface()) {
			// We have to walk up the hierarchy to also include all methods
			// registered for superclasses
			Collection<SootClass> superclasses = Scene.v().getActiveHierarchy().getSuperclassesOf(c);
			for(SootClass sclass : superclasses){
				if(classList.containsKey(sclass.getName()))
					methodList.addAll(getMethodsForClass(sclass));
			}
		}
		
		// If we implement interfaces, we also need to check whether they in
		// turn are in our method list
		for (SootClass ifc : c.getInterfaces())
			methodList.addAll(getMethodsForClass(ifc));
		
		return methodList;
	}

	private boolean hasMethodsForClass(SootClass c){
		if (classList.containsKey(c.getName()))
			return true;
		
		if(!c.isInterface()) {
			// We have to walk up the hierarchy to also include all methods
			// registered for superclasses
			Collection<SootClass> superclasses = Scene.v().getActiveHierarchy().getSuperclassesOf(c);
			for(SootClass sclass : superclasses){
				if(classList.containsKey(sclass.getName()))
					return true;
			}
		}
		
		return false;
	}

	@Override
	public boolean isExclusiveInternal(Stmt stmt, AccessPath taintedPath) {
		SootMethod method = stmt.getInvokeExpr().getMethod();
		
		// In aggressive mode, we always taint the return value if the base
		// object is tainted.
		if (aggressiveMode && stmt.getInvokeExpr() instanceof InstanceInvokeExpr) {
			InstanceInvokeExpr iiExpr = (InstanceInvokeExpr) stmt.getInvokeExpr();			
			if (iiExpr.getBase().equals(taintedPath.getPlainValue()))
				return true;
		}
		
		return hasMethodsForClass(method.getDeclaringClass());
	}
	
	/**
	 * Sets whether the taint wrapper shall always assume the return value of a
	 * call "a = x.foo()" to be tainted if the base object is tainted, even if
	 * the respective method is not in the data file.
	 * @param aggressiveMode True if return values shall always be tainted if
	 * the base object on which the method is invoked is tainted, otherwise
	 * false
	 */
	public void setAggressiveMode(boolean aggressiveMode) {
		this.aggressiveMode = aggressiveMode;
	}
	
	/**
	 * Gets whether the taint wrapper shall always consider return values as
	 * tainted if the base object of the respective invocation is tainted
	 * @return True if return values shall always be tainted if the base
	 * object on which the method is invoked is tainted, otherwise false
	 */
	public boolean getAggressiveMode() {
		return this.aggressiveMode;
	}

}
