package soot.jimple.infoflow;

import heros.InterproceduralCFG;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import soot.MethodOrMethodContext;
import soot.PackManager;
import soot.PatchingChain;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.Transform;
import soot.Unit;
import soot.dexpler.DexResolver;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.infoflow.AbstractInfoflowProblem.PathTrackingMethod;
import soot.jimple.infoflow.InfoflowResults.SourceInfo;
import soot.jimple.infoflow.config.IInfoflowSootConfig;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.source.DefaultSourceSinkManager;
import soot.jimple.infoflow.source.SourceSinkManager;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.jimple.infoflow.util.AndroidEntryPointCreator;
import soot.jimple.infoflow.util.IEntryPointCreator;
import soot.jimple.infoflow.util.SootMethodRepresentationParser;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.jimple.toolkits.ide.JimpleIFDSSolver;
import soot.options.Options;

public class Infoflow implements IInfoflow {

	public static boolean DEBUG = false;
	public boolean local = false;
	public InfoflowResults results;

	private final String androidPath;
	private final boolean forceAndroidJar;
	private ITaintPropagationWrapper taintWrapper;
	private PathTrackingMethod pathTracking = PathTrackingMethod.NoTracking;
	private IInfoflowSootConfig sootConfig;
	
	private boolean computeParamFlows = false;
	private boolean returnIsSink = false;
	private boolean stopAfterFirstFlow = false;

	/**
	 * Creates a new instance of the InfoFlow class for analyzing plain Java code without any references to APKs or the Android SDK.
	 */
	public Infoflow() {
		this.androidPath = "";
		this.forceAndroidJar = false;
	}

	/**
	 * Creates a new instance of the InfoFlow class for analyzing Android APK files. This constructor sets the right options for analyzing APK files.
	 * 
	 * @param androidPath
	 *            If forceAndroidJar is false, this is the base directory of the platform files in the Android SDK. If forceAndroidJar is true, this is the full path of a single android.jar file.
	 * @param forceAndroidJar
	 */
	public Infoflow(String androidPath, boolean forceAndroidJar) {
		this.androidPath = androidPath;
		this.forceAndroidJar = forceAndroidJar;
	}
	
	public void setTaintWrapper(ITaintPropagationWrapper wrapper){
		taintWrapper = wrapper;
	}
	
	public void setSootConfig(IInfoflowSootConfig config){
		sootConfig = config;
	}
	
	@Override
	public void setPathTracking(PathTrackingMethod method) {
		this.pathTracking = method;
	}
	
	@Override
	public void setComputeParamFlows(boolean computeParamFlows) {
		this.computeParamFlows = computeParamFlows;
	}
	
	@Override
	public void setReturnIsSink(boolean returnIsSink) {
		this.returnIsSink = returnIsSink;
	}

	@Override
	public void setStopAfterFirstFlow(boolean stopAfterFirstFlow) {
		this.stopAfterFirstFlow = stopAfterFirstFlow;
	}
	
	@Override
	public void computeInfoflow(String path, List<String> entryPoints, List<String> sources, List<String> sinks) {
		this.computeInfoflow(path, entryPoints, new DefaultSourceSinkManager(sources, sinks));
	}

	@Override
	public void computeInfoflow(String path, String entryPoint, List<String> sources, List<String> sinks) {
		this.computeInfoflow(path, entryPoint, new DefaultSourceSinkManager(sources, sinks));
	}
	
	/**
	 * Initializes Soot.
	 * @param path The Soot classpath
	 * @param classes The set of classes that shall be checked for data flow
	 * analysis seeds. All sources in these classes are used as seeds.
	 * @param sourcesSinks The manager object for identifying sources and sinks
	 */
	private void initializeSoot(String path, Set<String> classes, SourceSinkManager sourcesSinks) {
		initializeSoot(path, classes, sourcesSinks, "");
	}
	
	/**
	 * Initializes Soot.
	 * @param path The Soot classpath
	 * @param classes The set of classes that shall be checked for data flow
	 * analysis seeds. All sources in these classes are used as seeds. If a
	 * non-empty extra seed is given, this one is used too.
	 * @param sourcesSinks The manager object for identifying sources and sinks
	 * @param extraSeed An optional extra seed, can be empty.
	 */
	private void initializeSoot(String path, Set<String> classes, SourceSinkManager sourcesSinks, String extraSeed) {
		// reset Soot:
		soot.G.reset();
		DexResolver.reset();
		
		// add SceneTransformer which calculates and prints infoflow
		Set<String> seeds = Collections.emptySet();
		if (extraSeed != null && !extraSeed.isEmpty())
			seeds = Collections.singleton(extraSeed);
		addSceneTransformer(sourcesSinks, seeds);

		Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_allow_phantom_refs(true);
		if (DEBUG)
			Options.v().set_output_format(Options.output_format_jimple);
		else
			Options.v().set_output_format(Options.output_format_none);
		Options.v().set_whole_program(true);
		Options.v().set_soot_classpath(path);
//		soot.options.Options.v().set_prepend_classpath(true);
		Options.v().set_process_dir(Arrays.asList(classes.toArray()));
		if (extraSeed == null || extraSeed.isEmpty())
			Options.v().setPhaseOption("cg.spark", "on");
		else
			Options.v().setPhaseOption("cg.spark", "vta:true");
		Options.v().setPhaseOption("jb", "use-original-names:true");
		// do not merge variables (causes problems with PointsToSets)
		Options.v().setPhaseOption("jb.ulp", "off");
		if (!this.androidPath.isEmpty()) {
			Options.v().set_src_prec(Options.src_prec_apk);
			if (this.forceAndroidJar)
				soot.options.Options.v().set_force_android_jar(this.androidPath);
			else
				soot.options.Options.v().set_android_jars(this.androidPath);
		}
		else
			Options.v().set_src_prec(Options.src_prec_java);
		
		//at the end of setting: load user settings:
		if (sootConfig != null)
			sootConfig.setSootOptions(Options.v());
		
		// load all entryPoint classes with their bodies
		Scene.v().loadNecessaryClasses();
		boolean hasClasses = false;
		for (String className : classes) {
			SootClass c = Scene.v().forceResolve(className, SootClass.BODIES);
			c.setApplicationClass();
			if (c != null && !c.isPhantomClass() && !c.isPhantom())
				hasClasses = true;
		}
		if (!hasClasses) {
			System.out.println("Only phantom classes loaded, skipping analysis...");
			return;
		}
	}
	
	@Override
	public void computeInfoflow(String path, List<String> entryPoints, SourceSinkManager sourcesSinks) {
		results = null;
		if (sourcesSinks == null) {
			System.out.println("Error: sources are empty!");
			return;
		}
	
		// convert to internal format:
		SootMethodRepresentationParser parser = new SootMethodRepresentationParser();
		// parse classNames as String and methodNames as string in soot representation
		HashMap<String, List<String>> classes = parser.parseClassNames(entryPoints, false);

		initializeSoot(path, classes.keySet(), sourcesSinks);

		if (DEBUG) {
			for (List<String> methodList : classes.values()) {
				for(String methodSignature : methodList){
				if (Scene.v().containsMethod(methodSignature)) {
						SootMethod method = Scene.v().getMethod(methodSignature);
						System.err.println(method.retrieveActiveBody().toString());
					}
				}
			}
		}
		
		// entryPoints are the entryPoints required by Soot to calculate Graph - if there is no main method,
		// we have to create a new main method and use it as entryPoint and store our real entryPoints
		IEntryPointCreator epCreator = new AndroidEntryPointCreator();
		Scene.v().setEntryPoints(Collections.singletonList(epCreator.createDummyMain(classes)));
		PackManager.v().runPacks();
		if (DEBUG)
			PackManager.v().writeOutput();
	}

	@Override
	public void computeInfoflow(String path, String entryPoint, SourceSinkManager sourcesSinks) {
		results = null;
		if (sourcesSinks == null) {
			System.out.println("Error: sources are empty!");
			return;
		}

		// convert to internal format:
		SootMethodRepresentationParser parser = new SootMethodRepresentationParser();
		// parse classNames as String and methodNames as string in soot representation
		HashMap<String, List<String>> classes = parser.parseClassNames(Collections.singletonList(entryPoint), false);

		initializeSoot(path, classes.keySet(), sourcesSinks, entryPoint);

		if (DEBUG) {
			for (List<String> methodList : classes.values()) {
				for(String methodSignature : methodList){
				if (Scene.v().containsMethod(methodSignature)) {
						SootMethod method = Scene.v().getMethod(methodSignature);
						System.err.println(method.retrieveActiveBody().toString());
					}
				}
			}
		}

		if (!Scene.v().containsMethod(entryPoint)){
			System.err.println("Entry point not found");
			return;
		}
		SootMethod ep = Scene.v().getMethod(entryPoint);
		if (ep.isConcrete())
			ep.retrieveActiveBody();
		else {
			System.err.println("Skipping non-concrete method " + ep);
			return;
		}
		Scene.v().setEntryPoints(Collections.singletonList(ep));
		Options.v().set_main_class(ep.getDeclaringClass().getName());
		PackManager.v().runPacks();
		if (DEBUG)
			PackManager.v().writeOutput();
	}

	private void addSceneTransformer(final SourceSinkManager sourcesSinks, final Set<String> additionalSeeds) {
		Transform transform = new Transform("wjtp.ifds", new SceneTransformer() {
			protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
				AbstractInfoflowProblem problem;

				if (local) {
					problem = new InfoflowLocalProblem(sourcesSinks);
				} else {
					problem = new InfoflowProblem(sourcesSinks);
				}
				problem.setTaintWrapper(taintWrapper);
				problem.setPathTracking(pathTracking);
				problem.setComputeParamFlows(computeParamFlows);
				problem.setReturnIsSink(returnIsSink);
				problem.setStopAfterFirstFlow(stopAfterFirstFlow);

				// We have to look through the complete program to find sources
				// which are then taken as seeds.
				System.out.println("Looking for sources...");
				List<MethodOrMethodContext> eps = new ArrayList<MethodOrMethodContext>();
				eps.addAll(Scene.v().getEntryPoints());
				ReachableMethods reachableMethods = new ReachableMethods(Scene.v().getCallGraph(), eps.iterator(), null);
				reachableMethods.update();
				Map<String, String> classes = new HashMap<String, String>(10000);				
				for(Iterator<MethodOrMethodContext> iter = reachableMethods.listener(); iter.hasNext(); ) {
					SootMethod m = iter.next().method();
					if (m.hasActiveBody()) {
						// In Debug mode, we collect the Jimple bodies for
						// writing them to disk later
						if (DEBUG)
							if (classes.containsKey(m.getDeclaringClass().getName()))
								classes.put(m.getDeclaringClass().getName(), classes.get(m.getDeclaringClass().getName())
										+ m.getActiveBody().toString());
							else
								classes.put(m.getDeclaringClass().getName(), m.getActiveBody().toString());
						
						// Look for a source in the method
						PatchingChain<Unit> units = m.getActiveBody().getUnits();
						for (Unit u : units) {
						    if (sourcesSinks.isSourceMethod(u)){
						        problem.initialSeeds.add(u);
                                System.out.println("Source found: " + u);
						    }
						}
					}
				}
				
				// We optionally also allow additional seeds to be specified
				if (additionalSeeds != null)
					for (String meth : additionalSeeds) {
						SootMethod m = Scene.v().getMethod(meth);
						if (!m.hasActiveBody()) {
							System.err.println("Seed method " + m + " has no active body");
							continue;
						}
						problem.initialSeeds.add(m.getActiveBody().getUnits().getFirst());
					}

				// In Debug mode, we write the Jimple files to disk
				if (DEBUG)
					for (Entry<String, String> entry : classes.entrySet()) {
						try {
							stringToTextFile("JimpleFiles/" + entry.getKey() + ".jimple", entry.getValue());
						} catch (IOException e) {
							System.err.println("Could not write jimple file: " + e.getMessage());
							e.printStackTrace();
						}
					
					}
				
				if(problem.initialSeeds.isEmpty()){
					System.err.println("No Sources found!");
					return;
				}
				System.out.println("Source lookup done, found " + problem.initialSeeds.size() + " sources.");

				JimpleIFDSSolver<Abstraction, InterproceduralCFG<Unit, SootMethod>> solver =
						new JimpleIFDSSolver<Abstraction, InterproceduralCFG<Unit, SootMethod>>(problem, DEBUG);
				solver.solve();

				for (SootMethod ep : Scene.v().getEntryPoints()) {

					Unit ret = ep.getActiveBody().getUnits().getLast();
					System.err.println(ep.getActiveBody());

					System.err.println("----------------------------------------------");
					System.err.println("At end of: " + ep.getSignature());
					System.err.println(solver.ifdsResultsAt(ret).size() + " Variables (with "+ problem.results.size() +" source-to-sink connections):");
					System.err.println("----------------------------------------------");

					for (Abstraction l : solver.ifdsResultsAt(ret)) {
						System.err.println(l.getAccessPath() + " contains value from " + l.getSource());
					}
					System.err.println("---");
				}

				results = problem.results;
				if (results.getResults().isEmpty())
					System.out.println("No results found.");
				for (Entry<String, List<SourceInfo>> entry : results.getResults().entrySet()) {
					System.out.println("The sink " + entry.getKey() + " was called with values from the following sources:");
					for (SourceInfo source : entry.getValue()) {
						System.out.println("- " + source.getSource());
						if (source.getPath() != null && !source.getPath().isEmpty()) {
							System.out.println("\ton Path: ");
							for (String p : source.getPath()) {
								System.out.println("\t\t -> " + p);
							}
						}
					}
				}
			}

			private void stringToTextFile(String fileName, String contents) throws IOException {
				BufferedWriter wr = null;
				try {
					wr = new BufferedWriter(new FileWriter(fileName));
					wr.write(contents);
					wr.flush();
				}
				finally {
					if (wr != null)
						wr.close();
				}
			}
		});

		PackManager.v().getPack("wjtp").add(transform);
	}

	@Override
	public InfoflowResults getResults() {
		return results;
	}

	@Override
	public void setLocalInfoflow(boolean local) {
		this.local = local;
	}

	@Override
	public boolean isResultAvailable() {
		if (results == null) {
			return false;
		}
		return true;
	}
}