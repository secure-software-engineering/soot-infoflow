package soot.jimple.infoflow;

import heros.InterproceduralCFG;
import heros.solver.CountingThreadPoolExecutor;

import java.io.BufferedWriter;
import java.io.File;
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
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;

import soot.MethodOrMethodContext;
import soot.PackManager;
import soot.PatchingChain;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.Transform;
import soot.Unit;
import soot.jimple.Stmt;
import soot.jimple.infoflow.AbstractInfoflowProblem.PathTrackingMethod;
import soot.jimple.infoflow.InfoflowResults.SinkInfo;
import soot.jimple.infoflow.InfoflowResults.SourceInfo;
import soot.jimple.infoflow.config.IInfoflowConfig;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.entryPointCreators.DefaultEntryPointCreator;
import soot.jimple.infoflow.entryPointCreators.IEntryPointCreator;
import soot.jimple.infoflow.heros.InfoflowSolver;
import soot.jimple.infoflow.source.DefaultSourceSinkManager;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.jimple.infoflow.util.SootMethodRepresentationParser;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.jimple.toolkits.ide.JimpleIFDSSolver;
import soot.jimple.toolkits.scalar.ConstantPropagatorAndFolder;
import soot.options.Options;
/**
 * main infoflow class which triggers the analysis and offers method to customize it.
 *
 */
public class Infoflow implements IInfoflow {

	private static boolean debug = true;
	private static int accessPathLength = 5;
	private InfoflowResults results;

	private final String androidPath;
	private final boolean forceAndroidJar;
	private ITaintPropagationWrapper taintWrapper;
	private PathTrackingMethod pathTracking = PathTrackingMethod.NoTracking;
	private IInfoflowConfig sootConfig;
	private boolean stopAfterFirstFlow = false;
	private boolean inspectSinks = true;

    private BiDirICFGFactory icfgFactory = new DefaultBiDiICFGFactory();
    private List<Transform> preProcessors = Collections.emptyList();

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

	public void setTaintWrapper(ITaintPropagationWrapper wrapper) {
		taintWrapper = wrapper;
	}

	public static void setDebug(boolean debugflag) {
		debug = debugflag;
	}

	@Override
	public void setInspectSinks(boolean inspect){
		inspectSinks = inspect;
	}
	
	@Override
	public void setPathTracking(PathTrackingMethod method) {
		this.pathTracking = method;
	}
	
	public void setSootConfig(IInfoflowConfig config){
		sootConfig = config;
	}
	
	@Override
	public void setStopAfterFirstFlow(boolean stopAfterFirstFlow) {
		this.stopAfterFirstFlow = stopAfterFirstFlow;
	}

    @Override
    public void setIcfgFactory(BiDirICFGFactory factory){
        this.icfgFactory = factory;
    }

    @Override
    public void setPreProcessors(List<Transform> preprocessors){
        this.preProcessors = preprocessors;
    }
	
	@Override
	public void computeInfoflow(String path, IEntryPointCreator entryPointCreator,
			List<String> entryPoints, List<String> sources, List<String> sinks) {
		this.computeInfoflow(path, entryPointCreator, entryPoints,
				new DefaultSourceSinkManager(sources, sinks));
	}
	
	@Override
	public void computeInfoflow(String path, List<String> entryPoints, List<String> sources, List<String> sinks) {
		this.computeInfoflow(path, new DefaultEntryPointCreator(), entryPoints, new DefaultSourceSinkManager(sources, sinks));
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
	private void initializeSoot(String path, Set<String> classes, ISourceSinkManager sourcesSinks) {
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
	private void initializeSoot(String path, Set<String> classes, ISourceSinkManager sourcesSinks, String extraSeed) {
		// reset Soot:
		soot.G.reset();
		
		// add SceneTransformer which calculates and prints infoflow
		Set<String> seeds = Collections.emptySet();
		if (extraSeed != null && !extraSeed.isEmpty())
			seeds = Collections.singleton(extraSeed);
		addSceneTransformer(sourcesSinks, seeds);

		Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_allow_phantom_refs(true);
		if (debug)
			Options.v().set_output_format(Options.output_format_jimple);
		else
			Options.v().set_output_format(Options.output_format_none);
		Options.v().set_whole_program(true);
		Options.v().set_soot_classpath(path);
		Options.v().set_process_dir(Arrays.asList(classes.toArray()));

		if (extraSeed == null || extraSeed.isEmpty())
			Options.v().setPhaseOption("cg.spark", "on");
		else
			Options.v().setPhaseOption("cg.spark", "vta:true");
		// do not merge variables (causes problems with PointsToSets)
		Options.v().setPhaseOption("jb.ulp", "off");
		
		Options.v().setPhaseOption("cg", "trim-clinit:false");
		
		if (!this.androidPath.isEmpty()) {
			Options.v().set_src_prec(Options.src_prec_apk);
			if (this.forceAndroidJar)
				soot.options.Options.v().set_force_android_jar(this.androidPath);
			else
				soot.options.Options.v().set_android_jars(this.androidPath);
		} else
			Options.v().set_src_prec(Options.src_prec_java);
		
		//at the end of setting: load user settings:
		if (sootConfig != null)
			sootConfig.setSootOptions(Options.v());
		
		// load all entryPoint classes with their bodies
		Scene.v().loadNecessaryClasses();
		boolean hasClasses = false;
		for (String className : classes) {
			SootClass c = Scene.v().forceResolve(className, SootClass.BODIES);
			if (c != null){
				c.setApplicationClass();
				if(!c.isPhantomClass() && !c.isPhantom())
					hasClasses = true;
			}
		}
		if (!hasClasses) {
			System.out.println("Only phantom classes loaded, skipping analysis...");
			return;
		}

	}

	@Override
	public void computeInfoflow(String path, IEntryPointCreator entryPointCreator,
			List<String> entryPoints, ISourceSinkManager sourcesSinks) {
		results = null;
		if (sourcesSinks == null) {
			System.out.println("Error: sources are empty!");
			return;
		}
	
		initializeSoot(path,
				SootMethodRepresentationParser.v().parseClassNames(entryPoints, false).keySet(),
				sourcesSinks);

		// entryPoints are the entryPoints required by Soot to calculate Graph - if there is no main method,
		// we have to create a new main method and use it as entryPoint and store our real entryPoints
		Scene.v().setEntryPoints(Collections.singletonList(entryPointCreator.createDummyMain(entryPoints)));
		PackManager.v().runPacks();
		if (debug)
			PackManager.v().writeOutput();
	}


	@Override
	public void computeInfoflow(String path, String entryPoint, ISourceSinkManager sourcesSinks) {
		results = null;
		if (sourcesSinks == null) {
			System.out.println("Error: sources are empty!");
			return;
		}

		// parse classNames as String and methodNames as string in soot representation
		HashMap<String, List<String>> classes = SootMethodRepresentationParser.v().parseClassNames
						(Collections.singletonList(entryPoint), false);

		initializeSoot(path, classes.keySet(), sourcesSinks, entryPoint);
		
		if (debug) {
			for (List<String> methodList : classes.values()) {
				for (String methodSignature : methodList) {
					if (Scene.v().containsMethod(methodSignature)) {
						SootMethod method = Scene.v().getMethod(methodSignature);
						System.err.println(method.retrieveActiveBody().toString());
					}
				}
			}
		}

		if (!Scene.v().containsMethod(entryPoint)){
			System.err.println("Entry point not found: " + entryPoint);
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
		if (debug)
			PackManager.v().writeOutput();
	}

	private void addSceneTransformer(final ISourceSinkManager sourcesSinks, final Set<String> additionalSeeds) {
		Transform transform = new Transform("wjtp.ifds", new SceneTransformer() {
			protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
				// Perform a constant propagation to make it easier subsequent steps to
				// find e.g. layout IDs
				System.out.println("Running constant propagation...");
				for (SootClass sc : Scene.v().getClasses())
					for (SootMethod sm : sc.getMethods())
						if (sm.isConcrete())
							ConstantPropagatorAndFolder.v().transform(sm.retrieveActiveBody());
				System.out.println("Constant propagation done.");
				
				System.out.println("Callgraph has " + Scene.v().getCallGraph().size() + " edges");
				InfoflowProblem forwardProblem  = new InfoflowProblem(icfgFactory.buildBiDirICFG(), sourcesSinks);
				forwardProblem.setTaintWrapper(taintWrapper);
				forwardProblem.setPathTracking(pathTracking);
				forwardProblem.setStopAfterFirstFlow(stopAfterFirstFlow);


				// We have to look through the complete program to find sources
				// which are then taken as seeds.
				int sinkCount = 0;
				System.out.println("Looking for sources and sinks...");

				List<MethodOrMethodContext> eps = new ArrayList<MethodOrMethodContext>(Scene.v().getEntryPoints());
				ReachableMethods reachableMethods = new ReachableMethods(Scene.v().getCallGraph(), eps.iterator(), null);
				reachableMethods.update();
				Map<String, String> classes = new HashMap<String, String>(10000);
				for(Iterator<MethodOrMethodContext> iter = reachableMethods.listener(); iter.hasNext(); ) {
					SootMethod m = iter.next().method();
					if (m.hasActiveBody()) {
						// In Debug mode, we collect the Jimple bodies for
						// writing them to disk later
						if (debug)
							if (classes.containsKey(m.getDeclaringClass().getName()))
								classes.put(m.getDeclaringClass().getName(), classes.get(m.getDeclaringClass().getName())
										+ m.getActiveBody().toString());
							else
								classes.put(m.getDeclaringClass().getName(), m.getActiveBody().toString());
						
						// Look for a source in the method. Also look for sinks. If we
						// have no sink in the program, we don't need to perform any
						// analysis
						PatchingChain<Unit> units = m.getActiveBody().getUnits();
						for (Unit u : units) {
							Stmt s = (Stmt) u;
							if (sourcesSinks.isSource(s, forwardProblem.interproceduralCFG())) {
								forwardProblem.initialSeeds.add(u);

								if (debug)
									System.out.println("Source found: " + u);
							}
							if (sourcesSinks.isSink(s, forwardProblem.interproceduralCFG())) {
								if (debug)
									System.out.println("Sink found: " + u);
								sinkCount++;
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
						forwardProblem.initialSeeds.add(m.getActiveBody().getUnits().getFirst());
					}

				// In Debug mode, we write the Jimple files to disk
				if (debug){
					File dir = new File("JimpleFiles");
					if(!dir.exists()){
						dir.mkdir();
					}
					for (Entry<String, String> entry : classes.entrySet()) {
						try {
							stringToTextFile(new File(".").getAbsolutePath() + System.getProperty("file.separator") +"JimpleFiles"+ System.getProperty("file.separator") + entry.getKey() + ".jimple", entry.getValue());
						} catch (IOException e) {
							System.err.println("Could not write jimple file: " + e.getMessage());
							e.printStackTrace();
						}
					
					}
				}

				if (forwardProblem.initialSeeds.isEmpty() || sinkCount == 0){
					System.err.println("No sources or sinks found, aborting analysis");
					return;
				}

				JimpleIFDSSolver<Abstraction, InterproceduralCFG<Unit, SootMethod>> forwardSolver;
				System.out.println("Source lookup done, found " + forwardProblem.initialSeeds.size() + " sources.");

				CountingThreadPoolExecutor executor = new CountingThreadPoolExecutor(1, forwardProblem.numThreads(), 30, TimeUnit.SECONDS, new LinkedBlockingQueue<Runnable>());
				forwardSolver = new InfoflowSolver(forwardProblem, debug, executor);
				BackwardsInfoflowProblem backProblem = new BackwardsInfoflowProblem();
				InfoflowSolver backSolver = new InfoflowSolver(backProblem, debug, executor);
				forwardProblem.setBackwardSolver(backSolver);
				forwardProblem.setDebug(debug);
				forwardProblem.setInspectSinks(inspectSinks);
				
				backProblem.setForwardSolver((InfoflowSolver) forwardSolver);
				backProblem.setTaintWrapper(taintWrapper);
				backProblem.setDebug(debug);

				forwardSolver.solve();

				for (SootMethod ep : Scene.v().getEntryPoints()) {
					Unit ret = ep.getActiveBody().getUnits().getLast();

					System.err.println("----------------------------------------------");
					System.err.println("At end of: " + ep.getSignature());
					System.err.println(forwardSolver.ifdsResultsAt(ret).size() + " Variables (with " + forwardProblem.results.size() + " source-to-sink connections):");
					System.err.println("----------------------------------------------");

					for (Abstraction l : forwardSolver.ifdsResultsAt(ret)) {
						System.err.println(l.getAccessPath() + " contains value from " + l.getSource());
					}
					System.err.println("---");
				}


				results = forwardProblem.results;
				if (results.getResults().isEmpty())
					System.out.println("No results found.");

				for (Entry<SinkInfo, Set<SourceInfo>> entry : results.getResults().entrySet()) {
					System.out.println("The sink " + entry.getKey() + " was called with values from the following sources:");
					for (SourceInfo source : entry.getValue()) {
						System.out.println("- " + source.getSource());
						if (source.getPath() != null && !source.getPath().isEmpty()) {
							System.out.println("\ton Path: ");
							for (Unit p : source.getPath()) {
								System.out.println("\t\t -> " + p);
							}
						}
					}
				}
			}

			
		});

        for (Transform tr : preProcessors){
            PackManager.v().getPack("wjtp").add(tr);
        }
		PackManager.v().getPack("wjtp").add(transform);
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

	@Override
	public InfoflowResults getResults() {
		return results;
	}

	@Override
	public boolean isResultAvailable() {
		if (results == null) {
			return false;
		}
		return true;
	}

	
	public static int getAccessPathLength() {
		return accessPathLength;
	}
	
	@Override
	public void setAccessPathLength(int accessPathLength) {
		Infoflow.accessPathLength = accessPathLength;
	}
}
