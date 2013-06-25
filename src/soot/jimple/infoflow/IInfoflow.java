package soot.jimple.infoflow;

import java.util.List;

import soot.SootMethod;
import soot.Transform;
import soot.Transformer;
import soot.Unit;
import soot.jimple.infoflow.AbstractInfoflowProblem.PathTrackingMethod;
import soot.jimple.infoflow.entryPointCreators.IEntryPointCreator;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
/**
 * interface for the main infoflow class
 *
 */
public interface IInfoflow {
	
	/**
	 * Sets the taint wrapper for deciding on taint propagation through black-box
	 * methods
	 * @param wrapper The taint wrapper object that decides on how information is
	 * propagated through black-box methods
	 */
	public void setTaintWrapper(ITaintPropagationWrapper wrapper);

	/**
	 * Sets whether and how the paths between the sources and sinks shall be
	 * tracked
	 * @param method The method for tracking data flow paths through the
	 * program.
	 */
	public void setPathTracking(PathTrackingMethod method);
	
	/**
	 * Sets whether the information flow analysis shall stop after the first
	 * flow has been found
	 * @param stopAfterFirstFlow True if the analysis shall stop after the
	 * first flow has been found, otherwise false.
	 */
	public void setStopAfterFirstFlow(boolean stopAfterFirstFlow);


    /**
     * Sets the interprocedural CFG to be used by the InfoFlowProblem
     * @param factory the interprocedural control flow factory
     */
    public void setIcfgFactory(BiDirICFGFactory factory);

    /**
     * List of preprocessors that need to be executed in order before
     * the information flow.
     * @param preprocessors the pre-processors
     */
    public void setPreProcessors(List<Transform> preprocessors);

	/**
	 * Computes the information flow on a list of entry point methods. This list
	 * is used to construct an artificial main method following the Android
	 * life cycle for all methods that are detected to be part of Android's
	 * application infrastructure (e.g. android.app.Activity.onCreate)
	 * @param path the path to the main folder of the (unpacked) class files
	 * @param entryPointCreator the entry point creator to use for generating the dummy
	 * main method
	 * @param entryPoints the entryPoints (string conforms to SootMethod representation)
	 * @param sources list of source class+method (as string conforms to SootMethod representation)
	 * @param sinks list of sink class+method (as string conforms to SootMethod representation)
	 */
	public void computeInfoflow(String path, IEntryPointCreator entryPointCreator,
			List<String> entryPoints, List<String> sources, List<String> sinks);
	
	/**
	 * Computes the information flow on a list of entry point methods. This list
	 * is used to construct an artificial main method following the Android
	 * life cycle for all methods that are detected to be part of Android's
	 * application infrastructure (e.g. android.app.Activity.onCreate)
	 * @param path the path to the main folder of the (unpacked) class files
	 * @param entryPoints the entryPoints (string conforms to SootMethod representation)
	 * @param sources list of source class+method (as string conforms to SootMethod representation)
	 * @param sinks list of sink class+method (as string conforms to SootMethod representation)
	 */
	public void computeInfoflow(String path, List<String> entryPoints, List<String> sources,
			List<String> sinks);

	/**
	 * Computes the information flow on a single method. This method is
	 * directly taken as the entry point into the program, even if it is an
	 * instance method.
	 * @param path the path to the main folder of the (unpacked) class files
	 * @param entryPoint the main method to analyze
	 * @param sources list of source class+method (as string conforms to SootMethod representation)
	 * @param sinks list of sink class+method (as string conforms to SootMethod representation)
	 */
	public void computeInfoflow(String path, String entryPoint, List<String> sources, List<String> sinks);

	/**
	 * Computes the information flow on a list of entry point methods. This list
	 * is used to construct an artificial main method following the Android
	 * life cycle for all methods that are detected to be part of Android's
	 * application infrastructure (e.g. android.app.Activity.onCreate)
	 * @param path the path to the main folder of the (unpacked) class files
	 * @param entryPointCreator the entry point creator to use for generating the dummy
	 * main method
	 * @param entryPoints the entryPoints (string conforms to SootMethod representation)
	 * @param sourcesSinks manager class for identifying sources and sinks in the source code
	 */
	public void computeInfoflow(String path, IEntryPointCreator entryPointCreator,
			List<String> entryPoints, ISourceSinkManager sourcesSinks);

	/**
	 * Computes the information flow on a single method. This method is
	 * directly taken as the entry point into the program, even if it is an
	 * instance method.
	 * @param path the path to the main folder of the (unpacked) class files
	 * @param entryPoint the main method to analyze
	 * @param sourcesSinks manager class for identifying sources and sinks in the source code
	 */
	public void computeInfoflow(String path, String entryPoint, ISourceSinkManager sourcesSinks);

	/**
	 * getResults returns the results found by the analysis
	 * @return the results
	 */
	public InfoflowResults getResults();
	
	/**
	 * A result is available if the analysis has finished - so if this method returns false the
	 * analysis has not finished yet or was not started (e.g. no sources or sinks found)
	 * @return boolean that states if a result is available
	 */
	public boolean isResultAvailable();
	
	/**
	 * default: inspectSinks is set to true, this means sinks are analyzed as well.
	 * If inspectSinks is set to false, then the analysis does not propagate values into 
	 * the sink method. 
	 * @param inspect boolean that determines the inspectSink option
	 */
	public void setInspectSinks(boolean inspect);
	
	/**
	 * sets the depth of the access path that are tracked
	 * @param accessPathLength the maximum value of an access path. If it gets longer than
	 *  this value, it is truncated and all following fields are assumed as tainted 
	 *  (which is imprecise but gains performance)
	 *  Default value is 5.
	 */
	public void setAccessPathLength(int accessPathLength);
	
}
