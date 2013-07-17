package soot.jimple.infoflow;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.Unit;
import soot.Value;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.tagkit.LineNumberTag;

/**
 * Class for collecting information flow results
 * 
 * @author Steven Arzt
 */
public class InfoflowResults {

    private final Logger logger = LoggerFactory.getLogger(getClass());
	
	/**
	 * Class for modeling information flowing out of a specific source
	 * @author Steven Arzt
	 */
	public class SourceInfo {
		private final Value source;
		private final Stmt context;
		private final List<Unit> path;
		
		public SourceInfo(Value source, Stmt context) {
			assert source != null;
			
			this.source = source;
			this.context = context;
			this.path = null;
		}
		
		public SourceInfo(Value source, Stmt context, List<Unit> path) {
			assert source != null;

			this.source = source;
			this.context = context;
			this.path = path;
		}

		public Value getSource() {
			return this.source;
		}
		
		public Stmt getContext() {
			return this.context;
		}
		
		public List<Unit> getPath() {
			return this.path;
		}

        @Override
        public String toString(){
            StringBuilder sb = new StringBuilder(context.toString());

            if (context.hasTag("LineNumberTag"))
                sb.append(" on line ").append(((LineNumberTag) context.getTag("LineNumberTag")).getLineNumber());

            return sb.toString();
        }

		@Override
		public int hashCode() {
			return 31 * this.source.hashCode()
					+ 7 * this.context.hashCode();
		}
		
		@Override
		public boolean equals(Object o) {
			if (super.equals(o))
				return true;
			if (o == null || !(o instanceof SourceInfo))
				return false;
			SourceInfo si = (SourceInfo) o;
			return this.source.equals(si.source)
					&& this.context.equals(si.context);
		}
	}
	
	/**
	 * Class for modeling information flowing into a specific source
	 * @author Steven Arzt
	 */
	public class SinkInfo {
		private final Value sink;
		private final Stmt context;
		
		public SinkInfo(Value sink, Stmt context) {
			assert sink != null;

			this.sink = sink;
			this.context = context;
		}
		
		public Value getSink() {
			return this.sink;
		}
		
		public Stmt getContext() {
			return this.context;
		}
		
		@Override
		public String toString() {
            StringBuilder sb = new StringBuilder(context.toString());

            if (context.hasTag("LineNumberTag"))
                sb.append(" on line ").append(((LineNumberTag)context.getTag("LineNumberTag")).getLineNumber());

			return sb.toString();
		}

		@Override
		public int hashCode() {
			return 31 * this.sink.hashCode()
					+ 7 * this.context.hashCode();
		}
		
		@Override
		public boolean equals(Object o) {
			if (super.equals(o))
				return true;
			if (o == null || !(o instanceof SinkInfo))
				return false;
			SinkInfo si = (SinkInfo) o;
			return this.sink.equals(si.sink)
					&& this.context.equals(si.context);
		}
	}
	
	private final Map<SinkInfo, Set<SourceInfo>> results = new ConcurrentHashMap<SinkInfo, Set<SourceInfo>>();
	
	public InfoflowResults() {
		
	}
	
	/**
	 * Gets the number of entries in this result object
	 * @return The number of entries in this result object
	 */
	public int size() {
		return this.results.size();
	}
	
	/**
	 * Gets whether this result object is empty, i.e. contains no information
	 * flows
	 * @return True if this result object is empty, otherwise false.
	 */
	public boolean isEmpty() {
		return this.results.isEmpty();
	}
	
	/**
	 * Checks whether this result object contains a sink that exactly matches the
	 * given value.
	 * @param sink The sink to check for
	 * @return True if this result contains the given value as a sink, otherwise
	 * false.
	 */
	public boolean containsSink(Value sink) {
		for (SinkInfo si : this.results.keySet())
			if (si.getSink().equals(sink))
				return true;
		return false;
	}
	
	/**
	 * Checks whether this result object contains a sink with the given method
	 * signature
	 * @param sinkSignature The method signature to check for
	 * @return True if there is a sink with the given method signature in this
	 * result object, otherwise false.
	 */
	public boolean containsSinkMethod(String sinkSignature) {
		return !findSinkByMethodSignature(sinkSignature).isEmpty();
	}

	public void addResult(Value sink, Stmt sinkStmt, Value source, Stmt sourceStmt) {
		this.addResult(new SinkInfo(sink, sinkStmt), new SourceInfo(source, sourceStmt));
	}
	
	public void addResult(Value sink, Stmt sinkStmt, Value source,
			Stmt sourceStmt, List<Unit> propagationPath) {
		this.addResult(new SinkInfo(sink, sinkStmt), new SourceInfo(source, sourceStmt, propagationPath));
	}

	public void addResult(Value sink, Stmt sinkContext, Value source,
			Stmt sourceStmt, List<Unit> propagationPath, Unit stmt) {
		List<Unit> newPropPath = new ArrayList<Unit>(propagationPath);
		newPropPath.add(stmt);
		this.addResult(new SinkInfo(sink, sinkContext),
				new SourceInfo(source, sourceStmt, newPropPath));
	}

	public void addResult(SinkInfo sink, SourceInfo source) {
		Set<SourceInfo> sourceInfo = this.results.get(sink);
		if (sourceInfo == null) {
			sourceInfo = new HashSet<SourceInfo>();
			this.results.put(sink, sourceInfo);
		}
		synchronized (sourceInfo) {
			sourceInfo.add(source);
		}
	}

	/**
	 * Gets all results in this object as a hash map.
	 * @return All results in this object as a hash map.
	 */
	public Map<SinkInfo, Set<SourceInfo>> getResults() {
		return this.results;
	}
	
	/**
	 * Checks whether there is a path between the given source and sink.
	 * @param sink The sink to which there may be a path
	 * @param source The source from which there may be a path
	 * @return True if there is a path between the given source and sink, false
	 * otherwise
	 */
	public boolean isPathBetween(Value sink, Value source) {
		Set<SourceInfo> sources = null;
		for(SinkInfo sI : this.results.keySet()){
			if(sI.getSink().equals(sink)){
				sources = this.results.get(sI);
				break;
			}
		}
		if (sources == null)
			return false;
		for (SourceInfo src : sources)
			if (src.source.equals(source))
				return true;
		return false;
	}
	
	/**
	 * Checks whether there is a path between the given source and sink.
	 * @param sink The sink to which there may be a path
	 * @param source The source from which there may be a path
	 * @return True if there is a path between the given source and sink, false
	 * otherwise
	 */
	public boolean isPathBetween(String sink, String source) {
		for (SinkInfo si : this.results.keySet())
			if (si.getSink().toString().equals(sink)) {
				Set<SourceInfo> sources = this.results.get(si);
				for (SourceInfo src : sources)
					if (src.source.toString().equals(source))
						return true;
		}
		return false;
	}

	/**
	 * Checks whether there is an information flow between the two
	 * given methods (specified by their respective Soot signatures). 
	 * @param sinkSignature The sink to which there may be a path
	 * @param sourceSignature The source from which there may be a path
	 * @return True if there is a path between the given source and sink, false
	 * otherwise
	 */
	public boolean isPathBetweenMethods(String sinkSignature, String sourceSignature) {
		List<SinkInfo> sinkVals = findSinkByMethodSignature(sinkSignature);
		for (SinkInfo si : sinkVals) {
			Set<SourceInfo> sources = this.results.get(si);
			if (sources == null)
				return false;
			for (SourceInfo src : sources)
				if (src.source instanceof InvokeExpr) {
					InvokeExpr expr = (InvokeExpr) src.source;
					if (expr.getMethod().getSignature().equals(sourceSignature))
						return true;
				}
		}
		return false;
	}

	/**
	 * Finds the entry for a sink method with the given signature
	 * @param sinkSignature The sink's method signature to look for
	 * @return The key of the entry with the given method signature if such an
	 * entry has been found, otherwise null.
	 */
	private List<SinkInfo> findSinkByMethodSignature(String sinkSignature) {
		List<SinkInfo> sinkVals = new ArrayList<SinkInfo>();
		for (SinkInfo si : this.results.keySet())
			if (si.getSink() instanceof InvokeExpr) {
				InvokeExpr expr = (InvokeExpr) si.getSink();
				if (expr.getMethod().getSignature().equals(sinkSignature))
					sinkVals.add(si);
			}
		return sinkVals;
	}

	/**
	 * Prints all results stored in this object to the standard output
	 */
	public void printResults() {
		for (SinkInfo sink : this.results.keySet()) {
			logger.info("Found a flow to sink {}, from the following sources:", sink);
			for (SourceInfo source : this.results.get(sink))
				logger.info("\t- {}", source.getSource());
		}
	}

}
