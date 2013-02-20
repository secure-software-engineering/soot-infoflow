package soot.jimple.infoflow.source;

import java.util.List;

import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;

public class DefaultSourceSinkManager implements SourceSinkManager {

	private List<String> sources;
	private List<String> sinks;
	
	public void setSources(List<String> sources){
		this.sources = sources;
	}
	
	public void setSinks(List<String> sinks){
		this.sinks = sinks;
	}

	public DefaultSourceSinkManager(List<String> sources, List<String> sinks){
		this.sources = sources;
		this.sinks = sinks;
	}
	
	@Override
	public boolean isSourceMethod(SootMethod sMethod) {
		return sources.contains(sMethod.toString());
	}

	@Override
	public boolean isSinkMethod(SootMethod sMethod) {
		return sinks.contains(sMethod.toString());
	}

    @Override
    public boolean isSourceMethod(Unit unit) {
        return unit instanceof Stmt && ((Stmt)unit).containsInvokeExpr() && 
                isSourceMethod(((Stmt)unit).getInvokeExpr().getMethod());
    }

    @Override
    public boolean isSinkMethod(Unit unit) {
        return unit instanceof Stmt && ((Stmt)unit).containsInvokeExpr() && 
                isSinkMethod(((Stmt)unit).getInvokeExpr().getMethod());
    }

}
