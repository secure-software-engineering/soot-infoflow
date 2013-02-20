package soot.jimple.infoflow.source;

import soot.SootMethod;
import soot.Unit;

public interface SourceSinkManager {

    public abstract boolean isSourceMethod(Unit unit);
    public abstract boolean isSinkMethod(Unit unit);
    
    @Deprecated
	public abstract boolean isSourceMethod(SootMethod sMethod);
    @Deprecated
	public abstract boolean isSinkMethod(SootMethod sMethod);

}
