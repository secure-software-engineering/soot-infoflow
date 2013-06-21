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

import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Value;
import soot.jimple.AssignStmt;
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
public class EasyTaintWrapper implements ITaintPropagationWrapper {
	private final Map<String, List<String>> classList;
	private final Map<String, List<String>> excludeList;
	private final Map<String, List<String>> killList;

	public EasyTaintWrapper(HashMap<String, List<String>> classList){
		this.classList = classList;
		this.excludeList = new HashMap<String, List<String>>();
		this.killList = new HashMap<String, List<String>>();
	}
	
	public EasyTaintWrapper(HashMap<String, List<String>> classList,
			HashMap<String, List<String>> excludeList) {
		this.classList = classList;
		this.excludeList = excludeList;
		this.killList = new HashMap<String, List<String>>();
	}

	public EasyTaintWrapper(HashMap<String, List<String>> classList,
			HashMap<String, List<String>> excludeList,
			HashMap<String, List<String>> killList) {
		this.classList = classList;
		this.excludeList = excludeList;
		this.killList = killList;
	}

    public EasyTaintWrapper(String f) throws IOException{
        this(new File(f));
    }

	public EasyTaintWrapper(File f) throws IOException{
		BufferedReader reader = null;
		try{
			FileReader freader = new FileReader(f);
			reader = new BufferedReader(freader);
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
					else
						methodList.add(line);
				line = reader.readLine();
			}
			this.classList = SootMethodRepresentationParser.v().parseClassNames(methodList, true);
			this.excludeList = SootMethodRepresentationParser.v().parseClassNames(excludeList, true);
			this.killList = SootMethodRepresentationParser.v().parseClassNames(killList, true);
			System.out.println("Loaded wrapper entries for " + classList.size() + " classes " +
					"and " + excludeList.size() + " exclusions.");
		}
		finally {
			if (reader != null)
				reader.close();
		}
	}
	
	@Override
	public boolean supportsTaintWrappingForClass(SootClass c) {
		// We can't tell without knowing whether the base object is tainted, so
		// we accept all objects here and filter later on
		return true;
	}

	@Override
	public Set<AccessPath> getTaintsForMethod(Stmt stmt, AccessPath taintedPath) {
		if (!stmt.containsInvokeExpr())
			return Collections.emptySet();

		Set<AccessPath> taints = new HashSet<AccessPath>();

		if (stmt.getInvokeExpr() instanceof InstanceInvokeExpr) {
			InstanceInvokeExpr iiExpr = (InstanceInvokeExpr) stmt.getInvokeExpr();
			
			if (taintedPath.getPlainValue().equals(iiExpr.getBase())) {
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
				
		//if param is tainted && classList contains classname && if list. contains signature of method -> add propagation
		for (Value param : stmt.getInvokeExpr().getArgs())
			if (taintedPath.getPlainValue().equals(param)) {
				SootMethod method = stmt.getInvokeExpr().getMethod();
				List<String> methodList = getMethodsForClass(method.getDeclaringClass());
			
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
					
					// The parameter as such stays tainted
					taints.add(taintedPath);
			}
		}
		
		return taints;
	}
	
	private List<String> getMethodsForClass(SootClass c){
		List<String> methodList = new LinkedList<String>();
		if(classList.containsKey(c.getName())){
			methodList.addAll(classList.get(c.getName()));
		}
		
		if(!c.isInterface()) {
			// We have to walk up the hierarchy to also include all methods
			// registered for superclasses
			List<SootClass> superclasses = Scene.v().getActiveHierarchy().getSuperclassesOf(c);
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

	@Override
	public boolean isExclusive(Stmt stmt, AccessPath taintedPath) {
		SootMethod method = stmt.getInvokeExpr().getMethod();
		return getMethodsForClass(method.getDeclaringClass()).contains(method.getSubSignature());
	}

}
