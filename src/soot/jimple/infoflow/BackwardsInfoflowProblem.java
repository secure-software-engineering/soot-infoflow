package soot.jimple.infoflow;

import heros.FlowFunction;
import heros.FlowFunctions;
import heros.InterproceduralCFG;
import heros.flowfunc.Identity;
import heros.solver.PathEdge;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import soot.EquivalentValue;
import soot.Local;
import soot.NullType;
import soot.PointsToAnalysis;
import soot.PrimType;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.NewExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.heros.InfoflowSolver;
import soot.jimple.infoflow.nativ.DefaultNativeCallHandler;
import soot.jimple.infoflow.nativ.NativeCallHandler;
import soot.jimple.infoflow.source.SourceSinkManager;
import soot.jimple.infoflow.util.BaseSelector;
import soot.jimple.infoflow.util.ITaintPropagationWrapper;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.ide.DefaultJimpleIFDSTabulationProblem;
import soot.jimple.toolkits.ide.icfg.BackwardsInterproceduralCFG;

public class BackwardsInfoflowProblem extends DefaultJimpleIFDSTabulationProblem<Abstraction, InterproceduralCFG<Unit,SootMethod>>{
	Set<Unit> initialSeeds = new HashSet<Unit>();
	final HashMap<String, List<String>> results;
	final SourceSinkManager sourceSinkManager;
	Abstraction zeroValue;
	InfoflowSolver fSolver;
	ITaintPropagationWrapper taintWrapper;
	
	public void setTaintWrapper(ITaintPropagationWrapper wrapper){
		taintWrapper = wrapper;
	}
	
	public BackwardsInfoflowProblem(InterproceduralCFG<Unit,SootMethod> icfg, SourceSinkManager manager) {
		super(icfg);
		results = new HashMap<String, List<String>>();
		sourceSinkManager = manager;
	}
	
	public BackwardsInfoflowProblem(SourceSinkManager manager) {
		super(new BackwardsInterproceduralCFG());
		results = new HashMap<String, List<String>>();
		sourceSinkManager = manager;
	}
	
	public void setForwardSolver(InfoflowSolver forwardSolver){
		fSolver = forwardSolver;
	}

	@Override
	public Set<Unit> initialSeeds() {
		return initialSeeds;
	}

	@Override
	protected Abstraction createZeroValue() {
		if (zeroValue == null)
			return new Abstraction(new EquivalentValue(new JimpleLocal("zero", NullType.v())), null, null);

		return zeroValue;
	}
	
	@Override
	public boolean autoAddZero() {
		return false;
	}
	
	@Override
	public boolean followReturnsPastSeeds() {
		return true;
	}

	@Override
	public FlowFunctions<Unit, Abstraction, SootMethod> createFlowFunctionsFactory() {
		return new FlowFunctions<Unit, Abstraction, SootMethod>() {

			@Override
			public FlowFunction<Abstraction> getNormalFlowFunction(final Unit src, final Unit dest) {
				// taint is propagated with assignStmt
				if (src instanceof AssignStmt) {
					AssignStmt assignStmt = (AssignStmt) src;
					Value right = assignStmt.getRightOp();
					Value left = assignStmt.getLeftOp();

					// find rightValue (remove casts):
					right = BaseSelector.selectBase(right, false);

					// find appropriate leftValue:
					left = BaseSelector.selectBase(left, true);

					final Value leftValue = left;
					final Value rightValue = right;
					final Unit srcUnit = src;

					return new FlowFunction<Abstraction>() {

						@Override
						public Set<Abstraction> computeTargets(Abstraction source) {
							boolean addRightValue = false;
							boolean keepAllFieldTaintStar = true;
							Set<Abstraction> res = new HashSet<Abstraction>();
							PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
							// shortcuts:
							// on NormalFlow taint cannot be created:
							if (source.equals(zeroValue)) {
								return Collections.emptySet();
							}
							//if we have the tainted value on the right side of the assignment, we have to start a new forward task:
							if(rightValue instanceof InstanceFieldRef){
								InstanceFieldRef ref = (InstanceFieldRef) rightValue;
								
								if(!(ref.getField().getType() instanceof PrimType) &&  ref.getBase().equals(source.getAccessPath().getPlainValue()) && ref.getField().getName().equals(source.getAccessPath().getField())){
									Abstraction abs = new Abstraction(new EquivalentValue(leftValue), source.getSource(), interproceduralCFG().getMethodOf(srcUnit),keepAllFieldTaintStar && source.getAccessPath().isOnlyFieldsTainted());
									//this should be successor (but successor is reversed because backwardsproblem, so predecessor is required.. -> but this should work, too:
									fSolver.processEdge(new PathEdge<Unit, Abstraction, SootMethod>(abs, srcUnit, abs));
									
								}
							}else{
								
								if(!(rightValue.getType() instanceof PrimType) && rightValue.equals(source.getAccessPath().getPlainValue())){
									Abstraction abs = new Abstraction(source.getAccessPath().copyWithNewValue(leftValue), source.getSource(), interproceduralCFG().getMethodOf(srcUnit));
									fSolver.processEdge(new PathEdge<Unit, Abstraction, SootMethod>(abs, srcUnit, abs));
									
								}
							}
							//termination shortcut:
							if(leftValue.equals(source.getAccessPath().getPlainValue()) && rightValue instanceof NewExpr){
								return Collections.emptySet();
							}
							
							//if we have the tainted value on the left side of the assignment, we have to track the right side of the assignment
							
							//we do not track StaticFieldRefs during BackwardAnalysis:
							if (!(leftValue instanceof StaticFieldRef)) {
								// if both are fields, we have to compare their fieldName via equals and their bases via PTS
								// might happen that source is local because of max(length(accesspath)) == 1
								if (leftValue instanceof InstanceFieldRef) {
									InstanceFieldRef leftRef = (InstanceFieldRef) leftValue;
									Local leftBase = (Local) leftRef.getBase();
									Local sourceBase = (Local) source.getAccessPath().getPlainValue();
									if (leftBase.equals(sourceBase)) {
										if (source.getAccessPath().isInstanceFieldRef()) {
											if (leftRef.getField().getName().equals(source.getAccessPath().getField())) {
												addRightValue = true;
											}
										} else {
											addRightValue = true;
											keepAllFieldTaintStar = false;
										}
									}
									// indirect taint propagation:
									// if leftValue is local and source is instancefield of this local:
								}else if (leftValue instanceof Local && source.getAccessPath().isInstanceFieldRef()) {
									Local base = (Local) source.getAccessPath().getPlainValue(); // ?
									if (leftValue.equals(base)) { 
										if (rightValue instanceof Local) {
											res.add(new Abstraction(source.getAccessPath().copyWithNewValue(rightValue), source.getSource(), source.getCorrespondingMethod()));
										} else {
											// access path length = 1 - taint entire value if left is field reference
											res.add(new Abstraction(new EquivalentValue(rightValue), source.getSource(), source.getCorrespondingMethod(), true));
										}
									}
								} else if (leftValue instanceof ArrayRef) {
									Local leftBase = (Local) ((ArrayRef) leftValue).getBase();
									if (leftBase.equals(source.getAccessPath().getPlainValue()) || (source.getAccessPath().isLocal() && pta.reachingObjects(leftBase).hasNonEmptyIntersection(pta.reachingObjects((Local) source.getAccessPath().getPlainValue())))) {
										addRightValue = true;
									}
									// generic case, is true for Locals, ArrayRefs that are equal etc..
								}else if (leftValue.equals(source.getAccessPath().getPlainValue())) {
									addRightValue = true; 
								}
							}
							// if one of them is true -> add rightValue
							if (addRightValue) { 
								res.add(new Abstraction(new EquivalentValue(rightValue), source.getSource(), interproceduralCFG().getMethodOf(srcUnit), keepAllFieldTaintStar && source.getAccessPath().isOnlyFieldsTainted()));
								return res;
							}
							if(!res.isEmpty()){ 
								return res;
							}else{
								return Collections.singleton(source);
							}

						}
					};

				}
				return Identity.v();
			}

			@Override
			public FlowFunction<Abstraction> getCallFlowFunction(Unit src, final SootMethod dest) {
				final SootMethod method = dest;
				final Unit callUnit = src;

				return new FlowFunction<Abstraction>() {

					@Override
					public Set<Abstraction> computeTargets(Abstraction source) {
						if (source.equals(zeroValue)) {
							return Collections.emptySet();
						}
						
						Set<Abstraction> res = new HashSet<Abstraction>();

						// if the returned value is tainted  - taint values from return statements
						if (callUnit instanceof DefinitionStmt) {
							DefinitionStmt defnStmt = (DefinitionStmt) callUnit;
							Value leftOp = defnStmt.getLeftOp();
							if (leftOp.equals(source.getAccessPath().getPlainValue())) {
								//look for returnStmts:
								for(Unit u : method.getActiveBody().getUnits()){
									if(u instanceof ReturnStmt){
										ReturnStmt rStmt = (ReturnStmt) u;
										res.add(new Abstraction(source.getAccessPath().copyWithNewValue(rStmt.getOp()), source.getSource(), interproceduralCFG().getMethodOf(callUnit)));
									}
								}
							}
						}

						// easy: static
						if (source.getAccessPath().isStaticFieldRef()) {
							res.add(source);
						}

						// checks: this/fields

						Value sourceBase = source.getAccessPath().getPlainValue();
						Stmt iStmt = (Stmt) callUnit;
						Local thisL = null;
						if (!method.isStatic()) {
							thisL = method.getActiveBody().getThisLocal();
						}
						//TODO: wie NullConstant
						if (thisL != null) {
							InstanceInvokeExpr iIExpr = (InstanceInvokeExpr) iStmt.getInvokeExpr();
							if (iIExpr.getBase().equals(sourceBase)) {
								// there is only one case in which this must be added, too: if the caller-Method has the same thisLocal - check this:
								
									boolean param = false;
									// check if it is not one of the params (then we have already fixed it)
									for (int i = 0; i < method.getParameterCount(); i++) {
										if (iStmt.getInvokeExpr().getArg(i).equals(sourceBase)) { 
											param = true;
										}
									}
									if (!param) {
										if (callUnit instanceof Stmt) {
											Stmt stmt = (Stmt) callUnit;
											if (stmt.getInvokeExpr() instanceof InstanceInvokeExpr) {
												
												res.add(new Abstraction(source.getAccessPath().copyWithNewValue(thisL), source.getSource(), interproceduralCFG().getMethodOf(callUnit)));
											}
										}
									}
								//TODO: maybe params?
							}
						}

						return res;
					}

				};
			}

			@Override
			public FlowFunction<Abstraction> getReturnFlowFunction(Unit callSite, final SootMethod callee, Unit exitStmt, final Unit retSite) {
				final Stmt stmt = (Stmt) callSite;
				final InvokeExpr ie = stmt.getInvokeExpr();
				final List<Value> callArgs = ie.getArgs();
				final List<Value> paramLocals = new ArrayList<Value>();
				for (int i = 0; i < callee.getParameterCount(); i++) {
					paramLocals.add(callee.getActiveBody().getParameterLocal(i));
				}
				
				return new FlowFunction<Abstraction>() {

					@Override
					public Set<Abstraction> computeTargets(Abstraction source) {
						if(taintWrapper != null && taintWrapper.supportsBackwardWrapping() && taintWrapper.supportsTaintWrappingForClass(ie.getMethod().getDeclaringClass())){
							//taint is propagated in CallToReturnFunction, so we do not need any taint here:
							return Collections.emptySet();
						}
						if (source.equals(zeroValue)) {
							return Collections.emptySet();
						}

						Value base = source.getAccessPath().getPlainValue();
						Set<Abstraction> res = new HashSet<Abstraction>();
						// if taintedobject is instancefieldRef we have to check if the object is delivered..
						if (source.getAccessPath().isInstanceFieldRef()) {

							// second, they might be changed as param - check this

							// first, instancefieldRefs must be propagated if they come from the same class:
							if (callee.getActiveBody().getThisLocal().equals(base) && ie instanceof InstanceInvokeExpr) {
								InstanceInvokeExpr vie = (InstanceInvokeExpr) ie;
								res.add(new Abstraction(source.getAccessPath().copyWithNewValue(vie.getBase()), source.getSource(), callee));	
							}
						}

						// check if param is tainted:
						for (int i = 0; i < callArgs.size(); i++) {
							if (paramLocals.get(i).equals(base)) {
								Abstraction abs = new Abstraction(source.getAccessPath().copyWithNewValue(callArgs.get(i)), source.getSource(), callee);
								res.add(abs);
							}
						}

						// staticfieldRefs must be analyzed even if they are not part of the params:
						if (source.getAccessPath().isStaticFieldRef()) {
							res.add(source);
						}
						
						return res;
					}
				};		
			}

			@Override
			public FlowFunction<Abstraction> getCallToReturnFlowFunction(Unit call, Unit returnSite) {
				final Unit unit = returnSite;
				// special treatment for native methods:
				if (call instanceof Stmt) {
					final Stmt iStmt = (Stmt) call;
					final List<Value> callArgs = iStmt.getInvokeExpr().getArgs();

					return new FlowFunction<Abstraction>() {

						@Override
						public Set<Abstraction> computeTargets(Abstraction source) {
							Set<Abstraction> res = new HashSet<Abstraction>();
																		
							//only pass source if the source is not created by this methodcall
							if(!(iStmt instanceof DefinitionStmt) || !((DefinitionStmt)iStmt).getLeftOp().equals(source.getAccessPath().getPlainValue())){
								res.add(source);
							}
							//taintwrapper (might be very conservative/inprecise...)
							if(taintWrapper != null && taintWrapper.supportsBackwardWrapping() && taintWrapper.supportsTaintWrappingForClass(iStmt.getInvokeExpr().getMethod().getDeclaringClass())){
								if(iStmt instanceof DefinitionStmt && ((DefinitionStmt)iStmt).getLeftOp().equals(source.getAccessPath().getPlainValue())){
									List<Value> vals = taintWrapper.getBackwardTaintsForMethod(iStmt);
									if(vals != null){
										for (Value val : vals){
											res.add(new Abstraction(new EquivalentValue(val), source.getSource(), source.getCorrespondingMethod()));
										}
									}
								}
							}
							if (iStmt.getInvokeExpr().getMethod().isNative()) {
								if (callArgs.contains(source.getAccessPath().getPlainValue()) || (iStmt instanceof DefinitionStmt && ((DefinitionStmt)iStmt).getLeftOp().equals(source.getAccessPath().getPlainValue()) )) {
									// java uses call by value, but fields of complex objects can be changed (and tainted), so use this conservative approach:
									// taint all params if one param or return value is tainted)
									NativeCallHandler ncHandler = new DefaultNativeCallHandler();
									res.addAll(ncHandler.getTaintedValuesForBackwardAnalysis(iStmt, source, callArgs, interproceduralCFG().getMethodOf(unit)));
								}
							}
							return res;
						}
					};
				}
				return Identity.v();
			}
		};
	}
	
}
