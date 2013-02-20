package soot.jimple.infoflow;

import heros.FlowFunction;
import heros.FlowFunctions;
import heros.InterproceduralCFG;
import heros.flowfunc.Identity;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;


import soot.Local;
import soot.NullType;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.Scene;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AbstractionWithPath;
import soot.jimple.infoflow.nativ.DefaultNativeCallHandler;
import soot.jimple.infoflow.nativ.NativeCallHandler;
import soot.jimple.infoflow.source.DefaultSourceSinkManager;
import soot.jimple.infoflow.source.SourceSinkManager;
import soot.jimple.infoflow.util.LocalBaseSelector;
import soot.jimple.internal.InvokeExprBox;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;

public class InfoflowLocalProblem extends AbstractInfoflowProblem {

	final SourceSinkManager sourceSinkManager;
	Abstraction zeroValue = null;

	public FlowFunctions<Unit, Abstraction, SootMethod> createFlowFunctionsFactory() {
		return new FlowFunctions<Unit, Abstraction, SootMethod>() {

			public FlowFunction<Abstraction> getNormalFlowFunction(final Unit src, Unit dest) {
				// If we compute flows on parameters, we create the initial
				// flow fact here
				if (computeParamFlows && src instanceof IdentityStmt
						&& isInitialMethod(interproceduralCFG().getMethodOf(src))) {
					final IdentityStmt is = (IdentityStmt) src;
					return new FlowFunction<Abstraction>() {

						@Override
						public Set<Abstraction> computeTargets(Abstraction source) {
							if (is.getRightOp() instanceof ParameterRef) {
								if (pathTracking != PathTrackingMethod.NoTracking) {
									List<Unit> empty = Collections.emptyList();
									Abstraction abs = new AbstractionWithPath(is.getLeftOp(),
										is.getRightOp(),
										empty,
										is);
									return Collections.singleton(abs);
								}
								else
									return Collections.singleton
										(new Abstraction(is.getLeftOp(),
										is.getRightOp()));
							}
							return Collections.singleton(source);
						}
					};
				}
				// taint is propagated with assignStmt
				else if (src instanceof DefinitionStmt) {
					DefinitionStmt defStmt = (DefinitionStmt) src;
					Value right = defStmt.getRightOp();
					Value left = defStmt.getLeftOp();

					// find appropriate leftValue:
					final Value originalLeft = left;

					final Value leftValue = LocalBaseSelector.selectBase(left);
					final Set<Value> rightVals = LocalBaseSelector.selectBaseList(right);

					return new FlowFunction<Abstraction>() {

						public Set<Abstraction> computeTargets(Abstraction source) {
							boolean addLeftValue = false;
							// on NormalFlow taint cannot be created
							if (source.equals(zeroValue)) {
								return Collections.singleton(source);
							}
							for (Value rightValue : rightVals) {
								// for efficiency (static field refs are always propagated) we check first if field refs are matching:
								if (source.getAccessPath().isStaticFieldRef()) {
									// static variable can be identified by name and declaring class
									if (rightValue instanceof StaticFieldRef) {
										StaticFieldRef rightRef = (StaticFieldRef) rightValue;
										if (source.getAccessPath().getField().equals(InfoflowLocalProblem.getStaticFieldRefStringRepresentation(rightRef))) {
											addLeftValue = true;
										}
									}
								} else {
	
									// if objects are equal, taint is necessary
									if (source.getAccessPath().getPlainValue().equals(rightValue)) {
										assert source.getAccessPath().getPlainValue() instanceof Local && rightValue instanceof Local;
										addLeftValue = true;
									}
								}
							}
							// if one of them is true -> add leftValue
							if (addLeftValue) {
								Set<Abstraction> res = new HashSet<Abstraction>();
								res.add(source);
								res.add(new Abstraction(leftValue, source.getSource()));

								SootMethod m = interproceduralCFG().getMethodOf(src);
								if (originalLeft instanceof InstanceFieldRef) {
									assert leftValue instanceof Local: "Should be local but is " +leftValue.getClass(); // always true
									Value base = ((InstanceFieldRef) originalLeft).getBase();
									Set<Value> aliases = getAliasesinMethod(m.getActiveBody().getUnits(), src, base, ((InstanceFieldRef) originalLeft).getFieldRef());
									for (Value v : aliases) {
										// for normal analysis this would be enough but since this is local analysis we have to "truncate" instancefieldrefs
										// res.add(new Abstraction(new EquivalentValue(v), source.getSource(), interproceduralCFG().getMethodOf(src)));
										if (v instanceof InstanceFieldRef) {
											res.add(new Abstraction(((InstanceFieldRef) v).getBase(), source.getSource()));
										} else {
											res.add(new Abstraction(v, source.getSource()));
										}
									}
								}
								return res;
							}
							return Collections.singleton(source);

						}
					};

				}

				return Identity.v();
			}

			public FlowFunction<Abstraction> getCallFlowFunction(Unit src, final SootMethod dest) {
				final Stmt stmt = (Stmt) src;
				final InvokeExpr ie = stmt.getInvokeExpr();
				final List<Value> callArgs = ie.getArgs();
				final List<Value> paramLocals = new ArrayList<Value>();
				for (int i = 0; i < dest.getParameterCount(); i++) {
					paramLocals.add(dest.getActiveBody().getParameterLocal(i));
				}
				return new FlowFunction<Abstraction>() {

					public Set<Abstraction> computeTargets(Abstraction source) {
						if (source.equals(zeroValue)) {
							return Collections.singleton(source);
						}

						Set<Abstraction> res = new HashSet<Abstraction>();

						// check if whole target object is tainted (happens with strings, for example:)
						if (!dest.isStatic() && ie instanceof InstanceInvokeExpr && source.getAccessPath().isLocal()) {
							InstanceInvokeExpr vie = (InstanceInvokeExpr) ie;
							// this might be enough because every call must happen with a local variable which is tainted itself:
							if (vie.getBase().equals(source.getAccessPath().getPlainValue())) {
								res.add(new Abstraction(dest.getActiveBody().getThisLocal(), source.getSource()));
							}
						}

						// check if param is tainted:
						for (int i = 0; i < callArgs.size(); i++) {
							if (callArgs.get(i).equals(source.getAccessPath().getPlainValue())) {
								Abstraction abs = new Abstraction(paramLocals.get(i), source.getSource());
								res.add(abs);
							}
							// because params are locals, we compare with the class of staticfieldref, not the field
							if (source.getAccessPath().isStaticFieldRef()) {
								if (source.getAccessPath().getField().substring(0, source.getAccessPath().getField().lastIndexOf('.')).equals((callArgs.get(i)).getType().toString())) {
									Abstraction abs = new Abstraction(paramLocals.get(i), source.getSource());
									res.add(abs);
								}
							}
						}

						// fieldRefs must be analyzed even if they are not part of the params:
						if (source.getAccessPath().isStaticFieldRef()) {
							res.add(source);
						}
						return res;
					}
				};
			}

			public FlowFunction<Abstraction> getReturnFlowFunction(Unit callSite, SootMethod callee, Unit exitStmt, final Unit retSite) {
				final SootMethod calleeMethod = callee;
				final Unit callUnit = callSite;
				final Unit exitUnit = exitStmt;

				return new FlowFunction<Abstraction>() {

					public Set<Abstraction> computeTargets(Abstraction source) {
						if (source.equals(zeroValue)) {
							return Collections.singleton(source);
						}
						Set<Abstraction> res = new HashSet<Abstraction>();
						// if we have a returnStmt we have to look at the returned value:
						if (exitUnit instanceof ReturnStmt) {
							ReturnStmt returnStmt = (ReturnStmt) exitUnit;
							Value retLocal = returnStmt.getOp();
							if (callUnit instanceof DefinitionStmt) {
								DefinitionStmt defnStmt = (DefinitionStmt) callUnit;
								Value leftOp = defnStmt.getLeftOp();
								if (retLocal.equals(source.getAccessPath().getPlainValue())) {
									res.add(new Abstraction(LocalBaseSelector.selectBase(leftOp), source.getSource()));
								}
								//this is required for sublists, because they assign the list to the return variable and call a method that taints the list afterwards
								Set<Value> aliases = getAliasesinMethod(calleeMethod.getActiveBody().getUnits(), retSite, retLocal, null);
								for (Value v : aliases) {
									if(v.equals(source.getAccessPath().getPlainValue())){
										res.add(new Abstraction(LocalBaseSelector.selectBase(leftOp), source.getSource()));
									}
								}
							}
						}
						// easy: static
						if (source.getAccessPath().isStaticFieldRef()) {
							res.add(source);
						}
						if (source.getAccessPath().isLocal()) {
							// 1. source equals thislocal:
							if (!calleeMethod.isStatic() && source.getAccessPath().getPlainValue().equals(calleeMethod.getActiveBody().getThisLocal())) {
								// find InvokeStmt:
								InstanceInvokeExpr iIExpr = null;
								if (callUnit instanceof JInvokeStmt) {
									iIExpr = (InstanceInvokeExpr) ((JInvokeStmt) callUnit).getInvokeExpr();
								} else if (callUnit instanceof AssignStmt) {
									iIExpr = (InstanceInvokeExpr) ((JAssignStmt) callUnit).getInvokeExpr();
								}
								if (iIExpr != null) {
									res.add(new Abstraction(iIExpr.getBase(), source.getSource()));
								}
							}

							// TODO can this be removed for the "Local" analysis?
							// REMOVE START
							// reassign the ones we changed into local params:
							PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
							PointsToSet ptsSource = pta.reachingObjects((Local) source.getAccessPath().getPlainValue());

							for (SootField globalField : calleeMethod.getDeclaringClass().getFields()) {
								if (globalField.isStatic()) {
									PointsToSet ptsGlobal = pta.reachingObjects(globalField);
									if (ptsSource.hasNonEmptyIntersection(ptsGlobal)) {
										res.add(new Abstraction(Jimple.v().newStaticFieldRef(globalField.makeRef()), source.getSource()));
									}
								} else {
									// new approach
									if (globalField.equals(source.getAccessPath().getPlainValue())) {
										Local base = null;
										if (callUnit instanceof JAssignStmt) {
											base = (Local) ((InstanceInvokeExpr) ((JAssignStmt) callUnit).getInvokeExpr()).getBase();
										}

										if (callUnit instanceof JInvokeStmt) {
											JInvokeStmt iStmt = (JInvokeStmt) callUnit;
											InvokeExprBox ieb = (InvokeExprBox) iStmt.getInvokeExprBox();
											Value v = ieb.getValue();
											InstanceInvokeExpr jvie = (InstanceInvokeExpr) v;
											base = (Local) jvie.getBase();
										}
										if (base != null) {
											res.add(new Abstraction(base, source.getSource()));
										}
									}
									if (!calleeMethod.isStatic()) {
										PointsToSet ptsGlobal = pta.reachingObjects(calleeMethod.getActiveBody().getThisLocal(), globalField);
										if (ptsGlobal.hasNonEmptyIntersection(ptsSource)) {
											Local base = null;
											if (callUnit instanceof JAssignStmt) {
												base = (Local) ((InstanceInvokeExpr) ((JAssignStmt) callUnit).getInvokeExpr()).getBase();
											}

											if (callUnit instanceof JInvokeStmt) {
												JInvokeStmt iStmt = (JInvokeStmt) callUnit;
												InvokeExprBox ieb = (InvokeExprBox) iStmt.getInvokeExprBox();
												Value v = ieb.getValue();
												InstanceInvokeExpr jvie = (InstanceInvokeExpr) v;
												base = (Local) jvie.getBase();
											}
											if (base != null) {
												res.add(new Abstraction(base, source.getSource()));
											}
										}
									}
								}
							}

							for (int i = 0; i < calleeMethod.getParameterCount(); i++) {
								if (calleeMethod.getActiveBody().getParameterLocal(i).equals(source.getAccessPath().getPlainValue())) {
									if (callUnit instanceof Stmt) {
										Stmt iStmt = (Stmt) callUnit;
										res.add(new Abstraction(iStmt.getInvokeExpr().getArg(i), source.getSource()));
									}
								}
							}
						}
						return res;
					}

				};
			}

			public FlowFunction<Abstraction> getCallToReturnFlowFunction(final Unit call, Unit returnSite) {
				if (call instanceof Stmt) {
					final Stmt iStmt = (Stmt) call;

					final List<Value> callArgs = iStmt.getInvokeExpr().getArgs();

					return new FlowFunction<Abstraction>() {

						public Set<Abstraction> computeTargets(Abstraction source) {
							Set<Abstraction> res = new HashSet<Abstraction>();
							res.add(source);
							// special treatment for native methods:
							if (iStmt.getInvokeExpr().getMethod().isNative()) {
								if (callArgs.contains(source.getAccessPath().getPlainValue())) {
									// java uses call by value, but fields of complex objects can be changed (and tainted), so use this conservative approach:
									NativeCallHandler ncHandler = new DefaultNativeCallHandler();
									res.addAll(ncHandler.getTaintedValues(iStmt, source, callArgs));
								}
							}
							if (iStmt instanceof JAssignStmt) {
								final JAssignStmt stmt = (JAssignStmt) iStmt;

								if (sourceSinkManager.isSourceMethod(stmt)) {
									res.add(new Abstraction(LocalBaseSelector.selectBase(stmt.getLeftOp()), stmt.getInvokeExpr()));
								}
							}
							// if we have called a sink we have to store the path from the source - in case one of the params is tainted!
							if (sourceSinkManager.isSinkMethod(iStmt)) {
								boolean taintedParam = false;
								for (int i = 0; i < callArgs.size(); i++) {
									if (callArgs.get(i).equals(source.getAccessPath().getPlainValue())) {
										taintedParam = true;
										break;
									}
									if (source.getAccessPath().isStaticFieldRef()) {
										if (source.getAccessPath().getField().substring(0, source.getAccessPath().getField().lastIndexOf('.')).equals((callArgs.get(i)).getType().toString())) {
											taintedParam = true;
											break;
										}
									}
								}

								if (taintedParam) {
									if (pathTracking != PathTrackingMethod.NoTracking)
										results.addResult(iStmt.getInvokeExpr().getMethod().toString(),
												source.getSource().toString(),
												((AbstractionWithPath) source).getPropagationPathAsString(interproceduralCFG()),
												call.toString());
									else
										results.addResult(iStmt.getInvokeExpr().getMethod().toString(),
												source.getSource().toString());
								}
								// only for LocalAnalysis at the moment: if the base object which executes the method is tainted the sink is reached, too.
								if (iStmt.getInvokeExpr() instanceof InstanceInvokeExpr) {
									InstanceInvokeExpr vie = (InstanceInvokeExpr) iStmt.getInvokeExpr();
									if (vie.getBase().equals(source.getAccessPath().getPlainValue())) {
										if (pathTracking != PathTrackingMethod.NoTracking)
											results.addResult(iStmt.getInvokeExpr().getMethod().toString(),
													source.getSource().toString(),
													((AbstractionWithPath) source).getPropagationPathAsString(interproceduralCFG()),
													call.toString());
										else
											results.addResult(iStmt.getInvokeExpr().getMethod().toString(),
													source.getSource().toString());
									}
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

	public InfoflowLocalProblem(List<String> sourceList, List<String> sinkList) {
		super(new JimpleBasedInterproceduralCFG());
		this.sourceSinkManager = new DefaultSourceSinkManager(sourceList, sinkList);
	}

	public InfoflowLocalProblem(SourceSinkManager sourceSinkManager) {
		super(new JimpleBasedInterproceduralCFG());
		this.sourceSinkManager = sourceSinkManager;
	}

	public InfoflowLocalProblem(InterproceduralCFG<Unit, SootMethod> icfg, List<String> sourceList, List<String> sinkList) {
		super(icfg);
		this.sourceSinkManager = new DefaultSourceSinkManager(sourceList, sinkList);
	}

	public InfoflowLocalProblem(InterproceduralCFG<Unit, SootMethod> icfg, SourceSinkManager sourceSinkManager) {
		super(icfg);
		this.sourceSinkManager = sourceSinkManager;
	}

	public Abstraction createZeroValue() {
		if (zeroValue == null) {
			zeroValue = this.pathTracking == PathTrackingMethod.NoTracking ?
					new Abstraction(new JimpleLocal("zero", NullType.v()), null) :
					new AbstractionWithPath(new JimpleLocal("zero", NullType.v()), null, null);
		}
		return zeroValue;
	}

	@Override
	public Set<Unit> initialSeeds() {
		return initialSeeds;
	}
	
	@Override
	public boolean autoAddZero() {
		return false;
	}

}