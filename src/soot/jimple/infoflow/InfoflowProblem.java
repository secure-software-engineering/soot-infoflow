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
import soot.PrimType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
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
import soot.jimple.infoflow.source.DefaultSourceSinkManager;
import soot.jimple.infoflow.source.SourceSinkManager;
import soot.jimple.infoflow.util.BaseSelector;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;

public class InfoflowProblem extends AbstractInfoflowProblem {

	private final static boolean DEBUG = true;
	
	final SourceSinkManager sourceSinkManager;
	Abstraction zeroValue = null;
	
	/**
	 * Computes the taints produced by a taint wrapper object
	 * @param iStmt The call statement the taint wrapper shall check for well-
	 * known methods that introduce black-box taint propagation 
	 * @param callArgs The actual parameters with which the method in invoked
	 * @param source The taint source
	 * @return The taints computed by the wrapper
	 */
	private Set<Abstraction> computeWrapperTaints
			(final Stmt iStmt,
			final List<Value> callArgs,
			Abstraction source) {
		Set<Abstraction> res = new HashSet<Abstraction>();
		if(taintWrapper == null || !taintWrapper.supportsTaintWrappingForClass(iStmt.getInvokeExpr().getMethod().getDeclaringClass()))
			return Collections.emptySet();
		
		int taintedPos = -1;
		for(int i=0; i< callArgs.size(); i++){
			if(source.getAccessPath().isLocal() && callArgs.get(i).equals(source.getAccessPath().getPlainValue())){
				taintedPos = i;
				break;
			}
		}
		Value taintedBase = null;
		if(iStmt.getInvokeExpr() instanceof InstanceInvokeExpr){
			InstanceInvokeExpr iiExpr = (InstanceInvokeExpr) iStmt.getInvokeExpr();
			if(iiExpr.getBase().equals(source.getAccessPath().getPlainValue())){
				if(source.getAccessPath().isLocal()){
					taintedBase = iiExpr.getBase();
				}
				else if(source.getAccessPath().isInstanceFieldRef()){
					// The taint refers to the actual type of the field, not the formal type,
					// so we must check whether we have the tainted field at all
					SootClass callerClass = interproceduralCFG().getMethodOf(iStmt).getDeclaringClass();
					if (callerClass.declaresFieldByName(source.getAccessPath().getField()))
						taintedBase = new JInstanceFieldRef(iiExpr.getBase(),
								callerClass.getFieldByName(source.getAccessPath().getField()).makeRef());
				}
			}
			
			// For the moment, we don't implement static taints on wrappers
			if(source.getAccessPath().isStaticFieldRef()){
				//TODO
			}
		}
			
		List<Value> vals = taintWrapper.getTaintsForMethod(iStmt, taintedPos, taintedBase);
		if(vals != null)
			for (Value val : vals)
				if (pathTracking == PathTrackingMethod.ForwardTracking)
					res.add(new AbstractionWithPath(val, source.getSource(),
							((AbstractionWithPath) source).getPropagationPath(),
							iStmt));
				else
					res.add(new Abstraction(val, source.getSource()));
		return res;
	}

	/**
	 * Checks whether a taint wrapper is exclusive for a specific invocation statement
	 * @param iStmt The call statement the taint wrapper shall check for well-
	 * known methods that introduce black-box taint propagation 
	 * @param callArgs The actual parameters with which the method in invoked
	 * @param source The taint source
	 * @return True if the wrapper is exclusive, otherwise false
	 */
	private boolean isWrapperExclusive
			(final Stmt iStmt,
			final List<Value> callArgs,
			Abstraction source) {
		if(taintWrapper == null || !taintWrapper.supportsTaintWrappingForClass(iStmt.getInvokeExpr().getMethod().getDeclaringClass()))
			return false;
		
		int taintedPos = -1;
		for(int i=0; i< callArgs.size(); i++){
			if(source.getAccessPath().isLocal() && callArgs.get(i).equals(source.getAccessPath().getPlainValue())){
				taintedPos = i;
				break;
			}
		}
		Value taintedBase = null;
		if(iStmt.getInvokeExpr() instanceof InstanceInvokeExpr){
			InstanceInvokeExpr iiExpr = (InstanceInvokeExpr) iStmt.getInvokeExpr();
			if(iiExpr.getBase().equals(source.getAccessPath().getPlainValue())){
				if(source.getAccessPath().isLocal()){
					taintedBase = iiExpr.getBase();
				}else if(source.getAccessPath().isInstanceFieldRef()){
					// The taint refers to the actual type of the field, not the formal type,
					// so we must check whether we have the tainted field at all
					SootClass callerClass = interproceduralCFG().getMethodOf(iStmt).getDeclaringClass();
					if (callerClass.declaresFieldByName(source.getAccessPath().getField()))
						taintedBase = new JInstanceFieldRef(iiExpr.getBase(),
								callerClass.getFieldByName(source.getAccessPath().getField()).makeRef());
				}
			}
			if(source.getAccessPath().isStaticFieldRef()){
				//TODO
			}
		}
			
		return taintWrapper.isExclusive(iStmt, taintedPos, taintedBase);
	}
	
	@Override
	public FlowFunctions<Unit, Abstraction, SootMethod> createFlowFunctionsFactory() {
		return new FlowFunctions<Unit, Abstraction, SootMethod>() {

			/**
			 * Creates a new taint abstraction for the given value
			 * @param src The source statement from which the taint originated
			 * @param targetValue The target value that shall now be tainted
			 * @param source The incoming taint abstraction from the source
			 * @param taintSet The taint set to which to add all newly produced
			 * taints
			 */
			private void addTaintViaStmt
					(final Unit src,
					final Value targetValue,
					Abstraction source,
					Set<Abstraction> taintSet) {
				taintSet.add(source);
				if (pathTracking == PathTrackingMethod.ForwardTracking)
					taintSet.add(new AbstractionWithPath(targetValue,
							source.getSource(),
							((AbstractionWithPath) source).getPropagationPath(),
							src));
				else
					taintSet.add(new Abstraction(targetValue,
							source.getSource()));

				SootMethod m = interproceduralCFG().getMethodOf(src);
				if (targetValue instanceof InstanceFieldRef) {
					InstanceFieldRef ifr = (InstanceFieldRef) targetValue;

					Set<Value> aliases = getAliasesinMethod(m.getActiveBody().getUnits(), src, ifr.getBase(), ifr.getFieldRef());
					for (Value v : aliases) {
						if (pathTracking == PathTrackingMethod.ForwardTracking)
							taintSet.add(new AbstractionWithPath(v, source.getSource(),
								((AbstractionWithPath) source).getPropagationPath(),
								src));
						else
							taintSet.add(new Abstraction(v, source.getSource()));
					}
				}
			}

			@Override
			public FlowFunction<Abstraction> getNormalFlowFunction(final Unit src, final Unit dest) {
				// If we compute flows on parameters, we create the initial
				// flow fact here
				if (computeParamFlows && src instanceof IdentityStmt
						&& isInitialMethod(interproceduralCFG().getMethodOf(src))) {
					final IdentityStmt is = (IdentityStmt) src;
					return new FlowFunction<Abstraction>() {

						@Override
						public Set<Abstraction> computeTargets(Abstraction source) {
							if (stopAfterFirstFlow && !results.isEmpty())
								return Collections.emptySet();
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
				else if (src instanceof AssignStmt) {
					AssignStmt assignStmt = (AssignStmt) src;
					Value right = assignStmt.getRightOp();
					Value left = assignStmt.getLeftOp();

					final Value leftValue = BaseSelector.selectBase(left, false);
					final Set<Value> rightVals = BaseSelector.selectBaseList(right, true);

					return new FlowFunction<Abstraction>() {

						@Override
						public Set<Abstraction> computeTargets(Abstraction source) {
							if (stopAfterFirstFlow && !results.isEmpty())
								return Collections.emptySet();

							boolean addLeftValue = false;
							Set<Abstraction> res = new HashSet<Abstraction>();
							PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
							// shortcuts:
							// on NormalFlow taint cannot be created:
							if (source.equals(zeroValue)) {
								return Collections.singleton(source);
							}
							
							for (Value rightValue : rightVals) {
								// check if static variable is tainted (same name, same class)
								if (source.getAccessPath().isStaticFieldRef()) {
									if (rightValue instanceof StaticFieldRef) {
										StaticFieldRef rightRef = (StaticFieldRef) rightValue;
										if (source.getAccessPath().getField().equals(InfoflowProblem.getStaticFieldRefStringRepresentation(rightRef))) {
											addLeftValue = true;
										}
									}
								} else {
									// if both are fields, we have to compare their fieldName via equals and their bases via PTS
									// might happen that source is local because of max(length(accesspath)) == 1
									if (rightValue instanceof InstanceFieldRef) {
										InstanceFieldRef rightRef = (InstanceFieldRef) rightValue;
										Local rightBase = (Local) rightRef.getBase();
										PointsToSet ptsRight = pta.reachingObjects(rightBase);
										Local sourceBase = (Local) source.getAccessPath().getPlainValue();
										PointsToSet ptsSource = pta.reachingObjects(sourceBase);
										if (ptsRight.hasNonEmptyIntersection(ptsSource)) {
											if (source.getAccessPath().isInstanceFieldRef()) {
												if (rightRef.getField().getName().equals(source.getAccessPath().getField())) {
													addLeftValue = true;
												}
											} else {
												addLeftValue = true;
											}
										}
									}
	
									// indirect taint propagation:
									// if rightvalue is local and source is instancefield of this local:
									if (rightValue instanceof Local && source.getAccessPath().isInstanceFieldRef()) {
										Local base = (Local) source.getAccessPath().getPlainValue(); // ?
										PointsToSet ptsSourceBase = pta.reachingObjects(base);
										PointsToSet ptsRight = pta.reachingObjects((Local) rightValue);
										if (ptsSourceBase.hasNonEmptyIntersection(ptsRight)) {
											if (leftValue instanceof Local) {
												if (pathTracking == PathTrackingMethod.ForwardTracking)
													res.add(new AbstractionWithPath(source.getAccessPath().copyWithNewValue(leftValue),
															source.getSource(),
															((AbstractionWithPath) source).getPropagationPath(),
															src));
												else
													res.add(new Abstraction(source.getAccessPath().copyWithNewValue(leftValue),
															source.getSource()));												
											} else {
												// access path length = 1 - taint entire value if left is field reference
												if (pathTracking == PathTrackingMethod.ForwardTracking)
													res.add(new AbstractionWithPath(leftValue,
															source.getSource(),
															((AbstractionWithPath) source).getPropagationPath(),
															src));
												else
													res.add(new Abstraction(leftValue, source.getSource()));
											}
										}
									}
	
									if (rightValue instanceof ArrayRef) {
										Local rightBase = (Local) ((ArrayRef) rightValue).getBase();
										if (rightBase.equals(source.getAccessPath().getPlainValue()) || (source.getAccessPath().isLocal() && pta.reachingObjects(rightBase).hasNonEmptyIntersection(pta.reachingObjects((Local) source.getAccessPath().getPlainValue())))) {
											addLeftValue = true;
										}
									}
	
									// generic case, is true for Locals, ArrayRefs that are equal etc..
									if (rightValue.equals(source.getAccessPath().getPlainValue())) {
										addLeftValue = true;
									}
								}
							}
							// if one of them is true -> add leftValue
							if (addLeftValue) {
								addTaintViaStmt(src, leftValue, source, res);
								return res;
							}
							return Collections.singleton(source);

						}
					};

				}
				else if (returnIsSink &&  dest instanceof ReturnStmt) {
					// Returning from the main method may also count as a sink
					final ReturnStmt returnStmt = (ReturnStmt) dest;
					return new FlowFunction<Abstraction>() {

						@Override
						public Set<Abstraction> computeTargets(Abstraction source) {
							if (stopAfterFirstFlow && !results.isEmpty())
								return Collections.emptySet();

							boolean isSink = false;
							if (source.getAccessPath().isStaticFieldRef())
								isSink = source.getAccessPath().getField().equals(returnStmt.getOp().toString());
							else
								isSink = isInitialMethod(interproceduralCFG().getMethodOf(dest))
									&& source.getAccessPath().getPlainValue().equals(returnStmt.getOp());
							if (isSink) {
								if (pathTracking != PathTrackingMethod.NoTracking)
									results.addResult(returnStmt.toString(),
											source.getSource().toString(),
											((AbstractionWithPath) source).getPropagationPathAsString(interproceduralCFG()),
											interproceduralCFG().getMethodOf(returnStmt) + ": " + returnStmt.toString());
								else
									results.addResult(returnStmt.toString(),
											source.getSource().toString());
							}
							return Collections.singleton(source);
						}
					};
				}
				return Identity.v();
			}

			@Override
			public FlowFunction<Abstraction> getCallFlowFunction(Unit src, final SootMethod dest) {
				final Stmt stmt = (Stmt) src;
				final InvokeExpr ie = stmt.getInvokeExpr();
				final List<Value> callArgs = ie.getArgs();
				final List<Value> paramLocals = new ArrayList<Value>();
				for (int i = 0; i < dest.getParameterCount(); i++) {
					paramLocals.add(dest.getActiveBody().getParameterLocal(i));
				}
				
				return new FlowFunction<Abstraction>() {

					@Override
					public Set<Abstraction> computeTargets(Abstraction source) {
						if (stopAfterFirstFlow && !results.isEmpty())
							return Collections.emptySet();
						if (source.equals(zeroValue)) {
							return Collections.singleton(source);
						}
						if(isWrapperExclusive(stmt, callArgs, source)) {
							//taint is propagated in CallToReturnFunction, so we do not need any taint here:
							return Collections.emptySet();
						}

						Set<Abstraction> res = new HashSet<Abstraction>();
						Value base = source.getAccessPath().getPlainValue();

						PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
						// if taintedobject is instancefieldRef we have to check if the object is delivered..
						if (source.getAccessPath().isInstanceFieldRef()) {

							// second, they might be changed as param - check this

							// first, instancefieldRefs must be propagated if they come from the same class:
							if (ie instanceof InstanceInvokeExpr) {
								InstanceInvokeExpr vie = (InstanceInvokeExpr) ie;

								PointsToSet ptsSource = pta.reachingObjects((Local) base);
								PointsToSet ptsCall = pta.reachingObjects((Local) vie.getBase());
								if (ptsCall.hasNonEmptyIntersection(ptsSource)) {
									if (pathTracking == PathTrackingMethod.ForwardTracking)
										res.add(new AbstractionWithPath
												(source.getAccessPath().copyWithNewValue(dest.getActiveBody().getThisLocal()),
												source.getSource(),
												((AbstractionWithPath) source).getPropagationPath(),
												stmt));
									else
										res.add(new Abstraction
												(source.getAccessPath().copyWithNewValue(dest.getActiveBody().getThisLocal()),
												source.getSource()));
								}
							}

						}

						// check if whole object is tainted (happens with strings, for example:)
						if (!dest.isStatic() && ie instanceof InstanceInvokeExpr && source.getAccessPath().isLocal()) {
							InstanceInvokeExpr vie = (InstanceInvokeExpr) ie;
							// this might be enough because every call must happen with a local variable which is tainted itself:
							if (vie.getBase().equals(source.getAccessPath().getPlainValue())) {
								if (pathTracking == PathTrackingMethod.ForwardTracking)
									res.add(new AbstractionWithPath(dest.getActiveBody().getThisLocal(),
											source.getSource(), ((AbstractionWithPath) source).getPropagationPath(),
											stmt));
								else
									res.add(new Abstraction(dest.getActiveBody().getThisLocal(),
											source.getSource()));
							}
						}

						// check if param is tainted:
						for (int i = 0; i < callArgs.size(); i++) {
							if (callArgs.get(i).equals(base)) {
								if (pathTracking == PathTrackingMethod.ForwardTracking)
									res.add(new AbstractionWithPath(source.getAccessPath().copyWithNewValue(paramLocals.get(i)),
											source.getSource(), ((AbstractionWithPath) source).getPropagationPath(),
											stmt));
								else
									res.add(new Abstraction(source.getAccessPath().copyWithNewValue(paramLocals.get(i)),
											source.getSource()));
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
			public FlowFunction<Abstraction> getReturnFlowFunction(Unit callSite, SootMethod callee, final Unit exitStmt, final Unit retSite) {
				final SootMethod calleeMethod = callee;
				final Unit callUnit = callSite;
				final Unit exitUnit = exitStmt;

				return new FlowFunction<Abstraction>() {

					@Override
					public Set<Abstraction> computeTargets(Abstraction source) {
						if (stopAfterFirstFlow && !results.isEmpty())
							return Collections.emptySet();
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
									if (pathTracking == PathTrackingMethod.ForwardTracking)
										res.add(new AbstractionWithPath(source.getAccessPath().copyWithNewValue(leftOp),
												source.getSource(),
												((AbstractionWithPath) source).getPropagationPath(),
												exitStmt));
									else
										res.add(new Abstraction(source.getAccessPath().copyWithNewValue(leftOp),
												source.getSource()));
								}
								// this is required for sublists, because they assign the list to the return variable and call a method that taints the list afterwards
								Set<Value> aliases = getAliasesinMethod(calleeMethod.getActiveBody().getUnits(), retSite, retLocal, null);
								for (Value v : aliases) {
									if (v.equals(source.getAccessPath().getPlainValue())) {
										if (pathTracking == PathTrackingMethod.ForwardTracking)
											res.add(new AbstractionWithPath(source.getAccessPath().copyWithNewValue(leftOp),
													source.getSource(),
													((AbstractionWithPath) source).getPropagationPath(),
													exitStmt));
										else
											res.add(new Abstraction(source.getAccessPath().copyWithNewValue(leftOp),
													source.getSource()));
									}
								}
							}
						}

						// easy: static
						if (source.getAccessPath().isStaticFieldRef()) {
							res.add(source);
						}

						// checks: this/params/fields

						// check one of the call params are tainted (not if simple type)
						Value sourceBase = source.getAccessPath().getPlainValue();
						Value originalCallArg = null;
						for (int i = 0; i < calleeMethod.getParameterCount(); i++) {
							if (calleeMethod.getActiveBody().getParameterLocal(i).equals(sourceBase)) { // or pts?
								if (callUnit instanceof Stmt) {
									Stmt iStmt = (Stmt) callUnit;
									originalCallArg = iStmt.getInvokeExpr().getArg(i);
									if (!(originalCallArg instanceof Constant) && !(originalCallArg.getType() instanceof PrimType)) {
										if (pathTracking == PathTrackingMethod.ForwardTracking)
											res.add(new AbstractionWithPath(source.getAccessPath().copyWithNewValue(originalCallArg),
													source.getSource(),
													((AbstractionWithPath) source).getPropagationPath(),
													exitStmt));
										else
											res.add(new Abstraction(source.getAccessPath().copyWithNewValue(originalCallArg),
													source.getSource()));
									}
								}
							}
						}

						// Do not try to construct a PTS if we have no base (i.e. we have a static
						// reference) or if the base is some constant
						if (sourceBase != null && sourceBase instanceof Local) {
							Local thisL = null;
							PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
							PointsToSet ptsSource = pta.reachingObjects((Local) sourceBase);
							if (!calleeMethod.isStatic()) {
								thisL = calleeMethod.getActiveBody().getThisLocal();
							}
							if (thisL != null) {
								if (thisL.equals(sourceBase)) {
									// TODO: either remove PTS check here or remove the if-condition above!
									// there is only one case in which this must be added, too: if the caller-Method has the same thisLocal - check this:
									// for super-calls we have to use pts
									PointsToSet ptsThis = pta.reachingObjects(thisL);
	
									if (ptsSource.hasNonEmptyIntersection(ptsThis) || sourceBase.equals(thisL)) {
										boolean param = false;
										// check if it is not one of the params (then we have already fixed it)
										for (int i = 0; i < calleeMethod.getParameterCount(); i++) {
											if (calleeMethod.getActiveBody().getParameterLocal(i).equals(sourceBase)) {
												param = true;
											}
										}
										if (!param) {
											if (callUnit instanceof Stmt) {
												Stmt stmt = (Stmt) callUnit;
												if (stmt.getInvokeExpr() instanceof InstanceInvokeExpr) {
													InstanceInvokeExpr iIExpr = (InstanceInvokeExpr) stmt.getInvokeExpr();
													if (pathTracking == PathTrackingMethod.ForwardTracking)
														res.add(new AbstractionWithPath(source.getAccessPath().copyWithNewValue(iIExpr.getBase()),
																source.getSource(),
																((AbstractionWithPath) source).getPropagationPath(),
																exitStmt));
													else
														res.add(new Abstraction(source.getAccessPath().copyWithNewValue(iIExpr.getBase()),
																source.getSource()));
												}
											}
										}
									}
								}
								// remember that we only support max(length(accesspath))==1 -> if source is a fieldref, only its base is taken!
								for (SootField globalField : calleeMethod.getDeclaringClass().getFields()) {
									if (!globalField.isStatic()) { // else is checked later
										PointsToSet ptsGlobal = pta.reachingObjects(calleeMethod.getActiveBody().getThisLocal(), globalField);
										if (ptsGlobal.hasNonEmptyIntersection(ptsSource)) {
											Local callBaseVar = null;
											if (callUnit instanceof JAssignStmt) {
												callBaseVar = (Local) ((InstanceInvokeExpr) ((JAssignStmt) callUnit).getInvokeExpr()).getBase();
											}
	
											if (callUnit instanceof JInvokeStmt) {
												JInvokeStmt iStmt = (JInvokeStmt) callUnit;
												Value v = iStmt.getInvokeExprBox().getValue();
												InstanceInvokeExpr jvie = (InstanceInvokeExpr) v;
												callBaseVar = (Local) jvie.getBase();
											}
											if (callBaseVar != null) {
												SootFieldRef ref = globalField.makeRef();
												InstanceFieldRef fRef = Jimple.v().newInstanceFieldRef(callBaseVar, ref);
												if (pathTracking == PathTrackingMethod.ForwardTracking)
													res.add(new AbstractionWithPath(fRef, source.getSource(),
															((AbstractionWithPath) source).getPropagationPath(),
															exitStmt));
												else
													res.add(new Abstraction(fRef, source.getSource()));
											}
										}
									}
								}
							}

							for (SootField globalField : calleeMethod.getDeclaringClass().getFields()) {
								if (globalField.isStatic()) {
									PointsToSet ptsGlobal = pta.reachingObjects(globalField);
									if (ptsSource.hasNonEmptyIntersection(ptsGlobal)) {
										if (pathTracking == PathTrackingMethod.ForwardTracking)
											res.add(new AbstractionWithPath(Jimple.v().newStaticFieldRef(globalField.makeRef()),
													source.getSource(),
													((AbstractionWithPath) source).getPropagationPath(),
													exitStmt));
										else
											res.add(new Abstraction(Jimple.v().newStaticFieldRef(globalField.makeRef()),
													source.getSource()));
									}
								}
							}
						}
						return res;
					}

				};
			}

			@Override
			public FlowFunction<Abstraction> getCallToReturnFlowFunction(final Unit call, final Unit returnSite) {
				// special treatment for native methods:
				if (call instanceof Stmt) {
					final Stmt iStmt = (Stmt) call;
					final List<Value> callArgs = iStmt.getInvokeExpr().getArgs();

					return new FlowFunction<Abstraction>() {

						@Override
						public Set<Abstraction> computeTargets(Abstraction source) {
							if (stopAfterFirstFlow && !results.isEmpty())
								return Collections.emptySet();

							Set<Abstraction> res = new HashSet<Abstraction>();
							res.add(source);

							res.addAll(computeWrapperTaints(iStmt, callArgs, source));
							
							if (iStmt.getInvokeExpr().getMethod().isNative()) {
								if (callArgs.contains(source.getAccessPath().getPlainValue())) {
									// java uses call by value, but fields of complex objects can be changed (and tainted), so use this conservative approach:
									res.addAll(ncHandler.getTaintedValues(iStmt, source, callArgs));
								}
							}

							if (iStmt instanceof JAssignStmt) {
								final JAssignStmt stmt = (JAssignStmt) iStmt;

								if (sourceSinkManager.isSourceMethod(stmt)) {
									if (DEBUG)
										System.out.println("Found source: " + stmt.getInvokeExpr().getMethod());
									if (pathTracking == PathTrackingMethod.ForwardTracking)
										res.add(new AbstractionWithPath(stmt.getLeftOp(),
												stmt.getInvokeExpr(), 
												((AbstractionWithPath) source).getPropagationPath(),
												call));
									else
										res.add(new Abstraction(stmt.getLeftOp(),
												stmt.getInvokeExpr()));
									res.remove(zeroValue);
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
												interproceduralCFG().getMethodOf(call) + ": " + call.toString());
									else
										results.addResult(iStmt.getInvokeExpr().getMethod().toString(),
												source.getSource().toString());
								}
								//if the base object which executes the method is tainted the sink is reached, too.
								if (iStmt.getInvokeExpr() instanceof InstanceInvokeExpr) {
									InstanceInvokeExpr vie = (InstanceInvokeExpr) iStmt.getInvokeExpr();
									if (vie.getBase().equals(source.getAccessPath().getPlainValue())) {
										if (pathTracking != PathTrackingMethod.NoTracking)
											results.addResult(iStmt.getInvokeExpr().getMethod().toString(),
													source.getSource().toString(),
													((AbstractionWithPath) source).getPropagationPathAsString(interproceduralCFG()),
													interproceduralCFG().getMethodOf(call) + ": " + call.toString());
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

	public InfoflowProblem(List<String> sourceList, List<String> sinkList) {
		super(new JimpleBasedInterproceduralCFG());
		this.sourceSinkManager = new DefaultSourceSinkManager(sourceList, sinkList);
	}

	public InfoflowProblem(SourceSinkManager sourceSinkManager) {
		super(new JimpleBasedInterproceduralCFG());
		this.sourceSinkManager = sourceSinkManager;
	}

	public InfoflowProblem(InterproceduralCFG<Unit, SootMethod> icfg, List<String> sourceList, List<String> sinkList) {
		super(icfg);
		this.sourceSinkManager = new DefaultSourceSinkManager(sourceList, sinkList);
	}

	public InfoflowProblem(InterproceduralCFG<Unit, SootMethod> icfg, SourceSinkManager sourceSinkManager) {
		super(icfg);
		this.sourceSinkManager = sourceSinkManager;
	}

	public InfoflowProblem(SourceSinkManager mySourceSinkManager, Set<Unit> analysisSeeds) {
	    super(new JimpleBasedInterproceduralCFG());
	    this.sourceSinkManager = mySourceSinkManager;
	    this.initialSeeds.addAll(analysisSeeds);
    }

    @Override
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