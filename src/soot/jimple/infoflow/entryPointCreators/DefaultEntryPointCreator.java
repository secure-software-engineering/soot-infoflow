package soot.jimple.infoflow.entryPointCreators;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.IntType;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Value;
import soot.javaToJimple.LocalGenerator;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.infoflow.data.SootMethodAndClass;
import soot.jimple.infoflow.util.SootMethodRepresentationParser;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JGotoStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JNopStmt;

public class DefaultEntryPointCreator extends BaseEntryPointCreator {

    private final Logger logger = LoggerFactory.getLogger(getClass());

	/**
	 * Soot requires a main method, so we create a dummy method which calls all entry functions.
	 * 
	 * @param classMap
	 *            the methods to call (signature as String)
	 * @param createdClass
	 *            the class which contains the methods
	 * @return list of entryPoints
	 */
	@Override
	protected SootMethod createDummyMainInternal(List<String> methods) {
		Map<String, List<String>> classMap =
				SootMethodRepresentationParser.v().parseClassNames(methods, false);
		
		// create new class:
 		JimpleBody body = Jimple.v().newBody();
 		SootMethod mainMethod = createEmptyMainMethod(body);
		
 		LocalGenerator generator = new LocalGenerator(body);
		HashMap<String, Local> localVarsForClasses = new HashMap<String, Local>();
		
		// create constructors:
		for(String className : classMap.keySet()){
			SootClass createdClass = Scene.v().forceResolve(className, SootClass.BODIES);
			createdClass.setApplicationClass();
			
			Local localVal = generateClassConstructor(createdClass, body);
			if (localVal == null) {
				logger.warn("Cannot generate constructor for class: {}", createdClass);
				continue;
			}
			localVarsForClasses.put(className, localVal);
		}
		
		// add entrypoint calls
		int conditionCounter = 0;
		JNopStmt startStmt = new JNopStmt();
		JNopStmt endStmt = new JNopStmt();
		Value intCounter = generator.generateLocal(IntType.v());
		body.getUnits().add(startStmt);
		for (Entry<String, List<String>> entry : classMap.entrySet()){
			Local classLocal = localVarsForClasses.get(entry.getKey());
			for (String method : entry.getValue()){
				SootMethodAndClass methodAndClass =
						SootMethodRepresentationParser.v().parseSootMethodString(method);
				SootMethod currentMethod = findMethod(Scene.v().getSootClass(methodAndClass.getClassName()),
						methodAndClass.getSubSignature());
				if (currentMethod == null) {
					logger.warn("Entry point not found: {}", method);
					continue;
				}
				
				JEqExpr cond = new JEqExpr(intCounter, IntConstant.v(conditionCounter));
				conditionCounter++;
				JNopStmt thenStmt = new JNopStmt();
				JIfStmt ifStmt = new JIfStmt(cond, thenStmt);
				body.getUnits().add(ifStmt);
				buildMethodCall(currentMethod, body, classLocal, generator);
				body.getUnits().add(thenStmt);
			}
		}
		body.getUnits().add(endStmt);
		JGotoStmt gotoStart = new JGotoStmt(startStmt);
		body.getUnits().add(gotoStart);
		
		body.getUnits().add(Jimple.v().newReturnVoidStmt());
		return mainMethod;
	}

}