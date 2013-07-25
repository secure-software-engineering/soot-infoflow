package soot.jimple.infoflow.test.junit;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.BeforeClass;

import soot.jimple.infoflow.Infoflow;
import soot.jimple.infoflow.InfoflowResults;
import soot.jimple.infoflow.config.ConfigForTest;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;
/**
 * abstract super class of all test cases which handles initialization, keeps track of sources and sinks and allows to customize the tests (taintWrapper, debug)
 *
 */
public abstract class JUnitTests {


    protected static String path;
    
    protected static List<String> sinks;

    protected static final String sink = "<soot.jimple.infoflow.test.android.ConnectionManager: void publish(java.lang.String)>";
    protected static final String sinkInt = "<soot.jimple.infoflow.test.android.ConnectionManager: void publish(int)>";

    protected static List<String> sources;
    protected static final String sourceDeviceId = "<soot.jimple.infoflow.test.android.TelephonyManager: java.lang.String getDeviceId()>";
    protected static final String sourcePwd = "<soot.jimple.infoflow.test.android.AccountManager: java.lang.String getPassword()>";
    protected static final String sourceUserData = "<soot.jimple.infoflow.test.android.AccountManager: java.lang.String[] getUserData(java.lang.String)>";
   	

    protected static boolean taintWrapper = false;
    protected static boolean debug = true;
   
    @BeforeClass
    public static void setUp() throws IOException
    {
        final String sep = System.getProperty("path.separator");
    	File f = new File(".");
        File testSrc1 = new File(f,"bin");
        File testSrc2 = new File(f,"build" + File.separator + "classes");

        if (! (testSrc1.exists() || testSrc2.exists())){
            fail("Test aborted - none of the test sources are available");
        }

    	path = System.getProperty("java.home") + File.separator + "lib" + File.separator + "rt.jar"
    			+ sep + testSrc1.getCanonicalPath()
    			+ sep + testSrc2.getCanonicalPath();
    	
        sources = new ArrayList<String>();
        sources.add(sourcePwd);
        sources.add(sourceUserData);
        sources.add(sourceDeviceId);
        
        sinks = new ArrayList<String>();
        sinks.add(sink);
        sinks.add(sinkInt);
    }
    
    @Before
    public void resetSootAndStream() throws IOException{
    	 soot.G.reset();
    	 System.gc();
    	 
    }
    
    protected void checkInfoflow(Infoflow infoflow, int resultCount){
    	 if(infoflow.isResultAvailable()){
				InfoflowResults map = infoflow.getResults();
				assertEquals(resultCount, map.size());
				assertTrue(map.containsSinkMethod(sink) || map.containsSinkMethod(sinkInt));
				assertTrue(map.isPathBetweenMethods(sink, sourceDeviceId)
						|| map.isPathBetweenMethods(sinkInt, sourceDeviceId));
			}else{
				fail("result is not available");
			}
    	
    }
    
//    protected void checkInfoflow(Infoflow infoflow){
//		  if(infoflow.isResultAvailable()){
//				InfoflowResults map = infoflow.getResults();
//				assertTrue(map.containsSinkMethod(sink) || map.containsSinkMethod(sinkInt));
//				assertTrue(map.isPathBetweenMethods(sink, sourceDeviceId)
//						|| map.isPathBetweenMethods(sinkInt, sourceDeviceId));
//			}else{
//				fail("result is not available");
//			}
//	  }
    
    protected void negativeCheckInfoflow(Infoflow infoflow){
    	if(infoflow.isResultAvailable()){
			InfoflowResults map = infoflow.getResults();
			assertEquals(0, map.size());
			assertFalse(map.containsSinkMethod(sink));
			assertFalse(map.containsSinkMethod(sinkInt));
		}else{
				fail("result is not available");
			}
	  }
    
    protected Infoflow initInfoflow(){
    	Infoflow result = new Infoflow();
    	Infoflow.setDebug(debug);
    	ConfigForTest testConfig = new ConfigForTest();
    	result.setSootConfig(testConfig);
    	if(taintWrapper){
    		EasyTaintWrapper easyWrapper;
			try {
				easyWrapper = new EasyTaintWrapper(new File("EasyTaintWrapperSource.txt"));
				result.setTaintWrapper(easyWrapper);
			} catch (IOException e) {
				System.err.println("Could not initialized Taintwrapper:");
				e.printStackTrace();
			}
    		
    	}
    	return result;
    }
    
}
