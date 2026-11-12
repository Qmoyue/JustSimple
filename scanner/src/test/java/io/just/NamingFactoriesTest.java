package io.just;

import io.just.analysis.*;
import io.just.input.Inputs;
import io.just.knowledge.*;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Path;
import java.nio.file.Files;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class NamingFactoriesTest {
    @TempDir Path temp;
    private ScanResult scan(Path classes,String entry)throws Exception {
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,30_000);
            var result=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.COMPONENT,false,
                    Set.of(new Program.MethodId("Factories",entry,"()V")));
            return result;
        }
    }
    private boolean calls(ScanResult result,String owner,String name){return result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.owner().equals(owner) && t.name().equals(name));}
    private Path fixture()throws Exception {
        return BytecodeFixtures.compile(temp,8,Map.of("Factories.java","""
                import javax.naming.*;import javax.naming.spi.*;import java.util.*;import java.lang.reflect.*;
                public class Factories {
                  static void hit(){}static void wrong(){}static void good(){}static void pair(String a,String b){}
                  public static class Chosen implements ObjectFactory {String prefix;public Chosen(){prefix="h";}public Object getObjectInstance(Object ref,Name name,Context context,Hashtable<?,?> env){return prefix+((Reference)ref).get("suffix").getContent();}}
                  public static class Unused implements ObjectFactory {public Object getObjectInstance(Object ref,Name name,Context context,Hashtable<?,?> env){wrong();return null;}}
                  public static class NamedReference extends Reference {String chosen;public NamedReference(String factory,String suffix){super("ignored",new StringRefAddr("suffix",suffix),Unused.class.getName(),null);chosen=factory;}public String getFactoryClassName(){return chosen;}}
                  public static class Tuple implements ObjectFactory {public Object getObjectInstance(Object ref,Name name,Context context,Hashtable<?,?> env){return new Object[]{ref,name,context,env};}}
                  public static class WrongType {public WrongType(){good();}}
                  public static abstract class Abstract implements ObjectFactory {public Abstract(){}}
                  public static class Private implements ObjectFactory {private Private(){}public Object getObjectInstance(Object a,Name b,Context c,Hashtable<?,?> d){wrong();return null;}}
                  public static class Handler implements InvocationHandler {public Object invoke(Object p,Method m,Object[] a){wrong();return null;}}
                  public static class ProxyFactory implements ObjectFactory {public Object getObjectInstance(Object a,Name b,Context c,Hashtable<?,?> d){return Proxy.newProxyInstance(Factories.class.getClassLoader(),new Class[]{Runnable.class},new Handler());}}
                  static Reference ref(String factory,String suffix){return new Reference("ignored.type",new StringRefAddr("suffix",suffix),factory,null);}
                  static Object create(Reference ref)throws Exception {return NamingManager.getObjectInstance(ref,null,null,null);}
                  static void use(String name)throws Exception {Factories.class.getDeclaredMethod(name).invoke(null);}
                  public static void selected()throws Exception {use((String)create(ref(Chosen.class.getName(),"it")));}
                  public static void isolated()throws Exception {pair((String)create(ref(Chosen.class.getName(),"it")),(String)create(ref(Chosen.class.getName(),"alt")));}
                  public static void overridden()throws Exception {use((String)create(new NamedReference(Chosen.class.getName(),"it")));}
                  public static void overrideIsolation()throws Exception {pair((String)create(new NamedReference(Chosen.class.getName(),"it")),(String)create(new NamedReference(Chosen.class.getName(),"alt")));}
                  public static void tuple()throws Exception {Reference ref=ref(Tuple.class.getName(),"");Name name=new CompositeName();Context context=new InitialContext();Hashtable<String,String> env=new Hashtable<>();Object[] result=(Object[])NamingManager.getObjectInstance(ref,name,context,env);if(result[0]==ref && result[1]==name && result[2]==context && result[3]==env)good();else wrong();}
                  public static void wrongType()throws Exception {Reference ref=ref(WrongType.class.getName(),"");try{create(ref);wrong();}catch(ClassCastException expected){good();}}
                  public static void abstractType()throws Exception {Reference ref=ref(Abstract.class.getName(),"");try{create(ref);wrong();}catch(InstantiationException expected){good();}}
                  public static void privateType()throws Exception {Reference ref=ref(Private.class.getName(),"");try{create(ref);wrong();}catch(IllegalAccessException expected){good();}}
                  public static void discarded()throws Exception {create(ref(ProxyFactory.class.getName(),""));good();}
                  public static void remoteOnly()throws Exception {create(new Reference("ignored.type","missing.RemoteFactory","https://example.invalid/"));}
                }
                """));
    }
    @Test void localFactoryConstructionAndResultsUseTheActualReference()throws Exception {
        Path classes=fixture();var result=scan(classes,"selected");
        assertTrue(calls(result,"Factories$Chosen","<init>"));assertTrue(calls(result,"Factories$Chosen","getObjectInstance"));assertTrue(calls(result,"Factories","hit"));
        assertFalse(calls(result,"Factories$Unused","getObjectInstance"));assertFalse(calls(result,"Factories","wrong"));
        assertTrue(result.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Factories") && t.name().equals("hit")).isPresent()).flatMap(r -> r.supports().stream()).allMatch(support -> support.gaps().stream().anyMatch(g -> g.kind()==GapKind.DEPLOYMENT)));
        var isolated=scan(classes,"isolated");
        assertTrue(isolated.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Factories") && t.name().equals("pair")).isPresent())
                .anyMatch(r -> r.arguments().equals(List.of(new Literal("hit"),new Literal("halt")))));
        var overridden=scan(classes,"overridden");assertTrue(calls(overridden,"Factories$NamedReference","getFactoryClassName"));assertTrue(calls(overridden,"Factories","hit"));assertFalse(calls(overridden,"Factories","wrong"));
        var separate=scan(classes,"overrideIsolation");assertTrue(separate.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Factories") && t.name().equals("pair")).isPresent()).anyMatch(r -> r.arguments().equals(List.of(new Literal("hit"),new Literal("halt")))));
    }
    @Test void factoryArgumentsKeepTheirPositionsAndIgnoredProxiesAreNotInvoked()throws Exception {
        Path classes=fixture();var tuple=scan(classes,"tuple");
        assertTrue(calls(tuple,"Factories","good"));assertFalse(calls(tuple,"Factories","wrong"));
        var discarded=scan(classes,"discarded");assertTrue(calls(discarded,"Factories$ProxyFactory","getObjectInstance"));
        assertFalse(calls(discarded,"Factories$Handler","invoke"));assertFalse(calls(discarded,"Factories","wrong"));
    }
    @Test void invalidFactoriesMissingCodeAndRemoteLocationsDoNotSelectOtherClasses()throws Exception {
        Path classes=fixture();
        for(String entry:List.of("wrongType","abstractType","privateType")) {
            var result=scan(classes,entry);assertTrue(calls(result,"Factories","good"),entry);assertFalse(calls(result,"Factories","wrong"),entry);
            assertFalse(calls(result,"Factories$Unused","getObjectInstance"));
        }
        var remote=scan(classes,"remoteOnly");assertFalse(calls(remote,"Factories$Chosen","getObjectInstance"));
        assertTrue(remote.findings().stream().flatMap(f -> f.gaps().stream()).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY));
        Files.delete(classes.resolve("Factories$Chosen.class"));var missing=scan(classes,"selected");
        assertFalse(calls(missing,"Factories$Unused","getObjectInstance"));
        assertTrue(missing.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Factories") && t.name().equals("hit")).isPresent())
                .flatMap(r -> r.supports().stream()).allMatch(support -> support.gaps().stream().anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY)));
        assertTrue(missing.findings().stream().flatMap(f -> f.gaps().stream()).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY));
    }
}
