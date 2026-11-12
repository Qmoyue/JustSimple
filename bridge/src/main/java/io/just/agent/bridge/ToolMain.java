package io.just.agent.bridge;

import com.google.gson.*;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.Map;
import java.util.concurrent.CancellationException;

/** JSON-lines transport. One worker owns scanner state; the reader only delivers cancellation. */
public final class ToolMain {
    private ToolMain() {}
    private static final int MAX_REQUEST_CHARS = 1_000_000;
    private record Work(String id,Thread thread) {}
    private final Object lock=new Object();
    private final PrintWriter output=new PrintWriter(System.out,true,StandardCharsets.UTF_8);
    private Work active;

    public static void main(String[] args)throws Exception {
        System.setErr(new PrintStream(System.err,true,StandardCharsets.UTF_8));
        if(args.length!=1)throw new IllegalArgumentException("expected host configuration file");
        ScannerTools.Config config;
        try(Reader reader=Files.newBufferedReader(Path.of(args[0]),StandardCharsets.UTF_8)){config=ToolJson.GSON.fromJson(reader,ScannerTools.Config.class);}
        new ToolMain().serve(config);
    }
    private void serve(ScannerTools.Config config)throws Exception {
        try(ScannerTools tools=new ScannerTools(config);RequestReader reader=new RequestReader(System.in)) {
            send(Map.of("id","ready","protocol",1,"inputId",tools.identity(),"scanLimits",tools.scanLimits(),"scanDefaults",tools.scanDefaults()));
            try {
                String line;
                while((line=reader.readLine())!=null) {
                    JsonObject request=JsonParser.parseString(line).getAsJsonObject();String id=request.get("id").getAsString();
                    synchronized(lock) {
                        if(request.has("cancel")) {if(active!=null && active.id().equals(id))active.thread().interrupt();continue;}
                        if(active!=null){send(Map.of("id",id,"error",Map.of("code","BUSY","message","scanner tools execute sequentially")));continue;}
                        Thread worker=new Thread(() -> run(tools,id,request),"scanner-tool");
                        worker.setUncaughtExceptionHandler((thread,failure) -> {failure.printStackTrace(System.err);System.exit(2);});
                        active=new Work(id,worker);worker.start();
                    }
                }
            } finally {
                Work work;synchronized(lock){work=active;if(work!=null)work.thread().interrupt();}
                if(work!=null)work.thread().join();
            }
        }
    }

    private static final class RequestReader extends BufferedReader {
        private boolean skipLf;

        RequestReader(InputStream input) {
            super(new InputStreamReader(input, StandardCharsets.UTF_8.newDecoder()));
        }

        @Override public String readLine() throws IOException {
            int next = read();
            if (skipLf && next == '\n') next = read();
            StringBuilder line = new StringBuilder();
            for (; next != -1 && next != '\n' && next != '\r'; next = read()) {
                if (line.length() == MAX_REQUEST_CHARS) throw new IOException("tool request exceeds 1M characters");
                line.append((char) next);
            }
            skipLf = next == '\r';
            return next == -1 && line.isEmpty() ? null : line.toString();
        }
    }

    private void run(ScannerTools tools,String id,JsonObject request) {
        Object response;
        try {
            if (!(request.get("tool") instanceof JsonPrimitive tool) || !tool.isString())
                throw new IllegalArgumentException("tool name must be a string");
            if (!(request.get("args") instanceof JsonObject args))
                throw new IllegalArgumentException("tool args object is required");
            Object value=tools.execute(tool.getAsString(),args,progress -> {
                synchronized(lock){send(Map.of("id",id,"progress",progress));}
            });
            response=Map.of("id",id,"result",value);
        } catch(Exception failure) {
            String code=failure instanceof CancellationException?"CANCELLED":failure instanceof IllegalArgumentException?"INVALID_ARGUMENT":"ANALYSIS_ERROR";
            if(code.equals("ANALYSIS_ERROR"))failure.printStackTrace(System.err);
            response=Map.of("id",id,"error",Map.of("code",code,"message",failure.toString()));
        }
        synchronized(lock){active=null;send(response);}
    }
    private void send(Object value) {
        output.println(ToolJson.GSON.toJson(value));
        if(output.checkError() || System.out.checkError())throw new UncheckedIOException(new IOException("bridge output closed"));
    }
}
