package io.just.agent.bridge;

import java.nio.file.*;
import java.util.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import static org.junit.jupiter.api.Assertions.*;

class ResultStoreTest {
    @TempDir Path temp;
    @Test void stringPagesKeepSupplementaryCharactersWhole()throws Exception {
        String value="a".repeat(255)+"😀中文".repeat(100);
        try(ResultStore store=new ResultStore(temp,"input",1,20000)) {
            String ref=store.save(Map.of("value",value));
            var first=store.read(ref,List.of("value"),0,1,256);assertEquals(255,first.next());
            StringBuilder restored=new StringBuilder(first.data().getAsString());int offset=first.next();
            while(offset>=0) {
                var page=store.read(ref,List.of("value"),offset,1,256);restored.append(page.data().getAsString());offset=page.next();
            }
            assertEquals(value,restored.toString());
            assertThrows(IllegalArgumentException.class,() -> store.read(ref,List.of("value"),256,1,256));
        }
    }
    @Test void utf8ByteBudgetStopsTheWriterBeforeItFinishesAndFailedWritesFreeCapacity()throws Exception {
        boolean[] completed={false};
        try(ResultStore store=new ResultStore(temp,"input",1,1024)) {
            assertThrows(java.io.IOException.class,() -> store.save(writer -> {
                writer.write("\""+"中".repeat(600)+"\"");writer.flush();completed[0]=true;
            }));
            assertFalse(completed[0],"the byte limit must apply during writing, not after an oversized file is complete");
            String ref=store.save(Map.of("value","字节码"));
            assertEquals("字节码",store.read(ref,List.of("value"),0,1,256).data().getAsString());
        }
        try(var paths=Files.list(temp)){assertEquals(0,paths.count());}
    }
    @Test void selectedEvidenceKeepsIdsSeparateFromPositionsAndBudgetFrontiers()throws Exception {
        try(ResultStore store=new ResultStore(temp,"input",4,50000)) {
            String ref=store.save(Map.of("relations",List.of(Map.of("id",81,"value","small"),Map.of("id",9001,"value","x".repeat(2000)),Map.of("id",4,"value","tail"))));
            var selected=store.select(ref,List.of("relations"),Map.of(0,81,2,4),10,6000);
            assertEquals(List.of(),selected.deferred());assertEquals(2,selected.data().size());
            assertEquals(81,selected.data().get(0).getAsJsonObject().get("id").getAsInt());
            var limited=store.select(ref,List.of("relations"),new LinkedHashMap<>(Map.of(0,81,2,4)),1,6000);
            assertEquals(1,limited.data().size());assertEquals(List.of(4),limited.deferred());
            var large=store.select(ref,List.of("relations"),Map.of(1,9001),1,300);
            assertEquals(9001,large.data().get(0).getAsJsonObject().get("id").getAsInt());
            assertTrue(large.data().get(0).getAsJsonObject().get("requiresNarrowerPath").getAsBoolean());
            assertEquals("1",large.data().get(0).getAsJsonObject().getAsJsonArray("path").get(1).getAsString());
            assertThrows(java.io.IOException.class,() -> store.select(ref,List.of("relations"),Map.of(0,12),1,6000));
        }
    }
    @Test void cancelledWritesCloseFilesAndLeaveCapacityAvailable()throws Exception {
        try(ResultStore store=new ResultStore(temp,"input",1,20000)) {
            try {
                assertThrows(java.util.concurrent.CancellationException.class,() -> store.save(writer -> {
                    writer.write("\"partial\"");Thread.currentThread().interrupt();writer.flush();
                }));
            } finally {Thread.interrupted();}
            try(var paths=Files.list(temp)){assertEquals(0,paths.count());}
            String ref=store.save(Map.of("after","cancel"));
            assertEquals("cancel",store.read(ref,List.of("after"),0,1,256).data().getAsString());
        }
    }

    @Test void cancelledReadsKeepTheResultAvailable() throws Exception {
        try (ResultStore store = new ResultStore(temp, "input", 1, 1024)) {
            String ref = store.save(Map.of("label", "local record", "rows", List.of(Map.of("id", 3))));
            Thread.currentThread().interrupt();
            try {
                assertThrows(java.util.concurrent.CancellationException.class,
                        () -> store.read(ref, List.of("label"), 0, 1, 256));
                assertThrows(java.util.concurrent.CancellationException.class,
                        () -> store.select(ref, List.of("rows"), Map.of(0, 3), 1, 256));
                assertTrue(Thread.currentThread().isInterrupted());
            } finally { Thread.interrupted(); }
            assertEquals("local record", store.read(ref, List.of("label"), 0, 1, 256).data().getAsString());
        }
    }

    @Test void arrayAndSelectionBudgetsIncludeTheJsonEnvelope() throws Exception {
        try (ResultStore store = new ResultStore(temp, "input", 1, 4096)) {
            String value = "x".repeat(254);
            String ref = store.save(Map.of("values", List.of(value), "records", List.of(Map.of("id", 7, "value", "x".repeat(237)))));
            var page = store.read(ref, List.of("values"), 0, 1, 256);
            assertTrue(page.data().toString().length() <= 256);
            var pointer = page.data().getAsJsonArray().get(0).getAsJsonObject();
            assertEquals("0", pointer.getAsJsonArray("path").get(1).getAsString());
            assertEquals(value, store.read(ref, List.of("values", "0"), 0, 1, 256).data().getAsString());
            var selected = store.select(ref, List.of("records"), Map.of(0, 7), 1, 256);
            assertTrue(selected.data().toString().length() <= 256);
            assertEquals(7, selected.data().get(0).getAsJsonObject().get("id").getAsInt());
            assertTrue(selected.deferred().isEmpty());
        }
    }

    @Test void cancelledExportsLeaveNoCopyAndKeepTheSourceAvailable() throws Exception {
        try (ResultStore store = new ResultStore(temp, "input", 1, 1024)) {
            String ref = store.save(Map.of("value", "本地记录"));
            Path output = temp.resolve("export.json");
            Thread.currentThread().interrupt();
            try {
                assertThrows(java.util.concurrent.CancellationException.class, () -> store.export(ref, output, 1024));
            } finally { Thread.interrupted(); }
            assertFalse(Files.exists(output));
            assertEquals(store.export(ref, output, 1024), Files.size(output));
            assertEquals("{\"value\":\"本地记录\"}", Files.readString(output));
        }
    }

    @Test void releasingAnAlreadyMissingFileReturnsItsRecordedCapacity() throws Exception {
        try (ResultStore store = new ResultStore(temp, "input", 1, 3)) {
            String ref = store.save(writer -> writer.write("\"a\""));
            Path backingFile;
            try (var paths = Files.list(temp)) { backingFile = paths.findFirst().orElseThrow(); }
            Files.delete(backingFile);
            store.release(ref);

            String next = store.save(writer -> writer.write("\"b\""));
            assertEquals("b", store.read(next, List.of(), 0, 1, 256).data().getAsString());
            assertThrows(IllegalArgumentException.class, () -> store.read(ref, List.of(), 0, 1, 256));
        }
    }
    @Test void storageBoundsAndReleasedIdentitiesAreEnforced()throws Exception {
        java.nio.file.Path directory=Files.createDirectory(temp.resolve("results"));
        try(ResultStore store=new ResultStore(directory,"input",2,20000)) {
            String ref=store.save(Map.of("value",List.of(Map.of("large","x".repeat(5000)),Map.of("small",3))));
            var page=store.read(ref,List.of("value"),0,2,600);
            assertTrue(page.data().getAsJsonArray().get(0).getAsJsonObject().get("requiresNarrowerPath").getAsBoolean());
            assertEquals(2,page.data().getAsJsonArray().size());
            assertEquals(256,store.read(ref,List.of("value","0","large"),0,1,256).next());
            assertThrows(IllegalArgumentException.class,() -> store.read("foreign/1",List.of(),0,1,1000));
            store.save(Map.of("next",2));assertThrows(java.io.IOException.class,() -> store.save(Map.of("overflow",3)));
            store.release(ref);assertThrows(IllegalArgumentException.class,() -> store.read(ref,List.of(),0,1,1000));
            assertThrows(java.io.IOException.class,() -> store.save(Map.of("large","y".repeat(30000))));
        }
        try(var paths=Files.list(directory)){assertEquals(0,paths.count());}
        Map<String,String> wide=new LinkedHashMap<>();for(int i=0;i<1000;i++)wide.put("key"+i,"data");
        try(ResultStore store=new ResultStore(directory,"wide",1,100000)) {
            String ref=store.save(wide);var keys=store.read(ref,List.of(),0,3,256);
            assertEquals("object-keys",keys.kind());assertEquals(3,keys.next());assertEquals(3,keys.data().getAsJsonArray().size());
            assertEquals("key3",store.read(ref,List.of(),3,3,256).data().getAsJsonArray().get(0).getAsString());
        }
    }
}
