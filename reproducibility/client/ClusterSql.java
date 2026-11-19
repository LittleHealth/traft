import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import org.apache.iotdb.session.Session;
import org.apache.iotdb.isession.SessionDataSet;
import org.apache.tsfile.read.common.Field;
import org.apache.tsfile.read.common.RowRecord;
import org.apache.tsfile.enums.TSDataType;
import org.apache.tsfile.file.metadata.enums.TSEncoding;
import org.apache.tsfile.file.metadata.enums.CompressionType;

/** SQL control/verification uses the same package classpath as the benchmark client. */
public final class ClusterSql {
  public static void main(String[] args) throws Exception {
    Properties p = OpenLoop.properties(args[0]);
    try (Session session = new Session.Builder().host(p.getProperty("host"))
        .port(Integer.parseInt(p.getProperty("port", "6667")))
        .username(p.getProperty("username", "root")).password(p.getProperty("password", "root"))
        .maxRetryCount(0).timeOut(60000).build()) {
      session.open(false, 60000);
      String operation = args[1];
      if (operation.equals("query")) {
        try (SessionDataSet data = session.executeQueryStatement(args[2], 60000)) {
          Map<String, Object> result = new LinkedHashMap<>();
          result.put("columns", data.getColumnNames()); List<Object> rows = new ArrayList<>();
          while (data.hasNext()) {
            RowRecord row = data.next(); Map<String, Object> value = new LinkedHashMap<>();
            value.put("time", row.getTimestamp()); List<Object> fields = new ArrayList<>();
            for (Field f : row.getFields()) fields.add(f == null || f.getDataType() == null ? null : f.getStringValue());
            value.put("fields", fields); rows.add(value);
          }
          result.put("rows", rows); System.out.println("CLUSTER_JSON=" + OpenLoop.json(result));
        }
      } else if (operation.equals("execute-file")) {
        for (String line : Files.readAllLines(Paths.get(args[2]), StandardCharsets.UTF_8))
          if (!line.trim().isEmpty()) session.executeNonQueryStatement(line);
        System.out.println("CLUSTER_JSON={\"ok\":true}");
      } else if (operation.equals("initialize")) {
        int devices = Integer.parseInt(args[2]);
        for (int base = 0; base < devices; base += 256) {
          List<String> paths = new ArrayList<>();
          for (int d = base; d < Math.min(devices, base + 256); d++) paths.add(p.getProperty("database") + ".d" + d + ".field0");
          session.createMultiTimeseries(paths, Collections.nCopies(paths.size(), TSDataType.TEXT),
              Collections.nCopies(paths.size(), TSEncoding.PLAIN), Collections.nCopies(paths.size(), CompressionType.LZ4),
              null, null, null, null);
        }
        System.out.println("CLUSTER_JSON={\"initialized_devices\":" + devices + "}");
      } else if (operation.equals("verify")) {
        Map<Integer, Long> expected = new TreeMap<>();
        for (String file : args[2].split(",")) {
          List<String> lines = Files.readAllLines(Paths.get(file), StandardCharsets.UTF_8);
          for (String line : lines.subList(1, lines.size())) {
            String[] cells = line.split(","); expected.put(Integer.parseInt(cells[0]), Long.parseLong(cells[1]));
          }
        }
        String database = p.getProperty("database"); Map<Integer, Long> actual = new TreeMap<>();
        try (SessionDataSet data = session.executeQueryStatement("select count(field0) from " + database + ".d* align by device", 120000)) {
          while (data.hasNext()) {
            List<Field> fields = data.next().getFields();
            String device = fields.get(0).getStringValue();
            actual.put(Integer.parseInt(device.substring(device.lastIndexOf(".d") + 2)), Long.parseLong(fields.get(1).getStringValue()));
          }
        }
        List<String> mismatches = new ArrayList<>();
        for (Map.Entry<Integer,Long> e : expected.entrySet())
          if (actual.getOrDefault(e.getKey(), 0L).longValue() != e.getValue().longValue())
            mismatches.add("device=" + e.getKey() + " expected=" + e.getValue() + " actual=" + actual.get(e.getKey()));
        long checked = 0;
        for (String file : args[3].split(",")) {
          List<String> lines = Files.readAllLines(Paths.get(file), StandardCharsets.UTF_8);
          for (String line : lines.subList(1, lines.size())) {
            String[] cells = line.split(",");
            String sql = "select field0 from " + database + ".d" + cells[0] + " where time=" + cells[1];
            try (SessionDataSet data = session.executeQueryStatement(sql, 60000)) {
              if (!data.hasNext() || !cells[2].equals(data.next().getFields().get(0).getStringValue())) mismatches.add("value mismatch " + line);
              checked++;
            }
          }
        }
        Map<String,Object> result = new LinkedHashMap<>();
        result.put("expected_devices", expected.size()); result.put("actual_devices", actual.size());
        result.put("sample_values_checked", checked); result.put("mismatches", mismatches);
        result.put("passed", mismatches.isEmpty());
        System.out.println("CLUSTER_JSON=" + OpenLoop.json(result));
        if (!mismatches.isEmpty()) System.exit(2);
      } else throw new IllegalArgumentException("Unknown SQL operation " + operation);
    }
  }
}
