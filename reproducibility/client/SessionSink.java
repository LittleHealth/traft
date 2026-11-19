import java.util.*;
import java.util.concurrent.atomic.AtomicLong;
import org.apache.iotdb.session.Session;
import org.apache.tsfile.enums.TSDataType;

/** One real, blocking Session per worker; admission is controlled by OpenLoop independently. */
public final class SessionSink implements OpenLoop.Factory {
  final Properties p;
  final AtomicLong singleCalls = new AtomicLong(), batchCalls = new AtomicLong();
  public SessionSink(Properties p) { this.p = p; }
  public OpenLoop.Sink open(int worker) throws Exception {
    String[] endpoints = p.getProperty("endpoints").split(",");
    String[] endpoint = endpoints[worker % endpoints.length].split(":");
    final Session session = new Session.Builder().host(endpoint[0]).port(Integer.parseInt(endpoint[1]))
        .username(p.getProperty("username", "root")).password(p.getProperty("password", "root"))
        .enableRedirection(false).enableRecordsAutoConvertTablet(false).maxRetryCount(0)
        .timeOut(60000).build();
    session.open(false, 60000);
    final String prefix = p.getProperty("database") + ".d";
    return sink(session, prefix, singleCalls, batchCalls);
  }
  public Map<String, Object> diagnostics() {
    long single = singleCalls.get(), batch = batchCalls.get();
    Map<String, Object> result = new LinkedHashMap<>();
    result.put("write_api", single > 0 && batch > 0 ? "mixed" :
        single > 0 ? "Session.insertRecord" : batch > 0 ? "Session.insertRecords" : "none");
    result.put("insert_record_calls", single);
    result.put("insert_records_calls", batch);
    return result;
  }
  static OpenLoop.Sink sink(final Session session, final String prefix,
                            final AtomicLong singleCalls, final AtomicLong batchCalls) {
    final List<String> measurement = Collections.singletonList("field0");
    final List<TSDataType> type = Collections.singletonList(TSDataType.TEXT);
    return new OpenLoop.Sink() {
      public void write(OpenLoop.Request request) throws Exception {
        int n = request.times.length;
        String device = prefix + request.device;
        if (n == 1) {
          long timestamp = request.times[0];
          singleCalls.incrementAndGet();
          // This blocking single-record API returns only after the server's write result.
          session.insertRecord(device, timestamp, measurement, type,
              Collections.<Object>singletonList(OpenLoop.value(request.device, timestamp)));
          return;
        }
        if (n != 10) throw new IllegalArgumentException("Expected one or ten points per request");
        List<String> devices = new ArrayList<>(n); List<Long> times = new ArrayList<>(n);
        List<List<String>> measurements = new ArrayList<>(n);
        List<List<TSDataType>> types = new ArrayList<>(n);
        List<List<Object>> values = new ArrayList<>(n);
        for (long timestamp : request.times) {
          devices.add(device); times.add(timestamp); measurements.add(measurement); types.add(type);
          values.add(Collections.<Object>singletonList(OpenLoop.value(request.device, timestamp)));
        }
        batchCalls.incrementAndGet();
        session.insertRecords(devices, times, measurements, types, values);
      }
      public void close() throws Exception { session.close(); }
    };
  }
}
