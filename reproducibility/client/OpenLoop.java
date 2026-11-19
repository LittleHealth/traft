import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.LockSupport;

/** Bounded open-loop driver with explicit one-point or ten-point requests. */
public final class OpenLoop {
  public interface Sink extends AutoCloseable {
    void write(Request request) throws Exception;
    default void close() throws Exception {}
  }
  public interface Factory {
    Sink open(int worker) throws Exception;
    default Map<String, Object> diagnostics() { return Collections.emptyMap(); }
  }
  public static final class Request {
    public final int device;
    public final long ordinal, scheduledNanos;
    public final long[] times;
    public Request(int device, long ordinal, long scheduledNanos, long[] times) {
      this.device = device; this.ordinal = ordinal;
      this.scheduledNanos = scheduledNanos; this.times = times;
    }
  }
  /** Mergeable 1%-width logarithmic histogram; values are upper bounds, in microseconds. */
  public static final class Histogram {
    static final double LOG = Math.log(1.01);
    final long[] bins = new long[2400];
    long count;
    double totalNanos;
    public void record(long nanos) {
      double us = Math.max(1, nanos / 1000.0);
      int bin = Math.min(bins.length - 1, (int)Math.ceil(Math.log(us) / LOG));
      bins[bin]++; count++; totalNanos += nanos;
    }
    public void add(Histogram h) {
      for (int i = 0; i < bins.length; i++) bins[i] += h.bins[i];
      count += h.count; totalNanos += h.totalNanos;
    }
    public double percentile(double p) {
      if (count == 0) return Double.NaN;
      long need = (long)Math.ceil(count * p), seen = 0;
      for (int i = 0; i < bins.length; i++) {
        seen += bins[i]; if (seen >= need) return Math.exp(i * LOG) / 1000;
      }
      throw new AssertionError();
    }
    public Map<String, Object> json() {
      Map<String, Object> result = new LinkedHashMap<>();
      for (int i = 0; i < bins.length; i++) if (bins[i] != 0) result.put("" + i, bins[i]);
      return result;
    }
  }
  public static final class Config {
    int workers = 2, devices = 16, deviceOffset = 0, batch = 1, capacity = 32;
    double ratePoints = 1000, probability = 0, duration = 2, steadyStart = 0, steadyEnd = 2;
    long seed = 20261109, timestampBase = 1_700_000_000_000L;
    int drainSeconds = 120;
    Path output, startFile;
    void validate() {
      if (workers < 1 || devices < 1 || workers > 9600 || capacity < 1 || (batch != 1 && batch != 10)
          || !Double.isFinite(ratePoints) || ratePoints <= 0
          || !Double.isFinite(probability) || probability < 0 || probability > 1
          || !(duration > 0 && duration <= 3600 && steadyStart >= 0
               && steadyEnd > steadyStart && steadyEnd <= duration))
        throw new IllegalArgumentException("Invalid driver configuration");
    }
  }
  static final class Lane {
    final ArrayDeque<Request> queue = new ArrayDeque<>();
    boolean active;
  }
  static final String[] FIELDS = {"generated", "accepted", "unsent", "sent", "success", "failed"};
  final Config c;
  final Factory factory;
  final Semaphore slots;
  final Lane[] lanes;
  final BlockingQueue<Integer> ready = new LinkedBlockingQueue<>();
  final AtomicLongArray totals = new AtomicLongArray(FIELDS.length);
  final AtomicLongArray[] seconds;
  final AtomicInteger peak = new AtomicInteger(), outstanding = new AtomicInteger();
  final AtomicReference<Throwable> fatal = new AtomicReference<>();
  final CountDownLatch opened, start = new CountDownLatch(1);
  final Histogram[] endToEnd, rpc, scheduleLag;
  final List<Thread> workers = new ArrayList<>();
  final List<Map<String, Object>> errors = Collections.synchronizedList(new ArrayList<>());
  final Map<Integer, Request> samples = new ConcurrentHashMap<>();
  final AtomicLongArray successfulRows;
  volatile boolean stop;
  volatile long startNanos;
  volatile long startEpochMs;

  public OpenLoop(Config c, Factory factory) {
    c.validate(); this.c = c; this.factory = factory;
    slots = new Semaphore(c.capacity); opened = new CountDownLatch(c.workers);
    lanes = new Lane[c.devices]; successfulRows = new AtomicLongArray(c.devices);
    for (int i = 0; i < lanes.length; i++) lanes[i] = new Lane();
    seconds = new AtomicLongArray[(int)Math.ceil(c.duration) + c.drainSeconds + 5];
    for (int i = 0; i < seconds.length; i++) seconds[i] = new AtomicLongArray(FIELDS.length);
    endToEnd = new Histogram[c.workers]; rpc = new Histogram[c.workers];
    scheduleLag = new Histogram[] {new Histogram()};
    for (int i = 0; i < c.workers; i++) { endToEnd[i] = new Histogram(); rpc[i] = new Histogram(); }
  }
  static long hash(long value) {
    value = (value ^ (value >>> 30)) * 0xbf58476d1ce4e5b9L;
    value = (value ^ (value >>> 27)) * 0x94d049bb133111ebL;
    return value ^ (value >>> 31);
  }
  public static String value(int device, long timestamp) {
    long x = hash(timestamp ^ ((long)device << 32));
    char[] out = new char[10];
    for (int i = 0; i < 10; i++) { out[i] = "0123456789abcdef".charAt((int)x & 15); x >>>= 4; }
    return new String(out);
  }
  Request generate(int localDevice, long ordinal, long scheduled) {
    long[] times = new long[c.batch];
    int device = localDevice + c.deviceOffset;
    for (int i = 0; i < c.batch; i++) {
      long row = ordinal * c.batch + i + 1;
      double uniform = (hash(c.seed ^ ((long)device << 32) ^ row) >>> 11) * 0x1.0p-53;
      times[i] = c.timestampBase + (uniform < c.probability ? -row : row);
    }
    return new Request(device, ordinal, scheduled, times);
  }
  void event(int field, long at) {
    totals.incrementAndGet(field);
    int second = (int)((at - startNanos) / 1_000_000_000L);
    if (second >= 0 && second < seconds.length) seconds[second].incrementAndGet(field);
  }
  boolean inSteady(long at) {
    double t = (at - startNanos) / 1e9;
    return t >= c.steadyStart && t < c.steadyEnd;
  }
  void worker(int index, Semaphore opening) {
    Sink sink = null;
    try {
      opening.acquire();
      try { sink = factory.open(index); } finally { opening.release(); }
      opened.countDown(); start.await();
      while (!stop || outstanding.get() > 0) {
        Integer device = ready.poll(100, TimeUnit.MILLISECONDS);
        if (device == null) continue;
        Lane lane = lanes[device];
        Request r;
        synchronized (lane) { r = lane.queue.removeFirst(); }
        long begin = System.nanoTime(); event(3, begin);
        try {
          sink.write(r);
          long done = System.nanoTime(); event(4, done);
          successfulRows.addAndGet(device, c.batch);
          // Deterministic small sample, including each client's first sequence.
          if (device % Math.max(1, c.devices / 16) == 0) samples.put(r.device, r);
          if (inSteady(done)) { endToEnd[index].record(done - r.scheduledNanos); rpc[index].record(done - begin); }
        } catch (Exception ex) {
          event(5, System.nanoTime());
          synchronized (errors) {
            if (errors.size() < 100) {
              Map<String, Object> error = new LinkedHashMap<>();
              error.put("device", r.device); error.put("ordinal", r.ordinal); error.put("error", ex.toString());
              errors.add(error);
            }
          }
        } finally {
          synchronized (lane) {
            if (lane.queue.isEmpty()) lane.active = false;
            else ready.add(device);
          }
          outstanding.decrementAndGet(); slots.release();
        }
      }
    } catch (Throwable ex) { fatal.compareAndSet(null, ex); }
    finally {
      opened.countDown();
      if (sink != null) try { sink.close(); } catch (Exception ex) { fatal.compareAndSet(null, ex); }
    }
  }
  public Map<String, Object> run() throws Exception {
    Semaphore opening = new Semaphore(8);
    for (int i = 0; i < c.workers; i++) {
      final int index = i;
      Thread t = new Thread(() -> worker(index, opening), "writer-" + i);
      t.setDaemon(true); workers.add(t); t.start();
    }
    if (!opened.await(180, TimeUnit.SECONDS) || fatal.get() != null) {
      stop = true; start.countDown();
      throw new IllegalStateException("Session preparation failed", fatal.get());
    }
    if (c.output != null) Files.write(c.output.resolve("ready"), "ready\n".getBytes(StandardCharsets.UTF_8));
    startEpochMs = System.currentTimeMillis() + 100;
    if (c.startFile != null) {
      long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(300);
      while (!Files.exists(c.startFile)) {
        if (System.nanoTime() > deadline) throw new IllegalStateException("No controller start barrier");
        Thread.sleep(50);
      }
      startEpochMs = Long.parseLong(new String(Files.readAllBytes(c.startFile), StandardCharsets.UTF_8).trim());
      if (startEpochMs < System.currentTimeMillis() + 100) throw new IllegalStateException("Missed start barrier");
    }
    startNanos = System.nanoTime() + TimeUnit.MILLISECONDS.toNanos(startEpochMs - System.currentTimeMillis());
    start.countDown();
    long count = (long)Math.floor(c.ratePoints / c.batch * c.duration);
    for (long i = 0; i < count; i++) {
      if (fatal.get() != null) throw new IllegalStateException("Worker terminated", fatal.get());
      long scheduled = startNanos + (long)(i * 1e9 * c.batch / c.ratePoints);
      long delay;
      while ((delay = scheduled - System.nanoTime()) > 0) LockSupport.parkNanos(delay);
      event(0, scheduled);
      if (inSteady(scheduled)) scheduleLag[0].record(System.nanoTime() - scheduled);
      if (!slots.tryAcquire()) { event(2, scheduled); continue; }
      event(1, scheduled);
      int active = outstanding.incrementAndGet(); peak.accumulateAndGet(active, Math::max);
      int device = (int)(i % c.devices);
      Request r = generate(device, i / c.devices, scheduled);
      Lane lane = lanes[device];
      synchronized (lane) {
        lane.queue.addLast(r);
        if (!lane.active) { lane.active = true; ready.add(device); }
      }
    }
    long deadline = startNanos + (long)(c.duration * 1e9) + TimeUnit.SECONDS.toNanos(c.drainSeconds);
    stop = true;
    for (Thread t : workers) {
      long left = deadline - System.nanoTime();
      if (left > 0) t.join(Math.max(1, TimeUnit.NANOSECONDS.toMillis(left)));
    }
    if (outstanding.get() > 0) fatal.compareAndSet(null, new IOException("Drain deadline exceeded"));
    Map<String, Object> result = result();
    if (c.output != null) {
      writeJson(c.output.resolve("result.json"), result);
      writeArtifacts();
    }
    return result;
  }
  Map<String, Object> result() {
    Histogram merged = new Histogram(), service = new Histogram();
    for (int i = 0; i < c.workers; i++) { merged.add(endToEnd[i]); service.add(rpc[i]); }
    Map<String, Object> result = new LinkedHashMap<>();
    result.put("format", 1); result.put("start_epoch_ms", startEpochMs);
    result.put("duration_seconds", c.duration); result.put("steady_start_seconds", c.steadyStart);
    result.put("steady_end_seconds", c.steadyEnd); result.put("rate_points", c.ratePoints);
    result.put("batch_rows", c.batch); result.put("probability", c.probability);
    result.put("workers", c.workers); result.put("devices", c.devices);
    result.put("device_offset", c.deviceOffset); result.put("capacity", c.capacity);
    result.put("peak_outstanding", peak.get()); result.put("outstanding_at_end", outstanding.get());
    for (int f = 0; f < FIELDS.length; f++) {
      result.put(FIELDS[f] + "_requests", totals.get(f));
      long steady = 0;
      for (int sec = (int)c.steadyStart; sec < c.steadyEnd; sec++) steady += seconds[sec].get(f);
      result.put("steady_" + FIELDS[f] + "_requests", steady);
    }
    result.put("latency_histogram", merged.json()); result.put("rpc_histogram", service.json());
    result.put("scheduler_lag_histogram", scheduleLag[0].json());
    result.put("histogram_base", 1.01); result.put("histogram_unit", "microseconds_upper_bound");
    result.put("latency_samples", merged.count);
    result.put("rpc_mean_ms", service.count == 0 ? Double.NaN : service.totalNanos / service.count / 1e6);
    result.put("rpc_p50_ms", service.percentile(.50)); result.put("rpc_p99_ms", service.percentile(.99));
    result.put("throughput_kpt_s", ((Number)result.get("steady_success_requests")).doubleValue() / (c.steadyEnd - c.steadyStart) / 1000);
    result.put("p50_ms", merged.percentile(.50)); result.put("p99_ms", merged.percentile(.99));
    result.put("scheduler_p99_ms", scheduleLag[0].percentile(.99));
    result.put("fatal", fatal.get() == null ? null : fatal.get().toString());
    result.put("errors", errors);
    result.put("sink_diagnostics", factory.diagnostics());
    return result;
  }
  void writeArtifacts() throws IOException {
    try (PrintWriter out = new PrintWriter(Files.newBufferedWriter(c.output.resolve("timeseries.csv"), StandardCharsets.UTF_8))) {
      out.println("second,generated,accepted,unsent,sent,success,failed");
      for (int s = 0; s < seconds.length; s++) {
        out.print(s); for (int f = 0; f < FIELDS.length; f++) out.print("," + seconds[s].get(f)); out.println();
      }
    }
    try (PrintWriter out = new PrintWriter(Files.newBufferedWriter(c.output.resolve("acknowledged.csv"), StandardCharsets.UTF_8))) {
      out.println("device,rows");
      for (int d = 0; d < c.devices; d++) out.println((d + c.deviceOffset) + "," + successfulRows.get(d));
    }
    try (PrintWriter out = new PrintWriter(Files.newBufferedWriter(c.output.resolve("samples.csv"), StandardCharsets.UTF_8))) {
      out.println("device,timestamp,value");
      for (int device : new TreeSet<>(samples.keySet())) {
        Request r = samples.get(device);
        for (long t : r.times) out.println(device + "," + t + "," + value(device, t));
      }
    }
  }
  static String json(Object obj) {
    if (obj == null) return "null";
    if (obj instanceof Double && !Double.isFinite((Double)obj)) return "null";
    if (obj instanceof Number || obj instanceof Boolean) return obj.toString();
    if (obj instanceof Map) {
      List<String> values = new ArrayList<>();
      for (Object e : ((Map<?,?>)obj).entrySet()) {
        Map.Entry<?,?> entry = (Map.Entry<?,?>)e;
        values.add(json(entry.getKey().toString()) + ":" + json(entry.getValue()));
      }
      return "{" + String.join(",", values) + "}";
    }
    if (obj instanceof Iterable) {
      List<String> values = new ArrayList<>(); for (Object v : (Iterable<?>)obj) values.add(json(v));
      return "[" + String.join(",", values) + "]";
    }
    String s = obj.toString(); StringBuilder out = new StringBuilder("\"");
    for (int i = 0; i < s.length(); i++) {
      char ch = s.charAt(i);
      if (ch == '"' || ch == '\\') out.append('\\').append(ch);
      else if (ch < 32) out.append(String.format("\\u%04x", (int)ch));
      else out.append(ch);
    }
    return out.append('"').toString();
  }
  static void writeJson(Path p, Object value) throws IOException {
    Path temporary = p.resolveSibling(p.getFileName() + ".tmp");
    Files.write(temporary, (json(value) + "\n").getBytes(StandardCharsets.UTF_8));
    Files.move(temporary, p, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE);
  }
  public static Properties properties(String path) throws IOException {
    Properties p = new Properties(); try (Reader reader = Files.newBufferedReader(Paths.get(path), StandardCharsets.UTF_8)) { p.load(reader); }
    return p;
  }
  public static void main(String[] args) throws Exception {
    Properties p = properties(args[0]); Config c = new Config();
    c.batch = Integer.parseInt(p.getProperty("batch", "1"));
    c.workers = Integer.parseInt(p.getProperty("workers")); c.devices = Integer.parseInt(p.getProperty("devices"));
    c.deviceOffset = Integer.parseInt(p.getProperty("deviceOffset", "0")); c.capacity = Integer.parseInt(p.getProperty("capacity"));
    c.ratePoints = Double.parseDouble(p.getProperty("ratePoints")); c.probability = Double.parseDouble(p.getProperty("probability"));
    c.duration = Double.parseDouble(p.getProperty("duration")); c.steadyStart = Double.parseDouble(p.getProperty("steadyStart"));
    c.steadyEnd = Double.parseDouble(p.getProperty("steadyEnd")); c.seed = Long.parseLong(p.getProperty("seed"));
    c.timestampBase = Long.parseLong(p.getProperty("timestampBase")); c.drainSeconds = Integer.parseInt(p.getProperty("drainSeconds", "120"));
    c.output = Paths.get(p.getProperty("output")); Files.createDirectories(c.output);
    c.startFile = Paths.get(p.getProperty("startFile"));
    Factory factory = (Factory)Class.forName(p.getProperty("factory", "SessionSink")).getConstructor(Properties.class).newInstance(p);
    Map<String, Object> result = new OpenLoop(c, factory).run();
    if (result.get("fatal") != null || ((Number)result.get("failed_requests")).longValue() > 0) System.exit(2);
  }
}
