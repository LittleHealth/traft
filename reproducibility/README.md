# Minimal TRaft experiment runner

Code: [Apache IoTDB, research/traft](https://github.com/apache/iotdb/tree/research/traft).
Historical experiments used `374f166686f5ce8b7ee161289b31d08f1b09323e`; the current branch may differ.
This directory provides a basic single-point test, not the historical performance matrices or their archived results.

## Prepare

Use Linux servers, passwordless SSH from the controller, Python 3.11+, and a compatible JDK (JDK 17 for the server). The controller also needs `java` and `javac` on PATH. Use the same built IoTDB distribution on the controller and servers; no server source or binaries are bundled.

Extract one dedicated ConfigNode installation and one dedicated DataNode installation per server. Use fresh data directories when changing protocols. Configure each installation's `conf/iotdb-system.properties` using the distribution's template:

- Set `cn_seed_config_node` and `dn_seed_config_node` to the ConfigNode's private address and port (normally 10710).
- Set `cn_internal_address` on the ConfigNode; set `dn_internal_address` and `dn_rpc_address` to each DataNode's reachable private address.
- Use `org.apache.iotdb.consensus.simple.SimpleConsensus` for the single ConfigNode's consensus and for schema regions; set `schema_replication_factor=1`.
- On the ConfigNode and all DataNodes, set `data_replication_factor` to the number of DataNodes and `data_region_consensus_protocol_class` to the selected class below.
- For single-point application, set `raft_pipeline_rows=false`, `raft_apply_batch=false`, `traft_pipeline_rows=false`, `traft_apply_batch=false`, and `traft_apply_async=false` where supported by the selected implementation.

| Protocol key | Data-region consensus class |
|---|---|
| `raft` | `org.apache.iotdb.consensus.raft.RaftConsensus` |
| `traft` | `org.apache.iotdb.consensus.traft.TRaftConsensus` |
| `parallelraft` | `org.apache.iotdb.consensus.parallelraft.ParallelRaftConsensus` |
| `lsmraft` | `org.apache.iotdb.consensus.lsmraft.LsmRaftConsensus` |
| `iotconsensus` | `org.apache.iotdb.consensus.iot.IoTConsensus` |

Open the configured internal and RPC ports between nodes. Set memory and durability options in the installation configuration; these scripts do not impose resource limits, rebalance leaders, or change monitoring services. They use the distribution's start/stop scripts, so only point them at installations dedicated to this experiment.

## Configure and run

```bash
cd reproducibility
cp config.example.json config.json
# Edit SSH aliases, installation paths, RPC endpoints and workload values.
./start.sh --config config.json --dry-run
./start.sh --config config.json
# Use IoTDB's CLI: SHOW CLUSTER. Wait until the expected nodes are Running.
./run.sh --config config.json --out results/traft-01
./stop.sh --config config.json
```

`protocol` validates the configured backend; it does not change an existing cluster's protocol. `local_iotdb_home` points to the controller's extracted distribution with Session dependency JARs in `lib/`. The default root/root database credentials are used; adapt the client for a secured deployment.

The input rate is total points/second across this controller's workers, not per thread. Each request writes one 10-byte TEXT value with `Session.insertRecord`; the worker waits for the return before its next write. The independent scheduler uses a bounded queue, keeps per-series ordering, and records unsent requests under overload. Timestamps are ordered (`p=0`). The retained historical admission policy can be biased under heavy overload; this minimal runner does not establish protocol saturation or reproduce every historical validity check.

Each run creates a unique database and pre-creates the series. Output directories must be new. Results and server data are retained; stopping does not remove them. After initialization failures, inspect the output and server logs before retrying with a new output directory.

## Results

`result.json` includes successful-acknowledgment throughput (`throughput_kpt_s`), full RPC mean/p50/p99 (`rpc_mean_ms`, `rpc_p50_ms`, `rpc_p99_ms`), queue-inclusive p50/p99 (`p50_ms`, `p99_ms`), generated/sent/success/failed/unsent counts, backlog, and mergeable histograms. Latency samples are successful requests completed in the configured measurement window; percentiles use approximately 1%-wide histogram bins. A failed write produces a nonzero exit and preserves diagnostics.

`timeseries.csv`, `acknowledged.csv`, `samples.csv`, and `client.log` retain per-second counters, acknowledged point counts, sample values, and client diagnostics. This basic runner does not perform automatic readback or asynchronous replication catch-up validation. IoTConsensus reports local asynchronous acknowledgment, which is not durable quorum acknowledgment. Do not interpret one run or a client concurrency limit as a sustainable protocol maximum.

See the [full paper with appendix](../supplementary/appendix.pdf) for the complete manuscript, proofs, and partition-size and disorder-probability results.
