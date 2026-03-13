# IoTDB Cluster Experiment — Reproducibility Package

This repository contains the scripts and benchmark configuration files needed to reproduce the cluster experiments reported in the paper.

The setup runs a **3-ConfigNode + 3-DataNode** IoTDB cluster — deployable on a single machine or across servers — with Prometheus scraping internal metrics from every node, and `iot-benchmark` driving the write workload.

---

## Repository Structure

```
.
├── config.sh                          # Central configuration (paths, ports, versions)
├── run.sh                             # Bootstrap cluster + monitoring + benchmark
├── stop.sh                            # Stop processes and/or clean data
├── benchmark/
│   ├── conf-small/
│   │   └── config.properties          # Small: 10 devices × 100 sensors, 1 000 loops (in-order)
│   ├── conf-medium/
│   │   └── config.properties          # Medium: 100 devices × 100 sensors, 10 000 loops (out-of-order)
│   └── conf-large/
│       └── config.properties          # Large: 1 000 devices × 1 000 sensors, 10 000 000 loops (in-order)
├── downloads/                         # Place binary archives here (not tracked by git)
└── .gitignore
```

---

## Prerequisites

| Requirement | Version | Notes |
|---|---|---|
| macOS or Linux | — | Scripts use `bash` and POSIX utilities |
| Java (JDK) | 17 or above | Required by IoTDB |
| `unzip` | any | For extracting IoTDB |
| `tar` | any | For extracting Prometheus / Grafana |

### Binary downloads

The following archives must be downloaded manually and placed in the `downloads/` directory.

**IoTDB** (required)

Download or build the all-in-one binary for the version used in the paper:

```
downloads/apache-iotdb-2.0.7-SNAPSHOT-all-bin.zip
```

- Official releases: <https://iotdb.apache.org/Download/>
- To build from source: `mvn package -pl distribution -am -DskipTests -P with-cpp`

**Prometheus** (optional — needed for metrics collection)

```
downloads/prometheus.tar.gz
```

Download from <https://prometheus.io/download/> (tested with v2.45.x).
Rename the tarball to `prometheus.tar.gz` after downloading.

**Grafana** (optional — needed for dashboard visualisation)

```
downloads/grafana.tar.gz
```

Download from <https://grafana.com/grafana/download> (tested with v11.0.x).
Rename the tarball to `grafana.tar.gz` after downloading.

**iot-benchmark** (required for benchmark runs)

Unzip `iot-benchmark-iotdb-2.0.zip` into:

```
benchmark/iot-benchmark-iotdb-2.0/
```

Source and releases: <https://github.com/thulab/iot-benchmark>

---

## Quick Start

### 1. Configure paths

Open `config.sh` and verify that `IOTDB_VERSION` and the `downloads/` paths match the filenames you downloaded:

```bash
IOTDB_VERSION="apache-iotdb-2.0.7-SNAPSHOT-all-bin"
IOTDB_ZIP="${REPO_ROOT}/downloads/${IOTDB_VERSION}.zip"
PROMETHEUS_TAR="${REPO_ROOT}/downloads/prometheus.tar.gz"
GRAFANA_TAR="${REPO_ROOT}/downloads/grafana.tar.gz"
BM_RUN_DIR="${REPO_ROOT}/benchmark/iot-benchmark-iotdb-2.0"
```

### 2. Make scripts executable

```bash
chmod +x run.sh stop.sh
```

### 3. Run the experiment

```bash
# Main experiment (TRaft consensus, medium workload — matches the paper)
./run.sh traft conf-medium

# Small-scale baseline (in-order write)
./run.sh traft conf-small

# Large-scale stress test
./run.sh traft conf-large

# Alternative consensus protocols
./run.sh ratis conf-medium
./run.sh pipe  conf-medium
```

`run.sh` performs the following steps automatically:

1. Unpack IoTDB into `cluster/confignode{1-3}/` and `cluster/datanode{1-3}/`
2. Write `iotdb-system.properties` for each node (ports, consensus, metrics)
3. Start 3 ConfigNodes, wait for leader election, then start 3 DataNodes
4. Wait for the cluster to stabilize and run `show cluster;`
5. Start Prometheus (scrapes all 6 metric endpoints)
6. Start Grafana
7. Copy the selected benchmark profile and launch `iot-benchmark`

### 4. Observe metrics

| Service | URL |
|---|---|
| Prometheus | `http://<host>:9090` |
| Grafana | `http://<host>:3000` (default credentials: `admin` / `admin`) |

Import the official IoTDB dashboards from the Grafana UI:
*Dashboards → Import → upload JSON* — dashboard JSON files can be found in the IoTDB repository under `grafana/`.

### 5. Stop and clean up

```bash
# Stop all processes
./stop.sh stop

# Delete all generated data and logs (keeps binaries intact)
./stop.sh clean

# To start fresh completely, also delete the unpacked node directories
rm -rf cluster/confignode* cluster/datanode*
```

---

## Cluster Architecture

```
<host>
│
├─ ConfigNode 1   internal=11710  consensus=11720  metrics=9091
├─ ConfigNode 2   internal=11711  consensus=11721  metrics=9092
├─ ConfigNode 3   internal=11712  consensus=11722  metrics=9093
│
├─ DataNode 1     rpc=6667  internal=10700  metrics=9191
├─ DataNode 2     rpc=6668  internal=10701  metrics=9192
└─ DataNode 3     rpc=6669  internal=10702  metrics=9193
                                    │
                             Prometheus :9090
                             (scrapes all 6 nodes every 15 s)
                                    │
                              Grafana :3000
```

By default all nodes bind to `127.0.0.1`. For remote deployment, update `cn_internal_address` / `dn_internal_address` in `config.sh` to the actual host IP. The seed ConfigNode address must be reachable by all other nodes.

---

## Benchmark Profiles

| Profile | Devices | Sensors | Loops | Out-of-order | Use case |
|---|---|---|---|---|---|
| `conf-small` | 10 | 100 | 1 000 | No | In-order baseline |
| `conf-medium` | 100 | 100 | 10 000 | Yes (Poisson) | Main paper experiment |
| `conf-large` | 1 000 | 1 000 | 10 000 000 | No | Large-scale stress test |

All profiles use:
- `DB_SWITCH=IoTDB-200-SESSION_BY_TABLET`
- `IoTDB_DIALECT_MODE=tree`
- Write-only workload (`OPERATION_PROPORTION=1:0:0:0:0:0:0:0:0:0:0:0`)
- 10 concurrent data clients, 10 schema clients

---

## Consensus Protocols

| Argument | Class | Description |
|---|---|---|
| `traft` | `TRaftConsensus` | TRaft — the consensus algorithm evaluated in the paper |
| `ratis` | `RatisConsensus` | Apache Ratis (baseline comparison) |
| `pipe` | `IoTConsensusV2` | IoTConsensus V2 pipe-based replication |

---

## IoTDB Configuration Parameters

The following non-default parameters are set by `run.sh` for every node:

| Parameter | Value | Purpose |
|---|---|---|
| `schema_replication_factor` | 3 | Every schema region is replicated to all 3 nodes |
| `data_replication_factor` | 3 | Every data region is replicated to all 3 nodes |
| `cn_metric_level` / `dn_metric_level` | `IMPORTANT` | Enable Prometheus metric export |
| `seq_memtable_flush_check_interval_in_ms` | 300 | More frequent memtable flush checks |
| `target_chunk_point_num` | 10 000 | Target chunk size for compaction |
| `candidate_compaction_task_queue_size` | 5 | Compaction task queue depth |

---

## Troubleshooting

**`unzip: command not found`** — Install `unzip` (e.g. `brew install unzip` on macOS).

**Nodes fail to start** — Check logs in `cluster/confignode1/.../logs/` and `cluster/datanode1/.../logs/`.

**Port already in use** — Run `./stop.sh stop && ./stop.sh clean`, or edit port base values in `config.sh`.

**`show cluster;` shows fewer than 3 nodes** — The DataNodes may still be joining. Wait 10–20 seconds and re-run the CLI command:
```bash
cluster/datanode1/apache-iotdb-*/sbin/start-cli.sh -h 127.0.0.1 -e "show cluster;"
```

**Prometheus shows no data** — Confirm `cn_metric_reporter_list=PROMETHEUS` is in each node's config and the node has fully started (check `cluster_status` in `show cluster;`).
