#!/bin/bash
# =============================================================================
# run.sh — Bootstrap and run the IoTDB cluster with metrics collection.
#
# Usage:
#   ./run.sh [CONSENSUS_TYPE] [BENCHMARK_PROFILE]
#
#   CONSENSUS_TYPE   : traft | ratis | pipe   (default: traft)
#   BENCHMARK_PROFILE: conf-small | conf-medium | conf-large
#                      (default: conf-small)
#
# Example:
#   ./run.sh traft conf-medium
#
# Prerequisites — edit config.sh first:
#   1. Place the IoTDB distribution zip at $IOTDB_ZIP
#   2. Place Prometheus tarball at $PROMETHEUS_TAR
#   3. Place Grafana tarball at $GRAFANA_TAR
#   4. Unzip iot-benchmark into $BM_RUN_DIR
# =============================================================================

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/config.sh"

# -- Parse arguments ----------------------------------------------------------
CONSENSUS_TYPE="${1:-traft}"
BM_PROFILE="${2:-conf-small}"

case "$CONSENSUS_TYPE" in
  ratis) CONSENSUS_CLASS="org.apache.iotdb.consensus.ratis.RatisConsensus" ;;
  pipe)  CONSENSUS_CLASS="org.apache.iotdb.consensus.iot.IoTConsensusV2" ;;
  traft) CONSENSUS_CLASS="org.apache.iotdb.consensus.traft.TRaftConsensus" ;;
  *)
    echo "ERROR: Unknown consensus type '$CONSENSUS_TYPE'. Use: traft | ratis | pipe"
    exit 1
    ;;
esac

BM_CONF_FILE="${BM_CONF_DIR}/${BM_PROFILE}/config.properties"
if [[ ! -f "$BM_CONF_FILE" ]]; then
  echo "ERROR: Benchmark config not found: $BM_CONF_FILE"
  echo "       Available profiles: conf-small, conf-medium, conf-large"
  exit 1
fi

echo "======================================================"
echo " IoTDB Cluster Experiment"
echo " Consensus : $CONSENSUS_TYPE ($CONSENSUS_CLASS)"
echo " Benchmark : $BM_PROFILE"
echo "======================================================"

# =============================================================================
# Helper: check whether nodes are already running
# Returns: 0 = no nodes running (safe to start)
#          1 = partial nodes running (manual cleanup required)
#          2 = all nodes already running (skip startup)
# =============================================================================
before_start_check() {
  PROM_RUNNING=$(pgrep -f prometheus | wc -l | tr -d ' ')
  GRAFANA_RUNNING=$(pgrep -f grafana | wc -l | tr -d ' ')
  DN_COUNT=$(pgrep -f DataNode | wc -l | tr -d ' ')
  CN_COUNT=$(pgrep -f ConfigNode | wc -l | tr -d ' ')

  echo "Running processes: ConfigNode=$CN_COUNT, DataNode=$DN_COUNT, Prometheus=$PROM_RUNNING, Grafana=$GRAFANA_RUNNING"

  if [[ $DN_COUNT -ge $NODE_COUNT && $CN_COUNT -ge $NODE_COUNT ]]; then
    echo "All $NODE_COUNT ConfigNodes and $NODE_COUNT DataNodes are already running — skipping startup."
    return 2
  elif [[ $DN_COUNT -gt 0 || $CN_COUNT -gt 0 ]]; then
    echo "WARNING: Partial nodes detected (DataNode=$DN_COUNT, ConfigNode=$CN_COUNT)."
    echo "         Run './stop.sh stop' then './stop.sh clean' before retrying."
    return 1
  else
    echo "No nodes running. Ready to initialize the cluster."
    return 0
  fi
}

# =============================================================================
# Helper: confirm all nodes are up and show cluster status
# =============================================================================
after_start_check() {
  DN_COUNT=$(pgrep -f DataNode | wc -l | tr -d ' ')
  CN_COUNT=$(pgrep -f ConfigNode | wc -l | tr -d ' ')
  echo "Detected $DN_COUNT DataNode(s) and $CN_COUNT ConfigNode(s) running."
  CLI_PATH="${CLUSTER_DIR}/datanode1/${IOTDB_VERSION}/sbin/start-cli.sh"
  if [[ -f "$CLI_PATH" ]]; then
    bash "$CLI_PATH" -h "127.0.0.1" -e "show cluster;"
  fi
}

# =============================================================================
# Step 1: Unzip the IoTDB distribution into each node directory
# =============================================================================
init_node_dirs() {
  echo ""
  echo "[Step 1] Unpacking IoTDB distribution into node directories..."

  if [[ ! -f "$IOTDB_ZIP" ]]; then
    echo "ERROR: IoTDB zip not found at $IOTDB_ZIP"
    echo "       Download it and update IOTDB_ZIP in config.sh"
    exit 1
  fi

  mkdir -p "$CLUSTER_DIR"

  for ((i=1; i<=NODE_COUNT; i++)); do
    CN_PATH="${CLUSTER_DIR}/confignode${i}/${IOTDB_VERSION}"
    DN_PATH="${CLUSTER_DIR}/datanode${i}/${IOTDB_VERSION}"

    if [[ -d "$CN_PATH" ]]; then
      echo "  confignode${i}: already unpacked — skipping."
    else
      echo "  confignode${i}: unpacking..."
      unzip -q "$IOTDB_ZIP" -d "${CLUSTER_DIR}/confignode${i}"
    fi

    if [[ -d "$DN_PATH" ]]; then
      echo "  datanode${i}: already unpacked — skipping."
    else
      echo "  datanode${i}: unpacking..."
      unzip -q "$IOTDB_ZIP" -d "${CLUSTER_DIR}/datanode${i}"
    fi
  done
}

# =============================================================================
# Step 2: Write iotdb-system.properties for every node
# =============================================================================
write_config() {
  echo ""
  echo "[Step 2] Writing iotdb-system.properties for each node..."

  for ((i=1; i<=NODE_COUNT; i++)); do
    CN_DIR="${CLUSTER_DIR}/confignode${i}/${IOTDB_VERSION}"
    DN_DIR="${CLUSTER_DIR}/datanode${i}/${IOTDB_VERSION}"
    CN_CONF="${CN_DIR}/conf/iotdb-system.properties"
    DN_CONF="${DN_DIR}/conf/iotdb-system.properties"

    CN_PORT=$((CN_INTERNAL_PORT + i - 1))
    CN_CONS=$((CN_CONS_PORT + i - 1))
    CN_METRIC=$((CN_METRIC_REPORTER_PORT + i - 1))

    RPC=$((DN_RPC_PORT + i - 1))
    INT=$((DN_INTERNAL_PORT + i - 1))
    XCHG=$((DN_MPP_DATA_EXCHANGE_PORT + i - 1))
    SCH=$((DN_SCHEMA_CONS_PORT + i - 1))
    DAT=$((DN_DATA_CONS_PORT + i - 1))
    MET=$((DN_METRIC_REPORTER_PORT + i - 1))

    # ConfigNode config
    cat > "$CN_CONF" <<EOF
cluster_name=defaultCluster
cn_internal_address=127.0.0.1
cn_internal_port=$CN_PORT
cn_consensus_port=$CN_CONS
cn_seed_config_node=127.0.0.1:$CN_INTERNAL_PORT
cn_metric_reporter_list=PROMETHEUS
cn_metric_prometheus_reporter_port=$CN_METRIC
cn_metric_level=IMPORTANT

dn_rpc_address=0.0.0.0
dn_rpc_port=$RPC
dn_internal_address=127.0.0.1
dn_internal_port=$INT
dn_seed_config_node=127.0.0.1:$CN_INTERNAL_PORT
dn_mpp_data_exchange_port=$XCHG
dn_schema_region_consensus_port=$SCH
dn_data_region_consensus_port=$DAT
dn_data_dirs=data/datanode${i}/data
dn_wal_dirs=data/datanode${i}/wal
dn_metric_reporter_list=PROMETHEUS
dn_metric_prometheus_reporter_port=$MET
dn_metric_level=IMPORTANT

schema_replication_factor=3
data_replication_factor=3
data_region_consensus_protocol_class=$CONSENSUS_CLASS

seq_memtable_flush_check_interval_in_ms=300
target_chunk_point_num=10000
candidate_compaction_task_queue_size=5
EOF

    # DataNode config (identical layout — DataNode reads both its own and CN sections)
    cat > "$DN_CONF" <<EOF
cluster_name=defaultCluster
cn_internal_address=127.0.0.1
cn_internal_port=$CN_PORT
cn_consensus_port=$CN_CONS
cn_seed_config_node=127.0.0.1:$CN_INTERNAL_PORT
cn_metric_reporter_list=PROMETHEUS
cn_metric_prometheus_reporter_port=$CN_METRIC
cn_metric_level=IMPORTANT

dn_rpc_address=0.0.0.0
dn_rpc_port=$RPC
dn_internal_address=127.0.0.1
dn_internal_port=$INT
dn_seed_config_node=127.0.0.1:$CN_INTERNAL_PORT
dn_mpp_data_exchange_port=$XCHG
dn_schema_region_consensus_port=$SCH
dn_data_region_consensus_port=$DAT
dn_data_dirs=data/datanode${i}/data
dn_wal_dirs=data/datanode${i}/wal
dn_metric_reporter_list=PROMETHEUS
dn_metric_prometheus_reporter_port=$MET
dn_metric_level=IMPORTANT

schema_replication_factor=3
data_replication_factor=3
data_region_consensus_protocol_class=$CONSENSUS_CLASS

seq_memtable_flush_check_interval_in_ms=300
target_chunk_point_num=10000
candidate_compaction_task_queue_size=5
EOF

    echo "  node${i}: config written (CN port=$CN_PORT, DN RPC port=$RPC)"
  done
}

# =============================================================================
# Step 3: Start all ConfigNodes, then DataNodes
# =============================================================================
start_iotdb_nodes() {
  echo ""
  echo "[Step 3] Starting ConfigNodes and DataNodes..."

  for ((i=1; i<=NODE_COUNT; i++)); do
    CN_DIR="${CLUSTER_DIR}/confignode${i}/${IOTDB_VERSION}"
    echo "  Starting confignode${i}..."
    nohup bash "${CN_DIR}/sbin/start-confignode.sh" > /dev/null 2>&1 &
  done

  # Wait for ConfigNodes to form a quorum before starting DataNodes
  echo "  Waiting 10s for ConfigNodes to elect a leader..."
  sleep 10

  for ((i=1; i<=NODE_COUNT; i++)); do
    DN_DIR="${CLUSTER_DIR}/datanode${i}/${IOTDB_VERSION}"
    echo "  Starting datanode${i}..."
    nohup bash "${DN_DIR}/sbin/start-datanode.sh" > /dev/null 2>&1 &
  done
}

# =============================================================================
# Step 4: Start Prometheus metrics scraper
# =============================================================================
start_prometheus() {
  echo ""
  echo "[Step 4] Starting Prometheus..."

  if [[ -d "$PROMETHEUS_DIR" && -f "${PROMETHEUS_DIR}/prometheus" ]]; then
    echo "  Prometheus binary found — skipping extraction."
  else
    if [[ ! -f "$PROMETHEUS_TAR" ]]; then
      echo "  WARNING: Prometheus tarball not found at $PROMETHEUS_TAR — skipping."
      return
    fi
    mkdir -p "$PROMETHEUS_DIR"
    tar -xzf "$PROMETHEUS_TAR" -C "$PROMETHEUS_DIR" --strip-components=1
  fi

  # Generate prometheus.yml to scrape all CN and DN metric endpoints
  cat > "$PROMETHEUS_CONFIG" <<EOF
global:
  scrape_interval: 15s
  evaluation_interval: 15s

alerting:
  alertmanagers:
    - static_configs:
        - targets: []

rule_files: []

scrape_configs:
  - job_name: iotdb-cluster
    honor_labels: true
    honor_timestamps: true
    scrape_interval: 15s
    scrape_timeout: 10s
    metrics_path: /metrics
    scheme: http
    static_configs:
      - targets:
EOF

  for ((i=1; i<=NODE_COUNT; i++)); do
    CN_PORT=$((CN_METRIC_REPORTER_PORT + i - 1))
    DN_PORT=$((DN_METRIC_REPORTER_PORT + i - 1))
    echo "          - 127.0.0.1:$CN_PORT" >> "$PROMETHEUS_CONFIG"
    echo "          - 127.0.0.1:$DN_PORT" >> "$PROMETHEUS_CONFIG"
  done

  nohup "${PROMETHEUS_DIR}/prometheus" \
    --config.file="$PROMETHEUS_CONFIG" \
    > "${PROMETHEUS_DIR}/prometheus.log" 2>&1 &

  echo "  Prometheus started. UI: http://<host>:9090"
}

# =============================================================================
# Step 5: Start Grafana dashboard
# =============================================================================
start_grafana() {
  echo ""
  echo "[Step 5] Starting Grafana..."

  if [[ -d "$GRAFANA_DIR" && -f "${GRAFANA_DIR}/bin/grafana-server" ]]; then
    echo "  Grafana binary found — skipping extraction."
  else
    if [[ ! -f "$GRAFANA_TAR" ]]; then
      echo "  WARNING: Grafana tarball not found at $GRAFANA_TAR — skipping."
      return
    fi
    mkdir -p "$GRAFANA_DIR"
    tar -xzf "$GRAFANA_TAR" -C "$GRAFANA_DIR" --strip-components=1
  fi

  nohup "${GRAFANA_DIR}/bin/grafana-server" \
    --homepath "$GRAFANA_DIR" \
    > "${GRAFANA_DIR}/grafana.log" 2>&1 &

  echo "  Grafana started. UI: http://<host>:3000 (admin/admin)"
  echo "  Import IoTDB dashboards manually via the Grafana UI."
}

# =============================================================================
# Step 6: Copy benchmark profile and run iot-benchmark
# =============================================================================
start_benchmark() {
  echo ""
  echo "[Step 6] Starting iot-benchmark with profile: $BM_PROFILE..."

  if [[ ! -d "$BM_RUN_DIR" ]]; then
    echo "  ERROR: iot-benchmark not found at $BM_RUN_DIR"
    echo "         Unzip iot-benchmark-iotdb-2.0.zip into ${REPO_ROOT}/benchmark/"
    exit 1
  fi

  echo "  Applying config profile: $BM_CONF_FILE"
  cp "$BM_CONF_FILE" "${BM_RUN_DIR}/conf/config.properties"
  echo "  Active config (first 10 non-comment lines):"
  grep -v '^#' "${BM_RUN_DIR}/conf/config.properties" | grep -v '^$' | head -10 | sed 's/^/    /'

  mkdir -p "${BM_RUN_DIR}/logs"
  nohup bash "${BM_RUN_DIR}/benchmark.sh" \
    > "${BM_RUN_DIR}/logs/benchmark.log" 2>&1 &

  echo "  Benchmark started. Following log output (Ctrl-C to stop tailing):"
  echo "  (The benchmark process continues running in the background.)"
  tail -f "${BM_RUN_DIR}/logs/benchmark.log"
}

# =============================================================================
# Main execution flow
# =============================================================================
before_start_check
CHECK=$?

if [[ $CHECK -eq 1 ]]; then
  echo "Aborting. Clean up partial nodes first with: ./stop.sh stop && ./stop.sh clean"
  exit 1
fi

if [[ $CHECK -eq 0 ]]; then
  init_node_dirs
  write_config
  start_iotdb_nodes
  echo ""
  echo "Waiting 15s for all nodes to finish joining the cluster..."
  sleep 15
  after_start_check
fi

start_prometheus
start_grafana

echo ""
echo "Cluster is ready. Starting benchmark in 5s..."
sleep 5
start_benchmark
