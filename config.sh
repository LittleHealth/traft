#!/bin/bash
# =============================================================================
# config.sh — Central configuration for the IoTDB cluster experiment.
#
# Edit the variables in this file to match your local environment before
# running run.sh or stop.sh.
# =============================================================================

# -- Repository root (auto-detected; override if needed) ---------------------
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# -- IoTDB distribution -------------------------------------------------------
# Version string that matches the zip filename (without .zip).
IOTDB_VERSION="apache-iotdb-2.0.7-SNAPSHOT-all-bin"

# Path to the IoTDB all-in-one zip.
# Download a release build from https://iotdb.apache.org/Download/
# or build from source, then place the zip here.
IOTDB_ZIP="${REPO_ROOT}/downloads/${IOTDB_VERSION}.zip"

# -- Cluster layout -----------------------------------------------------------
CLUSTER_DIR="${REPO_ROOT}/cluster"
NODE_COUNT=3          # Number of ConfigNode + DataNode pairs

# -- Port base values (node i uses base_port + i - 1) ------------------------
CN_INTERNAL_PORT=11710
CN_CONS_PORT=11720
CN_METRIC_REPORTER_PORT=9091   # ConfigNode Prometheus exporter: 9091, 9092, 9093

DN_RPC_PORT=6667               # DataNode client RPC: 6667, 6668, 6669
DN_INTERNAL_PORT=10700
DN_METRIC_REPORTER_PORT=9191   # DataNode Prometheus exporter: 9191, 9192, 9193
DN_MPP_DATA_EXCHANGE_PORT=10800
DN_SCHEMA_CONS_PORT=10900
DN_DATA_CONS_PORT=11000

# -- Monitoring stack ---------------------------------------------------------
# Download Prometheus from https://prometheus.io/download/
# and Grafana from https://grafana.com/grafana/download
# Place the tarballs in downloads/ and set the paths below.
PROMETHEUS_TAR="${REPO_ROOT}/downloads/prometheus.tar.gz"
GRAFANA_TAR="${REPO_ROOT}/downloads/grafana.tar.gz"

PROMETHEUS_DIR="${CLUSTER_DIR}/prometheus"
GRAFANA_DIR="${CLUSTER_DIR}/grafana"
PROMETHEUS_CONFIG="${PROMETHEUS_DIR}/prometheus.yml"

# -- iot-benchmark ------------------------------------------------------------
# Unzip iot-benchmark-iotdb-2.0.zip into benchmark/ before running.
# Download from https://github.com/thulab/iot-benchmark/releases
BM_RUN_DIR="${REPO_ROOT}/benchmark/iot-benchmark-iotdb-2.0"

# Benchmark config profiles bundled in this repo (see benchmark/ directory).
BM_CONF_DIR="${REPO_ROOT}/benchmark"
