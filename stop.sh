#!/bin/bash
# =============================================================================
# stop.sh — Stop processes and/or clean data for the IoTDB cluster.
#
# Usage:
#   ./stop.sh stop              Stop all nodes, Prometheus and Grafana
#   ./stop.sh stop <N>          Stop DataNode N only (e.g. ./stop.sh stop 2)
#   ./stop.sh stop iotdb        Stop ConfigNodes and DataNodes only
#   ./stop.sh stop prometheus   Stop Prometheus and Grafana only
#
#   ./stop.sh clean             Delete all data / log directories
#   ./stop.sh clean <N>         Delete data/logs for DataNode N only
#   ./stop.sh clean iotdb       Delete data/logs for all IoTDB nodes
#   ./stop.sh clean prometheus  Delete Prometheus and Grafana data
# =============================================================================

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/config.sh"

MODE="$1"
TARGET="$2"

CN_COUNT=$(pgrep -f ConfigNode | wc -l | tr -d ' ')
DN_COUNT=$(pgrep -f DataNode | wc -l | tr -d ' ')
PROM_COUNT=$(pgrep -f prometheus | wc -l | tr -d ' ')
GRAF_COUNT=$(pgrep -f grafana-server | wc -l | tr -d ' ')

# =============================================================================
# clean — remove data and log directories
# =============================================================================
if [[ "$MODE" == "clean" ]]; then

  if [[ -z "$TARGET" ]]; then
    # Guard: refuse to clean while processes are still running
    if [[ $CN_COUNT -gt 0 || $DN_COUNT -gt 0 || $PROM_COUNT -gt 0 || $GRAF_COUNT -gt 0 ]]; then
      echo "ERROR: Processes still running (CN=$CN_COUNT, DN=$DN_COUNT, Prometheus=$PROM_COUNT, Grafana=$GRAF_COUNT)."
      echo "       Run './stop.sh stop' first."
      exit 1
    fi
    echo "Cleaning all data and log directories..."
    rm -rf "${CLUSTER_DIR}"/confignode*/*/data
    rm -rf "${CLUSTER_DIR}"/datanode*/*/data
    rm -rf "${CLUSTER_DIR}"/confignode*/*/logs
    rm -rf "${CLUSTER_DIR}"/datanode*/*/logs
    rm -rf "${CLUSTER_DIR}"/grafana/data
    echo "Done. All node data and logs removed."
    exit 0

  elif [[ "$TARGET" =~ ^[0-9]+$ ]]; then
    echo "Cleaning data and logs for datanode${TARGET}..."
    rm -rf "${CLUSTER_DIR}/datanode${TARGET}/*/data"
    rm -rf "${CLUSTER_DIR}/datanode${TARGET}/*/logs"
    echo "Done."
    exit 0

  elif [[ "$TARGET" == "iotdb" ]]; then
    echo "Cleaning data and logs for all IoTDB nodes..."
    rm -rf "${CLUSTER_DIR}"/confignode*/*/data
    rm -rf "${CLUSTER_DIR}"/datanode*/*/data
    rm -rf "${CLUSTER_DIR}"/confignode*/*/logs
    rm -rf "${CLUSTER_DIR}"/datanode*/*/logs
    echo "Done."
    exit 0

  elif [[ "$TARGET" == "prometheus" ]]; then
    echo "Cleaning Prometheus and Grafana data..."
    rm -rf "${CLUSTER_DIR}"/grafana/data
    echo "Done."
    exit 0
  fi
fi

# =============================================================================
# stop — kill processes
# =============================================================================
if [[ "$MODE" == "stop" ]]; then

  if [[ -z "$TARGET" ]]; then
    echo "Stopping all processes..."
    pkill -f ConfigNode   2>/dev/null || true
    pkill -f DataNode     2>/dev/null || true
    pkill -f prometheus   2>/dev/null || true
    pkill -f grafana-server 2>/dev/null || true

  elif [[ "$TARGET" =~ ^[0-9]+$ ]]; then
    echo "Stopping datanode${TARGET}..."
    DN_STOP="${CLUSTER_DIR}/datanode${TARGET}/${IOTDB_VERSION}/sbin/stop-datanode.sh"
    if [[ -f "$DN_STOP" ]]; then
      bash "$DN_STOP"
    fi
    DN_PID=$(pgrep -f "datanode${TARGET}" 2>/dev/null || true)
    if [[ -n "$DN_PID" ]]; then
      kill -9 $DN_PID 2>/dev/null || true
    fi

  elif [[ "$TARGET" == "iotdb" ]]; then
    echo "Stopping all ConfigNodes and DataNodes..."
    pkill -f ConfigNode 2>/dev/null || true
    pkill -f DataNode   2>/dev/null || true

  elif [[ "$TARGET" == "prometheus" ]]; then
    echo "Stopping Prometheus and Grafana..."
    pkill -f prometheus     2>/dev/null || true
    pkill -f grafana-server 2>/dev/null || true
  fi

  sleep 1
  CN_LEFT=$(pgrep -f ConfigNode | wc -l | tr -d ' ')
  DN_LEFT=$(pgrep -f DataNode | wc -l | tr -d ' ')
  PROM_LEFT=$(pgrep -f prometheus | wc -l | tr -d ' ')
  GRAF_LEFT=$(pgrep -f grafana-server | wc -l | tr -d ' ')

  echo "Remaining: ConfigNode=$CN_LEFT, DataNode=$DN_LEFT, Prometheus=$PROM_LEFT, Grafana=$GRAF_LEFT"
  if [[ $CN_LEFT -eq 0 && $DN_LEFT -eq 0 && $PROM_LEFT -eq 0 && $GRAF_LEFT -eq 0 ]]; then
    echo "All processes stopped."
  else
    echo "WARNING: Some processes are still running. Check manually with: ps aux | grep -E 'ConfigNode|DataNode|prometheus|grafana'"
  fi
  exit 0
fi

# =============================================================================
# Usage
# =============================================================================
echo "Usage:"
echo "  ./stop.sh stop              Stop all processes"
echo "  ./stop.sh stop <N>          Stop DataNode N"
echo "  ./stop.sh stop iotdb        Stop IoTDB nodes only"
echo "  ./stop.sh stop prometheus   Stop Prometheus and Grafana only"
echo ""
echo "  ./stop.sh clean             Delete all data and logs"
echo "  ./stop.sh clean <N>         Delete DataNode N data/logs"
echo "  ./stop.sh clean iotdb       Delete IoTDB data/logs"
echo "  ./stop.sh clean prometheus  Delete Prometheus/Grafana data"
exit 1
