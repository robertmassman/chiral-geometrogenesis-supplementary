#!/bin/bash
# Priority 6: η Precision Campaign — AWS Remote Runner
# =====================================================
#
# This script runs on the EC2 instance. It:
#   1. Compiles soup_multi_stella.c for Linux
#   2. Runs all 16 campaign jobs (GNU parallel, 2 at a time × 8 threads)
#   3. Saves logs to ~/p6_logs/
#   4. Creates a tarball for download when done
#
# Usage (on EC2):
#   chmod +x aws_p6_campaign.sh
#   nohup ./aws_p6_campaign.sh > campaign_master.log 2>&1 &

set -euo pipefail

WORKDIR="$HOME/p6_campaign"
LOGDIR="$WORKDIR/logs"
BINARY="$WORKDIR/soup_multi_stella_wf"
SOURCE="$WORKDIR/soup_multi_stella.c"

LATTICE_SIZE=2
CROSS_RATE=0.0
MUTATION_RATE=0.001
CENSUS_INTERVAL=50000
CHECK_INTERVAL=50000
LOG_INTERVAL=100000
THREADS_PER_JOB=8
PARALLEL_JOBS=2

mkdir -p "$LOGDIR"

echo "=============================================="
echo "Priority 6: eta Precision Campaign (AWS)"
echo "=============================================="
echo "Started: $(date)"
echo "Host: $(hostname)"
echo "CPUs: $(nproc)"
echo ""

# ---- 1. Install build tools ----
echo "[1/4] Installing build tools..."
if ! command -v gcc &>/dev/null; then
    sudo dnf install -y gcc make
fi
if ! command -v parallel &>/dev/null; then
    sudo dnf install -y parallel
fi
echo "  gcc: $(gcc --version | head -1)"
echo ""

# ---- 2. Compile ----
echo "[2/4] Compiling soup_multi_stella.c..."
gcc -O3 -march=native -ffast-math -flto \
    -o "$BINARY" "$SOURCE" -lm -lpthread
echo "  Binary: $BINARY ($(stat --printf='%s' "$BINARY") bytes)"
echo ""

# ---- 3. Define jobs ----
# Format: nsub pairing seed epochs
JOBS=(
    "200 local  789  5000000"
    "200 local  1024 5000000"
    "200 global 789  5000000"
    "200 global 1024 5000000"
    "283 local  789  5000000"
    "283 local  1024 5000000"
    "283 global 789  5000000"
    "283 global 1024 5000000"
    "400 local  789  5000000"
    "400 local  1024 5000000"
    "400 global 789  5000000"
    "400 global 1024 5000000"
    "548 local  789  2000000"
    "548 local  1024 2000000"
    "548 global 789  2000000"
    "548 global 1024 2000000"
)

echo "[3/4] Running ${#JOBS[@]} jobs (${PARALLEL_JOBS} parallel × ${THREADS_PER_JOB} threads)..."
echo ""

# ---- 4. Run jobs ----
run_one() {
    local nsub=$1 pairing=$2 seed=$3 epochs=$4
    local logfile="$LOGDIR/nsub${nsub}_${pairing}_s${seed}.log"
    local label="nsub=$nsub $pairing seed=$seed ${epochs}ep"

    local cmd="$BINARY --lattice-size $LATTICE_SIZE --n-sub $nsub \
        --epochs $epochs --cross-rate $CROSS_RATE \
        --mutation-rate $MUTATION_RATE \
        --census-interval $CENSUS_INTERVAL \
        --check-interval $CHECK_INTERVAL \
        --log-interval $LOG_INTERVAL \
        --seed $seed --threads $THREADS_PER_JOB"

    if [ "$pairing" = "global" ]; then
        cmd="$cmd --global"
    fi

    echo "[START $(date +%H:%M:%S)] $label"
    local t0=$(date +%s)
    eval $cmd > "$logfile" 2>&1
    local rc=$?
    local t1=$(date +%s)
    local elapsed=$(( t1 - t0 ))
    local hours=$(echo "scale=1; $elapsed / 3600" | bc)

    if [ $rc -eq 0 ]; then
        echo "[DONE  $(date +%H:%M:%S)] $label — OK in ${hours}h"
    else
        echo "[FAIL  $(date +%H:%M:%S)] $label — rc=$rc in ${hours}h"
    fi
}
export -f run_one
export BINARY LOGDIR LATTICE_SIZE CROSS_RATE MUTATION_RATE
export CENSUS_INTERVAL CHECK_INTERVAL LOG_INTERVAL THREADS_PER_JOB

# Use GNU parallel to manage the job queue
printf '%s\n' "${JOBS[@]}" | parallel -j $PARALLEL_JOBS --colsep ' ' \
    run_one {1} {2} {3} {4}

echo ""
echo "[4/4] Packaging results..."
cd "$WORKDIR"
tar czf ~/p6_results.tar.gz -C "$LOGDIR" .

echo ""
echo "=============================================="
echo "CAMPAIGN COMPLETE"
echo "=============================================="
echo "Finished: $(date)"
echo "Logs: $LOGDIR/"
echo "Tarball: ~/p6_results.tar.gz"
echo ""
echo "Download with:"
echo "  scp -i ~/.ssh/stella-compute.pem ec2-user@<IP>:~/p6_results.tar.gz ."
ls -la "$LOGDIR/"
