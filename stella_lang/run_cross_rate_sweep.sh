#!/bin/bash
# Cross-rate sweep at fixed L=4 (32 stellae, n_sub=100)
# Varies cross_rate over {0.01, 0.1, 1.0, 10.0}
#
# Expected inter-stella interactions per epoch (n_fcc=32):
#   cross_rate=0.01 -> 1 interaction/epoch  (minimum clamp)
#   cross_rate=0.1  -> 3 interactions/epoch
#   cross_rate=1.0  -> 32 interactions/epoch
#   cross_rate=10.0 -> 320 interactions/epoch
#
# Each run: ~5M epochs
# Re-run 2026-03-11: all 4 rates included (greedy-fill tiling fix)

DIR="$(cd "$(dirname "$0")" && pwd)"
BIN="$DIR/soup_multi_stella"

if [ ! -x "$BIN" ]; then
    echo "Binary not found, compiling..."
    cc -O3 -march=native -ffast-math -flto -o "$BIN" "$DIR/soup_multi_stella.c" -lm -lpthread
fi

RATES=(0.01 0.1 1.0 10.0)
N_JOBS=${#RATES[@]}
NCPU=$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 16)
THREADS_PER=$(( NCPU / N_JOBS ))
if [ "$THREADS_PER" -lt 1 ]; then THREADS_PER=1; fi

COMMON_ARGS="--lattice-size 4 --n-sub 100 --prog-size 24 --max-steps 729 \
--epochs 5000000 --mutation-rate 0.001 --log-interval 10000 \
--check-interval 100000 --seed 42 --threads $THREADS_PER"

echo "Running ${N_JOBS} cross-rates in parallel (${THREADS_PER} threads each, ${NCPU} cores total)"

for RATE in "${RATES[@]}"; do
    LOGFILE="$DIR/multi_L4_cross${RATE}.log"
    if [ -f "$LOGFILE" ]; then
        echo "Skipping cross_rate=$RATE (log already exists: $LOGFILE)"
        continue
    fi
    echo "============================================"
    echo "Starting cross_rate=$RATE at $(date)"
    echo "Log: $LOGFILE"
    echo "============================================"
    $BIN $COMMON_ARGS --cross-rate "$RATE" > "$LOGFILE" 2>&1 &
done

echo "Waiting for all jobs..."
wait
echo "All jobs finished at $(date)"

for RATE in "${RATES[@]}"; do
    LOGFILE="$DIR/multi_L4_cross${RATE}.log"
    echo ""
    echo "=== cross_rate=$RATE ==="
    tail -5 "$LOGFILE" 2>/dev/null || echo "(no output)"
done

echo "============================================"
echo "Cross-rate sweep complete at $(date)"
echo "Logs:"
for RATE in "${RATES[@]}"; do
    echo "  cross_rate=$RATE: $DIR/multi_L4_cross${RATE}.log"
done
echo "============================================"
