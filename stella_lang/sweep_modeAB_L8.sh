#!/bin/bash
# Mode A vs Mode B at L=8 (256 stellae)
# ======================================
# Tests whether octahedral mediation matters at larger lattice sizes.
# At L=4 (32 stellae, 4 shells), Mode A ≈ Mode B. At L=8 (256 stellae,
# 7 shells), more distance shells may reveal structural differences.
#
# Comparison groups:
#   1. Same nominal cross-rate: Mode A cr=X vs Mode B cr=X
#   2. VM-equalized: Mode A cr=X vs Mode B cr=X/2
#      (Mode B uses 2 VM execs per event vs Mode A's 1)
#
# Parameters: L=8, n_sub=100 (~20K sites/tetra, 1666 tiles/stella)
# Estimated speed: ~13-15 epochs/sec → 15K epochs ≈ 17 min/run
# Total: 27 runs × ~17 min ≈ ~7.5 hours (sequential)
#        With MAX_PARALLEL=2: ~4 hours

set -e
DIR="$(cd "$(dirname "$0")" && pwd)"
BIN="$DIR/soup_multi_stella"
OUT="$DIR/sweep_modeAB_L8_results"
mkdir -p "$OUT"

EPOCHS=${1:-15000}
MAX_PARALLEL=${2:-2}
L=8
NSUB=100
CENSUS=100
LOG=1000
CHECK=50000
SEEDS="42 137 271"

# Threads per job: split available cores across parallel jobs
TOTAL_CORES=$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 8)
THREADS=$((TOTAL_CORES / MAX_PARALLEL))
[ "$THREADS" -lt 1 ] && THREADS=1

echo "================================================================"
echo "Mode A vs Mode B at L=$L ($(( L*L*L/2 )) stellae)"
echo "================================================================"
echo "Epochs:       $EPOCHS"
echo "n_sub:        $NSUB"
echo "Census:       every $CENSUS epochs"
echo "Seeds:        $SEEDS"
echo "Threads/job:  $THREADS (of $TOTAL_CORES cores)"
echo "Max parallel: $MAX_PARALLEL"
echo "Output:       $OUT"
echo ""

# Configurations: mode,cross_rate
CONFIGS=(
    "direct,0.01"
    "direct,0.1"
    "direct,1.0"
    "octahedral,0.01"
    "octahedral,0.1"
    "octahedral,1.0"
    "octahedral,0.005"
    "octahedral,0.05"
    "octahedral,0.5"
)

run_one() {
    local MODE=$1 CR=$2 SEED=$3
    local TAG="${MODE}_cr${CR}_s${SEED}"
    local OUTFILE="$OUT/${TAG}.txt"

    echo "  START $TAG ($(date +%H:%M:%S))"
    $BIN --lattice-size $L --n-sub $NSUB --epochs $EPOCHS \
        --coupling-mode "$MODE" --cross-rate "$CR" \
        --seed-replicator --seed "$SEED" \
        --threads $THREADS \
        --log-interval $LOG --check-interval $CHECK \
        --census-interval $CENSUS \
        > "$OUTFILE" 2>&1
    echo "  DONE  $TAG ($(date +%H:%M:%S))"
}

for CFG in "${CONFIGS[@]}"; do
    IFS=',' read -r MODE CR <<< "$CFG"
    for SEED in $SEEDS; do
        run_one "$MODE" "$CR" "$SEED"
    done
done

echo ""
echo "================================================================"
echo "All runs complete. Extracting summary..."
echo "================================================================"

# ── Analysis ───────────────────────────────────────────────────────
echo ""
echo "Running analysis..."
python3 "$DIR/analyze_modeAB_L8.py" "$OUT"
