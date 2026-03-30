#!/bin/bash
# Q4: Does the cs=1.0 replicator resurgence represent a different species?
#
# Compare dominant programs at cs=0.0, cs=0.5, cs=1.0 (3 seeds each)
# with program dumps to identify structural differences.
#
# Uses same parameters as original Exp 3 except:
#   - --dump-top 10 to capture program contents
#   - 3 seeds per config for statistical confidence

set -euo pipefail
cd "$(dirname "$0")"

BINARY=./soup_g1g2
OUTDIR=phase_q4_results
mkdir -p "$OUTDIR"

EPOCHS=500000
N_SUB=100
LOG_INT=10000
CHECK_INT=50000
CENSUS_INT=100000
THREADS=8
DUMP_TOP=10

SEEDS=(42 137 271)

for CS in 0.0 0.5 1.0; do
    for SEED in "${SEEDS[@]}"; do
        TAG="cs${CS}_seed${SEED}"
        OUT="$OUTDIR/${TAG}.log"
        echo "=== Running cs=$CS seed=$SEED ==="

        $BINARY \
            --lattice-size 2 \
            --n-sub $N_SUB \
            --epochs $EPOCHS \
            --log-interval $LOG_INT \
            --check-interval $CHECK_INT \
            --census-interval $CENSUS_INT \
            --seed-replicator \
            --seed $SEED \
            --threads $THREADS \
            --dump-top $DUMP_TOP \
            --g1 --coupling-strength $CS \
            > "$OUT" 2>&1

        echo "  -> $OUT"
    done
done

echo ""
echo "All Q4 runs complete. Results in $OUTDIR/"
