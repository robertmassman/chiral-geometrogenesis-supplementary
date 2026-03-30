#!/bin/bash
# Phase C8: Chiral Wavefront Propagation on G1+G2 FCC Lattice
# =============================================================
# Tests whether chirality (right-handed pressure asymmetry) combined
# with G1+G2 produces directional replicator propagation on the FCC lattice.
#
# ROADMAP-G2-Mechanisms.md remaining open question #1.
# Reference: GPU-TEST-PLAN.md Q3/Q3b (wavefront experiments).

set -e
DIR="$(cd "$(dirname "$0")" && pwd)"
BIN="$DIR/soup_g1g2"
OUT="$DIR/phase_C8_results"
mkdir -p "$OUT"

# ── Parameters ────────────────────────────────────────────────
# L=4 at n_sub=100 is too slow (~12 ep/s with G1). Use L=2 (4 stellae,
# 2 distance shells) at n_sub=100 (~930 ep/s) which gives enough tiles
# (1666/stella) for replicator survival. The key observables (dir bias,
# T+/T- ratio, coherence, colonization timing) work at L=2.
L=2              # 4 stellae on FCC lattice (d=0, d=1)
NSUB=100         # standard mesh resolution (1666 tiles/stella)
EPOCHS=500000    # 500K epochs (replicators emerge by ~50K, steady state by ~200K)
CS=0.5           # G1 coupling strength (established optimal)
EPS=0.1          # pressure regularization
CHI_MODE=0       # pressure-asymmetry mode
THREADS=8
LOG=10000
CHECK=50000
CENSUS=50000     # frequent census for wavefront tracking
SEED_TILES=0     # 0 = seed ALL tiles in stella 0

# Chirality sweep: 0 (baseline), up through crossover at ~0.42
CHI_VALUES="0.00 0.05 0.10 0.15 0.20 0.30 0.42"
SEEDS="42 137 271"

# Quick mode: pass --quick for a fast validation run
if [ "$1" = "--quick" ]; then
    EPOCHS=500000
    CHI_VALUES="0.00 0.15"
    SEEDS="42"
    echo "*** QUICK MODE: 2 chi values, 1 seed, 500K epochs ***"
    echo ""
fi

# ── Compile if needed ─────────────────────────────────────────
if [ ! -f "$BIN" ] || [ "$DIR/soup_g1g2.c" -nt "$BIN" ]; then
    echo "Compiling soup_g1g2..."
    cc -O3 -march=native -ffast-math -flto -o "$BIN" "$DIR/soup_g1g2.c" -lm -lpthread
    echo "Done."
fi

# ── Run sweep ─────────────────────────────────────────────────
N_RUNS=0
for CHI in $CHI_VALUES; do N_RUNS=$((N_RUNS + 1)); done
N_SEEDS=0
for S in $SEEDS; do N_SEEDS=$((N_SEEDS + 1)); done
TOTAL=$((N_RUNS * N_SEEDS))
RUN=0

echo "================================================================"
echo "Phase C8: Chiral Wavefront Propagation"
echo "================================================================"
echo "Lattice:    L=$L (32 stellae)"
echo "n_sub:      $NSUB"
echo "Epochs:     $EPOCHS"
echo "G1:         cs=$CS, eps=$EPS"
echo "Chi mode:   $CHI_MODE (pressure-asymmetry)"
echo "Chi values: $CHI_VALUES"
echo "Seeds:      $SEEDS"
echo "Total runs: $TOTAL"
echo "Output:     $OUT"
echo "================================================================"
echo ""

for CHI in $CHI_VALUES; do
    echo "=== Chirality = $CHI ==="
    for SEED in $SEEDS; do
        RUN=$((RUN + 1))
        LOGFILE="$OUT/C8_chi${CHI}_seed${SEED}.log"
        echo "  [$RUN/$TOTAL] chi=$CHI seed=$SEED ..."

        $BIN --lattice-size $L --n-sub $NSUB --epochs $EPOCHS --seed $SEED \
            --g1 --coupling-strength $CS --epsilon $EPS \
            --chirality $CHI --chirality-mode $CHI_MODE \
            --seed-replicator --seed-n-tiles $SEED_TILES --seed-stella 0 \
            --threads $THREADS \
            --log-interval $LOG --check-interval $CHECK --census-interval $CENSUS \
            > "$LOGFILE" 2>&1

        ELAPSED=$(grep 'Completed' "$LOGFILE" | head -1)
        BIAS=$(grep 'Directional bias' "$LOGFILE" | head -1 | awk '{print $3}')
        COH=$(grep 'Mean coherence' "$LOGFILE" | head -1 | awk '{print $3}')
        echo "    $ELAPSED"
        echo "    Bias=$BIAS Coh=$COH"
    done
    echo ""
done

echo "================================================================"
echo "All $TOTAL runs complete. Logs in $OUT/"
echo "Run: python3 $DIR/phase_C8_chiral_wavefront.py"
echo "================================================================"
