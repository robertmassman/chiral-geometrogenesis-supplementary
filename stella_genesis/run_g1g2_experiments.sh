#!/bin/bash
# G1+G2 Combined Experiment Campaign
# ===================================
# Runs experiments 1-4 from the ROADMAP-G2-Mechanisms.md plan.
#
# At ~822 epochs/sec (L=2, n_sub=100, 8 threads), 500K epochs ≈ 10 min.
# Total: ~13 runs × 10 min = ~130 min (runs are sequential).

set -e
DIR="$(cd "$(dirname "$0")" && pwd)"
BIN="$DIR/soup_g1g2"
OUT="$DIR/phase_g1g2_results"
mkdir -p "$OUT"

EPOCHS=500000
NSUB=100
L=2
THREADS=8
LOG=10000
CHECK=50000
CENSUS=100000

echo "================================================================"
echo "G1+G2 Experiment Campaign"
echo "================================================================"
echo "Epochs:  $EPOCHS"
echo "n_sub:   $NSUB"
echo "Lattice: L=$L"
echo "Output:  $OUT"
echo ""

# ── Exp 1: Baseline Calibration (G2-only) ──────────────────────────

echo "=== EXP 1: G2-only baseline (3 seeds) ==="
for SEED in 42 137 271; do
    echo "  Seed=$SEED ..."
    $BIN --lattice-size $L --n-sub $NSUB --epochs $EPOCHS --seed $SEED \
        --seed-replicator --threads $THREADS \
        --log-interval $LOG --check-interval $CHECK --census-interval $CENSUS \
        > "$OUT/exp1_g2only_seed${SEED}.log" 2>&1
    echo "  Done: $(grep 'Completed' "$OUT/exp1_g2only_seed${SEED}.log")"
done

# ── Exp 2: G1+G2 Combined (5 seeds) ────────────────────────────────

echo ""
echo "=== EXP 2: G1+G2 combined, cs=0.5 (5 seeds) ==="
for SEED in 42 137 271 314 577; do
    echo "  Seed=$SEED ..."
    $BIN --lattice-size $L --n-sub $NSUB --epochs $EPOCHS --seed $SEED \
        --g1 --coupling-strength 0.5 \
        --seed-replicator --threads $THREADS \
        --log-interval $LOG --check-interval $CHECK --census-interval $CENSUS \
        > "$OUT/exp2_g1g2_cs0.5_seed${SEED}.log" 2>&1
    echo "  Done: $(grep 'Completed' "$OUT/exp2_g1g2_cs0.5_seed${SEED}.log")"
done

# ── Exp 3: Coupling Strength Sweep ─────────────────────────────────

echo ""
echo "=== EXP 3: Coupling strength sweep (seed=42) ==="
for CS in 0.0 0.1 0.25 0.5 0.75 1.0; do
    echo "  cs=$CS ..."
    $BIN --lattice-size $L --n-sub $NSUB --epochs $EPOCHS --seed 42 \
        --g1 --coupling-strength $CS \
        --seed-replicator --threads $THREADS \
        --log-interval $LOG --check-interval $CHECK --census-interval $CENSUS \
        > "$OUT/exp3_sweep_cs${CS}_seed42.log" 2>&1
    echo "  Done: $(grep 'Completed' "$OUT/exp3_sweep_cs${CS}_seed42.log")"
done

# ── Exp 4: G1-only Multi-Stella ────────────────────────────────────

echo ""
echo "=== EXP 4: G1-only (no inter-stella VM coupling) ==="
$BIN --lattice-size $L --n-sub $NSUB --epochs $EPOCHS --seed 42 \
    --g1 --coupling-strength 0.5 --cross-rate 0 \
    --threads $THREADS \
    --log-interval $LOG --check-interval $CHECK \
    > "$OUT/exp4_g1only_seed42.log" 2>&1
echo "  Done: $(grep 'Completed' "$OUT/exp4_g1only_seed42.log")"

echo ""
echo "================================================================"
echo "All experiments complete. Results in: $OUT"
echo "================================================================"

# ── Summary extraction ──────────────────────────────────────────────

echo ""
echo "=== SUMMARY ==="
echo ""
echo "Exp 1 (G2-only baseline):"
for f in "$OUT"/exp1_g2only_*.log; do
    SEED=$(echo "$f" | grep -o 'seed[0-9]*' | grep -o '[0-9]*')
    COH=$(grep 'Mean coherence' "$f" | tail -1 | awk '{print $NF}')
    REP=$(grep 'Nontrivial' "$f" | head -1)
    COLON=$(grep 'stellae colonized' "$f" | tail -1 | awk '{print $1}')
    echo "  seed=$SEED: coh=${COH:-N/A} $COLON colonized ${REP:+[REPLICATORS]}"
done

echo ""
echo "Exp 2 (G1+G2 combined, cs=0.5):"
for f in "$OUT"/exp2_g1g2_*.log; do
    SEED=$(echo "$f" | grep -o 'seed[0-9]*' | grep -o '[0-9]*')
    COH=$(grep 'Mean coherence' "$f" | tail -1 | awk '{print $NF}')
    REP=$(grep 'Nontrivial' "$f" | head -1)
    COLON=$(grep 'stellae colonized' "$f" | tail -1 | awk '{print $1}')
    echo "  seed=$SEED: coh=${COH:-N/A} $COLON colonized ${REP:+[REPLICATORS]}"
done

echo ""
echo "Exp 3 (coupling strength sweep, seed=42):"
printf "  %6s | %5s | %10s | %s\n" "cs" "coh" "colonized" "replicators"
printf "  %6s-+-%5s-+-%10s-+-%s\n" "------" "-----" "----------" "-----------"
for f in "$OUT"/exp3_sweep_*.log; do
    CS=$(echo "$f" | grep -o 'cs[0-9.]*' | sed 's/cs//')
    COH=$(grep 'Mean coherence' "$f" | tail -1 | awk '{print $NF}')
    COLON=$(grep 'stellae colonized' "$f" | tail -1 | awk '{print $1}')
    REP=$(grep -c 'Nontrivial' "$f" 2>/dev/null || echo 0)
    printf "  %6s | %5s | %10s | %s\n" "$CS" "${COH:-N/A}" "${COLON:-0/4}" "$([ "$REP" -gt 0 ] && echo 'YES' || echo 'no')"
done

echo ""
echo "Exp 4 (G1-only, no inter-stella):"
f="$OUT/exp4_g1only_seed42.log"
COH=$(grep 'Mean coherence' "$f" | tail -1 | awk '{print $NF}')
echo "  coh=${COH:-N/A}"
