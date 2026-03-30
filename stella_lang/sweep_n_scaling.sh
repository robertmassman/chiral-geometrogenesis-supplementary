#!/usr/bin/env bash
#
# sweep_n_scaling.sh — Multi-seed campaign for N-scaling of emergence time
#
# Addresses Open Refinement §7 item 2 of Lemma-0.0.XXe-NP:
#   Determine T_emerge(N) scaling — Poisson (T ∝ 1/N) vs Cooperative (T ∝ N^{η-1})
#
# Proposed in §3.5.3: ≥5 seeds at N ∈ {1666, 2520, 3036, 4108}
# with both local and global pairing.
#
# Usage:
#   bash sweep_n_scaling.sh [epochs] [max_parallel]
#   bash sweep_n_scaling.sh 5000000 4       # 5M epochs, 4 jobs in parallel
#   bash sweep_n_scaling.sh 2000000         # 2M epochs, auto-detect cores
#
set -euo pipefail

EPOCHS="${1:-5000000}"
MAX_PARALLEL="${2:-$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 4)}"

BINARY="./soup_2d_tile"
OUTDIR="sweep_n_scaling_results"
SEEDS=(42 123 456 789 1024)

# n_sub → N mapping (verified):
#   100 → 1666,  123 → 2520,  135 → 3036,  157 → 4108
NSUB_VALUES=(100 123 135 157)
N_VALUES=(1666 2520 3036 4108)

PAIRING_MODES=("local" "global")

LOG_INTERVAL=10000
CHECK_INTERVAL=100000

mkdir -p "$OUTDIR"

echo "============================================================"
echo "N-Scaling Sweep for Lemma 0.0.XXe-NP (§3.5.3)"
echo "============================================================"
echo "Epochs:        $EPOCHS"
echo "Seeds:         ${SEEDS[*]}"
echo "N_sub values:  ${NSUB_VALUES[*]}"
echo "N (tiles):     ${N_VALUES[*]}"
echo "Pairing modes: ${PAIRING_MODES[*]}"
echo "Max parallel:  $MAX_PARALLEL"
echo "Output dir:    $OUTDIR"
echo "============================================================"
echo ""

# Count total runs
TOTAL=$((${#NSUB_VALUES[@]} * ${#SEEDS[@]} * ${#PAIRING_MODES[@]}))
echo "Total runs: $TOTAL"
echo ""

# Track running jobs
RUNNING=0
COMPLETED=0

run_one() {
    local nsub=$1 N=$2 seed=$3 mode=$4
    local pairing_flag=""
    [ "$mode" = "global" ] && pairing_flag="--global"

    local outfile="${OUTDIR}/${mode}_n${nsub}_N${N}_s${seed}.txt"

    # Skip if already completed
    if [ -f "$outfile" ] && grep -q "Completed.*epochs" "$outfile" 2>/dev/null; then
        echo "[SKIP] $outfile (already complete)"
        COMPLETED=$((COMPLETED + 1))
        return 0
    fi

    echo "[START] mode=$mode n_sub=$nsub N=$N seed=$seed → $outfile"

    $BINARY \
        --n-sub "$nsub" \
        --epochs "$EPOCHS" \
        --seed "$seed" \
        --log-interval "$LOG_INTERVAL" \
        --check-interval "$CHECK_INTERVAL" \
        --threads 1 \
        $pairing_flag \
        > "$outfile" 2>&1 &

    RUNNING=$((RUNNING + 1))

    # Throttle parallelism
    if [ "$RUNNING" -ge "$MAX_PARALLEL" ]; then
        wait -n 2>/dev/null || wait
        RUNNING=$((RUNNING - 1))
        COMPLETED=$((COMPLETED + 1))
        echo "  [$COMPLETED/$TOTAL completed]"
    fi
}

START_TIME=$(date +%s)

for mode in "${PAIRING_MODES[@]}"; do
    for i in "${!NSUB_VALUES[@]}"; do
        nsub="${NSUB_VALUES[$i]}"
        N="${N_VALUES[$i]}"
        for seed in "${SEEDS[@]}"; do
            run_one "$nsub" "$N" "$seed" "$mode"
        done
    done
done

# Wait for remaining jobs
wait
END_TIME=$(date +%s)
ELAPSED=$((END_TIME - START_TIME))

echo ""
echo "============================================================"
echo "All $TOTAL runs complete in ${ELAPSED}s ($(( ELAPSED / 3600 ))h $(( (ELAPSED % 3600) / 60 ))m)"
echo "============================================================"
echo ""

# ---- Generate summary CSV ----
SUMMARY="$OUTDIR/summary.csv"
echo "mode,n_sub,N,seed,t_emerge,epochs_run,emerged,epochs_per_sec" > "$SUMMARY"

for mode in "${PAIRING_MODES[@]}"; do
    for i in "${!NSUB_VALUES[@]}"; do
        nsub="${NSUB_VALUES[$i]}"
        N="${N_VALUES[$i]}"
        for seed in "${SEEDS[@]}"; do
            outfile="${OUTDIR}/${mode}_n${nsub}_N${N}_s${seed}.txt"
            if [ ! -f "$outfile" ]; then
                echo "$mode,$nsub,$N,$seed,NA,0,no,0" >> "$SUMMARY"
                continue
            fi

            # Extract first epoch with nontrivial replicators
            # Log format: "    100000 |   1598 |    12 |  1.4907 | *** NONTRIVIAL REPLICATORS ***"
            first_line=$(grep 'NONTRIVIAL REPLICATORS' "$outfile" | head -1)
            if [ -n "$first_line" ]; then
                # Epoch is the first number on the line
                t_emerge=$(echo "$first_line" | awk '{print $1}')
                emerged="yes"
            else
                t_emerge="NA"
                emerged="no"
            fi

            # Extract total epochs and rate
            epochs_run=$(grep -oE 'Completed [0-9]+ epochs' "$outfile" | grep -oE '[0-9]+' || echo "0")
            rate=$(grep -oE '[0-9]+ epochs/sec' "$outfile" | grep -oE '[0-9]+' || echo "0")

            echo "$mode,$nsub,$N,$seed,$t_emerge,$epochs_run,$emerged,$rate" >> "$SUMMARY"
        done
    done
done

echo "Summary written to $SUMMARY"
echo ""

# ---- Print summary table ----
echo "============================================================"
echo "RESULTS SUMMARY"
echo "============================================================"
printf "%-8s %6s %6s | %-28s | emerged\n" "mode" "n_sub" "N" "t_emerge (per seed)"
echo "--------------------------------------------------------------"

for mode in "${PAIRING_MODES[@]}"; do
    for i in "${!NSUB_VALUES[@]}"; do
        nsub="${NSUB_VALUES[$i]}"
        N="${N_VALUES[$i]}"
        results=""
        n_emerged=0
        n_total=0
        for seed in "${SEEDS[@]}"; do
            outfile="${OUTDIR}/${mode}_n${nsub}_N${N}_s${seed}.txt"
            n_total=$((n_total + 1))
            if [ -f "$outfile" ] && grep -q 'NONTRIVIAL REPLICATORS' "$outfile"; then
                t=$(grep 'NONTRIVIAL REPLICATORS' "$outfile" | head -1 | grep -oE '[0-9]+' | head -1)
                results="$results ${t}"
                n_emerged=$((n_emerged + 1))
            else
                results="$results >$EPOCHS"
            fi
        done
        printf "%-8s %6d %6d | %-28s | %d/%d\n" "$mode" "$nsub" "$N" "$results" "$n_emerged" "$n_total"
    done
done

echo ""
echo "Done. Raw data in $OUTDIR/"
