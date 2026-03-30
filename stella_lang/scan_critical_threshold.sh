#!/bin/bash
# Phase A: Coarse scan to locate the nucleation threshold
# Phase B: Dense scan around the transition (run after Phase A)
#
# Usage:
#   bash scan_critical_threshold.sh phaseA    # ~5 hours
#   bash scan_critical_threshold.sh phaseB    # ~2-3 hours (after reviewing Phase A)
#   bash scan_critical_threshold.sh analyze   # Parse all logs and summarize

set -euo pipefail
cd "$(dirname "$0")"

BINARY=./soup_2d_tile
EPOCHS=5000000
LOG_DIR=path1_critical_mesh_logs
mkdir -p "$LOG_DIR"

# Phase A: coarse grid across the unknown region [40..90]
PHASE_A_NSUB=(40 50 55 60 65 70 75 80 85 90)
PHASE_A_SEEDS=(42 123 456 789 1024)

# Phase B: dense grid around the transition (edit after Phase A results)
# Default: focused around n_sub=60-75 with more seeds
PHASE_B_NSUB=(58 60 62 64 65 66 67 68 70 72)
PHASE_B_SEEDS=(42 123 456 789 1024 2048 3141 4096 5555 6789 7777 8192 9001 9999 10007)

run_one() {
    local nsub=$1
    local seed=$2
    local logfile="$LOG_DIR/nsub${nsub}_global_s${seed}.log"

    if [ -f "$logfile" ]; then
        echo "  SKIP n_sub=$nsub seed=$seed (log exists)"
        return 0
    fi

    echo "  RUN  n_sub=$nsub seed=$seed ..."
    $BINARY --n-sub "$nsub" --epochs "$EPOCHS" --seed "$seed" --global \
        --log-interval 100000 --check-interval 500000 \
        > "$logfile" 2>&1
    echo "  DONE n_sub=$nsub seed=$seed"
}

run_phase() {
    local phase_name=$1
    shift
    local -a nsub_vals=()
    local -a seed_vals=()

    # Parse nsub and seed arrays from arguments
    local parsing_nsub=true
    for arg in "$@"; do
        if [ "$arg" = "---" ]; then
            parsing_nsub=false
            continue
        fi
        if $parsing_nsub; then
            nsub_vals+=("$arg")
        else
            seed_vals+=("$arg")
        fi
    done

    local total=$((${#nsub_vals[@]} * ${#seed_vals[@]}))
    local count=0
    echo "========================================"
    echo "Phase $phase_name: ${#nsub_vals[@]} n_sub values × ${#seed_vals[@]} seeds = $total runs"
    echo "Epochs: $EPOCHS, pairing: global"
    echo "========================================"

    for nsub in "${nsub_vals[@]}"; do
        echo ""
        echo "--- n_sub=$nsub ---"
        for seed in "${seed_vals[@]}"; do
            count=$((count + 1))
            echo "[$count/$total]"
            run_one "$nsub" "$seed"
        done
    done

    echo ""
    echo "Phase $phase_name complete: $count runs"
}

analyze_logs() {
    echo "========================================"
    echo "Analyzing all logs in $LOG_DIR/"
    echo "========================================"
    echo ""
    printf "%6s %8s %6s %6s %8s\n" "n_sub" "N_tiles" "yes" "no" "P_nuc"
    printf "%6s %8s %6s %6s %8s\n" "------" "--------" "------" "------" "--------"

    # Collect all n_sub values from logs
    for logfile in "$LOG_DIR"/nsub*_global_s*.log; do
        [ -f "$logfile" ] || continue
        basename "$logfile"
    done | sed 's/nsub\([0-9]*\)_.*/\1/' | sort -un | while read nsub; do
        # Count replicator emergence across seeds
        yes=0
        no=0
        for logfile in "$LOG_DIR"/nsub${nsub}_global_s*.log; do
            [ -f "$logfile" ] || continue
            # Check for replicator signatures: "nontrivial" or dominant % > 5
            if grep -qi "nontrivial\|REPLICATOR" "$logfile" 2>/dev/null; then
                yes=$((yes + 1))
            elif grep -oP '\d+\.\d+%' "$logfile" 2>/dev/null | awk -F% '{if ($1 > 5.0) exit 0; else exit 1}'; then
                yes=$((yes + 1))
            else
                no=$((no + 1))
            fi
        done
        total=$((yes + no))
        if [ $total -gt 0 ]; then
            pnuc=$(echo "scale=3; $yes / $total" | bc)
            # Compute N_tiles = 2 * floor((2*nsub^2 + 2) / 24)
            nsites=$((2 * nsub * nsub + 2))
            ntiles=$((2 * (nsites / 24)))
            printf "%6d %8d %6d %6d %8s\n" "$nsub" "$ntiles" "$yes" "$no" "$pnuc"
        fi
    done

    echo ""
    echo "Known reference points:"
    echo "  n_sub=16  N=42     P_nuc=0.000 (RERUN_PLAN)"
    echo "  n_sub=32  N=170    P_nuc=0.000 (RERUN_PLAN)"
    echo "  n_sub=100 N=1666   P_nuc=0.750 (n_scaling, 20 seeds)"
    echo "  n_sub=157 N=4108   P_nuc=0.900 (n_scaling, 20 seeds)"
}

case "${1:-analyze}" in
    phaseA|phase_a|a|A)
        run_phase "A" "${PHASE_A_NSUB[@]}" "---" "${PHASE_A_SEEDS[@]}"
        echo ""
        analyze_logs
        ;;
    phaseB|phase_b|b|B)
        run_phase "B" "${PHASE_B_NSUB[@]}" "---" "${PHASE_B_SEEDS[@]}"
        echo ""
        analyze_logs
        ;;
    analyze|results)
        analyze_logs
        ;;
    *)
        echo "Usage: $0 {phaseA|phaseB|analyze}"
        exit 1
        ;;
esac
