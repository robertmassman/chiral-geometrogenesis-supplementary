#!/bin/bash
# Systematic Mode A vs Mode B comparison sweep
# Runs multiple seeds × cross-rates for both coupling modes.
# Extracts time-to-50% and time-to-100% colonization from census output.
#
# Usage: bash sweep_octahedral.sh [epochs] [max_parallel]

EPOCHS=${1:-15000}
NCPU="$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 4)"
# soup_multi_stella uses internal threads, so we split cores between
# parallel jobs and per-job threads to maximize total throughput.
# Default: 4 parallel jobs × 4 threads each = 16 cores fully utilized.
MAX_PARALLEL="${2:-4}"
THREADS_PER_JOB="${3:-$(( NCPU / MAX_PARALLEL ))}"
BINARY=./soup_multi_stella
OUTDIR=sweep_oct_results
mkdir -p "$OUTDIR"

SEEDS=(42 123 456 789 1024)
# Mode A cross-rates and their Mode B equalized counterparts
# Mode A cr=X does 1 VM exec/event; Mode B cr=X does 2 VM execs/event
# So Mode B at cr=X/2 equalizes total VM work
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

echo "============================================================"
echo "Octahedral Mediation Sweep: Mode A vs Mode B"
echo "============================================================"
echo "Epochs:    $EPOCHS"
echo "L=4 (32 stellae), n_sub=100, seeded replicator"
echo "Seeds:     ${SEEDS[*]}"
echo "Configs:   ${#CONFIGS[@]}"
echo "Total runs: $((${#SEEDS[@]} * ${#CONFIGS[@]}))"
echo "Max parallel: $MAX_PARALLEL (× $THREADS_PER_JOB threads each = $(( MAX_PARALLEL * THREADS_PER_JOB )) total)"
echo "============================================================"
echo ""

# Summary CSV header
SUMMARY="$OUTDIR/summary.csv"
echo "mode,cross_rate,seed,t_first,t_half,t_full,oct_rep_pct" > "$SUMMARY"

run_sim() {
    local mode=$1 cr=$2 seed=$3
    local tag="${mode}_cr${cr}_s${seed}"
    local outfile="$OUTDIR/${tag}.txt"

    $BINARY --lattice-size 4 --n-sub 100 --epochs "$EPOCHS" \
        --coupling-mode "$mode" --seed-replicator --cross-rate "$cr" \
        --log-interval 1000 --check-interval 50000 \
        --census-interval 100 --seed "$seed" --threads "$THREADS_PER_JOB" \
        > "$outfile" 2>&1
}

extract_results() {
    local mode=$1 cr=$2 seed=$3
    local tag="${mode}_cr${cr}_s${seed}"
    local outfile="$OUTDIR/${tag}.txt"

    local t_first="" t_half="" t_full=""
    while IFS= read -r line; do
        if [[ $line =~ "CENSUS epoch "([0-9]+)": "([0-9]+)"/32 stellae" ]]; then
            local epoch="${BASH_REMATCH[1]}"
            local col="${BASH_REMATCH[2]}"
            if [[ -z "$t_first" && "$col" -ge 2 ]]; then t_first=$epoch; fi
            if [[ -z "$t_half" && "$col" -ge 16 ]]; then t_half=$epoch; fi
            if [[ -z "$t_full" && "$col" -ge 32 ]]; then t_full=$epoch; fi
        fi
    done < "$outfile"

    local oct_pct="N/A"
    local oct_line
    oct_line=$(grep "Octahedral interstitials:" "$outfile" | tail -1 2>/dev/null)
    if [[ $oct_line =~ \(([0-9.]+)%\) ]]; then
        oct_pct="${BASH_REMATCH[1]}"
    fi

    t_first=${t_first:-">$EPOCHS"}
    t_half=${t_half:-">$EPOCHS"}
    t_full=${t_full:-">$EPOCHS"}

    echo "$mode,$cr,$seed,$t_first,$t_half,$t_full,$oct_pct" >> "$SUMMARY"
    echo "  $tag: first=$t_first half=$t_half full=$t_full oct=$oct_pct"
}

# Run all simulations in parallel (throttled to MAX_PARALLEL)
RUNNING=0
COMPLETED=0
TOTAL=$((${#SEEDS[@]} * ${#CONFIGS[@]}))

for config in "${CONFIGS[@]}"; do
    IFS=',' read -r mode cr <<< "$config"
    for seed in "${SEEDS[@]}"; do
        echo "[START] ${mode}_cr${cr}_s${seed}"
        run_sim "$mode" "$cr" "$seed" &
        RUNNING=$((RUNNING + 1))

        if [ "$RUNNING" -ge "$MAX_PARALLEL" ]; then
            wait -n 2>/dev/null || wait
            RUNNING=$((RUNNING - 1))
            COMPLETED=$((COMPLETED + 1))
            echo "  [$COMPLETED/$TOTAL completed]"
        fi
    done
done

# Wait for remaining
wait
echo "All $TOTAL simulations finished."
echo ""

# Extract results sequentially (fast, just parsing output files)
for config in "${CONFIGS[@]}"; do
    IFS=',' read -r mode cr <<< "$config"
    echo "--- $mode cr=$cr ---"
    for seed in "${SEEDS[@]}"; do
        extract_results "$mode" "$cr" "$seed"
    done
    echo ""
done

echo "============================================================"
echo "Results saved to: $OUTDIR/summary.csv"
echo "============================================================"
echo ""

# Print summary table
echo "=== SUMMARY TABLE ==="
echo ""
printf "%-12s %8s | %8s %8s %8s | %s\n" "Mode" "cr" "t_first" "t_half" "t_full" "oct%"
printf "%-12s %8s | %8s %8s %8s | %s\n" "----" "----" "-------" "------" "------" "----"

# Group by config and compute mean
for config in "${CONFIGS[@]}"; do
    IFS=',' read -r mode cr <<< "$config"
    local_sum_first=0 local_sum_half=0 local_sum_full=0 local_n=0
    local_oct_sum=0 local_oct_n=0
    while IFS=',' read -r m c s tf th tfl op; do
        if [[ "$m" == "$mode" && "$c" == "$cr" ]]; then
            if [[ "$tf" != ">"* ]]; then local_sum_first=$((local_sum_first + tf)); fi
            if [[ "$th" != ">"* ]]; then local_sum_half=$((local_sum_half + th)); fi
            if [[ "$tfl" != ">"* ]]; then
                local_sum_full=$((local_sum_full + tfl))
                local_n=$((local_n + 1))
            fi
            if [[ "$op" != "N/A" ]]; then
                local_oct_sum=$(echo "$local_oct_sum + $op" | bc)
                local_oct_n=$((local_oct_n + 1))
            fi
        fi
    done < <(tail -n +2 "$SUMMARY")

    mean_first="N/A"; mean_half="N/A"; mean_full="N/A"; mean_oct="N/A"
    n_seeds=${#SEEDS[@]}
    if [[ $local_n -gt 0 ]]; then
        mean_first=$((local_sum_first / n_seeds))
        mean_half=$((local_sum_half / n_seeds))
        mean_full=$((local_sum_full / local_n))
    fi
    if [[ $local_oct_n -gt 0 ]]; then
        mean_oct=$(echo "scale=1; $local_oct_sum / $local_oct_n" | bc)
    fi

    printf "%-12s %8s | %8s %8s %8s | %s%%\n" "$mode" "$cr" "$mean_first" "$mean_half" "$mean_full" "$mean_oct"
done

echo ""
echo "t_first = first epoch with >=2 stellae colonized (propagation started)"
echo "t_half  = first epoch with >=16/32 stellae colonized"
echo "t_full  = first epoch with 32/32 stellae colonized"
echo "oct%    = percentage of octahedral interstitials containing replicators (Mode B only)"
