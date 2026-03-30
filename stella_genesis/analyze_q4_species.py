#!/usr/bin/env python3
"""
Q4 Analysis: Does cs=1.0 replicator resurgence represent a different species?

Parses program dumps from run_q4_replicator_species.sh logs and compares:
  1. Instruction profiles (opcode frequency in dominant programs)
  2. Structural motifs (CPY01/FWD0/FWD1 core vs alternatives)
  3. Replicator status across coupling strengths
  4. Temporal dynamics (when does the top program establish dominance?)
"""

import os
import re
import sys
from collections import defaultdict

RESULT_DIR = os.path.join(os.path.dirname(__file__), "phase_q4_results")

def parse_log(filepath):
    """Parse a single Q4 log file for program dumps and time series."""
    result = {
        "file": os.path.basename(filepath),
        "final_programs": [],
        "time_series": [],      # (epoch, unique, top_count, coh)
        "census_programs": {},   # epoch -> list of top programs
    }

    with open(filepath) as f:
        lines = f.readlines()

    # Parse time series
    for line in lines:
        m = re.match(r'\s+(\d+)\s+\|\s+(\d+)\s+\|\s+(\d+)\s+\|\s+([\d.]+)\s+\|\s+([\d.]+)', line)
        if m:
            epoch = int(m.group(1))
            unique = int(m.group(2))
            top = int(m.group(3))
            entropy = float(m.group(4))
            coh = float(m.group(5))
            result["time_series"].append({
                "epoch": epoch, "unique": unique, "top": top,
                "entropy": entropy, "coh": coh
            })

    # Parse TOP-N program dumps
    current_epoch = None
    current_programs = []
    i = 0
    while i < len(lines):
        line = lines[i]

        m = re.match(r'\s+TOP-\d+ PROGRAMS \(epoch (\d+)', line)
        if m:
            if current_epoch is not None and current_programs:
                result["census_programs"][current_epoch] = current_programs
            current_epoch = int(m.group(1))
            current_programs = []
            i += 1
            continue

        m = re.match(r'\s+#(\d+) \((\d+) copies, ([\d.]+)%\) \[(\w+)\]:(.*)', line)
        if m:
            rank = int(m.group(1))
            copies = int(m.group(2))
            pct = float(m.group(3))
            status = m.group(4)
            instr_str = m.group(5).strip()

            # Split at " | trits:" to get instructions and trits
            parts = instr_str.split(" | trits:")
            instructions = parts[0].strip().split()
            trits = parts[1].strip() if len(parts) > 1 else ""

            # Parse profile from next line
            profile = {}
            if i + 1 < len(lines):
                pm = re.match(r'\s+profile:(.*)', lines[i + 1])
                if pm:
                    for tok in pm.group(1).strip().split():
                        k, v = tok.split("=")
                        profile[k] = int(v)
                    i += 1

            prog = {
                "rank": rank, "copies": copies, "pct": pct,
                "status": status, "instructions": instructions,
                "trits": trits, "profile": profile
            }
            current_programs.append(prog)

        i += 1

    if current_epoch is not None and current_programs:
        result["census_programs"][current_epoch] = current_programs

    # Final programs = last census dump
    if result["census_programs"]:
        last_epoch = max(result["census_programs"].keys())
        result["final_programs"] = result["census_programs"][last_epoch]

    return result


def print_comparison(results_by_cs):
    """Print cross-cs comparison of dominant programs."""

    print("=" * 80)
    print("Q4: REPLICATOR SPECIES COMPARISON ACROSS COUPLING STRENGTHS")
    print("=" * 80)

    for cs in sorted(results_by_cs.keys()):
        runs = results_by_cs[cs]
        print(f"\n{'='*70}")
        print(f"  cs = {cs}")
        print(f"{'='*70}")

        for run in runs:
            seed = re.search(r'seed(\d+)', run["file"]).group(1)
            print(f"\n  --- seed={seed} ---")

            # Time series: when does top surge?
            ts = run["time_series"]
            if ts:
                # Find first epoch where top > 100
                surge_epoch = None
                for pt in ts:
                    if pt["top"] > 100:
                        surge_epoch = pt["epoch"]
                        break
                final = ts[-1]
                print(f"  Final: unique={final['unique']}, top={final['top']}, coh={final['coh']:.3f}")
                if surge_epoch:
                    print(f"  Surge epoch (top>100): {surge_epoch}")
                else:
                    print(f"  No surge (top never exceeded 100)")

            # Top programs
            progs = run["final_programs"]
            if not progs:
                print("  No program dumps found")
                continue

            for p in progs[:3]:  # top 3
                instr = " ".join(p["instructions"])
                print(f"  #{p['rank']} ({p['copies']} copies, {p['pct']:.1f}%) [{p['status']}]")
                print(f"    {instr}")
                prof_str = " ".join(f"{k}={v}" for k, v in sorted(p["profile"].items()))
                print(f"    profile: {prof_str}")

    # Cross-cs instruction profile comparison
    print(f"\n{'='*80}")
    print("INSTRUCTION PROFILE COMPARISON (top-1 dominant program)")
    print("=" * 80)

    all_ops = ["NOP", "ROT", "FWD0", "BCK0", "FWD1", "[", "]", "CPY01", "CPY10"]
    header = f"{'cs':>4} {'seed':>5} {'copies':>6} {'status':>10}"
    for op in all_ops:
        header += f" {op:>5}"
    print(header)
    print("-" * len(header))

    for cs in sorted(results_by_cs.keys()):
        for run in results_by_cs[cs]:
            seed = re.search(r'seed(\d+)', run["file"]).group(1)
            progs = run["final_programs"]
            if not progs:
                continue
            p = progs[0]
            row = f"{cs:>4} {seed:>5} {p['copies']:>6} {p['status']:>10}"
            for op in all_ops:
                row += f" {p['profile'].get(op, 0):>5}"
            print(row)

    # Structural motif analysis
    print(f"\n{'='*80}")
    print("STRUCTURAL MOTIF ANALYSIS")
    print("=" * 80)

    for cs in sorted(results_by_cs.keys()):
        motifs = defaultdict(int)
        for run in results_by_cs[cs]:
            progs = run["final_programs"]
            if not progs:
                continue
            p = progs[0]
            # Check for standard CPY01-FWD copy machine motif
            instr = p["instructions"]
            has_cpy01 = "CPY01" in instr
            has_cpy10 = "CPY10" in instr
            has_fwd0 = "FWD0" in instr
            has_fwd1 = "FWD1" in instr
            has_brackets = "[" in instr and "]" in instr

            if has_cpy01 and has_fwd0 and has_fwd1 and has_brackets and not has_cpy10:
                motif = "CPY01+FWD0+FWD1+brackets (standard copy machine)"
            elif has_cpy01 and has_fwd0 and has_fwd1 and not has_cpy10:
                motif = "CPY01+FWD0+FWD1 (no brackets)"
            elif has_cpy01 and not has_cpy10:
                motif = f"CPY01-based (other: {' '.join(instr)})"
            elif has_cpy10 and not has_cpy01:
                motif = "CPY10-based (reversed chirality)"
            elif p["status"] == "inert":
                motif = f"inert ({' '.join(instr[:6])}...)"
            else:
                motif = f"other ({' '.join(instr[:6])}...)"

            motifs[motif] += 1

        print(f"\n  cs={cs}:")
        for motif, count in sorted(motifs.items(), key=lambda x: -x[1]):
            print(f"    {count}/3 seeds: {motif}")

    # Temporal dynamics: resurgence timing
    print(f"\n{'='*80}")
    print("RESURGENCE TIMING")
    print("=" * 80)
    print(f"{'cs':>4} {'seed':>5} {'surge_epoch':>12} {'final_top':>10} {'final_unique':>13}")
    print("-" * 50)
    for cs in sorted(results_by_cs.keys()):
        for run in results_by_cs[cs]:
            seed = re.search(r'seed(\d+)', run["file"]).group(1)
            ts = run["time_series"]
            if not ts:
                continue
            surge = "none"
            for pt in ts:
                if pt["top"] > 100:
                    surge = str(pt["epoch"])
                    break
            final = ts[-1]
            print(f"{cs:>4} {seed:>5} {surge:>12} {final['top']:>10} {final['unique']:>13}")


def main():
    if not os.path.isdir(RESULT_DIR):
        print(f"Error: {RESULT_DIR} not found. Run run_q4_replicator_species.sh first.")
        sys.exit(1)

    # Parse all logs
    results_by_cs = defaultdict(list)
    for fname in sorted(os.listdir(RESULT_DIR)):
        if not fname.endswith(".log"):
            continue
        m = re.match(r'cs([\d.]+)_seed(\d+)\.log', fname)
        if not m:
            continue
        cs = m.group(1)
        filepath = os.path.join(RESULT_DIR, fname)
        result = parse_log(filepath)
        results_by_cs[cs].append(result)

    if not results_by_cs:
        print("No Q4 result files found.")
        sys.exit(1)

    print_comparison(results_by_cs)


if __name__ == "__main__":
    main()
