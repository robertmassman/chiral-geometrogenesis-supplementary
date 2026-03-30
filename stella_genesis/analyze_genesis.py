#!/usr/bin/env python3
"""
Analyze Stella Genesis experiment output.

Parses diagnostic lines from genesis_soup and produces summary statistics
and comparison metrics against StellaLang baselines.

Usage:
    python3 analyze_genesis.py results.log
    python3 analyze_genesis.py --compare results_mode0.log results_mode1.log results_mode2.log
"""

import sys
import re
import json


def parse_log(filepath):
    """Parse genesis_soup output into structured data."""
    records = []
    metadata = {}

    with open(filepath) as f:
        for line in f:
            line = line.strip()

            # Parse metadata
            if line.startswith("Mode:"):
                metadata["mode"] = line.split(":")[1].strip()
            elif line.startswith("Coupling strength:"):
                metadata["coupling_strength"] = float(line.split(":")[1])
            elif line.startswith("Seed:"):
                metadata["seed"] = int(line.split(":")[1])
            elif line.startswith("N_sub:"):
                metadata["n_sub"] = int(line.split(":")[1])

            # Parse diagnostic lines
            m = re.match(
                r"epoch=(\d+)\s+"
                r"H_tp=([\d.]+)\s+H_tm=([\d.]+)\s+"
                r"corr=([\d.]+)\s+"
                r"auto_tp=([\d.]+)\s+auto_tm=([\d.]+)\s+"
                r"local_repl=([\d.]+)\s+"
                r"dir_bias=([\d.]+)",
                line,
            )
            if m:
                records.append({
                    "epoch": int(m.group(1)),
                    "H_tp": float(m.group(2)),
                    "H_tm": float(m.group(3)),
                    "corr": float(m.group(4)),
                    "auto_tp": float(m.group(5)),
                    "auto_tm": float(m.group(6)),
                    "local_repl": float(m.group(7)),
                    "dir_bias": float(m.group(8)),
                })

    return metadata, records


def summarize(metadata, records):
    """Print summary statistics."""
    if not records:
        print("No diagnostic records found.")
        return

    first = records[0]
    last = records[-1]
    max_entropy = 1.585  # log2(3)

    print(f"\n{'='*60}")
    print(f"  Stella Genesis — {metadata.get('mode', 'unknown')} mode")
    print(f"{'='*60}")
    print(f"  Coupling strength: {metadata.get('coupling_strength', '?')}")
    print(f"  Epochs: {last['epoch']}")
    print()

    # Entropy analysis
    print("  ENTROPY (max = 1.585 = random):")
    print(f"    T+ : {first['H_tp']:.4f} → {last['H_tp']:.4f}  "
          f"(Δ = {last['H_tp'] - first['H_tp']:+.4f})")
    print(f"    T- : {first['H_tm']:.4f} → {last['H_tm']:.4f}  "
          f"(Δ = {last['H_tm'] - first['H_tm']:+.4f})")

    entropy_drop = (first['H_tp'] + first['H_tm']) / 2 - \
                   (last['H_tp'] + last['H_tm']) / 2
    print(f"    Avg drop: {entropy_drop:+.4f}")
    if entropy_drop > 0.01:
        print("    → SELF-ORGANIZATION DETECTED")
    else:
        print("    → No significant ordering")

    # Correlation analysis
    print()
    print("  T+/T- CORRELATION (0.333 = random):")
    print(f"    Initial: {first['corr']:.4f}")
    print(f"    Final:   {last['corr']:.4f}")
    if last['corr'] > 0.4:
        print("    → INTER-SURFACE COHERENCE DETECTED")

    # Spatial autocorrelation
    print()
    print("  SPATIAL AUTOCORRELATION (0.333 = random):")
    print(f"    T+ : {first['auto_tp']:.4f} → {last['auto_tp']:.4f}")
    print(f"    T- : {first['auto_tm']:.4f} → {last['auto_tm']:.4f}")
    if last['auto_tp'] > 0.4 or last['auto_tm'] > 0.4:
        print("    → SPATIAL PATTERN FORMATION DETECTED")

    # Directional bias
    print()
    print("  DIRECTIONAL BIAS (0.5 = symmetric):")
    print(f"    Final: {last['dir_bias']:.4f}")
    if abs(last['dir_bias'] - 0.5) > 0.05:
        direction = "T+ → T-" if last['dir_bias'] > 0.5 else "T- → T+"
        print(f"    → EMERGENT ARROW: net {direction} flow")
    else:
        print("    → No significant directional bias")

    # Local replication
    print()
    print("  LOCAL REPLICATION DENSITY (0.333 = random):")
    print(f"    Final: {last['local_repl']:.4f}")
    if last['local_repl'] > 0.5:
        print("    → LOCAL PATTERN REPLICATION DETECTED")

    # Comparison with StellaLang baselines
    print()
    print("  COMPARISON WITH STELLALANG:")
    print(f"    StellaLang entropy at 30M: ~1.52 (with replicators)")
    print(f"    Genesis entropy at {last['epoch']}: "
          f"{(last['H_tp'] + last['H_tm'])/2:.4f}")
    print(f"    StellaLang replicator density: ~88%")
    print(f"    Genesis local replication: {last['local_repl']*100:.1f}%")

    print(f"\n{'='*60}\n")


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 analyze_genesis.py <results.log>")
        print("       python3 analyze_genesis.py --compare <log1> <log2> ...")
        sys.exit(1)

    if sys.argv[1] == "--compare":
        for filepath in sys.argv[2:]:
            metadata, records = parse_log(filepath)
            summarize(metadata, records)
    else:
        metadata, records = parse_log(sys.argv[1])
        summarize(metadata, records)

        # Also dump JSON for further analysis
        json_path = sys.argv[1].replace(".log", "_parsed.json")
        with open(json_path, "w") as f:
            json.dump({"metadata": metadata, "records": records}, f, indent=2)
        print(f"Parsed data written to {json_path}")


if __name__ == "__main__":
    main()
