#!/usr/bin/env python3
"""
Phase 5: Genesis vs StellaLang Comparison at Matched Parameters
================================================================

Open Question #5 from RESULTS-Phase1.md:
  "Run StellaLang soup_2d with identical mesh, mutation rate, and epochs
   to get a precise baseline for the contribution of CPY01 vs geometric
   coupling."

This script runs both systems with matched parameters and computes
comparable metrics to isolate the coupling mechanism difference:
  - Genesis:    single-head VM + pressure-mediated geometric coupling (G1)
  - StellaLang: dual-head VM   + CPY01/CPY10 instruction-based coupling (G2)

Matched parameters:
  - program_size = 24 trits
  - max_steps = 729
  - mutation_rate = 0.001
  - seed = 42

Comparable metrics:
  - Trit entropy H (max = log2(3) = 1.585 for random)
  - Inter-component correlation (T+/T- matching fraction)
  - Self-organization signal (entropy drop from initial)
"""

import subprocess
import sys
import os
import re
import time
import json
import numpy as np
from pathlib import Path

# Add stella_lang to path for imports
SCRIPT_DIR = Path(__file__).parent
STELLALANG_DIR = SCRIPT_DIR.parent / "stella_lang"
sys.path.insert(0, str(STELLALANG_DIR))

from soup import StellaSoup, execute_tape, Z3


# =============================================================================
# StellaLang with comparable metrics
# =============================================================================

class StellaLangBenchmark:
    """Run StellaLang soup with Genesis-comparable metrics.

    Adds inter-component correlation: after each interaction, measure
    how much of A's content matches B's content. This is analogous to
    Genesis's T+/T- correlation at co-located sites.
    """

    def __init__(self, soup_size=4096, program_size=24, max_steps=729,
                 mutation_rate=0.001, seed=42):
        self.soup = StellaSoup(
            soup_size=soup_size,
            program_size=program_size,
            max_steps=max_steps,
            mutation_rate=mutation_rate,
            seed=seed,
        )
        self.seed = seed
        self.log_records = []

    def measure_ab_correlation(self, sample_size=500):
        """Measure inter-component (A/B half) correlation.

        After running pairs through the VM, measure how much the
        two halves of the tape match. This is analogous to Genesis's
        T+/T- correlation.

        Returns the fraction of trit positions where A[i] == B[i].
        """
        rng = np.random.default_rng(self.seed + self.soup.epoch)
        matches = 0
        total = 0

        for _ in range(sample_size):
            a, b = rng.choice(self.soup.soup_size, size=2, replace=False)
            prog_a = self.soup.soup[a].copy()
            prog_b = self.soup.soup[b].copy()

            # Run interaction (without modifying soup)
            tape = np.concatenate([prog_a, prog_b]).copy()
            tape = execute_tape(tape, self.soup.max_steps, len(tape))

            half = self.soup.program_size
            result_a = tape[:half]
            result_b = tape[half:]

            matches += np.sum(result_a == result_b)
            total += half

        return matches / total if total > 0 else 0.333

    def measure_spatial_correlation(self, sample_size=500):
        """Measure neighbor-like correlation in the soup.

        Since StellaLang has no spatial mesh, we measure correlation
        between adjacent programs in the array as a proxy. This is
        NOT geometrically meaningful but provides a structural baseline.
        """
        matches = 0
        total = 0

        for i in range(min(sample_size, self.soup.soup_size - 1)):
            prog_a = self.soup.soup[i]
            prog_b = self.soup.soup[i + 1]
            matches += np.sum(prog_a == prog_b)
            total += self.soup.program_size

        return matches / total if total > 0 else 0.333

    def compute_trit_entropy(self):
        """Compute Shannon entropy of trit distribution."""
        all_trits = self.soup.soup.flatten()
        counts = np.bincount(all_trits, minlength=Z3).astype(float)
        probs = counts / counts.sum()
        return -sum(p * np.log2(p) for p in probs if p > 0)

    def run(self, epochs=2000, log_interval=100):
        """Run StellaLang soup and collect Genesis-comparable metrics."""
        print(f"\n{'='*65}")
        print(f"  StellaLang Soup (CPY01/CPY10 coupling)")
        print(f"{'='*65}")
        print(f"  soup_size={self.soup.soup_size}  program_size={self.soup.program_size}")
        print(f"  max_steps={self.soup.max_steps}  mutation_rate={self.soup.mutation_rate}")
        print(f"  seed={self.seed}  epochs={epochs}")
        print(f"{'='*65}")
        print()
        print(f"{'Epoch':>7} | {'H(trit)':>7} | {'AB_corr':>7} | "
              f"{'Nbr_corr':>8} | {'Unique':>6} | {'TopCnt':>6}")
        print("-" * 65)

        start = time.time()

        for e in range(epochs):
            self.soup.run_epoch()

            if self.soup.epoch % log_interval == 0:
                H = self.compute_trit_entropy()
                ab_corr = self.measure_ab_correlation()
                nbr_corr = self.measure_spatial_correlation()
                metrics = self.soup.compute_metrics()

                rec = {
                    "epoch": self.soup.epoch,
                    "H_trit": round(H, 4),
                    "ab_corr": round(ab_corr, 4),
                    "nbr_corr": round(nbr_corr, 4),
                    "unique": metrics["unique_programs"],
                    "top_count": metrics["top_count"],
                    "compression": metrics["compression_ratio"],
                }
                self.log_records.append(rec)

                print(f"{rec['epoch']:>7} | {rec['H_trit']:>7.4f} | "
                      f"{rec['ab_corr']:>7.4f} | {rec['nbr_corr']:>8.4f} | "
                      f"{rec['unique']:>6} | {rec['top_count']:>6}")

        elapsed = time.time() - start

        # Check for replicators at the end
        replicators = self.soup.check_self_replicators(sample_size=500)
        perfect = [r for r in replicators if r[0] == "perfect"]

        print(f"\n  Completed in {elapsed:.1f}s")
        print(f"  Replicators found: {len(perfect)} perfect")

        return self.log_records, perfect


# =============================================================================
# Genesis runner (calls compiled C binary)
# =============================================================================

def run_genesis(epochs, seed, coupling_strength, mode=0, n_sub=16,
                mutation_rate=0.001, epsilon=0.1, chirality=0.0,
                chirality_mode=0, instr_mode=0):
    """Run genesis_soup C binary and parse output."""
    binary = SCRIPT_DIR / "genesis_soup"
    if not binary.exists():
        print(f"ERROR: {binary} not found. Compile with:")
        print(f"  cc -O3 -o genesis_soup genesis_soup.c -lm")
        sys.exit(1)

    cmd = [
        str(binary),
        str(epochs), str(seed), str(coupling_strength),
        str(mode), str(n_sub), str(mutation_rate),
        str(epsilon), str(chirality), str(chirality_mode),
        str(instr_mode),
    ]

    print(f"\n  Running: {' '.join(cmd)}")
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=600)

    if result.returncode != 0:
        print(f"ERROR: genesis_soup returned {result.returncode}")
        print(result.stderr)
        sys.exit(1)

    return result.stdout


def parse_genesis_output(output):
    """Parse genesis_soup diagnostic lines."""
    records = []
    for line in output.split("\n"):
        m = re.match(
            r"epoch=(\d+)\s+"
            r"H_tp=([\d.]+)\s+H_tm=([\d.]+)\s+"
            r"corr=([\d.]+)\s+"
            r"auto_tp=([\d.]+)\s+auto_tm=([\d.]+)\s+"
            r"local_repl=([\d.]+)\s+"
            r"dir_bias=([\d.]+)",
            line.strip(),
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
    return records


# =============================================================================
# Comparison
# =============================================================================

def compare_results(genesis_records, stellalang_records, genesis_label="Genesis",
                    stellalang_replicators=None):
    """Print side-by-side comparison of final metrics."""
    if not genesis_records or not stellalang_records:
        print("ERROR: No records to compare")
        return {}

    g = genesis_records[-1]
    s = stellalang_records[-1]

    g_H = (g["H_tp"] + g["H_tm"]) / 2
    s_H = s["H_trit"]

    max_H = 1.585  # log2(3)
    random_corr = 0.333

    print(f"\n{'='*70}")
    print(f"  COMPARISON: {genesis_label} vs StellaLang")
    print(f"{'='*70}")
    print()
    print(f"  {'Metric':<30} | {'Genesis':>10} | {'StellaLang':>10} | {'Δ':>10}")
    print(f"  {'-'*30}-+-{'-'*10}-+-{'-'*10}-+-{'-'*10}")

    # Trit entropy
    print(f"  {'Trit entropy H':<30} | {g_H:>10.4f} | {s_H:>10.4f} | "
          f"{g_H - s_H:>+10.4f}")
    print(f"  {'H drop from random (1.585)':<30} | "
          f"{max_H - g_H:>10.4f} | {max_H - s_H:>10.4f} | "
          f"{(max_H - g_H) - (max_H - s_H):>+10.4f}")

    # Inter-component correlation
    g_corr = g["corr"]
    s_corr = s["ab_corr"]
    print(f"  {'Inter-comp correlation':<30} | {g_corr:>10.4f} | {s_corr:>10.4f} | "
          f"{g_corr - s_corr:>+10.4f}")
    print(f"  {'  (above random 0.333)':<30} | "
          f"{g_corr - random_corr:>10.4f} | {s_corr - random_corr:>10.4f} | "
          f"{(g_corr - random_corr) - (s_corr - random_corr):>+10.4f}")

    # Spatial correlation
    g_auto = (g["auto_tp"] + g["auto_tm"]) / 2
    s_nbr = s["nbr_corr"]
    print(f"  {'Spatial/neighbor corr':<30} | {g_auto:>10.4f} | {s_nbr:>10.4f} | "
          f"{g_auto - s_nbr:>+10.4f}")

    # Local replication
    g_repl = g["local_repl"]
    print(f"  {'Local replication density':<30} | {g_repl:>10.4f} | {'—':>10} | {'—':>10}")

    # Directional bias
    g_bias = g["dir_bias"]
    print(f"  {'Directional bias (0.5=sym)':<30} | {g_bias:>10.4f} | {'—':>10} | {'—':>10}")

    # StellaLang-only metrics
    print(f"  {'Unique programs':<30} | {'—':>10} | {s['unique']:>10} | {'—':>10}")
    print(f"  {'Top program count':<30} | {'—':>10} | {s['top_count']:>10} | {'—':>10}")

    n_repl = len(stellalang_replicators) if stellalang_replicators else 0
    print(f"  {'Self-replicators found':<30} | {'—':>10} | {n_repl:>10} | {'—':>10}")

    print()

    # Interpretation
    print(f"  INTERPRETATION:")
    print(f"  {'-'*65}")

    corr_ratio = (g_corr - random_corr) / (s_corr - random_corr) if s_corr > random_corr else float('inf')
    print(f"  Inter-component correlation ratio (Genesis/StellaLang): {corr_ratio:.2f}x")

    if g_corr > s_corr:
        print(f"  → Geometric coupling produces MORE inter-surface coherence than CPY01")
    elif s_corr > g_corr:
        print(f"  → CPY01 produces MORE inter-surface coherence than geometric coupling")
    else:
        print(f"  → Both coupling mechanisms produce similar coherence")

    entropy_ratio = (max_H - g_H) / (max_H - s_H) if s_H < max_H else float('inf')
    print(f"  Entropy reduction ratio (Genesis/StellaLang): {entropy_ratio:.2f}x")

    if g_H < s_H:
        print(f"  → Genesis produces MORE self-organization (lower entropy)")
    elif s_H < g_H:
        print(f"  → StellaLang produces MORE self-organization (lower entropy)")
    else:
        print(f"  → Both produce similar entropy levels")

    print()

    return {
        "genesis_final": g,
        "stellalang_final": s,
        "corr_ratio": round(corr_ratio, 3),
        "entropy_ratio": round(entropy_ratio, 3),
        "stellalang_replicators": n_repl,
    }


# =============================================================================
# Main
# =============================================================================

def main():
    """Run Genesis vs StellaLang comparison at matched parameters."""
    print("=" * 70)
    print("  Phase 5: Genesis vs StellaLang Comparison")
    print("  Coupling mechanism: geometric pressure (G1) vs CPY01/CPY10 (G2)")
    print("=" * 70)

    # Matched parameters
    SEED = 42
    MUTATION_RATE = 0.001
    PROGRAM_SIZE = 24
    MAX_STEPS = 729

    # Genesis parameters
    GENESIS_EPOCHS = 1_000_000   # 1M epochs (each = 1 patch interaction)
    COUPLING_STRENGTH = 0.5      # Standard coupling strength
    N_SUB = 16                   # Standard mesh subdivision

    # StellaLang parameters
    # Each StellaLang epoch = soup_size/2 = 2048 interactions
    # 1M Genesis epochs ≈ 1M patch interactions
    # To match total interactions: SL_epochs = 1M / 2048 ≈ 488
    # But StellaLang needs more epochs for dynamics, so use 2000 (standard)
    SL_SOUP_SIZE = 4096
    SL_EPOCHS = 2000
    SL_LOG_INTERVAL = 100

    # Total interactions comparison:
    sl_total = SL_EPOCHS * SL_SOUP_SIZE // 2
    print(f"\n  Parameter matching:")
    print(f"    program_size = {PROGRAM_SIZE}")
    print(f"    max_steps    = {MAX_STEPS}")
    print(f"    mutation_rate = {MUTATION_RATE}")
    print(f"    seed         = {SEED}")
    print(f"    Genesis epochs       = {GENESIS_EPOCHS:,} (1 patch/epoch)")
    print(f"    StellaLang epochs    = {SL_EPOCHS:,} ({SL_SOUP_SIZE//2} pairs/epoch)")
    print(f"    StellaLang total interactions = {sl_total:,}")
    print()

    # ── Run Genesis (3 configurations) ──
    genesis_configs = [
        ("Genesis classic (cs=0.5)", 0.5, 0),   # classic VM
        ("Genesis enhanced (cs=0.5)", 0.5, 1),   # SENSE/COUPLE VM
    ]

    genesis_results = {}
    for label, cs, instr_mode in genesis_configs:
        print(f"\n{'='*65}")
        print(f"  {label}")
        print(f"{'='*65}")

        output = run_genesis(
            epochs=GENESIS_EPOCHS,
            seed=SEED,
            coupling_strength=cs,
            mode=0,
            n_sub=N_SUB,
            mutation_rate=MUTATION_RATE,
            epsilon=0.1,
            chirality=0.0,
            chirality_mode=0,
            instr_mode=instr_mode,
        )
        records = parse_genesis_output(output)

        if records:
            last = records[-1]
            g_H = (last["H_tp"] + last["H_tm"]) / 2
            print(f"  Final: H={g_H:.4f}  corr={last['corr']:.4f}  "
                  f"auto={(last['auto_tp']+last['auto_tm'])/2:.4f}  "
                  f"repl={last['local_repl']:.4f}  bias={last['dir_bias']:.4f}")
        else:
            print("  WARNING: No diagnostic records parsed")

        genesis_results[label] = records

    # ── Run StellaLang ──
    sl_bench = StellaLangBenchmark(
        soup_size=SL_SOUP_SIZE,
        program_size=PROGRAM_SIZE,
        max_steps=MAX_STEPS,
        mutation_rate=MUTATION_RATE,
        seed=SEED,
    )
    sl_records, sl_replicators = sl_bench.run(
        epochs=SL_EPOCHS,
        log_interval=SL_LOG_INTERVAL,
    )

    # ── Compare ──
    all_comparisons = {}
    for label, records in genesis_results.items():
        comp = compare_results(
            records, sl_records,
            genesis_label=label,
            stellalang_replicators=sl_replicators,
        )
        all_comparisons[label] = comp

    # ── Summary table ──
    print(f"\n{'='*70}")
    print(f"  SUMMARY TABLE")
    print(f"{'='*70}")
    print()
    print(f"  {'System':<30} | {'H(trit)':>7} | {'Corr':>7} | {'Auto':>7} | {'Repl':>7}")
    print(f"  {'-'*30}-+-{'-'*7}-+-{'-'*7}-+-{'-'*7}-+-{'-'*7}")

    for label, records in genesis_results.items():
        if records:
            last = records[-1]
            g_H = (last["H_tp"] + last["H_tm"]) / 2
            g_auto = (last["auto_tp"] + last["auto_tm"]) / 2
            print(f"  {label:<30} | {g_H:>7.4f} | {last['corr']:>7.4f} | "
                  f"{g_auto:>7.4f} | {last['local_repl']:>7.4f}")

    if sl_records:
        s = sl_records[-1]
        print(f"  {'StellaLang (CPY01/CPY10)':<30} | {s['H_trit']:>7.4f} | "
              f"{s['ab_corr']:>7.4f} | {s['nbr_corr']:>7.4f} | {'—':>7}")

    print(f"  {'Random baseline':<30} | {'1.5850':>7} | {'0.3333':>7} | "
          f"{'0.3333':>7} | {'0.3333':>7}")
    print()

    # ── Save results ──
    output_path = SCRIPT_DIR / "phase5_comparison.json"
    with open(output_path, "w") as f:
        json.dump({
            "parameters": {
                "program_size": PROGRAM_SIZE,
                "max_steps": MAX_STEPS,
                "mutation_rate": MUTATION_RATE,
                "seed": SEED,
                "genesis_epochs": GENESIS_EPOCHS,
                "stellalang_epochs": SL_EPOCHS,
                "stellalang_soup_size": SL_SOUP_SIZE,
            },
            "genesis_configs": {
                label: records[-1] if records else None
                for label, records in genesis_results.items()
            },
            "stellalang_final": sl_records[-1] if sl_records else None,
            "stellalang_replicators": len(sl_replicators),
            "comparisons": all_comparisons,
        }, f, indent=2, default=str)
    print(f"  Results saved to {output_path}")


if __name__ == "__main__":
    main()
