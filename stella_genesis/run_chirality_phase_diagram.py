#!/usr/bin/env python3
"""
Chirality × Enhanced VM Phase Diagram (RESULTS-Phase1 Item #1)
===============================================================

Joint (χ, cs) sweep with all three instruction modes (classic, enhanced, write)
to map the phase diagram and find the crossover boundary χ*(cs) where enhanced
VM stops outperforming classic.

Motivation: Experiment 4b showed enhanced beats classic at low χ but loses at
high χ (0.903 vs 0.881 at χ=1.0, cs=0.5). The crossover χ* may depend on cs,
revealing distinct regimes in the (χ, cs) plane.
"""

import subprocess
import re
import json
import sys
import time
from datetime import datetime

BINARY = "./genesis_soup"
EPOCHS = 1_000_000
N_SUB = 16
MU = 0.001
EPS = 0.1
SEED = 42
CHI_MODE = 0  # pressure-asymmetry

# Grid: 5 cs × 11 χ × 3 modes = 165 runs
CS_VALUES = [0.1, 0.3, 0.5, 0.7, 1.0]
CHI_VALUES = [0.0, 0.1, 0.2, 0.3, 0.35, 0.4, 0.45, 0.5, 0.6, 0.8, 1.0]
INSTR_MODES = [(0, "classic"), (1, "enhanced"), (2, "write")]

OUTPUT_FILE = "chirality_phase_diagram_results.json"


def run_genesis(cs, chi, instr_mode):
    """Run genesis_soup and parse final diagnostics."""
    cmd = [
        BINARY, str(EPOCHS), str(SEED), str(cs), "0",
        str(N_SUB), str(MU), str(EPS), str(chi), str(CHI_MODE),
        str(instr_mode)
    ]
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout

    epoch_lines = [l for l in output.split('\n') if l.startswith('epoch=')]
    if not epoch_lines:
        return None
    last = epoch_lines[-1]

    data = {}
    for match in re.finditer(r'(\w+)=([\d.e+-]+)', last):
        key, val = match.groups()
        try:
            data[key] = float(val)
        except ValueError:
            data[key] = val

    for line in output.split('\n'):
        if 'SENSE executions:' in line:
            data['sense_exec'] = int(re.search(r'(\d+)', line.split(':')[1]).group())
        if 'COUPLE executions:' in line:
            data['couple_exec'] = int(re.search(r'(\d+)', line.split(':')[1]).group())
        if 'COUPLE-enhanced couplings:' in line:
            data['couple_enhanced'] = int(re.search(r'(\d+)', line.split(':')[1]).group())
        if 'WRITE executions:' in line:
            data['write_exec'] = int(re.search(r'(\d+)', line.split(':')[1]).group())

    return data


def main():
    total_runs = len(CS_VALUES) * len(CHI_VALUES) * len(INSTR_MODES)
    print(f"Chirality × Enhanced VM Phase Diagram")
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print(f"Grid: {len(CS_VALUES)} cs × {len(CHI_VALUES)} χ × {len(INSTR_MODES)} modes = {total_runs} runs")
    print(f"Epochs: {EPOCHS:,} per run")
    print()

    results = []
    run_num = 0
    t_start = time.time()

    # Header
    print(f"{'#':>3} | {'cs':>4} | {'χ':>5} | {'mode':>8} | {'corr':>6} | "
          f"{'auto_tp':>7} | {'H_tp':>5} | {'repl':>5} | {'bias':>5}")
    print("-" * 75)

    for cs in CS_VALUES:
        for chi in CHI_VALUES:
            for instr_code, label in INSTR_MODES:
                run_num += 1
                d = run_genesis(cs, chi, instr_code)
                if d is None:
                    print(f"{run_num:3d} | {cs:4.1f} | {chi:5.2f} | {label:>8} | FAILED")
                    continue

                corr = d.get('corr', 0)
                auto_tp = d.get('auto_tp', 0)
                H_tp = d.get('H_tp', 0)
                repl = d.get('local_repl', 0)
                bias = d.get('dir_bias', 0)

                print(f"{run_num:3d} | {cs:4.1f} | {chi:5.2f} | {label:>8} | "
                      f"{corr:6.3f} | {auto_tp:7.3f} | {H_tp:5.3f} | "
                      f"{repl:5.3f} | {bias:5.3f}")

                results.append({
                    'cs': cs, 'chi': chi, 'instr_mode': label, **d
                })

                # Progress estimate
                elapsed = time.time() - t_start
                rate = elapsed / run_num
                remaining = rate * (total_runs - run_num)
                if run_num % 10 == 0:
                    print(f"    [{run_num}/{total_runs}] "
                          f"~{remaining/60:.0f} min remaining", file=sys.stderr)

    elapsed = time.time() - t_start
    print(f"\nCompleted {run_num} runs in {elapsed/60:.1f} minutes")

    # Save results
    output = {
        'metadata': {
            'experiment': 'chirality_phase_diagram',
            'date': datetime.now().isoformat(),
            'epochs': EPOCHS,
            'seed': SEED,
            'n_sub': N_SUB,
            'mu': MU,
            'eps': EPS,
            'cs_values': CS_VALUES,
            'chi_values': CHI_VALUES,
            'instr_modes': [m[1] for m in INSTR_MODES],
            'total_runs': total_runs,
            'elapsed_seconds': elapsed
        },
        'results': results
    }

    with open(OUTPUT_FILE, 'w') as f:
        json.dump(output, f, indent=2, default=str)
    print(f"Results saved to {OUTPUT_FILE}")

    # Quick summary: find crossover for each cs
    print("\n" + "=" * 70)
    print("CROSSOVER ANALYSIS: χ* where classic overtakes enhanced")
    print("=" * 70)

    for cs in CS_VALUES:
        classic = {r['chi']: r['corr'] for r in results
                   if r['cs'] == cs and r['instr_mode'] == 'classic'}
        enhanced = {r['chi']: r['corr'] for r in results
                    if r['cs'] == cs and r['instr_mode'] == 'enhanced'}
        write_ = {r['chi']: r['corr'] for r in results
                  if r['cs'] == cs and r['instr_mode'] == 'write'}

        print(f"\ncs = {cs}:")
        print(f"  {'χ':>5} | {'classic':>7} | {'enhanced':>8} | {'write':>7} | {'Δ(e-c)':>7} | {'best':>8}")
        print(f"  " + "-" * 60)

        crossover = None
        prev_delta = None
        for chi in CHI_VALUES:
            c = classic.get(chi)
            e = enhanced.get(chi)
            w = write_.get(chi)
            if c is None or e is None:
                continue
            delta = e - c
            best_val = max(c, e, w if w else 0)
            best_label = 'classic' if best_val == c else ('enhanced' if best_val == e else 'write')

            marker = ""
            if prev_delta is not None and prev_delta > 0 and delta <= 0:
                crossover = chi
                marker = " ← crossover"
            prev_delta = delta

            print(f"  {chi:5.2f} | {c:7.3f} | {e:8.3f} | "
                  f"{w:7.3f} | {delta:+7.3f} | {best_label:>8}{marker}")

        if crossover is not None:
            print(f"  → χ* ≈ {crossover} (enhanced → classic crossover)")
        else:
            enh_always = all(enhanced.get(chi, 0) >= classic.get(chi, 0)
                            for chi in CHI_VALUES if chi in classic)
            if enh_always:
                print(f"  → No crossover: enhanced dominates across all χ")
            else:
                print(f"  → No crossover: classic dominates across all χ")


if __name__ == "__main__":
    main()
