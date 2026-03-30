#!/usr/bin/env python3
"""
Phase 4 Experiment: Enhanced VM Instructions (SENSE/COUPLE)
============================================================

Tests whether replacing NOP1/NOP2 with geometric-aware instructions
improves program-level emergence in the G1-only VM.

SENSE (opcode 7): Reads P_own/(P_own+P_other) at head position,
    encodes as Z3 trit: 0=own-dominant, 1=balanced, 2=other-dominant.
    Grounded in Def 0.1.3 (pressure is an observable geometric quantity).

COUPLE (opcode 8): Marks current site for 2x enhanced coupling probability.
    Meta-operation: computation influences the geometry->computation loop.
"""

import subprocess
import re
import json
from datetime import datetime

BINARY = "./genesis_soup"
EPOCHS = 1_000_000
SEED = 42
N_SUB = 16
MU = 0.001
EPS = 0.1

def run_genesis(epochs, seed, cs, mode, n_sub, mu, eps, chi, chi_mode, instr_mode):
    """Run genesis_soup and parse the final diagnostics."""
    cmd = [
        BINARY, str(epochs), str(seed), str(cs), str(mode),
        str(n_sub), str(mu), str(eps), str(chi), str(chi_mode),
        str(instr_mode)
    ]
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout

    # Parse final epoch line (last one matching epoch=)
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

    # Parse SENSE/COUPLE stats from final output
    for line in output.split('\n'):
        if 'SENSE executions:' in line:
            data['sense_exec'] = int(re.search(r'(\d+)', line.split(':')[1]).group())
        if 'COUPLE executions:' in line:
            data['couple_exec'] = int(re.search(r'(\d+)', line.split(':')[1]).group())
        if 'COUPLE-enhanced couplings:' in line:
            data['couple_enhanced'] = int(re.search(r'(\d+)', line.split(':')[1]).group())

    return data


def experiment_4a_coupling_sweep():
    """Compare classic vs enhanced across coupling strengths."""
    print("=" * 70)
    print("Experiment 4a: Coupling Strength Sweep (classic vs enhanced)")
    print("=" * 70)

    cs_values = [0.0, 0.1, 0.3, 0.5, 0.7, 1.0]
    results = []

    print(f"\n{'cs':>4} | {'Mode':>10} | {'corr':>6} | {'auto_tp':>7} | {'auto_tm':>7} | "
          f"{'H(T+)':>6} | {'H(T-)':>6} | {'repl':>6} | {'bias':>5}")
    print("-" * 80)

    for cs in cs_values:
        for instr_mode, label in [(0, "classic"), (1, "enhanced")]:
            d = run_genesis(EPOCHS, SEED, cs, 0, N_SUB, MU, EPS, 0.0, 0, instr_mode)
            if d:
                print(f"{cs:4.1f} | {label:>10} | {d['corr']:6.3f} | "
                      f"{d['auto_tp']:7.3f} | {d['auto_tm']:7.3f} | "
                      f"{d['H_tp']:6.3f} | {d['H_tm']:6.3f} | "
                      f"{d.get('local_repl', 0):6.3f} | {d['dir_bias']:5.3f}")
                results.append({
                    'cs': cs, 'instr_mode': label, **d
                })

    return results


def experiment_4b_chirality_interaction():
    """Test interaction between enhanced VM and chirality."""
    print("\n" + "=" * 70)
    print("Experiment 4b: Enhanced VM + Chirality Interaction (cs=0.5)")
    print("=" * 70)

    chi_values = [0.0, 0.05, 0.1, 0.2, 0.3, 0.5, 1.0]
    results = []

    print(f"\n{'chi':>5} | {'Mode':>10} | {'corr':>6} | {'auto_tp':>7} | "
          f"{'repl':>6} | {'bias':>5}")
    print("-" * 60)

    for chi in chi_values:
        for instr_mode, label in [(0, "classic"), (1, "enhanced")]:
            d = run_genesis(EPOCHS, SEED, 0.5, 0, N_SUB, MU, EPS, chi, 0, instr_mode)
            if d:
                print(f"{chi:5.2f} | {label:>10} | {d['corr']:6.3f} | "
                      f"{d['auto_tp']:7.3f} | "
                      f"{d.get('local_repl', 0):6.3f} | {d['dir_bias']:5.3f}")
                results.append({
                    'chi': chi, 'instr_mode': label, **d
                })

    return results


def experiment_4c_seed_robustness():
    """Test across multiple seeds for robustness."""
    print("\n" + "=" * 70)
    print("Experiment 4c: Seed Robustness (cs=0.5, 5 seeds)")
    print("=" * 70)

    seeds = [42, 137, 2718, 31415, 99999]
    results = []

    print(f"\n{'seed':>6} | {'Mode':>10} | {'corr':>6} | {'auto_tp':>7} | "
          f"{'repl':>6} | {'sense':>8} | {'couple':>8}")
    print("-" * 72)

    for seed in seeds:
        for instr_mode, label in [(0, "classic"), (1, "enhanced")]:
            d = run_genesis(EPOCHS, seed, 0.5, 0, N_SUB, MU, EPS, 0.0, 0, instr_mode)
            if d:
                sense = d.get('sense_exec', 0)
                couple = d.get('couple_exec', 0)
                print(f"{seed:6d} | {label:>10} | {d['corr']:6.3f} | "
                      f"{d['auto_tp']:7.3f} | "
                      f"{d.get('local_repl', 0):6.3f} | "
                      f"{sense:8d} | {couple:8d}")
                results.append({
                    'seed': seed, 'instr_mode': label, **d
                })

    # Compute averages
    print("\n--- Averages ---")
    for label in ["classic", "enhanced"]:
        subset = [r for r in results if r['instr_mode'] == label]
        avg_corr = sum(r['corr'] for r in subset) / len(subset)
        avg_auto = sum(r['auto_tp'] for r in subset) / len(subset)
        avg_repl = sum(r.get('local_repl', 0) for r in subset) / len(subset)
        print(f"{label:>10}: corr={avg_corr:.3f}  auto_tp={avg_auto:.3f}  repl={avg_repl:.3f}")

    return results


def experiment_4d_vm_only():
    """Test SENSE alone (no coupling) to isolate its contribution."""
    print("\n" + "=" * 70)
    print("Experiment 4d: SENSE Contribution (VM-only mode, no coupling)")
    print("=" * 70)

    results = []
    print(f"\n{'Mode':>10} | {'Instr':>10} | {'H(T+)':>6} | {'auto_tp':>7} | {'auto_tm':>7}")
    print("-" * 55)

    for instr_mode, label in [(0, "classic"), (1, "enhanced")]:
        d = run_genesis(EPOCHS, SEED, 0.5, 2, N_SUB, MU, EPS, 0.0, 0, instr_mode)
        if d:
            print(f"{'VM-only':>10} | {label:>10} | {d['H_tp']:6.3f} | "
                  f"{d['auto_tp']:7.3f} | {d['auto_tm']:7.3f}")
            results.append({'experiment': 'vm_only', 'instr_mode': label, **d})

    return results


def main():
    print("Phase 4: Enhanced VM Instructions (SENSE/COUPLE)")
    print(f"Date: {datetime.now().strftime('%Y-%m-%d')}")
    print(f"Epochs: {EPOCHS:,}")
    print()

    all_results = {}
    all_results['4a'] = experiment_4a_coupling_sweep()
    all_results['4b'] = experiment_4b_chirality_interaction()
    all_results['4c'] = experiment_4c_seed_robustness()
    all_results['4d'] = experiment_4d_vm_only()

    # Save raw results
    with open('phase4_enhanced_vm_results.json', 'w') as f:
        json.dump(all_results, f, indent=2, default=str)

    print("\n" + "=" * 70)
    print("Results saved to phase4_enhanced_vm_results.json")


if __name__ == "__main__":
    main()
