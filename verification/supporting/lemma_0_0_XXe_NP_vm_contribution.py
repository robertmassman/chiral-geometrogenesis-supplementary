#!/usr/bin/env python3
"""
Lemma 0.0.XXe-NP: VM Contribution to Nucleation — Monte Carlo Estimation
=========================================================================

Estimates the VM's contribution to program-space exploration by:
1. Measuring per-interaction replicator generation probability p_VM
2. Measuring per-trit scrambling rate (Hamming distance statistics)
3. Computing the effective mixing time reduction
4. Deriving tightened nucleation bounds

Related Documents:
- Proof: docs/proofs/supporting/Lemma-0.0.XXe-Nucleation-Probability-Proof.md §4.2
- VM spec: stella_lang/soup.c
- Phase 1 data: docs/proofs/verification-records/Proposition-0.0.XXe-Phase1-2D-Soup-Results.md

Verification Date: 2026-03-11
"""

import numpy as np
import json
from datetime import datetime
import time

# ==============================================================================
# VM IMPLEMENTATION (exact port of soup.c execute_tape)
# ==============================================================================

# Instruction encoding: (high, low) -> high * 3 + low
OP_NOP   = 0  # (0,0)
OP_ROT   = 1  # (0,1) phase rotate
OP_FWD0  = 2  # (0,2) advance h0
OP_BCK0  = 3  # (1,0) retreat h0
OP_FWD1  = 4  # (1,1) advance h1
OP_OPEN  = 5  # (1,2) loop open
OP_CLOSE = 6  # (2,0) loop close
OP_CPY01 = 7  # (2,1) T+ -> T-
OP_CPY10 = 8  # (2,2) T- -> T+

OPNAMES = ['NOP', 'ROT', 'FWD0', 'BCK0', 'FWD1', 'OPEN', 'CLOSE', 'CPY01', 'CPY10']


def execute_tape(tape, max_steps=729):
    """Execute the VM on a mutable tape (list of ints 0-2).

    Exact port of soup.c execute_tape().
    Returns the tape modified in-place (also returns it for convenience).
    """
    tape_len = len(tape)
    ip = 0
    h0 = 0
    h1 = tape_len // 2
    steps = 0

    while steps < max_steps and ip + 1 < tape_len:
        op = tape[ip] * 3 + tape[ip + 1]

        if op == OP_NOP:
            pass

        elif op == OP_ROT:
            v = tape[h0]
            tape[h0] = v + 1 if v < 2 else 0

        elif op == OP_FWD0:
            h0 += 1
            if h0 >= tape_len:
                h0 = 0

        elif op == OP_BCK0:
            h0 -= 1
            if h0 < 0:
                h0 = tape_len - 1

        elif op == OP_FWD1:
            h1 += 1
            if h1 >= tape_len:
                h1 = 0

        elif op == OP_OPEN:
            if tape[h0] == 0:
                depth = 1
                pos = ip + 2
                while depth > 0 and pos + 1 < tape_len:
                    inner = tape[pos] * 3 + tape[pos + 1]
                    if inner == OP_OPEN:
                        depth += 1
                    elif inner == OP_CLOSE:
                        depth -= 1
                    pos += 2
                if depth == 0:
                    ip = pos - 2

        elif op == OP_CLOSE:
            if tape[h0] != 0:
                depth = 1
                pos = ip - 2
                while depth > 0 and pos >= 0:
                    inner = tape[pos] * 3 + tape[pos + 1]
                    if inner == OP_CLOSE:
                        depth += 1
                    elif inner == OP_OPEN:
                        depth -= 1
                    pos -= 2
                if depth == 0:
                    ip = pos + 2

        elif op == OP_CPY01:
            tape[h1] = tape[h0]

        elif op == OP_CPY10:
            tape[h0] = tape[h1]

        ip += 2
        steps += 1

    return tape


def vm_interact(A, B, max_steps=729):
    """Execute VM interaction between tiles A and B.

    Args:
        A, B: lists/arrays of ints (0-2), each of length L
        max_steps: VM step limit

    Returns:
        (A', B'): output tiles after VM execution
    """
    L = len(A)
    tape = list(A) + list(B)
    execute_tape(tape, max_steps)
    return tape[:L], tape[L:]


def is_replicator(prog, max_steps=729):
    """Test if prog is a self-replicator (S + 0^L -> (S, S)).

    Args:
        prog: list of ints (0-2), length L

    Returns:
        True if prog is a perfect self-replicator with zero food
    """
    L = len(prog)
    food = [0] * L
    tape = list(prog) + food
    execute_tape(tape, max_steps)
    return tape[:L] == list(prog) and tape[L:] == list(prog)


def is_trivial(prog):
    """Check if program is trivially a replicator (all same trit)."""
    return len(set(prog)) <= 1


# ==============================================================================
# MONTE CARLO ESTIMATION: p_VM (replicator generation probability)
# ==============================================================================

def estimate_p_vm(n_trials, L=24, max_steps=729, rng=None, verbose=True):
    """Estimate per-interaction replicator generation probability.

    For n_trials random (A, B) pairs, execute the VM and check if
    either output tile is a (nontrivial) self-replicator.

    Returns dict with estimates and statistics.
    """
    if rng is None:
        rng = np.random.default_rng(42)

    replicator_count = 0
    trivial_replicator_count = 0
    hamming_A = []  # Hamming distance d(A, A')
    hamming_B = []  # Hamming distance d(B, B')
    trits_changed_A = []  # Fraction of trits changed in A
    trits_changed_B = []

    t0 = time.time()
    report_interval = max(n_trials // 10, 1)

    for trial in range(n_trials):
        # Generate random tiles
        A = rng.integers(0, 3, size=L).tolist()
        B = rng.integers(0, 3, size=L).tolist()

        # Execute VM
        Ap, Bp = vm_interact(A, B, max_steps)

        # Hamming distances
        dA = sum(1 for a, ap in zip(A, Ap) if a != ap)
        dB = sum(1 for b, bp in zip(B, Bp) if b != bp)
        hamming_A.append(dA)
        hamming_B.append(dB)
        trits_changed_A.append(dA / L)
        trits_changed_B.append(dB / L)

        # Check if outputs are replicators
        found = False
        for prog in (Ap, Bp):
            if is_replicator(prog, max_steps):
                if is_trivial(prog):
                    trivial_replicator_count += 1
                else:
                    replicator_count += 1
                    found = True

        if found and verbose:
            print(f"  [Trial {trial}] Found nontrivial replicator!")
            print(f"    A = {A}")
            print(f"    B = {B}")
            print(f"    A' = {Ap}")
            print(f"    B' = {Bp}")

        if verbose and (trial + 1) % report_interval == 0:
            elapsed = time.time() - t0
            rate = (trial + 1) / elapsed
            print(f"  Progress: {trial+1}/{n_trials} ({rate:.0f} trials/s), "
                  f"replicators found: {replicator_count}")

    elapsed = time.time() - t0

    # Compute statistics
    hamming_A = np.array(hamming_A)
    hamming_B = np.array(hamming_B)

    results = {
        "n_trials": n_trials,
        "L": L,
        "max_steps": max_steps,
        "elapsed_seconds": elapsed,
        "trials_per_second": n_trials / elapsed,

        # Replicator generation
        "nontrivial_replicators_found": replicator_count,
        "trivial_replicators_found": trivial_replicator_count,
        "p_vm_estimate": replicator_count / n_trials,
        "p_vm_upper_95": (replicator_count + 1.96 * np.sqrt(max(replicator_count, 1))) / n_trials,

        # Hamming distance statistics (A -> A')
        "hamming_A_mean": float(hamming_A.mean()),
        "hamming_A_std": float(hamming_A.std()),
        "hamming_A_median": float(np.median(hamming_A)),
        "hamming_A_zero_frac": float(np.mean(hamming_A == 0)),

        # Hamming distance statistics (B -> B')
        "hamming_B_mean": float(hamming_B.mean()),
        "hamming_B_std": float(hamming_B.std()),
        "hamming_B_median": float(np.median(hamming_B)),
        "hamming_B_zero_frac": float(np.mean(hamming_B == 0)),

        # Per-trit scrambling rate
        "alpha_A_mean": float(np.mean(trits_changed_A)),
        "alpha_B_mean": float(np.mean(trits_changed_B)),
        "alpha_combined_mean": float((np.mean(trits_changed_A) + np.mean(trits_changed_B)) / 2),

        # Distribution of Hamming distances
        "hamming_A_histogram": {str(k): int(v) for k, v in
                                zip(*np.unique(hamming_A, return_counts=True))},
        "hamming_B_histogram": {str(k): int(v) for k, v in
                                zip(*np.unique(hamming_B, return_counts=True))},
    }

    return results


# ==============================================================================
# MONTE CARLO ESTIMATION: Effective scrambling per trit position
# ==============================================================================

def estimate_per_trit_scrambling(n_trials, L=24, max_steps=729, rng=None):
    """Measure how often each trit position is changed by VM interactions.

    Returns per-position scrambling rates alpha_ell for ell = 0..L-1.
    """
    if rng is None:
        rng = np.random.default_rng(123)

    changed_A = np.zeros(L, dtype=int)
    changed_B = np.zeros(L, dtype=int)

    for _ in range(n_trials):
        A = rng.integers(0, 3, size=L).tolist()
        B = rng.integers(0, 3, size=L).tolist()
        Ap, Bp = vm_interact(A, B, max_steps)

        for ell in range(L):
            if A[ell] != Ap[ell]:
                changed_A[ell] += 1
            if B[ell] != Bp[ell]:
                changed_B[ell] += 1

    return {
        "alpha_A_per_trit": (changed_A / n_trials).tolist(),
        "alpha_B_per_trit": (changed_B / n_trials).tolist(),
        "alpha_A_mean": float(changed_A.mean() / n_trials),
        "alpha_B_mean": float(changed_B.mean() / n_trials),
    }


# ==============================================================================
# MONTE CARLO: VM output distribution analysis
# ==============================================================================

def analyze_vm_output_distribution(n_trials, L=24, max_steps=729, rng=None):
    """Analyze the distribution of VM outputs from random inputs.

    Measures:
    - Per-trit output distribution (how close to uniform?)
    - Per-trit entropy of the output
    - Correlation between output trits
    """
    if rng is None:
        rng = np.random.default_rng(456)

    # Count per-trit output values for A' and B'
    counts_A = np.zeros((L, 3), dtype=int)
    counts_B = np.zeros((L, 3), dtype=int)

    for _ in range(n_trials):
        A = rng.integers(0, 3, size=L).tolist()
        B = rng.integers(0, 3, size=L).tolist()
        Ap, Bp = vm_interact(A, B, max_steps)

        for ell in range(L):
            counts_A[ell, Ap[ell]] += 1
            counts_B[ell, Bp[ell]] += 1

    # Per-trit entropy
    def trit_entropy(counts_row, n):
        p = counts_row / n
        p = p[p > 0]
        return -np.sum(p * np.log2(p))

    entropy_A = [trit_entropy(counts_A[ell], n_trials) for ell in range(L)]
    entropy_B = [trit_entropy(counts_B[ell], n_trials) for ell in range(L)]

    # TV distance from uniform
    def tv_from_uniform(counts_row, n):
        p = counts_row / n
        return 0.5 * np.sum(np.abs(p - 1/3))

    tv_A = [tv_from_uniform(counts_A[ell], n_trials) for ell in range(L)]
    tv_B = [tv_from_uniform(counts_B[ell], n_trials) for ell in range(L)]

    return {
        "entropy_A_per_trit": entropy_A,
        "entropy_B_per_trit": entropy_B,
        "entropy_A_mean": float(np.mean(entropy_A)),
        "entropy_B_mean": float(np.mean(entropy_B)),
        "max_entropy": float(np.log2(3)),
        "tv_A_per_trit": tv_A,
        "tv_B_per_trit": tv_B,
        "tv_A_mean": float(np.mean(tv_A)),
        "tv_B_mean": float(np.mean(tv_B)),
    }


# ==============================================================================
# COMPUTE TIGHTENED BOUNDS
# ==============================================================================

def compute_tightened_bounds(alpha_vm, L=24, r=120, mu=0.001):
    """Compute tightened nucleation bounds incorporating VM scrambling.

    Args:
        alpha_vm: per-trit per-epoch VM scrambling rate
        L: program length (trits)
        r: number of replicator programs
        mu: per-trit mutation rate

    Returns dict with tightened bounds and comparison to mutation-only.
    """
    import math

    # Mutation-only parameters (from §2.3)
    tau_mix_mut = math.ceil(3 / mu)
    q_min_mut = (1/3 - math.exp(-3)) ** L

    # VM-enhanced effective mutation rate
    # Each tile participates in ~1 VM interaction per epoch (N/2 interactions for N tiles)
    # The VM changes each trit with probability alpha_vm
    # Combined with mutation rate mu, the effective per-trit randomization rate is:
    mu_eff = 1 - (1 - mu) * (1 - alpha_vm * 2/3)
    # Factor of 2/3: when VM changes a trit, it maps to a value that is
    # ~uniformly distributed over Z_3 (from random partner), so probability
    # of change to any specific target = 2/3 * alpha_vm (since change happens
    # only if new value differs from old, but we want probability of being
    # set to any specific value, which is alpha_vm * 1/3 + (1-alpha_vm) * delta)

    # More precisely: after VM + mutation, the probability of trit taking value v
    # given it started at v0 is:
    # P(v|v0) = sum_w P_VM(w|v0) * P_mut(v|w)
    # where P_VM(w|v0) = alpha_vm * q_vm(w) + (1-alpha_vm) * delta(w,v0)
    # and P_mut(v|w) = (1-mu)*delta(v,w) + mu/3

    # If VM output is approximately uniform: q_vm(w) ≈ 1/3 for all w
    # Then P(v|v0) = alpha_vm * (1/3)(1-mu) + alpha_vm * mu/3
    #              + (1-alpha_vm) * [(1-mu)*delta(v,v0) + mu/3]
    #              = alpha_vm/3 + (1-alpha_vm)[(1-mu)*delta(v,v0) + mu/3]
    #              = (alpha_vm + (1-alpha_vm)*mu)/3 + (1-alpha_vm)(1-mu)*delta(v,v0)*(1 - 1/3... wait

    # Let me redo this carefully
    # P(v|v0) = [alpha_vm * 1/3 + (1-alpha_vm) * delta(v,v0)] * (1-mu) + mu/3
    #
    # For v = target value (not v0):
    # P(target|v0) = [alpha_vm/3 + 0] * (1-mu) + mu/3
    #              = alpha_vm*(1-mu)/3 + mu/3
    #              = (alpha_vm*(1-mu) + mu)/3
    #              = (alpha_vm + mu - alpha_vm*mu)/3
    #
    # For v = v0:
    # P(v0|v0) = [alpha_vm/3 + (1-alpha_vm)] * (1-mu) + mu/3
    #          = [(1 - 2*alpha_vm/3)] * (1-mu) + mu/3

    # The "memory" of v0 after one epoch is:
    # P(v0|v0) - 1/3 = [(1 - 2*alpha_vm/3)(1-mu) + mu/3] - 1/3
    #                = (1-mu) - 2*alpha_vm*(1-mu)/3 + mu/3 - 1/3
    #                = (1 - mu - 2*alpha_vm*(1-mu)/3 + mu/3 - 1/3)
    #                = (2/3 - 2mu/3 - 2*alpha_vm*(1-mu)/3)
    #                = (2/3)(1 - mu - alpha_vm*(1-mu))
    #                = (2/3)(1 - mu)(1 - alpha_vm)

    # So the contraction factor per epoch is:
    rho_eff = (1 - mu) * (1 - alpha_vm)
    rho_mut = (1 - mu)

    # After k epochs, the deviation from uniform is:
    # |P_k(v) - 1/3| <= (2/3) * rho_eff^k

    # Mixing time: set rho_eff^tau <= e^{-3}
    if rho_eff > 0 and rho_eff < 1:
        tau_mix_eff = math.ceil(-3 / math.log(rho_eff))
    else:
        tau_mix_eff = 1

    # q_min with enhanced mixing
    # After tau_mix_eff epochs, each trit is within delta of uniform
    delta_eff = rho_eff ** tau_mix_eff
    q_min_eff = (1/3 - delta_eff) ** L

    # Bounds
    results = {
        "parameters": {
            "L": L, "r": r, "mu": mu, "alpha_vm": alpha_vm,
        },

        "mutation_only": {
            "rho": rho_mut,
            "tau_mix": tau_mix_mut,
            "q_min": q_min_mut,
            "r_q_min": r * q_min_mut,
            "inv_r_q_min": 1 / (r * q_min_mut),
        },

        "vm_enhanced": {
            "rho_eff": rho_eff,
            "tau_mix_eff": tau_mix_eff,
            "q_min_eff": q_min_eff,
            "r_q_min_eff": r * q_min_eff,
            "inv_r_q_min_eff": 1 / (r * q_min_eff) if r * q_min_eff > 0 else float('inf'),
        },

        "improvement_factor": {
            "mixing_time_ratio": tau_mix_mut / tau_mix_eff if tau_mix_eff > 0 else float('inf'),
            "q_min_ratio": q_min_eff / q_min_mut if q_min_mut > 0 else float('inf'),
            "rho_ratio": rho_eff / rho_mut if rho_mut > 0 else 0,
        },
    }

    # Compute N0 and T0 for epsilon = 0.01
    eps = 0.01
    ln_inv_eps = math.log(1 / eps)

    # Mutation-only bounds
    T_test = 1_000_000
    K_mut = T_test // tau_mix_mut
    N0_mut = ln_inv_eps / (r * q_min_mut * max(K_mut, 1))
    T0_mut_N1666 = tau_mix_mut * ln_inv_eps / (r * q_min_mut * 1666)

    # VM-enhanced bounds
    K_eff = T_test // tau_mix_eff if tau_mix_eff > 0 else T_test
    N0_eff = ln_inv_eps / (r * q_min_eff * max(K_eff, 1))
    T0_eff_N1666 = tau_mix_eff * ln_inv_eps / (r * q_min_eff * 1666)

    results["bounds_eps_0.01"] = {
        "mutation_only": {
            "N0_at_T1M": N0_mut,
            "T0_at_N1666": T0_mut_N1666,
        },
        "vm_enhanced": {
            "N0_at_T1M": N0_eff,
            "T0_at_N1666": T0_eff_N1666,
        },
        "improvement": {
            "N0_ratio": N0_mut / N0_eff if N0_eff > 0 else float('inf'),
            "T0_ratio": T0_mut_N1666 / T0_eff_N1666 if T0_eff_N1666 > 0 else float('inf'),
        },
    }

    return results


# ==============================================================================
# ENUMERATE KNOWN REPLICATORS (from Phase 1 data)
# ==============================================================================

def find_replicators_exhaustive(L=24, max_steps=729, n_samples=10_000_000, rng=None):
    """Search for replicators by random sampling.

    This is NOT exhaustive (3^24 ≈ 2.8×10^11 programs), but samples
    randomly to estimate the density of replicators in program space.
    """
    if rng is None:
        rng = np.random.default_rng(789)

    replicators = set()
    trivial = set()

    t0 = time.time()
    report_interval = max(n_samples // 10, 1)

    for i in range(n_samples):
        prog = rng.integers(0, 3, size=L).tolist()
        if is_replicator(prog, max_steps):
            key = tuple(prog)
            if is_trivial(prog):
                trivial.add(key)
            else:
                replicators.add(key)

        if (i + 1) % report_interval == 0:
            elapsed = time.time() - t0
            print(f"  Sampled {i+1}/{n_samples} ({(i+1)/elapsed:.0f}/s), "
                  f"found {len(replicators)} nontrivial + {len(trivial)} trivial")

    return {
        "n_samples": n_samples,
        "nontrivial_count": len(replicators),
        "trivial_count": len(trivial),
        "density_estimate": len(replicators) / n_samples,
        "replicators": [list(r) for r in sorted(replicators)],
        "elapsed_seconds": time.time() - t0,
    }


# ==============================================================================
# MAIN
# ==============================================================================

def main():
    print("=" * 70)
    print("Lemma 0.0.XXe-NP: VM Contribution to Nucleation")
    print("Monte Carlo Estimation")
    print("=" * 70)

    results = {
        "title": "VM Contribution to Nucleation — Monte Carlo Estimation",
        "timestamp": datetime.now().isoformat(),
        "sections": {},
    }

    # ------------------------------------------------------------------
    # 1. Search for replicators to validate r ≈ 120
    # ------------------------------------------------------------------
    print("\n--- Section 1: Replicator Census (random sampling) ---")
    rep_results = find_replicators_exhaustive(n_samples=5_000_000)
    results["sections"]["replicator_census"] = rep_results
    print(f"  Found {rep_results['nontrivial_count']} nontrivial replicators "
          f"in {rep_results['n_samples']} samples")
    print(f"  Density estimate: {rep_results['density_estimate']:.2e}")
    if rep_results['nontrivial_count'] > 0:
        r_estimate = rep_results['density_estimate'] * 3**24
        print(f"  Estimated total r = density × 3^24 = {r_estimate:.0f}")

    # ------------------------------------------------------------------
    # 2. Estimate p_VM (per-interaction replicator generation probability)
    # ------------------------------------------------------------------
    print("\n--- Section 2: p_VM Estimation (VM + replicator check) ---")
    pvm_results = estimate_p_vm(n_trials=2_000_000, verbose=True)
    results["sections"]["p_vm_estimation"] = pvm_results
    print(f"\n  p_VM estimate: {pvm_results['p_vm_estimate']:.2e}")
    print(f"  Nontrivial replicators from VM: {pvm_results['nontrivial_replicators_found']}")
    print(f"  Mean Hamming distance (A→A'): {pvm_results['hamming_A_mean']:.2f} / 24")
    print(f"  Mean Hamming distance (B→B'): {pvm_results['hamming_B_mean']:.2f} / 24")
    print(f"  Per-trit scrambling rate (A): {pvm_results['alpha_A_mean']:.4f}")
    print(f"  Per-trit scrambling rate (B): {pvm_results['alpha_B_mean']:.4f}")
    print(f"  Fraction of interactions with NO change to A: "
          f"{pvm_results['hamming_A_zero_frac']:.4f}")

    # ------------------------------------------------------------------
    # 3. Per-trit scrambling analysis
    # ------------------------------------------------------------------
    print("\n--- Section 3: Per-Trit Scrambling Analysis ---")
    trit_results = estimate_per_trit_scrambling(n_trials=500_000)
    results["sections"]["per_trit_scrambling"] = trit_results
    print(f"  Per-trit scrambling rate (A, mean): {trit_results['alpha_A_mean']:.4f}")
    print(f"  Per-trit scrambling rate (B, mean): {trit_results['alpha_B_mean']:.4f}")
    print(f"  Per-trit rates (A): ", end="")
    print(" ".join(f"{x:.3f}" for x in trit_results['alpha_A_per_trit']))
    print(f"  Per-trit rates (B): ", end="")
    print(" ".join(f"{x:.3f}" for x in trit_results['alpha_B_per_trit']))

    # ------------------------------------------------------------------
    # 4. VM output distribution analysis
    # ------------------------------------------------------------------
    print("\n--- Section 4: VM Output Distribution Analysis ---")
    dist_results = analyze_vm_output_distribution(n_trials=500_000)
    results["sections"]["output_distribution"] = dist_results
    print(f"  Output entropy (A, mean): {dist_results['entropy_A_mean']:.4f} "
          f"(max = {dist_results['max_entropy']:.4f})")
    print(f"  Output entropy (B, mean): {dist_results['entropy_B_mean']:.4f}")
    print(f"  TV distance from uniform (A, mean): {dist_results['tv_A_mean']:.4f}")
    print(f"  TV distance from uniform (B, mean): {dist_results['tv_B_mean']:.4f}")

    # ------------------------------------------------------------------
    # 5. Compute tightened bounds
    # ------------------------------------------------------------------
    print("\n--- Section 5: Tightened Nucleation Bounds ---")
    alpha_vm = pvm_results['alpha_combined_mean']
    bounds = compute_tightened_bounds(alpha_vm=alpha_vm)
    results["sections"]["tightened_bounds"] = bounds

    print(f"\n  Mutation-only parameters:")
    print(f"    rho = {bounds['mutation_only']['rho']:.6f}")
    print(f"    tau_mix = {bounds['mutation_only']['tau_mix']}")
    print(f"    q_min = {bounds['mutation_only']['q_min']:.4e}")
    print(f"    1/(r·q_min) = {bounds['mutation_only']['inv_r_q_min']:.4e}")

    print(f"\n  VM-enhanced parameters:")
    print(f"    rho_eff = {bounds['vm_enhanced']['rho_eff']:.6f}")
    print(f"    tau_mix_eff = {bounds['vm_enhanced']['tau_mix_eff']}")
    print(f"    q_min_eff = {bounds['vm_enhanced']['q_min_eff']:.4e}")
    print(f"    1/(r·q_min_eff) = {bounds['vm_enhanced']['inv_r_q_min_eff']:.4e}")

    print(f"\n  Improvement factors:")
    print(f"    Mixing time reduction: {bounds['improvement_factor']['mixing_time_ratio']:.1f}×")
    print(f"    q_min improvement: {bounds['improvement_factor']['q_min_ratio']:.2e}×")
    print(f"    Contraction rate ratio: {bounds['improvement_factor']['rho_ratio']:.6f}")

    print(f"\n  Bounds for 99% nucleation (epsilon = 0.01):")
    b = bounds['bounds_eps_0.01']
    print(f"    Mutation-only: N0(T=10^6) = {b['mutation_only']['N0_at_T1M']:.2e}, "
          f"T0(N=1666) = {b['mutation_only']['T0_at_N1666']:.2e}")
    print(f"    VM-enhanced:   N0(T=10^6) = {b['vm_enhanced']['N0_at_T1M']:.2e}, "
          f"T0(N=1666) = {b['vm_enhanced']['T0_at_N1666']:.2e}")
    print(f"    N0 improvement: {b['improvement']['N0_ratio']:.1f}×")
    print(f"    T0 improvement: {b['improvement']['T0_ratio']:.1f}×")

    # Comparison with Phase 1 observed values
    print(f"\n  Comparison with Phase 1 observations:")
    print(f"    Observed T_emerge (n100 local): ~800,000 epochs")
    print(f"    VM-enhanced T0 (N=1666): {b['vm_enhanced']['T0_at_N1666']:.2e} epochs")
    remaining_gap = b['vm_enhanced']['T0_at_N1666'] / 800_000
    print(f"    Remaining gap: {remaining_gap:.1f}× "
          f"(down from ~{b['mutation_only']['T0_at_N1666']/800_000:.1f}×)")

    # ------------------------------------------------------------------
    # Save results
    # ------------------------------------------------------------------
    outpath = "lemma_0_0_XXe_NP_vm_contribution_results.json"
    with open(outpath, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to {outpath}")

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"  VM per-trit scrambling rate: alpha_VM = {alpha_vm:.4f}")
    print(f"  VM interaction changes ~{alpha_vm*24:.1f} trits per tile on average")
    print(f"  Effective contraction: rho_eff = {bounds['vm_enhanced']['rho_eff']:.6f} "
          f"(vs rho_mut = {bounds['mutation_only']['rho']:.6f})")
    print(f"  Mixing time: {bounds['vm_enhanced']['tau_mix_eff']} epochs "
          f"(vs {bounds['mutation_only']['tau_mix']} mutation-only)")
    print(f"  Gap to observation narrowed from ~10^6 to ~{remaining_gap:.0e}")

    return results


if __name__ == "__main__":
    main()
