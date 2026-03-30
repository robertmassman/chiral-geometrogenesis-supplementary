#!/usr/bin/env python3
"""
Phase B: Z₃ Color Crystallization

Can two-component Z₃ interactions crystallize the stella octangula geometry?

Setup:
  - 8 points on the unit sphere, 4 labeled A ("T₊") and 4 labeled B ("T₋")
  - Energy: E = α·Σ_{same} 1/d² + β·Σ_{cross} 1/d²
  - Simulated annealing minimizes E by moving points on the sphere

Prediction:
  - α/β = 1 (Thomson problem): equilibrium is square antiprism (not stella)
  - α/β >> 1: same-component repulsion forces each group into a regular
    tetrahedron (Z₃ 3-fold axes). Cross-component repulsion orients the two
    tetrahedra into the stella configuration (maximizes min cross distance).

The Z₃ connection: the regular tetrahedron IS the equilibrium of 4 repelling
points on a sphere, and its symmetry group A₄ contains Z₃. Two tetrahedra
with asymmetric interactions → stella octangula.

Usage:
  python3 run_phase_b.py [--quick] [--seed N]
"""

import numpy as np
from itertools import permutations
import json
import os
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

# ── Stella reference geometry ─────────────────────────────────────────

def stella_vertices():
    """Return stella octangula vertices on unit sphere."""
    s = 1.0 / np.sqrt(3.0)
    tp = np.array([[ s, s, s], [ s,-s,-s], [-s, s,-s], [-s,-s, s]])
    tm = -tp
    return tp, tm


def all_tet_distances(pts):
    """Pairwise distances for 4 points. Returns sorted array of 6 values."""
    dists = []
    for i in range(4):
        for j in range(i+1, 4):
            dists.append(np.linalg.norm(pts[i] - pts[j]))
    return np.sort(dists)


def tetrahedral_quality(pts):
    """How regular is a 4-point configuration?
    1.0 = perfect regular tetrahedron (all 6 distances equal).
    Uses 1 - CV(distances)."""
    dists = all_tet_distances(pts)
    if dists.mean() < 1e-10:
        return 0.0
    cv = dists.std() / dists.mean()
    return max(0.0, 1.0 - cv)


# ── Stella-likeness via Procrustes RMSD ───────────────────────────────

def kabsch_rmsd(P, Q):
    """Compute RMSD between point sets P and Q after optimal rotation.
    P, Q: (n, 3) arrays, already centered."""
    H = P.T @ Q
    U, S, Vt = np.linalg.svd(H)
    d = np.linalg.det(Vt.T @ U.T)
    sign_matrix = np.diag([1, 1, np.sign(d)])
    R = Vt.T @ sign_matrix @ U.T
    P_rot = P @ R.T
    return np.sqrt(np.mean(np.sum((P_rot - Q)**2, axis=1)))


def stella_rmsd(group_a, group_b):
    """Find best RMSD of (group_a, group_b) to stella (T₊, T₋).
    Tries all 24 permutations of matching group_a to T₊ vertices,
    and both A→T₊/B→T₋ and A→T₋/B→T₊ assignments."""
    tp, tm = stella_vertices()
    all_points = np.vstack([group_a, group_b])
    center = all_points.mean(axis=0)
    all_centered = all_points - center

    stella_all = np.vstack([tp, tm])
    stella_center = stella_all.mean(axis=0)
    stella_centered = stella_all - stella_center

    best_rmsd = 1e10
    perms_4 = list(permutations(range(4)))

    for swap in [False, True]:
        for perm_a in perms_4:
            # Match group_a to T₊ (or T₋ if swapped) using this permutation
            if swap:
                target_a = tm[list(perm_a)]
                target_b_base = tp
            else:
                target_a = tp[list(perm_a)]
                target_b_base = tm

            # For each perm of group_a, find best perm for group_b
            for perm_b in perms_4:
                target_b = target_b_base[list(perm_b)]
                target = np.vstack([target_a, target_b]) - stella_center

                rmsd = kabsch_rmsd(all_centered, target)
                if rmsd < best_rmsd:
                    best_rmsd = rmsd

    return best_rmsd


def cross_distance_pattern(group_a, group_b):
    """Compute cross-component distance statistics.
    For the stella: 12 distances at d_near ≈ 1.155, 4 at d_far = 2.0 (unit sphere).
    Returns (min_d, max_d, ratio, sorted_distances)."""
    dists = []
    for i in range(len(group_a)):
        for j in range(len(group_b)):
            dists.append(np.linalg.norm(group_a[i] - group_b[j]))
    dists = np.sort(dists)
    ratio = dists[-1] / dists[0] if dists[0] > 1e-10 else float('inf')
    return dists[0], dists[-1], ratio, dists


# ── Energy function ───────────────────────────────────────────────────

def compute_energy(points, labels, alpha, beta):
    """E = α·Σ_{same label} 1/d² + β·Σ_{cross label} 1/d²"""
    n = len(points)
    energy = 0.0
    for i in range(n):
        for j in range(i+1, n):
            d2 = np.sum((points[i] - points[j])**2)
            if d2 < 1e-12:
                return 1e15  # avoid singularity
            if labels[i] == labels[j]:
                energy += alpha / d2
            else:
                energy += beta / d2
    return energy


# ── Simulated annealing ──────────────────────────────────────────────

def random_sphere_point(rng):
    """Generate a random unit vector (uniform on sphere)."""
    z = rng.uniform(-1, 1)
    phi = rng.uniform(0, 2 * np.pi)
    r = np.sqrt(1 - z*z)
    return np.array([r * np.cos(phi), r * np.sin(phi), z])


def perturb_on_sphere(point, step_size, rng):
    """Perturb a point on the unit sphere by a small displacement."""
    perturbation = rng.normal(0, step_size, 3)
    new_point = point + perturbation
    norm = np.linalg.norm(new_point)
    if norm < 1e-10:
        return point.copy()
    return new_point / norm


def anneal(n_points, labels, alpha, beta, n_steps=500_000,
           T_init=2.0, T_final=0.001, seed=42, verbose=False):
    """Simulated annealing on the unit sphere."""
    rng = np.random.RandomState(seed)

    # Initialize random points on sphere
    points = np.array([random_sphere_point(rng) for _ in range(n_points)])

    energy = compute_energy(points, labels, alpha, beta)
    best_points = points.copy()
    best_energy = energy

    # Cooling rate
    cool_rate = (T_final / T_init) ** (1.0 / n_steps)
    T = T_init
    accepted = 0

    for step in range(n_steps):
        # Pick random point to move
        idx = rng.randint(n_points)
        step_size = 0.3 * np.sqrt(T / T_init)  # adaptive step

        old_pos = points[idx].copy()
        points[idx] = perturb_on_sphere(old_pos, step_size, rng)

        new_energy = compute_energy(points, labels, alpha, beta)
        dE = new_energy - energy

        # Metropolis acceptance
        if dE < 0 or rng.random() < np.exp(-dE / T):
            energy = new_energy
            accepted += 1
            if energy < best_energy:
                best_energy = energy
                best_points = points.copy()
        else:
            points[idx] = old_pos

        T *= cool_rate

        if verbose and (step + 1) % (n_steps // 5) == 0:
            print(f"  step={step+1:,}  T={T:.4f}  E={energy:.4f}  "
                  f"best_E={best_energy:.4f}  accept={accepted/(step+1):.2f}")

    return best_points, best_energy, accepted / n_steps


# ── Analysis ──────────────────────────────────────────────────────────

def analyze_result(points, labels, alpha, beta, seed):
    """Compute all metrics for an annealing result."""
    group_a = points[labels == 0]
    group_b = points[labels == 1]

    tet_q_a = tetrahedral_quality(group_a)
    tet_q_b = tetrahedral_quality(group_b)
    rmsd = stella_rmsd(group_a, group_b)
    d_min, d_max, d_ratio, cross_dists = cross_distance_pattern(group_a, group_b)

    # Stella reference values (unit sphere)
    # d_near = 2/√3 ≈ 1.1547, d_far = 2.0, ratio = √3 ≈ 1.732
    stella_ratio = np.sqrt(3.0)

    # Same-component distance uniformity
    dists_a = all_tet_distances(group_a)
    dists_b = all_tet_distances(group_b)

    return {
        'alpha': alpha,
        'beta': beta,
        'ratio': alpha / beta if beta > 0 else float('inf'),
        'seed': seed,
        'energy': compute_energy(points, labels, alpha, beta),
        'tet_quality_a': tet_q_a,
        'tet_quality_b': tet_q_b,
        'tet_quality_avg': (tet_q_a + tet_q_b) / 2,
        'stella_rmsd': rmsd,
        'cross_d_min': d_min,
        'cross_d_max': d_max,
        'cross_d_ratio': d_ratio,
        'stella_ratio_err': abs(d_ratio - stella_ratio) / stella_ratio,
        'intra_a_mean': dists_a.mean(),
        'intra_b_mean': dists_b.mean(),
        'intra_a_std': dists_a.std(),
        'intra_b_std': dists_b.std(),
    }


# ── Main experiments ──────────────────────────────────────────────────

def run_ratio_sweep(n_steps, seeds):
    """Sweep α/β ratio to find transition from antiprism to stella."""
    ratios = [1.0, 1.5, 2.0, 3.0, 5.0, 7.0, 10.0, 15.0, 20.0, 50.0, 100.0]
    labels = np.array([0, 0, 0, 0, 1, 1, 1, 1])

    print("=" * 70)
    print("EXPERIMENT B1: α/β Ratio Sweep")
    print("  α/β = 1: Thomson problem (no component preference)")
    print("  α/β >> 1: strong same-component repulsion → tetrahedra → stella?")
    print("=" * 70)

    all_results = []

    for ratio in ratios:
        alpha = ratio
        beta = 1.0
        print(f"\n--- α/β = {ratio:.1f} ---")

        seed_results = []
        for seed in seeds:
            points, energy, accept_rate = anneal(
                8, labels, alpha, beta,
                n_steps=n_steps, seed=seed, verbose=False
            )
            result = analyze_result(points, labels, alpha, beta, seed)
            result['accept_rate'] = accept_rate
            result['points'] = points.tolist()
            seed_results.append(result)

        # Average over seeds
        avg = {
            'ratio': ratio,
            'tet_quality': np.mean([r['tet_quality_avg'] for r in seed_results]),
            'stella_rmsd': np.mean([r['stella_rmsd'] for r in seed_results]),
            'cross_d_ratio': np.mean([r['cross_d_ratio'] for r in seed_results]),
            'stella_ratio_err': np.mean([r['stella_ratio_err'] for r in seed_results]),
            'intra_std': np.mean([r['intra_a_std'] + r['intra_b_std']
                                  for r in seed_results]) / 2,
            'seeds': seed_results,
        }
        all_results.append(avg)

        print(f"  tet_quality={avg['tet_quality']:.4f}  "
              f"stella_rmsd={avg['stella_rmsd']:.4f}  "
              f"d_ratio={avg['cross_d_ratio']:.3f} (stella=1.732)  "
              f"intra_std={avg['intra_std']:.4f}")

    return all_results


def run_seed_study(n_steps, alpha_beta_ratio, n_seeds=20):
    """Run many seeds at a specific α/β ratio to test robustness."""
    labels = np.array([0, 0, 0, 0, 1, 1, 1, 1])
    alpha = alpha_beta_ratio
    beta = 1.0

    print(f"\n{'=' * 70}")
    print(f"EXPERIMENT B2: Seed Robustness (α/β = {alpha_beta_ratio}, {n_seeds} seeds)")
    print(f"{'=' * 70}")

    results = []
    for seed in range(n_seeds):
        points, energy, accept_rate = anneal(
            8, labels, alpha, beta,
            n_steps=n_steps, seed=seed + 1000, verbose=False
        )
        result = analyze_result(points, labels, alpha, beta, seed + 1000)
        results.append(result)

    rmsds = [r['stella_rmsd'] for r in results]
    tet_qs = [r['tet_quality_avg'] for r in results]
    d_ratios = [r['cross_d_ratio'] for r in results]

    print(f"\n  Over {n_seeds} seeds:")
    print(f"  Stella RMSD:    {np.mean(rmsds):.4f} ± {np.std(rmsds):.4f}  "
          f"(min={np.min(rmsds):.4f}, max={np.max(rmsds):.4f})")
    print(f"  Tet quality:    {np.mean(tet_qs):.4f} ± {np.std(tet_qs):.4f}")
    print(f"  Cross d ratio:  {np.mean(d_ratios):.3f} ± {np.std(d_ratios):.3f}  "
          f"(stella = 1.732)")

    converged = sum(1 for r in rmsds if r < 0.05)
    print(f"  Converged to stella (RMSD < 0.05): {converged}/{n_seeds} "
          f"({100*converged/n_seeds:.0f}%)")

    return results


def print_results_table(results):
    """Print ratio sweep as markdown table."""
    print("\n## α/β Ratio Sweep Results")
    print()
    print("| α/β | tet_quality | stella_RMSD | cross_d_ratio | "
          "stella_ratio_err | intra_std |")
    print("|:---:|:----------:|:-----------:|:-------------:|"
          ":----------------:|:---------:|")

    for r in results:
        print(f"| {r['ratio']:5.1f} | {r['tet_quality']:.4f} | "
              f"{r['stella_rmsd']:.4f} | {r['cross_d_ratio']:.3f} | "
              f"{r['stella_ratio_err']:.4f} | {r['intra_std']:.4f} |")

    # Find transition point
    for i, r in enumerate(results):
        if r['stella_rmsd'] < 0.05:
            print(f"\n**Stella crystallization threshold: α/β ≈ {r['ratio']:.1f}**")
            print(f"  (RMSD drops below 0.05 — configuration is stella)")
            break
    else:
        best = min(results, key=lambda r: r['stella_rmsd'])
        print(f"\n**Best RMSD = {best['stella_rmsd']:.4f} at α/β = {best['ratio']:.1f}**")

    # Stella reference
    print(f"\nStella reference: cross_d_ratio = √3 ≈ 1.732, "
          f"tet_quality = 1.000, RMSD = 0.000")
    print(f"Thomson (α/β=1): expected square antiprism (RMSD >> 0)")


def print_analysis(sweep_results, seed_results):
    """Print analysis section."""
    print("\n## Analysis")

    # Thomson vs stella comparison
    thomson = sweep_results[0]  # α/β = 1
    best = min(sweep_results, key=lambda r: r['stella_rmsd'])

    print(f"\n### Thomson (α/β=1) vs Best Stella")
    print(f"  Thomson:  tet_quality={thomson['tet_quality']:.4f}, "
          f"RMSD={thomson['stella_rmsd']:.4f}")
    print(f"  Best:     tet_quality={best['tet_quality']:.4f}, "
          f"RMSD={best['stella_rmsd']:.4f}  (α/β={best['ratio']:.1f})")

    print(f"\n### Key Findings")
    print()

    # Check if there's a clear transition
    threshold_found = False
    for r in sweep_results:
        if r['stella_rmsd'] < 0.05:
            print(f"1. **Stella crystallization occurs at α/β ≥ {r['ratio']:.1f}.**")
            print(f"   When same-component repulsion is {r['ratio']:.0f}× stronger than")
            print(f"   cross-component, the 8 points spontaneously form the stella.")
            threshold_found = True
            break

    if not threshold_found:
        print(f"1. **No clean stella crystallization observed.**")
        print(f"   Best RMSD = {best['stella_rmsd']:.4f} at α/β = {best['ratio']:.1f}.")

    # Tetrahedral quality
    high_tet = [r for r in sweep_results if r['tet_quality'] > 0.99]
    if high_tet:
        print(f"\n2. **Perfect tetrahedra form at α/β ≥ {high_tet[0]['ratio']:.1f}.**")
        print(f"   Tetrahedral quality > 0.99 (all intra-group distances equal).")
    else:
        best_tet = max(sweep_results, key=lambda r: r['tet_quality'])
        print(f"\n2. **Best tetrahedral quality: {best_tet['tet_quality']:.4f} "
              f"at α/β = {best_tet['ratio']:.1f}.**")

    # Cross-distance ratio
    stella_ratio = np.sqrt(3)
    close_ratio = [r for r in sweep_results
                   if abs(r['cross_d_ratio'] - stella_ratio) / stella_ratio < 0.05]
    if close_ratio:
        print(f"\n3. **Cross-distance ratio matches stella (√3 ≈ 1.732) at "
              f"α/β ≥ {close_ratio[0]['ratio']:.1f}.**")
        print(f"   The characteristic 12-near / 4-far distance pattern emerges.")

    # Seed robustness
    if seed_results:
        rmsds = [r['stella_rmsd'] for r in seed_results]
        converged = sum(1 for r in rmsds if r < 0.05)
        total = len(seed_results)
        print(f"\n4. **Seed robustness: {converged}/{total} seeds converge "
              f"to stella ({100*converged/total:.0f}%).**")
        if converged < total:
            print(f"   Some seeds find local minima (other polyhedra).")


def save_results(sweep_results, seed_results):
    """Save results to JSON (strip numpy arrays for JSON serialization)."""
    def clean(obj):
        if isinstance(obj, dict):
            return {k: clean(v) for k, v in obj.items()
                    if k != 'points'}  # skip raw point data for brevity
        if isinstance(obj, list):
            return [clean(v) for v in obj]
        if isinstance(obj, (np.floating, np.float64)):
            return float(obj)
        if isinstance(obj, (np.integer, np.int64)):
            return int(obj)
        return obj

    output = {
        "experiment": "Phase B: Z₃ Color Crystallization",
        "sweep": clean(sweep_results),
        "seed_study": clean(seed_results),
    }
    path = os.path.join(SCRIPT_DIR, "phase_b_results.json")
    with open(path, 'w') as f:
        json.dump(output, f, indent=2)
    print(f"\nResults saved to {path}")


# ── Main ──────────────────────────────────────────────────────────────

def main():
    quick = "--quick" in sys.argv
    seed_arg = None
    for i, arg in enumerate(sys.argv):
        if arg == "--seed" and i + 1 < len(sys.argv):
            seed_arg = int(sys.argv[i + 1])

    if quick:
        n_steps = 200_000
        seeds = [42, 137, 2718]
        n_seed_study = 10
        print(f"*** QUICK MODE: {n_steps:,} steps, {len(seeds)} seeds ***\n")
    else:
        n_steps = 500_000
        seeds = [42, 137, 2718, 31415, 99999]
        n_seed_study = 20
        print(f"Running with {n_steps:,} steps, {len(seeds)} seeds\n")

    # Experiment B1: ratio sweep
    sweep_results = run_ratio_sweep(n_steps, seeds)

    # Find best ratio for seed study
    best_ratio = min(sweep_results, key=lambda r: r['stella_rmsd'])['ratio']
    study_ratio = max(best_ratio, 10.0)  # at least 10

    # Experiment B2: seed robustness at best ratio
    seed_results = run_seed_study(n_steps, study_ratio, n_seed_study)

    # Print results
    print(f"\n{'=' * 70}")
    print("RESULTS")
    print(f"{'=' * 70}")
    print_results_table(sweep_results)
    print_analysis(sweep_results, seed_results)

    save_results(sweep_results, seed_results)


if __name__ == "__main__":
    main()
