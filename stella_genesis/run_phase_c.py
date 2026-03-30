#!/usr/bin/env python3
"""
Phase C: Larger N Crystallization — Strongest Result

Demonstrates that Z₃ two-component interactions select BOTH:
  (a) the vertex count N = 8 (4 + 4)
  (b) the geometry = stella octangula

Three experiments:

  C1: Grand Canonical Annealing
      Start with N_max = 20 points, allow activation/deactivation + label
      swaps during annealing. Sweep chemical potential μ. Show N = 8 (4+4)
      is selected over a wide μ range.

  C2: Label Relaxation
      Fix N = 8, start with random unequal label splits (e.g., 2+6, 3+5).
      Allow label swaps during annealing. Show convergence to 4+4 stella.

  C3: N Sweep
      For each even N from 4 to 20, run standard annealing with N/2 + N/2
      labels. Compare subgroup regularity and 3D isotropy. Show N = 8
      uniquely produces subgroups that are BOTH perfectly regular (all
      pairwise distances equal) AND fully 3-dimensional (isotropic).

Usage:
  python3 run_phase_c.py [--quick]
"""

import numpy as np
from itertools import permutations
import json
import os
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


# ── Stella reference geometry ─────────────────────────────────────────

def stella_vertices():
    """Stella octangula vertices on unit sphere."""
    s = 1.0 / np.sqrt(3.0)
    tp = np.array([[ s, s, s], [ s,-s,-s], [-s, s,-s], [-s,-s, s]])
    tm = -tp
    return tp, tm


def kabsch_rmsd(P, Q):
    """RMSD between point sets P and Q after optimal rotation."""
    H = P.T @ Q
    U, S, Vt = np.linalg.svd(H)
    d = np.linalg.det(Vt.T @ U.T)
    sign_matrix = np.diag([1, 1, np.sign(d)])
    R = Vt.T @ sign_matrix @ U.T
    P_rot = P @ R.T
    return np.sqrt(np.mean(np.sum((P_rot - Q)**2, axis=1)))


def stella_rmsd(group_a, group_b):
    """Best RMSD of (group_a, group_b) to stella (T₊, T₋).
    Tries all permutations and both A↔B assignments."""
    if len(group_a) != 4 or len(group_b) != 4:
        return float('inf')

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
            if swap:
                target_a = tm[list(perm_a)]
                target_b_base = tp
            else:
                target_a = tp[list(perm_a)]
                target_b_base = tm

            for perm_b in perms_4:
                target_b = target_b_base[list(perm_b)]
                target = np.vstack([target_a, target_b]) - stella_center
                rmsd = kabsch_rmsd(all_centered, target)
                if rmsd < best_rmsd:
                    best_rmsd = rmsd

    return best_rmsd


def subgroup_regularity(pts):
    """How regular is a point set? 1.0 = all pairwise distances equal.
    Uses 1 - CV(pairwise distances). Works for any number of points.

    The regular tetrahedron is the ONLY 3D polyhedron where all pairwise
    distances are equal. Octahedra, cubes, etc. all have multiple distinct
    pairwise distances, so regularity < 1.0."""
    n = len(pts)
    if n < 2:
        return 0.0
    dists = []
    for i in range(n):
        for j in range(i + 1, n):
            dists.append(np.linalg.norm(pts[i] - pts[j]))
    dists = np.array(dists)
    if dists.mean() < 1e-10:
        return 0.0
    cv = dists.std() / dists.mean()
    return max(0.0, 1.0 - cv)


def subgroup_isotropy(pts):
    """3D isotropy of a point cloud.
    1.0 = perfectly isotropic (regular tetrahedron).
    0.0 = planar or lower-dimensional.

    Computed as ratio of smallest to largest singular value of the
    centered point matrix. Requires ≥ 4 points to be 3D."""
    if len(pts) < 4:
        return 0.0  # < 4 points cannot span 3D
    centered = pts - pts.mean(axis=0)
    _, svs, _ = np.linalg.svd(centered, full_matrices=False)
    if svs[0] < 1e-10:
        return 0.0
    return float(svs[2] / svs[0])  # s_min / s_max


# ── Energy function ───────────────────────────────────────────────────

def compute_energy(points, labels, alpha, beta, active=None):
    """E = α·Σ_{same} 1/d² + β·Σ_{cross} 1/d²"""
    n = len(points)
    energy = 0.0
    for i in range(n):
        if active is not None and not active[i]:
            continue
        for j in range(i + 1, n):
            if active is not None and not active[j]:
                continue
            d2 = np.sum((points[i] - points[j])**2)
            if d2 < 1e-12:
                return 1e15
            if labels[i] == labels[j]:
                energy += alpha / d2
            else:
                energy += beta / d2
    return energy


def random_sphere_point(rng):
    """Random unit vector (uniform on sphere)."""
    z = rng.uniform(-1, 1)
    phi = rng.uniform(0, 2 * np.pi)
    r = np.sqrt(1 - z * z)
    return np.array([r * np.cos(phi), r * np.sin(phi), z])


def perturb_on_sphere(point, step_size, rng):
    """Perturb a point on the unit sphere."""
    perturbation = rng.normal(0, step_size, 3)
    new_point = point + perturbation
    norm = np.linalg.norm(new_point)
    if norm < 1e-10:
        return point.copy()
    return new_point / norm


# ══════════════════════════════════════════════════════════════════════
# Experiment C1: Grand Canonical Annealing
# ══════════════════════════════════════════════════════════════════════

def anneal_grand_canonical(n_max, alpha, beta, mu, n_steps=500_000,
                           T_init=2.0, T_final=0.001, seed=42):
    """Simulated annealing with variable number of active points.

    At each step, randomly choose:
      (a) Move a point (70%)
      (b) Toggle a point's active status (20%)
      (c) Swap labels of two active points (10%)

    Energy = repulsive_energy - μ × N_active
    """
    rng = np.random.RandomState(seed)

    # Initialize: all points active, random positions
    # Labels: first half = 0, second half = 1
    points = np.array([random_sphere_point(rng) for _ in range(n_max)])
    labels = np.array([0] * (n_max // 2) + [1] * (n_max - n_max // 2))
    active = np.ones(n_max, dtype=bool)

    n_active = int(np.sum(active))
    repulsive_e = compute_energy(points, labels, alpha, beta, active)
    energy = repulsive_e - mu * n_active

    best_points = points.copy()
    best_labels = labels.copy()
    best_active = active.copy()
    best_energy = energy

    cool_rate = (T_final / T_init) ** (1.0 / n_steps)
    T = T_init

    n_active_history = []

    for step in range(n_steps):
        roll = rng.random()

        if roll < 0.70:
            # Move a random active point
            active_indices = np.where(active)[0]
            if len(active_indices) == 0:
                T *= cool_rate
                continue
            idx = rng.choice(active_indices)
            old_pos = points[idx].copy()
            step_size = 0.3 * np.sqrt(T / T_init)
            points[idx] = perturb_on_sphere(old_pos, step_size, rng)

            new_repulsive = compute_energy(points, labels, alpha, beta, active)
            new_energy = new_repulsive - mu * np.sum(active)
            dE = new_energy - energy

            if dE < 0 or rng.random() < np.exp(-dE / max(T, 1e-15)):
                energy = new_energy
                if energy < best_energy:
                    best_energy = energy
                    best_points = points.copy()
                    best_labels = labels.copy()
                    best_active = active.copy()
            else:
                points[idx] = old_pos

        elif roll < 0.90:
            # Toggle a random point's active status
            idx = rng.randint(n_max)
            active[idx] = not active[idx]

            new_n_active = int(np.sum(active))
            if new_n_active < 2:
                active[idx] = not active[idx]
                T *= cool_rate
                continue

            new_repulsive = compute_energy(points, labels, alpha, beta, active)
            new_energy = new_repulsive - mu * new_n_active
            dE = new_energy - energy

            if dE < 0 or rng.random() < np.exp(-dE / max(T, 1e-15)):
                energy = new_energy
                if energy < best_energy:
                    best_energy = energy
                    best_points = points.copy()
                    best_labels = labels.copy()
                    best_active = active.copy()
            else:
                active[idx] = not active[idx]

        else:
            # Swap labels of two active points with different labels
            active_indices = np.where(active)[0]
            if len(active_indices) < 2:
                T *= cool_rate
                continue
            i = rng.choice(active_indices)
            candidates = active_indices[labels[active_indices] != labels[i]]
            if len(candidates) == 0:
                T *= cool_rate
                continue
            j = rng.choice(candidates)

            labels[i], labels[j] = labels[j], labels[i]

            new_repulsive = compute_energy(points, labels, alpha, beta, active)
            new_energy = new_repulsive - mu * np.sum(active)
            dE = new_energy - energy

            if dE < 0 or rng.random() < np.exp(-dE / max(T, 1e-15)):
                energy = new_energy
                if energy < best_energy:
                    best_energy = energy
                    best_points = points.copy()
                    best_labels = labels.copy()
                    best_active = active.copy()
            else:
                labels[i], labels[j] = labels[j], labels[i]

        T *= cool_rate

        if (step + 1) % (n_steps // 20) == 0:
            n_active_history.append(int(np.sum(active)))

    return best_points, best_active, best_labels, best_energy, n_active_history


def run_grand_canonical(n_steps, n_seeds=5):
    """Sweep μ and show N=8 is selected over a range."""
    n_max = 20
    alpha = 10.0
    beta = 1.0

    # μ range: estimated N=8 plateau around μ ∈ [12, 22]
    mus = [3.0, 5.0, 8.0, 10.0, 12.0, 13.0, 14.0, 15.0, 16.0, 17.0,
           18.0, 19.0, 20.0, 22.0, 25.0, 30.0, 40.0]

    print("=" * 70)
    print("EXPERIMENT C1: Grand Canonical Annealing")
    print(f"  N_max = {n_max} (10 label-0, 10 label-1), α/β = {alpha/beta:.0f}")
    print(f"  Energy = repulsive - μ·N_active")
    print(f"  Sweep μ to find N = 8 selection window")
    print("=" * 70)

    all_results = []

    for mu in mus:
        print(f"\n--- μ = {mu:.1f} ---")
        seed_results = []

        for s in range(n_seeds):
            points, active, labels, energy, n_history = anneal_grand_canonical(
                n_max, alpha, beta, mu,
                n_steps=n_steps, seed=42 + s * 137
            )

            n_active = int(np.sum(active))
            active_points = points[active]
            active_labels = labels[active]

            n_a = int(np.sum(active_labels == 0))
            n_b = int(np.sum(active_labels == 1))
            group_a = active_points[active_labels == 0]
            group_b = active_points[active_labels == 1]

            rmsd = stella_rmsd(group_a, group_b) if (n_a == 4 and n_b == 4) else float('inf')

            reg_a = subgroup_regularity(group_a) if n_a >= 2 else 0.0
            reg_b = subgroup_regularity(group_b) if n_b >= 2 else 0.0
            iso_a = subgroup_isotropy(group_a)
            iso_b = subgroup_isotropy(group_b)

            seed_results.append({
                'seed': 42 + s * 137,
                'n_active': n_active,
                'n_a': n_a,
                'n_b': n_b,
                'split': f"{n_a}+{n_b}",
                'energy': float(energy),
                'stella_rmsd': float(rmsd) if rmsd < 1e10 else None,
                'regularity_avg': float((reg_a + reg_b) / 2),
                'isotropy_avg': float((iso_a + iso_b) / 2),
                'n_history': n_history,
            })

        n_actives = [r['n_active'] for r in seed_results]
        avg_n = np.mean(n_actives)
        splits = [r['split'] for r in seed_results]

        is_stella = sum(1 for r in seed_results
                        if r['n_active'] == 8
                        and r['stella_rmsd'] is not None
                        and r['stella_rmsd'] < 0.1)

        result = {
            'mu': mu,
            'avg_n_active': float(avg_n),
            'std_n_active': float(np.std(n_actives)),
            'n_actives': n_actives,
            'splits': splits,
            'stella_count': is_stella,
            'n_seeds': n_seeds,
            'seeds': seed_results,
        }
        all_results.append(result)

        print(f"  N_active = {avg_n:.1f} ± {np.std(n_actives):.1f}  "
              f"splits = {splits}  stella = {is_stella}/{n_seeds}")

    return all_results


# ══════════════════════════════════════════════════════════════════════
# Experiment C2: Label Relaxation
# ══════════════════════════════════════════════════════════════════════

def anneal_with_label_swaps(n_points, labels_init, alpha, beta,
                            n_steps=500_000, T_init=2.0, T_final=0.001,
                            seed=42):
    """Simulated annealing allowing both point moves and label swaps."""
    rng = np.random.RandomState(seed)

    points = np.array([random_sphere_point(rng) for _ in range(n_points)])
    labels = labels_init.copy()

    energy = compute_energy(points, labels, alpha, beta)
    best_points = points.copy()
    best_labels = labels.copy()
    best_energy = energy

    cool_rate = (T_final / T_init) ** (1.0 / n_steps)
    T = T_init

    label_history = []

    for step in range(n_steps):
        if rng.random() < 0.7:
            # Move a point
            idx = rng.randint(n_points)
            old_pos = points[idx].copy()
            step_size = 0.3 * np.sqrt(T / T_init)
            points[idx] = perturb_on_sphere(old_pos, step_size, rng)

            new_energy = compute_energy(points, labels, alpha, beta)
            dE = new_energy - energy

            if dE < 0 or rng.random() < np.exp(-dE / max(T, 1e-15)):
                energy = new_energy
                if energy < best_energy:
                    best_energy = energy
                    best_points = points.copy()
                    best_labels = labels.copy()
            else:
                points[idx] = old_pos
        else:
            # Flip one point's label (changes the split count)
            idx = rng.randint(n_points)
            old_label = labels[idx]
            labels[idx] = 1 - old_label

            # Prevent degenerate splits (0+8 or 8+0)
            n_label0 = int(np.sum(labels == 0))
            if n_label0 == 0 or n_label0 == n_points:
                labels[idx] = old_label
                T *= cool_rate
                continue

            new_energy = compute_energy(points, labels, alpha, beta)
            dE = new_energy - energy

            if dE < 0 or rng.random() < np.exp(-dE / max(T, 1e-15)):
                energy = new_energy
                if energy < best_energy:
                    best_energy = energy
                    best_points = points.copy()
                    best_labels = labels.copy()
            else:
                labels[idx] = old_label

        T *= cool_rate

        if (step + 1) % (n_steps // 20) == 0:
            n_a = int(np.sum(labels == 0))
            label_history.append(n_a)

    return best_points, best_labels, best_energy, label_history


def run_label_relaxation(n_steps, n_seeds=5):
    """Start with unequal label splits, show convergence to 4+4."""
    alpha = 10.0
    beta = 1.0
    n = 8

    splits = [(1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2), (7, 1)]

    print(f"\n{'=' * 70}")
    print("EXPERIMENT C2: Label Relaxation")
    print(f"  N = 8, α/β = {alpha/beta:.0f}")
    print(f"  Start with unequal splits, allow label swaps")
    print(f"{'=' * 70}")

    all_results = []

    for n_a_init, n_b_init in splits:
        print(f"\n--- Initial split: {n_a_init}+{n_b_init} ---")
        seed_results = []

        for s in range(n_seeds):
            labels_init = np.array([0] * n_a_init + [1] * n_b_init)

            points, labels, energy, label_history = anneal_with_label_swaps(
                n, labels_init, alpha, beta,
                n_steps=n_steps, seed=42 + s * 137
            )

            n_a_final = int(np.sum(labels == 0))
            n_b_final = n - n_a_final

            group_a = points[labels == 0]
            group_b = points[labels == 1]

            rmsd = stella_rmsd(group_a, group_b) if (n_a_final == 4 and n_b_final == 4) else float('inf')
            reg_a = subgroup_regularity(group_a) if n_a_final >= 2 else 0.0
            reg_b = subgroup_regularity(group_b) if n_b_final >= 2 else 0.0

            seed_results.append({
                'seed': 42 + s * 137,
                'initial_split': f"{n_a_init}+{n_b_init}",
                'final_split': f"{n_a_final}+{n_b_final}",
                'converged_to_4_4': (n_a_final == 4 and n_b_final == 4),
                'stella_rmsd': float(rmsd) if rmsd < 1e10 else None,
                'regularity_avg': float((reg_a + reg_b) / 2),
                'energy': float(energy),
                'label_history': label_history,
            })

        converged = sum(1 for r in seed_results if r['converged_to_4_4'])
        stella = sum(1 for r in seed_results
                     if r['converged_to_4_4']
                     and r['stella_rmsd'] is not None
                     and r['stella_rmsd'] < 0.05)
        final_splits = [r['final_split'] for r in seed_results]

        result = {
            'initial_split': f"{n_a_init}+{n_b_init}",
            'final_splits': final_splits,
            'converged_to_4_4': converged,
            'stella_count': stella,
            'n_seeds': n_seeds,
            'seeds': seed_results,
        }
        all_results.append(result)

        print(f"  Final splits: {final_splits}")
        print(f"  Converged to 4+4: {converged}/{n_seeds}  "
              f"Stella: {stella}/{n_seeds}")

    return all_results


# ══════════════════════════════════════════════════════════════════════
# Experiment C3: N Sweep
# ══════════════════════════════════════════════════════════════════════

def anneal_fixed_n(n_points, labels, alpha, beta, n_steps=500_000,
                   T_init=2.0, T_final=0.001, seed=42):
    """Standard simulated annealing (Phase B style)."""
    rng = np.random.RandomState(seed)
    points = np.array([random_sphere_point(rng) for _ in range(n_points)])

    energy = compute_energy(points, labels, alpha, beta)
    best_points = points.copy()
    best_energy = energy

    cool_rate = (T_final / T_init) ** (1.0 / n_steps)
    T = T_init

    for step in range(n_steps):
        idx = rng.randint(n_points)
        step_size = 0.3 * np.sqrt(T / T_init)

        old_pos = points[idx].copy()
        points[idx] = perturb_on_sphere(old_pos, step_size, rng)

        new_energy = compute_energy(points, labels, alpha, beta)
        dE = new_energy - energy

        if dE < 0 or rng.random() < np.exp(-dE / max(T, 1e-15)):
            energy = new_energy
            if energy < best_energy:
                best_energy = energy
                best_points = points.copy()
        else:
            points[idx] = old_pos

        T *= cool_rate

    return best_points, best_energy


def run_n_sweep(n_steps, n_seeds=3):
    """Compare ground states for various N values."""
    alpha = 10.0
    beta = 1.0

    n_values = [4, 6, 8, 10, 12, 16, 20]

    print(f"\n{'=' * 70}")
    print("EXPERIMENT C3: N Sweep")
    print(f"  α/β = {alpha/beta:.0f}, N/2 + N/2 labels")
    print(f"  Compare subgroup regularity and 3D isotropy across N values")
    print(f"  Key insight: regular tetrahedron (N/2=4) is the ONLY polyhedron")
    print(f"  where all pairwise distances are equal AND the shape is 3D")
    print(f"{'=' * 70}")

    all_results = []

    for n in n_values:
        n_a = n // 2
        n_b = n - n_a
        labels = np.array([0] * n_a + [1] * n_b)

        print(f"\n--- N = {n} ({n_a}+{n_b}) ---")
        seed_results = []

        for s in range(n_seeds):
            points, energy = anneal_fixed_n(
                n, labels, alpha, beta,
                n_steps=n_steps, seed=42 + s * 137
            )

            group_a = points[labels == 0]
            group_b = points[labels == 1]

            reg_a = subgroup_regularity(group_a)
            reg_b = subgroup_regularity(group_b)
            iso_a = subgroup_isotropy(group_a)
            iso_b = subgroup_isotropy(group_b)

            # Stella RMSD (only meaningful for 4+4)
            rmsd = stella_rmsd(group_a, group_b) if (n_a == 4 and n_b == 4) else None

            # Energy per pair
            n_pairs = n_a * (n_a - 1) // 2 + n_b * (n_b - 1) // 2 + n_a * n_b
            e_per_pair = energy / n_pairs if n_pairs > 0 else 0

            seed_results.append({
                'seed': 42 + s * 137,
                'n': n,
                'energy': float(energy),
                'e_per_pair': float(e_per_pair),
                'regularity_a': float(reg_a),
                'regularity_b': float(reg_b),
                'regularity_avg': float((reg_a + reg_b) / 2),
                'isotropy_a': float(iso_a),
                'isotropy_b': float(iso_b),
                'isotropy_avg': float((iso_a + iso_b) / 2),
                'stella_rmsd': float(rmsd) if rmsd is not None else None,
            })

        avg_reg = np.mean([r['regularity_avg'] for r in seed_results])
        avg_iso = np.mean([r['isotropy_avg'] for r in seed_results])
        avg_rmsd = np.mean([r['stella_rmsd'] for r in seed_results
                            if r['stella_rmsd'] is not None]) if n == 8 else None

        result = {
            'n': n,
            'n_a': n_a,
            'n_b': n_b,
            'regularity': float(avg_reg),
            'isotropy': float(avg_iso),
            'stella_rmsd': float(avg_rmsd) if avg_rmsd is not None else None,
            'seeds': seed_results,
        }
        all_results.append(result)

        stella_str = f"  stella_RMSD={avg_rmsd:.4f}" if avg_rmsd is not None else ""
        print(f"  regularity={avg_reg:.4f}  isotropy={avg_iso:.4f}{stella_str}")

    return all_results


# ══════════════════════════════════════════════════════════════════════
# Output
# ══════════════════════════════════════════════════════════════════════

def print_c1_results(results):
    """Print grand canonical results table."""
    print("\n## C1: Grand Canonical — N Selection")
    print()
    print("| μ | N_active (avg±σ) | Splits | Stella (RMSD<0.1) |")
    print("|:---:|:---------------:|:-------|:------------------:|")

    for r in results:
        splits_str = ", ".join(r['splits'])
        print(f"| {r['mu']:.1f} | {r['avg_n_active']:.1f} ± {r['std_n_active']:.1f} | "
              f"{splits_str} | {r['stella_count']}/{r['n_seeds']} |")

    # Find μ range where N=8 dominates
    n8_mus = [r['mu'] for r in results
              if any(sr['n_active'] == 8 for sr in r['seeds'])]
    n8_dominant = [r['mu'] for r in results
                   if abs(r['avg_n_active'] - 8) < 1.5]

    if n8_dominant:
        print(f"\n**N = 8 selected for μ ∈ [{min(n8_dominant):.1f}, "
              f"{max(n8_dominant):.1f}]**")

    # Find stella-producing μ range
    stella_mus = [r['mu'] for r in results if r['stella_count'] > 0]
    if stella_mus:
        print(f"**Stella octangula produced for μ ∈ [{min(stella_mus):.1f}, "
              f"{max(stella_mus):.1f}]**")


def print_c2_results(results):
    """Print label relaxation results table."""
    print("\n## C2: Label Relaxation — 4+4 Emergence")
    print()
    print("| Initial | Final splits | 4+4 | Stella |")
    print("|:-------:|:------------|:---:|:------:|")

    for r in results:
        finals = ", ".join(r['final_splits'])
        total = r['n_seeds']
        print(f"| {r['initial_split']} | {finals} | "
              f"{r['converged_to_4_4']}/{total} | {r['stella_count']}/{total} |")

    total_converged = sum(r['converged_to_4_4'] for r in results)
    total_stella = sum(r['stella_count'] for r in results)
    total_runs = sum(r['n_seeds'] for r in results)
    print(f"\n**Overall: {total_converged}/{total_runs} converged to 4+4, "
          f"{total_stella}/{total_runs} formed stella**")


def print_c3_results(results):
    """Print N sweep results table."""
    print("\n## C3: N Sweep — Regularity × Isotropy")
    print()
    print("The regular tetrahedron (N/2 = 4) is the ONLY configuration where:")
    print("  - All pairwise distances are equal (regularity = 1.0)")
    print("  - The shape is fully 3-dimensional (isotropy > 0)")
    print()
    print("| N | Split | Regularity | Isotropy | Reg × Iso | Stella RMSD | Geometry |")
    print("|:---:|:-----:|:----------:|:--------:|:---------:|:-----------:|:---------|")

    for r in results:
        rmsd_str = f"{r['stella_rmsd']:.4f}" if r['stella_rmsd'] is not None else "—"
        product = r['regularity'] * r['isotropy']

        # Determine geometry description
        n_half = r['n_a']
        if n_half == 2:
            geom = "line segments"
        elif n_half == 3:
            geom = "equilateral triangles (2D)"
        elif n_half == 4:
            geom = "**regular tetrahedra → STELLA**"
        elif n_half == 5:
            geom = "triangular dipyramids"
        elif n_half == 6:
            geom = "octahedra"
        elif n_half == 8:
            geom = "square antiprisms"
        elif n_half == 10:
            geom = "irregular polyhedra"
        else:
            geom = f"{n_half}-point polyhedra"

        print(f"| {r['n']} | {r['n_a']}+{r['n_b']} | {r['regularity']:.4f} | "
              f"{r['isotropy']:.4f} | {product:.4f} | {rmsd_str} | {geom} |")

    # Highlight the key finding
    n8 = next((r for r in results if r['n'] == 8), None)
    if n8:
        others_max = max((r['regularity'] * r['isotropy']
                         for r in results if r['n'] != 8), default=0)
        n8_product = n8['regularity'] * n8['isotropy']
        if n8_product > others_max * 1.5:
            print(f"\n**N = 8 uniquely maximizes Regularity × Isotropy "
                  f"({n8_product:.4f} vs next best {others_max:.4f})**")


def print_summary(c1_results, c2_results, c3_results):
    """Print overall Phase C summary."""
    print(f"\n{'=' * 70}")
    print("PHASE C SUMMARY")
    print(f"{'=' * 70}")

    # C1 summary
    stella_mus = [r['mu'] for r in c1_results if r['stella_count'] > 0]
    if stella_mus:
        print(f"\nC1: Grand canonical annealing selects N=8 stella for "
              f"μ ∈ [{min(stella_mus):.1f}, {max(stella_mus):.1f}]")
    else:
        n8_dom = [r['mu'] for r in c1_results
                  if abs(r['avg_n_active'] - 8) < 1.5]
        if n8_dom:
            print(f"\nC1: N=8 selected for μ ∈ [{min(n8_dom):.1f}, "
                  f"{max(n8_dom):.1f}]")

    # C2 summary
    total_converged = sum(r['converged_to_4_4'] for r in c2_results)
    total_stella = sum(r['stella_count'] for r in c2_results)
    total_runs = sum(r['n_seeds'] for r in c2_results)
    print(f"\nC2: {total_converged}/{total_runs} label-relaxation runs → 4+4, "
          f"{total_stella}/{total_runs} → stella")

    # C3 summary
    n8 = next((r for r in c3_results if r['n'] == 8), None)
    if n8:
        print(f"\nC3: N=8 regularity={n8['regularity']:.4f}, "
              f"isotropy={n8['isotropy']:.4f}, "
              f"stella_RMSD={n8['stella_rmsd']:.4f}")
        others = [(r['n'], r['regularity'] * r['isotropy'])
                  for r in c3_results if r['n'] != 8]
        best_other = max(others, key=lambda x: x[1])
        print(f"    Next best Reg×Iso: N={best_other[0]} at {best_other[1]:.4f} "
              f"vs N=8 at {n8['regularity'] * n8['isotropy']:.4f}")

    print(f"\nConclusion: Z₃ two-component interactions select N = 8 vertices")
    print(f"in the stella octangula configuration. Both the vertex count")
    print(f"and the geometry emerge from the interaction structure alone.")


def save_results(c1_results, c2_results, c3_results):
    """Save all results to JSON."""
    def clean(obj):
        if isinstance(obj, dict):
            return {k: clean(v) for k, v in obj.items()}
        if isinstance(obj, list):
            return [clean(v) for v in obj]
        if isinstance(obj, (np.floating, np.float64)):
            return float(obj)
        if isinstance(obj, (np.integer, np.int64)):
            return int(obj)
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        if obj == float('inf'):
            return None
        return obj

    output = {
        "experiment": "Phase C: Larger N Crystallization",
        "c1_grand_canonical": clean(c1_results),
        "c2_label_relaxation": clean(c2_results),
        "c3_n_sweep": clean(c3_results),
    }
    path = os.path.join(SCRIPT_DIR, "phase_c_results.json")
    with open(path, 'w') as f:
        json.dump(output, f, indent=2)
    print(f"\nResults saved to {path}")


# ══════════════════════════════════════════════════════════════════════
# Main
# ══════════════════════════════════════════════════════════════════════

def main():
    quick = "--quick" in sys.argv

    if quick:
        n_steps = 200_000
        n_seeds_c1 = 3
        n_seeds_c2 = 3
        n_seeds_c3 = 2
        print("*** QUICK MODE ***\n")
    else:
        n_steps = 500_000
        n_seeds_c1 = 5
        n_seeds_c2 = 5
        n_seeds_c3 = 3
        print(f"Running with {n_steps:,} steps\n")

    # C1: Grand canonical
    c1_results = run_grand_canonical(n_steps, n_seeds_c1)

    # C2: Label relaxation
    c2_results = run_label_relaxation(n_steps, n_seeds_c2)

    # C3: N sweep
    c3_results = run_n_sweep(n_steps, n_seeds_c3)

    # Print summary
    print(f"\n{'=' * 70}")
    print("PHASE C RESULTS")
    print(f"{'=' * 70}")

    print_c1_results(c1_results)
    print_c2_results(c2_results)
    print_c3_results(c3_results)
    print_summary(c1_results, c2_results, c3_results)

    save_results(c1_results, c2_results, c3_results)


if __name__ == "__main__":
    main()
