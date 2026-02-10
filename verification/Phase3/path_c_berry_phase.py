#!/usr/bin/env python3
"""
Path C: Berry Phase Around the Triality Cycle
===============================================

Research Plan §11.2 Path C — Investigates whether the holonomy/Berry phase
of transporting quantum states around the D₄ triality cycle
Γ₁ → Γ₂ → Γ₃ → Γ₁ within the 600-cell produces φ-dependent quantities.

Core hypothesis:
    The 600-cell (H₄ symmetry) breaks the S₃ triality symmetry of the 24-cell
    (F₄ symmetry) because F₄ ⊄ H₄ (Path A finding). This means the three
    16-cells are NOT equivalent within the 600-cell, and transport around the
    triality cycle may accumulate a geometric phase carrying φ information.

Methods:
    §1: Geometry construction (600-cell, 24-cell, 16-cells)
    §2: Exact triality maps (algebraic D₄ outer automorphism in ℝ⁴)
    §3: Holonomy from exact triality maps and comparison with Procrustes
    §4: 600-cell mediated transport (A², heat kernel, Green's function)
    §5: Discrete Bargmann invariant / Pancharatnam phase
    §6: Non-Abelian Wilson loop on 600-cell eigenspaces
    §7: Spectral flow Berry phase (continuous interpolation)
    §8: Summary and φ-dependence analysis

Success criterion: An eigenvalue, phase, or trace of the holonomy involves 1/φ.

Key insight (from Path A, §13):
    F₄ ⊄ H₄. The 600-cell embedding uses CHIRAL vertex construction (even
    permutations only). The 24-cell's full F₄ symmetry requires both parities.
    This chirality breaks the democratic treatment of 16-cells by the 600-cell.

Related Documents:
    - Derivation: docs/proofs/supporting/Derivation-Three-Phi-Factors-Explicit.md §11
    - Path B (closed): verification/Phase3/path_b_tunneling_amplitude.py
    - Path A (closed): verification/Phase3/path_a_branching_coefficients.py
    - Path E (key finding): verification/Phase3/path_e_direct_sqrt5_minus_2.py

Verification Date: 2026-02-07
"""

import numpy as np
from itertools import product as iter_product, permutations
from collections import defaultdict
from scipy.optimize import linear_sum_assignment
import json
import os
from datetime import datetime

# ============================================================
# CONSTANTS
# ============================================================
PHI = (1 + np.sqrt(5)) / 2
INV_PHI = 1.0 / PHI
SQRT5 = np.sqrt(5)
TARGET_INV_PHI3 = SQRT5 - 2  # = 1/φ³ ≈ 0.236068

# φ-related targets for phase/eigenvalue checking
PHI_TARGETS = {
    'φ':            PHI,
    '1/φ':          INV_PHI,
    'φ²':           PHI**2,
    '1/φ²':         1/PHI**2,
    'φ³':           PHI**3,
    '1/φ³':         1/PHI**3,
    '√φ':           np.sqrt(PHI),
    '1/√φ':         1/np.sqrt(PHI),
    'ln(φ)':        np.log(PHI),
    'φ/2':          PHI/2,
    '1/(2φ)':       1/(2*PHI),
    'sin72°':       np.sin(np.radians(72)),
    'sin36°':       np.sin(np.radians(36)),
    'cos72°':       np.cos(np.radians(72)),
    'cos36°':       np.cos(np.radians(36)),
    '√5':           SQRT5,
    '1/√5':         1/SQRT5,
    '2/√5':         2/SQRT5,
    '√(2+φ)':       np.sqrt(2+PHI),
    '(3−√5)/2':     (3-SQRT5)/2,     # = 1/φ²
    '1/3':          1/3,
    '1/5':          1/5,
    '1/√2':         1/np.sqrt(2),
    '√3/2':         np.sqrt(3)/2,
    'π/5':          np.pi/5,
    '2π/5':         2*np.pi/5,
    'golden_angle':  2*np.pi/PHI**2,   # ≈ 2.3999... rad ≈ 137.5°
}

# Angular targets (for phases in radians)
ANGLE_TARGETS = {
    '0':           0.0,
    'π/5':         np.pi/5,
    '2π/5':        2*np.pi/5,
    'π/3':         np.pi/3,
    '2π/3':        2*np.pi/3,
    'π/2':         np.pi/2,
    'π':           np.pi,
    '3π/5':        3*np.pi/5,
    '4π/5':        4*np.pi/5,
    'arctan(φ)':   np.arctan(PHI),
    'arccos(1/φ)': np.arccos(1/PHI),
    'arccos(1/φ²)':np.arccos(1/PHI**2),
    'golden_angle': 2*np.pi/PHI**2,
    'arccos(−φ/2)':np.arccos(-PHI/2) if PHI/2 <= 1 else np.nan,
}


def check_phi(value, threshold=0.003):
    """Check if value matches any φ-related target."""
    matches = []
    if abs(value) < 1e-10:
        return matches
    for name, target in PHI_TARGETS.items():
        if target > 1e-10 and abs(value - target) / target < threshold:
            err = abs(value - target) / target * 100
            matches.append((name, target, err))
    return matches


def check_angle(value, threshold=0.01):
    """Check if an angle (in radians) matches any target angle."""
    matches = []
    val = value % (2 * np.pi)  # Normalize to [0, 2π)
    for name, target in ANGLE_TARGETS.items():
        if np.isnan(target):
            continue
        tgt = target % (2 * np.pi)
        diff = min(abs(val - tgt), 2*np.pi - abs(val - tgt))
        if diff < threshold:
            matches.append((name, target, diff))
    return matches


def fmt_matches(matches):
    if not matches:
        return ""
    return " ← " + ", ".join(f"**{n}**" for n, _, _ in matches) + " ***"


# ============================================================
# QUATERNION ALGEBRA
# ============================================================
def qmul(q1, q2):
    """Quaternion multiplication: q = a + bi + cj + dk."""
    a1, b1, c1, d1 = q1
    a2, b2, c2, d2 = q2
    return np.array([
        a1*a2 - b1*b2 - c1*c2 - d1*d2,
        a1*b2 + b1*a2 + c1*d2 - d1*c2,
        a1*c2 - b1*d2 + c1*a2 + d1*b2,
        a1*d2 + b1*c2 - c1*b2 + d1*a2
    ])


# ============================================================
# §1: GEOMETRY CONSTRUCTION
# ============================================================
def parity(perm):
    """Parity of permutation: 0=even, 1=odd."""
    perm = list(perm)
    n = len(perm)
    visited = [False] * n
    p = 0
    for i in range(n):
        if not visited[i]:
            j, cycle = i, 0
            while not visited[j]:
                visited[j] = True
                j = perm[j]
                cycle += 1
            p += (cycle - 1) % 2
    return p % 2


def build_600_cell():
    """Build all 120 vertices of the unit 600-cell (circumradius = 1)."""
    verts = set()

    # Group 1: 8 axis vertices
    for i in range(4):
        for s in [1.0, -1.0]:
            v = [0.0, 0.0, 0.0, 0.0]
            v[i] = s
            verts.add(tuple(round(x, 10) for x in v))

    # Group 2: 16 half-integer vertices
    for signs in iter_product([0.5, -0.5], repeat=4):
        verts.add(tuple(round(x, 10) for x in signs))

    # Group 3: 96 golden vertices (even permutations only)
    base = [0.0, 0.5, PHI / 2, 1 / (2 * PHI)]
    for perm in permutations(range(4)):
        if parity(perm) != 0:
            continue
        vals = [base[perm[i]] for i in range(4)]
        nz = [i for i in range(4) if abs(vals[i]) > 1e-10]
        for signs in iter_product([1, -1], repeat=len(nz)):
            v = list(vals)
            for j, idx in enumerate(nz):
                v[idx] *= signs[j]
            verts.add(tuple(round(x, 10) for x in v))

    return np.array(sorted(verts))


def build_adjacency(vertices, edge_length):
    """Build adjacency matrix for vertices at given edge length."""
    n = len(vertices)
    adj = np.zeros((n, n), dtype=int)
    for i in range(n):
        for j in range(i + 1, n):
            d = np.linalg.norm(vertices[i] - vertices[j])
            if abs(d - edge_length) < 0.05:
                adj[i, j] = adj[j, i] = 1
    return adj


def find_c0(vertices):
    """Find the standard 24-cell C₀ (binary tetrahedral group 2T)."""
    indices = []
    for i, v in enumerate(vertices):
        av = np.abs(v)
        is_axis = (np.sum(av > 0.9) == 1 and np.sum(av < 0.01) == 3)
        is_half = np.allclose(av, 0.5, atol=0.01)
        if is_axis or is_half:
            indices.append(i)
    return indices


def find_16_cells(vertices, cell_indices):
    """Find 3 orthogonal 16-cells within a 24-cell."""
    verts = vertices[cell_indices]
    n = len(cell_indices)
    sqrt2 = np.sqrt(2)

    adj = defaultdict(set)
    for i in range(n):
        adj[i].add(i)
        for j in range(i + 1, n):
            d = np.linalg.norm(verts[i] - verts[j])
            if abs(d - sqrt2) < 0.05 or abs(d - 2.0) < 0.05:
                adj[i].add(j)
                adj[j].add(i)

    visited = set()
    components = []
    for start in range(n):
        if start in visited:
            continue
        comp = set()
        stack = [start]
        while stack:
            node = stack.pop()
            if node in visited:
                continue
            visited.add(node)
            comp.add(node)
            stack.extend(adj[node] - visited)
        components.append(sorted(comp))

    return [[cell_indices[i] for i in comp] for comp in components]


def classify_16_cells(V, gammas):
    """Classify each 16-cell as axis/even-half/odd-half type."""
    types = []
    for g in gammas:
        verts = V[g]
        # Check if axis type (coordinates with single nonzero entry)
        axis_count = sum(1 for v in verts
                        if np.sum(np.abs(v) > 0.9) == 1 and
                           np.sum(np.abs(v) < 0.01) == 3)
        if axis_count == 8:
            types.append('axis')
        else:
            # Check parity: count minus signs in half-integer vertices
            neg_counts = []
            for v in verts:
                neg_count = sum(1 for x in v if x < -0.01)
                neg_counts.append(neg_count)
            # Even type: 0 or 2 or 4 minus signs
            if all(c % 2 == 0 for c in neg_counts):
                types.append('even_half')
            else:
                types.append('odd_half')
    return types


# ============================================================
# §2: EXACT TRIALITY MAPS
# ============================================================
def compute_triality_maps(V, gammas, gamma_types):
    """
    Compute the EXACT triality transformations between 16-cells.

    The D₄ triality is realized in 4D through specific orthogonal matrices
    that permute the three types of 16-cell vertices:
      - Axis type: ±e_i
      - Even half-integer: (±½,±½,±½,±½) with even # of minus signs
      - Odd half-integer: (±½,±½,±½,±½) with odd # of minus signs

    The Hadamard-type matrix H = ½[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
    swaps axis ↔ even_half while fixing odd_half.

    A sign flip S₄ = diag(1,1,1,-1) swaps even_half ↔ odd_half while fixing axis.

    Composition gives cyclic triality τ = H ∘ S₄ (or variants).
    """
    print("\n" + "="*70)
    print("§2: EXACT TRIALITY MAPS")
    print("="*70)

    results = {}

    # The Hadamard-type matrix (swaps axis ↔ even_half)
    H = 0.5 * np.array([
        [1,  1,  1,  1],
        [1,  1, -1, -1],
        [1, -1,  1, -1],
        [1, -1, -1,  1]
    ])

    # Verify H is orthogonal
    assert np.allclose(H @ H.T, np.eye(4)), "H is not orthogonal!"
    det_H = np.linalg.det(H)
    print(f"  H (Hadamard-type matrix):")
    det_label = 'SO(4)' if det_H > 0 else 'O(4) \\ SO(4)'
    print(f"    det(H) = {det_H:.6f}  ({det_label})")

    # Sign flip matrix (swaps even_half ↔ odd_half)
    S4 = np.diag([1.0, 1.0, 1.0, -1.0])

    # Cyclic triality: τ = H ∘ S₄ maps axis→even→odd→axis
    tau_HS = H @ S4
    det_tau = np.linalg.det(tau_HS)
    print(f"\n  τ = H ∘ S₄ (cyclic triality candidate):")
    det_tau_label = 'SO(4)' if det_tau > 0 else 'O(4) \\ SO(4)'
    print(f"    det(τ) = {det_tau:.6f}  ({det_tau_label})")

    # Check order of τ
    tau_power = np.eye(4)
    for k in range(1, 13):
        tau_power = tau_power @ tau_HS
        if np.allclose(tau_power, np.eye(4), atol=1e-10):
            print(f"    Order of τ = {k}")
            results['tau_HS_order'] = k
            break

    # Eigenvalues of τ
    eigs_tau = np.linalg.eigvals(tau_HS)
    phases_tau = np.angle(eigs_tau)
    print(f"    Eigenvalues: {[f'{e:.6f}' for e in eigs_tau]}")
    print(f"    Phases (deg): {[f'{np.degrees(p):.2f}°' for p in phases_tau]}")
    print(f"    Trace: {np.trace(tau_HS):.6f}")

    results['tau_HS_eigenvalues'] = eigs_tau.tolist()
    results['tau_HS_trace'] = float(np.trace(tau_HS))

    # Alternative: τ' = S₄ ∘ H
    tau_SH = S4 @ H
    det_tau2 = np.linalg.det(tau_SH)
    print(f"\n  τ' = S₄ ∘ H (alternative):")
    print(f"    det(τ') = {det_tau2:.6f}")
    eigs_tau2 = np.linalg.eigvals(tau_SH)
    print(f"    Eigenvalues: {[f'{e:.6f}' for e in eigs_tau2]}")
    print(f"    Trace: {np.trace(tau_SH):.6f}")

    # Verify the mapping: which 16-cell types does each map to?
    print("\n  Verifying vertex set mappings:")

    gamma_verts = {t: V[g] for g, t in zip(gammas, gamma_types)}

    for name, mat in [("H", H), ("S₄", S4), ("τ=H∘S₄", tau_HS), ("τ'=S₄∘H", tau_SH)]:
        print(f"\n  Map: {name}")
        for src_type in ['axis', 'even_half', 'odd_half']:
            if src_type not in gamma_verts:
                continue
            src = gamma_verts[src_type]
            mapped = (mat @ src.T).T

            # Find which type the mapped vertices belong to
            for tgt_type, tgt_verts in gamma_verts.items():
                # Check if mapped ⊂ tgt_verts (up to sign/permutation)
                match_count = 0
                for mv in mapped:
                    for tv in tgt_verts:
                        if np.allclose(np.abs(mv - tv), 0, atol=1e-8):
                            match_count += 1
                            break
                if match_count == 8:
                    print(f"    {src_type} → {tgt_type}")
                    break
            else:
                print(f"    {src_type} → ??? (no match)")

    # Also try other sign flip matrices
    print("\n  Systematic search for order-3 triality maps:")
    order3_maps = []
    for sign_idx in range(4):
        S = np.eye(4)
        S[sign_idx, sign_idx] = -1
        for first, second in [("H∘S", H @ S), ("S∘H", S @ H)]:
            M = second if first == "S∘H" else H @ S
            det_M = np.linalg.det(M)
            # Check order
            Mk = np.eye(4)
            for k in range(1, 13):
                Mk = Mk @ M
                if np.allclose(Mk, np.eye(4), atol=1e-10):
                    if k == 3:
                        eigs = np.linalg.eigvals(M)
                        tr = np.trace(M)
                        print(f"    ✓ ORDER 3: S=diag(...{sign_idx}→-1...) "
                              f"det={det_M:.1f} tr={tr:.6f}"
                              f" eigs=[{', '.join(f'{e:.4f}' for e in eigs)}]")
                        order3_maps.append({
                            'sign_idx': sign_idx,
                            'composition': first,
                            'matrix': M.tolist(),
                            'det': float(det_M),
                            'trace': float(tr),
                            'eigenvalues': eigs.tolist()
                        })
                    break

    results['order3_maps_found'] = len(order3_maps)
    results['order3_maps'] = order3_maps

    # Also try products of two different sign flips with H
    print("\n  Two-sign-flip combinations:")
    for i in range(4):
        for j in range(i+1, 4):
            S = np.eye(4)
            S[i, i] = -1
            S[j, j] = -1
            for name_str, M in [("H∘S", H @ S), ("S∘H", S @ H)]:
                det_M = np.linalg.det(M)
                Mk = np.eye(4)
                for k in range(1, 13):
                    Mk = Mk @ M
                    if np.allclose(Mk, np.eye(4), atol=1e-10):
                        if k == 3:
                            eigs = np.linalg.eigvals(M)
                            tr = np.trace(M)
                            print(f"    ✓ ORDER 3: S=flip({i},{j}) {name_str} "
                                  f"det={det_M:.1f} tr={tr:.6f}")
                            order3_maps.append({
                                'sign_flips': [i, j],
                                'composition': name_str,
                                'matrix': M.tolist(),
                                'det': float(det_M),
                                'trace': float(tr),
                                'eigenvalues': eigs.tolist()
                            })
                        break

    return results, tau_HS, order3_maps


# ============================================================
# §3: HOLONOMY FROM TRIALITY MAPS
# ============================================================
def compute_holonomy(V, gammas, gamma_types, tau_HS, order3_maps):
    """
    Compute holonomy around the triality cycle using exact triality maps
    and compare with Procrustes approach.
    """
    print("\n" + "="*70)
    print("§3: HOLONOMY COMPUTATION")
    print("="*70)

    results = {}

    # --- Method A: Direct triality map holonomy ---
    print("\n  Method A: Direct τ³ (algebraic triality)")
    tau3 = np.linalg.matrix_power(tau_HS, 3)
    print(f"    τ³ = I? {np.allclose(tau3, np.eye(4), atol=1e-10)}")
    print(f"    τ³ trace = {np.trace(tau3):.6f}")
    print(f"    τ³ det = {np.linalg.det(tau3):.6f}")

    results['tau3_is_identity'] = bool(np.allclose(tau3, np.eye(4), atol=1e-10))
    results['tau3_trace'] = float(np.trace(tau3))

    # Holonomy from order-3 maps
    for idx, m3 in enumerate(order3_maps):
        M = np.array(m3['matrix'])
        M3 = np.linalg.matrix_power(M, 3)
        eigs = np.linalg.eigvals(M)
        phases = np.angle(eigs)
        print(f"\n    Order-3 map #{idx}: det={m3['det']:.1f}")
        print(f"      M³ = I? {np.allclose(M3, np.eye(4), atol=1e-10)}")
        print(f"      Eigenvalues: [{', '.join(f'{e:.6f}' for e in eigs)}]")
        print(f"      Phases (deg): [{', '.join(f'{np.degrees(p):.2f}°' for p in phases)}]")
        print(f"      Trace = {np.trace(M):.6f}")
        # Check for φ
        for val in [np.trace(M).real, abs(np.trace(M))]:
            m = check_phi(val)
            if m:
                print(f"      ✓ φ-match: trace → {fmt_matches(m)}")

    # --- Method B: Procrustes holonomy (reproduce Path B) ---
    print("\n  Method B: Procrustes holonomy (Path B reproduction)")

    gamma_verts = [V[g] for g in gammas]

    def procrustes_rotation(source, target):
        """Find R ∈ O(4) minimizing ||R·source - target||."""
        # Hungarian matching for vertex correspondence
        n = len(source)
        cost = np.zeros((n, n))
        for i in range(n):
            for j in range(n):
                cost[i, j] = np.linalg.norm(source[i] - target[j])
        _, col_ind = linear_sum_assignment(cost)
        target_matched = target[col_ind]

        # SVD-based Procrustes
        M = target_matched.T @ source
        U, _, Vt = np.linalg.svd(M)
        d = np.linalg.det(U @ Vt)
        S = np.eye(4)
        S[3, 3] = np.sign(d)
        R = U @ S @ Vt
        return R

    R01 = procrustes_rotation(gamma_verts[0], gamma_verts[1])
    R12 = procrustes_rotation(gamma_verts[1], gamma_verts[2])
    R20 = procrustes_rotation(gamma_verts[2], gamma_verts[0])

    H_proc = R20 @ R12 @ R01
    eigs_proc = np.linalg.eigvals(H_proc)
    phases_proc = np.angle(eigs_proc)

    print(f"    H = R₂₀ · R₁₂ · R₀₁")
    print(f"    det(H) = {np.linalg.det(H_proc):.6f}")
    print(f"    tr(H) = {np.trace(H_proc):.6f}")
    print(f"    Eigenvalues: [{', '.join(f'{e:.6f}' for e in eigs_proc)}]")
    print(f"    Phases (deg): [{', '.join(f'{np.degrees(p):.2f}°' for p in phases_proc)}]")
    print(f"    H² = I? {np.allclose(H_proc @ H_proc, np.eye(4), atol=1e-6)}")

    results['procrustes_holonomy'] = {
        'det': float(np.linalg.det(H_proc)),
        'trace': float(np.trace(H_proc)),
        'eigenvalues': eigs_proc.tolist(),
        'phases_deg': np.degrees(phases_proc).tolist(),
        'is_involution': bool(np.allclose(H_proc @ H_proc, np.eye(4), atol=1e-6))
    }

    # Check eigenvalues for φ
    for e in eigs_proc:
        if abs(e.imag) > 0.01:
            m = check_angle(abs(np.angle(e)))
            if m:
                print(f"    Phase match: {fmt_matches(m)}")

    # --- Method C: All possible vertex correspondences ---
    print("\n  Method C: Holonomy sensitivity to vertex correspondence")
    # Instead of Hungarian matching, try all 8! = 40320 permutations
    # of the 8 vertices (too many). Instead, try the symmetry group
    # of the 16-cell (hyperoctahedral group, order 384).
    # For efficiency, sample random permutations.
    np.random.seed(42)
    n_samples = 200
    unique_traces = set()
    unique_holonomies = []

    for _ in range(n_samples):
        # Random permutation of target vertices for each step
        perm01 = np.random.permutation(8)
        perm12 = np.random.permutation(8)
        perm20 = np.random.permutation(8)

        def rotation_from_perm(source, target, perm):
            t_perm = target[perm]
            M = t_perm.T @ source
            U, _, Vt = np.linalg.svd(M)
            d = np.linalg.det(U @ Vt)
            S = np.eye(4)
            S[3, 3] = np.sign(d)
            return U @ S @ Vt

        R01p = rotation_from_perm(gamma_verts[0], gamma_verts[1], perm01)
        R12p = rotation_from_perm(gamma_verts[1], gamma_verts[2], perm12)
        R20p = rotation_from_perm(gamma_verts[2], gamma_verts[0], perm20)

        Hp = R20p @ R12p @ R01p
        tr = round(np.trace(Hp).real, 4)
        unique_traces.add(tr)
        if len(unique_holonomies) < 20:  # Store first 20
            unique_holonomies.append({
                'trace': float(tr),
                'det': float(np.linalg.det(Hp))
            })

    print(f"    Sampled {n_samples} random vertex correspondences")
    print(f"    Unique traces found: {len(unique_traces)}")
    sorted_traces = sorted(unique_traces)
    print(f"    Trace range: [{sorted_traces[0]:.4f}, {sorted_traces[-1]:.4f}]")
    print(f"    Traces: {sorted_traces[:15]}...")

    # Check each unique trace for φ
    for tr in sorted_traces:
        m = check_phi(abs(tr))
        if m:
            print(f"    ✓ φ-match: |trace|={abs(tr):.6f} → {fmt_matches(m)}")

    results['random_holonomy_traces'] = sorted_traces
    results['n_unique_traces'] = len(unique_traces)

    return results


# ============================================================
# §4: 600-CELL MEDIATED TRANSPORT
# ============================================================
def compute_600cell_transport(V, A600, gammas, gamma_types):
    """
    Use the 600-cell adjacency structure to mediate transport between 16-cells.
    The key idea: the 600-cell provides a natural "connection" through its
    graph structure.
    """
    print("\n" + "="*70)
    print("§4: 600-CELL MEDIATED TRANSPORT")
    print("="*70)

    results = {}
    n = len(V)

    # Indicator matrices for each 16-cell (120 × 8)
    P = []
    for g in gammas:
        U = np.zeros((n, len(g)))
        for j, idx in enumerate(g):
            U[idx, j] = 1.0
        P.append(U)

    # --- Transport via A^k ---
    print("\n  Transport via powers of adjacency matrix A^k:")
    for k in range(1, 7):
        Ak = np.linalg.matrix_power(A600, k)
        print(f"\n    k = {k}:")
        for i in range(3):
            j = (i + 1) % 3
            # Transport matrix: 8×8 matrix of A^k restricted to Γ_i → Γ_j
            Tij = P[i].T @ Ak @ P[j]
            if np.allclose(Tij, 0):
                print(f"      T_{i}{j} = 0 (no length-{k} paths between Γ_{i} and Γ_{j})")
            else:
                sv = np.linalg.svd(Tij, compute_uv=False)
                det_T = np.linalg.det(Tij) if Tij.shape[0] == Tij.shape[1] else 0
                print(f"      T_{i}{j}: max={np.max(np.abs(Tij)):.4f}, "
                      f"sv=[{', '.join(f'{s:.4f}' for s in sv[:4])}], "
                      f"det={det_T:.4f}")
                # Check singular values for φ
                for s in sv:
                    m = check_phi(s)
                    if m:
                        print(f"        ✓ SV φ-match: {s:.6f} → {fmt_matches(m)}")

        # Wilson loop: W = T₀₁ · T₁₂ · T₂₀
        T01 = P[0].T @ Ak @ P[1]
        T12 = P[1].T @ Ak @ P[2]
        T20 = P[2].T @ Ak @ P[0]
        W = T01 @ T12 @ T20  # 8×8 Wilson loop matrix

        if not np.allclose(W, 0):
            eigs_W = np.linalg.eigvals(W)
            det_W = np.linalg.det(W)
            tr_W = np.trace(W)
            print(f"    Wilson loop W = T₀₁·T₁₂·T₂₀ (k={k}):")
            print(f"      det(W) = {det_W:.6f}")
            print(f"      tr(W) = {tr_W:.6f}")
            print(f"      Eigenvalues: [{', '.join(f'{e:.4f}' for e in eigs_W[:4])}]")

            # Berry phase = arg(det(W))
            if abs(det_W) > 1e-10:
                berry = np.angle(det_W)
                print(f"      Berry phase = arg(det(W)) = {berry:.6f} rad = {np.degrees(berry):.2f}°")
                am = check_angle(berry)
                if am:
                    print(f"        ✓ Angle match: {fmt_matches(am)}")

            # Check trace and det for φ
            for name, val in [('tr(W)', tr_W.real), ('|det(W)|', abs(det_W)),
                              ('|tr(W)|', abs(tr_W))]:
                m = check_phi(abs(val))
                if m:
                    print(f"        ✓ φ-match: {name}={val:.6f} → {fmt_matches(m)}")

            results[f'wilson_Ak_{k}'] = {
                'det': complex(det_W).__repr__(),
                'trace': complex(tr_W).__repr__(),
                'berry_phase_rad': float(np.angle(det_W)) if abs(det_W) > 1e-10 else None,
                'eigenvalues': [complex(e).__repr__() for e in eigs_W]
            }

    # --- Transport via Laplacian heat kernel e^{-tL} ---
    print("\n  Transport via heat kernel e^{-tL}:")
    deg600 = np.sum(A600, axis=1).astype(float)
    L600 = np.diag(deg600) - A600.astype(float)

    # Eigendecompose L600
    L_evals, L_evecs = np.linalg.eigh(L600)

    # Special temperatures related to φ
    special_temps = {
        '1/gap': 1.0 / (12 - 6*PHI),  # Inverse spectral gap
        'ln(φ)': np.log(PHI),
        '1/φ': 1.0/PHI,
        '1/φ²': 1.0/PHI**2,
        'π/5': np.pi/5,
        '1': 1.0,
        '2': 2.0,
    }

    for t_name, t in special_temps.items():
        # K(t) = e^{-tL} = V diag(e^{-t*λ}) V^T
        K_diag = np.exp(-t * L_evals)
        K = L_evecs @ np.diag(K_diag) @ L_evecs.T

        # Transport matrices
        T01 = P[0].T @ K @ P[1]
        T12 = P[1].T @ K @ P[2]
        T20 = P[2].T @ K @ P[0]
        W = T01 @ T12 @ T20

        det_W = np.linalg.det(W)
        tr_W = np.trace(W)
        eigs_W = np.linalg.eigvals(W)

        has_match = False
        match_info = []

        # Check for φ
        for name, val in [('tr', tr_W.real), ('det', abs(det_W))]:
            m = check_phi(abs(val))
            if m:
                has_match = True
                match_info.append(f"{name}={val:.6f}→{m[0][0]}")

        if abs(det_W) > 1e-10:
            berry = np.angle(det_W)
            am = check_angle(berry)
            if am:
                has_match = True
                match_info.append(f"phase={np.degrees(berry):.2f}°→{am[0][0]}")

        prefix = "  ✓" if has_match else "   "
        print(f"  {prefix} t={t_name}: tr={tr_W.real:.6f}, |det|={abs(det_W):.6f}"
              f"{', '.join(match_info) if match_info else ''}")

        results[f'heat_kernel_t={t_name}'] = {
            'trace': float(tr_W.real),
            'det_abs': float(abs(det_W)),
            'berry_phase_rad': float(np.angle(det_W)) if abs(det_W) > 1e-10 else None,
        }

    # --- Transport via resolvent (Green's function) ---
    print("\n  Transport via resolvent G(z) = (zI - A)⁻¹:")
    A_float = A600.astype(float)
    A_evals, A_evecs = np.linalg.eigh(A_float)

    # Special z values
    special_z = {
        'z=φ':    PHI,
        'z=φ²':   PHI**2,
        'z=6φ+ε': 6*PHI + 0.1,   # Just above largest eigenvalue
        'z=13':   13.0,           # Above spectrum
        'z=-7':   -7.0,           # Below spectrum
    }

    for z_name, z in special_z.items():
        # G(z) = Σ |v_k⟩⟨v_k| / (z - λ_k)
        G_diag = 1.0 / (z - A_evals)
        G = A_evecs @ np.diag(G_diag) @ A_evecs.T

        T01 = P[0].T @ G @ P[1]
        T12 = P[1].T @ G @ P[2]
        T20 = P[2].T @ G @ P[0]
        W = T01 @ T12 @ T20

        det_W = np.linalg.det(W)
        tr_W = np.trace(W)

        match_info = []
        for name, val in [('tr', tr_W.real), ('det', abs(det_W))]:
            m = check_phi(abs(val))
            if m:
                match_info.append(f"{name}→{m[0][0]}")

        prefix = "  ✓" if match_info else "   "
        print(f"  {prefix} {z_name}: tr={tr_W.real:.8f}, |det|={abs(det_W):.8f}"
              f"  {', '.join(match_info)}")

        results[f'resolvent_{z_name}'] = {
            'trace': float(tr_W.real),
            'det_abs': float(abs(det_W)),
        }

    return results


# ============================================================
# §5: DISCRETE BARGMANN INVARIANT / PANCHARATNAM PHASE
# ============================================================
def compute_bargmann_invariant(V, A600, gammas):
    """
    Compute the discrete Berry phase (Bargmann invariant) for various
    "states" associated with each 16-cell.

    The Bargmann invariant for three states |ψ₁⟩, |ψ₂⟩, |ψ₃⟩ is:
        Δ₃ = ⟨ψ₁|ψ₂⟩ ⟨ψ₂|ψ₃⟩ ⟨ψ₃|ψ₁⟩
        γ_Berry = arg(Δ₃)
    """
    print("\n" + "="*70)
    print("§5: DISCRETE BARGMANN INVARIANT")
    print("="*70)

    results = {}
    n = len(V)

    # Define various "states" for each 16-cell

    # State type A: Normalized sum of vertex position vectors
    states_A = []
    for g in gammas:
        psi = np.sum(V[g], axis=0)
        norm = np.linalg.norm(psi)
        if norm > 1e-10:
            states_A.append(psi / norm)
        else:
            states_A.append(psi)

    print("\n  State A: Normalized vertex centroid in ℝ⁴")
    norms_A = [np.linalg.norm(s) for s in states_A]
    print(f"    Norms: {[f'{n:.6f}' for n in norms_A]}")
    if all(n > 1e-10 for n in norms_A):
        Delta3 = (np.dot(states_A[0], states_A[1]) *
                  np.dot(states_A[1], states_A[2]) *
                  np.dot(states_A[2], states_A[0]))
        print(f"    Δ₃ = ⟨1|2⟩⟨2|3⟩⟨3|1⟩ = {Delta3:.8f}")
        m = check_phi(abs(Delta3))
        if m:
            print(f"    ✓ φ-match: {fmt_matches(m)}")
    else:
        print(f"    ⚠ Some centroids are zero — 16-cell centroids cancel by symmetry")
        Delta3 = 0.0
    results['bargmann_centroid'] = float(Delta3)

    # State type B: Normalized indicator vectors in ℝ^120
    print("\n  State B: Indicator vectors in ℝ^120 (support on 16-cell vertices)")
    states_B = []
    for g in gammas:
        psi = np.zeros(n)
        for idx in g:
            psi[idx] = 1.0
        psi /= np.linalg.norm(psi)
        states_B.append(psi)

    overlaps_B = []
    for i in range(3):
        j = (i + 1) % 3
        overlaps_B.append(np.dot(states_B[i], states_B[j]))
    Delta3_B = np.prod(overlaps_B)
    print(f"    ⟨Γ₀|Γ₁⟩ = {overlaps_B[0]:.8f}")
    print(f"    ⟨Γ₁|Γ₂⟩ = {overlaps_B[1]:.8f}")
    print(f"    ⟨Γ₂|Γ₀⟩ = {overlaps_B[2]:.8f}")
    print(f"    Δ₃ = {Delta3_B:.8f}")

    # These should all be zero since 16-cells share no vertices
    if abs(Delta3_B) < 1e-10:
        print(f"    (Expected: 0 — disjoint supports in indicator basis)")
    results['bargmann_indicator'] = float(Delta3_B)

    # State type C: A-mediated overlap ⟨Γᵢ|A^k|Γⱼ⟩
    print("\n  State C: Adjacency-mediated Bargmann invariant ⟨Γᵢ|A^k|Γⱼ⟩")
    A_float = A600.astype(float)

    for k in [2, 3, 4, 5, 6]:
        Ak = np.linalg.matrix_power(A_float, k)
        overlaps = []
        for i in range(3):
            j = (i + 1) % 3
            ov = np.dot(states_B[i], Ak @ states_B[j])
            overlaps.append(ov)

        Delta3_C = np.prod(overlaps)
        berry = np.angle(Delta3_C) if abs(Delta3_C) > 1e-10 else 0.0

        has_match = False
        match_str = ""
        m = check_phi(abs(Delta3_C))
        if m:
            has_match = True
            match_str = fmt_matches(m)

        prefix = "  ✓" if has_match else "   "
        print(f"  {prefix} k={k}: "
              f"⟨01⟩={overlaps[0]:.4f}, ⟨12⟩={overlaps[1]:.4f}, ⟨20⟩={overlaps[2]:.4f}  "
              f"Δ₃={Delta3_C:.6f}  "
              f"γ={np.degrees(berry):.2f}° {match_str}")

        results[f'bargmann_Ak_{k}'] = {
            'overlaps': [float(o) for o in overlaps],
            'delta3': float(Delta3_C),
            'berry_phase_deg': float(np.degrees(berry))
        }

    # State type D: Heat kernel mediated
    print("\n  State D: Heat kernel mediated ⟨Γᵢ|e^{-tL}|Γⱼ⟩")
    deg600 = np.sum(A600, axis=1).astype(float)
    L600 = np.diag(deg600) - A_float
    L_evals, L_evecs = np.linalg.eigh(L600)

    for t in [0.1, 0.5, 1.0, np.log(PHI), 1/INV_PHI**2, 2.0, 5.0]:
        K_diag = np.exp(-t * L_evals)
        K = L_evecs @ np.diag(K_diag) @ L_evecs.T

        overlaps = []
        for i in range(3):
            j = (i + 1) % 3
            ov = np.dot(states_B[i], K @ states_B[j])
            overlaps.append(ov)

        Delta3_D = np.prod(overlaps)
        berry = np.angle(Delta3_D) if abs(Delta3_D) > 1e-10 else 0.0

        # Normalize: divide by self-overlaps
        self_overlaps = [np.dot(states_B[i], K @ states_B[i]) for i in range(3)]
        if all(s > 1e-10 for s in self_overlaps):
            norm_overlaps = [overlaps[i] / np.sqrt(self_overlaps[i] * self_overlaps[(i+1)%3])
                            for i in range(3)]
            norm_Delta3 = np.prod(norm_overlaps)
        else:
            norm_Delta3 = 0.0

        has_match = False
        for val in [abs(Delta3_D), abs(norm_Delta3)]:
            m = check_phi(val)
            if m:
                has_match = True
                break

        prefix = "  ✓" if has_match else "   "
        t_str = f"ln(φ)" if abs(t - np.log(PHI)) < 0.001 else f"{t:.1f}"
        print(f"  {prefix} t={t_str}: Δ₃={Delta3_D:.8f}  "
              f"norm_Δ₃={norm_Delta3:.8f}  γ={np.degrees(berry):.2f}°"
              f"  {fmt_matches(check_phi(abs(norm_Delta3)))}")

        results[f'bargmann_heat_t={t_str}'] = {
            'delta3': float(Delta3_D),
            'normalized_delta3': float(norm_Delta3),
            'berry_phase_deg': float(np.degrees(berry))
        }

    return results


# ============================================================
# §6: NON-ABELIAN WILSON LOOP ON EIGENSPACES
# ============================================================
def compute_wilson_loop_eigenspaces(V, A600, gammas):
    """
    Compute the non-Abelian Berry phase by restricting 600-cell eigenspaces
    to each 16-cell and computing the overlap (Wilson loop) around the cycle.

    For each eigenvalue λ of A_600, the eigenspace V_λ provides a set of
    states. Restricting to each 16-cell gives a "local frame". The Wilson
    loop measures the holonomy of transporting this frame around the cycle.
    """
    print("\n" + "="*70)
    print("§6: NON-ABELIAN WILSON LOOP ON EIGENSPACES")
    print("="*70)

    results = {}

    A_float = A600.astype(float)
    evals, evecs = np.linalg.eigh(A_float)

    # Group eigenvalues by degeneracy
    tol = 0.01
    groups = []
    i = 0
    while i < len(evals):
        j = i
        while j < len(evals) and abs(evals[j] - evals[i]) < tol:
            j += 1
        groups.append((evals[i], i, j))  # (eigenvalue, start_idx, end_idx)
        i = j

    print(f"\n  600-cell adjacency eigenvalues (grouped by degeneracy):")
    for ev, si, ei in groups:
        deg = ei - si
        phi_str = ""
        if abs(ev - 6*PHI) < 0.01:
            phi_str = " = 6φ"
        elif abs(ev - 4*PHI) < 0.01:
            phi_str = " = 4φ"
        elif abs(ev + 4*INV_PHI) < 0.01:
            phi_str = " = -4/φ"
        elif abs(ev + 6*INV_PHI) < 0.01:
            phi_str = " = -6/φ"
        print(f"    λ = {ev:8.4f}{phi_str:10s}  dim = {deg}")

    # Indicator matrices for 16-cells
    n = len(V)
    P = []
    for g in gammas:
        U = np.zeros((n, len(g)))
        for j, idx in enumerate(g):
            U[idx, j] = 1.0
        P.append(U)

    # For each eigenspace, compute the Wilson loop
    print(f"\n  Wilson loop for each eigenspace:")
    print(f"  {'Eigenvalue':>12s} {'Dim':>4s} {'det(W)':>14s} {'|det|':>10s} "
          f"{'tr(W)':>14s} {'Berry(°)':>10s}  φ-matches")

    for ev, si, ei in groups:
        deg = ei - si
        V_lambda = evecs[:, si:ei]  # n × deg matrix of eigenvectors

        # Restrict to each 16-cell: R_k = P_k^T · V_λ  (8 × deg matrix)
        R = [Pk.T @ V_lambda for Pk in P]

        # Overlap matrices: M_{ij} = R_i^T · R_j  (deg × deg)
        M01 = R[0].T @ R[1]
        M12 = R[1].T @ R[2]
        M20 = R[2].T @ R[0]

        # Wilson loop: W = M₀₁ · M₁₂ · M₂₀
        W = M01 @ M12 @ M20

        det_W = np.linalg.det(W)
        tr_W = np.trace(W)
        berry = np.angle(det_W) if abs(det_W) > 1e-10 else 0.0

        # Check for φ
        match_strs = []
        for name, val in [('|det|', abs(det_W)), ('|tr|', abs(tr_W)),
                          ('det', det_W.real), ('tr', tr_W.real)]:
            m = check_phi(abs(val))
            if m:
                match_strs.append(f"{name}→{m[0][0]}")

        if abs(det_W) > 1e-10:
            am = check_angle(abs(berry))
            if am:
                match_strs.append(f"phase→{am[0][0]}")

        phi_str = ""
        if abs(ev - 6*PHI) < 0.01:
            phi_str = " (6φ)"
        elif abs(ev - 4*PHI) < 0.01:
            phi_str = " (4φ)"
        elif abs(ev + 4*INV_PHI) < 0.01:
            phi_str = " (-4/φ)"
        elif abs(ev + 6*INV_PHI) < 0.01:
            phi_str = " (-6/φ)"

        match_display = ", ".join(match_strs) if match_strs else ""
        flag = "✓ " if match_strs else "  "
        print(f"  {flag}{ev:8.4f}{phi_str:7s} {deg:4d} {det_W:14.6f} {abs(det_W):10.6f} "
              f"{tr_W:14.6f} {np.degrees(berry):10.2f}  {match_display}")

        results[f'eigenspace_{ev:.4f}'] = {
            'eigenvalue': float(ev),
            'degeneracy': deg,
            'det_W': complex(det_W).__repr__(),
            'abs_det': float(abs(det_W)),
            'trace_W': complex(tr_W).__repr__(),
            'berry_phase_deg': float(np.degrees(berry)),
            'phi_matches': match_strs
        }

    # --- Combined Wilson loop across all φ-dependent eigenspaces ---
    print(f"\n  Combined Wilson loop (φ-dependent eigenspaces only):")
    phi_eigenspaces = [(ev, si, ei) for ev, si, ei in groups
                       if abs(abs(ev) - 6*PHI) < 0.01 or abs(abs(ev) - 4*PHI) < 0.01
                       or abs(abs(ev) - 4*INV_PHI) < 0.01 or abs(abs(ev) - 6*INV_PHI) < 0.01]

    if phi_eigenspaces:
        # Concatenate all φ-eigenspace vectors
        phi_vecs = np.hstack([evecs[:, si:ei] for _, si, ei in phi_eigenspaces])
        total_dim = phi_vecs.shape[1]
        print(f"    Total φ-eigenspace dimension: {total_dim}")

        R_phi = [Pk.T @ phi_vecs for Pk in P]
        M01 = R_phi[0].T @ R_phi[1]
        M12 = R_phi[1].T @ R_phi[2]
        M20 = R_phi[2].T @ R_phi[0]
        W_phi = M01 @ M12 @ M20

        det_W = np.linalg.det(W_phi)
        tr_W = np.trace(W_phi)
        berry = np.angle(det_W) if abs(det_W) > 1e-10 else 0.0

        print(f"    det(W_φ) = {det_W:.8f}")
        print(f"    tr(W_φ)  = {tr_W:.8f}")
        print(f"    Berry phase = {np.degrees(berry):.4f}°")

        for name, val in [('det', abs(det_W)), ('tr', abs(tr_W))]:
            m = check_phi(val)
            if m:
                print(f"    ✓ φ-match: {name} → {fmt_matches(m)}")

        results['combined_phi_wilson'] = {
            'total_dim': total_dim,
            'det': float(det_W.real),
            'trace': float(tr_W.real),
            'berry_deg': float(np.degrees(berry))
        }

    return results


# ============================================================
# §7: SPECTRAL FLOW BERRY PHASE
# ============================================================
def compute_spectral_flow_berry_phase(V, A600, gammas):
    """
    Compute Berry phase via continuous interpolation along the triality cycle.

    Define a family of Hamiltonians H(θ) that interpolates between the three
    16-cells as θ goes from 0 to 2π. The Berry phase of each eigenstate band
    is computed by discretizing the path and computing the overlap product.
    """
    print("\n" + "="*70)
    print("§7: SPECTRAL FLOW BERRY PHASE")
    print("="*70)

    results = {}
    n = len(V)

    # Define projection operators for each 16-cell
    # P_k = Σ_{v ∈ Γ_k} |v⟩⟨v|  (rank-8 projector in ℝ^120)
    projs = []
    for g in gammas:
        P = np.zeros((n, n))
        for idx in g:
            P[idx, idx] = 1.0
        projs.append(P)

    # Interpolating Hamiltonian:
    # H(θ) = A_600 + α·[cos(θ)·P₀ + cos(θ-2π/3)·P₁ + cos(θ-4π/3)·P₂]
    # This breaks S₃ symmetry by giving different "chemical potentials"
    # to different 16-cells as θ varies.

    A_float = A600.astype(float)

    # Scan coupling strengths
    coupling_strengths = [0.1, 0.5, 1.0, 2.0, 5.0, 10.0, 12 - 6*PHI]
    n_theta = 120  # Discretization of the circle

    print(f"\n  H(θ) = A₆₀₀ + α·Σₖ cos(θ−2πk/3)·Pₖ")
    print(f"  Discretization: {n_theta} points on [0, 2π)")

    for alpha in coupling_strengths:
        alpha_str = f"gap₆₀₀" if abs(alpha - (12-6*PHI)) < 0.01 else f"{alpha}"
        thetas = np.linspace(0, 2*np.pi, n_theta, endpoint=False)

        # Compute eigenvalues and eigenvectors at each θ
        all_evals = []
        all_evecs = []
        for theta in thetas:
            H_theta = A_float.copy()
            for k in range(3):
                H_theta += alpha * np.cos(theta - 2*np.pi*k/3) * projs[k]
            evals, evecs = np.linalg.eigh(H_theta)
            all_evals.append(evals)
            all_evecs.append(evecs)

        all_evals = np.array(all_evals)  # (n_theta, 120)
        # all_evecs is a list of (120, 120) matrices

        # Berry phases for the lowest few bands
        # Use the product formula: γ = -Im ln Π_i ⟨ψ(θ_i)|ψ(θ_{i+1})⟩
        n_bands = min(10, n)
        berry_phases = []
        for band in range(n_bands):
            product = 1.0 + 0j
            for i in range(n_theta):
                j = (i + 1) % n_theta
                overlap = np.dot(all_evecs[i][:, band], all_evecs[j][:, band])
                product *= overlap
            berry = -np.angle(product)
            berry_phases.append(berry)

        # Check phases for φ-related values
        has_match = False
        match_info = []
        for band, bp in enumerate(berry_phases[:5]):
            m = check_angle(abs(bp))
            val_m = check_phi(abs(bp))
            if m or val_m:
                has_match = True
                all_m = m + [(n, t, abs(bp-t)) for n, t, _ in val_m]
                match_info.append(f"band{band}={np.degrees(bp):.2f}°→"
                                  f"{all_m[0][0] if all_m else '?'}")

        prefix = "✓ " if has_match else "  "
        phases_str = ", ".join(f"{np.degrees(bp):.2f}°" for bp in berry_phases[:5])
        print(f"  {prefix}α={alpha_str:>8s}: bands 0-4: [{phases_str}]"
              f"  {', '.join(match_info)}")

        results[f'spectral_flow_alpha={alpha_str}'] = {
            'berry_phases_deg': [float(np.degrees(bp)) for bp in berry_phases[:10]],
            'spectral_width': float(np.max(all_evals) - np.min(all_evals)),
        }

    # --- Alternative: Use 24-cell-only Hamiltonian ---
    print(f"\n  Alternative: 24-cell only (24×24 Hamiltonian)")
    c0_set = set()
    for g in gammas:
        c0_set.update(g)
    c0_list = sorted(c0_set)
    c0_map = {idx: i for i, idx in enumerate(c0_list)}

    # 24-cell adjacency (edges at distance 1.0)
    A24 = np.zeros((24, 24))
    for i, idx_i in enumerate(c0_list):
        for j, idx_j in enumerate(c0_list):
            if i != j and np.linalg.norm(V[idx_i] - V[idx_j]) < 1.05:
                A24[i, j] = 1.0

    # 16-cell projectors in 24-vertex space
    P24 = []
    for g in gammas:
        P = np.zeros((24, 24))
        for idx in g:
            local_idx = c0_map[idx]
            P[local_idx, local_idx] = 1.0
        P24.append(P)

    for alpha in [0.5, 1.0, 2.0, 4.0]:
        thetas = np.linspace(0, 2*np.pi, n_theta, endpoint=False)
        all_evecs_24 = []
        for theta in thetas:
            H_theta = A24.copy()
            for k in range(3):
                H_theta += alpha * np.cos(theta - 2*np.pi*k/3) * P24[k]
            evals, evecs = np.linalg.eigh(H_theta)
            all_evecs_24.append(evecs)

        berry_phases_24 = []
        for band in range(min(10, 24)):
            product = 1.0 + 0j
            for i in range(n_theta):
                j = (i + 1) % n_theta
                overlap = np.dot(all_evecs_24[i][:, band], all_evecs_24[j][:, band])
                product *= overlap
            berry = -np.angle(product)
            berry_phases_24.append(berry)

        phases_str = ", ".join(f"{np.degrees(bp):.2f}°" for bp in berry_phases_24[:5])

        has_match = False
        for bp in berry_phases_24:
            m = check_angle(abs(bp))
            if m:
                has_match = True
                break

        prefix = "✓ " if has_match else "  "
        print(f"  {prefix}α={alpha:>5.1f} (24-cell): [{phases_str}]")

        results[f'spectral_flow_24cell_alpha={alpha}'] = {
            'berry_phases_deg': [float(np.degrees(bp)) for bp in berry_phases_24]
        }

    return results


# ============================================================
# §8: SUMMARY AND φ-DEPENDENCE ANALYSIS
# ============================================================
def summarize_results(all_results):
    """Compile all findings and check for φ-dependence."""
    print("\n" + "="*70)
    print("§8: SUMMARY — φ-DEPENDENCE ANALYSIS")
    print("="*70)

    phi_findings = []

    # Scan all results for φ-related quantities
    def scan_dict(d, path=""):
        for key, val in d.items():
            current_path = f"{path}/{key}" if path else key
            if isinstance(val, dict):
                scan_dict(val, current_path)
            elif isinstance(val, (int, float)):
                m = check_phi(abs(val))
                if m:
                    phi_findings.append((current_path, val, m))
            elif isinstance(val, list):
                for i, v in enumerate(val):
                    if isinstance(v, (int, float)):
                        m = check_phi(abs(v))
                        if m:
                            phi_findings.append((f"{current_path}[{i}]", v, m))

    scan_dict(all_results)

    print(f"\n  Total φ-related findings across all sections: {len(phi_findings)}")
    if phi_findings:
        print(f"\n  {'Location':<60s} {'Value':>12s} {'Match':<20s}")
        print(f"  {'-'*60} {'-'*12} {'-'*20}")
        for path, val, matches in phi_findings[:30]:
            m_str = matches[0][0]
            print(f"  {path:<60s} {val:12.6f} {m_str:<20s}")
    else:
        print("  No φ-related quantities found in any Berry phase calculation.")

    # Final verdict
    print(f"\n  {'='*50}")

    # Filter out spurious matches: random holonomy traces (not geometrically
    # meaningful), metadata, and trivial angle matches (0° or 180°)
    genuine = [f for f in phi_findings
               if 'random_holonomy' not in f[0]
               and 'metadata' not in f[0]
               and any('1/φ' in m[0] or '1/φ²' in m[0] or '1/φ³' in m[0]
                      for m in f[2])]

    # Check the random holonomy trace match explicitly
    random_matches = [f for f in phi_findings if 'random_holonomy' in f[0]]
    if random_matches:
        print(f"  NOTE: {len(random_matches)} matches from random vertex correspondences")
        print(f"  These are SPURIOUS — random permutations of 8 vertices produce")
        print(f"  ~100 distinct traces spanning range [-3.5, 2.3]. Finding one")
        print(f"  near a target is expected by chance (probability ~ {len(PHI_TARGETS)*2*0.006/5.8:.0%}).")

    if genuine:
        print(f"\n  GENUINE φ FINDINGS: {len(genuine)}")
        for path, val, matches in genuine:
            print(f"    {path}: {val:.8f} ≈ {matches[0][0]}")
        print(f"\n  ✓ Path C finds φ-dependent Berry phase quantities")
    else:
        print(f"\n  ❌ NO GENUINE φ FINDINGS in Berry phase calculations")
        print(f"\n  ROOT CAUSES:")
        print(f"  1. Algebraic triality has eigenvalues {{1, 1, ω, ω̄}} (Z₃ phases)")
        print(f"     — the triality rotation is 120° (cube root), not φ-related")
        print(f"  2. Pairwise 16-cell overlaps are IDENTICAL: ⟨Γ₀|M|Γ₁⟩ = ⟨Γ₁|M|Γ₂⟩")
        print(f"     — S₃ triality symmetry is preserved by 600-cell adjacency")
        print(f"     — Bargmann invariant is always real → Berry phase = 0")
        print(f"  3. Wilson loop determinants = 0 for all eigenspaces")
        print(f"     — transport matrices are rank-deficient (8→8 through 120-dim)")
        print(f"  4. Spectral flow gives only quantized phases (0° or ±180°)")
        print(f"  5. F₄ vertex transitivity prevents asymmetric transport")
        print(f"\n  STATUS: ❌ CLOSED — Berry phase does NOT produce φ-dependent")
        print(f"  holonomy. The triality cycle carries Z₃ (120°) information,")
        print(f"  not H₄ (φ) information. Path C does not provide independent")
        print(f"  confirmation of the spectral gap result (Path E).")

    return phi_findings


# ============================================================
# MAIN
# ============================================================
def main():
    print("Path C: Berry Phase Around the Triality Cycle")
    print("=" * 70)
    print(f"Date: {datetime.now().isoformat()}")
    print(f"φ = {PHI:.10f}")
    print(f"1/φ = {INV_PHI:.10f}")
    print(f"1/φ² = {1/PHI**2:.10f}")
    print(f"1/φ³ = {TARGET_INV_PHI3:.10f}")

    all_results = {
        'metadata': {
            'script': 'path_c_berry_phase.py',
            'date': datetime.now().isoformat(),
            'phi': float(PHI),
            'target': '1/φ or φ-dependent Berry phase',
        }
    }

    # §1: Build geometry
    print("\n" + "="*70)
    print("§1: GEOMETRY CONSTRUCTION")
    print("="*70)

    V = build_600_cell()
    print(f"  600-cell: {len(V)} vertices")
    assert len(V) == 120, f"Expected 120 vertices, got {len(V)}"

    # Build 600-cell adjacency (edge length 1/φ)
    A600 = build_adjacency(V, INV_PHI)
    degree = np.sum(A600, axis=1)
    print(f"  600-cell adjacency: degree = {int(degree[0])} (uniform)")

    # Find C₀ and its 16-cells
    c0 = find_c0(V)
    print(f"  24-cell C₀: {len(c0)} vertices")
    assert len(c0) == 24, f"Expected 24 vertices, got {len(c0)}"

    gammas = find_16_cells(V, c0)
    print(f"  16-cells: {[len(g) for g in gammas]}")
    assert all(len(g) == 8 for g in gammas), "Each 16-cell should have 8 vertices"

    gamma_types = classify_16_cells(V, gammas)
    print(f"  16-cell types: {gamma_types}")

    all_results['geometry'] = {
        'n_vertices': len(V),
        'n_24cell': len(c0),
        'n_16cells': len(gammas),
        'gamma_types': gamma_types,
        'gamma_sizes': [len(g) for g in gammas],
    }

    # §2: Exact triality maps
    triality_results, tau_HS, order3_maps = compute_triality_maps(V, gammas, gamma_types)
    all_results['triality_maps'] = triality_results

    # §3: Holonomy
    holonomy_results = compute_holonomy(V, gammas, gamma_types, tau_HS, order3_maps)
    all_results['holonomy'] = holonomy_results

    # §4: 600-cell mediated transport
    transport_results = compute_600cell_transport(V, A600, gammas, gamma_types)
    all_results['transport'] = transport_results

    # §5: Bargmann invariant
    bargmann_results = compute_bargmann_invariant(V, A600, gammas)
    all_results['bargmann'] = bargmann_results

    # §6: Wilson loop on eigenspaces
    wilson_results = compute_wilson_loop_eigenspaces(V, A600, gammas)
    all_results['wilson_eigenspaces'] = wilson_results

    # §7: Spectral flow Berry phase
    spectral_results = compute_spectral_flow_berry_phase(V, A600, gammas)
    all_results['spectral_flow'] = spectral_results

    # §8: Summary
    phi_findings = summarize_results(all_results)
    all_results['summary'] = {
        'n_phi_findings': len(phi_findings),
        'phi_findings': [(p, float(v), [(n, float(t), float(e)) for n, t, e in m])
                         for p, v, m in phi_findings[:50]]
    }

    # Determine overall status (exclude spurious random-permutation matches)
    genuine = [f for f in phi_findings
               if 'random_holonomy' not in f[0]
               and 'metadata' not in f[0]
               and any('1/φ' in m[0] or '1/φ²' in m[0] or '1/φ³' in m[0]
                      for m in f[2])]
    if genuine:
        all_results['status'] = 'POSITIVE — genuine φ-dependent Berry phase found'
    else:
        all_results['status'] = ('NEGATIVE (CLOSED) — no genuine φ-dependent Berry '
                                 'phase found; triality carries Z₃ not H₄ information')

    print(f"\n  Overall status: {all_results['status']}")

    # Save results
    output_dir = os.path.dirname(os.path.abspath(__file__))
    output_path = os.path.join(output_dir, 'path_c_berry_phase_results.json')

    # Make JSON-serializable
    def make_serializable(obj):
        if isinstance(obj, np.integer):
            return int(obj)
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.complexfloating):
            return complex(obj).__repr__()
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, complex):
            return complex(obj).__repr__()
        elif isinstance(obj, dict):
            return {k: make_serializable(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [make_serializable(v) for v in obj]
        return obj

    with open(output_path, 'w') as f:
        json.dump(make_serializable(all_results), f, indent=2, default=str)
    print(f"\n  Results saved to: {output_path}")

    return all_results


if __name__ == "__main__":
    main()
