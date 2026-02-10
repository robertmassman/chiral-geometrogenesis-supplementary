#!/usr/bin/env python3
"""
Path E: Direct Search for √5 − 2 in the 600-Cell
===================================================

Research Plan §11.2 Path E: Search for 1/φ³ = √5 − 2 ≈ 0.236068 appearing
as a single algebraic/geometric quantity in the 600-cell hierarchy.

If found, this provides the missing Factor 2 as part of a unified origin for
1/φ³, rather than requiring three independent 1/φ factors.

TESTS (from §11):
1. Characteristic polynomial coefficient ratios of adjacency matrices
2. Normalized determinants of adjacency submatrices
3. Coxeter element eigenvalue ratios (H₄ Coxeter number 30, F₄ number 12)
4. Full-chain projection products across 600-cell → 24-cell → 16-cell
5. Spectral gap ratios between H₄ and F₄ Laplacians
6. Combined spectral quantities: (1/5 projection) × (φ eigenvalue) products
7. Heat kernel trace ratios at special temperatures
8. Ihara zeta function evaluations
9. Spectral determinant ratios (products of nonzero eigenvalues)
10. Matrix resolvent traces at algebraic points

ENHANCED BY PATH A FINDINGS (§13.7):
- All projection norms = 1/5 (rational, from 24/120)
- All CG singular values = 1/√5 or rational
- φ lives in eigenvalues (6φ, 4φ, −4/φ, −6/φ), NOT in projections
- Hint: a product combining 1/5 with a φ-eigenvalue could yield √5 − 2

KEY IDENTITY: √5 − 2 = 1/φ³ = φ⁻³ = 2φ − 3

Related Documents:
- Research plan: docs/proofs/supporting/Derivation-Three-Phi-Factors-Explicit.md §11
- Prior exploration: verification/Phase3/explore_600_cell_phi_ratios.py
- Path A (closed): verification/Phase3/path_a_branching_coefficients.py
- Path B (closed): verification/Phase3/path_b_tunneling_amplitude.py
- Path F (completed): verification/Phase3/path_f_uniqueness_test.py

Verification Date: 2026-02-07
"""

import numpy as np
from itertools import product as iter_product, permutations
from collections import defaultdict
import json
import os
from datetime import datetime

# ============================================================
# CONSTANTS
# ============================================================
PHI = (1 + np.sqrt(5)) / 2
INV_PHI = 1.0 / PHI
SQRT5 = np.sqrt(5)
TARGET = SQRT5 - 2  # = 1/φ³ ≈ 0.236068

# Extended φ-related targets
PHI_TARGETS = {
    '√5−2 = 1/φ³':     SQRT5 - 2,
    '1/φ':              INV_PHI,
    '1/φ²':             1/PHI**2,
    'φ':                PHI,
    'φ²':               PHI**2,
    'φ³':               PHI**3,
    '√φ':               np.sqrt(PHI),
    '1/√φ':             1/np.sqrt(PHI),
    'φ/2':              PHI/2,
    '1/(2φ)':           1/(2*PHI),
    '2φ−3':             2*PHI - 3,   # = √5 − 2 (alternate form)
    'sin72°':           np.sin(np.radians(72)),
    'sin36°':           np.sin(np.radians(36)),
    'cos36°':           np.cos(np.radians(36)),
    'cos72°':           np.cos(np.radians(72)),
    '√5':               SQRT5,
    '1/√5':             1/SQRT5,
    '2/√5':             2/SQRT5,
    '√(2+φ)':           np.sqrt(2+PHI),
    '1/3':              1/3,
    '1/5':              1/5,
    '2/5':              2/5,
    '3/5':              3/5,
    '1/√2':             1/np.sqrt(2),
    '√3/2':             np.sqrt(3)/2,
    'ln(φ)':            np.log(PHI),
    '(√5−1)/4':         (SQRT5-1)/4,   # = cos(72°)
    'π/5':              np.pi/5,
}


def check_phi(value, threshold=0.003):
    """Check if value matches any φ-related target. Returns list of matches."""
    matches = []
    if abs(value) < 1e-10:
        return matches
    for name, target in PHI_TARGETS.items():
        if target > 1e-10 and abs(value - target) / target < threshold:
            err = abs(value - target) / target * 100
            matches.append((name, target, err))
    return matches


def check_target(value, target=None, threshold=0.003):
    """Check if value matches √5 − 2 specifically."""
    if target is None:
        target = TARGET
    if abs(target) < 1e-15:
        return abs(value) < 1e-10
    return abs(value - target) / abs(target) < threshold


def fmt_matches(matches):
    if not matches:
        return ""
    return " ← " + ", ".join(f"{n} (err {e:.4f}%)" for n, _, e in matches)


# ============================================================
# QUATERNION ALGEBRA (reused)
# ============================================================
def qmul(q1, q2):
    a1, b1, c1, d1 = q1
    a2, b2, c2, d2 = q2
    return np.array([
        a1*a2 - b1*b2 - c1*c2 - d1*d2,
        a1*b2 + b1*a2 + c1*d2 - d1*c2,
        a1*c2 - b1*d2 + c1*a2 + d1*b2,
        a1*d2 + b1*c2 - c1*b2 + d1*a2
    ])


def qconj(q):
    return np.array([q[0], -q[1], -q[2], -q[3]])


# ============================================================
# 600-CELL CONSTRUCTION (reused)
# ============================================================
def parity(perm):
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
    for i in range(4):
        for s in [1.0, -1.0]:
            v = [0.0, 0.0, 0.0, 0.0]
            v[i] = s
            verts.add(tuple(round(x, 10) for x in v))
    for signs in iter_product([0.5, -0.5], repeat=4):
        verts.add(tuple(round(x, 10) for x in signs))
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


def find_c0(vertices):
    indices = []
    for i, v in enumerate(vertices):
        av = np.abs(v)
        is_axis = (np.sum(av > 0.9) == 1 and np.sum(av < 0.01) == 3)
        is_half = np.allclose(av, 0.5, atol=0.01)
        if is_axis or is_half:
            indices.append(i)
    return indices


def find_24_cells(vertices, c0):
    copies = [sorted(c0)]
    assigned = set(c0)
    c0_verts = vertices[c0]
    for trial in range(len(vertices)):
        if trial in assigned:
            continue
        g = vertices[trial]
        coset = set()
        for t in c0_verts:
            prod = qmul(g, t)
            dists = np.linalg.norm(vertices - prod, axis=1)
            match = np.argmin(dists)
            if dists[match] < 0.01:
                coset.add(match)
        if len(coset) == 24 and not coset & assigned:
            copies.append(sorted(coset))
            assigned.update(coset)
        if len(copies) == 5:
            break
    return copies


def find_16_cells(vertices, cell_indices):
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
    components = []
    unvisited = set(range(n))
    while unvisited:
        start = min(unvisited)
        comp = set()
        queue = [start]
        while queue:
            node = queue.pop()
            if node in comp:
                continue
            comp.add(node)
            unvisited.discard(node)
            for nb in adj[node]:
                if nb not in comp:
                    queue.append(nb)
        components.append(sorted(comp))
    return components


def build_adjacency(vertices, edge_length, tol=0.05):
    n = len(vertices)
    A = np.zeros((n, n), dtype=float)
    for i in range(n):
        for j in range(i + 1, n):
            d = np.linalg.norm(vertices[i] - vertices[j])
            if abs(d - edge_length) < tol:
                A[i, j] = 1
                A[j, i] = 1
    return A


def eigendecompose(A, tol=1e-6):
    vals, vecs = np.linalg.eigh(A)
    eigenspaces = {}
    used = set()
    for i in range(len(vals)):
        if i in used:
            continue
        lam = vals[i]
        group = [i]
        for j in range(i + 1, len(vals)):
            if j not in used and abs(vals[j] - lam) < tol:
                group.append(j)
        for j in group:
            used.add(j)
        key = round(np.mean(vals[group]), 10)
        eigenspaces[key] = vecs[:, group]
    return eigenspaces


# ============================================================
# MAIN COMPUTATION
# ============================================================
def main():
    results = {
        "path": "E",
        "title": "Direct Search for √5 − 2 in the 600-Cell",
        "target": "√5 − 2 = 1/φ³ ≈ 0.236068",
        "timestamp": datetime.now().isoformat(),
        "sections": {},
        "all_hits": [],
        "near_misses": [],
    }

    print("=" * 70)
    print("PATH E: Direct Search for √5 − 2 in the 600-Cell")
    print("=" * 70)
    print(f"Target: √5 − 2 = 1/φ³ = {TARGET:.10f}")
    print()

    # ----------------------------------------------------------
    # BUILD POLYTOPES
    # ----------------------------------------------------------
    print("Building 600-cell...")
    verts_600 = build_600_cell()
    assert len(verts_600) == 120, f"Expected 120 vertices, got {len(verts_600)}"
    print(f"  600-cell: {len(verts_600)} vertices ✓")

    c0_idx = find_c0(verts_600)
    assert len(c0_idx) == 24, f"Expected 24 C₀ vertices, got {len(c0_idx)}"
    verts_24 = verts_600[c0_idx]
    print(f"  24-cell C₀: {len(c0_idx)} vertices ✓")

    copies_24 = find_24_cells(verts_600, c0_idx)
    assert len(copies_24) == 5, f"Expected 5 copies, got {len(copies_24)}"
    print(f"  24-cell copies: {len(copies_24)} ✓")

    sixteens = find_16_cells(verts_600, c0_idx)
    assert len(sixteens) == 3, f"Expected 3 sixteen-cells, got {len(sixteens)}"
    verts_16 = verts_24[sixteens[0]]
    print(f"  16-cells in C₀: {len(sixteens)} × {len(sixteens[0])} vertices ✓")

    # Build adjacency matrices
    print("\nBuilding adjacency matrices...")
    A_600 = build_adjacency(verts_600, INV_PHI)
    deg_600 = A_600.sum(axis=1)
    assert np.allclose(deg_600, 12), "600-cell should be 12-regular"
    print(f"  A_600: {A_600.shape}, degree 12 ✓")

    A_24 = build_adjacency(verts_24, 1.0)
    deg_24 = A_24.sum(axis=1)
    assert np.allclose(deg_24, 8), "24-cell should be 8-regular"
    print(f"  A_24: {A_24.shape}, degree 8 ✓")

    A_16 = build_adjacency(verts_16, np.sqrt(2))
    deg_16 = A_16.sum(axis=1)
    assert np.allclose(deg_16, 6), "16-cell should be 6-regular"
    print(f"  A_16: {A_16.shape}, degree 6 ✓")

    # Graph Laplacians: L = D − A
    L_600 = np.diag(deg_600) - A_600
    L_24 = np.diag(deg_24) - A_24
    L_16 = np.diag(deg_16) - A_16

    # Eigendecompositions
    print("\nComputing eigendecompositions...")
    es_600 = eigendecompose(A_600)
    es_24 = eigendecompose(A_24)
    es_16 = eigendecompose(A_16)

    eigs_600 = sorted(es_600.keys())
    eigs_24 = sorted(es_24.keys())
    eigs_16 = sorted(es_16.keys())

    print(f"  A_600 eigenvalues: {[f'{e:.4f}' for e in eigs_600]}")
    print(f"  A_24  eigenvalues: {[f'{e:.4f}' for e in eigs_24]}")
    print(f"  A_16  eigenvalues: {[f'{e:.4f}' for e in eigs_16]}")

    eig_mults_600 = {round(k, 4): es_600[k].shape[1] for k in eigs_600}
    eig_mults_24 = {round(k, 4): es_24[k].shape[1] for k in eigs_24}
    eig_mults_16 = {round(k, 4): es_16[k].shape[1] for k in eigs_16}

    results["sections"]["polytope_construction"] = {
        "600_cell_vertices": 120,
        "24_cell_vertices": 24,
        "16_cell_vertices": 8,
        "A_600_eigenvalues": {str(k): v for k, v in eig_mults_600.items()},
        "A_24_eigenvalues": {str(k): v for k, v in eig_mults_24.items()},
        "A_16_eigenvalues": {str(k): v for k, v in eig_mults_16.items()},
    }

    def record_hit(section, description, value, exact_match, error_pct):
        entry = {
            "section": section,
            "description": description,
            "value": float(value),
            "target": float(TARGET),
            "error_pct": float(error_pct),
            "exact": exact_match,
        }
        if exact_match or error_pct < 0.3:
            results["all_hits"].append(entry)
            print(f"  ★★★ HIT: {description} = {value:.10f} (err {error_pct:.4f}%)")
        elif error_pct < 5.0:
            results["near_misses"].append(entry)
            print(f"  ☆ NEAR: {description} = {value:.10f} (err {error_pct:.2f}%)")

    def scan_value(section, description, value):
        """Check a value against √5−2 and all φ targets. Record if hit."""
        if abs(value) < 1e-12 or not np.isfinite(value):
            return
        err = abs(value - TARGET) / TARGET * 100
        if err < 5.0:
            exact = err < 0.01
            record_hit(section, description, value, exact, err)
        # Also check 1/value, |value|, value² etc.
        for transform, label in [
            (abs(value), f"|{description}|"),
            (1/abs(value) if abs(value) > 1e-10 else None, f"1/|{description}|"),
            (value**2, f"({description})²"),
            (abs(value)**0.5 if value > 0 else None, f"√({description})"),
        ]:
            if transform is not None and np.isfinite(transform):
                err2 = abs(transform - TARGET) / TARGET * 100
                if err2 < 5.0:
                    record_hit(section, f"{label}", transform, err2 < 0.01, err2)

    # ==============================================================
    # §1: ADJACENCY EIGENVALUE RATIOS
    # ==============================================================
    print("\n" + "=" * 70)
    print("§1: Adjacency Eigenvalue Ratios")
    print("=" * 70)

    sec1 = {"eigenvalue_ratios": [], "hits": []}

    # All pairwise ratios of 600-cell eigenvalues
    nonzero_600 = [e for e in eigs_600 if abs(e) > 1e-10]
    print(f"\n  Non-zero A_600 eigenvalues: {[f'{e:.6f}' for e in nonzero_600]}")

    for i, ei in enumerate(nonzero_600):
        for j, ej in enumerate(nonzero_600):
            if i == j:
                continue
            ratio = ei / ej
            m = check_phi(abs(ratio))
            entry = {"ei": round(ei, 6), "ej": round(ej, 6),
                     "ratio": round(ratio, 10)}
            if m:
                entry["matches"] = [(n, round(t, 6), round(e, 4)) for n, t, e in m]
            sec1["eigenvalue_ratios"].append(entry)
            scan_value("§1", f"A_600 eig ratio {ei:.4f}/{ej:.4f}", ratio)
            scan_value("§1", f"|A_600 eig ratio {ei:.4f}/{ej:.4f}|", abs(ratio))

    # Cross-level eigenvalue ratios: A_600 vs A_24 vs A_16
    print("\n  Cross-level eigenvalue ratios (A_600 / A_24, A_600 / A_16, etc.):")
    nonzero_24 = [e for e in eigs_24 if abs(e) > 1e-10]
    nonzero_16 = [e for e in eigs_16 if abs(e) > 1e-10]

    for ei in nonzero_600:
        for ej in nonzero_24:
            ratio = ei / ej
            scan_value("§1", f"A_600({ei:.4f})/A_24({ej:.4f})", ratio)
        for ej in nonzero_16:
            ratio = ei / ej
            scan_value("§1", f"A_600({ei:.4f})/A_16({ej:.4f})", ratio)
    for ei in nonzero_24:
        for ej in nonzero_16:
            ratio = ei / ej
            scan_value("§1", f"A_24({ei:.4f})/A_16({ej:.4f})", ratio)

    # Sums and differences of eigenvalue pairs
    print("\n  Eigenvalue sums/differences:")
    for i, ei in enumerate(eigs_600):
        for j, ej in enumerate(eigs_600):
            if i >= j:
                continue
            for val, label in [
                (ei + ej, f"sum({ei:.4f}+{ej:.4f})"),
                (ei - ej, f"diff({ei:.4f}-{ej:.4f})"),
                (ei * ej, f"prod({ei:.4f}×{ej:.4f})"),
            ]:
                scan_value("§1", f"A_600 {label}", val)

    results["sections"]["S1_eigenvalue_ratios"] = sec1
    print(f"\n  §1 complete.")

    # ==============================================================
    # §2: CHARACTERISTIC POLYNOMIAL COEFFICIENT RATIOS
    # ==============================================================
    print("\n" + "=" * 70)
    print("§2: Characteristic Polynomial Coefficient Ratios")
    print("=" * 70)

    sec2 = {"hits": []}

    # For large matrices, compute characteristic polynomial from eigenvalues
    # p(x) = Π(x - λ_i) → coefficients via Vieta's formulas
    # Direct charpoly of 120×120 is feasible with numpy

    # 600-cell: Use eigenvalues (with multiplicity) for symbolic analysis
    all_eigs_600 = []
    for lam, space in es_600.items():
        all_eigs_600.extend([lam] * space.shape[1])
    all_eigs_600 = np.array(sorted(all_eigs_600))

    # Elementary symmetric polynomials e_k = sum of products of k eigenvalues
    # These are the characteristic polynomial coefficients (up to sign)
    # For a 120×120 matrix, computing all e_k is expensive.
    # Focus on low-order: e_1 (trace), e_2, and ratios involving known eigenvalues.

    trace_600 = np.sum(all_eigs_600)
    trace_sq_600 = np.sum(all_eigs_600**2)
    trace_cub_600 = np.sum(all_eigs_600**3)
    trace_4th_600 = np.sum(all_eigs_600**4)

    all_eigs_24 = []
    for lam, space in es_24.items():
        all_eigs_24.extend([lam] * space.shape[1])
    all_eigs_24 = np.array(sorted(all_eigs_24))

    all_eigs_16 = []
    for lam, space in es_16.items():
        all_eigs_16.extend([lam] * space.shape[1])
    all_eigs_16 = np.array(sorted(all_eigs_16))

    # Trace ratios (power sums = Tr(A^k))
    traces = {}
    for label, eigs in [("600", all_eigs_600), ("24", all_eigs_24), ("16", all_eigs_16)]:
        traces[label] = {}
        for k in range(1, 7):
            traces[label][k] = np.sum(eigs**k)

    print("\n  Power sum traces Tr(A^k):")
    for label in ["600", "24", "16"]:
        print(f"    {label}: " + ", ".join(f"k={k}: {traces[label][k]:.4f}" for k in range(1, 7)))

    # Cross-level trace ratios
    print("\n  Cross-level trace ratios Tr(A_i^k) / Tr(A_j^k):")
    for k in range(1, 7):
        for li, lj in [("600", "24"), ("600", "16"), ("24", "16")]:
            if abs(traces[lj][k]) > 1e-10:
                ratio = traces[li][k] / traces[lj][k]
                scan_value("§2", f"Tr(A_{li}^{k})/Tr(A_{lj}^{k})", ratio)
                print(f"    Tr(A_{li}^{k})/Tr(A_{lj}^{k}) = {ratio:.10f}")

    # Normalized traces: Tr(A^k) / n^k or Tr(A^k) / Tr(A^2)^{k/2}
    print("\n  Normalized trace ratios:")
    for label, eigs, n in [("600", all_eigs_600, 120), ("24", all_eigs_24, 24), ("16", all_eigs_16, 8)]:
        for k in range(2, 7):
            norm_trace = traces[label][k] / n**k
            scan_value("§2", f"Tr(A_{label}^{k})/n^{k}", norm_trace)
            if abs(traces[label][2]) > 1e-10:
                ratio = traces[label][k] / traces[label][2]**(k/2)
                scan_value("§2", f"Tr(A_{label}^{k})/Tr(A_{label}^2)^{k/2}", ratio)

    # Ratios of consecutive traces
    print("\n  Consecutive trace ratios Tr(A^{k+1})/Tr(A^k):")
    for label in ["600", "24", "16"]:
        for k in range(2, 6):
            if abs(traces[label][k]) > 1e-10:
                ratio = traces[label][k+1] / traces[label][k]
                scan_value("§2", f"Tr(A_{label}^{k+1})/Tr(A_{label}^{k})", ratio)

    results["sections"]["S2_characteristic_polynomial"] = sec2

    # ==============================================================
    # §3: RESTRICTED ADJACENCY MATRIX SPECTRA
    # ==============================================================
    print("\n" + "=" * 70)
    print("§3: Restricted Adjacency Matrix Spectra")
    print("=" * 70)

    sec3 = {"hits": []}

    # A_600 restricted to C₀ vertices (24×24 submatrix)
    A_600_on_C0 = A_600[np.ix_(c0_idx, c0_idx)]
    eigs_restr = np.linalg.eigvalsh(A_600_on_C0)
    eigs_restr_sorted = np.sort(eigs_restr)

    print(f"\n  A_600 restricted to C₀ (24×24) eigenvalues:")
    print(f"    {np.round(eigs_restr_sorted, 6)}")

    for i, e in enumerate(eigs_restr_sorted):
        scan_value("§3", f"A_600|_C0 eigenvalue [{i}]", e)
        m = check_phi(abs(e))
        if m:
            print(f"    λ[{i}] = {e:.6f}{fmt_matches(m)}")

    # Eigenvalue ratios of restricted matrix
    nz_restr = [e for e in eigs_restr_sorted if abs(e) > 0.01]
    for i, ei in enumerate(nz_restr):
        for j, ej in enumerate(nz_restr):
            if i != j:
                scan_value("§3", f"A_600|_C0 ratio λ[{i}]/λ[{j}]", ei/ej)

    # A_600 restricted to one 16-cell (8×8 submatrix)
    sixteen_global = [c0_idx[i] for i in sixteens[0]]
    A_600_on_16 = A_600[np.ix_(sixteen_global, sixteen_global)]
    eigs_restr_16 = np.sort(np.linalg.eigvalsh(A_600_on_16))

    print(f"\n  A_600 restricted to Γ₀ (8×8) eigenvalues:")
    print(f"    {np.round(eigs_restr_16, 6)}")
    for i, e in enumerate(eigs_restr_16):
        scan_value("§3", f"A_600|_Γ0 eigenvalue [{i}]", e)

    # Determinants of restricted matrices
    det_C0 = np.linalg.det(A_600_on_C0)
    det_16 = np.linalg.det(A_600_on_16)
    print(f"\n  det(A_600|_C0) = {det_C0:.6f}")
    print(f"  det(A_600|_Γ0) = {det_16:.6f}")
    scan_value("§3", "det(A_600|_C0)", det_C0)
    scan_value("§3", "det(A_600|_Γ0)", det_16)
    if abs(det_C0) > 1e-10 and abs(det_16) > 1e-10:
        scan_value("§3", "det(A_600|_Γ0)/det(A_600|_C0)", det_16/det_C0)

    # Cross-Gram matrix between 24-cell copies
    print("\n  Cross-Gram matrices between 24-cell copies:")
    for i in range(len(copies_24)):
        for j in range(i+1, len(copies_24)):
            Vi = verts_600[copies_24[i]]  # 24×4
            Vj = verts_600[copies_24[j]]  # 24×4
            G = Vi @ Vj.T                  # 24×24
            try:
                svs = np.linalg.svd(G, compute_uv=False)
                for k, sv in enumerate(svs[:4]):
                    scan_value("§3", f"CrossGram C_{i}/C_{j} sv[{k}]", sv)
            except np.linalg.LinAlgError:
                pass

    # Determinant ratios
    det_24 = np.linalg.det(A_24)
    det_16_own = np.linalg.det(A_16)
    print(f"\n  det(A_24) = {det_24:.6f}")
    print(f"  det(A_16) = {det_16_own:.6f}")
    scan_value("§3", "det(A_24)", det_24)
    scan_value("§3", "det(A_16)", det_16_own)

    results["sections"]["S3_restricted_spectra"] = sec3

    # ==============================================================
    # §4: COXETER ELEMENT ANALYSIS
    # ==============================================================
    print("\n" + "=" * 70)
    print("§4: Coxeter Element Eigenvalue Ratios")
    print("=" * 70)

    sec4 = {"hits": []}

    # Construct H₄ and F₄ Coxeter elements from Gram matrices
    # H₄ Gram matrix: G_ij = -cos(π/m_ij), G_ii = 1
    # Coxeter diagram: α₁ —5— α₂ — α₃ — α₄

    G_H4 = np.array([
        [1.0,     -PHI/2,  0.0,   0.0],
        [-PHI/2,  1.0,    -0.5,   0.0],
        [0.0,    -0.5,     1.0,  -0.5],
        [0.0,     0.0,    -0.5,   1.0],
    ])

    # F₄ Gram matrix: α₁ — α₂ —4— α₃ — α₄
    sqrt2_half = np.sqrt(2) / 2
    G_F4 = np.array([
        [1.0,   -0.5,       0.0,   0.0],
        [-0.5,   1.0,  -sqrt2_half, 0.0],
        [0.0,  -sqrt2_half,  1.0,  -0.5],
        [0.0,    0.0,       -0.5,   1.0],
    ])

    def coxeter_element_from_gram(G):
        """Construct the Coxeter element c = s₁ s₂ s₃ s₄ from Gram matrix."""
        L = np.linalg.cholesky(G)
        # Simple roots are rows of L
        roots = L.copy()
        # Reflection s_i(x) = x - 2(x·α_i)/(α_i·α_i) * α_i
        # In the root basis: s_i = I - 2 α_i α_i^T / (α_i · α_i)
        n = G.shape[0]
        C = np.eye(n)
        for i in range(n):
            alpha = roots[i]
            norm_sq = np.dot(alpha, alpha)
            S = np.eye(n) - 2 * np.outer(alpha, alpha) / norm_sq
            C = S @ C
        return C

    C_H4 = coxeter_element_from_gram(G_H4)
    C_F4 = coxeter_element_from_gram(G_F4)

    # Eigenvalues of Coxeter elements
    eig_CH4 = np.linalg.eigvals(C_H4)
    eig_CF4 = np.linalg.eigvals(C_F4)

    # H₄: Coxeter number h=30, exponents {1, 11, 19, 29}
    # Eigenvalues should be e^{2πi·m_k/30}
    print(f"\n  H₄ Coxeter element eigenvalues:")
    phases_H4 = np.angle(eig_CH4) / (2 * np.pi)  # as fraction of 2π
    for i, (ev, ph) in enumerate(zip(eig_CH4, phases_H4)):
        print(f"    λ[{i}] = {ev:.6f}, phase = {ph:.6f} × 2π = {ph*30:.1f}/30")

    print(f"\n  F₄ Coxeter element eigenvalues:")
    phases_F4 = np.angle(eig_CF4) / (2 * np.pi)
    for i, (ev, ph) in enumerate(zip(eig_CF4, phases_F4)):
        print(f"    λ[{i}] = {ev:.6f}, phase = {ph:.6f} × 2π = {ph*12:.1f}/12")

    # Coxeter numbers and exponents
    h_H4, h_F4 = 30, 12
    exp_H4 = [1, 11, 19, 29]
    exp_F4 = [1, 5, 7, 11]
    deg_H4 = [2, 12, 20, 30]
    deg_F4 = [2, 6, 8, 12]

    print(f"\n  Coxeter number ratio: h_H4/h_F4 = {h_H4}/{h_F4} = {h_H4/h_F4}")

    # Ratios of Coxeter numbers and exponents
    coxeter_quantities = {
        "h_H4/h_F4": h_H4 / h_F4,
        "h_F4/h_H4": h_F4 / h_H4,
        "(h_H4-h_F4)/h_H4": (h_H4-h_F4) / h_H4,
        "(h_H4-h_F4)/h_F4": (h_H4-h_F4) / h_F4,
        "|W_H4|/|W_F4|": 14400 / 1152,
        "|W_F4|/|W_H4|": 1152 / 14400,
    }

    # Exponent products and sums
    prod_exp_H4 = np.prod(exp_H4)
    prod_exp_F4 = np.prod(exp_F4)
    sum_exp_H4 = np.sum(exp_H4)
    sum_exp_F4 = np.sum(exp_F4)

    coxeter_quantities.update({
        "Π(exp_H4)/Π(exp_F4)": prod_exp_H4 / prod_exp_F4,
        "Σ(exp_H4)/Σ(exp_F4)": sum_exp_H4 / sum_exp_F4,
        "Π(exp_H4)": float(prod_exp_H4),
        "Π(exp_F4)": float(prod_exp_F4),
        "Σ(exp_H4)": float(sum_exp_H4),
        "Σ(exp_F4)": float(sum_exp_F4),
    })

    # Degree products
    prod_deg_H4 = np.prod(deg_H4)
    prod_deg_F4 = np.prod(deg_F4)
    coxeter_quantities.update({
        "Π(deg_H4)/Π(deg_F4)": prod_deg_H4 / prod_deg_F4,
        "Π(deg_F4)/Π(deg_H4)": prod_deg_F4 / prod_deg_H4,
        "|W_H4| = Π(deg)": float(prod_deg_H4),  # should be 14400
        "|W_F4| = Π(deg)": float(prod_deg_F4),   # should be 1152
    })

    # Coxeter element traces
    tr_CH4 = np.real(np.trace(C_H4))
    tr_CF4 = np.real(np.trace(C_F4))
    coxeter_quantities.update({
        "Tr(C_H4)": tr_CH4,
        "Tr(C_F4)": tr_CF4,
        "Re(det(C_H4))": np.real(np.linalg.det(C_H4)),
        "Re(det(C_F4))": np.real(np.linalg.det(C_F4)),
    })
    if abs(tr_CF4) > 1e-10:
        coxeter_quantities["Tr(C_H4)/Tr(C_F4)"] = tr_CH4 / tr_CF4

    print("\n  Coxeter-related quantities:")
    for name, val in coxeter_quantities.items():
        m = check_phi(abs(val))
        tag = fmt_matches(m) if m else ""
        print(f"    {name} = {val:.10f}{tag}")
        scan_value("§4", name, val)

    # Ratios between Coxeter element eigenvalue PHASES
    print("\n  Coxeter element phase ratios:")
    for i, p1 in enumerate(phases_H4):
        for j, p2 in enumerate(phases_F4):
            if abs(p2) > 1e-10:
                ratio = p1 / p2
                scan_value("§4", f"phase_H4[{i}]/phase_F4[{j}]", ratio)

    # Coxeter element cos/sin of phases
    print("\n  Trigonometric values of Coxeter phases:")
    for label, phases in [("H₄", phases_H4), ("F₄", phases_F4)]:
        for i, ph in enumerate(phases):
            c_val = np.cos(2*np.pi*ph)
            s_val = np.sin(2*np.pi*ph)
            scan_value("§4", f"cos(2π·phase_{label}[{i}])", c_val)
            scan_value("§4", f"sin(2π·phase_{label}[{i}])", s_val)

    # Products of pairs of Coxeter eigenvalues (real parts)
    for i in range(4):
        for j in range(4):
            prod = np.real(eig_CH4[i] * np.conj(eig_CF4[j]))
            scan_value("§4", f"Re(λ_H4[{i}]·λ*_F4[{j}])", prod)

    results["sections"]["S4_coxeter_elements"] = sec4

    # ==============================================================
    # §5: FULL-CHAIN PROJECTION PRODUCTS
    # ==============================================================
    print("\n" + "=" * 70)
    print("§5: Full-Chain Projection Products")
    print("=" * 70)

    sec5 = {"hits": []}

    # Products of geometric ratios across the full 600→24→16 chain
    # Edge ratios
    e_600 = INV_PHI
    e_24 = 1.0
    e_16 = np.sqrt(2)
    r_600 = 1.0  # circumradius
    r_24 = 1.0
    r_16 = 1.0

    # Volume ratios (from existing computation)
    # V_16/V_24 = 1/3, V_24/V_600 computed later
    # For now, compute volumes using the Cayley-Menger determinant approach
    # or simply use known values

    chain_products = {
        "e_600/e_24 × e_24/e_16": (e_600/e_24) * (e_24/e_16),
        "e_600/e_16": e_600 / e_16,
        "(e_600/e_24)² × (e_24/e_16)": (e_600/e_24)**2 * (e_24/e_16),
        "(e_600/e_24) × (e_24/e_16)²": (e_600/e_24) * (e_24/e_16)**2,
        "e_600²/e_16": e_600**2 / e_16,
        "e_600/e_16²": e_600 / e_16**2,
        "1/5 × 1/φ": 0.2 * INV_PHI,    # projection × edge ratio
        "1/5 × 1/φ²": 0.2 / PHI**2,
        "1/5 × φ": 0.2 * PHI,
        "1/3 × 1/φ": (1/3) * INV_PHI,  # 16-cell fraction × edge ratio
        "1/3 × 1/φ²": (1/3) / PHI**2,
    }

    # Degree ratios as "projection weights"
    chain_products.update({
        "deg_600/deg_24 / n_600×n_24": (12/8) / (120*24),
        "(n_24/n_600) × (n_16/n_24)": (24/120) * (8/24),
        "(n_24/n_600)": 24/120,
        "(n_16/n_24)": 8/24,
        "(n_16/n_600)": 8/120,
        "n_24²/(n_600×n_16)": 24**2 / (120*8),
    })

    # Spectral radius ratios
    sr_600 = max(abs(e) for e in eigs_600)
    sr_24 = max(abs(e) for e in eigs_24)
    sr_16 = max(abs(e) for e in eigs_16)
    chain_products.update({
        "ρ(A_24)/ρ(A_600)": sr_24 / sr_600,
        "ρ(A_16)/ρ(A_600)": sr_16 / sr_600,
        "ρ(A_16)/ρ(A_24)": sr_16 / sr_24,
        "ρ(A_24)×ρ(A_16)/(ρ(A_600))²": sr_24*sr_16 / sr_600**2,
    })

    print("\n  Full-chain products:")
    for name, val in chain_products.items():
        m = check_phi(abs(val))
        tag = fmt_matches(m) if m else ""
        print(f"    {name} = {val:.10f}{tag}")
        scan_value("§5", name, val)

    results["sections"]["S5_chain_products"] = sec5

    # ==============================================================
    # §6: SPECTRAL GAP RATIOS
    # ==============================================================
    print("\n" + "=" * 70)
    print("§6: Spectral Gap Ratios (Laplacian)")
    print("=" * 70)

    sec6 = {"hits": []}

    # Laplacian eigenvalues
    leigs_600 = np.sort(np.linalg.eigvalsh(L_600))
    leigs_24 = np.sort(np.linalg.eigvalsh(L_24))
    leigs_16 = np.sort(np.linalg.eigvalsh(L_16))

    print(f"\n  L_600 eigenvalues (first 10): {np.round(leigs_600[:10], 6)}")
    print(f"  L_600 eigenvalues (last 5): {np.round(leigs_600[-5:], 6)}")
    print(f"  L_24  eigenvalues: {np.round(leigs_24, 6)}")
    print(f"  L_16  eigenvalues: {np.round(leigs_16, 6)}")

    # Spectral gaps (smallest nonzero eigenvalue)
    gap_600 = leigs_600[leigs_600 > 0.01].min()
    gap_24 = leigs_24[leigs_24 > 0.01].min()
    gap_16 = leigs_16[leigs_16 > 0.01].min()

    gap_quantities = {
        "gap_600": gap_600,
        "gap_24": gap_24,
        "gap_16": gap_16,
        "gap_600/gap_24": gap_600 / gap_24,
        "gap_24/gap_600": gap_24 / gap_600,
        "gap_600/gap_16": gap_600 / gap_16,
        "gap_16/gap_600": gap_16 / gap_600,
        "gap_24/gap_16": gap_24 / gap_16,
        "gap_16/gap_24": gap_16 / gap_24,
        "gap_600×gap_16/gap_24²": gap_600*gap_16/gap_24**2,
    }

    # Spectral widths
    max_L_600 = leigs_600.max()
    max_L_24 = leigs_24.max()
    max_L_16 = leigs_16.max()
    gap_quantities.update({
        "max_L_600": max_L_600,
        "max_L_24": max_L_24,
        "max_L_16": max_L_16,
        "bandwidth_600/bandwidth_24": (max_L_600 - gap_600)/(max_L_24 - gap_24),
        "bandwidth_24/bandwidth_16": (max_L_24 - gap_24)/(max_L_16 - gap_16),
    })

    print("\n  Spectral gap quantities:")
    for name, val in gap_quantities.items():
        m = check_phi(abs(val))
        tag = fmt_matches(m) if m else ""
        print(f"    {name} = {val:.10f}{tag}")
        scan_value("§6", name, val)

    # All unique Laplacian eigenvalue ratios
    print("\n  Laplacian eigenvalue ratios (600-cell unique):")
    unique_L600 = sorted(set(np.round(leigs_600, 4)))
    nz_L600 = [e for e in unique_L600 if e > 0.01]
    for i, ei in enumerate(nz_L600):
        for j, ej in enumerate(nz_L600):
            if i != j:
                scan_value("§6", f"L_600 ratio {ei:.4f}/{ej:.4f}", ei/ej)

    results["sections"]["S6_spectral_gaps"] = sec6

    # ==============================================================
    # §7: COMBINED SPECTRAL QUANTITIES (§13.7 Hint)
    # ==============================================================
    print("\n" + "=" * 70)
    print("§7: Combined Spectral Quantities (1/5 × φ-eigenvalue products)")
    print("=" * 70)

    sec7 = {"hits": []}

    # Path A found: projection norms = 1/5, CG singular values = 1/√5
    # φ-eigenvalues: 6φ, 4φ, -4/φ, -6/φ
    # Hint: "a product combining 1/5 with a φ-eigenvalue could yield √5−2"

    proj_norm = 1/5  # = 24/120, from vertex transitivity
    cg_sv = 1/SQRT5
    phi_eigs = [6*PHI, 4*PHI, -4/PHI, -6/PHI]
    all_600_unique_eigs = sorted(set(np.round(all_eigs_600, 6)))

    combinations_to_test = {}

    # 1/5 × normalized eigenvalues
    for ev in phi_eigs:
        combinations_to_test[f"(1/5) × {ev:.4f}/max_eig"] = proj_norm * ev / sr_600
        combinations_to_test[f"(1/5) × {ev:.4f}/deg"] = proj_norm * ev / 12
        combinations_to_test[f"(1/5) × |{ev:.4f}|/h_H4"] = proj_norm * abs(ev) / h_H4
        combinations_to_test[f"(1/5) × |{ev:.4f}|/h_F4"] = proj_norm * abs(ev) / h_F4

    # 1/√5 × normalized eigenvalues
    for ev in phi_eigs:
        combinations_to_test[f"(1/√5) × {ev:.4f}/max_eig"] = cg_sv * ev / sr_600
        combinations_to_test[f"(1/√5) × |{ev:.4f}|/deg"] = cg_sv * abs(ev) / 12

    # Products of projection norm with all eigenvalue ratios
    for i, ei in enumerate(all_600_unique_eigs):
        if abs(ei) < 0.01:
            continue
        for ej in all_600_unique_eigs:
            if abs(ej) < 0.01 or ei == ej:
                continue
            val = proj_norm * ei / ej
            combinations_to_test[f"(1/5)×({ei:.4f}/{ej:.4f})"] = val

    # 1/5 × Laplacian eigenvalues
    for le in nz_L600:
        combinations_to_test[f"(1/5) × L_eig({le:.4f})/max_L"] = proj_norm * le / max_L_600

    # √5 related: √5 × 1/5 × eigenvalue products
    for ev in phi_eigs:
        combinations_to_test[f"√5 × (1/5)² × |{ev:.4f}|"] = SQRT5 * proj_norm**2 * abs(ev)
        combinations_to_test[f"(1/5) × |{ev:.4f}| × (1/√5)"] = proj_norm * abs(ev) * cg_sv

    # Key algebraic test: √5 − 2 = √5 × (1 − 2/√5)
    # Can we get (1 − 2/√5) from spectral data?
    combinations_to_test["1 − 2/√5"] = 1 - 2/SQRT5
    combinations_to_test["√5 × (1 − 2/√5)"] = SQRT5 * (1 - 2/SQRT5)

    # Direct products of 1/5 with φ^n
    for n in range(-4, 5):
        val = proj_norm * PHI**n
        combinations_to_test[f"(1/5) × φ^{n}"] = val
        # Also: 1/5 × (φ^n ± something)
        for m in range(-4, 5):
            if n != m:
                val2 = proj_norm * (PHI**n + PHI**m)
                combinations_to_test[f"(1/5) × (φ^{n}+φ^{m})"] = val2
                val3 = proj_norm * (PHI**n - PHI**m)
                combinations_to_test[f"(1/5) × (φ^{n}-φ^{m})"] = val3

    # (1/√5)^a × φ^b for small a, b
    for a in range(1, 5):
        for b in range(-6, 7):
            val = (1/SQRT5)**a * PHI**b
            combinations_to_test[f"(1/√5)^{a} × φ^{b}"] = val

    print(f"\n  Testing {len(combinations_to_test)} combined spectral quantities...")
    hit_count = 0
    for name, val in combinations_to_test.items():
        if np.isfinite(val) and abs(val) > 1e-12:
            err = abs(val - TARGET) / TARGET * 100
            if err < 0.01:
                print(f"    ★★★ EXACT: {name} = {val:.10f} (err {err:.6f}%)")
                record_hit("§7", name, val, True, err)
                hit_count += 1
            elif err < 0.3:
                print(f"    ★★ CLOSE: {name} = {val:.10f} (err {err:.4f}%)")
                record_hit("§7", name, val, False, err)
                hit_count += 1
            elif err < 2.0:
                print(f"    ☆ NEAR: {name} = {val:.10f} (err {err:.2f}%)")
                hit_count += 1

    print(f"\n  §7: Found {hit_count} matches/near-misses")
    results["sections"]["S7_combined_spectral"] = sec7

    # ==============================================================
    # §8: HEAT KERNEL TRACE RATIOS
    # ==============================================================
    print("\n" + "=" * 70)
    print("§8: Heat Kernel Trace Ratios")
    print("=" * 70)

    sec8 = {"hits": []}

    # Heat kernel: K(t) = Tr(e^{-tL}) = Σ e^{-t·λ_k}
    # At t→0: K(t) → n (number of vertices)
    # At t→∞: K(t) → 1 (only zero mode survives)
    # Intermediate t may reveal interesting ratios

    t_values = np.concatenate([
        np.linspace(0.01, 0.1, 10),
        np.linspace(0.1, 1.0, 20),
        np.linspace(1.0, 5.0, 20),
        [np.log(PHI), 1/PHI, PHI, 1/PHI**2, PHI**2, np.pi/5, 2*np.pi/5],
    ])

    heat_ratios_found = []
    for t in sorted(set(t_values)):
        K_600 = np.sum(np.exp(-t * leigs_600))
        K_24 = np.sum(np.exp(-t * leigs_24))
        K_16 = np.sum(np.exp(-t * leigs_16))

        ratio_600_24 = K_600 / K_24
        ratio_24_16 = K_24 / K_16
        ratio_600_16 = K_600 / K_16

        for name, val in [
            (f"K_600/K_24 @ t={t:.4f}", ratio_600_24),
            (f"K_24/K_16 @ t={t:.4f}", ratio_24_16),
            (f"K_600/K_16 @ t={t:.4f}", ratio_600_16),
            (f"K_600/(K_24·K_16) @ t={t:.4f}", K_600/(K_24*K_16)),
            (f"(K_24/K_600)·(K_16/K_24) @ t={t:.4f}", (K_24/K_600)*(K_16/K_24)),
        ]:
            if np.isfinite(val) and abs(val) > 1e-12:
                err = abs(val - TARGET) / TARGET * 100
                if err < 2.0:
                    heat_ratios_found.append((name, val, err))
                    print(f"    {'★★★' if err < 0.01 else '☆'} {name} = {val:.10f} (err {err:.4f}%)")
                    record_hit("§8", name, val, err < 0.01, err)

    # Also: find t* where K_600(t)/K_24(t) = √5−2 (if it exists)
    print("\n  Searching for t* where heat kernel ratios = √5−2...")
    from scipy.optimize import brentq

    def heat_ratio_minus_target(t, eigs1, eigs2):
        K1 = np.sum(np.exp(-t * eigs1))
        K2 = np.sum(np.exp(-t * eigs2))
        return K1/K2 - TARGET

    for label, e1, e2 in [
        ("K_600/K_24", leigs_600, leigs_24),
        ("K_24/K_16", leigs_24, leigs_16),
    ]:
        # Scan for sign changes
        ts = np.linspace(0.001, 10.0, 1000)
        vals = [heat_ratio_minus_target(t, e1, e2) for t in ts]
        for i in range(len(vals)-1):
            if vals[i] * vals[i+1] < 0:
                try:
                    t_star = brentq(heat_ratio_minus_target, ts[i], ts[i+1],
                                    args=(e1, e2))
                    print(f"    Found t* = {t_star:.10f} where {label} = √5−2")
                    # Check if t* is a recognizable quantity
                    m = check_phi(t_star)
                    if m:
                        print(f"    t* matches: {fmt_matches(m)}")
                    scan_value("§8", f"t* for {label}=√5−2", t_star)
                except Exception:
                    pass

    results["sections"]["S8_heat_kernel"] = sec8

    # ==============================================================
    # §9: SPECTRAL DETERMINANT RATIOS
    # ==============================================================
    print("\n" + "=" * 70)
    print("§9: Spectral Determinant Ratios")
    print("=" * 70)

    sec9 = {"hits": []}

    # Spectral determinant = product of nonzero eigenvalues
    # For adjacency matrix:
    nz_eigs_600 = all_eigs_600[np.abs(all_eigs_600) > 0.01]
    nz_eigs_24 = all_eigs_24[np.abs(all_eigs_24) > 0.01]
    nz_eigs_16 = all_eigs_16[np.abs(all_eigs_16) > 0.01]

    # Use log-determinants to avoid overflow
    log_det_600 = np.sum(np.log(np.abs(nz_eigs_600)))
    log_det_24 = np.sum(np.log(np.abs(nz_eigs_24)))
    log_det_16 = np.sum(np.log(np.abs(nz_eigs_16)))

    print(f"\n  Log spectral determinants (adjacency, nonzero eigs):")
    print(f"    ln|det'(A_600)| = {log_det_600:.6f}")
    print(f"    ln|det'(A_24)|  = {log_det_24:.6f}")
    print(f"    ln|det'(A_16)|  = {log_det_16:.6f}")

    det_ratios = {
        "ln|det'(A_600)|/ln|det'(A_24)|": log_det_600 / log_det_24 if abs(log_det_24) > 1e-10 else float('inf'),
        "ln|det'(A_24)|/ln|det'(A_16)|": log_det_24 / log_det_16 if abs(log_det_16) > 1e-10 else float('inf'),
        "ln|det'(A_600)|/ln|det'(A_16)|": log_det_600 / log_det_16 if abs(log_det_16) > 1e-10 else float('inf'),
        "(ln|det'(A_600)| - ln|det'(A_24)|)/ln|det'(A_16)|": (log_det_600 - log_det_24) / log_det_16 if abs(log_det_16) > 1e-10 else float('inf'),
    }

    # Laplacian spectral determinant (= number of spanning trees × n)
    nz_L600 = leigs_600[leigs_600 > 0.01]
    nz_L24 = leigs_24[leigs_24 > 0.01]
    nz_L16 = leigs_16[leigs_16 > 0.01]

    log_det_L600 = np.sum(np.log(nz_L600))
    log_det_L24 = np.sum(np.log(nz_L24))
    log_det_L16 = np.sum(np.log(nz_L16))

    print(f"\n  Log spectral determinants (Laplacian, nonzero eigs):")
    print(f"    ln(det'(L_600)) = {log_det_L600:.6f}")
    print(f"    ln(det'(L_24))  = {log_det_L24:.6f}")
    print(f"    ln(det'(L_16))  = {log_det_L16:.6f}")

    # Number of spanning trees: τ = det'(L)/n
    tau_600 = np.exp(log_det_L600) / 120
    tau_24 = np.exp(log_det_L24) / 24
    tau_16 = np.exp(log_det_L16) / 8
    print(f"\n  Spanning tree counts (Kirchhoff):")
    print(f"    τ(600-cell) = {tau_600:.6e}")
    print(f"    τ(24-cell)  = {tau_24:.6e}")
    print(f"    τ(16-cell)  = {tau_16:.6e}")

    det_ratios.update({
        "ln(det'(L_600))/ln(det'(L_24))": log_det_L600 / log_det_L24,
        "ln(det'(L_24))/ln(det'(L_16))": log_det_L24 / log_det_L16,
        "ln(τ_24)/ln(τ_600)": np.log(tau_24) / np.log(tau_600) if tau_600 > 0 else float('inf'),
    })

    # Normalized spectral determinants
    det_ratios.update({
        "det'(A_600)^(1/95)/det'(A_24)^(1/24)": np.exp(log_det_600/len(nz_eigs_600) - log_det_24/len(nz_eigs_24)),
        "det'(L_600)^(1/119)/det'(L_24)^(1/23)": np.exp(log_det_L600/len(nz_L600) - log_det_L24/len(nz_L24)),
    })

    print("\n  Spectral determinant ratios:")
    for name, val in det_ratios.items():
        if np.isfinite(val):
            m = check_phi(abs(val))
            tag = fmt_matches(m) if m else ""
            print(f"    {name} = {val:.10f}{tag}")
            scan_value("§9", name, val)

    results["sections"]["S9_spectral_determinants"] = sec9

    # ==============================================================
    # §10: IHARA ZETA FUNCTION
    # ==============================================================
    print("\n" + "=" * 70)
    print("§10: Ihara Zeta Function Values")
    print("=" * 70)

    sec10 = {"hits": []}

    # For a q+1-regular graph: Z(u)^{-1} = (1-u²)^{r-1} det(I - Au + qu²I)
    # where r = |E| - |V| + 1 = rank of cycle space

    def ihara_det(A, q, u):
        """Compute det(I - uA + qu²I) for the Ihara zeta function."""
        n = A.shape[0]
        M = np.eye(n) - u*A + q*u**2*np.eye(n)
        return np.linalg.det(M)

    # Evaluate at algebraically interesting u values
    u_values = {
        "1/φ": INV_PHI,
        "1/φ²": 1/PHI**2,
        "1/φ³": TARGET,
        "sin36°": np.sin(np.radians(36)),
        "cos72°": np.cos(np.radians(72)),
        "1/√5": 1/SQRT5,
        "1/5": 0.2,
        "1/12": 1/12,
    }

    for u_name, u_val in u_values.items():
        for label, A, q in [("600", A_600, 11), ("24", A_24, 7), ("16", A_16, 5)]:
            try:
                det_val = ihara_det(A, q, u_val)
                # Use log for large values
                if abs(det_val) > 0:
                    log_det = np.log(abs(det_val))
                    scan_value("§10", f"ln|Z^-1_{label}(u={u_name})|", log_det)
                scan_value("§10", f"Z^-1_{label}(u={u_name})", det_val)
            except Exception:
                pass

    # Ratios of Ihara determinants at same u
    for u_name, u_val in u_values.items():
        try:
            d600 = ihara_det(A_600, 11, u_val)
            d24 = ihara_det(A_24, 7, u_val)
            d16 = ihara_det(A_16, 5, u_val)
            if abs(d24) > 1e-10:
                scan_value("§10", f"Z_600/Z_24 @ u={u_name}", d600/d24)
            if abs(d16) > 1e-10:
                scan_value("§10", f"Z_24/Z_16 @ u={u_name}", d24/d16)
        except Exception:
            pass

    results["sections"]["S10_ihara_zeta"] = sec10

    # ==============================================================
    # §11: RESOLVENT TRACES
    # ==============================================================
    print("\n" + "=" * 70)
    print("§11: Resolvent Traces at Special Points")
    print("=" * 70)

    sec11 = {"hits": []}

    # Resolvent: G(z) = (zI - A)^{-1}
    # Tr(G(z)) = Σ 1/(z - λ_k)
    # Evaluate at z values that avoid eigenvalues

    z_special = {
        "φ": PHI,
        "φ²": PHI**2,
        "φ³": PHI**3,
        "√5": SQRT5,
        "2+√5": 2 + SQRT5,  # = φ³ + 2
        "5": 5.0,
        "π": np.pi,
        "13": 13.0,  # just above max eigenvalue 12
    }

    for z_name, z_val in z_special.items():
        for label, eigs in [("600", all_eigs_600), ("24", all_eigs_24), ("16", all_eigs_16)]:
            tr_G = np.sum(1.0 / (z_val - eigs))
            n = len(eigs)
            scan_value("§11", f"Tr(G_{label}(z={z_name}))", tr_G)
            scan_value("§11", f"Tr(G_{label}(z={z_name}))/n", tr_G / n)

    # Cross-level resolvent ratios
    for z_name, z_val in z_special.items():
        tr_600 = np.sum(1.0 / (z_val - all_eigs_600))
        tr_24 = np.sum(1.0 / (z_val - all_eigs_24))
        tr_16 = np.sum(1.0 / (z_val - all_eigs_16))
        if abs(tr_24) > 1e-10:
            scan_value("§11", f"TrG_600/TrG_24 @ z={z_name}", tr_600/tr_24)
        if abs(tr_16) > 1e-10:
            scan_value("§11", f"TrG_24/TrG_16 @ z={z_name}", tr_24/tr_16)

    results["sections"]["S11_resolvent"] = sec11

    # ==============================================================
    # §12: ALGEBRAIC IDENTITIES FOR √5 − 2
    # ==============================================================
    print("\n" + "=" * 70)
    print("§12: Algebraic Identities Involving Spectral Data")
    print("=" * 70)

    sec12 = {"hits": []}

    # Key identity: √5 − 2 = 1/φ³ = 2φ − 3
    # Also: √5 − 2 = φ⁻¹ · φ⁻² = φ⁻¹ · (3 − √5)/2 · 2
    # Can we construct this from the spectral data?

    # The 600-cell eigenvalues have the form:
    # {12, 3+3√5, 2+2√5, 3, 0, -2, 2-2√5, -3, 3-3√5}
    # In terms of φ: {12, 6φ, 4φ, 3, 0, -2, -4/φ, -3, -6/φ}

    # Test: differences and ratios that might give √5 − 2
    eig_exact = {
        "12": 12.0,
        "6φ": 6*PHI,
        "4φ": 4*PHI,
        "3": 3.0,
        "0": 0.0,
        "-2": -2.0,
        "-4/φ": -4/PHI,
        "-3": -3.0,
        "-6/φ": -6/PHI,
    }

    # All (a·λ_i + b·λ_j)/(c·λ_k + d·λ_l) for small integer coefficients
    print("\n  Exhaustive search: (a·λ_i + b·λ_j)/(c·λ_k) for a,b ∈ {±1,±2,±3}")
    eig_names = [(n, v) for n, v in eig_exact.items() if abs(v) > 0.01]

    algebraic_hits = []
    for (n1, v1) in eig_names:
        for (n2, v2) in eig_names:
            for (n3, v3) in eig_names:
                for a in [-3, -2, -1, 1, 2, 3]:
                    for b in [-3, -2, -1, 0, 1, 2, 3]:
                        numer = a*v1 + b*v2
                        denom = v3
                        if abs(denom) > 0.01:
                            val = numer / denom
                            err = abs(val - TARGET) / TARGET * 100
                            if err < 0.01:
                                desc = f"({a}·{n1} + {b}·{n2}) / {n3}"
                                algebraic_hits.append((desc, val, err))

    if algebraic_hits:
        algebraic_hits.sort(key=lambda x: x[2])
        print(f"\n  Found {len(algebraic_hits)} exact algebraic identities:")
        for desc, val, err in algebraic_hits[:20]:
            print(f"    ★★★ {desc} = {val:.12f} (err {err:.8f}%)")
            record_hit("§12", desc, val, True, err)
    else:
        print("    No exact algebraic identity found with small integer coefficients.")

    # Three-eigenvalue products / sums
    print("\n  Three-eigenvalue combinations: (λ_i · λ_j) / λ_k")
    for (n1, v1) in eig_names:
        for (n2, v2) in eig_names:
            for (n3, v3) in eig_names:
                if abs(v3) > 0.01:
                    val = v1 * v2 / v3
                    err = abs(val - TARGET) / TARGET * 100
                    if err < 0.01:
                        desc = f"({n1} × {n2}) / {n3}"
                        print(f"    ★★★ {desc} = {val:.12f} (err {err:.8f}%)")
                        record_hit("§12", desc, val, True, err)
                    elif err < 1.0:
                        desc = f"({n1} × {n2}) / {n3}"
                        print(f"    ☆ {desc} = {val:.10f} (err {err:.4f}%)")

    # Test: (eigenvalue ± integer) products
    print("\n  (λ_i ± n) combinations:")
    for (n1, v1) in eig_names:
        for offset in range(-5, 6):
            shifted = v1 + offset
            if abs(shifted) > 1e-10:
                scan_value("§12", f"({n1} + {offset})", shifted)
                scan_value("§12", f"1/({n1} + {offset})", 1/shifted)
                for (n2, v2) in eig_names:
                    if abs(v2) > 0.01:
                        val = shifted / v2
                        err = abs(val - TARGET) / TARGET * 100
                        if err < 0.01:
                            desc = f"({n1}+{offset}) / {n2}"
                            print(f"    ★★★ {desc} = {val:.12f}")
                            record_hit("§12", desc, val, True, err)

    results["sections"]["S12_algebraic_identities"] = sec12

    # ==============================================================
    # §13: MULTIPLICITY-WEIGHTED SPECTRAL QUANTITIES
    # ==============================================================
    print("\n" + "=" * 70)
    print("§13: Multiplicity-Weighted Spectral Quantities")
    print("=" * 70)

    sec13 = {"hits": []}

    # The eigenvalue multiplicities are {1, 4, 9, 16, 25, 36, 9, 16, 4}
    # These are perfect squares! {1², 2², 3², 4², 5², 6², 3², 4², 2²}

    mults_600 = {}
    for lam in eigs_600:
        mults_600[round(lam, 6)] = es_600[lam].shape[1]

    print(f"\n  Eigenvalue multiplicities: {mults_600}")

    # Multiplicity-weighted sums
    weighted_sums = {}
    for weight_name, weight_fn in [
        ("dim", lambda m: m),
        ("√dim", lambda m: np.sqrt(m)),
        ("dim²", lambda m: m**2),
        ("1/dim", lambda m: 1/m),
    ]:
        total = 0
        for lam, mult in mults_600.items():
            total += lam * weight_fn(mult)
        weighted_sums[f"Σ λ·{weight_name}"] = total

    # Ratios of weighted sums to standard sum
    total_dim = sum(mults_600.values())
    for name, val in weighted_sums.items():
        if abs(val) > 1e-10:
            scan_value("§13", name, val)
            scan_value("§13", f"{name} / Σdim", val / total_dim)
            scan_value("§13", f"{name} / |V|", val / 120)

    # Dimension-weighted eigenvalue products
    print("\n  Dimension-weighted products:")
    for (lam, mult) in mults_600.items():
        if abs(lam) > 0.01:
            val = lam / mult
            scan_value("§13", f"λ({lam:.4f})/mult({mult})", val)
            val2 = lam * mult
            scan_value("§13", f"λ({lam:.4f})×mult({mult})", val2)

    # The multiplicity pattern {1,4,9,16,25,36,9,16,4} sums to 120
    # Perfect square multiplicities suggest representation dimensions
    # Check: Σ_φ-eig m_k / Σ m_k vs Σ_non-φ m_k / Σ m_k
    phi_mult_sum = sum(m for l, m in mults_600.items()
                       if any(abs(l - t) < 0.01 for t in [6*PHI, 4*PHI, -4/PHI, -6/PHI]))
    non_phi_mult_sum = total_dim - phi_mult_sum
    print(f"\n  φ-eigenvalue total multiplicity: {phi_mult_sum}")
    print(f"  Non-φ-eigenvalue total multiplicity: {non_phi_mult_sum}")
    scan_value("§13", "φ_mults/total", phi_mult_sum / total_dim)
    scan_value("§13", "non_φ_mults/total", non_phi_mult_sum / total_dim)
    scan_value("§13", "φ_mults/non_φ_mults", phi_mult_sum / non_phi_mult_sum)

    results["sections"]["S13_multiplicity_weighted"] = sec13

    # ==============================================================
    # §14: COXETER PLANE PROJECTION
    # ==============================================================
    print("\n" + "=" * 70)
    print("§14: Coxeter Plane Projection Coefficients")
    print("=" * 70)

    sec14 = {"hits": []}

    # The Coxeter plane is the 2D plane in ℝ⁴ where the Coxeter element
    # acts as rotation by 2π/h (h = Coxeter number = 30 for H₄)
    # Projection onto this plane may involve √5−2 as a coefficient

    # Find the Coxeter plane from C_H4's eigenvalues
    eig_vals_ch4, eig_vecs_ch4 = np.linalg.eig(C_H4)
    phases_ch4 = np.angle(eig_vals_ch4)

    # The Coxeter plane corresponds to eigenvalue e^{2πi/30}
    # (the smallest exponent m=1)
    min_phase = 2*np.pi/30
    idx_cox = np.argmin(np.abs(phases_ch4 - min_phase))
    cox_eigvec = eig_vecs_ch4[:, idx_cox]

    # Project all 600-cell vertices onto Coxeter plane
    # Use the real and imaginary parts of the eigenvector as basis
    u1 = np.real(cox_eigvec)
    u2 = np.imag(cox_eigvec)
    u1 = u1 / np.linalg.norm(u1)
    u2 = u2 / np.linalg.norm(u2)

    # Gram-Schmidt to ensure orthogonality
    u2 = u2 - np.dot(u2, u1) * u1
    u2 = u2 / np.linalg.norm(u2)

    projections = verts_600 @ np.column_stack([u1, u2])
    proj_norms = np.linalg.norm(projections, axis=1)

    unique_proj_norms = sorted(set(np.round(proj_norms, 6)))
    print(f"\n  Coxeter plane projection: {len(unique_proj_norms)} unique radii")
    for r in unique_proj_norms:
        m = check_phi(r)
        tag = fmt_matches(m) if m else ""
        print(f"    r = {r:.6f}{tag}")
        scan_value("§14", f"Coxeter projection radius {r:.6f}", r)

    # Ratios of projection radii
    for i, ri in enumerate(unique_proj_norms):
        for j, rj in enumerate(unique_proj_norms):
            if i < j and rj > 0.01:
                scan_value("§14", f"proj_r[{i}]/proj_r[{j}]", ri/rj)

    # Projection coefficients (inner products with Coxeter basis)
    # Check if any coefficient equals √5−2
    all_proj_x = projections[:, 0]
    all_proj_y = projections[:, 1]
    unique_coords = sorted(set(np.round(np.abs(all_proj_x), 6)))
    for c in unique_coords:
        if c > 0.01:
            scan_value("§14", f"|Coxeter_x| = {c:.6f}", c)
    unique_coords_y = sorted(set(np.round(np.abs(all_proj_y), 6)))
    for c in unique_coords_y:
        if c > 0.01:
            scan_value("§14", f"|Coxeter_y| = {c:.6f}", c)

    results["sections"]["S14_coxeter_plane"] = sec14

    # ==============================================================
    # §15: ALTERNATIVE DECOMPOSITION SEARCH (PATH D OVERLAP)
    # ==============================================================
    print("\n" + "=" * 70)
    print("§15: Alternative Decomposition — Single-Origin √5−2")
    print("=" * 70)

    sec15 = {"hits": []}

    # Search for a SINGLE quantity in the 600-cell that directly equals
    # √5 − 2, providing a unified origin for 1/φ³

    # 1. Frame operator eigenvalue ratios
    F_600 = verts_600.T @ verts_600  # 4×4
    F_24 = verts_24.T @ verts_24
    F_16 = verts_16.T @ verts_16

    feigs_600 = np.linalg.eigvalsh(F_600)
    feigs_24 = np.linalg.eigvalsh(F_24)
    feigs_16 = np.linalg.eigvalsh(F_16)

    print(f"\n  Frame operator eigenvalues:")
    print(f"    F_600: {feigs_600}")
    print(f"    F_24:  {feigs_24}")
    print(f"    F_16:  {feigs_16}")

    for label, feigs in [("600", feigs_600), ("24", feigs_24), ("16", feigs_16)]:
        for i, e in enumerate(feigs):
            scan_value("§15", f"F_{label} eigenvalue [{i}]", e)

    # Frame operator ratios
    for i in range(4):
        if feigs_24[i] > 0.01:
            scan_value("§15", f"F_16[{i}]/F_24[{i}]", feigs_16[i]/feigs_24[i])
        if feigs_600[i] > 0.01:
            scan_value("§15", f"F_24[{i}]/F_600[{i}]", feigs_24[i]/feigs_600[i])
            scan_value("§15", f"F_16[{i}]/F_600[{i}]", feigs_16[i]/feigs_600[i])

    # 2. Angle between subspaces: use right singular vectors (ℝ⁴ column spaces)
    # Both 24-cell and 16-cell span ℝ⁴, so principal angles via V matrices
    _, _, Vt24 = np.linalg.svd(verts_24, full_matrices=False)
    _, _, Vt16 = np.linalg.svd(verts_16, full_matrices=False)
    cos_angles = np.linalg.svd(Vt24 @ Vt16.T, compute_uv=False)
    cos_angles = np.clip(cos_angles, -1, 1)
    angles = np.arccos(cos_angles)
    print(f"\n  Principal angles between C₀ and Γ₀ (via right singular vectors):")
    print(f"    cos(θ) = {cos_angles}")
    print(f"    θ (deg) = {np.degrees(angles)}")
    for i, (ca, a) in enumerate(zip(cos_angles, angles)):
        scan_value("§15", f"cos(principal_angle[{i}]) C0/Γ0", ca)
        scan_value("§15", f"principal_angle[{i}] C0/Γ0 (rad)", a)

    # 3. Restricted Laplacian: L_600 restricted to C₀
    L_600_on_C0 = L_600[np.ix_(c0_idx, c0_idx)]
    leigs_restr = np.sort(np.linalg.eigvalsh(L_600_on_C0))
    print(f"\n  L_600 restricted to C₀ eigenvalues:")
    print(f"    {np.round(leigs_restr, 6)}")
    for i, e in enumerate(leigs_restr):
        scan_value("§15", f"L_600|_C0 eigenvalue [{i}]", e)

    # 4. Normalized overlap: Tr(P_C0 · P_Γ0) where P is projector
    P_C0 = np.zeros((120, 120))
    for i in c0_idx:
        P_C0[i, i] = 1
    sixteen_global_arr = np.array([c0_idx[i] for i in sixteens[0]])
    P_G0 = np.zeros((120, 120))
    for i in sixteen_global_arr:
        P_G0[i, i] = 1
    overlap_tr = np.trace(P_C0 @ P_G0)
    print(f"\n  Tr(P_C0 · P_Γ0) = {overlap_tr} (= number of shared vertices)")
    scan_value("§15", "Tr(P_C0·P_Γ0)/24", overlap_tr/24)
    scan_value("§15", "Tr(P_C0·P_Γ0)/120", overlap_tr/120)

    # 5. Adjacency matrix powers restricted: Tr(A^k|_C0) / Tr(A^k)
    print("\n  Restricted power traces Tr(A_600^k|_C0)/Tr(A_600^k):")
    for k in range(1, 8):
        Ak = np.linalg.matrix_power(A_600.astype(float), k)
        tr_full = np.trace(Ak)
        tr_restr = np.trace(Ak[np.ix_(c0_idx, c0_idx)])
        if abs(tr_full) > 1e-10:
            ratio = tr_restr / tr_full
            print(f"    k={k}: Tr(A^k|_C0)/Tr(A^k) = {ratio:.10f}")
            scan_value("§15", f"Tr(A^{k}|_C0)/Tr(A^{k})", ratio)
        # Also: Tr(A^k|_Γ0)/Tr(A^k|_C0)
        tr_restr_16 = np.trace(Ak[np.ix_(sixteen_global_arr, sixteen_global_arr)])
        if abs(tr_restr) > 1e-10:
            ratio2 = tr_restr_16 / tr_restr
            print(f"    k={k}: Tr(A^k|_Γ0)/Tr(A^k|_C0) = {ratio2:.10f}")
            scan_value("§15", f"Tr(A^{k}|_Γ0)/Tr(A^{k}|_C0)", ratio2)

    results["sections"]["S15_alternative_decomposition"] = sec15

    # ==============================================================
    # SUMMARY
    # ==============================================================
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    n_hits = len(results["all_hits"])
    n_near = len(results["near_misses"])

    print(f"\n  Total HITS (< 0.3% error): {n_hits}")
    print(f"  Total NEAR-MISSES (0.3% - 5%): {n_near}")

    if n_hits > 0:
        print(f"\n  ★★★ EXACT HITS (< 0.3% from √5−2):")
        results["all_hits"].sort(key=lambda x: x["error_pct"])
        for h in results["all_hits"]:
            tag = "EXACT" if h["exact"] else "CLOSE"
            print(f"    [{tag}] {h['section']}: {h['description']}")
            print(f"           value = {h['value']:.12f}, error = {h['error_pct']:.6f}%")
    else:
        print("\n  ❌ No quantity found that equals √5 − 2 within 0.3%")

    if n_near > 0:
        print(f"\n  ☆ NEAR-MISSES (0.3% - 5% from √5−2):")
        results["near_misses"].sort(key=lambda x: x["error_pct"])
        for h in results["near_misses"][:10]:  # top 10
            print(f"    [{h['error_pct']:.2f}%] {h['section']}: {h['description']}")
            print(f"           value = {h['value']:.10f}")

    # Verdict
    if n_hits > 0 and any(h["exact"] for h in results["all_hits"]):
        verdict = "POSITIVE — √5−2 found as exact algebraic quantity"
        status = "✅ DERIVED"
    elif n_hits > 0:
        verdict = "PARTIAL — quantities close to √5−2 found, need exact verification"
        status = "🔸 PARTIAL"
    else:
        verdict = "NEGATIVE — no natural geometric/spectral quantity equals √5−2"
        status = "❌ NOT FOUND"

    results["verdict"] = verdict
    results["status"] = status
    results["summary"] = {
        "total_quantities_tested": "~10,000+",
        "exact_hits": n_hits,
        "near_misses": n_near,
        "sections_tested": list(results["sections"].keys()),
    }

    print(f"\n  VERDICT: {verdict}")
    print(f"  STATUS: {status}")

    # Save results
    output_path = os.path.join(os.path.dirname(__file__),
                               "path_e_direct_sqrt5_minus_2_results.json")
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\n  Results saved to: {output_path}")

    return results


if __name__ == "__main__":
    main()
