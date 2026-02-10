#!/usr/bin/env python3
"""
600-Cell Geometric Ratio Explorer
==================================
Constructs the 600-cell and systematically searches for geometric quantities
involving φ (golden ratio) at each level of the polytope hierarchy:

    600-cell (H₄, 120 vertices)
      → 24-cell (F₄, 24 vertices) × 5 copies
        → 16-cell (B₄, 8 vertices) × 3 per 24-cell

Motivation: λ = (1/φ³) sin(72°) ≈ 0.2245 matches the Cabibbo angle.
Factor 1 (edge ratio = 1/φ) and Factor 3 (overlap ≈ 1/φ) are derived.
Factor 2 (24-cell → 16-cell) lacks rigorous derivation.

This script searches for ANY geometric quantity at the 24→16 level
that equals 1/φ, and also checks whether 1/φ³ arises as a single quantity.
"""

import numpy as np
from itertools import product as iter_product, combinations, permutations
from collections import defaultdict
import json
import os

# ============================================================
# CONSTANTS
# ============================================================
PHI = (1 + np.sqrt(5)) / 2
INV_PHI = 1.0 / PHI
SQRT5 = np.sqrt(5)

# φ-related targets to check against
PHI_TARGETS = {
    'φ':        PHI,
    '1/φ':      INV_PHI,
    'φ²':       PHI**2,
    '1/φ²':     1/PHI**2,
    'φ³':       PHI**3,
    '1/φ³':     1/PHI**3,
    '√φ':       np.sqrt(PHI),
    '1/√φ':     1/np.sqrt(PHI),
    'φ/2':      PHI/2,
    '1/(2φ)':   1/(2*PHI),
    'sin72°':   np.sin(np.radians(72)),
    'sin36°':   np.sin(np.radians(36)),
    '√5':       SQRT5,
    '2/√5':     2/SQRT5,
    '1/√5':     1/SQRT5,
    '√3/2':     np.sqrt(3)/2,
    '1/√3':     1/np.sqrt(3),
    '√(2+φ)':   np.sqrt(2+PHI),
    '1/3':      1/3,
    '1/5':      1/5,
    '2/3':      2/3,
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


def fmt_matches(matches):
    """Format match list for printing."""
    if not matches:
        return ""
    return " ← " + ", ".join(f"{n}" for n, _, _ in matches) + " ***"


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
# 600-CELL CONSTRUCTION
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

    # Group 1: 8 axis vertices — permutations of (±1, 0, 0, 0)
    for i in range(4):
        for s in [1.0, -1.0]:
            v = [0.0, 0.0, 0.0, 0.0]
            v[i] = s
            verts.add(tuple(round(x, 10) for x in v))

    # Group 2: 16 half-integer vertices — (±½, ±½, ±½, ±½)
    for signs in iter_product([0.5, -0.5], repeat=4):
        verts.add(tuple(round(x, 10) for x in signs))

    # Group 3: 96 golden vertices — even perms of (0, ±½, ±φ/2, ±1/(2φ))
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


# ============================================================
# STRUCTURE IDENTIFICATION
# ============================================================
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


def find_24_cells(vertices, c0):
    """Find all 5 copies of the 24-cell via quaternion cosets."""
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
    """Find 3 orthogonal 16-cells within a 24-cell using distance structure."""
    verts = vertices[cell_indices]
    n = len(cell_indices)
    sqrt2 = np.sqrt(2)

    # Two vertices are in the SAME 16-cell if their distance is √2 or 2
    # (not 1, which connects different 16-cells)
    adj = defaultdict(set)
    for i in range(n):
        adj[i].add(i)
        for j in range(i + 1, n):
            d = np.linalg.norm(verts[i] - verts[j])
            if abs(d - sqrt2) < 0.05 or abs(d - 2.0) < 0.05:
                adj[i].add(j)
                adj[j].add(i)

    # Connected components
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


# ============================================================
# GEOMETRIC COMPUTATIONS
# ============================================================
def edge_length(vertices, indices):
    """Minimum nonzero pairwise distance."""
    verts = vertices[indices]
    min_d = np.inf
    for i in range(len(verts)):
        for j in range(i + 1, len(verts)):
            d = np.linalg.norm(verts[i] - verts[j])
            if 0.001 < d < min_d:
                min_d = d
    return min_d


def distance_spectrum(vertices, indices):
    """All unique pairwise distances with multiplicities."""
    verts = vertices[indices]
    dists = []
    for i in range(len(verts)):
        for j in range(i + 1, len(verts)):
            dists.append(np.linalg.norm(verts[i] - verts[j]))
    dists.sort()
    unique = []
    for d in dists:
        if not unique or abs(d - unique[-1][0]) > 0.001:
            unique.append([d, 1])
        else:
            unique[-1][1] += 1
    return unique


def circumradius(vertices, indices):
    """Max distance from centroid to any vertex."""
    verts = vertices[indices]
    center = np.mean(verts, axis=0)
    return max(np.linalg.norm(v - center) for v in verts)


def inradius(vertices, indices):
    """Distance from centroid to nearest convex hull facet."""
    from scipy.spatial import ConvexHull
    verts = vertices[indices]
    center = np.mean(verts, axis=0)
    try:
        hull = ConvexHull(verts)
        return min(abs(np.dot(eq[:-1], center) + eq[-1]) for eq in hull.equations)
    except Exception:
        return None


def volume_4d(vertices, indices):
    """4D convex hull volume."""
    from scipy.spatial import ConvexHull
    try:
        return ConvexHull(vertices[indices]).volume
    except Exception:
        return None


def frame_operator(vertices, indices):
    """Frame operator F = Σ |v⟩⟨v|, returns 4×4 matrix."""
    verts = vertices[indices]
    return verts.T @ verts


# ============================================================
# MAIN ANALYSIS
# ============================================================
def main():
    print("=" * 78)
    print("600-CELL GEOMETRIC RATIO EXPLORER")
    print("Searching for φ-related quantities in the polytope hierarchy")
    print("=" * 78)

    all_hits = []  # Collect all φ matches
    all_ratios = {}  # Store all computed ratios

    # ----------------------------------------------------------
    # 1. BUILD 600-CELL
    # ----------------------------------------------------------
    print("\n§1. CONSTRUCTING 600-CELL")
    print("-" * 40)
    V = build_600_cell()
    print(f"  Vertices: {len(V)}")
    norms = np.linalg.norm(V, axis=1)
    print(f"  All unit norm: {np.allclose(norms, 1.0)}")

    all_idx = list(range(len(V)))
    e600 = edge_length(V, all_idx)
    print(f"  Edge length: {e600:.6f}  (expected 1/φ = {INV_PHI:.6f})")

    print("\n  Distance spectrum:")
    spec = distance_spectrum(V, all_idx)
    for d, cnt in spec:
        m = check_phi(d)
        print(f"    d = {d:.6f}  ×{cnt:>5}{fmt_matches(m)}")
        if m:
            all_hits.append((f"600-cell dist {d:.4f}", d, m))

    # ----------------------------------------------------------
    # 2. IDENTIFY STRUCTURES
    # ----------------------------------------------------------
    print("\n§2. STRUCTURE IDENTIFICATION")
    print("-" * 40)

    c0 = find_c0(V)
    print(f"  C₀ (standard 24-cell): {len(c0)} vertices")

    copies = find_24_cells(V, c0)
    print(f"  24-cell copies found: {len(copies)}")

    gammas = find_16_cells(V, c0)
    print(f"  16-cells in C₀: {len(gammas)}, sizes: {[len(g) for g in gammas]}")

    # ----------------------------------------------------------
    # 3. BASIC PROPERTIES AT EACH LEVEL
    # ----------------------------------------------------------
    print("\n§3. BASIC PROPERTIES")
    print("-" * 40)

    e24 = edge_length(V, c0)
    e16 = edge_length(V, gammas[0])
    R600 = circumradius(V, all_idx)
    R24 = circumradius(V, c0)
    R16 = circumradius(V, gammas[0])
    r600 = inradius(V, all_idx)
    r24 = inradius(V, c0)
    r16 = inradius(V, gammas[0])
    V600 = volume_4d(V, all_idx)
    V24 = volume_4d(V, c0)
    V16 = volume_4d(V, gammas[0])

    props = [
        ("Edge lengths", [
            ("e_600", e600), ("e_24", e24), ("e_16", e16)]),
        ("Circumradii", [
            ("R_600", R600), ("R_24", R24), ("R_16", R16)]),
        ("Inradii", [
            ("r_600", r600), ("r_24", r24), ("r_16", r16)]),
        ("4D Volumes", [
            ("V_600", V600), ("V_24", V24), ("V_16", V16)]),
    ]
    for section, items in props:
        print(f"\n  {section}:")
        for name, val in items:
            if val is not None:
                print(f"    {name} = {val:.6f}")

    # 24-cell distance spectrum
    print("\n  24-cell distance spectrum:")
    for d, cnt in distance_spectrum(V, c0):
        m = check_phi(d)
        print(f"    d = {d:.6f}  ×{cnt:>3}{fmt_matches(m)}")

    # 16-cell distance spectrum
    print("\n  16-cell Γ₀ distance spectrum:")
    for d, cnt in distance_spectrum(V, gammas[0]):
        m = check_phi(d)
        print(f"    d = {d:.6f}  ×{cnt:>3}{fmt_matches(m)}")

    # ----------------------------------------------------------
    # 4. EDGE LENGTH RATIOS
    # ----------------------------------------------------------
    print("\n§4. EDGE LENGTH RATIOS")
    print("-" * 40)

    ratios = {
        'e600/e24':     e600 / e24,
        'e24/e600':     e24 / e600,
        'e600/e16':     e600 / e16,
        'e16/e600':     e16 / e600,
        'e24/e16':      e24 / e16,
        'e16/e24':      e16 / e24,
        '(e600/e24)²':  (e600 / e24)**2,
        '(e600/e24)³':  (e600 / e24)**3,
        '(e600/e16)²':  (e600 / e16)**2,
    }
    for name, val in ratios.items():
        m = check_phi(val)
        print(f"  {name:20s} = {val:.6f}{fmt_matches(m)}")
        all_ratios[name] = val
        if m:
            all_hits.append((name, val, m))

    # ----------------------------------------------------------
    # 5. RADIUS RATIOS
    # ----------------------------------------------------------
    print("\n§5. RADIUS RATIOS")
    print("-" * 40)

    radius_ratios = {
        'R24/R600': R24 / R600,
        'R16/R24':  R16 / R24,
        'R16/R600': R16 / R600,
    }
    if r600 and r24 and r16:
        radius_ratios.update({
            'r24/r600':     r24 / r600,
            'r16/r24':      r16 / r24,
            'r16/r600':     r16 / r600,
            'r24/R24':      r24 / R24,
            'r16/R16':      r16 / R16,
            'r600/R600':    r600 / R600,
            '(r/R)16/(r/R)24':   (r16/R16) / (r24/R24),
            '(r/R)24/(r/R)600':  (r24/R24) / (r600/R600),
        })
    for name, val in radius_ratios.items():
        m = check_phi(val)
        print(f"  {name:24s} = {val:.6f}{fmt_matches(m)}")
        all_ratios[name] = val
        if m:
            all_hits.append((name, val, m))

    # ----------------------------------------------------------
    # 6. VOLUME RATIOS
    # ----------------------------------------------------------
    print("\n§6. VOLUME RATIOS")
    print("-" * 40)

    if V600 and V24 and V16:
        vol_ratios = {
            'V24/V600':         V24 / V600,
            'V16/V24':          V16 / V24,
            'V16/V600':         V16 / V600,
            '3×V16/V24':        3 * V16 / V24,
            '5×V24/V600':       5 * V24 / V600,
            '15×V16/V600':      15 * V16 / V600,
            '(V24/V600)^(1/4)': (V24 / V600)**0.25,
            '(V16/V24)^(1/4)':  (V16 / V24)**0.25,
            '(V16/V24)^(1/3)':  (V16 / V24)**(1/3),
            '(V24/V600)^(1/3)': (V24 / V600)**(1/3),
        }
        for name, val in vol_ratios.items():
            m = check_phi(val)
            print(f"  {name:24s} = {val:.6f}{fmt_matches(m)}")
            all_ratios[name] = val
            if m:
                all_hits.append((name, val, m))

    # ----------------------------------------------------------
    # 7. FRAME OPERATOR ANALYSIS
    # ----------------------------------------------------------
    print("\n§7. FRAME OPERATOR F = Σ|v⟩⟨v|")
    print("-" * 40)

    F600 = frame_operator(V, all_idx)
    F24  = frame_operator(V, c0)
    Fg   = [frame_operator(V, g) for g in gammas]

    print(f"  F_600 = {np.trace(F600)/4:.4f} × I₄  (trace/4)")
    print(f"  F_24  = {np.trace(F24)/4:.4f} × I₄  (trace/4)")
    for i, F in enumerate(Fg):
        print(f"  F_Γ{i}  = {np.trace(F)/4:.4f} × I₄  (trace/4)")
        # Check if proportional to identity
        eigvals = np.linalg.eigvalsh(F)
        if np.allclose(eigvals, eigvals[0], atol=0.01):
            print(f"         Proportional to I₄ (all eigenvalues = {eigvals[0]:.4f})")
        else:
            print(f"         NOT proportional to I₄: eigenvalues = {np.sort(eigvals)}")

    tr_ratio = np.trace(Fg[0]) / np.trace(F24)
    m = check_phi(tr_ratio)
    print(f"\n  Tr(F_Γ₀)/Tr(F_24) = {tr_ratio:.6f}{fmt_matches(m)}")
    all_ratios['frame_ratio'] = tr_ratio
    if m:
        all_hits.append(('frame_ratio', tr_ratio, m))

    # ----------------------------------------------------------
    # 8. INTER-16-CELL GEOMETRY
    # ----------------------------------------------------------
    print("\n§8. INTER-16-CELL GEOMETRY")
    print("-" * 40)

    for i, j in combinations(range(len(gammas)), 2):
        dists = []
        for vi in gammas[i]:
            for vj in gammas[j]:
                dists.append(np.linalg.norm(V[vi] - V[vj]))
        avg_d = np.mean(dists)
        min_d = np.min(dists)

        for name, val in [(f'd_avg(Γ{i},Γ{j})', avg_d),
                          (f'd_min(Γ{i},Γ{j})', min_d)]:
            m = check_phi(val)
            print(f"  {name:24s} = {val:.6f}{fmt_matches(m)}")
            all_ratios[name] = val
            if m:
                all_hits.append((name, val, m))

    # Inner products between 16-cell vertices across cells
    print("\n  Cross-Gram singular values:")
    for i, j in combinations(range(len(gammas)), 2):
        vi = V[gammas[i]]
        vj = V[gammas[j]]
        cross = vi @ vj.T
        svs = np.sort(np.linalg.svd(cross, compute_uv=False))[::-1]
        print(f"    Cross(Γ{i},Γ{j}): [{', '.join(f'{s:.4f}' for s in svs[:4])}]")
        for k, sv in enumerate(svs[:4]):
            m = check_phi(sv)
            if m:
                name = f'sv{k}(Γ{i},Γ{j})'
                all_hits.append((name, sv, m))
                print(f"      sv_{k} = {sv:.6f}{fmt_matches(m)}")

    # ----------------------------------------------------------
    # 9. 3D PROJECTION (STELLA OCTANGULA)
    # ----------------------------------------------------------
    print("\n§9. 3D PROJECTION (VERTEX NORM RATIOS)")
    print("-" * 40)
    print("  Reviewer's point: ||v₃D||/||v₄D|| = √3/2, NOT 1/√φ")
    print()

    unique_ratios = set()
    for idx in c0:
        v = V[idx]
        n4 = np.linalg.norm(v)
        n3 = np.linalg.norm(v[:3])
        if n4 > 0.001:
            unique_ratios.add(round(n3 / n4, 6))

    print("  Unique ||v₃D||/||v₄D|| for C₀ vertices:")
    for r in sorted(unique_ratios):
        m = check_phi(r)
        print(f"    {r:.6f}{fmt_matches(m)}")
        all_ratios[f'proj_ratio_{r}'] = r
        if m:
            all_hits.append((f'proj_ratio_{r}', r, m))

    # Also check projection norm ratios for each 16-cell
    print("\n  Per-16-cell projection ratios:")
    for gi, g in enumerate(gammas):
        ratios_g = set()
        for idx in g:
            v = V[idx]
            n4 = np.linalg.norm(v)
            n3 = np.linalg.norm(v[:3])
            if n4 > 0.001 and n3 > 0.001:
                ratios_g.add(round(n3 / n4, 6))
        print(f"    Γ{gi}: {sorted(ratios_g)}")

    # ----------------------------------------------------------
    # 10. 600-CELL CONNECTIVITY FROM 16-CELL PERSPECTIVE
    # ----------------------------------------------------------
    print("\n§10. 600-CELL NEIGHBORS OF 16-CELL VERTICES")
    print("-" * 40)

    c0_set = set(c0)
    g0_set = set(gammas[0])

    # For each vertex in Γ₀, count 600-cell neighbors (at distance 1/φ)
    # that are inside vs outside C₀
    for idx in gammas[0][:2]:  # Show first 2 as examples
        v = V[idx]
        neighbors_in_c0 = 0
        neighbors_outside = 0
        neighbor_dists_outside = []
        for j in range(len(V)):
            if j == idx:
                continue
            d = np.linalg.norm(V[j] - v)
            if abs(d - INV_PHI) < 0.01:  # 600-cell edge
                if j in c0_set:
                    neighbors_in_c0 += 1
                else:
                    neighbors_outside += 1
                    neighbor_dists_outside.append(d)
        print(f"  Vertex {idx} ({V[idx]})")
        print(f"    600-cell neighbors (d≈1/φ): {neighbors_in_c0} in C₀, "
              f"{neighbors_outside} outside")

    # Aggregate: average inner products of Γ₀ vertices with golden vertices
    golden_idx = [i for i in range(len(V)) if i not in c0_set]
    golden_verts = V[golden_idx]
    g0_verts = V[gammas[0]]

    # Average |inner product| between Γ₀ and golden vertices
    inner_prods = np.abs(g0_verts @ golden_verts.T)
    avg_ip = np.mean(inner_prods)
    max_ip = np.max(inner_prods)
    m = check_phi(avg_ip)
    print(f"\n  Avg |⟨Γ₀|golden⟩| = {avg_ip:.6f}{fmt_matches(m)}")
    m = check_phi(max_ip)
    print(f"  Max |⟨Γ₀|golden⟩| = {max_ip:.6f}{fmt_matches(m)}")

    # ----------------------------------------------------------
    # 11. ADJACENCY MATRIX EIGENVALUES
    # ----------------------------------------------------------
    print("\n§11. ADJACENCY MATRIX EIGENVALUES")
    print("-" * 40)

    # Build adjacency matrix of 600-cell
    n = len(V)
    adj = np.zeros((n, n), dtype=int)
    for i in range(n):
        for j in range(i + 1, n):
            if abs(np.linalg.norm(V[i] - V[j]) - INV_PHI) < 0.01:
                adj[i, j] = adj[j, i] = 1

    degree = np.sum(adj[0])
    print(f"  Vertex degree: {degree}  (expected 12 for 600-cell)")

    eigvals = np.sort(np.linalg.eigvalsh(adj.astype(float)))[::-1]
    unique_eigs = sorted(set(round(e, 4) for e in eigvals), reverse=True)
    print(f"  Unique eigenvalues ({len(unique_eigs)}):")
    for e in unique_eigs:
        m = check_phi(abs(e))
        sign_e = e
        print(f"    λ = {sign_e:+.4f}{fmt_matches(m)}")
        if m:
            all_hits.append((f'adj_eigval_{e:.4f}', abs(e), m))

    # Restricted adjacency: 600-cell edges involving Γ₀ vertices
    # How many 600-cell edges connect Γ₀ to each other 24-cell copy?
    if len(copies) == 5:
        print("\n  600-cell edges from Γ₀ to each 24-cell copy:")
        for ci, copy in enumerate(copies):
            copy_set = set(copy)
            edge_count = 0
            for gi in gammas[0]:
                for j in range(n):
                    if j in copy_set and adj[gi, j]:
                        edge_count += 1
            print(f"    Γ₀ → C_{ci}: {edge_count} edges")

    # ----------------------------------------------------------
    # 12. COMPOUND RATIO SEARCH
    # ----------------------------------------------------------
    print("\n§12. COMPOUND RATIO SEARCH")
    print("-" * 40)

    # Check if any PAIR of ratios multiplied gives 1/φ
    ratio_list = [(n, v) for n, v in all_ratios.items()
                  if 0.01 < abs(v) < 100]
    pair_hits = []
    for i in range(len(ratio_list)):
        for j in range(i, len(ratio_list)):
            n1, v1 = ratio_list[i]
            n2, v2 = ratio_list[j]
            for op, val in [('×', v1 * v2), ('÷', v1 / v2)]:
                m = check_phi(val)
                if m:
                    for mn, _, _ in m:
                        pair_hits.append((f"{n1} {op} {n2}", val, mn))

    if pair_hits:
        print(f"  Found {len(pair_hits)} compound matches:")
        seen = set()
        for expr, val, target in pair_hits[:30]:
            key = (round(val, 6), target)
            if key not in seen:
                seen.add(key)
                print(f"    {expr} = {val:.6f} ≈ {target}")
    else:
        print("  No compound φ matches found.")

    # ----------------------------------------------------------
    # 13. DIRECT SEARCH FOR 1/φ³
    # ----------------------------------------------------------
    print("\n§13. DIRECT SEARCH FOR 1/φ³ ≈ 0.236068")
    print("-" * 40)

    print("\n  Single ratios within 5% of 1/φ³:")
    found_phi3 = False
    for name, val in sorted(all_ratios.items(), key=lambda x: abs(x[1] - 1/PHI**3)):
        dev = (val - 1/PHI**3) / (1/PHI**3) * 100
        if abs(dev) < 5:
            print(f"    {name:30s} = {val:.6f}  (dev: {dev:+.2f}%)")
            found_phi3 = True
    if not found_phi3:
        print("    None found.")

    print("\n  Checking (e600/e24)³ = (1/φ)³:")
    cube = (e600 / e24)**3
    print(f"    (e600/e24)³ = {cube:.6f}  vs  1/φ³ = {1/PHI**3:.6f}")
    print(f"    This is trivially true since e600/e24 = 1/φ.")
    print(f"    The question is whether 1/φ³ has INDEPENDENT geometric meaning.")

    # ----------------------------------------------------------
    # 14. THE KEY QUESTION: FACTOR 2
    # ----------------------------------------------------------
    print("\n" + "=" * 78)
    print("§14. THE KEY QUESTION: IS THERE A FACTOR 1/φ AT THE 24→16 LEVEL?")
    print("=" * 78)

    print("\n  Quantities involving BOTH 16-cell AND 24-cell or 600-cell:")
    factor2_candidates = []
    for name, val in all_ratios.items():
        if ('16' in name or 'Γ' in name or 'gamma' in name.lower()):
            m = check_phi(val)
            if m:
                for mn, mt, me in m:
                    if mn == '1/φ':
                        factor2_candidates.append((name, val))
                        print(f"    ✓ {name} = {val:.6f} ≈ 1/φ  ***")
            else:
                # Also report these for reference
                pass

    if not factor2_candidates:
        print("\n  *** NO geometric quantity at the 24→16 level matches 1/φ ***")

    # ----------------------------------------------------------
    # 15. ALTERNATIVE DECOMPOSITIONS OF 1/φ³
    # ----------------------------------------------------------
    print("\n§15. ALTERNATIVE DECOMPOSITIONS OF 1/φ³")
    print("-" * 40)
    print("  If 1/φ³ doesn't factor as (1/φ)×(1/φ)×(1/φ) geometrically,")
    print("  what other decompositions are possible?")
    print()

    alt_decomps = [
        ("(1/φ) × (1/φ²)",       INV_PHI * 1/PHI**2,     "Factor1 × (Factor2+3 combined)"),
        ("(e600/e24)³",           (e600/e24)**3,           "Cube of edge ratio (trivial)"),
        ("(1/φ) × (√3/2)²",      INV_PHI * (np.sqrt(3)/2)**2,
         "Factor1 × (actual projection ratio)²"),
        ("(1/φ) × (1/3)",        INV_PHI * (1/3),
         "Factor1 × (vertex count 8/24)"),
    ]
    if V24 and V16:
        alt_decomps.append(
            ("(1/φ) × (V16/V24)",  INV_PHI * V16/V24,
             "Factor1 × volume ratio"))
    if r16 and r24:
        alt_decomps.append(
            ("(1/φ) × (r16/r24)",  INV_PHI * r16/r24,
             "Factor1 × inradius ratio"))

    for expr, val, note in alt_decomps:
        ratio_to_target = val / (1/PHI**3)
        print(f"  {expr:30s} = {val:.6f}  (ratio to 1/φ³: {ratio_to_target:.4f})  [{note}]")

    # Check: what value of Factor2 is NEEDED?
    print("\n  REQUIRED Factor 2 value:")
    print(f"  If Factor1 = 1/φ = {INV_PHI:.6f} and Factor3 = 0.6159 (derived),")
    needed = (1/PHI**3) / (INV_PHI * 0.6159)
    print(f"  then Factor2 = 1/φ³ / (Factor1 × Factor3) = {needed:.6f}")
    m = check_phi(needed)
    print(f"  {fmt_matches(m) if m else '  (no clean φ match)'}")
    print()
    print(f"  If Factor1 = 1/φ and Factor3 = 1/φ (idealized),")
    needed2 = (1/PHI**3) / (INV_PHI * INV_PHI)
    print(f"  then Factor2 = 1/φ³ / (1/φ × 1/φ) = {needed2:.6f}")
    m2 = check_phi(needed2)
    print(f"  {fmt_matches(m2) if m2 else '  (no clean φ match)'}")

    # ----------------------------------------------------------
    # SUMMARY
    # ----------------------------------------------------------
    print("\n" + "=" * 78)
    print("SUMMARY")
    print("=" * 78)

    print(f"\n  Total φ-related matches found: {len(all_hits)}")
    if all_hits:
        # Deduplicate
        seen = set()
        for name, val, matches in all_hits:
            for mn, mt, me in matches:
                key = (name, mn)
                if key not in seen:
                    seen.add(key)
                    print(f"  ✓ {name:35s} = {val:.6f} ≈ {mn} = {mt:.6f}  "
                          f"(err {me:.3f}%)")

    print("\n  FACTOR 2 STATUS:")
    if factor2_candidates:
        print("  ✓ Candidate(s) found for Factor 2 = 1/φ at 24→16 level!")
        for name, val in factor2_candidates:
            print(f"    → {name} = {val:.6f}")
    else:
        print("  ✗ NO candidate for Factor 2 = 1/φ at the 24→16 level.")
        print("    Implications:")
        print("    (a) The 3-factor decomposition (1/φ)³ may be wrong")
        print("    (b) 1/φ³ may arise as a single geometric quantity")
        print("    (c) The formula λ=(1/φ³)sin72° may be numerological")

    print("\n  CONFIRMED RESULTS:")
    print(f"  Factor 1: e_600/e_24 = {e600/e24:.6f} ≈ 1/φ = {INV_PHI:.6f}  ✓")
    print(f"  Factor 3: overlap integral = 0.6159 ≈ 1/φ (separate derivation)  ✓")
    print(f"  Product: (1/φ³) × sin(72°) = {(1/PHI**3)*np.sin(np.radians(72)):.6f}")
    print(f"  PDG λ:   0.22497 ± 0.00070")

    # Save results
    output = {
        'all_ratios': {k: float(v) for k, v in all_ratios.items()},
        'phi_matches': [(n, float(v), [(mn, float(mt), float(me))
                        for mn, mt, me in ms]) for n, v, ms in all_hits],
        'factor2_candidates': [(n, float(v)) for n, v in factor2_candidates],
    }
    out_dir = os.path.dirname(os.path.abspath(__file__))
    out_path = os.path.join(out_dir, 'explore_600_cell_phi_ratios_results.json')
    with open(out_path, 'w') as f:
        json.dump(output, f, indent=2)
    print(f"\n  Results saved to: {out_path}")


if __name__ == "__main__":
    main()
