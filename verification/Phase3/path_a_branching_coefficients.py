#!/usr/bin/env python3
"""
Path A: H₄ → F₄ Branching Coefficients
========================================

Research Plan §11.2 Path A: Check whether any Clebsch-Gordan coefficient
in the H₄ ↓ F₄ decomposition equals 1/φ.

APPROACH:
1. Build 600-cell (H₄) and 24-cell (F₄) vertices
2. Check whether F₄ (24-cell symmetry group) ⊂ H₄ (600-cell symmetry group)
3. Compute adjacency spectra for both polytopes
4. Project 600-cell eigenspaces onto 24-cell vertices
5. Compute overlap matrices (CG-like coefficients)
6. Compute stabilizer Stab_{H₄}(C₀) and analyze its structure
7. Search for 1/φ in all representation-theoretic quantities

Related Documents:
- Research plan: docs/proofs/supporting/Derivation-Three-Phi-Factors-Explicit.md §11
- Prior exploration: verification/Phase3/explore_600_cell_phi_ratios.py
- Path B (closed): verification/Phase3/path_b_tunneling_amplitude.py

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
    'cos36°':   np.cos(np.radians(36)),
    'cos72°':   np.cos(np.radians(72)),
    '√5':       SQRT5,
    '2/√5':     2/SQRT5,
    '1/√5':     1/SQRT5,
    '√(2+φ)':   np.sqrt(2+PHI),
    '1/3':      1/3,
    '1/5':      1/5,
    '2/5':      2/5,
    '3/5':      3/5,
    '√2/2':     np.sqrt(2)/2,
    '1/√2':     1/np.sqrt(2),
    '√3/2':     np.sqrt(3)/2,
    'ln(φ)':    np.log(PHI),
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


# ============================================================
# QUATERNION ALGEBRA (reused from explore_600_cell_phi_ratios.py)
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


def qconj(q):
    """Quaternion conjugate: a + bi + cj + dk → a - bi - cj - dk."""
    return np.array([q[0], -q[1], -q[2], -q[3]])


# ============================================================
# 600-CELL CONSTRUCTION (reused)
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
    """Find the standard 24-cell C₀."""
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


# ============================================================
# §1: BUILD ADJACENCY MATRICES
# ============================================================
def build_adjacency(vertices, edge_length, tol=0.05):
    """Build adjacency matrix for vertices with given edge length."""
    n = len(vertices)
    A = np.zeros((n, n), dtype=int)
    for i in range(n):
        for j in range(i + 1, n):
            d = np.linalg.norm(vertices[i] - vertices[j])
            if abs(d - edge_length) < tol:
                A[i, j] = 1
                A[j, i] = 1
    return A


def build_distance_matrices(vertices, tol=0.01):
    """Build distance-class adjacency matrices (Bose-Mesner algebra)."""
    n = len(vertices)
    dists = np.zeros((n, n))
    for i in range(n):
        for j in range(i + 1, n):
            d = np.linalg.norm(vertices[i] - vertices[j])
            dists[i, j] = d
            dists[j, i] = d

    # Find unique distances
    upper = dists[np.triu_indices(n, k=1)]
    unique_dists = []
    for d in sorted(set(np.round(upper, 6))):
        if d > 0:
            unique_dists.append(d)

    # Build one adjacency matrix per distance class
    dist_matrices = {}
    for dk in unique_dists:
        Ak = np.zeros((n, n), dtype=int)
        for i in range(n):
            for j in range(i + 1, n):
                if abs(dists[i, j] - dk) < tol:
                    Ak[i, j] = 1
                    Ak[j, i] = 1
        if np.any(Ak):
            dist_matrices[round(dk, 6)] = Ak

    return dist_matrices


# ============================================================
# §2: SPECTRAL DECOMPOSITION
# ============================================================
def eigendecompose(A, tol=1e-8):
    """Eigendecompose a symmetric matrix. Returns (eigenvalues, eigenspaces).
    Each eigenspace is a dict: {eigenvalue: matrix_of_eigenvectors}."""
    vals, vecs = np.linalg.eigh(A)

    # Group by eigenvalue
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
        eigenspaces[key] = vecs[:, group]  # columns are eigenvectors

    return eigenspaces


# ============================================================
# §3: VERIFY F₄ ⊄ H₄
# ============================================================
def check_matrix_preserves_set(M, vertices, tol=0.01):
    """Check if 4x4 matrix M permutes the vertex set."""
    for v in vertices:
        Mv = M @ v
        dists = np.linalg.norm(vertices - Mv, axis=1)
        if np.min(dists) > tol:
            return False
    return True


def generate_f4_generators(c0_verts):
    """Generate the symmetry group generators of the 24-cell.
    These include signed permutations and the Hadamard-like matrix
    that mixes axis and half-integer vertices."""
    generators = []

    # Coordinate transpositions: swap coords i and j
    for i in range(4):
        for j in range(i + 1, 4):
            M = np.eye(4)
            M[i, i] = 0
            M[j, j] = 0
            M[i, j] = 1
            M[j, i] = 1
            generators.append(M)

    # Sign changes: negate coordinate i
    for i in range(4):
        M = np.eye(4)
        M[i, i] = -1
        generators.append(M)

    # Hadamard-like: maps (1,0,0,0) → (½,½,½,½)
    H = 0.5 * np.array([
        [1, 1, 1, 1],
        [1, -1, -1, 1],
        [1, -1, 1, -1],
        [1, 1, -1, -1]
    ])
    generators.append(H)

    return generators


def generate_group_from_generators(generators, max_size=15000, tol=1e-6):
    """Generate a finite group by closure under multiplication.
    Uses BFS approach: multiply every element by every generator."""
    def mat_key(M):
        return tuple(round(x, 4) for x in M.flatten())

    group = {}
    identity = np.eye(4)
    group[mat_key(identity)] = identity

    # Add generators and their inverses
    queue = []
    for g in generators:
        k = mat_key(g)
        if k not in group:
            group[k] = g.copy()
            queue.append(g.copy())
        ginv = np.linalg.inv(g)
        kinv = mat_key(ginv)
        if kinv not in group:
            group[kinv] = ginv
            queue.append(ginv)

    # BFS: multiply frontier by all generators
    while queue and len(group) < max_size:
        next_queue = []
        for elem in queue:
            for g in generators:
                for prod in [elem @ g, g @ elem, elem @ np.linalg.inv(g),
                             np.linalg.inv(g) @ elem]:
                    pk = mat_key(prod)
                    if pk not in group:
                        group[pk] = prod
                        next_queue.append(prod)
                        if len(group) >= max_size:
                            return list(group.values())
        queue = next_queue

    return list(group.values())


def verify_f4_not_in_h4(vertices_600, c0_verts):
    """Verify that some F₄ generators do NOT preserve the 600-cell."""
    print("\n" + "=" * 70)
    print("§3: CHECKING WHETHER F₄ ⊂ H₄")
    print("=" * 70)

    generators = generate_f4_generators(c0_verts)
    results = []

    gen_names = []
    for i in range(4):
        for j in range(i + 1, 4):
            gen_names.append(f"Swap({i},{j})")
    for i in range(4):
        gen_names.append(f"Negate({i})")
    gen_names.append("Hadamard")

    for name, gen in zip(gen_names, generators):
        preserves_24 = check_matrix_preserves_set(gen, c0_verts)
        preserves_600 = check_matrix_preserves_set(gen, vertices_600)
        results.append({
            'generator': name,
            'preserves_24_cell': preserves_24,
            'preserves_600_cell': preserves_600,
            'in_F4_and_H4': preserves_24 and preserves_600,
            'in_F4_not_H4': preserves_24 and not preserves_600,
        })
        status = "✓ in H₄" if preserves_600 else "✗ NOT in H₄"
        f4_status = "✓ in F₄" if preserves_24 else "✗ NOT in F₄"
        print(f"  {name:15s}: {f4_status}, {status}")

    n_in_both = sum(1 for r in results if r['in_F4_and_H4'])
    n_in_f4_only = sum(1 for r in results if r['in_F4_not_H4'])

    print(f"\n  Generators in F₄ ∩ H₄: {n_in_both}/{len(generators)}")
    print(f"  Generators in F₄ \\ H₄: {n_in_f4_only}/{len(generators)}")

    if n_in_f4_only > 0:
        print("\n  ⚠ CONFIRMED: F₄ ⊄ H₄ (some F₄ generators break the 600-cell)")
    else:
        print("\n  All F₄ generators also in H₄ — F₄ may be a subgroup of H₄")

    return results


# ============================================================
# §4: STABILIZER Stab_{H₄}(C₀) — symmetries of 600-cell fixing C₀
# ============================================================
def find_h4_generators_preserving_c0(vertices_600, c0_indices):
    """Find generators of Stab_{H₄}(C₀): elements of H₄ that map C₀ to itself.
    Uses reflections in hyperplanes perpendicular to roots."""
    print("\n" + "=" * 70)
    print("§4: STABILIZER Stab_{H₄}(C₀)")
    print("=" * 70)

    c0_set = set(c0_indices)
    generators = []

    # Try reflections in the perpendicular bisectors of pairs of 600-cell vertices
    # A reflection s_v(x) = x - 2(x·v)/(v·v) * v
    # Using the 600-cell vertices themselves as reflection normals (roots of H₄)
    for i in range(len(vertices_600)):
        v = vertices_600[i]
        # Reflection matrix: R = I - 2*v*v^T / (v^T*v)
        R = np.eye(4) - 2 * np.outer(v, v) / np.dot(v, v)

        # Check: does R preserve 600-cell?
        if not check_matrix_preserves_set(R, vertices_600):
            continue  # Not an H₄ element (shouldn't happen for 600-cell roots)

        # Check: does R preserve C₀ (as a set)?
        preserves_c0 = True
        for idx in c0_indices:
            Rv = R @ vertices_600[idx]
            dists = np.linalg.norm(vertices_600 - Rv, axis=1)
            match = np.argmin(dists)
            if match not in c0_set:
                preserves_c0 = False
                break
        if preserves_c0:
            generators.append(R)

    print(f"  Reflections in H₄ that preserve C₀: {len(generators)}")

    # Also check: even coordinate permutations + sign changes
    even_perms_gens = []
    # Even permutation (0123) → (1230) — 4-cycle is odd, skip
    # Even permutation: (0123) → (0213) — transposition, odd, skip
    # Even permutation: (0123) → (1032) — product of two transpositions, even!
    for p in permutations(range(4)):
        if parity(p) != 0:
            continue
        M = np.zeros((4, 4))
        for i in range(4):
            M[i, p[i]] = 1
        if check_matrix_preserves_set(M, vertices_600):
            if check_matrix_preserves_set(M, vertices_600[c0_indices]):
                even_perms_gens.append(M)

    # Sign changes
    sign_gens = []
    for i in range(4):
        M = np.eye(4)
        M[i, i] = -1
        if check_matrix_preserves_set(M, vertices_600):
            sign_gens.append(M)

    all_gens = generators + even_perms_gens + sign_gens
    # Remove duplicates
    seen = set()
    unique_gens = []
    for g in all_gens:
        k = tuple(round(x, 5) for x in g.flatten())
        if k not in seen:
            seen.add(k)
            unique_gens.append(g)

    print(f"  Unique generators for Stab_{'{H₄}'}(C₀): {len(unique_gens)}")
    print(f"    (from reflections: {len(generators)}, "
          f"even perms: {len(even_perms_gens)}, "
          f"sign changes: {len(sign_gens)})")

    return unique_gens


def compute_stabilizer_order(generators, max_size=3000):
    """Compute the stabilizer group and its order."""
    group = generate_group_from_generators(generators, max_size=max_size)
    print(f"  |Stab_{'{H₄}'}(C₀)| = {len(group)}")
    print(f"  |H₄| / |Stab| = {14400 / len(group):.1f} "
          f"(should be 5 if H₄ transitive on 5 copies)")
    return group


# ============================================================
# §5: SPECTRAL PROJECTION — Project 600-cell eigenspaces onto 24-cell
# ============================================================
def spectral_projection_analysis(vertices_600, c0_indices, A600, A24):
    """Project 600-cell eigenspaces onto 24-cell and analyze overlaps."""
    print("\n" + "=" * 70)
    print("§5: SPECTRAL PROJECTION — 600-cell eigenspaces onto 24-cell")
    print("=" * 70)

    # Eigendecompose both adjacency matrices
    es600 = eigendecompose(A600)
    es24 = eigendecompose(A24)

    print(f"\n  600-cell adjacency eigenvalues ({len(es600)} distinct):")
    for lam in sorted(es600.keys()):
        dim = es600[lam].shape[1]
        matches = check_phi(abs(lam))
        m_str = " ← " + ", ".join(n for n, _, _ in matches) if matches else ""
        print(f"    λ = {lam:10.6f}  (dim {dim:3d}){m_str}")

    print(f"\n  24-cell adjacency eigenvalues ({len(es24)} distinct):")
    for mu in sorted(es24.keys()):
        dim = es24[mu].shape[1]
        print(f"    μ = {mu:10.6f}  (dim {dim:3d})")

    # Restriction matrix: P is 24×120, picks out C₀ rows
    P = np.zeros((len(c0_indices), len(vertices_600)))
    for i, idx in enumerate(c0_indices):
        P[i, idx] = 1.0

    # For each H₄ eigenspace W_k, compute its projection onto C₀
    print("\n  Projection norms ||P·W_k||² / ||W_k||² for each 600-cell eigenspace:")
    projection_results = []
    for lam in sorted(es600.keys()):
        W = es600[lam]  # 120 × dim_k
        PW = P @ W      # 24 × dim_k
        # Frobenius norms
        norm_W = np.linalg.norm(W, 'fro') ** 2
        norm_PW = np.linalg.norm(PW, 'fro') ** 2
        ratio = norm_PW / norm_W if norm_W > 1e-15 else 0
        dim = W.shape[1]
        matches = check_phi(ratio)
        m_str = " ← " + ", ".join(n for n, _, _ in matches) if matches else ""
        print(f"    λ={lam:9.5f} (dim {dim:3d}): "
              f"||proj||²/||orig||² = {ratio:.8f}{m_str}")
        projection_results.append({
            'eigenvalue_600': float(lam),
            'dimension': int(dim),
            'projection_norm_ratio': float(ratio),
            'phi_matches': [(n, float(t), float(e)) for n, t, e in matches]
        })

    return projection_results, es600, es24, P


# ============================================================
# §6: CG-LIKE OVERLAP MATRICES
# ============================================================
def cg_overlap_analysis(es600, es24, P, c0_indices):
    """Compute CG-like overlap matrices between H₄ and F₄ eigenspaces."""
    print("\n" + "=" * 70)
    print("§6: CG-LIKE OVERLAP MATRICES")
    print("=" * 70)

    print("\n  For each (λ_H₄, μ_F₄) pair, computing overlap M = U_jᵀ · P · V_k")
    print("  and checking singular values for φ-matches.\n")

    all_phi_hits = []
    overlap_results = []

    for lam in sorted(es600.keys()):
        V = es600[lam]    # 120 × dim_H4
        PV = P @ V        # 24 × dim_H4

        for mu in sorted(es24.keys()):
            U = es24[mu]   # 24 × dim_F4

            # Overlap matrix: M = Uᵀ · PV  (dim_F4 × dim_H4)
            M = U.T @ PV

            # Singular values of M
            if M.shape[0] > 0 and M.shape[1] > 0:
                svs = np.linalg.svd(M, compute_uv=False)
                svs = svs[svs > 1e-10]  # nonzero only
            else:
                svs = np.array([])

            # Check singular values for φ
            for sv in svs:
                matches = check_phi(sv)
                if matches:
                    all_phi_hits.append({
                        'lambda_H4': float(lam),
                        'mu_F4': float(mu),
                        'singular_value': float(sv),
                        'matches': [(n, float(t), float(e)) for n, t, e in matches]
                    })
                # Also check sv²
                matches2 = check_phi(sv**2)
                if matches2:
                    all_phi_hits.append({
                        'lambda_H4': float(lam),
                        'mu_F4': float(mu),
                        'singular_value_squared': float(sv**2),
                        'matches': [(n, float(t), float(e)) for n, t, e in matches2]
                    })

            # Also check Frobenius norm of M and individual entries
            frob = np.linalg.norm(M, 'fro')
            fmatches = check_phi(frob)
            if fmatches:
                all_phi_hits.append({
                    'lambda_H4': float(lam),
                    'mu_F4': float(mu),
                    'frobenius_norm': float(frob),
                    'matches': [(n, float(t), float(e)) for n, t, e in fmatches]
                })

            # Check individual matrix entries
            for i in range(M.shape[0]):
                for j in range(M.shape[1]):
                    val = abs(M[i, j])
                    if val > 1e-10:
                        ematches = check_phi(val)
                        if ematches:
                            all_phi_hits.append({
                                'lambda_H4': float(lam),
                                'mu_F4': float(mu),
                                'matrix_entry': f'M[{i},{j}]',
                                'value': float(val),
                                'matches': [(n, float(t), float(e))
                                            for n, t, e in ematches]
                            })

            # Summary line for non-trivial overlaps
            if len(svs) > 0:
                overlap_results.append({
                    'lambda_H4': float(lam),
                    'mu_F4': float(mu),
                    'rank': int(len(svs)),
                    'singular_values': [float(s) for s in svs],
                    'frobenius_norm': float(frob)
                })

    # Print results
    if all_phi_hits:
        print(f"  *** FOUND {len(all_phi_hits)} φ-MATCHES in CG overlaps! ***\n")
        for hit in all_phi_hits:
            print(f"    λ_H₄={hit.get('lambda_H4', '?'):.5f}, "
                  f"μ_F₄={hit.get('mu_F4', '?'):.5f}: ", end="")
            if 'singular_value' in hit:
                print(f"σ = {hit['singular_value']:.8f}", end="")
            elif 'singular_value_squared' in hit:
                print(f"σ² = {hit['singular_value_squared']:.8f}", end="")
            elif 'frobenius_norm' in hit:
                print(f"||M||_F = {hit['frobenius_norm']:.8f}", end="")
            elif 'matrix_entry' in hit:
                print(f"{hit['matrix_entry']} = {hit['value']:.8f}", end="")
            print(f" ← {', '.join(n for n,_,_ in hit['matches'])}")
    else:
        print("  No φ-matches found in CG overlap matrices.")

    return all_phi_hits, overlap_results


# ============================================================
# §7: DISTANCE-CLASS (BOSE-MESNER) ANALYSIS
# ============================================================
def bose_mesner_analysis(vertices_600, vertices_24, c0_indices):
    """Analyze ALL distance-class matrices, not just adjacency."""
    print("\n" + "=" * 70)
    print("§7: BOSE-MESNER ALGEBRA — All distance-class matrices")
    print("=" * 70)

    dm600 = build_distance_matrices(vertices_600)
    dm24 = build_distance_matrices(vertices_24)

    print(f"\n  600-cell distance classes: {len(dm600)}")
    for d, A in sorted(dm600.items()):
        deg = A.sum(axis=1)[0]
        matches = check_phi(d)
        m_str = " ← " + ", ".join(n for n, _, _ in matches) if matches else ""
        print(f"    d = {d:.6f}: degree {deg}{m_str}")

    print(f"\n  24-cell distance classes: {len(dm24)}")
    for d, A in sorted(dm24.items()):
        deg = A.sum(axis=1)[0]
        print(f"    d = {d:.6f}: degree {deg}")

    # For each 600-cell distance class, project eigenspaces onto 24-cell
    # and check for φ in the overlaps
    P = np.zeros((len(c0_indices), len(vertices_600)))
    for i, idx in enumerate(c0_indices):
        P[i, idx] = 1.0

    phi_hits_bm = []

    for d600, A600_d in sorted(dm600.items()):
        A600_f = A600_d.astype(np.float64)
        try:
            es = eigendecompose(A600_f)
        except Exception as e:
            print(f"    Skipping d={d600} (eigendecompose failed: {e})")
            continue
        for lam, V in es.items():
            if not np.all(np.isfinite(V)):
                continue
            PV = P @ V
            norm_V = np.linalg.norm(V, 'fro') ** 2
            norm_PV = np.linalg.norm(PV, 'fro') ** 2
            ratio = norm_PV / norm_V if norm_V > 1e-15 else 0
            if not np.isfinite(ratio):
                continue

            matches = check_phi(ratio)
            if matches and abs(ratio - 0.2) > 0.001:  # Skip trivial 1/5
                phi_hits_bm.append({
                    'distance_class': float(d600),
                    'eigenvalue': float(lam),
                    'dimension': int(V.shape[1]),
                    'projection_ratio': float(ratio),
                    'matches': [(n, float(t), float(e)) for n, t, e in matches]
                })

    if phi_hits_bm:
        print(f"\n  *** FOUND {len(phi_hits_bm)} non-trivial φ-matches "
              f"in Bose-Mesner projections! ***")
        for hit in phi_hits_bm:
            print(f"    d={hit['distance_class']:.4f}, "
                  f"λ={hit['eigenvalue']:.5f} (dim {hit['dimension']}): "
                  f"proj ratio = {hit['projection_ratio']:.8f} "
                  f"← {', '.join(n for n,_,_ in hit['matches'])}")
    else:
        print("\n  No non-trivial φ-matches in Bose-Mesner projections.")
        print("  (All projection ratios ≈ 1/5 as expected from H₄ transitivity)")

    return phi_hits_bm


# ============================================================
# §8: GRAM MATRIX AND REPRESENTATION-THEORETIC PROJECTIONS
# ============================================================
def gram_matrix_analysis(vertices_600, vertices_24, c0_indices):
    """Analyze the Gram matrix of the restriction and its spectral structure."""
    print("\n" + "=" * 70)
    print("§8: GRAM MATRIX ANALYSIS")
    print("=" * 70)

    V600 = vertices_600          # 120 × 4
    V24 = vertices_24            # 24 × 4

    # Cross-Gram matrix: G = V24 · V600ᵀ  (24 × 120)
    # This captures how 24-cell vertices project onto 600-cell vertices
    G = V24 @ V600.T  # inner products

    # Singular values of G
    svd_vals = np.linalg.svd(G, compute_uv=False)
    svd_vals = svd_vals[svd_vals > 1e-10]

    print(f"\n  Cross-Gram matrix G = V₂₄ · V₆₀₀ᵀ  ({G.shape})")
    print(f"  Nonzero singular values: {len(svd_vals)}")
    for i, sv in enumerate(svd_vals):
        matches = check_phi(sv)
        m_str = " ← " + ", ".join(n for n, _, _ in matches) if matches else ""
        print(f"    σ_{i+1} = {sv:.8f}{m_str}")

    # Inner product matrix: I₂₄ = V24 · V24ᵀ  (24 × 24)
    I24 = V24 @ V24.T
    evals24 = np.linalg.eigvalsh(I24)
    evals24 = evals24[abs(evals24) > 1e-10]
    print(f"\n  24-cell inner product matrix eigenvalues:")
    for ev in sorted(set(np.round(evals24, 6))):
        mult = np.sum(np.abs(evals24 - ev) < 1e-4)
        matches = check_phi(abs(ev))
        m_str = " ← " + ", ".join(n for n, _, _ in matches) if matches else ""
        print(f"    {ev:.8f} (mult {mult}){m_str}")

    # Frame operator restricted: F = V600[c0]ᵀ · V600[c0]  (4 × 4)
    V_c0 = vertices_600[c0_indices]  # 24 × 4
    F = V_c0.T @ V_c0  # 4 × 4
    print(f"\n  Frame operator F = Σ|v⟩⟨v| for C₀ vertices (4×4):")
    print(f"    F = {F[0,0]:.4f} · I₄")
    print(f"    Tr(F) = {np.trace(F):.4f}")
    print(f"    Tr(F)/4 = {np.trace(F)/4:.4f}")

    phi_hits = []

    # Check singular value ratios
    if len(svd_vals) >= 2:
        for i in range(len(svd_vals)):
            for j in range(i + 1, len(svd_vals)):
                if svd_vals[j] > 1e-10:
                    ratio = svd_vals[i] / svd_vals[j]
                    matches = check_phi(ratio)
                    if matches:
                        phi_hits.append({
                            'type': 'sv_ratio',
                            'i': i, 'j': j,
                            'ratio': float(ratio),
                            'matches': [(n, float(t), float(e))
                                        for n, t, e in matches]
                        })

    return phi_hits


# ============================================================
# §9: QUATERNIONIC CG COEFFICIENTS
# ============================================================
def quaternionic_cg_analysis(vertices_600, c0_indices, all_24_cells):
    """Analyze quaternionic structure for CG-like coefficients.

    The 600-cell vertices form the binary icosahedral group 2I under
    quaternion multiplication. The 24-cell is the subgroup 2T.
    Coset decomposition: 2I = 2T ∪ g₁·2T ∪ g₂·2T ∪ g₃·2T ∪ g₄·2T

    The coset representatives g₁,...,g₄ and their properties may involve φ.
    """
    print("\n" + "=" * 70)
    print("§9: QUATERNIONIC CG ANALYSIS")
    print("=" * 70)

    c0_verts = vertices_600[c0_indices]

    # Find coset representatives (one vertex from each non-identity 24-cell)
    coset_reps = []
    for copy_idx, copy in enumerate(all_24_cells):
        if copy == c0_indices:
            continue
        rep = vertices_600[copy[0]]
        coset_reps.append((copy_idx, rep))

    print(f"\n  Coset representatives (one from each of 4 non-identity 24-cells):")
    for idx, rep in coset_reps:
        matches = []
        for comp in rep:
            m = check_phi(abs(comp))
            matches.extend(m)
        m_str = ""
        if matches:
            m_str = " ← components match: " + ", ".join(
                set(n for n, _, _ in matches))
        print(f"    C_{idx}: {rep}  {m_str}")

    # For each coset representative g, compute:
    # The "intertwiner" T_g: C₀ → C_k defined by T_g(v) = g*v (quaternion mult)
    # In matrix form: T_g is a 4×4 matrix (left multiplication by g)
    phi_hits = []

    print("\n  Left-multiplication matrices L_g for coset representatives:")
    for idx, g in coset_reps:
        # L_g: v → g*v as a 4×4 real matrix
        # q = (a,b,c,d), Lq = [[a,-b,-c,-d],[b,a,-d,c],[c,d,a,-b],[d,-c,b,a]]
        a, b, c, d = g
        L = np.array([
            [a, -b, -c, -d],
            [b,  a, -d,  c],
            [c,  d,  a, -b],
            [d, -c,  b,  a]
        ])

        # Eigenvalues of L
        evals = np.linalg.eigvals(L)
        print(f"\n    L_{idx} eigenvalues: "
              f"{[f'{ev:.6f}' for ev in sorted(evals, key=lambda x: x.real)]}")
        print(f"    det(L_{idx}) = {np.linalg.det(L):.6f}")
        print(f"    tr(L_{idx}) = {np.trace(L):.6f} = 4·Re(g) = 4×{a:.6f}")

        # Check trace and eigenvalue magnitudes for φ
        for ev in evals:
            for val in [abs(ev), ev.real, ev.imag]:
                if abs(val) > 1e-10:
                    matches = check_phi(abs(val))
                    if matches:
                        phi_hits.append({
                            'coset': idx,
                            'type': 'L_eigenvalue',
                            'value': float(abs(val)),
                            'matches': [(n, float(t), float(e))
                                        for n, t, e in matches]
                        })
                        print(f"      *** eigenvalue component {val:.8f} "
                              f"matches {', '.join(n for n,_,_ in matches)}")

        # The "projection coefficient": how much of g*v lands back in C₀
        # For v ∈ C₀, g*v ∈ g·C₀ (a different 24-cell). So the projection
        # of g*v onto C₀ depends on the overlap between the two 24-cells.
        # This is captured by: P_C₀ · L_g acting on the 24-cell vertex space

        # Compute overlap: for each pair (v,w) with v ∈ C₀, w ∈ g·C₀,
        # inner product ⟨v, w⟩ = Re(v̄·w) = Re(v̄·g·t) for some t ∈ C₀
        overlap_matrix = c0_verts @ L @ c0_verts.T  # 24×4 @ 4×4 @ 4×24 = 24×24
        # This gives ⟨v_i, L_g · v_j⟩ for v_i, v_j ∈ C₀

        # Singular values of overlap
        ov_svs = np.linalg.svd(overlap_matrix, compute_uv=False)
        ov_svs = ov_svs[ov_svs > 1e-10]
        print(f"    Overlap matrix ⟨C₀|L_g|C₀⟩ singular values "
              f"(first 5): {[f'{s:.6f}' for s in ov_svs[:5]]}")

        for sv in ov_svs:
            matches = check_phi(sv)
            if matches:
                phi_hits.append({
                    'coset': idx,
                    'type': 'overlap_sv',
                    'value': float(sv),
                    'matches': [(n, float(t), float(e)) for n, t, e in matches]
                })
                print(f"      *** overlap SV {sv:.8f} matches "
                      f"{', '.join(n for n,_,_ in matches)}")

    return phi_hits


# ============================================================
# §10: COMPREHENSIVE φ SEARCH IN REPRESENTATION-THEORETIC QUANTITIES
# ============================================================
def comprehensive_phi_search(vertices_600, vertices_24, c0_indices,
                             A600, A24, es600, es24, P):
    """Search for φ in every conceivable representation-theoretic quantity."""
    print("\n" + "=" * 70)
    print("§10: COMPREHENSIVE φ SEARCH")
    print("=" * 70)

    all_hits = []

    # 1. Idempotent projectors of the 600-cell Bose-Mesner algebra
    # For a distance-regular graph, the idempotent projectors E_k
    # satisfy A = Σ_k θ_k E_k. The E_k projected onto C₀ give the
    # "spherical functions" of the H₄ representation.
    print("\n  [1] Idempotent projectors of 600-cell adjacency:")
    for lam, V in sorted(es600.items()):
        # Projector: E_lam = V · V^T / dim (if V columns are orthonormal)
        # V^T V should be identity since eigenvectors are orthonormal
        dim = V.shape[1]
        E = V @ V.T  # 120 × 120 projector (rank = dim)

        # Restrict to C₀ × C₀ block
        E_c0 = E[np.ix_(c0_indices, c0_indices)]  # 24 × 24

        # Trace of E_c0
        tr = np.trace(E_c0)
        expected_tr = dim * 24 / 120  # = dim/5 if uniform
        deviation = abs(tr - expected_tr)

        if deviation > 0.01:
            matches = check_phi(tr)
            if matches:
                all_hits.append({
                    'section': 'idempotent_trace',
                    'eigenvalue': float(lam),
                    'trace': float(tr),
                    'expected': float(expected_tr),
                    'matches': [(n, float(t), float(e)) for n, t, e in matches]
                })
                print(f"    λ={lam:.5f}: Tr(E|C₀) = {tr:.6f} "
                      f"(expected {expected_tr:.1f}) "
                      f"← {', '.join(n for n,_,_ in matches)}")

        # Eigenvalues of E_c0
        evals_ec0 = np.linalg.eigvalsh(E_c0)
        unique_evals = sorted(set(round(e, 6) for e in evals_ec0
                                  if abs(e) > 1e-8))
        for ev in unique_evals:
            matches = check_phi(abs(ev))
            if matches:
                all_hits.append({
                    'section': 'idempotent_eigenvalue',
                    'lambda_600': float(lam),
                    'eigenvalue': float(ev),
                    'matches': [(n, float(t), float(e)) for n, t, e in matches]
                })
                print(f"    λ={lam:.5f}: E|C₀ eigenvalue {ev:.8f} "
                      f"← {', '.join(n for n,_,_ in matches)}")

    # 2. Zonal spherical functions
    print("\n  [2] Zonal spherical functions (diagonal of E|C₀):")
    for lam, V in sorted(es600.items()):
        E = V @ V.T
        diag_c0 = np.array([E[i, i] for i in c0_indices])
        unique_diag = sorted(set(round(d, 8) for d in diag_c0))
        for dv in unique_diag:
            if abs(dv) > 1e-10:
                matches = check_phi(abs(dv))
                if matches:
                    all_hits.append({
                        'section': 'zonal_function',
                        'eigenvalue': float(lam),
                        'zonal_value': float(dv),
                        'matches': [(n, float(t), float(e))
                                    for n, t, e in matches]
                    })
                    print(f"    λ={lam:.5f}: zonal = {dv:.8f} "
                          f"← {', '.join(n for n,_,_ in matches)}")

    # 3. Transfer matrix: T = exp(-β·L_600) restricted to C₀
    # This is the "propagator" from 600-cell dynamics
    print("\n  [3] Transfer matrix eigenvalues for various β:")
    L600 = np.diag(A600.sum(axis=1)) - A600  # Graph Laplacian
    for beta in [0.1, 0.5, 1.0, np.log(PHI), 1/PHI, PHI]:
        T = np.eye(120)
        # Use eigendecomposition for matrix exponential
        evals_L, evecs_L = np.linalg.eigh(L600)
        T = evecs_L @ np.diag(np.exp(-beta * evals_L)) @ evecs_L.T
        # Restrict to C₀
        T_c0 = T[np.ix_(c0_indices, c0_indices)]
        evals_T = np.linalg.eigvalsh(T_c0)
        # Check eigenvalue ratios
        evals_T = sorted(evals_T[abs(evals_T) > 1e-15], reverse=True)
        if len(evals_T) >= 2:
            ratio = evals_T[0] / evals_T[1] if evals_T[1] > 1e-15 else 0
            matches = check_phi(ratio)
            if matches:
                all_hits.append({
                    'section': 'transfer_matrix',
                    'beta': float(beta),
                    'eigenvalue_ratio': float(ratio),
                    'matches': [(n, float(t), float(e)) for n, t, e in matches]
                })
                print(f"    β={beta:.4f}: λ₁/λ₂ = {ratio:.8f} "
                      f"← {', '.join(n for n,_,_ in matches)}")

    # 4. Normalized overlap: how H₄ irreps decompose on C₀
    print("\n  [4] Normalized CG matrix norms (per irrep pair):")
    for lam in sorted(es600.keys()):
        V = es600[lam]
        PV = P @ V
        for mu in sorted(es24.keys()):
            U = es24[mu]
            M = U.T @ PV
            if M.size == 0:
                continue
            # Normalized Frobenius norm²
            norm2 = np.linalg.norm(M, 'fro') ** 2
            dim_H = V.shape[1]
            dim_F = U.shape[1]
            # Normalize by geometric mean of dimensions
            norm_geo = norm2 / np.sqrt(dim_H * dim_F) if dim_H * dim_F > 0 else 0
            matches = check_phi(norm_geo)
            if matches:
                all_hits.append({
                    'section': 'normalized_cg',
                    'lambda_H4': float(lam),
                    'mu_F4': float(mu),
                    'normalized_norm': float(norm_geo),
                    'matches': [(n, float(t), float(e)) for n, t, e in matches]
                })
                print(f"    (λ={lam:.4f}, μ={mu:.4f}): "
                      f"||M||²/√(d₁d₂) = {norm_geo:.8f} "
                      f"← {', '.join(n for n,_,_ in matches)}")

    print(f"\n  Total φ-hits in comprehensive search: {len(all_hits)}")
    return all_hits


# ============================================================
# MAIN
# ============================================================
def main():
    print("=" * 70)
    print("PATH A: H₄ → F₄ BRANCHING COEFFICIENTS")
    print("Research Plan §11.2 — Searching for 1/φ in CG coefficients")
    print("=" * 70)

    results = {
        'title': 'Path A: H₄ → F₄ Branching Coefficients',
        'timestamp': datetime.now().isoformat(),
        'goal': 'Find 1/φ in Clebsch-Gordan coefficients of H₄ ↓ F₄',
        'sections': {}
    }

    # Build geometry
    print("\n  Building 600-cell...")
    vertices_600 = build_600_cell()
    print(f"  600-cell: {len(vertices_600)} vertices")

    c0_indices = find_c0(vertices_600)
    print(f"  24-cell C₀: {len(c0_indices)} vertices")
    vertices_24 = vertices_600[c0_indices]

    all_24_cells = find_24_cells(vertices_600, c0_indices)
    print(f"  Found {len(all_24_cells)} copies of the 24-cell")

    # Build adjacency matrices
    print("\n  Building adjacency matrices...")
    edge_600 = INV_PHI  # 600-cell edge length = 1/φ
    A600 = build_adjacency(vertices_600, edge_600)
    deg600 = A600.sum(axis=1)
    print(f"  600-cell: edge length {edge_600:.6f}, "
          f"degree {deg600[0]} (uniform: {np.all(deg600 == deg600[0])})")

    edge_24 = 1.0  # 24-cell edge length
    A24 = build_adjacency(vertices_24, edge_24)
    deg24 = A24.sum(axis=1)
    print(f"  24-cell: edge length {edge_24:.6f}, "
          f"degree {deg24[0]} (uniform: {np.all(deg24 == deg24[0])})")

    # §3: Check F₄ ⊄ H₄
    f4_h4_results = verify_f4_not_in_h4(vertices_600, vertices_24)
    results['sections']['f4_not_in_h4'] = f4_h4_results

    # §4: Stabilizer
    stab_gens = find_h4_generators_preserving_c0(vertices_600, c0_indices)
    if len(stab_gens) > 0:
        print("\n  Generating stabilizer group (may take a moment)...")
        stab_group = compute_stabilizer_order(stab_gens, max_size=3000)
        results['sections']['stabilizer'] = {
            'n_generators': len(stab_gens),
            'group_order': len(stab_group)
        }
    else:
        print("  WARNING: No stabilizer generators found")
        stab_group = []
        results['sections']['stabilizer'] = {
            'n_generators': 0,
            'group_order': 0
        }

    # §5: Spectral projection
    proj_results, es600, es24, P = spectral_projection_analysis(
        vertices_600, c0_indices, A600, A24)
    results['sections']['spectral_projection'] = proj_results

    # §6: CG overlap matrices
    cg_hits, overlap_results = cg_overlap_analysis(es600, es24, P, c0_indices)
    results['sections']['cg_overlaps'] = {
        'phi_hits': cg_hits,
        'overlap_summary': overlap_results[:20]  # First 20
    }

    # §7: Bose-Mesner analysis
    bm_hits = bose_mesner_analysis(vertices_600, vertices_24, c0_indices)
    results['sections']['bose_mesner'] = bm_hits

    # §8: Gram matrix analysis
    gram_hits = gram_matrix_analysis(vertices_600, vertices_24, c0_indices)
    results['sections']['gram_matrix'] = gram_hits

    # §9: Quaternionic CG analysis
    qcg_hits = quaternionic_cg_analysis(
        vertices_600, c0_indices, all_24_cells)
    results['sections']['quaternionic_cg'] = qcg_hits

    # §10: Comprehensive search
    comp_hits = comprehensive_phi_search(
        vertices_600, vertices_24, c0_indices, A600, A24, es600, es24, P)
    results['sections']['comprehensive_search'] = comp_hits

    # ============================================================
    # VERDICT
    # ============================================================
    all_phi_hits = cg_hits + bm_hits + gram_hits + qcg_hits + comp_hits

    print("\n" + "=" * 70)
    print("VERDICT")
    print("=" * 70)

    results['total_phi_hits'] = len(all_phi_hits)

    if len(all_phi_hits) > 0:
        # Check specifically for 1/φ
        inv_phi_hits = [h for h in all_phi_hits
                        if any(n == '1/φ' for n, _, _ in h.get('matches', []))]
        print(f"\n  Total φ-related hits: {len(all_phi_hits)}")
        print(f"  Hits specifically matching 1/φ: {len(inv_phi_hits)}")

        if inv_phi_hits:
            print("\n  *** 1/φ CANDIDATES FOUND: ***")
            for hit in inv_phi_hits:
                print(f"    {hit}")
            results['verdict'] = 'POSITIVE — 1/φ candidates found'
            results['inv_phi_hits'] = inv_phi_hits
        else:
            print("\n  φ-related quantities found but none equals 1/φ exactly.")
            print("  Investigating whether alternative decompositions are suggested...")
            results['verdict'] = 'PARTIAL — φ-related but no 1/φ'
            results['all_phi_hits_summary'] = [
                {k: v for k, v in h.items() if k != 'matches'}
                for h in all_phi_hits[:20]
            ]
    else:
        print("\n  NO φ-related quantities found in any CG-type coefficient.")
        print("  The representation-theoretic decomposition H₄ → F₄ does not")
        print("  produce 1/φ through standard branching mechanisms.")
        results['verdict'] = 'NEGATIVE — no φ in CG coefficients'

    # Check the critical structural finding
    f4_in_h4 = all(r['preserves_600_cell'] for r in f4_h4_results
                    if r['preserves_24_cell'])
    if not f4_in_h4:
        print(f"\n  KEY STRUCTURAL FINDING: F₄ ⊄ H₄")
        print(f"  The standard branching rules H₄ ↓ F₄ do not apply.")
        print(f"  The relevant decomposition is H₄ ↓ Stab_{'{H₄}'}(C₀),")
        print(f"  where |Stab| = {len(stab_group) if stab_group else '?'}")
        results['f4_subset_h4'] = False
    else:
        results['f4_subset_h4'] = True

    # Save results
    output_path = os.path.join(os.path.dirname(__file__),
                                'path_a_branching_coefficients_results.json')
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\n  Results saved to {output_path}")

    return results


if __name__ == '__main__':
    main()
