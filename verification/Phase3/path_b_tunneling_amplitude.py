#!/usr/bin/env python3
"""
Path B: Tunneling Amplitude Between 16-Cell Sectors
=====================================================

Research Plan §11.2 Path B — Tests whether the "missing Factor 2" (1/φ at the
24-cell → 16-cell level) emerges from DYNAMICAL quantities rather than static
geometric ratios.

Core hypothesis:
    The 600-cell embedding defines an energy landscape on the 24-cell.
    The tunneling amplitude between orthogonal 16-cell sectors, governed by
    this H₄-sourced potential, may equal 1/φ — providing the missing factor
    in the Cabibbo angle formula λ = (1/φ³) × sin(72°).

Key insight (from §11.1):
    Static geometric quantities at the 24→16 level (volumes, radii, edges)
    show NO φ. But the DYNAMICS of transitions — governed by the parent H₄
    symmetry — might carry φ as a "latent geometric factor."

Approaches implemented:
    1. 600-cell neighbor potential on 24-cell vertices
    2. WKB tunneling amplitude along inter-sector paths
    3. Transfer matrix / propagator spectral analysis
    4. Graph Laplacian with H₄ potential: spectral gaps
    5. Action-weighted path sums (path integral approach)
    6. Triality holonomy (Berry phase, basic)

Success criterion: Any computed amplitude = 1/φ ≈ 0.6180

Related Documents:
    - Derivation: docs/proofs/supporting/Derivation-Three-Phi-Factors-Explicit.md §11
    - Prior search: verification/Phase3/explore_600_cell_phi_ratios.py
    - Proof: docs/proofs/Phase3/Lemma-3.1.2a-24-Cell-Two-Tetrahedra-Connection.md

Verification Date: 2026-02-07
"""

import numpy as np
from itertools import product as iter_product, combinations, permutations
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
LN_PHI = np.log(PHI)  # ≈ 0.48121

# φ-related targets (extended from explore script)
PHI_TARGETS = {
    'φ':        PHI,
    '1/φ':      INV_PHI,
    'φ²':       PHI**2,
    '1/φ²':     1/PHI**2,
    'φ³':       PHI**3,
    '1/φ³':     1/PHI**3,
    '√φ':       np.sqrt(PHI),
    '1/√φ':     1/np.sqrt(PHI),
    'ln(φ)':    LN_PHI,
    '2ln(φ)':   2*LN_PHI,
    'φ/2':      PHI/2,
    '1/(2φ)':   1/(2*PHI),
    'sin72°':   np.sin(np.radians(72)),
    'sin36°':   np.sin(np.radians(36)),
    'cos72°':   np.cos(np.radians(72)),
    'cos36°':   np.cos(np.radians(36)),
    '√5':       SQRT5,
    '2/√5':     2/SQRT5,
    '1/√5':     1/SQRT5,
    '√(2+φ)':   np.sqrt(2+PHI),
    '(√5-1)/2': (SQRT5-1)/2,    # = 1/φ
    '(√5-2)':   SQRT5-2,        # = 1/φ³
    '√3/2':     np.sqrt(3)/2,
    '1/√3':     1/np.sqrt(3),
    '1/3':      1/3,
    '1/√2':     1/np.sqrt(2),
    'π/5':      np.pi/5,
    '2π/5':     2*np.pi/5,
    'e^(-ln φ)': np.exp(-LN_PHI),  # = 1/φ (consistency check)
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


def fmt_matches(matches):
    """Format match list for printing."""
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
# 600-CELL CONSTRUCTION (from explore_600_cell_phi_ratios.py)
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

    # Group 3: 96 golden vertices
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


# ============================================================
# BUILD 24-CELL ADJACENCY (edges of distance 1.0)
# ============================================================
def build_24cell_adjacency(vertices, c0_indices):
    """Build adjacency matrix for the 24-cell graph (edges at distance 1.0)."""
    n = len(c0_indices)
    adj = np.zeros((n, n), dtype=int)
    verts = vertices[c0_indices]
    for i in range(n):
        for j in range(i + 1, n):
            d = np.linalg.norm(verts[i] - verts[j])
            if abs(d - 1.0) < 0.05:
                adj[i, j] = adj[j, i] = 1
    return adj


# ============================================================
# PART 1: DEFINE POTENTIALS FROM 600-CELL EMBEDDING
# ============================================================
def compute_potentials(V, c0, all_600_adj):
    """
    Define multiple potentials on the 24-cell vertices from the 600-cell
    embedding. Each potential captures a different aspect of the H₄ → F₄
    relationship.

    Returns dict of {potential_name: array of V(v) for v in c0}.
    """
    n = len(c0)
    c0_set = set(c0)
    potentials = {}

    # --- Potential A: Number of 600-cell neighbors OUTSIDE C₀ ---
    # V_A(v) = #{j : j ∉ C₀ and |v-j| = 1/φ (600-cell edge)}
    # This measures the "external pull" from the H₄ embedding
    pot_a = np.zeros(n)
    for i, idx in enumerate(c0):
        outside = 0
        for j in range(len(V)):
            if all_600_adj[idx, j] and j not in c0_set:
                outside += 1
        pot_a[i] = outside
    potentials['A: ext_neighbors'] = pot_a

    # --- Potential B: Number of 600-cell neighbors INSIDE C₀ ---
    # V_B(v) = #{j : j ∈ C₀ and |v-j| = 1/φ}
    pot_b = np.zeros(n)
    for i, idx in enumerate(c0):
        inside = 0
        for j in range(len(V)):
            if all_600_adj[idx, j] and j in c0_set:
                inside += 1
        pot_b[i] = inside
    potentials['B: int_neighbors'] = pot_b

    # --- Potential C: Total 600-cell degree (should be 12 for all) ---
    pot_c = np.zeros(n)
    for i, idx in enumerate(c0):
        pot_c[i] = np.sum(all_600_adj[idx])
    potentials['C: total_degree'] = pot_c

    # --- Potential D: Sum of inner products with non-C₀ neighbors ---
    # V_D(v) = Σ_{j∉C₀, adj} ⟨v|j⟩
    # Captures the "direction" of the H₄ pull
    pot_d = np.zeros(n)
    for i, idx in enumerate(c0):
        total_ip = 0.0
        for j in range(len(V)):
            if all_600_adj[idx, j] and j not in c0_set:
                total_ip += np.dot(V[idx], V[j])
        pot_d[i] = total_ip
    potentials['D: ext_inner_product'] = pot_d

    # --- Potential E: Distance to nearest non-C₀ 600-cell vertex ---
    # V_E(v) = min_{j∉C₀} |v - j|  (not restricted to edges)
    pot_e = np.zeros(n)
    non_c0 = [j for j in range(len(V)) if j not in c0_set]
    for i, idx in enumerate(c0):
        min_d = np.inf
        for j in non_c0:
            d = np.linalg.norm(V[idx] - V[j])
            if d < min_d:
                min_d = d
        pot_e[i] = min_d
    potentials['E: min_dist_ext'] = pot_e

    # --- Potential F: Weighted sum over ALL other 24-cell copies ---
    # V_F(v) = Σ_{k=1}^{4} Σ_{w ∈ C_k} 1/|v - w|²
    # This is a "Coulomb-like" potential from the other 4 copies
    # (We compute this after finding all 5 copies)
    # --> handled separately in main

    # --- Potential G: Projection onto golden vertex subspace ---
    # The 96 golden vertices form a specific subspace of ℝ⁴.
    # V_G(v) = ||P_golden × v||²  where P_golden projects onto golden subspace
    golden_idx = [j for j in range(len(V)) if j not in c0_set]
    golden_verts = V[golden_idx]
    # SVD of golden vertex matrix
    U, S, Vt = np.linalg.svd(golden_verts, full_matrices=False)
    # Since golden verts span all of R⁴, this projection is trivial
    # Instead: project onto the COMPLEMENT within the golden subspace
    # V_G = Σ (v · g_i)² where g_i are golden vertices (unnormalized)
    pot_g = np.zeros(n)
    for i, idx in enumerate(c0):
        v = V[idx]
        pot_g[i] = np.sum(np.dot(golden_verts, v)**2)
    potentials['G: golden_projection'] = pot_g

    return potentials


# ============================================================
# PART 2: WKB TUNNELING AMPLITUDE
# ============================================================
def wkb_tunneling(potential, adj_24, gammas_local, vertices_24):
    """
    Compute WKB tunneling amplitude between 16-cell sectors.

    For a discrete 1D path through vertices with potential V(v),
    the WKB action is:
        S = Σ_path √(V(v) - V_min) × Δx

    where Δx = edge length on the 24-cell (= 1 for unit circumradius).

    Returns dict with amplitudes for each pair of 16-cell sectors.
    """
    n = len(potential)

    # Map local indices to 16-cell membership
    gamma_membership = {}
    for gi, gamma in enumerate(gammas_local):
        for idx in gamma:
            gamma_membership[idx] = gi

    # Find shortest paths between 16-cell sectors using BFS
    def bfs_paths(start_sector, end_sector):
        """Find ALL shortest paths from any vertex in start_sector
        to any vertex in end_sector."""
        start_nodes = gammas_local[start_sector]
        end_set = set(gammas_local[end_sector])

        # BFS from all start nodes simultaneously
        from collections import deque
        queue = deque()
        # (node, path)
        for s in start_nodes:
            queue.append((s, [s]))

        visited_at_depth = {}
        all_paths = []
        min_depth = float('inf')

        while queue:
            node, path = queue.popleft()
            if len(path) > min_depth:
                break

            if node in end_set:
                all_paths.append(path)
                min_depth = len(path)
                continue

            if node in visited_at_depth and visited_at_depth[node] < len(path):
                continue
            visited_at_depth[node] = len(path)

            for j in range(n):
                if adj_24[node, j] and j not in set(path):
                    queue.append((j, path + [j]))

        return all_paths

    results = {}
    V_min = np.min(potential)

    for i, j in combinations(range(3), 2):
        paths = bfs_paths(i, j)
        if not paths:
            results[f'Γ{i}→Γ{j}'] = {'amplitude': 0, 'action': np.inf, 'paths': 0}
            continue

        # Compute WKB action for each path
        actions = []
        for path in paths:
            # Action = sum of √(V - V_min) along path
            # Use midpoint rule: barrier at intermediate vertices
            S = 0.0
            for k in range(1, len(path) - 1):
                v_k = potential[path[k]]
                S += np.sqrt(max(0, v_k - V_min))
            # Edge length on 24-cell = 1.0
            actions.append(S)

        # The dominant tunneling comes from the path with MINIMUM action
        S_min = min(actions) if actions else 0
        S_avg = np.mean(actions) if actions else 0

        # Also compute the path-integral sum (sum over all paths)
        path_integral = sum(np.exp(-S) for S in actions)

        results[f'Γ{i}→Γ{j}'] = {
            'S_min': S_min,
            'S_avg': S_avg,
            'amplitude_min': np.exp(-S_min) if S_min < 100 else 0,
            'amplitude_avg': np.exp(-S_avg) if S_avg < 100 else 0,
            'path_integral': path_integral,
            'n_paths': len(paths),
            'path_length': len(paths[0]) if paths else 0,
        }

    return results


# ============================================================
# PART 3: TRANSFER MATRIX / PROPAGATOR
# ============================================================
def transfer_matrix_analysis(V, c0, gammas, adj_24, all_600_adj):
    """
    Construct the transfer matrix T between 16-cell sectors.

    T_ij = ⟨Γ_i | e^{-H} | Γ_j⟩

    where H is the graph Hamiltonian on the 24-cell with 600-cell potential.

    Also computes the Green's function (resolvent) and its spectral properties.
    """
    n = len(c0)
    c0_set = set(c0)

    # Map global vertex indices to local 0..23 indices
    global_to_local = {g: i for i, g in enumerate(c0)}

    # --- Hamiltonian: -Δ + V on 24-cell graph ---
    # Δ = D - A (graph Laplacian), D = degree matrix, A = adjacency
    D = np.diag(np.sum(adj_24, axis=1).astype(float))
    A = adj_24.astype(float)
    laplacian = D - A

    # Multiple Hamiltonians with different potentials
    results = {}

    # External neighbor potential (most physically motivated)
    pot = np.zeros(n)
    for i, idx in enumerate(c0):
        outside = 0
        for j in range(len(V)):
            if all_600_adj[idx, j] and j not in c0_set:
                outside += 1
        pot[i] = outside

    # Normalize potential to [0, 1]
    pot_range = np.max(pot) - np.min(pot)
    if pot_range > 0:
        pot_norm = (pot - np.min(pot)) / pot_range
    else:
        pot_norm = np.zeros(n)

    # Build projectors onto each 16-cell sector
    gamma_projectors = []
    for gamma in gammas:
        local_idx = [global_to_local[g] for g in gamma]
        P = np.zeros((n, n))
        for k in local_idx:
            P[k, k] = 1.0 / len(local_idx)  # Normalized projector
        gamma_projectors.append(P)

    # --- Analysis for multiple coupling strengths ---
    for alpha_label, alpha in [('weak', 0.1), ('moderate', 0.5),
                                ('unit', 1.0), ('strong', 2.0),
                                ('ln(φ)', LN_PHI), ('1/φ', INV_PHI),
                                ('φ', PHI)]:
        V_diag = np.diag(alpha * pot_norm)
        H = laplacian + V_diag

        # Eigendecomposition
        eigvals, eigvecs = np.linalg.eigh(H)

        # Transfer matrix T = e^{-H}
        T = eigvecs @ np.diag(np.exp(-eigvals)) @ eigvecs.T

        # Sector-to-sector amplitudes: T_ij = Tr(P_i T P_j)
        sector_T = np.zeros((3, 3))
        for i in range(3):
            for j in range(3):
                sector_T[i, j] = np.trace(gamma_projectors[i] @ T @ gamma_projectors[j])

        # Off-diagonal elements = tunneling amplitudes
        off_diag = [sector_T[0, 1], sector_T[0, 2], sector_T[1, 2]]

        # Spectral gap
        spectral_gap = eigvals[1] - eigvals[0] if len(eigvals) > 1 else 0

        # Green's function at E=0: G = H^{-1} (pseudo-inverse)
        # Since Laplacian has zero mode, use pseudo-inverse
        try:
            H_pinv = np.linalg.pinv(H)
            sector_G = np.zeros((3, 3))
            for i in range(3):
                for j in range(3):
                    sector_G[i, j] = np.trace(gamma_projectors[i] @ H_pinv @ gamma_projectors[j])
            green_off_diag = [sector_G[0, 1], sector_G[0, 2], sector_G[1, 2]]
        except Exception:
            green_off_diag = [0, 0, 0]

        results[alpha_label] = {
            'alpha': alpha,
            'eigvals_first5': eigvals[:5].tolist(),
            'spectral_gap': spectral_gap,
            'sector_T': sector_T.tolist(),
            'tunneling_01': off_diag[0],
            'tunneling_02': off_diag[1],
            'tunneling_12': off_diag[2],
            'green_01': green_off_diag[0],
            'green_02': green_off_diag[1],
            'green_12': green_off_diag[2],
        }

    return results


# ============================================================
# PART 4: GRAPH LAPLACIAN SPECTRAL ANALYSIS
# ============================================================
def laplacian_spectral_analysis(V, c0, gammas, adj_24, all_600_adj):
    """
    Study the spectrum of the graph Laplacian on the 24-cell,
    modified by the 600-cell embedding potential.

    Key question: Do spectral ratios or gaps involve φ?
    """
    n = len(c0)
    c0_set = set(c0)

    # Pure 24-cell Laplacian (no potential)
    D = np.diag(np.sum(adj_24, axis=1).astype(float))
    A = adj_24.astype(float)
    L0 = D - A

    eigvals_0, eigvecs_0 = np.linalg.eigh(L0)

    results = {'pure_24cell': {
        'eigenvalues': sorted(set(np.round(eigvals_0, 6))),
        'multiplicities': [],
    }}

    # Count multiplicities
    unique_eigs = sorted(set(np.round(eigvals_0, 6)))
    for e in unique_eigs:
        mult = np.sum(np.abs(eigvals_0 - e) < 0.001)
        results['pure_24cell']['multiplicities'].append((e, int(mult)))

    # External neighbor potential
    pot = np.zeros(n)
    for i, idx in enumerate(c0):
        for j in range(len(V)):
            if all_600_adj[idx, j] and j not in c0_set:
                pot[i] += 1

    # Normalized Laplacian with potential
    for alpha_label, alpha in [('0.1', 0.1), ('0.5', 0.5), ('1.0', 1.0),
                                ('ln(φ)', LN_PHI), ('1/φ', INV_PHI), ('φ', PHI)]:
        L = L0 + alpha * np.diag(pot - np.min(pot))
        eigvals, _ = np.linalg.eigh(L)

        # Spectral ratios
        nonzero_eigs = eigvals[eigvals > 0.001]
        spectral_ratios = {}
        if len(nonzero_eigs) >= 2:
            spectral_ratios['λ₂/λ₁'] = nonzero_eigs[1] / nonzero_eigs[0]
            spectral_ratios['λ₃/λ₁'] = nonzero_eigs[2] / nonzero_eigs[0] if len(nonzero_eigs) > 2 else None
            spectral_ratios['λ₃/λ₂'] = nonzero_eigs[2] / nonzero_eigs[1] if len(nonzero_eigs) > 2 else None
            spectral_ratios['gap'] = nonzero_eigs[0]

        results[f'α={alpha_label}'] = {
            'eigenvalues_first8': eigvals[:8].tolist(),
            'spectral_ratios': {k: v for k, v in spectral_ratios.items() if v is not None},
        }

    return results


# ============================================================
# PART 5: ACTION-WEIGHTED PATH SUMS
# ============================================================
def action_path_sums(V, c0, gammas, adj_24, all_600_adj):
    """
    Path-integral style computation: sum over ALL paths from one
    16-cell sector to another, weighted by e^{-S[path]}.

    The action S[path] is defined by the 600-cell potential along the path.

    This tests whether the TOTAL tunneling amplitude (not just WKB
    through the minimum-action path) gives 1/φ.
    """
    n = len(c0)
    c0_set = set(c0)

    # External neighbor potential
    pot = np.zeros(n)
    for i, idx in enumerate(c0):
        for j in range(len(V)):
            if all_600_adj[idx, j] and j not in c0_set:
                pot[i] += 1

    # Map global to local
    global_to_local = {g: i for i, g in enumerate(c0)}

    # Gammas in local indices
    gammas_local = [[global_to_local[g] for g in gamma] for gamma in gammas]

    # Find all paths of length up to max_length between sectors using DFS
    def all_paths_between(start_set, end_set, max_length=6):
        """Find all simple paths from start_set to end_set."""
        paths = []
        for start in start_set:
            stack = [(start, [start])]
            while stack:
                node, path = stack.pop()
                if len(path) > max_length:
                    continue
                if node in end_set and len(path) > 1:
                    paths.append(list(path))
                    continue
                for j in range(n):
                    if adj_24[node, j] and j not in set(path):
                        stack.append((j, path + [j]))
        return paths

    results = {}
    pot_norm = pot - np.min(pot)

    for i, j in combinations(range(3), 2):
        start_set = set(gammas_local[i])
        end_set = set(gammas_local[j])

        # Find paths of length 2 (direct hop through one intermediate vertex)
        # The shortest paths between 16-cells go through ONE intermediate vertex
        # because 16-cells are distance 1.0 apart
        paths_2 = all_paths_between(start_set, end_set, max_length=2)
        paths_3 = all_paths_between(start_set, end_set, max_length=3)
        paths_4 = all_paths_between(start_set, end_set, max_length=4)

        for max_l, paths in [('len≤2', paths_2), ('len≤3', paths_3), ('len≤4', paths_4)]:
            if not paths:
                results[f'Γ{i}→Γ{j} ({max_l})'] = {
                    'n_paths': 0, 'amplitude': 0
                }
                continue

            # Multiple action definitions
            for action_label, action_fn in [
                ('sum_V', lambda path: sum(pot_norm[k] for k in path[1:-1])),
                ('sum_sqrt_V', lambda path: sum(np.sqrt(max(0, pot_norm[k]))
                                                for k in path[1:-1])),
                ('sum_V_normalized', lambda path: sum(pot_norm[k] / max(1, np.max(pot_norm))
                                                      for k in path[1:-1])),
                ('edge_weighted', lambda path: sum(
                    np.linalg.norm(V[c0[path[k]]] - V[c0[path[k+1]]])
                    for k in range(len(path)-1))),
            ]:
                actions = [action_fn(p) for p in paths]
                # Path integral: Z = Σ e^{-S}
                Z = sum(np.exp(-S) for S in actions)
                # Normalized amplitude
                Z_norm = Z / len(paths)

                key = f'Γ{i}→Γ{j} ({max_l}, {action_label})'
                results[key] = {
                    'n_paths': len(paths),
                    'Z': Z,
                    'Z_norm': Z_norm,
                    'S_min': min(actions),
                    'S_max': max(actions),
                    'S_mean': np.mean(actions),
                }

    return results


# ============================================================
# PART 6: TRIALITY HOLONOMY (BERRY PHASE)
# ============================================================
def triality_holonomy(V, c0, gammas):
    """
    Compute the holonomy of the triality cycle Γ₀ → Γ₁ → Γ₂ → Γ₀.

    For each pair of 16-cells, find the optimal rotation R_ij that maps
    Γ_i to Γ_j within the 600-cell coordinate system. The holonomy is:
        H = R₂₀ · R₁₂ · R₀₁

    Check if eigenvalues of H involve φ.
    """
    # Get vertex sets for each 16-cell
    gamma_verts = [V[g] for g in gammas]

    # Find best rotation R_{ij}: R that minimizes ||R · Γ_i - Γ_j||
    # Using Procrustes / polar decomposition
    def best_rotation(source, target):
        """Find rotation R such that R @ source ≈ target."""
        # Procrustes: M = target^T @ source, R = U @ V^T from SVD(M)
        M = target.T @ source
        U, _, Vt = np.linalg.svd(M)
        # Ensure proper rotation (det = +1)
        d = np.linalg.det(U @ Vt)
        S = np.eye(4)
        S[3, 3] = np.sign(d)
        R = U @ S @ Vt
        return R

    # Sort vertices for consistent matching
    # Match by Hungarian algorithm or nearest-neighbor
    def match_vertices(source, target):
        """Find the permutation of target rows that best matches source."""
        from scipy.optimize import linear_sum_assignment
        n = len(source)
        cost = np.zeros((n, n))
        for i in range(n):
            for j in range(n):
                cost[i, j] = np.linalg.norm(source[i] - target[j])
        row_ind, col_ind = linear_sum_assignment(cost)
        return target[col_ind]

    # Compute rotations around the triality cycle
    results = {}

    # R₀₁: maps Γ₀ → Γ₁
    target_01 = match_vertices(gamma_verts[0], gamma_verts[1])
    R01 = best_rotation(gamma_verts[0], target_01)

    # R₁₂: maps Γ₁ → Γ₂
    target_12 = match_vertices(gamma_verts[1], gamma_verts[2])
    R12 = best_rotation(gamma_verts[1], target_12)

    # R₂₀: maps Γ₂ → Γ₀
    target_20 = match_vertices(gamma_verts[2], gamma_verts[0])
    R20 = best_rotation(gamma_verts[2], target_20)

    # Holonomy = R₂₀ · R₁₂ · R₀₁
    H = R20 @ R12 @ R01

    # Eigenvalues of holonomy
    eigs = np.linalg.eigvals(H)
    eig_magnitudes = np.abs(eigs)
    eig_phases = np.angle(eigs)

    results['holonomy'] = {
        'matrix': H.tolist(),
        'eigenvalues': [(float(np.real(e)), float(np.imag(e))) for e in eigs],
        'eigenvalue_magnitudes': eig_magnitudes.tolist(),
        'eigenvalue_phases_rad': eig_phases.tolist(),
        'eigenvalue_phases_deg': np.degrees(eig_phases).tolist(),
        'det': float(np.real(np.linalg.det(H))),
        'trace': float(np.real(np.trace(H))),
    }

    # Check individual rotations
    for label, R in [('R₀₁', R01), ('R₁₂', R12), ('R₂₀', R20)]:
        eigs_R = np.linalg.eigvals(R)
        results[label] = {
            'det': float(np.real(np.linalg.det(R))),
            'trace': float(np.real(np.trace(R))),
            'eigenvalue_phases_deg': np.degrees(np.angle(eigs_R)).tolist(),
        }

    # Also check R² (double cycle) and R³ (triple)
    H2 = H @ H
    H3 = H @ H @ H
    results['holonomy²'] = {
        'trace': float(np.real(np.trace(H2))),
        'det': float(np.real(np.linalg.det(H2))),
    }
    results['holonomy³'] = {
        'trace': float(np.real(np.trace(H3))),
        'det': float(np.real(np.linalg.det(H3))),
    }

    return results


# ============================================================
# PART 7: SCAN FOR 1/φ AT SPECIAL COUPLING
# ============================================================
def scan_coupling_for_phi(V, c0, gammas, adj_24, all_600_adj):
    """
    Scan the coupling constant α in H = -Δ + α·V to find
    the value of α where the tunneling amplitude = 1/φ.

    If such α exists AND has a clean geometric interpretation,
    this would resolve Factor 2.
    """
    n = len(c0)
    c0_set = set(c0)

    # External neighbor potential
    pot = np.zeros(n)
    for i, idx in enumerate(c0):
        for j in range(len(V)):
            if all_600_adj[idx, j] and j not in c0_set:
                pot[i] += 1
    pot_norm = pot - np.min(pot)

    # Map global to local
    global_to_local = {g: i for i, g in enumerate(c0)}
    gammas_local = [[global_to_local[g] for g in gamma] for gamma in gammas]

    # Build projectors
    gamma_projectors = []
    for gl in gammas_local:
        P = np.zeros((n, n))
        for k in gl:
            P[k, k] = 1.0 / len(gl)
        gamma_projectors.append(P)

    D = np.diag(np.sum(adj_24, axis=1).astype(float))
    A = adj_24.astype(float)
    L0 = D - A

    # Scan α from 0 to 10 in fine steps
    alphas = np.linspace(0, 10, 1000)
    amplitudes_01 = []
    amplitudes_02 = []
    amplitudes_12 = []

    for alpha in alphas:
        H = L0 + alpha * np.diag(pot_norm)
        eigvals, eigvecs = np.linalg.eigh(H)
        T = eigvecs @ np.diag(np.exp(-eigvals)) @ eigvecs.T

        t01 = np.trace(gamma_projectors[0] @ T @ gamma_projectors[1])
        t02 = np.trace(gamma_projectors[0] @ T @ gamma_projectors[2])
        t12 = np.trace(gamma_projectors[1] @ T @ gamma_projectors[2])

        amplitudes_01.append(float(t01))
        amplitudes_02.append(float(t02))
        amplitudes_12.append(float(t12))

    amplitudes_01 = np.array(amplitudes_01)
    amplitudes_02 = np.array(amplitudes_02)
    amplitudes_12 = np.array(amplitudes_12)

    # Find where each amplitude crosses 1/φ
    results = {'target': INV_PHI}
    for label, amps in [('Γ0→Γ1', amplitudes_01),
                         ('Γ0→Γ2', amplitudes_02),
                         ('Γ1→Γ2', amplitudes_12)]:
        # Find zero crossings of (amp - 1/φ)
        crossings = []
        diff = amps - INV_PHI
        for k in range(len(diff) - 1):
            if diff[k] * diff[k+1] < 0:
                # Linear interpolation
                alpha_cross = alphas[k] - diff[k] * (alphas[k+1] - alphas[k]) / (diff[k+1] - diff[k])
                crossings.append(float(alpha_cross))

        results[label] = {
            'amp_at_alpha0': float(amps[0]),
            'amp_at_alpha1': float(amps[np.argmin(np.abs(alphas - 1.0))]),
            'amp_at_alpha_phi': float(amps[np.argmin(np.abs(alphas - PHI))]),
            'amp_at_alpha_invphi': float(amps[np.argmin(np.abs(alphas - INV_PHI))]),
            'amp_at_alpha_lnphi': float(amps[np.argmin(np.abs(alphas - LN_PHI))]),
            'crossings_1_over_phi': crossings,
            'amp_range': [float(np.min(amps)), float(np.max(amps))],
        }

    # Also check: does any amplitude at α = φ-related value equal 1/φ?
    special_alphas = {
        '1/φ': INV_PHI,
        'φ': PHI,
        'ln(φ)': LN_PHI,
        '1/φ²': 1/PHI**2,
        'φ²': PHI**2,
        'π/5': np.pi/5,
        '2π/5': 2*np.pi/5,
    }
    results['special_alpha_check'] = {}
    for label, alpha in special_alphas.items():
        H = L0 + alpha * np.diag(pot_norm)
        eigvals, eigvecs = np.linalg.eigh(H)
        T = eigvecs @ np.diag(np.exp(-eigvals)) @ eigvecs.T

        t01 = np.trace(gamma_projectors[0] @ T @ gamma_projectors[1])
        results['special_alpha_check'][f'α={label}'] = {
            'tunneling_01': float(t01),
            'matches_1_over_phi': abs(t01 - INV_PHI) / INV_PHI < 0.01,
        }

    return results


# ============================================================
# PART 8: COULOMB-LIKE POTENTIAL FROM OTHER 24-CELL COPIES
# ============================================================
def coulomb_potential_analysis(V, copies, c0, gammas, adj_24):
    """
    Define a Coulomb-like potential on C₀ vertices from the OTHER 4 copies
    of the 24-cell. This directly encodes the H₄ structure.

    V_Coulomb(v) = Σ_{k=1}^{4} Σ_{w ∈ C_k} 1/|v - w|²
    """
    n = len(c0)
    global_to_local = {g: i for i, g in enumerate(c0)}
    gammas_local = [[global_to_local[g] for g in gamma] for gamma in gammas]

    # Compute Coulomb potential
    pot_coulomb = np.zeros(n)
    for i, idx in enumerate(c0):
        for k in range(1, len(copies)):  # other 4 copies
            for w in copies[k]:
                d = np.linalg.norm(V[idx] - V[w])
                if d > 0.001:
                    pot_coulomb[i] += 1.0 / d**2

    # Also linear Coulomb: 1/|r|
    pot_linear = np.zeros(n)
    for i, idx in enumerate(c0):
        for k in range(1, len(copies)):
            for w in copies[k]:
                d = np.linalg.norm(V[idx] - V[w])
                if d > 0.001:
                    pot_linear[i] += 1.0 / d

    # Analyze potential structure per 16-cell
    results = {'coulomb_1_over_r2': {}, 'coulomb_1_over_r': {}}
    for pot_label, pot in [('coulomb_1_over_r2', pot_coulomb),
                            ('coulomb_1_over_r', pot_linear)]:
        for gi, gl in enumerate(gammas_local):
            vals = pot[gl]
            results[pot_label][f'Γ{gi}'] = {
                'mean': float(np.mean(vals)),
                'std': float(np.std(vals)),
                'min': float(np.min(vals)),
                'max': float(np.max(vals)),
            }
        # Ratio between sectors
        means = [np.mean(pot[gl]) for gl in gammas_local]
        if len(set(np.round(means, 4))) == 1:
            results[pot_label]['sector_symmetric'] = True
            results[pot_label]['common_value'] = float(means[0])
        else:
            results[pot_label]['sector_symmetric'] = False
            results[pot_label]['sector_means'] = [float(m) for m in means]

    # Transfer matrix with Coulomb potential
    gamma_projectors = []
    for gl in gammas_local:
        P = np.zeros((n, n))
        for k in gl:
            P[k, k] = 1.0 / len(gl)
        gamma_projectors.append(P)

    D = np.diag(np.sum(adj_24, axis=1).astype(float))
    A = adj_24.astype(float)
    L0 = D - A

    for pot_label, pot in [('coulomb_1_over_r2', pot_coulomb),
                            ('coulomb_1_over_r', pot_linear)]:
        pot_shifted = pot - np.min(pot)
        if np.max(pot_shifted) > 0:
            pot_shifted = pot_shifted / np.max(pot_shifted)

        H = L0 + np.diag(pot_shifted)
        eigvals, eigvecs = np.linalg.eigh(H)
        T = eigvecs @ np.diag(np.exp(-eigvals)) @ eigvecs.T

        t01 = np.trace(gamma_projectors[0] @ T @ gamma_projectors[1])
        results[pot_label]['tunneling_01'] = float(t01)
        results[pot_label]['tunneling_01_matches_phi'] = check_phi(abs(t01))

    return results


# ============================================================
# PART 9: DIRECT AMPLITUDE COMPUTATIONS
# ============================================================
def direct_amplitudes(V, c0, gammas, all_600_adj):
    """
    Compute various "direct" amplitudes between 16-cell sectors
    that don't go through the Hamiltonian formalism.
    """
    results = {}

    # --- 1. Overlap of 600-cell neighborhoods ---
    # For each 16-cell pair, count shared 600-cell neighbors outside C₀
    c0_set = set(c0)
    for i, j in combinations(range(3), 2):
        neighbors_i = set()
        for vi in gammas[i]:
            for k in range(len(V)):
                if all_600_adj[vi, k] and k not in c0_set:
                    neighbors_i.add(k)
        neighbors_j = set()
        for vj in gammas[j]:
            for k in range(len(V)):
                if all_600_adj[vj, k] and k not in c0_set:
                    neighbors_j.add(k)

        shared = neighbors_i & neighbors_j
        total = neighbors_i | neighbors_j

        ratio = len(shared) / len(total) if total else 0
        jaccard = ratio
        results[f'Γ{i}↔Γ{j}_shared_ext_neighbors'] = {
            'shared': len(shared),
            'total_i': len(neighbors_i),
            'total_j': len(neighbors_j),
            'union': len(total),
            'jaccard': jaccard,
        }

    # --- 2. 600-cell mediated coupling ---
    # Amplitude through a SINGLE 600-cell vertex outside C₀
    # A(Γ_i → v_ext → Γ_j) = (1/d_i) × (1/d_j) summed over all v_ext
    for i, j in combinations(range(3), 2):
        amplitude = 0.0
        for k in range(len(V)):
            if k in c0_set:
                continue
            # Check if k is connected to both Γ_i and Γ_j via 600-cell edges
            connects_i = any(all_600_adj[vi, k] for vi in gammas[i])
            connects_j = any(all_600_adj[vj, k] for vj in gammas[j])
            if connects_i and connects_j:
                amplitude += 1.0  # Each mediating vertex contributes equally

        results[f'Γ{i}↔Γ{j}_mediated_count'] = int(amplitude)

    # --- 3. Gram matrix of 16-cell subspaces ---
    # Treat each 16-cell as a subspace of R⁴ and compute principal angles
    for i, j in combinations(range(3), 2):
        vi = V[gammas[i]]  # 8×4
        vj = V[gammas[j]]  # 8×4

        # Compute cross-Gram matrix
        G = vi @ vj.T  # 8×8
        svs = np.linalg.svd(G, compute_uv=False)
        # Normalize by ||vi|| × ||vj|| (all unit vectors, so already normalized)
        # Principal angles between subspaces
        cos_angles = np.clip(svs / (np.linalg.norm(vi[0]) * np.linalg.norm(vj[0])), -1, 1)

        results[f'Γ{i}↔Γ{j}_principal_angles'] = {
            'cos_angles': cos_angles.tolist(),
            'angles_deg': np.degrees(np.arccos(np.clip(cos_angles, -1, 1))).tolist(),
            'product_cos': float(np.prod(cos_angles[cos_angles > 0.001])),
        }

    # --- 4. Transition probability from quantum state overlap ---
    # If |Γ_i⟩ = (1/√8) Σ_{v∈Γ_i} |v⟩, the transition amplitude is
    # ⟨Γ_i|Γ_j⟩ = (1/8) Σ Σ ⟨v_i|v_j⟩
    for i, j in combinations(range(3), 2):
        vi = V[gammas[i]]
        vj = V[gammas[j]]
        overlap = np.sum(vi @ vj.T) / (len(gammas[i]))
        results[f'Γ{i}↔Γ{j}_state_overlap'] = float(overlap)

    return results


# ============================================================
# MAIN
# ============================================================
def main():
    print("=" * 78)
    print("PATH B: TUNNELING AMPLITUDE BETWEEN 16-CELL SECTORS")
    print("Searching for dynamical origin of Factor 2 = 1/φ")
    print("=" * 78)

    all_phi_hits = []  # Collect all φ matches
    master_results = {
        'title': 'Path B: Tunneling Amplitude Between 16-Cell Sectors',
        'timestamp': datetime.now().isoformat(),
        'success_criterion': '1/φ ≈ 0.6180',
        'sections': {}
    }

    # ==========================================================
    # SETUP: Build structures
    # ==========================================================
    print("\n" + "=" * 78)
    print("SETUP: Building 600-cell and identifying structures")
    print("=" * 78)

    V = build_600_cell()
    print(f"  600-cell vertices: {len(V)}")

    c0 = find_c0(V)
    copies = find_24_cells(V, c0)
    gammas = find_16_cells(V, c0)
    print(f"  24-cell copies: {len(copies)}")
    print(f"  16-cells in C₀: {len(gammas)}, sizes: {[len(g) for g in gammas]}")

    # Build 600-cell adjacency
    n = len(V)
    all_600_adj = np.zeros((n, n), dtype=int)
    for i in range(n):
        for j in range(i + 1, n):
            if abs(np.linalg.norm(V[i] - V[j]) - INV_PHI) < 0.01:
                all_600_adj[i, j] = all_600_adj[j, i] = 1

    # Build 24-cell adjacency
    adj_24 = build_24cell_adjacency(V, c0)
    degree_24 = np.sum(adj_24[0])
    print(f"  24-cell vertex degree: {int(degree_24)}  (expected 8)")

    # Map for local indices
    global_to_local = {g: i for i, g in enumerate(c0)}
    gammas_local = [[global_to_local[g] for g in gamma] for gamma in gammas]

    # Verify 16-cell partition
    print(f"  16-cell partitions: {[sorted(gl) for gl in gammas_local]}")

    # ==========================================================
    # §1. POTENTIALS FROM 600-CELL EMBEDDING
    # ==========================================================
    print("\n" + "=" * 78)
    print("§1. POTENTIALS ON 24-CELL FROM 600-CELL EMBEDDING")
    print("=" * 78)

    potentials = compute_potentials(V, c0, all_600_adj)

    for name, pot in potentials.items():
        print(f"\n  Potential {name}:")
        unique_vals = sorted(set(np.round(pot, 4)))
        print(f"    Unique values: {unique_vals}")
        print(f"    Range: [{np.min(pot):.4f}, {np.max(pot):.4f}]")

        # Check per-16-cell structure
        for gi, gl in enumerate(gammas_local):
            vals = pot[gl]
            print(f"    Γ{gi}: mean={np.mean(vals):.4f}, "
                  f"std={np.std(vals):.4f}, "
                  f"vals={sorted(np.round(vals, 2))}")

        # Check if potential breaks 16-cell symmetry
        means = [np.mean(pot[gl]) for gl in gammas_local]
        if len(set(np.round(means, 3))) == 1:
            print(f"    → SYMMETRIC across 16-cells (mean = {means[0]:.4f})")
        else:
            print(f"    → ASYMMETRIC: means = {[f'{m:.4f}' for m in means]}")

    master_results['sections']['potentials'] = {
        name: {
            'values': pot.tolist(),
            'unique': sorted(set(np.round(pot, 4).tolist())),
            'per_sector': {
                f'Γ{gi}': {
                    'mean': float(np.mean(pot[gl])),
                    'std': float(np.std(pot[gl]))
                } for gi, gl in enumerate(gammas_local)
            }
        } for name, pot in potentials.items()
    }

    # ==========================================================
    # §2. WKB TUNNELING AMPLITUDES
    # ==========================================================
    print("\n" + "=" * 78)
    print("§2. WKB TUNNELING AMPLITUDES")
    print("=" * 78)

    for pot_name, pot in potentials.items():
        print(f"\n  Using potential: {pot_name}")
        wkb_results = wkb_tunneling(pot, adj_24, gammas_local, V[c0])

        for pair, data in wkb_results.items():
            print(f"    {pair}:")
            print(f"      Shortest path length: {data['path_length']}")
            print(f"      Number of paths: {data['n_paths']}")
            print(f"      S_min = {data['S_min']:.6f}")
            amp = data['amplitude_min']
            m = check_phi(amp) if amp > 0 else []
            print(f"      Amplitude (min action) = {amp:.6f}{fmt_matches(m)}")
            if m:
                all_phi_hits.append((f'WKB({pot_name},{pair})', amp, m))

            pi_amp = data['path_integral']
            m2 = check_phi(pi_amp) if pi_amp > 0 else []
            print(f"      Path integral sum = {pi_amp:.6f}{fmt_matches(m2)}")
            if m2:
                all_phi_hits.append((f'PathInt({pot_name},{pair})', pi_amp, m2))

    # ==========================================================
    # §3. TRANSFER MATRIX / PROPAGATOR
    # ==========================================================
    print("\n" + "=" * 78)
    print("§3. TRANSFER MATRIX T = e^{-H} BETWEEN SECTORS")
    print("=" * 78)

    tm_results = transfer_matrix_analysis(V, c0, gammas, adj_24, all_600_adj)
    master_results['sections']['transfer_matrix'] = {}

    for alpha_label, data in tm_results.items():
        print(f"\n  α = {alpha_label} (coupling = {data['alpha']:.4f}):")
        print(f"    Spectral gap: {data['spectral_gap']:.6f}")
        print(f"    First 5 eigenvalues: {[f'{e:.4f}' for e in data['eigvals_first5']]}")

        for pair, key in [('Γ0↔Γ1', 'tunneling_01'),
                           ('Γ0↔Γ2', 'tunneling_02'),
                           ('Γ1↔Γ2', 'tunneling_12')]:
            amp = data[key]
            m = check_phi(abs(amp))
            print(f"    T({pair}) = {amp:.6f}{fmt_matches(m)}")
            if m:
                all_phi_hits.append((f'Transfer(α={alpha_label},{pair})', abs(amp), m))

        for pair, key in [('Γ0↔Γ1', 'green_01'),
                           ('Γ0↔Γ2', 'green_02'),
                           ('Γ1↔Γ2', 'green_12')]:
            gval = data[key]
            m = check_phi(abs(gval))
            if m:
                print(f"    G({pair}) = {gval:.6f}{fmt_matches(m)}")
                all_phi_hits.append((f'Green(α={alpha_label},{pair})', abs(gval), m))

        master_results['sections']['transfer_matrix'][alpha_label] = data

    # ==========================================================
    # §4. GRAPH LAPLACIAN SPECTRAL ANALYSIS
    # ==========================================================
    print("\n" + "=" * 78)
    print("§4. GRAPH LAPLACIAN SPECTRAL ANALYSIS")
    print("=" * 78)

    spec_results = laplacian_spectral_analysis(V, c0, gammas, adj_24, all_600_adj)

    for label, data in spec_results.items():
        print(f"\n  {label}:")
        if 'multiplicities' in data:
            print(f"    Eigenvalues with multiplicities:")
            for e, mult in data['multiplicities']:
                m = check_phi(abs(e))
                print(f"      λ = {e:8.4f}  (×{mult}){fmt_matches(m)}")
                if m:
                    all_phi_hits.append((f'Laplacian({label},λ={e:.4f})', abs(e), m))
        if 'spectral_ratios' in data:
            print(f"    Spectral ratios:")
            for rname, rval in data['spectral_ratios'].items():
                m = check_phi(abs(rval))
                print(f"      {rname} = {rval:.6f}{fmt_matches(m)}")
                if m:
                    all_phi_hits.append((f'SpecRatio({label},{rname})', abs(rval), m))
        if 'eigenvalues_first8' in data:
            eigs = data['eigenvalues_first8']
            print(f"    First 8 eigenvalues: {[f'{e:.4f}' for e in eigs]}")

    master_results['sections']['spectral'] = {
        k: {kk: vv for kk, vv in v.items() if kk != 'multiplicities'}
        for k, v in spec_results.items()
    }

    # ==========================================================
    # §5. ACTION-WEIGHTED PATH SUMS
    # ==========================================================
    print("\n" + "=" * 78)
    print("§5. ACTION-WEIGHTED PATH SUMS (PATH INTEGRAL)")
    print("=" * 78)

    path_results = action_path_sums(V, c0, gammas, adj_24, all_600_adj)

    for label, data in path_results.items():
        if data['n_paths'] == 0:
            continue
        print(f"\n  {label}:")
        print(f"    Paths: {data['n_paths']}")
        Z = data['Z']
        Z_norm = data['Z_norm']
        m1 = check_phi(Z)
        m2 = check_phi(Z_norm)
        print(f"    Z (path sum) = {Z:.6f}{fmt_matches(m1)}")
        print(f"    Z/N_paths = {Z_norm:.6f}{fmt_matches(m2)}")
        print(f"    S range: [{data['S_min']:.4f}, {data['S_max']:.4f}]")
        if m1:
            all_phi_hits.append((f'PathSum({label})', Z, m1))
        if m2:
            all_phi_hits.append((f'PathSumNorm({label})', Z_norm, m2))

    master_results['sections']['path_sums'] = {
        k: {kk: float(vv) if isinstance(vv, (np.floating, float)) else vv
            for kk, vv in v.items()}
        for k, v in path_results.items()
    }

    # ==========================================================
    # §6. TRIALITY HOLONOMY (BERRY PHASE)
    # ==========================================================
    print("\n" + "=" * 78)
    print("§6. TRIALITY HOLONOMY (BERRY PHASE)")
    print("=" * 78)

    try:
        hol_results = triality_holonomy(V, c0, gammas)

        h = hol_results['holonomy']
        print(f"\n  Holonomy matrix H = R₂₀ · R₁₂ · R₀₁:")
        print(f"    det(H) = {h['det']:.6f}")
        print(f"    tr(H) = {h['trace']:.6f}")
        m = check_phi(abs(h['trace']))
        if m:
            print(f"      {fmt_matches(m)}")
            all_phi_hits.append(('holonomy_trace', abs(h['trace']), m))

        print(f"    Eigenvalue magnitudes: {[f'{x:.4f}' for x in h['eigenvalue_magnitudes']]}")
        print(f"    Eigenvalue phases (deg): {[f'{x:.2f}' for x in h['eigenvalue_phases_deg']]}")

        for phase in h['eigenvalue_phases_deg']:
            m = check_phi(abs(phase) / 180 * np.pi)  # Check radian value
            if m:
                print(f"      Phase {phase:.2f}° = {abs(phase)/180*np.pi:.6f} rad{fmt_matches(m)}")
                all_phi_hits.append((f'holonomy_phase_{phase:.1f}', abs(phase)/180*np.pi, m))

        for mag in h['eigenvalue_magnitudes']:
            m = check_phi(mag)
            if m:
                print(f"      |λ| = {mag:.6f}{fmt_matches(m)}")
                all_phi_hits.append((f'holonomy_eigmag_{mag:.4f}', mag, m))

        # Individual rotations
        for label in ['R₀₁', 'R₁₂', 'R₂₀']:
            r = hol_results[label]
            print(f"\n  {label}: det={r['det']:.4f}, tr={r['trace']:.4f}")
            m = check_phi(abs(r['trace']))
            if m:
                all_phi_hits.append((f'{label}_trace', abs(r['trace']), m))
                print(f"    {fmt_matches(m)}")

        print(f"\n  H²: tr={hol_results['holonomy²']['trace']:.4f}")
        print(f"  H³: tr={hol_results['holonomy³']['trace']:.4f}")

        master_results['sections']['holonomy'] = hol_results

    except ImportError:
        print("\n  SKIPPED: scipy.optimize.linear_sum_assignment not available")
        master_results['sections']['holonomy'] = {'status': 'skipped'}

    # ==========================================================
    # §7. COUPLING SCAN FOR 1/φ
    # ==========================================================
    print("\n" + "=" * 78)
    print("§7. COUPLING SCAN: Find α where tunneling = 1/φ")
    print("=" * 78)

    scan_results = scan_coupling_for_phi(V, c0, gammas, adj_24, all_600_adj)

    for pair in ['Γ0→Γ1', 'Γ0→Γ2', 'Γ1→Γ2']:
        data = scan_results[pair]
        print(f"\n  {pair}:")
        print(f"    Amplitude at α=0: {data['amp_at_alpha0']:.6f}")
        print(f"    Amplitude at α=1: {data['amp_at_alpha1']:.6f}")
        print(f"    Amplitude at α=φ: {data['amp_at_alpha_phi']:.6f}")
        print(f"    Amplitude at α=1/φ: {data['amp_at_alpha_invphi']:.6f}")
        print(f"    Amplitude at α=ln(φ): {data['amp_at_alpha_lnphi']:.6f}")
        print(f"    Range: [{data['amp_range'][0]:.6f}, {data['amp_range'][1]:.6f}]")
        if data['crossings_1_over_phi']:
            print(f"    *** CROSSES 1/φ at α = {data['crossings_1_over_phi']} ***")
            for alpha_cross in data['crossings_1_over_phi']:
                m = check_phi(alpha_cross)
                if m:
                    print(f"      α = {alpha_cross:.6f}{fmt_matches(m)}")
                    all_phi_hits.append((f'crossing_alpha({pair})', alpha_cross, m))
        else:
            print(f"    Does NOT cross 1/φ = {INV_PHI:.6f}")

    # Special alpha check
    print(f"\n  Special α values:")
    for label, data in scan_results['special_alpha_check'].items():
        amp = data['tunneling_01']
        match = data['matches_1_over_phi']
        m = check_phi(abs(amp))
        status = "✓ MATCH" if match else ""
        print(f"    {label}: T(Γ0↔Γ1) = {amp:.6f}  {status}{fmt_matches(m)}")
        if m:
            all_phi_hits.append((f'special_{label}', abs(amp), m))

    master_results['sections']['coupling_scan'] = {
        k: v for k, v in scan_results.items() if k != 'special_alpha_check'
    }
    master_results['sections']['coupling_scan']['special_alpha'] = scan_results['special_alpha_check']

    # ==========================================================
    # §8. COULOMB POTENTIAL FROM OTHER 24-CELL COPIES
    # ==========================================================
    print("\n" + "=" * 78)
    print("§8. COULOMB POTENTIAL FROM OTHER 24-CELL COPIES")
    print("=" * 78)

    if len(copies) == 5:
        coulomb_results = coulomb_potential_analysis(V, copies, c0, gammas, adj_24)

        for pot_label in ['coulomb_1_over_r2', 'coulomb_1_over_r']:
            print(f"\n  {pot_label}:")
            data = coulomb_results[pot_label]
            if 'sector_symmetric' in data:
                if data['sector_symmetric']:
                    print(f"    Symmetric across sectors (value = {data['common_value']:.4f})")
                else:
                    print(f"    Asymmetric: {data['sector_means']}")

            if 'tunneling_01' in data:
                amp = data['tunneling_01']
                m = check_phi(abs(amp))
                print(f"    Tunneling Γ0↔Γ1 = {amp:.6f}{fmt_matches(m)}")
                if m:
                    all_phi_hits.append((f'{pot_label}_tunneling', abs(amp), m))

        master_results['sections']['coulomb'] = {
            k: {kk: vv for kk, vv in v.items()
                if not isinstance(vv, list) or len(vv) < 10}
            for k, v in coulomb_results.items()
        }
    else:
        print("  SKIPPED: Could not find all 5 copies of 24-cell")

    # ==========================================================
    # §9. DIRECT AMPLITUDE COMPUTATIONS
    # ==========================================================
    print("\n" + "=" * 78)
    print("§9. DIRECT AMPLITUDE COMPUTATIONS")
    print("=" * 78)

    direct_results = direct_amplitudes(V, c0, gammas, all_600_adj)

    for label, data in direct_results.items():
        if isinstance(data, dict):
            print(f"\n  {label}:")
            for k, v in data.items():
                if isinstance(v, float):
                    m = check_phi(abs(v))
                    print(f"    {k} = {v:.6f}{fmt_matches(m)}")
                    if m:
                        all_phi_hits.append((f'direct({label},{k})', abs(v), m))
                elif isinstance(v, (int, np.integer)):
                    print(f"    {k} = {v}")
                elif isinstance(v, list) and len(v) < 10:
                    print(f"    {k} = {[f'{x:.4f}' if isinstance(x, float) else x for x in v]}")
        else:
            m = check_phi(abs(data))
            print(f"  {label} = {data:.6f}{fmt_matches(m)}")
            if m:
                all_phi_hits.append((f'direct({label})', abs(data), m))

    master_results['sections']['direct'] = {
        k: v if not isinstance(v, np.ndarray) else v.tolist()
        for k, v in direct_results.items()
    }

    # ==========================================================
    # SUMMARY
    # ==========================================================
    print("\n" + "=" * 78)
    print("SUMMARY: ALL φ-RELATED MATCHES")
    print("=" * 78)

    if all_phi_hits:
        # Deduplicate and organize
        seen = set()
        hits_1_over_phi = []
        hits_other = []
        for name, val, matches in all_phi_hits:
            for mn, mt, me in matches:
                key = (name, mn)
                if key not in seen:
                    seen.add(key)
                    entry = f"  {name:50s} = {val:.6f} ≈ {mn} (err {me:.3f}%)"
                    if mn == '1/φ' or mn == '(√5-1)/2' or mn == 'e^(-ln φ)':
                        hits_1_over_phi.append(entry)
                    else:
                        hits_other.append(entry)

        if hits_1_over_phi:
            print(f"\n  *** MATCHES FOR 1/φ (Factor 2 candidates): ***")
            for h in hits_1_over_phi:
                print(h)

        if hits_other:
            print(f"\n  Other φ-related matches:")
            for h in hits_other:
                print(h)

        print(f"\n  Total matches: {len(seen)}")
        print(f"  Factor 2 (1/φ) candidates: {len(hits_1_over_phi)}")
    else:
        print("\n  NO φ-related matches found in any dynamical quantity.")
        print("  This is a NEGATIVE result for Path B.")

    # Final verdict
    print("\n" + "=" * 78)
    print("VERDICT")
    print("=" * 78)

    has_factor2 = any(
        mn == '1/φ' or mn == '(√5-1)/2' or mn == 'e^(-ln φ)'
        for _, _, matches in all_phi_hits
        for mn, _, _ in matches
    )

    if has_factor2:
        print("\n  ✓ POSITIVE: Found dynamical quantity matching 1/φ!")
        print("  → Factor 2 may have a TUNNELING/DYNAMICAL origin")
        print("  → Check whether the matching quantity has clear physical interpretation")
        master_results['verdict'] = 'POSITIVE'
    else:
        print("\n  ✗ NEGATIVE: No dynamical quantity matches 1/φ")
        print("  → Path B does NOT resolve Factor 2")
        print("  → Proceed to Paths C, D, E, F per research plan")
        master_results['verdict'] = 'NEGATIVE'

    master_results['phi_hits'] = [
        {'name': name, 'value': float(val),
         'matches': [(mn, float(mt), float(me)) for mn, mt, me in matches]}
        for name, val, matches in all_phi_hits
    ]
    master_results['factor2_found'] = has_factor2

    # Save results
    out_dir = os.path.dirname(os.path.abspath(__file__))
    out_path = os.path.join(out_dir, 'path_b_tunneling_amplitude_results.json')
    with open(out_path, 'w') as f:
        json.dump(master_results, f, indent=2, default=str)
    print(f"\n  Results saved to: {out_path}")


if __name__ == "__main__":
    main()
