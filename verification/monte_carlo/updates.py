"""
Monte Carlo Update Algorithms
================================

Provides Metropolis and Cabibbo-Marinari heat bath sweeps for
SU(3) lattice gauge theory on FCC, D4, and Z^4 lattices.

Triangular-plaquette functions (FCC/D4, 3 edges per face):
    compute_staple      - Sum of triangle staple contributions
    metropolis_sweep    - One Metropolis sweep over all edges
    heatbath_sweep      - One Cabibbo-Marinari heat bath sweep

Square-plaquette functions (Z^4, 4 edges per face):
    compute_staple_square   - Sum of square staple contributions
    metropolis_sweep_square - One Metropolis sweep (square faces)
    heatbath_sweep_square   - One heat bath sweep (square faces)
"""

import numpy as np
from numba import njit
from . import su3_ops


@njit(cache=True)
def compute_staple(e_idx, links, face_edges, face_dirs,
                   edge_faces, edge_n_faces):
    """Compute the staple sum for edge e_idx.

    The staple is: V_e = sum_{f containing e} product of other two links in f.

    For a face f = (e0, e1, e2) with dirs (d0, d1, d2),
    traversal is: link(e0,d0) @ link(e1,d1) @ link(e2,d2) = Wilson loop.

    If the edge we're updating is e_k in face f, then the staple
    contribution from f is: product of the other two edges (in order).

    For edge e_k with direction d_k, the plaquette is:
        W = link(e0,d0) @ link(e1,d1) @ link(e2,d2)
    The staple for e_k is what multiplies U_{e_k} to form W:
        If k=0: staple_f = link(e1,d1) @ link(e2,d2)   (right staple, since W = U_e0 @ staple)
        If k=1: staple_f = link(e2,d2) @ link(e0,d0)
        If k=2: staple_f = link(e0,d0) @ link(e1,d1)
    But we need to account for the direction of e_k itself:
        If d_k = +1: W = U_e @ staple, so contribution = staple
        If d_k = -1: W = ... @ U_e^dag @ ..., rearrange accordingly

    Actually, let's think carefully. The Wilson loop around face f is:
        W_f = link(e0,d0) @ link(e1,d1) @ link(e2,d2)
    where link(e, +1) = links[e] and link(e, -1) = links[e]^dag.

    The action contribution from face f is: (beta/Nc) * Re Tr(W_f).
    When updating edge e_idx, the part that depends on links[e_idx] is:
        For face f containing e_idx at position k with direction d_k:
        If d_k = +1: the term is Re Tr(links[e_idx] @ S_f) where
            S_f = product of remaining links in order
        If d_k = -1: the term is Re Tr(links[e_idx]^dag @ S_f') where
            S_f' = rearranged product

    To unify, we compute V = sum_f S_f such that the e_idx contribution
    to the action is (beta/Nc) * Re Tr(links[e_idx] @ V) for d_k = +1.

    For d_k = +1 (e at position k):
        k=0: S_f = link(e1,d1) @ link(e2,d2)
        k=1: S_f = link(e2,d2) @ link(e0,d0)
        k=2: S_f = link(e0,d0) @ link(e1,d1)
    For d_k = -1, the contribution is Re Tr(U^dag @ ...) = Re Tr(... @ U)^*
        = Re Tr(U @ S_f^dag), so we add S_f^dag instead.

    Returns: V, a 3x3 complex matrix (the staple sum).
    """
    V = np.zeros((3, 3), dtype=np.complex128)

    n_f = edge_n_faces[e_idx]
    for fi in range(n_f):
        f_idx = edge_faces[e_idx, fi]
        if f_idx < 0:
            continue

        # Find which position (0,1,2) our edge is in this face
        e0 = face_edges[f_idx, 0]
        e1 = face_edges[f_idx, 1]
        e2 = face_edges[f_idx, 2]
        d0 = face_dirs[f_idx, 0]
        d1 = face_dirs[f_idx, 1]
        d2 = face_dirs[f_idx, 2]

        # Get oriented link matrices for each edge
        if d0 == 1:
            L0 = links[e0].copy()
        else:
            L0 = su3_ops.mat3x3_dag(links[e0])
        if d1 == 1:
            L1 = links[e1].copy()
        else:
            L1 = su3_ops.mat3x3_dag(links[e1])
        if d2 == 1:
            L2 = links[e2].copy()
        else:
            L2 = su3_ops.mat3x3_dag(links[e2])

        # Compute staple contribution based on position of e_idx
        if e_idx == e0:
            # W = U_{e0} @ L1 @ L2, so staple = L1 @ L2
            S = su3_ops.mat3x3_mul(L1, L2)
            if d0 == -1:
                S = su3_ops.mat3x3_dag(S)
        elif e_idx == e1:
            # W = L0 @ U_{e1} @ L2, so the U_{e1} contribution:
            # Re Tr(L0 @ U @ L2) = Re Tr(U @ L2 @ L0)
            S = su3_ops.mat3x3_mul(L2, L0)
            if d1 == -1:
                S = su3_ops.mat3x3_dag(S)
        else:  # e_idx == e2
            # W = L0 @ L1 @ U_{e2}
            # Re Tr(L0 @ L1 @ U) = Re Tr(U @ L0 @ L1)
            S = su3_ops.mat3x3_mul(L0, L1)
            if d2 == -1:
                S = su3_ops.mat3x3_dag(S)

        for i in range(3):
            for j in range(3):
                V[i, j] += S[i, j]

    return V


@njit(cache=True)
def metropolis_sweep(links, beta, epsilon, face_edges, face_dirs,
                     edge_faces, edge_n_faces, n_edges):
    """Perform one Metropolis sweep over all edges.

    For each edge:
        1. Compute staple V
        2. Propose U' = X @ U where X ~ SU(3) near identity
        3. Accept/reject based on change in action

    Returns: number of accepted proposals.
    """
    accepted = 0
    beta_over_nc = beta / 3.0

    for e_idx in range(n_edges):
        U_old = links[e_idx].copy()
        V = compute_staple(e_idx, links, face_edges, face_dirs,
                          edge_faces, edge_n_faces)

        # Old action contribution: (beta/Nc) * Re Tr(U_old @ V)
        UV_old = su3_ops.mat3x3_mul(U_old, V)
        S_old = beta_over_nc * su3_ops.mat3x3_trace(UV_old).real

        # Propose new link
        X = su3_ops.random_su3_near_id(epsilon)
        U_new = su3_ops.mat3x3_mul(X, U_old)

        UV_new = su3_ops.mat3x3_mul(U_new, V)
        S_new = beta_over_nc * su3_ops.mat3x3_trace(UV_new).real

        # Accept/reject (action in exponent is -S, so we want larger S)
        dS = S_new - S_old
        if dS > 0 or np.random.random() < np.exp(dS):
            links[e_idx] = U_new
            accepted += 1
        # else: keep U_old (already in links[e_idx])

    return accepted


@njit(cache=True)
def heatbath_sweep(links, beta, face_edges, face_dirs,
                   edge_faces, edge_n_faces, n_edges):
    """Perform one Cabibbo-Marinari heat bath sweep.

    For each edge:
        1. Compute staple V
        2. Form W = U @ V (unscaled)
        3. Sequentially update 3 SU(2) subgroups via Kennedy-Pendleton
        4. Each SU(2) update: R_s @ U_cur, then recompute W

    Returns: 0 (all updates accepted in heat bath).
    """
    beta_over_nc = beta / 3.0

    for e_idx in range(n_edges):
        V = compute_staple(e_idx, links, face_edges, face_dirs,
                          edge_faces, edge_n_faces)

        U_cur = links[e_idx].copy()

        # Three sequential SU(2) subgroup updates
        for sub in range(3):
            W = su3_ops.mat3x3_mul(U_cur, V)
            R = su3_ops.cabibbo_marinari_su2_update(W, beta_over_nc, sub)
            U_cur = su3_ops.mat3x3_mul(R, U_cur)

        links[e_idx] = U_cur

    return 0


@njit(cache=True)
def reunitarize(links, n_edges):
    """Reproject all links onto SU(3) to combat floating-point drift."""
    for e_idx in range(n_edges):
        links[e_idx] = su3_ops.project_su3_gs(links[e_idx])


def tune_epsilon(links, beta, face_edges, face_dirs, edge_faces,
                 edge_n_faces, n_edges, target_rate=0.5, n_tune=10):
    """Tune the Metropolis step size epsilon for target acceptance rate.

    Performs a few short sweeps and adjusts epsilon.
    """
    epsilon = min(0.5, 2.0 / max(beta, 0.1))
    for _ in range(n_tune):
        acc = metropolis_sweep(links, beta, epsilon, face_edges, face_dirs,
                              edge_faces, edge_n_faces, n_edges)
        rate = acc / n_edges
        if rate > target_rate + 0.05:
            epsilon *= 1.2
        elif rate < target_rate - 0.05:
            epsilon *= 0.8
        else:
            break
    return epsilon


# =============================================================================
# Square-plaquette functions (Z^4 hypercubic lattice)
# =============================================================================

@njit(cache=True)
def compute_staple_square(e_idx, links, face_edges, face_dirs,
                          edge_faces, edge_n_faces):
    """Compute the staple sum for edge e_idx on a square-plaquette lattice.

    Same logic as compute_staple but handles 4-edge faces.
    For a face f = (e0, e1, e2, e3) with dirs (d0, d1, d2, d3),
    the Wilson loop is: L0 @ L1 @ L2 @ L3.

    The staple for edge at position k is the product of the other
    three edges in cyclic order starting after k.

    Returns: V, a 3x3 complex matrix (the staple sum).
    """
    V = np.zeros((3, 3), dtype=np.complex128)

    n_f = edge_n_faces[e_idx]
    for fi in range(n_f):
        f_idx = edge_faces[e_idx, fi]
        if f_idx < 0:
            continue

        # Get the 4 edges and directions of this face
        e0 = face_edges[f_idx, 0]
        e1 = face_edges[f_idx, 1]
        e2 = face_edges[f_idx, 2]
        e3 = face_edges[f_idx, 3]
        d0 = face_dirs[f_idx, 0]
        d1 = face_dirs[f_idx, 1]
        d2 = face_dirs[f_idx, 2]
        d3 = face_dirs[f_idx, 3]

        # Get oriented link matrices
        if d0 == 1:
            L0 = links[e0].copy()
        else:
            L0 = su3_ops.mat3x3_dag(links[e0])
        if d1 == 1:
            L1 = links[e1].copy()
        else:
            L1 = su3_ops.mat3x3_dag(links[e1])
        if d2 == 1:
            L2 = links[e2].copy()
        else:
            L2 = su3_ops.mat3x3_dag(links[e2])
        if d3 == 1:
            L3 = links[e3].copy()
        else:
            L3 = su3_ops.mat3x3_dag(links[e3])

        # Wilson loop: W = L0 @ L1 @ L2 @ L3
        # Staple for edge at position k: product of other 3 in cyclic order
        # so that W = L_k @ S_k (when d_k = +1).
        if e_idx == e0:
            # W = L0 @ L1 @ L2 @ L3, staple = L1 @ L2 @ L3
            S = su3_ops.mat3x3_mul(su3_ops.mat3x3_mul(L1, L2), L3)
            if d0 == -1:
                S = su3_ops.mat3x3_dag(S)
        elif e_idx == e1:
            # Re Tr(L0 @ U @ L2 @ L3) = Re Tr(U @ L2 @ L3 @ L0)
            S = su3_ops.mat3x3_mul(su3_ops.mat3x3_mul(L2, L3), L0)
            if d1 == -1:
                S = su3_ops.mat3x3_dag(S)
        elif e_idx == e2:
            # Re Tr(L0 @ L1 @ U @ L3) = Re Tr(U @ L3 @ L0 @ L1)
            S = su3_ops.mat3x3_mul(su3_ops.mat3x3_mul(L3, L0), L1)
            if d2 == -1:
                S = su3_ops.mat3x3_dag(S)
        else:  # e_idx == e3
            # Re Tr(L0 @ L1 @ L2 @ U) = Re Tr(U @ L0 @ L1 @ L2)
            S = su3_ops.mat3x3_mul(su3_ops.mat3x3_mul(L0, L1), L2)
            if d3 == -1:
                S = su3_ops.mat3x3_dag(S)

        for i in range(3):
            for j in range(3):
                V[i, j] += S[i, j]

    return V


@njit(cache=True)
def metropolis_sweep_square(links, beta, epsilon, face_edges, face_dirs,
                            edge_faces, edge_n_faces, n_edges):
    """Perform one Metropolis sweep over all edges (square plaquettes).

    Returns: number of accepted proposals.
    """
    accepted = 0
    beta_over_nc = beta / 3.0

    for e_idx in range(n_edges):
        U_old = links[e_idx].copy()
        V = compute_staple_square(e_idx, links, face_edges, face_dirs,
                                  edge_faces, edge_n_faces)

        UV_old = su3_ops.mat3x3_mul(U_old, V)
        S_old = beta_over_nc * su3_ops.mat3x3_trace(UV_old).real

        X = su3_ops.random_su3_near_id(epsilon)
        U_new = su3_ops.mat3x3_mul(X, U_old)

        UV_new = su3_ops.mat3x3_mul(U_new, V)
        S_new = beta_over_nc * su3_ops.mat3x3_trace(UV_new).real

        dS = S_new - S_old
        if dS > 0 or np.random.random() < np.exp(dS):
            links[e_idx] = U_new
            accepted += 1

    return accepted


@njit(cache=True)
def heatbath_sweep_square(links, beta, face_edges, face_dirs,
                          edge_faces, edge_n_faces, n_edges):
    """Perform one Cabibbo-Marinari heat bath sweep (square plaquettes).

    Returns: 0 (all updates accepted in heat bath).
    """
    beta_over_nc = beta / 3.0

    for e_idx in range(n_edges):
        V = compute_staple_square(e_idx, links, face_edges, face_dirs,
                                  edge_faces, edge_n_faces)

        U_cur = links[e_idx].copy()

        for sub in range(3):
            W = su3_ops.mat3x3_mul(U_cur, V)
            R = su3_ops.cabibbo_marinari_su2_update(W, beta_over_nc, sub)
            U_cur = su3_ops.mat3x3_mul(R, U_cur)

        links[e_idx] = U_cur

    return 0


def tune_epsilon_square(links, beta, face_edges, face_dirs, edge_faces,
                        edge_n_faces, n_edges, target_rate=0.5, n_tune=10):
    """Tune Metropolis step size for square-plaquette lattice."""
    epsilon = min(0.5, 2.0 / max(beta, 0.1))
    for _ in range(n_tune):
        acc = metropolis_sweep_square(links, beta, epsilon, face_edges,
                                     face_dirs, edge_faces, edge_n_faces,
                                     n_edges)
        rate = acc / n_edges
        if rate > target_rate + 0.05:
            epsilon *= 1.2
        elif rate < target_rate - 0.05:
            epsilon *= 0.8
        else:
            break
    return epsilon
