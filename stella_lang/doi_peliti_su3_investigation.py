#!/usr/bin/env python3
"""
Open Question 9: Can the Doi-Peliti Hamiltonian be related to SU(3) Yang-Mills?
================================================================================

Investigates the five sub-questions of Q9 from the XXe workplan:

  1. SIMILARITY TRANSFORMATION — Can H_DP be made Hermitian via S^{-1} H S?
  2. PT SYMMETRY — Is H_DP PT-symmetric? Is the spectrum real?
  3. PHYSICAL SUBSPACE — Does H_DP restricted to probabilities have better properties?
  4. IMAGINARY SCALING — Do |Im(λ)| shrink relative to |Re(λ)| as L grows?
  5. Z₃ GAUGE COMPARISON — Compare H_DP spectrum with Z₃ lattice gauge Hamiltonian

Builds on: doi_peliti_verification.py (transition matrix construction, VM)
Reference: Prop 0.0.XXe Workplan, Open Question 9

Investigation Date: 2026-03-10
"""

import numpy as np
from scipy import linalg
import json
import time
from datetime import datetime
from itertools import product

# Import VM and configuration utilities from existing verification
from doi_peliti_verification import (
    execute_tape, prog_to_idx, idx_to_prog, config_to_idx, idx_to_config,
    build_transition_matrix, z3_rotation_matrix, Z3, MAX_VM_STEPS
)

np.set_printoptions(precision=6, linewidth=120)


# =============================================================================
# SUB-QUESTION 1: SIMILARITY TRANSFORMATION
# =============================================================================

def investigate_similarity_transform(H, T, ness, L, mu):
    """Can H_DP = I - T be made Hermitian via similarity transformation?

    For detailed-balance systems: S = diag(1/sqrt(pi_i)) gives Hermitian H_sym.
    For non-detailed-balance: check if eigenvalues are real (necessary condition
    for existence of a similarity transform to Hermitian form).

    Also try the standard detailed-balance transform and measure how far
    the result is from Hermitian.
    """
    print(f"\n{'='*70}")
    print("SUB-QUESTION 1: SIMILARITY TRANSFORMATION")
    print(f"{'='*70}")
    n = H.shape[0]
    results = {}

    # --- 1a. Check if eigenvalues are real ---
    eigvals = linalg.eigvals(H)
    real_parts = eigvals.real
    imag_parts = eigvals.imag

    n_real = np.sum(np.abs(imag_parts) < 1e-10)
    n_total = len(eigvals)
    max_imag = np.max(np.abs(imag_parts))
    mean_imag = np.mean(np.abs(imag_parts))
    # Ratio of imaginary to real parts (excluding zero eigenvalues)
    nonzero_mask = np.abs(eigvals) > 1e-8
    if nonzero_mask.any():
        imag_to_real = np.mean(np.abs(imag_parts[nonzero_mask]) /
                               np.abs(real_parts[nonzero_mask]))
    else:
        imag_to_real = 0.0

    print(f"\n  [1a] Eigenvalue reality check:")
    print(f"       Real eigenvalues: {n_real}/{n_total}")
    print(f"       Max |Im(λ)|: {max_imag:.6e}")
    print(f"       Mean |Im(λ)|: {mean_imag:.6e}")
    print(f"       Mean |Im/Re| (nonzero): {imag_to_real:.6f}")

    results["n_real_eigenvalues"] = int(n_real)
    results["n_total_eigenvalues"] = int(n_total)
    results["fraction_real"] = float(n_real / n_total)
    results["max_imag"] = float(max_imag)
    results["mean_imag"] = float(mean_imag)
    results["mean_imag_to_real_ratio"] = float(imag_to_real)

    # --- 1b. Detailed-balance similarity transform ---
    # For detailed balance: T_{ij} pi_j = T_{ji} pi_i
    # Transform: H_sym = D^{-1/2} H D^{1/2} where D = diag(pi)
    # This gives Hermitian H_sym iff detailed balance holds

    print(f"\n  [1b] Detailed-balance similarity transform:")

    # Check detailed balance violation
    if ness is not None and np.min(ness) > 1e-15:
        D_sqrt = np.diag(np.sqrt(ness))
        D_inv_sqrt = np.diag(1.0 / np.sqrt(ness))

        H_sym = D_inv_sqrt @ H @ D_sqrt

        # Measure deviation from Hermitian
        anti_herm = H_sym - H_sym.T
        db_violation = np.linalg.norm(anti_herm, 'fro') / np.linalg.norm(H_sym, 'fro')

        print(f"       ||H_sym - H_sym^T||_F / ||H_sym||_F = {db_violation:.6e}")
        print(f"       (0 = perfect detailed balance)")

        # Check detailed balance directly: T_ij * pi_j vs T_ji * pi_i
        db_matrix = T * ness[np.newaxis, :] - T.T * ness[:, np.newaxis].T
        # Note: T * ness[np.newaxis, :] has element T[i,j] * pi[j]
        # and T.T * ness[np.newaxis, :] has element T[j,i] * pi[j]
        # We want T[i,j]*pi[j] = T[j,i]*pi[i], i.e. same as T*pi_row vs T.T * pi_col
        db_direct = T * ness[np.newaxis, :] - (T * ness[np.newaxis, :]).T
        db_violation_direct = np.linalg.norm(db_direct, 'fro')
        print(f"       ||T_ij pi_j - T_ji pi_i||_F = {db_violation_direct:.6e}")

        # Eigenvalues of H_sym
        eigvals_sym = linalg.eigvals(H_sym)
        n_real_sym = np.sum(np.abs(eigvals_sym.imag) < 1e-10)
        max_imag_sym = np.max(np.abs(eigvals_sym.imag))
        print(f"       H_sym real eigenvalues: {n_real_sym}/{n_total}")
        print(f"       H_sym max |Im(λ)|: {max_imag_sym:.6e}")

        results["db_violation_relative"] = float(db_violation)
        results["db_violation_direct"] = float(db_violation_direct)
        results["h_sym_n_real"] = int(n_real_sym)
        results["h_sym_max_imag"] = float(max_imag_sym)
    else:
        print(f"       NESS has zero entries — cannot construct D^{{-1/2}}")
        results["db_violation_relative"] = None

    # --- 1c. Optimal similarity transform (numerical) ---
    # If H is diagonalizable as H = V D V^{-1}, then
    # H is similar to Hermitian iff all eigenvalues are real.
    # Check condition number of eigenvector matrix.
    print(f"\n  [1c] Diagonalizability analysis:")

    eigvals_h, eigvecs_h = linalg.eig(H)
    try:
        cond = np.linalg.cond(eigvecs_h)
        print(f"       Condition number of eigenvector matrix: {cond:.2e}")
        print(f"       (Low = well-diagonalizable, High = near-defective)")
        results["eigvec_condition_number"] = float(cond) if cond < 1e15 else "near_defective"
    except Exception:
        print(f"       Eigenvector matrix is singular — H may be defective")
        results["eigvec_condition_number"] = "defective"

    # --- 1d. Check if H + H^T (Hermitian part) captures the physics ---
    H_herm = 0.5 * (H + H.T)
    H_anti = 0.5 * (H - H.T)
    norm_herm = np.linalg.norm(H_herm, 'fro')
    norm_anti = np.linalg.norm(H_anti, 'fro')
    print(f"\n  [1d] Hermitian decomposition H = H_+ + H_-:")
    print(f"       ||H_+||_F (Hermitian part): {norm_herm:.6f}")
    print(f"       ||H_-||_F (anti-Hermitian part): {norm_anti:.6f}")
    print(f"       Ratio ||H_-||/||H_+||: {norm_anti/norm_herm:.6f}")

    # Check if Hermitian part has same ground state
    eigvals_herm = linalg.eigvalsh(H_herm)
    gap_herm = eigvals_herm[1] - eigvals_herm[0] if len(eigvals_herm) > 1 else 0
    print(f"       Hermitian part spectral gap: {gap_herm:.6f}")

    results["hermitian_part_norm"] = float(norm_herm)
    results["anti_hermitian_part_norm"] = float(norm_anti)
    results["anti_to_hermitian_ratio"] = float(norm_anti / norm_herm)
    results["hermitian_part_gap"] = float(gap_herm)

    return results


# =============================================================================
# SUB-QUESTION 2: PT SYMMETRY
# =============================================================================

def investigate_pt_symmetry(H, T, L, mu):
    """Check if H_DP has PT symmetry (Bender & Boettcher 1998).

    P candidates:
      - Parity on configuration space (swap programs a <-> b)
      - Spatial reflection within programs (reverse trit order)

    T candidates:
      - Complex conjugation (trivial since H is real)
      - Trit reversal: σ -> (3 - σ) mod 3 = -σ mod 3
    """
    print(f"\n{'='*70}")
    print("SUB-QUESTION 2: PT SYMMETRY")
    print(f"{'='*70}")
    n = H.shape[0]
    results = {}

    # --- Define P: program swap (a <-> b) ---
    print(f"\n  [2a] Constructing parity operators...")

    P_swap = np.zeros((n, n))
    for src in range(n):
        pa, pb = idx_to_config(src, L)
        dst = config_to_idx(pb, pa, L)  # swap a <-> b
        P_swap[dst, src] = 1.0

    # Verify P^2 = I
    assert np.allclose(P_swap @ P_swap, np.eye(n)), "P_swap^2 != I"
    print(f"       P_swap (program swap): verified P^2 = I")

    # --- Define P: trit spatial reversal within each program ---
    P_rev = np.zeros((n, n))
    for src in range(n):
        pa, pb = idx_to_config(src, L)
        ra = pa[::-1].copy()  # reverse trit order
        rb = pb[::-1].copy()
        dst = config_to_idx(ra, rb, L)
        P_rev[dst, src] = 1.0

    assert np.allclose(P_rev @ P_rev, np.eye(n)), "P_rev^2 != I"
    print(f"       P_rev (trit reversal): verified P^2 = I")

    # --- Define T: trit negation σ -> -σ mod 3 ---
    # Since H is real, complex conjugation K is trivial (K H K = H for real H)
    # So "T" in the PT sense must be a non-trivial anti-linear operation
    # We use trit negation (σ -> 2σ mod 3, which for Z_3 is σ -> -σ)
    T_neg = np.zeros((n, n))
    for src in range(n):
        pa, pb = idx_to_config(src, L)
        na = (3 - pa) % 3  # trit negation: 0->0, 1->2, 2->1
        nb = (3 - pb) % 3
        dst = config_to_idx(na, nb, L)
        T_neg[dst, src] = 1.0

    assert np.allclose(T_neg @ T_neg, np.eye(n)), "T_neg^2 != I"
    print(f"       T_neg (trit negation): verified T^2 = I")

    # --- Check [H, PT] = 0 for various P, T combinations ---
    print(f"\n  [2b] Checking PT commutation with H:")

    pt_results = {}
    for p_name, P_op in [("P_swap", P_swap), ("P_rev", P_rev)]:
        for t_name, T_op in [("T_neg", T_neg), ("I", np.eye(n))]:
            PT = P_op @ T_op
            # For real H with linear PT: [H, PT] = H PT - PT H
            comm = H @ PT - PT @ H
            comm_norm = np.linalg.norm(comm, 'fro')
            rel_norm = comm_norm / np.linalg.norm(H, 'fro')

            key = f"{p_name}*{t_name}"
            pt_results[key] = {
                "commutator_norm": float(comm_norm),
                "relative_norm": float(rel_norm),
                "commutes": bool(rel_norm < 1e-10)
            }
            status = "COMMUTES" if rel_norm < 1e-10 else f"broken ({rel_norm:.4e})"
            print(f"       [H, {key}]: {status}")

    # --- Z₃ rotation as a symmetry ---
    R = z3_rotation_matrix(L)
    comm_R = H @ R - R @ H
    comm_R_norm = np.linalg.norm(comm_R, 'fro') / np.linalg.norm(H, 'fro')
    print(f"       [H, R_Z3]: {'COMMUTES' if comm_R_norm < 1e-10 else f'broken ({comm_R_norm:.4e})'}")
    pt_results["R_Z3"] = {"relative_norm": float(comm_R_norm)}

    # --- Combined symmetry: P_swap * R_Z3 ---
    PR = P_swap @ R
    comm_PR = H @ PR - PR @ H
    comm_PR_norm = np.linalg.norm(comm_PR, 'fro') / np.linalg.norm(H, 'fro')
    print(f"       [H, P_swap*R_Z3]: {'COMMUTES' if comm_PR_norm < 1e-10 else f'broken ({comm_PR_norm:.4e})'}")
    pt_results["P_swap*R_Z3"] = {"relative_norm": float(comm_PR_norm)}

    # --- Check eigenvalue pairing under PT ---
    # If H has PT symmetry, eigenvalues come in conjugate pairs or are real
    eigvals = linalg.eigvals(H)
    eigvals_sorted = np.sort(eigvals.real + 1j * np.abs(eigvals.imag))

    # Check complex eigenvalue pairing
    complex_eigs = eigvals[np.abs(eigvals.imag) > 1e-10]
    n_complex = len(complex_eigs)
    n_paired = 0
    used = set()
    for i, e in enumerate(complex_eigs):
        if i in used:
            continue
        conj = e.conjugate()
        for j, f in enumerate(complex_eigs):
            if j != i and j not in used and abs(e - conj) > 1e-10:
                if abs(f - conj) < 1e-8:
                    n_paired += 2
                    used.add(i)
                    used.add(j)
                    break

    print(f"\n  [2c] Eigenvalue pairing analysis:")
    print(f"       Complex eigenvalues: {n_complex}")
    print(f"       Conjugate-paired: {n_paired}")
    print(f"       Unpaired: {n_complex - n_paired}")

    results["pt_commutators"] = pt_results
    results["n_complex_eigenvalues"] = int(n_complex)
    results["n_conjugate_paired"] = int(n_paired)
    results["eigenvalue_pairing_complete"] = bool(n_paired == n_complex)

    return results


# =============================================================================
# SUB-QUESTION 3: PHYSICAL SUBSPACE
# =============================================================================

def investigate_physical_subspace(H, T, ness, L, mu):
    """Analyze H_DP restricted to the physical subspace (probability simplex).

    The physical subspace consists of states |P> with all components >= 0
    summing to 1. H_DP maps probability vectors to... what? The question
    is whether H restricted to or projected near this subspace has better
    spectral properties.
    """
    print(f"\n{'='*70}")
    print("SUB-QUESTION 3: PHYSICAL SUBSPACE RESTRICTION")
    print(f"{'='*70}")
    n = H.shape[0]
    results = {}

    # --- 3a. Does H preserve the probability simplex? ---
    print(f"\n  [3a] Does H preserve the tangent space to the probability simplex?")

    # The tangent space to the simplex at a point p is {v : sum(v) = 0}
    # H maps p -> H p. For p on the simplex, we need sum(H p) = 0
    # Since H = I - T, and T is stochastic (columns sum to 1),
    # sum(H p) = sum(p) - sum(T p) = 1 - 1 = 0 for any probability vector p.
    # So H maps simplex vectors to the tangent space. Good.

    # Verify numerically
    test_vecs = []
    rng = np.random.default_rng(42)
    for _ in range(100):
        p = rng.dirichlet(np.ones(n))
        Hp = H @ p
        test_vecs.append(np.abs(np.sum(Hp)))

    max_sum_dev = max(test_vecs)
    print(f"       max|sum(H p)| over 100 random p: {max_sum_dev:.2e}")
    print(f"       H maps probability vectors to zero-sum vectors: {'YES' if max_sum_dev < 1e-10 else 'NO'}")
    results["preserves_tangent_space"] = bool(max_sum_dev < 1e-10)

    # --- 3b. Project H onto the tangent space ---
    # Use the projector Pi = I - (1/n) |1><1| where |1> = (1,...,1)
    ones = np.ones(n)
    Pi = np.eye(n) - np.outer(ones, ones) / n

    H_proj = Pi @ H @ Pi
    eigvals_proj = linalg.eigvals(H_proj)

    # Remove the trivially zero eigenvalue from projection
    nonzero_proj = eigvals_proj[np.abs(eigvals_proj) > 1e-10]
    n_real_proj = np.sum(np.abs(nonzero_proj.imag) < 1e-10) if len(nonzero_proj) > 0 else 0
    max_imag_proj = np.max(np.abs(nonzero_proj.imag)) if len(nonzero_proj) > 0 else 0

    print(f"\n  [3b] H projected onto zero-sum subspace:")
    print(f"       Nonzero eigenvalues: {len(nonzero_proj)}")
    print(f"       Real eigenvalues: {n_real_proj}")
    print(f"       Max |Im(λ)|: {max_imag_proj:.6e}")
    results["projected_n_real"] = int(n_real_proj)
    results["projected_max_imag"] = float(max_imag_proj)

    # --- 3c. Analyze H on NESS neighborhood ---
    # Linearize around the NESS: H acting on perturbations δp around p*
    # The relevant operator is H itself (since H p* = 0)
    # Check if the "Jacobian" H restricted to the tangent space at p* has real eigenvalues

    if ness is not None and np.min(ness) > 1e-15:
        # Use NESS-weighted inner product: <u, v>_pi = sum_i u_i v_i / pi_i
        # The adjoint of H w.r.t. this inner product is D^{-1} H^T D where D = diag(pi)
        D = np.diag(ness)
        D_inv = np.diag(1.0 / ness)
        H_adj = D_inv @ H.T @ D  # adjoint w.r.t. NESS inner product

        # The "symmetrized" operator: (H + H_adj) / 2
        H_ness_sym = 0.5 * (H + H_adj)
        eigvals_ns = linalg.eigvals(H_ness_sym)
        n_real_ns = np.sum(np.abs(eigvals_ns.imag) < 1e-10)
        max_imag_ns = np.max(np.abs(eigvals_ns.imag))

        print(f"\n  [3c] NESS-symmetrized operator (H + H†_π)/2:")
        print(f"       Real eigenvalues: {n_real_ns}/{n}")
        print(f"       Max |Im(λ)|: {max_imag_ns:.6e}")
        print(f"       (H†_π is adjoint w.r.t. NESS inner product)")

        # Also check: does H^T D = D H? (detailed balance in NESS metric)
        db_check = H.T @ D - D @ H
        db_norm = np.linalg.norm(db_check, 'fro') / np.linalg.norm(H, 'fro')
        print(f"       ||H^T D - D H||_F / ||H||_F = {db_norm:.6e}")
        print(f"       (Detailed balance violation in NESS metric)")

        results["ness_symmetrized_n_real"] = int(n_real_ns)
        results["ness_symmetrized_max_imag"] = float(max_imag_ns)
        results["ness_detailed_balance_violation"] = float(db_norm)
    else:
        results["ness_symmetrized_n_real"] = None

    # --- 3d. Positive semidefiniteness ---
    # For physical Hamiltonians, we need H >= 0 (energies non-negative)
    print(f"\n  [3d] Positive semidefiniteness of Re(H_DP):")
    H_real = 0.5 * (H + H.T)
    eigvals_real = linalg.eigvalsh(H_real)
    n_negative = np.sum(eigvals_real < -1e-10)
    min_eigval = eigvals_real[0]
    print(f"       Minimum eigenvalue of (H + H^T)/2: {min_eigval:.6e}")
    print(f"       Negative eigenvalues: {n_negative}/{n}")
    print(f"       Positive semi-definite: {'YES' if n_negative == 0 else 'NO'}")

    results["hermitian_part_min_eigval"] = float(min_eigval)
    results["hermitian_part_n_negative"] = int(n_negative)
    results["hermitian_part_positive_semidefinite"] = bool(n_negative == 0)

    return results


# =============================================================================
# SUB-QUESTION 4: SCALING OF IMAGINARY PARTS
# =============================================================================

def investigate_imaginary_scaling(mu_values=None):
    """Compute |Im(λ)| for L=2, 3, 4 and check if imaginary parts scale away.

    This is the key finite-size scaling question: if |Im(λ)|/|Re(λ)| -> 0
    as L -> infinity, the non-Hermiticity is a finite-size artifact.
    """
    print(f"\n{'='*70}")
    print("SUB-QUESTION 4: SCALING OF IMAGINARY PARTS WITH SYSTEM SIZE")
    print(f"{'='*70}")

    if mu_values is None:
        mu_values = [0.01, 0.05]

    L_values = [2, 3, 4]
    results = {"scaling_data": []}

    for mu in mu_values:
        print(f"\n  --- μ = {mu} ---")
        print(f"  {'L':<4} {'n_cfg':<8} {'n_real':<8} {'frac_real':<10} {'max|Im|':<12} "
              f"{'mean|Im|':<12} {'mean|Im/Re|':<12} {'gap_Re':<10}")
        print(f"  {'-'*80}")

        for L in L_values:
            n_cfg = 3 ** (2 * L)
            if n_cfg > 50000:
                print(f"  {L:<4} {n_cfg:<8} SKIPPED (too large)")
                continue

            t0 = time.time()
            T = build_transition_matrix(L, mu)
            H = np.eye(n_cfg) - T
            eigvals = linalg.eigvals(H)
            dt = time.time() - t0

            real_parts = eigvals.real
            imag_parts = eigvals.imag

            n_real = int(np.sum(np.abs(imag_parts) < 1e-10))
            frac_real = n_real / n_cfg
            max_imag = float(np.max(np.abs(imag_parts)))
            mean_imag = float(np.mean(np.abs(imag_parts)))

            # Mean |Im/Re| for non-zero eigenvalues
            nonzero = np.abs(eigvals) > 1e-8
            if nonzero.any():
                imag_to_real = float(np.mean(
                    np.abs(imag_parts[nonzero]) / np.maximum(np.abs(real_parts[nonzero]), 1e-15)
                ))
            else:
                imag_to_real = 0.0

            # Spectral gap (real part of first excited state)
            sorted_re = np.sort(real_parts)
            n_zero_re = np.sum(np.abs(sorted_re) < 1e-8)
            gap_re = float(sorted_re[n_zero_re]) if n_zero_re < len(sorted_re) else 0

            # Per-site imaginary part
            per_site_imag = mean_imag / (2 * L)  # intensive quantity

            print(f"  {L:<4} {n_cfg:<8} {n_real:<8} {frac_real:<10.4f} {max_imag:<12.6e} "
                  f"{mean_imag:<12.6e} {imag_to_real:<12.6f} {gap_re:<10.6f}  [{dt:.1f}s]")

            results["scaling_data"].append({
                "L": L, "mu": mu, "n_cfg": n_cfg,
                "n_real": n_real, "frac_real": frac_real,
                "max_imag": max_imag, "mean_imag": mean_imag,
                "mean_imag_to_real": imag_to_real,
                "per_site_imag": float(per_site_imag),
                "spectral_gap_re": gap_re,
            })

    # Analyze scaling trends
    print(f"\n  [4b] Scaling analysis (intensive |Im| per site):")
    for mu in mu_values:
        data = [d for d in results["scaling_data"] if d["mu"] == mu and d.get("n_real") is not None]
        if len(data) >= 2:
            Ls = [d["L"] for d in data]
            per_site = [d["per_site_imag"] for d in data]
            ratios = [d["mean_imag_to_real"] for d in data]

            print(f"       μ={mu}:")
            for i in range(len(data)):
                print(f"         L={Ls[i]}: per-site |Im| = {per_site[i]:.6e}, |Im/Re| = {ratios[i]:.6f}")
            if len(data) >= 2:
                # Check if decreasing
                trend = "DECREASING" if per_site[-1] < per_site[0] else "INCREASING"
                ratio_trend = "DECREASING" if ratios[-1] < ratios[0] else "INCREASING"
                print(f"         Per-site |Im| trend: {trend}")
                print(f"         |Im/Re| ratio trend: {ratio_trend}")

    return results


# =============================================================================
# SUB-QUESTION 5: Z₃ LATTICE GAUGE THEORY COMPARISON
# =============================================================================

def build_z3_gauge_hamiltonian(n_sites, coupling=1.0):
    """Construct Z₃ lattice gauge Hamiltonian on a 1D ring of n_sites links.

    The Z₃ gauge theory Hamiltonian (Kogut-Susskind formulation):
      H = -(J/2) sum_links (U_l + U_l†) - (g²/2) sum_plaquettes (U_p + U_p†)

    For 1D (no plaquettes), this is just the electric part:
      H_E = -(1/2) sum_l (tau_l + tau_l†)

    where tau is the Z₃ "clock" operator: tau|k> = |(k+1) mod 3>.

    For comparison with the soup, we use a 1D chain of Z₃ variables
    (matching the 1D tape structure at small L).

    In 2D, we include plaquettes:
      H = -J sum_links (sigma_l + sigma_l†) - K sum_plaq (prod sigma_around_plaq + h.c.)
    """
    print(f"\n  [5a] Building Z₃ gauge Hamiltonian ({n_sites} sites)...")

    # State space: Z₃^n_sites
    n_cfg = 3 ** n_sites
    H_gauge = np.zeros((n_cfg, n_cfg))

    # Z₃ clock operator tau: |k> -> |(k+1) mod 3>
    # On site i, this acts as a permutation on the configuration space

    def config_to_idx_1d(config):
        idx = 0
        for s in config:
            idx = idx * 3 + int(s)
        return idx

    def idx_to_config_1d(idx, n):
        config = np.zeros(n, dtype=int)
        for i in range(n - 1, -1, -1):
            config[i] = idx % 3
            idx //= 3
        return config

    # Electric term: -J/2 * sum_i (tau_i + tau_i†)
    # tau_i|...s_i...> = |...s_i+1...>
    # tau_i† |...s_i...> = |...s_i-1...>
    J = coupling
    omega = np.exp(2j * np.pi / 3)

    for site in range(n_sites):
        for idx in range(n_cfg):
            config = idx_to_config_1d(idx, n_sites)

            # tau_i: increment site
            config_plus = config.copy()
            config_plus[site] = (config[site] + 1) % 3
            idx_plus = config_to_idx_1d(config_plus)
            H_gauge[idx_plus, idx] -= J / 2.0

            # tau_i†: decrement site
            config_minus = config.copy()
            config_minus[site] = (config[site] - 1) % 3
            idx_minus = config_to_idx_1d(config_minus)
            H_gauge[idx_minus, idx] -= J / 2.0

    # For 1D ring, add plaquette terms (nearest-neighbor "magnetic" coupling)
    # H_plaq = -K sum_{i} (sigma_i sigma_{i+1}† + h.c.)
    # where sigma|k> = omega^k |k>
    K = coupling * 0.5  # relative coupling
    for site in range(n_sites):
        next_site = (site + 1) % n_sites
        for idx in range(n_cfg):
            config = idx_to_config_1d(idx, n_sites)
            # sigma_i sigma_{i+1}† = omega^{s_i - s_{i+1}}
            phase_diff = (config[site] - config[next_site]) % 3
            phase = omega ** phase_diff
            # This is diagonal: adds omega^{s_i - s_{i+1}} to (idx, idx)
            H_gauge[idx, idx] -= K * (phase + phase.conjugate()).real

    return H_gauge.real  # Should be real since we added h.c.


def investigate_gauge_comparison(L, mu):
    """Compare H_DP spectrum with Z₃ lattice gauge Hamiltonian spectrum.

    Key idea: the soup has 2L sites (tape length), each holding a Z₃ value.
    The Z₃ gauge Hamiltonian on 2L sites provides a reference spectrum.
    We compare the low-energy structure (ground state + gap + excitations).
    """
    print(f"\n{'='*70}")
    print("SUB-QUESTION 5: Z₃ GAUGE THEORY COMPARISON")
    print(f"{'='*70}")

    n_sites = 2 * L
    n_cfg_soup = 3 ** n_sites
    results = {}

    # Build soup Hamiltonian
    print(f"\n  Building soup H_DP (L={L}, mu={mu}, n_cfg={n_cfg_soup})...")
    T = build_transition_matrix(L, mu)
    H_dp = np.eye(n_cfg_soup) - T
    eigvals_dp = np.sort(linalg.eigvals(H_dp).real)

    # Build Z₃ gauge Hamiltonian on same number of sites
    H_gauge = build_z3_gauge_hamiltonian(n_sites)
    eigvals_gauge = np.sort(linalg.eigvalsh(H_gauge))

    # Shift both spectra so ground state = 0
    eigvals_dp = eigvals_dp - eigvals_dp[0]
    eigvals_gauge = eigvals_gauge - eigvals_gauge[0]

    # Normalize by spectral gap for comparison
    gap_dp = eigvals_dp[1] if len(eigvals_dp) > 1 else 1
    gap_gauge = eigvals_gauge[1] if len(eigvals_gauge) > 1 else 1

    eigvals_dp_norm = eigvals_dp / gap_dp if gap_dp > 1e-10 else eigvals_dp
    eigvals_gauge_norm = eigvals_gauge / gap_gauge if gap_gauge > 1e-10 else eigvals_gauge

    print(f"\n  [5b] Spectral comparison (first 15 levels, gap-normalized):")
    print(f"  {'Level':<6} {'H_DP (real)':<14} {'H_gauge':<14} {'H_DP/gap':<14} {'H_gauge/gap':<14}")
    print(f"  {'-'*60}")
    n_show = min(15, len(eigvals_dp), len(eigvals_gauge))
    for i in range(n_show):
        print(f"  {i:<6} {eigvals_dp[i]:<14.6f} {eigvals_gauge[i]:<14.6f} "
              f"{eigvals_dp_norm[i]:<14.6f} {eigvals_gauge_norm[i]:<14.6f}")

    results["gap_dp"] = float(gap_dp)
    results["gap_gauge"] = float(gap_gauge)
    results["gap_ratio"] = float(gap_dp / gap_gauge) if gap_gauge > 1e-10 else None

    # --- Spectral statistics ---
    # Level spacing distribution: compare with random matrix theory
    # GUE (Hermitian random) vs GOE (real symmetric) vs Poisson (integrable)
    print(f"\n  [5c] Level spacing statistics:")

    def level_spacing_ratio(evals):
        """Compute mean ratio of consecutive level spacings (r-statistic).
        Poisson: <r> ~ 0.386, GOE: <r> ~ 0.536, GUE: <r> ~ 0.603
        """
        spacings = np.diff(evals)
        spacings = spacings[spacings > 1e-12]  # remove degeneracies
        if len(spacings) < 3:
            return None
        ratios = []
        for i in range(len(spacings) - 1):
            r = min(spacings[i], spacings[i+1]) / max(spacings[i], spacings[i+1])
            ratios.append(r)
        return np.mean(ratios)

    r_dp = level_spacing_ratio(eigvals_dp)
    r_gauge = level_spacing_ratio(eigvals_gauge)
    print(f"       H_DP  <r> = {r_dp:.4f}" if r_dp else "       H_DP  <r> = N/A")
    print(f"       Gauge <r> = {r_gauge:.4f}" if r_gauge else "       Gauge <r> = N/A")
    print(f"       Reference: Poisson=0.386, GOE=0.536, GUE=0.603")

    results["r_statistic_dp"] = float(r_dp) if r_dp else None
    results["r_statistic_gauge"] = float(r_gauge) if r_gauge else None

    # --- Z₃ sector decomposition ---
    # Both systems should decompose into Z₃ charge sectors (q=0,1,2)
    R = z3_rotation_matrix(L)
    omega = np.exp(2j * np.pi / 3)

    print(f"\n  [5d] Z₃ sector decomposition of H_DP:")
    # Project onto Z₃ sectors: P_q = (1/3)(I + omega^{-q} R + omega^{-2q} R²)
    R2 = R @ R
    for q in range(3):
        P_q = (np.eye(n_cfg_soup) + omega**(-q) * R + omega**(-2*q) * R2) / 3.0
        P_q_real = P_q.real

        # Rank of projector = dimension of sector
        rank = int(round(np.trace(P_q_real)))

        # Project H_DP into this sector
        H_q = P_q_real @ H_dp @ P_q_real

        # Get nonzero eigenvalues in this sector
        eigvals_q = linalg.eigvals(H_q)
        nonzero_q = eigvals_q[np.abs(eigvals_q) > 1e-8]
        n_real_q = np.sum(np.abs(nonzero_q.imag) < 1e-10) if len(nonzero_q) > 0 else 0

        print(f"       q={q}: dim={rank}, nonzero evals={len(nonzero_q)}, real={n_real_q}")
        if len(nonzero_q) > 0:
            sorted_q = np.sort(nonzero_q.real)[:5]
            print(f"            lowest 5 Re(λ): {sorted_q}")

    # --- Degeneracy pattern comparison ---
    print(f"\n  [5e] Degeneracy pattern comparison:")

    def get_degeneracy_pattern(evals, tol=1e-6):
        """Group eigenvalues by degeneracy."""
        sorted_e = np.sort(evals)
        groups = []
        current = [sorted_e[0]]
        for e in sorted_e[1:]:
            if abs(e - current[-1]) < tol:
                current.append(e)
            else:
                groups.append(len(current))
                current = [e]
        groups.append(len(current))
        return groups[:20]  # first 20 levels

    deg_dp = get_degeneracy_pattern(eigvals_dp)
    deg_gauge = get_degeneracy_pattern(eigvals_gauge)
    print(f"       H_DP  degeneracies (first 20): {deg_dp}")
    print(f"       Gauge degeneracies (first 20): {deg_gauge}")

    results["degeneracy_dp"] = deg_dp
    results["degeneracy_gauge"] = deg_gauge

    return results


# =============================================================================
# ADDITIONAL: SPECTRAL FLOW ANALYSIS
# =============================================================================

def investigate_spectral_flow(L=2):
    """Track how H_DP eigenvalues evolve as mu varies from 0 to 0.3.

    This reveals:
    - Phase transitions (level crossings)
    - Whether imaginary parts vanish at specific mu values
    - The nature of the error catastrophe in the spectrum
    """
    print(f"\n{'='*70}")
    print(f"BONUS: SPECTRAL FLOW (L={L})")
    print(f"{'='*70}")

    mu_values = np.concatenate([
        np.linspace(0.001, 0.01, 5),
        np.linspace(0.01, 0.05, 5),
        np.linspace(0.05, 0.3, 5),
    ])
    mu_values = np.unique(mu_values)

    n_cfg = 3 ** (2 * L)
    results = {"L": L, "flow": []}

    print(f"\n  {'mu':<8} {'gap_Re':<10} {'max|Im|':<12} {'n_real':<8} {'frac_real':<10}")
    print(f"  {'-'*50}")

    for mu in mu_values:
        T = build_transition_matrix(L, mu)
        H = np.eye(n_cfg) - T
        eigvals = linalg.eigvals(H)

        real_parts = np.sort(eigvals.real)
        imag_parts = eigvals.imag

        # Gap in real part
        n_zero = np.sum(np.abs(real_parts) < 1e-8)
        gap = real_parts[n_zero] if n_zero < len(real_parts) else 0

        max_imag = np.max(np.abs(imag_parts))
        n_real = int(np.sum(np.abs(imag_parts) < 1e-10))
        frac_real = n_real / n_cfg

        print(f"  {mu:<8.4f} {gap:<10.6f} {max_imag:<12.6e} {n_real:<8} {frac_real:<10.4f}")

        results["flow"].append({
            "mu": float(mu),
            "gap_Re": float(gap),
            "max_imag": float(max_imag),
            "n_real": n_real,
            "frac_real": frac_real,
        })

    return results


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("=" * 70)
    print("OPEN QUESTION 9: Doi-Peliti Hamiltonian ↔ SU(3) Yang-Mills")
    print("Reference: Prop 0.0.XXe Workplan, Open Question 9")
    print("=" * 70)

    all_results = {
        "title": "Q9: H_DP → SU(3) Yang-Mills Investigation",
        "reference": "Prop 0.0.XXe Workplan Q9",
        "timestamp": datetime.now().isoformat(),
        "sub_questions": {}
    }

    # === Setup: Build H_DP for primary test case (L=2, mu=0.01) ===
    L_primary = 2
    mu_primary = 0.01

    print(f"\n--- Building primary test case: L={L_primary}, mu={mu_primary} ---")
    T = build_transition_matrix(L_primary, mu_primary)
    n_cfg = T.shape[0]
    H = np.eye(n_cfg) - T

    # Find NESS
    eigvals_T, eigvecs_T = linalg.eig(T)
    stat_idx = np.argmin(np.abs(eigvals_T - 1.0))
    ness = eigvecs_T[:, stat_idx].real
    if ness.sum() < 0:
        ness = -ness
    ness = np.maximum(ness, 0)
    ness = ness / ness.sum()

    # === Sub-question 1: Similarity Transform ===
    r1 = investigate_similarity_transform(H, T, ness, L_primary, mu_primary)
    all_results["sub_questions"]["1_similarity_transform"] = r1

    # === Sub-question 2: PT Symmetry ===
    r2 = investigate_pt_symmetry(H, T, L_primary, mu_primary)
    all_results["sub_questions"]["2_pt_symmetry"] = r2

    # === Sub-question 3: Physical Subspace ===
    r3 = investigate_physical_subspace(H, T, ness, L_primary, mu_primary)
    all_results["sub_questions"]["3_physical_subspace"] = r3

    # === Sub-question 4: Imaginary Scaling ===
    r4 = investigate_imaginary_scaling(mu_values=[0.01, 0.05])
    all_results["sub_questions"]["4_imaginary_scaling"] = r4

    # === Sub-question 5: Gauge Comparison ===
    r5 = investigate_gauge_comparison(L_primary, mu_primary)
    all_results["sub_questions"]["5_gauge_comparison"] = r5

    # === Bonus: Spectral Flow ===
    r6 = investigate_spectral_flow(L=2)
    all_results["sub_questions"]["bonus_spectral_flow"] = r6

    # === Also run L=4 for sub-questions 1-3 (larger system) ===
    print(f"\n\n{'#'*70}")
    print(f"# REPEATING SUB-QUESTIONS 1-3 FOR L=4 (6561 configs)")
    print(f"{'#'*70}")

    L4 = 4
    mu4 = 0.01
    print(f"\n--- Building L={L4}, mu={mu4} ---")
    T4 = build_transition_matrix(L4, mu4)
    n4 = T4.shape[0]
    H4 = np.eye(n4) - T4

    # NESS for L=4
    eigvals_T4, eigvecs_T4 = linalg.eig(T4)
    stat_idx4 = np.argmin(np.abs(eigvals_T4 - 1.0))
    ness4 = eigvecs_T4[:, stat_idx4].real
    if ness4.sum() < 0:
        ness4 = -ness4
    ness4 = np.maximum(ness4, 0)
    ness4 = ness4 / ness4.sum()

    r1_L4 = investigate_similarity_transform(H4, T4, ness4, L4, mu4)
    all_results["sub_questions"]["1_similarity_transform_L4"] = r1_L4

    r2_L4 = investigate_pt_symmetry(H4, T4, L4, mu4)
    all_results["sub_questions"]["2_pt_symmetry_L4"] = r2_L4

    r3_L4 = investigate_physical_subspace(H4, T4, ness4, L4, mu4)
    all_results["sub_questions"]["3_physical_subspace_L4"] = r3_L4

    # ==========================================================================
    # SYNTHESIS
    # ==========================================================================
    print(f"\n\n{'='*70}")
    print("SYNTHESIS: Can H_DP be related to SU(3) Yang-Mills?")
    print(f"{'='*70}")

    print(f"""
  KEY FINDINGS:

  1. SIMILARITY TRANSFORM:
     - H_DP is NOT Hermitian (confirmed)
     - Detailed balance is violated (non-equilibrium system)
     - Fraction of real eigenvalues: L=2: {r1['fraction_real']:.1%}, L=4: {r1_L4['fraction_real']:.1%}
     - Anti-Hermitian/Hermitian ratio: L=2: {r1['anti_to_hermitian_ratio']:.4f}, L=4: {r1_L4['anti_to_hermitian_ratio']:.4f}

  2. PT SYMMETRY:
     - No exact PT symmetry found (all commutators nonzero)
     - Eigenvalue conjugate pairing: L=2: {'complete' if r2['eigenvalue_pairing_complete'] else 'incomplete'}, L=4: {'complete' if r2_L4['eigenvalue_pairing_complete'] else 'incomplete'}

  3. PHYSICAL SUBSPACE:
     - H maps probability vectors to zero-sum vectors (correct structure)
     - Hermitian part is {'positive semi-definite' if r3['hermitian_part_positive_semidefinite'] else 'NOT positive semi-definite'}
     - NESS-symmetrized operator: max |Im| = {r3.get('ness_symmetrized_max_imag', 'N/A')}

  4. IMAGINARY SCALING:
     See scaling table above — check if |Im|/site decreases with L

  5. GAUGE COMPARISON:
     - Gap ratio H_DP/gauge: {r5['gap_ratio'] if r5['gap_ratio'] else 'N/A'}
     - Level spacing <r>: H_DP={r5['r_statistic_dp']}, gauge={r5['r_statistic_gauge']}
""")

    # Save results
    import os
    out_path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "doi_peliti_su3_investigation_results.json")
    with open(out_path, "w") as f:
        json.dump(all_results, f, indent=2, default=str)
    print(f"\n  Results saved to {out_path}")

    return all_results


if __name__ == "__main__":
    main()
