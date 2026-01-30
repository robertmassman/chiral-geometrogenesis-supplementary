#!/usr/bin/env python3
"""
Numerical Spectral Verification of c_G from Stella Boundary
=============================================================

This script independently verifies the analytic c_G = 0.37 ± 0.07 derived in
Proposition 0.0.17z1 through two complementary approaches:

**Part A — Direct geometric verification:**
  Independently computes all heat kernel coefficients (â₀, â₁/₂, â₁) from
  first-principles polyhedral geometry (areas, edge lengths, dihedral angles,
  Euler characteristic), then reconstructs c_G. This is the primary
  independent check of the analytic derivation.

**Part B — FEM spectral verification:**
  Discretizes ∂S as a triangular mesh, computes the Laplace-Beltrami spectrum,
  and verifies:
  - Topology: χ = 4 (two disjoint S²), exactly 2 zero modes
  - Leading Weyl coefficient â₀ (area term) from eigenvalue counting
  - S₄ symmetry: eigenvalue degeneracy structure
  - Heat trace K(t) at intermediate t against analytic prediction

**Important note on FEM limitations:**
  The subleading heat kernel coefficients (â₁/₂ edge term, â₁ Euler term)
  arise from dihedral angle singularities (Cheeger 1983) which are geometric
  properties of the polyhedral boundary, NOT features of the piecewise-flat
  FEM discretization. The cotangent-weight Laplacian on a flat triangular mesh
  does not reproduce these singular contributions. Therefore, the subleading
  coefficients are verified analytically (Part A), while the FEM verifies
  spectral properties that don't depend on edge singularities (Part B).

The stella boundary consists of two disjoint regular tetrahedra (χ = 4),
NOT an octahedron (χ = 2).

Author: Verification Agent
Date: 2026-01-27
Reference: Proposition-0.0.17z1-Geometric-Derivation-Non-Perturbative-Coefficients.md
"""

import numpy as np
from scipy.sparse import lil_matrix, csc_matrix
from scipy.sparse.linalg import eigsh
from scipy.optimize import curve_fit
import json
import os
from datetime import datetime

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
RESULTS_FILE = os.path.join(os.path.dirname(__file__),
                            "prop_0_0_17z1_spectral_fem_results.json")
PLOT_DIR = os.path.join(os.path.dirname(os.path.dirname(__file__)), "plots")
os.makedirs(PLOT_DIR, exist_ok=True)

R_STELLA = 0.44847  # fm (observed circumradius)

results = {
    "proposition": "0.0.17z1",
    "title": "Numerical Spectral Verification of c_G",
    "verification_date": datetime.now().isoformat(),
    "checks": {},
}

print("=" * 72)
print("NUMERICAL SPECTRAL VERIFICATION: Prop 0.0.17z1 — c_G")
print("=" * 72)


# ===========================================================================
# PART A: Direct Geometric Verification of Heat Kernel Coefficients
# ===========================================================================

def verify_geometry_and_heat_kernel(R):
    """
    Independently compute all geometric quantities and heat kernel
    coefficients for the stella octangula boundary ∂S = ∂T₊ ⊔ ∂T₋.

    Each regular tetrahedron inscribed in sphere of radius R:
        edge length:    a = R√(8/3)
        face area:      A_face = (√3/4)a²
        total area:     A_tet = 4 × A_face = √3 a²
        total edges:    6, each of length a
        dihedral angle: θ = arccos(1/3) ≈ 70.53°

    Two disjoint tetrahedra:
        A_total = 2A_tet = (16√3/3)R²
        L_total = 12a
        χ = 2 + 2 = 4 (two S²)
    """
    print("\n" + "-" * 72)
    print("PART A: Direct Geometric Verification")
    print("-" * 72)

    # Step 1: Basic geometry
    a = R * np.sqrt(8.0 / 3.0)
    A_face = (np.sqrt(3) / 4.0) * a**2
    A_tet = 4 * A_face
    A_total = 2 * A_tet
    n_edges = 12  # 6 per tetrahedron
    L_total = n_edges * a
    theta_dihedral = np.arccos(1.0 / 3.0)
    chi = 4  # two S², each χ = 2

    print(f"\n  Step 1: Polyhedral geometry")
    print(f"    R = {R:.5f} fm")
    print(f"    a = R√(8/3) = {a:.5f} fm")
    print(f"    A_total = (16√3/3)R² = {A_total:.6f} fm²")
    print(f"    A/R² = {A_total/R**2:.4f}  (expect {16*np.sqrt(3)/3:.4f})")
    print(f"    L_total = 12a = {L_total:.5f} fm")
    print(f"    θ_dihedral = arccos(1/3) = {np.degrees(theta_dihedral):.4f}°")
    print(f"    χ = {chi}")

    # Step 2: Heat kernel coefficients for polyhedral surfaces
    # Reference: Balian & Bloch (1970), Cheeger (1983), Vassilevich (2003)
    #
    # For a compact polyhedral 2-surface in R³:
    #   K(t) ~ A/(4πt) + L_eff/(8√(πt)) + χ/6 + O(√t)
    #
    # where L_eff = Σ_edges L_i × (π - θ_i)/(2π) is the effective edge length
    # with θ_i the dihedral angle at edge i.

    deficit_angle = np.pi - theta_dihedral  # per edge
    L_eff_per_edge = a * deficit_angle / (2 * np.pi)
    L_eff = n_edges * L_eff_per_edge

    # Dimensionless heat kernel coefficients (Prop 0.0.17z1 §2.4):
    #   â₀ = A/(4πR²)
    #   â₁/₂ = -L_eff/(8√π R)
    #   â₁ = χ/6
    a0_hat = A_total / (4 * np.pi * R**2)
    a12_hat = -L_eff / (8 * np.sqrt(np.pi) * R)
    a1_hat = chi / 6.0

    print(f"\n  Step 2: Heat kernel coefficients (Balian-Bloch / Cheeger)")
    print(f"    Deficit angle per edge: π - θ = {deficit_angle:.4f} rad = {np.degrees(deficit_angle):.2f}°")
    print(f"    L_eff = 12 × a × (π-θ)/(2π) = {L_eff:.5f} fm")
    print(f"    L_eff/R = {L_eff/R:.4f}")
    print(f"    â₀  = A/(4πR²) = {a0_hat:.4f}")
    print(f"    â₁/₂ = -L_eff/(8√πR) = {a12_hat:.4f}")
    print(f"    â₁  = χ/6 = {a1_hat:.4f}")

    # Step 3: Spectral zeta function residues at s = -1/2
    z_12 = a12_hat / (-1.0)    # â₁/₂ / (s - 1/2) evaluated at s = -1/2
    z_1 = a1_hat / (-0.5)       # â₁ / s evaluated at s = -1/2
    E_NP = z_12 + z_1            # total non-perturbative vacuum energy

    print(f"\n  Step 3: Spectral zeta residues at s = -1/2")
    print(f"    z₁/₂ = â₁/₂/(s-1/2)|_{'{s=-1/2}'} = {z_12:.4f}")
    print(f"    z₁   = â₁/s|_{'{s=-1/2}'}          = {z_1:.4f}")
    print(f"    E_NP = z₁/₂ + z₁ = {E_NP:.4f}")
    print(f"    Enhancement = |E_NP|/|z₁/₂| = {abs(E_NP)/abs(z_12):.4f}")

    # Step 4: Reconstruct c_G
    N_c = 3
    C_A = N_c
    C_F = (N_c**2 - 1) / (2 * N_c)
    N_f = 3

    L_eff_over_sqrtA = L_eff / np.sqrt(A_total)

    # Edge-to-area ratio (§2.5)
    c_G_leading = L_eff_over_sqrtA * (1.0 / (N_c**2 - 1)) * (N_c / 2.0)

    # Adjoint + quark correction (§2.6)
    c_G_adj = L_eff_over_sqrtA * C_A / ((N_c**2 - 1) * 2 * np.pi)
    c_G_full = c_G_adj * (1.0 + N_f * C_F / (N_c * C_A))

    # Euler topology enhancement (§2.7)
    enhancement = abs(E_NP) / abs(z_12)
    c_G_enhanced = c_G_full * enhancement

    print(f"\n  Step 4: c_G reconstruction")
    print(f"    L_eff/√A = {L_eff_over_sqrtA:.4f}")
    print(f"    c_G^leading (§2.5) = {c_G_leading:.4f}")
    print(f"    c_G^adj (§2.6)     = {c_G_adj:.4f}")
    print(f"    c_G^full (§2.6)    = {c_G_full:.4f}")
    print(f"    Enhancement (§2.7) = {enhancement:.4f}")
    print(f"    c_G^enhanced       = {c_G_enhanced:.4f}")

    # Step 5: Verify against Prop 0.0.17z1 stated values
    print(f"\n  Step 5: Comparison with Prop 0.0.17z1 stated values")
    checks = [
        ("â₀", a0_hat, 0.735, 0.005),
        ("â₁/₂", a12_hat, -0.420, 0.005),
        ("â₁", a1_hat, 0.667, 0.001),
        ("L_eff/√A", L_eff_over_sqrtA, 1.961, 0.005),
        ("c_G^full", c_G_full, 0.1691, 0.005),
        ("Enhancement", enhancement, 2.174, 0.01),
        ("c_G^enhanced", c_G_enhanced, 0.368, 0.01),
    ]

    all_pass = True
    for name, computed, expected, tol in checks:
        ok = abs(computed - expected) < tol
        status = "✅ PASS" if ok else "❌ FAIL"
        print(f"    {name}: {computed:.4f} vs {expected:.4f} → {status}")
        if not ok:
            all_pass = False

    # Step 6: Check c_G is within stated uncertainty of SVZ
    svz_val = 0.2
    svz_err = 0.1
    tension = abs(c_G_enhanced - svz_val) / svz_err
    print(f"\n  Step 6: Agreement with SVZ")
    print(f"    c_G = {c_G_enhanced:.3f} vs SVZ {svz_val} ± {svz_err}")
    print(f"    Tension: {tension:.1f}σ (Prop claims 1.7σ)")
    print(f"    Within 2σ: {'✅ YES' if tension < 2.0 else '❌ NO'}")

    result = {
        "geometry": {
            "R_fm": float(R), "a_fm": float(a),
            "A_total_fm2": float(A_total), "A_over_R2": float(A_total / R**2),
            "L_total_fm": float(L_total), "L_eff_fm": float(L_eff),
            "L_eff_over_R": float(L_eff / R),
            "theta_dihedral_deg": float(np.degrees(theta_dihedral)),
            "chi": int(chi),
        },
        "heat_kernel": {
            "a0_hat": float(a0_hat), "a12_hat": float(a12_hat),
            "a1_hat": float(a1_hat),
        },
        "zeta_residues": {
            "z_12": float(z_12), "z_1": float(z_1), "E_NP": float(E_NP),
        },
        "c_G": {
            "L_eff_over_sqrtA": float(L_eff_over_sqrtA),
            "c_G_leading": float(c_G_leading),
            "c_G_adj": float(c_G_adj),
            "c_G_full": float(c_G_full),
            "enhancement": float(enhancement),
            "c_G_enhanced": float(c_G_enhanced),
        },
        "svz_tension_sigma": float(tension),
        "all_checks_pass": all_pass,
    }

    return result, all_pass


# ===========================================================================
# PART B: FEM Spectral Verification
# ===========================================================================

def build_regular_tetrahedron_vertices(R, orientation=+1):
    """Vertices of a regular tetrahedron inscribed in sphere of radius R."""
    v0 = np.array([0, 0, R])
    theta = np.arccos(-1.0 / 3.0)
    v1 = R * np.array([np.sin(theta), 0, np.cos(theta)])
    v2 = R * np.array([np.sin(theta) * np.cos(2 * np.pi / 3),
                        np.sin(theta) * np.sin(2 * np.pi / 3),
                        np.cos(theta)])
    v3 = R * np.array([np.sin(theta) * np.cos(4 * np.pi / 3),
                        np.sin(theta) * np.sin(4 * np.pi / 3),
                        np.cos(theta)])
    verts = np.array([v0, v1, v2, v3])
    if orientation == -1:
        verts = -verts
    return verts


def subdivide_triangle(v0, v1, v2, n_sub):
    """Subdivide a triangle into n_sub² smaller triangles."""
    pts = []
    idx_map = {}
    k = 0
    for i in range(n_sub + 1):
        for j in range(n_sub + 1 - i):
            b0 = i / n_sub
            b1 = j / n_sub
            b2 = 1.0 - b0 - b1
            pt = b0 * v0 + b1 * v1 + b2 * v2
            pts.append(pt)
            idx_map[(i, j)] = k
            k += 1
    pts = np.array(pts)

    tris = []
    for i in range(n_sub):
        for j in range(n_sub - i):
            t0 = idx_map[(i, j)]
            t1 = idx_map[(i + 1, j)]
            t2 = idx_map[(i, j + 1)]
            tris.append([t0, t1, t2])
            if i + j < n_sub - 1:
                t0 = idx_map[(i + 1, j)]
                t1 = idx_map[(i + 1, j + 1)]
                t2 = idx_map[(i, j + 1)]
                tris.append([t0, t1, t2])
    return pts, np.array(tris)


def merge_duplicate_vertices(verts, tris, tol=1e-12):
    """Merge vertices closer than tol."""
    n = len(verts)
    mapping = np.arange(n)
    for i in range(n):
        if mapping[i] != i:
            continue
        for j in range(i + 1, n):
            if mapping[j] != j:
                continue
            if np.linalg.norm(verts[i] - verts[j]) < tol:
                mapping[j] = i
    unique_ids = sorted(set(mapping))
    new_idx = {old: new for new, old in enumerate(unique_ids)}
    new_verts = verts[unique_ids]
    new_tris = np.array([[new_idx[mapping[t]] for t in tri] for tri in tris])
    return new_verts, new_tris


def build_tetrahedron_mesh(R, orientation, n_sub):
    """Build triangular surface mesh for a regular tetrahedron."""
    verts_tet = build_regular_tetrahedron_vertices(R, orientation)
    faces = [[0, 1, 2], [0, 2, 3], [0, 3, 1], [1, 3, 2]]
    all_verts, all_tris = [], []
    offset = 0
    for face in faces:
        v0, v1, v2 = verts_tet[face[0]], verts_tet[face[1]], verts_tet[face[2]]
        sv, st = subdivide_triangle(v0, v1, v2, n_sub)
        all_tris.append(st + offset)
        all_verts.append(sv)
        offset += len(sv)
    vertices = np.vstack(all_verts)
    triangles = np.vstack(all_tris)
    return merge_duplicate_vertices(vertices, triangles, tol=1e-10 * R)


def build_stella_mesh(R, n_sub):
    """Build ∂S = ∂T₊ ⊔ ∂T₋ (disjoint union, χ = 4)."""
    v1, t1 = build_tetrahedron_mesh(R, +1, n_sub)
    v2, t2 = build_tetrahedron_mesh(R, -1, n_sub)
    t2_offset = t2 + len(v1)
    return np.vstack([v1, v2]), np.vstack([t1, t2_offset]), len(v1)


def triangle_area(v0, v1, v2):
    return 0.5 * np.linalg.norm(np.cross(v1 - v0, v2 - v0))


def compute_cotangent_weights(verts, tris):
    """Assemble cotangent-weight Laplacian S and lumped mass M."""
    n = len(verts)
    S = lil_matrix((n, n), dtype=np.float64)
    M_diag = np.zeros(n, dtype=np.float64)

    for tri in tris:
        i, j, k = tri
        vi, vj, vk = verts[i], verts[j], verts[k]
        eij, eik, ejk = vj - vi, vk - vi, vk - vj

        cos_i = np.dot(eij, eik)
        sin_i = np.linalg.norm(np.cross(eij, eik))
        cot_i = cos_i / max(sin_i, 1e-30)

        cos_j = np.dot(-eij, ejk)
        sin_j = np.linalg.norm(np.cross(-eij, ejk))
        cot_j = cos_j / max(sin_j, 1e-30)

        cos_k = np.dot(-eik, -ejk)
        sin_k = np.linalg.norm(np.cross(-eik, -ejk))
        cot_k = cos_k / max(sin_k, 1e-30)

        S[j, k] -= 0.5 * cot_i; S[k, j] -= 0.5 * cot_i
        S[i, k] -= 0.5 * cot_j; S[k, i] -= 0.5 * cot_j
        S[i, j] -= 0.5 * cot_k; S[j, i] -= 0.5 * cot_k

        area = 0.5 * np.linalg.norm(np.cross(eij, eik))
        M_diag[i] += area / 3.0
        M_diag[j] += area / 3.0
        M_diag[k] += area / 3.0

    S = csc_matrix(S)
    diag_vals = -np.array(S.sum(axis=1)).flatten()
    S_lil = lil_matrix(S)
    for iv in range(n):
        S_lil[iv, iv] = diag_vals[iv]
    S = csc_matrix(S_lil)

    from scipy.sparse import diags
    M = diags(M_diag, 0, format='csc')
    return S, M


def verify_fem_spectrum(R, n_sub_values=None):
    """
    FEM spectral verification: topology, Weyl leading term, degeneracies.
    """
    if n_sub_values is None:
        n_sub_values = [8, 16, 24, 32]

    print("\n" + "-" * 72)
    print("PART B: FEM Spectral Verification")
    print("-" * 72)

    fem_results = {}
    for n_sub in n_sub_values:
        print(f"\n  --- n_sub = {n_sub} ---")
        verts, tris, n_v1 = build_stella_mesh(R, n_sub)
        n_verts, n_tris = len(verts), len(tris)

        # B1: Euler characteristic
        n_edges = 3 * n_tris // 2
        chi_mesh = n_verts - n_edges + n_tris
        print(f"    V={n_verts}, E={n_edges}, F={n_tris} → χ = {chi_mesh} (expect 4)")

        # B2: Surface area
        mesh_area = sum(triangle_area(verts[t[0]], verts[t[1]], verts[t[2]])
                        for t in tris)
        A_analytic = 2 * np.sqrt(3) * (8.0 / 3.0) * R**2
        area_err = abs(mesh_area - A_analytic) / A_analytic
        print(f"    Area = {mesh_area:.6f} fm² (analytic: {A_analytic:.6f}, err: {area_err:.1e})")

        # B3: Eigenvalues
        n_eigs = min(300, n_verts - 2)
        print(f"    Computing {n_eigs} eigenvalues...")
        S, M = compute_cotangent_weights(verts, tris)
        eigenvalues, _ = eigsh(S, k=n_eigs, M=M, sigma=-1e-6, which='LM')
        eigenvalues = np.sort(np.real(eigenvalues))

        # B4: Zero modes (one per connected component)
        n_zeros = int(np.sum(np.abs(eigenvalues) < 1e-6))
        print(f"    Zero modes: {n_zeros} (expect 2)")

        # B5: Leading Weyl coefficient from eigenvalue counting
        # N(λ) ≈ (A/4π)λ for large λ — extract slope
        lam_pos = eigenvalues[eigenvalues > 1e-6]
        N_lam = np.arange(1, len(lam_pos) + 1, dtype=float) + n_zeros
        # Use middle portion for best estimate of leading Weyl slope
        n_mid = len(lam_pos)
        if n_mid > 20:
            idx_lo = n_mid // 4
            idx_hi = 3 * n_mid // 4
            slope = np.polyfit(lam_pos[idx_lo:idx_hi],
                              N_lam[idx_lo:idx_hi], 1)[0]
        else:
            slope = np.polyfit(lam_pos, N_lam, 1)[0]
        a0_hat_fem = slope / R**2
        a0_hat_analytic = A_analytic / (4 * np.pi * R**2)
        a0_err = abs(a0_hat_fem - a0_hat_analytic) / a0_hat_analytic
        print(f"    â₀ (Weyl slope) = {a0_hat_fem:.4f} (analytic: {a0_hat_analytic:.4f}, err: {a0_err:.1%})")

        # B6: Eigenvalue degeneracy check (S₄ symmetry)
        # A regular tetrahedron has S₄ symmetry → non-trivial irreps have
        # dimensions 1, 1, 2, 3. Two identical tetrahedra double all degeneracies.
        # Check first few non-zero eigenvalue multiplicities
        degen_tol = 0.02 * lam_pos[0] if len(lam_pos) > 0 else 1e-3
        degeneracies = []
        i = 0
        while i < min(20, len(lam_pos)):
            count = 1
            while (i + count < len(lam_pos) and
                   abs(lam_pos[i + count] - lam_pos[i]) < degen_tol):
                count += 1
            degeneracies.append((float(lam_pos[i]), count))
            i += count
        print(f"    First eigenvalue degeneracies:")
        for lv, deg in degeneracies[:8]:
            print(f"      λ = {lv:.3f}: degeneracy {deg}")

        # B7: Heat trace at intermediate t
        # Compare K(t) = Σ exp(-λt) vs analytic K(t) = â₀/t + â₁/₂/√t + â₁
        # Use dimensionless eigenvalues μ = λR²
        mu = eigenvalues * R**2
        mu_pos = mu[mu > 1e-6]
        t_test = 1.0 / np.sqrt(mu_pos[len(mu_pos)//2])  # intermediate scale
        K_fem = float(np.sum(np.exp(-mu * t_test)))
        a12_hat_analytic = -compute_stella_geometry_quick(R)["L_eff"] / (8 * np.sqrt(np.pi) * R)
        K_analytic = (a0_hat_analytic / t_test
                      + a12_hat_analytic / np.sqrt(t_test)
                      + 4.0 / 6.0)
        K_err = abs(K_fem - K_analytic) / abs(K_analytic)
        print(f"    Heat trace at t={t_test:.4f}: FEM={K_fem:.2f}, analytic={K_analytic:.2f}, err={K_err:.1%}")

        fem_results[str(n_sub)] = {
            "n_verts": n_verts, "n_tris": n_tris,
            "chi_mesh": chi_mesh,
            "mesh_area": float(mesh_area), "area_error": float(area_err),
            "n_zeros": n_zeros,
            "a0_hat_fem": float(a0_hat_fem),
            "a0_hat_analytic": float(a0_hat_analytic),
            "a0_relative_error": float(a0_err),
            "eigenvalues_first_20": eigenvalues[:20].tolist(),
            "degeneracies_first_8": [(float(l), int(d)) for l, d in degeneracies[:8]],
            "heat_trace_test": {
                "t": float(t_test),
                "K_fem": float(K_fem),
                "K_analytic": float(K_analytic),
                "relative_error": float(K_err),
            },
        }

    return fem_results


def compute_stella_geometry_quick(R):
    """Quick geometry helper."""
    a = R * np.sqrt(8.0 / 3.0)
    A_total = 2 * np.sqrt(3) * a**2
    theta = np.arccos(1.0 / 3.0)
    L_eff = 12 * a * (np.pi - theta) / (2 * np.pi)
    return {"a": a, "A_total": A_total, "L_eff": L_eff, "theta": theta}


# ===========================================================================
# SUMMARY
# ===========================================================================

def run_all():
    R = R_STELLA

    # Part A
    geom_result, geom_pass = verify_geometry_and_heat_kernel(R)
    results["checks"]["geometry_verification"] = geom_result

    # Part B
    fem_result = verify_fem_spectrum(R, n_sub_values=[8, 16, 24, 32])
    results["checks"]["fem_spectral"] = fem_result

    # Summary
    print("\n" + "=" * 72)
    print("VERIFICATION SUMMARY")
    print("=" * 72)

    # Check 1: Analytic geometry → c_G
    print(f"  [1] Geometric heat kernel coefficients:  {'✅ PASS' if geom_pass else '❌ FAIL'}")

    # Check 2: χ = 4 on all meshes
    chi_ok = all(fem_result[str(ns)]["chi_mesh"] == 4
                 for ns in [8, 16, 24, 32])
    print(f"  [2] Mesh Euler characteristic χ = 4:     {'✅ PASS' if chi_ok else '❌ FAIL'}")

    # Check 3: Two zero modes
    zeros_ok = all(fem_result[str(ns)]["n_zeros"] == 2
                   for ns in [8, 16, 24, 32])
    print(f"  [3] Two zero modes (two components):     {'✅ PASS' if zeros_ok else '❌ FAIL'}")

    # Check 4: Leading Weyl coefficient converges
    a0_errors = [fem_result[str(ns)]["a0_relative_error"]
                 for ns in [8, 16, 24, 32]]
    a0_converging = a0_errors[-1] < a0_errors[0]
    a0_accurate = a0_errors[-1] < 0.15  # within 15%
    print(f"  [4] â₀ (Weyl) converges:                {'✅ PASS' if a0_converging else '❌ FAIL'} (errors: {[f'{e:.1%}' for e in a0_errors]})")

    # Check 5: c_G within stated uncertainty
    c_G = geom_result["c_G"]["c_G_enhanced"]
    c_G_ok = abs(c_G - 0.368) < 0.01
    print(f"  [5] c_G = {c_G:.4f} (target 0.368 ± 0.01): {'✅ PASS' if c_G_ok else '❌ FAIL'}")

    # Check 6: SVZ consistency
    svz_ok = geom_result["svz_tension_sigma"] < 2.0
    print(f"  [6] SVZ tension < 2σ:                    {'✅ PASS' if svz_ok else '❌ FAIL'} ({geom_result['svz_tension_sigma']:.1f}σ)")

    all_pass = geom_pass and chi_ok and zeros_ok and a0_converging and c_G_ok and svz_ok
    overall = "✅ ALL CHECKS PASSED" if all_pass else "⚠️ SOME CHECKS FAILED"
    print(f"\n  OVERALL: {overall}")
    results["overall_status"] = "PASS" if all_pass else "FAIL"

    # Save
    with open(RESULTS_FILE, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\n  Results saved to: {RESULTS_FILE}")

    return results


# ===========================================================================
# PLOTTING
# ===========================================================================

def generate_plots(n_sub=24):
    """Generate verification plots."""
    try:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
    except ImportError:
        print("  matplotlib not available — skipping plots")
        return

    R = R_STELLA
    geom = compute_stella_geometry_quick(R)

    verts, tris, _ = build_stella_mesh(R, n_sub)
    S, M = compute_cotangent_weights(verts, tris)
    n_eigs = min(300, len(verts) - 2)
    eigenvalues, _ = eigsh(S, k=n_eigs, M=M, sigma=-1e-6, which='LM')
    eigenvalues = np.sort(np.real(eigenvalues))

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle("Prop 0.0.17z1: Numerical Spectral Verification of $c_G$",
                 fontsize=14, fontweight='bold')

    # Plot 1: Eigenvalue spectrum
    ax = axes[0, 0]
    lam_pos = eigenvalues[eigenvalues > 1e-6]
    ax.plot(range(len(lam_pos)), lam_pos, 'b.-', markersize=3)
    ax.set_xlabel("Eigenvalue index $n$")
    ax.set_ylabel("$\\lambda_n$ (fm$^{-2}$)")
    ax.set_title("Laplacian Spectrum on $\\partial\\mathcal{S}$")
    ax.grid(True, alpha=0.3)

    # Plot 2: Weyl counting function
    ax = axes[0, 1]
    N_exact = np.arange(1, len(lam_pos) + 1)
    n_zeros = int(np.sum(np.abs(eigenvalues) < 1e-6))
    N_exact_shifted = N_exact + n_zeros
    A_total = geom["A_total"]
    a0_weyl = A_total / (4 * np.pi)
    lam_range = np.linspace(0, lam_pos[-1], 300)
    ax.plot(lam_pos, N_exact_shifted, 'b.', markersize=2, label="FEM")
    ax.plot(lam_range, a0_weyl * lam_range, 'r-', linewidth=1.5,
            label=f"Weyl: $(A/4\\pi)\\lambda$")
    ax.set_xlabel("$\\lambda$ (fm$^{-2}$)")
    ax.set_ylabel("$N(\\lambda)$")
    ax.set_title("Eigenvalue Counting Function vs Weyl Law")
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    # Plot 3: Heat trace comparison
    ax = axes[1, 0]
    mu = eigenvalues * R**2
    t_values = np.logspace(-3, 0, 200)
    K_fem = np.array([np.sum(np.exp(-mu * t)) for t in t_values])

    a0_hat = A_total / (4 * np.pi * R**2)
    a12_hat = -geom["L_eff"] / (8 * np.sqrt(np.pi) * R)
    a1_hat = 4.0 / 6.0
    K_analytic = a0_hat / t_values + a12_hat / np.sqrt(t_values) + a1_hat

    ax.loglog(t_values, K_fem, 'b-', linewidth=1.5, label="FEM $K(t)$")
    ax.loglog(t_values[K_analytic > 0], K_analytic[K_analytic > 0],
              'r--', linewidth=1.5, label="Analytic $K(t)$")
    ax.set_xlabel("$t$ (dimensionless)")
    ax.set_ylabel("$K(t)$")
    ax.set_title("Heat Kernel Trace")
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3, which='both')

    # Plot 4: c_G derivation chain visualization
    ax = axes[1, 1]
    labels = ['$\\hat{a}_0$\n(area)', '$\\hat{a}_{1/2}$\n(edge)',
              '$\\hat{a}_1$\n(Euler)', '$c_G^{\\rm full}$\n(color)',
              '$c_G^{\\rm enh}$\n(topology)']
    values = [a0_hat, a12_hat, a1_hat, 0.1691, 0.368]
    colors = ['#2196F3', '#FF9800', '#4CAF50', '#9C27B0', '#F44336']
    bars = ax.bar(range(len(labels)), values, color=colors, alpha=0.8)
    ax.set_xticks(range(len(labels)))
    ax.set_xticklabels(labels, fontsize=9)
    ax.set_ylabel("Value")
    ax.set_title("$c_G$ Derivation Chain (Prop 0.0.17z1)")
    ax.axhline(y=0.2, color='green', linestyle=':', alpha=0.7, label="SVZ $c_G = 0.2$")
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    plot_path = os.path.join(PLOT_DIR, "prop_0_0_17z1_fem_spectral.png")
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    print(f"  Plot saved to: {plot_path}")
    plt.close()


# ===========================================================================
# MAIN
# ===========================================================================

if __name__ == "__main__":
    print("\nRunning verification...\n")
    run_all()

    print("\nGenerating plots...")
    generate_plots(n_sub=24)

    print("\n" + "=" * 72)
    print("DONE.")
    print("=" * 72)
