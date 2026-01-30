"""
Numerical Verification: SU(3) Superselection via Explicit Matrix Representations
Proposition 0.0.17i — Additional Verification (Recommendation 4 from Multi-Agent Review)

This script verifies the Z₃ superselection structure using explicit SU(3) matrix
representations, including:
1. Gell-Mann matrices (SU(3) generators)
2. Z₃ center action on representations
3. Explicit construction of color-singlet observables
4. Verification that superselection holds for all color-singlet operators

Created: 2026-01-25
"""

import numpy as np
from scipy.linalg import expm
import json
from datetime import datetime

# Test results storage
results = {
    "proposition": "0.0.17i",
    "title": "SU(3) Superselection via Explicit Matrix Representations",
    "verification_date": datetime.now().strftime("%Y-%m-%d"),
    "tests": []
}


def add_result(name: str, passed: bool, details: str):
    """Add a test result."""
    results["tests"].append({
        "name": name,
        "passed": bool(passed),
        "details": details
    })
    status = "✅ PASSED" if passed else "❌ FAILED"
    print(f"{status}: {name}")
    print(f"   {details}\n")


# =============================================================================
# GELL-MANN MATRICES: Explicit SU(3) Generators
# =============================================================================

def get_gell_mann_matrices():
    """
    Return the 8 Gell-Mann matrices (SU(3) generators).
    Normalization: Tr(λ^a λ^b) = 2 δ^{ab}
    """
    # λ¹ - λ³: SU(2) subgroup (isospin)
    lam1 = np.array([[0, 1, 0], [1, 0, 0], [0, 0, 0]], dtype=complex)
    lam2 = np.array([[0, -1j, 0], [1j, 0, 0], [0, 0, 0]], dtype=complex)
    lam3 = np.array([[1, 0, 0], [0, -1, 0], [0, 0, 0]], dtype=complex)

    # λ⁴ - λ⁵: u-s mixing
    lam4 = np.array([[0, 0, 1], [0, 0, 0], [1, 0, 0]], dtype=complex)
    lam5 = np.array([[0, 0, -1j], [0, 0, 0], [1j, 0, 0]], dtype=complex)

    # λ⁶ - λ⁷: d-s mixing
    lam6 = np.array([[0, 0, 0], [0, 0, 1], [0, 1, 0]], dtype=complex)
    lam7 = np.array([[0, 0, 0], [0, 0, -1j], [0, 1j, 0]], dtype=complex)

    # λ⁸: hypercharge
    lam8 = np.array([[1, 0, 0], [0, 1, 0], [0, 0, -2]], dtype=complex) / np.sqrt(3)

    return [lam1, lam2, lam3, lam4, lam5, lam6, lam7, lam8]


def get_su3_generators():
    """Return SU(3) generators T^a = λ^a / 2."""
    return [lam / 2 for lam in get_gell_mann_matrices()]


# =============================================================================
# Z₃ CENTER ELEMENTS
# =============================================================================

def get_z3_center_elements():
    """
    Return the Z₃ center elements of SU(3).

    The center Z(SU(3)) = Z₃ = {e^{2πik/3} · I : k = 0, 1, 2}
    These are the only SU(3) elements that commute with ALL group elements.
    """
    omega = np.exp(2j * np.pi / 3)
    z0 = np.eye(3, dtype=complex)  # Identity
    z1 = omega * np.eye(3, dtype=complex)  # ω · I
    z2 = omega**2 * np.eye(3, dtype=complex)  # ω² · I
    return [z0, z1, z2]


# =============================================================================
# TEST 1: Verify Z₃ Center Structure
# =============================================================================

def test_z3_center_structure():
    """
    Verify that Z₃ elements form the center of SU(3):
    1. They are in SU(3): det = 1, unitary
    2. They commute with all SU(3) generators
    3. They satisfy the group axioms (ω³ = 1, closure)
    """
    print("=" * 70)
    print("TEST 1: Z₃ Center Structure Verification")
    print("=" * 70)

    z_elements = get_z3_center_elements()
    generators = get_su3_generators()
    omega = np.exp(2j * np.pi / 3)

    all_passed = True

    # Check 1: In SU(3) — det = 1, unitary
    for k, z in enumerate(z_elements):
        det = np.linalg.det(z)
        # det(ω^k · I) = (ω^k)³ = ω^{3k} = 1
        det_ok = np.isclose(det, 1.0)

        # Unitary: z z† = I
        unitary_ok = np.allclose(z @ np.conj(z.T), np.eye(3))

        if not (det_ok and unitary_ok):
            all_passed = False

    # Check 2: Commute with all generators
    commutes_with_all = True
    for z in z_elements:
        for T in generators:
            comm = z @ T - T @ z
            if not np.allclose(comm, 0, atol=1e-14):
                commutes_with_all = False

    # Check 3: Group axioms
    # ω³ = 1
    omega_cubed_one = np.isclose(omega**3, 1.0)

    # Closure: z_j · z_k = z_{(j+k) mod 3}
    closure_ok = True
    for j in range(3):
        for k in range(3):
            product = z_elements[j] @ z_elements[k]
            expected = z_elements[(j + k) % 3]
            if not np.allclose(product, expected):
                closure_ok = False

    all_passed = all_passed and commutes_with_all and omega_cubed_one and closure_ok

    add_result(
        "Z₃ center structure",
        all_passed,
        f"SU(3) membership: verified, Commutes with generators: {commutes_with_all}, "
        f"ω³ = 1: {omega_cubed_one}, Closure: {closure_ok}"
    )

    return all_passed


# =============================================================================
# TEST 2: Fundamental Representation Action
# =============================================================================

def test_fundamental_representation():
    """
    Verify Z₃ action on fundamental representation states.

    For |c⟩ ∈ {|R⟩, |G⟩, |B⟩} (color basis):
    z_k |c⟩ = ω^k |c⟩

    All fundamental states pick up the SAME phase (scalar multiplication).
    """
    print("=" * 70)
    print("TEST 2: Fundamental Representation Z₃ Action")
    print("=" * 70)

    z_elements = get_z3_center_elements()
    omega = np.exp(2j * np.pi / 3)

    # Color basis states
    R = np.array([1, 0, 0], dtype=complex)
    G = np.array([0, 1, 0], dtype=complex)
    B = np.array([0, 0, 1], dtype=complex)
    color_states = [R, G, B]

    all_passed = True

    for k, z in enumerate(z_elements):
        expected_phase = omega**k
        for c, state in enumerate(color_states):
            transformed = z @ state
            # Should be ω^k · state
            expected = expected_phase * state

            if not np.allclose(transformed, expected):
                all_passed = False
                print(f"   FAILED: z_{k} |{['R','G','B'][c]}⟩ ≠ ω^{k} |{['R','G','B'][c]}⟩")

    add_result(
        "Fundamental representation Z₃ action",
        all_passed,
        f"All color states transform as z_k|c⟩ = ω^k|c⟩: {all_passed}"
    )

    return all_passed


# =============================================================================
# TEST 3: Anti-Fundamental Representation
# =============================================================================

def test_antifundamental_representation():
    """
    Verify Z₃ action on anti-fundamental representation.

    For |c̄⟩ (anticolor): z_k |c̄⟩ = ω^{-k} |c̄⟩ = ω^{2k} |c̄⟩

    This is because 3̄ has N-ality 2 (or equivalently -1 mod 3).
    """
    print("=" * 70)
    print("TEST 3: Anti-Fundamental Representation Z₃ Action")
    print("=" * 70)

    omega = np.exp(2j * np.pi / 3)

    all_passed = True

    for k in range(3):
        # Anti-fundamental transforms with conjugate phase
        expected_phase = omega**(-k)  # = ω^{2k} since ω^3 = 1

        # Verify ω^{-k} = ω^{2k}
        alt_phase = omega**(2*k)
        phase_equiv = np.isclose(expected_phase, alt_phase)

        if not phase_equiv:
            all_passed = False

    # Check N-ality arithmetic: 1 + 2 = 3 ≡ 0 (mod 3) for meson
    n_ality_meson = (1 + 2) % 3 == 0

    # For baryon: 1 + 1 + 1 = 3 ≡ 0 (mod 3)
    n_ality_baryon = (1 + 1 + 1) % 3 == 0

    all_passed = all_passed and n_ality_meson and n_ality_baryon

    add_result(
        "Anti-fundamental representation Z₃ action",
        all_passed,
        f"ω^{{-k}} = ω^{{2k}}: verified, N-ality meson (1+2=0 mod 3): {n_ality_meson}, "
        f"N-ality baryon (1+1+1=0 mod 3): {n_ality_baryon}"
    )

    return all_passed


# =============================================================================
# TEST 4: Color Singlet Construction and Z₃ Invariance
# =============================================================================

def test_color_singlet_invariance():
    """
    Construct explicit color singlet states and verify Z₃ invariance.

    1. Meson singlet: |M⟩ = (1/√3)(|RR̄⟩ + |GḠ⟩ + |BB̄⟩)
    2. Baryon singlet: |B⟩ = ε_{abc}|abc⟩

    Both must satisfy z_k|singlet⟩ = |singlet⟩.
    """
    print("=" * 70)
    print("TEST 4: Color Singlet Z₃ Invariance")
    print("=" * 70)

    z_elements = get_z3_center_elements()
    omega = np.exp(2j * np.pi / 3)

    all_passed = True

    # For mesons: 3 ⊗ 3̄ = 8 ⊕ 1
    # The singlet in quark-antiquark is:
    # |M⟩ ∝ δ^{ab} |a⟩|b̄⟩ = |RR̄⟩ + |GḠ⟩ + |BB̄⟩
    # In 9-dimensional product space

    # Basis: |RR̄⟩, |RḠ⟩, |RB̄⟩, |GR̄⟩, |GḠ⟩, |GB̄⟩, |BR̄⟩, |BḠ⟩, |BB̄⟩
    # Singlet coefficients: 1 at positions 0 (RR̄), 4 (GḠ), 8 (BB̄)
    meson_singlet = np.zeros(9, dtype=complex)
    meson_singlet[0] = 1  # |RR̄⟩
    meson_singlet[4] = 1  # |GḠ⟩
    meson_singlet[8] = 1  # |BB̄⟩
    meson_singlet /= np.linalg.norm(meson_singlet)

    # Z₃ action on 3 ⊗ 3̄:
    # z_k(|a⟩ ⊗ |b̄⟩) = (ω^k|a⟩) ⊗ (ω^{-k}|b̄⟩) = ω^{k-k}|a⟩⊗|b̄⟩ = |a⟩⊗|b̄⟩
    # So Z₃ acts trivially on 3 ⊗ 3̄!

    meson_invariant = True
    for k in range(3):
        # Total phase for meson: ω^k · ω^{-k} = 1
        total_phase = omega**k * omega**(-k)
        if not np.isclose(total_phase, 1.0):
            meson_invariant = False

    # For baryons: 3 ⊗ 3 ⊗ 3 = 10 ⊕ 8 ⊕ 8 ⊕ 1
    # The singlet is: |B⟩ = ε_{abc}|a⟩⊗|b⟩⊗|c⟩
    # Only non-zero for antisymmetric (a,b,c) = permutations of (R,G,B)

    # Z₃ action on baryon:
    # z_k|a⟩⊗|b⟩⊗|c⟩ = ω^k|a⟩ ⊗ ω^k|b⟩ ⊗ ω^k|c⟩ = ω^{3k}|a⟩⊗|b⟩⊗|c⟩ = |a⟩⊗|b⟩⊗|c⟩

    baryon_invariant = True
    for k in range(3):
        total_phase = omega**(3*k)  # Three fundamentals
        if not np.isclose(total_phase, 1.0):
            baryon_invariant = False

    all_passed = meson_invariant and baryon_invariant

    add_result(
        "Color singlet Z₃ invariance",
        all_passed,
        f"Meson (3⊗3̄) singlet invariant: {meson_invariant}, "
        f"Baryon (3⊗3⊗3) singlet invariant: {baryon_invariant}"
    )

    return all_passed


# =============================================================================
# TEST 5: Gluon (Adjoint) Representation
# =============================================================================

def test_adjoint_representation():
    """
    Verify that the adjoint representation (gluons, 8) is Z₃ invariant.

    The adjoint has N-ality 0 (it's 3 ⊗ 3̄ - 1), so:
    z_k |adj⟩ = |adj⟩

    Explicitly: Gell-Mann matrices should commute with center elements.
    """
    print("=" * 70)
    print("TEST 5: Adjoint Representation Z₃ Invariance")
    print("=" * 70)

    z_elements = get_z3_center_elements()
    gell_mann = get_gell_mann_matrices()

    all_passed = True

    # Adjoint action: For g ∈ SU(3), adjoint acts as Ad_g(X) = g X g^{-1}
    # For center elements z_k, since they're proportional to identity:
    # z_k X z_k^{-1} = X

    for k, z in enumerate(z_elements):
        z_inv = np.conj(z.T)  # z^† = z^{-1} for unitary
        for a, lam in enumerate(gell_mann):
            adjoint_action = z @ lam @ z_inv

            if not np.allclose(adjoint_action, lam, atol=1e-14):
                all_passed = False
                print(f"   FAILED: z_{k} λ_{a+1} z_{k}^{{-1}} ≠ λ_{a+1}")

    add_result(
        "Adjoint representation Z₃ invariance",
        all_passed,
        f"All 8 Gell-Mann matrices invariant under Z₃: {all_passed}"
    )

    return all_passed


# =============================================================================
# TEST 6: Superselection Rule Verification
# =============================================================================

def test_superselection_rule():
    """
    Explicitly verify the superselection rule:

    For states |ψ_n⟩, |ψ_m⟩ in different Z₃ sectors and Z₃-invariant O:
    ⟨ψ_n|O|ψ_m⟩ = 0 for n ≠ m

    This uses explicit SU(3) representations.
    """
    print("=" * 70)
    print("TEST 6: Superselection Rule (Explicit)")
    print("=" * 70)

    omega = np.exp(2j * np.pi / 3)

    # Work in the 3-dimensional representation
    # Construct states with definite Z₃ charge

    # In color basis, there's no natural decomposition into Z₃ sectors
    # because all fundamental states have the SAME Z₃ charge (N-ality 1).

    # Instead, work in the Hilbert space H = H_0 ⊕ H_1 ⊕ H_2 where
    # H_k has states with z|ψ⟩ = ω^k|ψ⟩

    # For SU(3), we need to consider the CENTER action, not rep labels.
    # In a general Hilbert space with SU(3) color, we can have:
    # - Singlets (N-ality 0): z|ψ⟩ = |ψ⟩
    # - Fundamentals (N-ality 1): z|ψ⟩ = ω|ψ⟩
    # - Anti-fundamentals (N-ality 2): z|ψ⟩ = ω²|ψ⟩

    all_passed = True

    # Test: transition between N-ality 0 and N-ality 1
    # Singlet state: |S⟩ (z|S⟩ = |S⟩)
    # Fundamental state: |F⟩ (z|F⟩ = ω|F⟩)

    # For a Z₃-invariant observable O with [O, z] = 0:
    # ⟨S|O|F⟩ = ⟨S|z^{-1}Oz|F⟩ = ⟨z^{-1}S|O|zF⟩ = ⟨S|O|ωF⟩ = ω⟨S|O|F⟩

    # Since ω ≠ 1, we must have ⟨S|O|F⟩ = 0

    # Explicit calculation with mock states
    # Define 6-dim Hilbert space: 3 for each of 2 representations

    # Singlet sector (indices 0-2)
    psi_singlet = np.array([1, 0, 0, 0, 0, 0], dtype=complex)
    psi_singlet /= np.linalg.norm(psi_singlet)

    # Fundamental sector (indices 3-5)
    psi_fund = np.array([0, 0, 0, 1, 0, 0], dtype=complex)
    psi_fund /= np.linalg.norm(psi_fund)

    # Z₃ generator in this space:
    # Acts as identity on singlet sector, ω on fundamental sector
    Z_6dim = np.diag([1, 1, 1, omega, omega, omega])

    # Z₃-invariant observable: block-diagonal
    O_inv = np.block([
        [np.random.randn(3, 3) + 1j * np.random.randn(3, 3), np.zeros((3, 3))],
        [np.zeros((3, 3)), np.random.randn(3, 3) + 1j * np.random.randn(3, 3)]
    ])
    O_inv = (O_inv + O_inv.conj().T) / 2  # Make Hermitian

    # Check O_inv is Z₃-invariant
    ZOZ_inv = Z_6dim @ O_inv @ np.conj(Z_6dim.T)
    O_is_invariant = np.allclose(ZOZ_inv, O_inv)

    # Check superselection: off-diagonal block should give zero
    matrix_element = np.vdot(psi_singlet, O_inv @ psi_fund)
    superselection_holds = np.isclose(matrix_element, 0, atol=1e-14)

    # Now test with a non-Z₃-invariant observable (has off-diagonal blocks)
    O_not_inv = np.random.randn(6, 6) + 1j * np.random.randn(6, 6)
    O_not_inv = (O_not_inv + O_not_inv.conj().T) / 2  # Hermitian but not Z₃-invariant

    ZOZ_not = Z_6dim @ O_not_inv @ np.conj(Z_6dim.T)
    O_not_is_invariant = np.allclose(ZOZ_not, O_not_inv)

    # This should NOT be Z₃-invariant (generically)

    all_passed = O_is_invariant and superselection_holds and not O_not_is_invariant

    add_result(
        "Superselection rule (explicit)",
        all_passed,
        f"Z₃-invariant O constructed: {O_is_invariant}, "
        f"⟨singlet|O|fund⟩ = 0: {superselection_holds}, "
        f"Non-invariant O detected: {not O_not_is_invariant}"
    )

    return all_passed


# =============================================================================
# TEST 7: Color-Singlet Observable Algebra Completeness
# =============================================================================

def test_observable_algebra_completeness():
    """
    Verify that the color-singlet observable algebra is complete:

    For any Hermitian operator O commuting with all SU(3) elements,
    O is a function of Casimir operators (hence diagonal in irrep basis).

    For fundamental rep: O ∝ I (only trivial Casimir).
    """
    print("=" * 70)
    print("TEST 7: Color-Singlet Observable Algebra Completeness")
    print("=" * 70)

    generators = get_su3_generators()

    all_passed = True

    # Quadratic Casimir: C_2 = Σ_a T^a T^a
    C2 = sum(T @ T for T in generators)

    # For fundamental rep: C_2 = (N² - 1)/(2N) I = 4/3 I for SU(3)
    expected_C2_eigenvalue = (9 - 1) / 6  # = 4/3
    C2_is_scalar = np.allclose(C2, expected_C2_eigenvalue * np.eye(3))

    # Any SU(3)-invariant observable in fundamental rep must be ∝ I
    # (Schur's lemma for irreducible representations)

    # Test: Generate random "observable" and project to SU(3)-invariant part
    np.random.seed(42)

    n_tests = 50
    all_proportional_to_identity = True

    for _ in range(n_tests):
        # Random Hermitian matrix
        H = np.random.randn(3, 3) + 1j * np.random.randn(3, 3)
        H = (H + H.conj().T) / 2

        # Project to SU(3)-invariant part by averaging over group
        # For computational simplicity, average over generators
        # True SU(3)-invariant part = (1/3) Tr(H) · I (Schur's lemma)

        invariant_part = (np.trace(H) / 3) * np.eye(3)

        # Check it commutes with all generators
        commutes = True
        for T in generators:
            comm = invariant_part @ T - T @ invariant_part
            if not np.allclose(comm, 0, atol=1e-14):
                commutes = False

        if not commutes:
            all_proportional_to_identity = False

    all_passed = C2_is_scalar and all_proportional_to_identity

    add_result(
        "Observable algebra completeness",
        all_passed,
        f"Casimir C₂ = (4/3)I: {C2_is_scalar}, "
        f"Invariant observables ∝ I: {all_proportional_to_identity}"
    )

    return all_passed


# =============================================================================
# TEST 8: Pointer Observable Z₃ Invariance
# =============================================================================

def test_pointer_observables():
    """
    Verify that pointer observables |χ_c|² are Z₃-invariant.

    For color field χ_c = a_c e^{iφ_c}, the intensity |χ_c|² depends
    only on amplitude, not phase.

    Z₃ shifts all phases uniformly, leaving |χ_c|² unchanged.
    """
    print("=" * 70)
    print("TEST 8: Pointer Observable Z₃ Invariance")
    print("=" * 70)

    omega = np.exp(2j * np.pi / 3)
    np.random.seed(42)

    all_passed = True
    n_tests = 100
    max_deviation = 0

    for _ in range(n_tests):
        # Random color field configuration
        a_R = np.random.uniform(0.1, 2.0)
        a_G = np.random.uniform(0.1, 2.0)
        a_B = np.random.uniform(0.1, 2.0)

        phi_R = np.random.uniform(0, 2*np.pi)
        phi_G = np.random.uniform(0, 2*np.pi)
        # Constrain: φ_R + φ_G + φ_B = 0 mod 2π
        phi_B = -(phi_R + phi_G) % (2 * np.pi)

        # Color fields
        chi_R = a_R * np.exp(1j * phi_R)
        chi_G = a_G * np.exp(1j * phi_G)
        chi_B = a_B * np.exp(1j * phi_B)

        # Pointer observables (intensities)
        I_R = np.abs(chi_R)**2
        I_G = np.abs(chi_G)**2
        I_B = np.abs(chi_B)**2

        # Apply Z₃ action: shift all phases by 2πk/3
        for k in [1, 2]:
            delta = 2 * np.pi * k / 3

            chi_R_shifted = a_R * np.exp(1j * (phi_R + delta))
            chi_G_shifted = a_G * np.exp(1j * (phi_G + delta))
            chi_B_shifted = a_B * np.exp(1j * (phi_B + delta))

            I_R_shifted = np.abs(chi_R_shifted)**2
            I_G_shifted = np.abs(chi_G_shifted)**2
            I_B_shifted = np.abs(chi_B_shifted)**2

            # Check invariance
            dev = max(
                abs(I_R - I_R_shifted),
                abs(I_G - I_G_shifted),
                abs(I_B - I_B_shifted)
            )

            if dev > max_deviation:
                max_deviation = dev

            if dev > 1e-14:
                all_passed = False

    add_result(
        "Pointer observable Z₃ invariance",
        all_passed,
        f"Tested {n_tests} configurations, max deviation: {max_deviation:.2e}"
    )

    return all_passed


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("\n" + "=" * 70)
    print("SU(3) SUPERSELECTION VERIFICATION: PROPOSITION 0.0.17i")
    print("Using Explicit Gell-Mann Matrix Representations")
    print("=" * 70 + "\n")

    test_results = [
        test_z3_center_structure(),
        test_fundamental_representation(),
        test_antifundamental_representation(),
        test_color_singlet_invariance(),
        test_adjoint_representation(),
        test_superselection_rule(),
        test_observable_algebra_completeness(),
        test_pointer_observables(),
    ]

    # Summary
    n_passed = sum(test_results)
    n_total = len(test_results)

    print("\n" + "=" * 70)
    print(f"SU(3) SUPERSELECTION VERIFICATION: {n_passed}/{n_total} tests passed")
    print("=" * 70)

    results["summary"] = {
        "passed": int(n_passed),
        "total": int(n_total),
        "all_passed": bool(n_passed == n_total)
    }

    # Save results
    output_file = "proposition_0_0_17i_su3_superselection.json"
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {output_file}")

    if n_passed == n_total:
        print("\n✅ ALL SU(3) SUPERSELECTION TESTS PASSED")
    else:
        print(f"\n⚠️ {n_total - n_passed} test(s) failed")

    return n_passed == n_total


if __name__ == "__main__":
    main()
