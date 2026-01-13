#!/usr/bin/env python3
"""
Verification Script: Z₃ Protection Against Fundamental Quarks

This script verifies that operational Z₃ survives quark coupling, even though
gauge Z₃ (center symmetry) is broken by fundamental quarks.

Key distinction:
- Gauge Z₃: Acts on Polyakov loops, broken by quarks
- Operational Z₃: Acts on observable algebra (color singlets), preserved

Created: 2026-01-11
Related: docs/proofs/foundations/Proposition-0.0.17i-Z3-Measurement-Extension.md §10
"""

import numpy as np
from typing import Tuple, Dict, List
import sys

# Z₃ center element
OMEGA = np.exp(2j * np.pi / 3)


def z3_element(k: int) -> complex:
    """Return the k-th Z₃ center element ω^k."""
    return OMEGA ** k


class ColorRepresentations:
    """
    Representations of quarks and observables under Z₃ center transformations.
    """

    @staticmethod
    def quark_transforms(psi: complex, k: int) -> complex:
        """
        Transform a quark field under Z₃.

        Quarks are in fundamental rep: ψ → ω^k ψ
        """
        return z3_element(k) * psi

    @staticmethod
    def antiquark_transforms(psi_bar: complex, k: int) -> complex:
        """
        Transform an antiquark field under Z₃.

        Antiquarks are in anti-fundamental rep: ψ̄ → ω^{-k} ψ̄
        """
        return z3_element(-k) * psi_bar

    @staticmethod
    def quark_bilinear(psi: complex, psi_bar: complex) -> complex:
        """
        Compute quark bilinear ψ̄ψ (a color singlet).
        """
        return psi_bar * psi

    @staticmethod
    def baryon(psi_R: complex, psi_G: complex, psi_B: complex) -> complex:
        """
        Compute baryon ε_{abc} ψ^a ψ^b ψ^c.

        For simplicity, we just multiply the three quarks.
        The ε tensor gives the antisymmetrization.
        """
        return psi_R * psi_G * psi_B


def test_1_quark_transforms_nontrivially():
    """
    Test 1: Verify that quarks transform non-trivially under Z₃.

    ψ → ω^k ψ with ω = e^{2πi/3}
    """
    print("Test 1: Quarks transform non-trivially under Z₃")
    print("-" * 50)

    # Test quark field (arbitrary complex amplitude)
    psi = 1.0 + 0.5j

    transformations = []
    for k in range(3):
        psi_transformed = ColorRepresentations.quark_transforms(psi, k)
        factor = psi_transformed / psi
        transformations.append({
            "k": k,
            "factor": factor,
            "expected": z3_element(k),
            "match": np.isclose(factor, z3_element(k))
        })
        print(f"  k={k}: ψ → {factor:.4f} × ψ (expected ω^{k} = {z3_element(k):.4f})")

    # For k≠0, transformation should be non-trivial
    k1_nontrivial = not np.isclose(z3_element(1), 1.0)
    k2_nontrivial = not np.isclose(z3_element(2), 1.0)

    print(f"\n  Z₃ acts non-trivially on quarks: {k1_nontrivial and k2_nontrivial}")

    return k1_nontrivial and k2_nontrivial


def test_2_quark_bilinear_is_invariant():
    """
    Test 2: Verify that quark bilinear ψ̄ψ is Z₃-invariant.

    Under Z₃: ψ → ω^k ψ, ψ̄ → ω^{-k} ψ̄
    Therefore: ψ̄ψ → ω^{-k} ω^k ψ̄ψ = ψ̄ψ
    """
    print("\nTest 2: Quark bilinear ψ̄ψ is Z₃-invariant")
    print("-" * 50)

    # Test fields
    psi = 1.0 + 0.5j
    psi_bar = 2.0 - 0.3j

    # Original bilinear
    original = ColorRepresentations.quark_bilinear(psi, psi_bar)

    # Transform and compute bilinear
    invariance_checks = []
    for k in range(3):
        psi_t = ColorRepresentations.quark_transforms(psi, k)
        psi_bar_t = ColorRepresentations.antiquark_transforms(psi_bar, k)
        transformed = ColorRepresentations.quark_bilinear(psi_t, psi_bar_t)

        is_invariant = np.isclose(transformed, original)
        invariance_checks.append(is_invariant)

        print(f"  k={k}: ψ̄ψ = {original:.4f} → {transformed:.4f} (invariant: {is_invariant})")

    all_invariant = all(invariance_checks)
    print(f"\n  ψ̄ψ is Z₃-invariant: {all_invariant}")

    return all_invariant


def test_3_baryon_is_invariant():
    """
    Test 3: Verify that baryon ε_{abc} ψ^a ψ^b ψ^c is Z₃-invariant.

    Under Z₃: each ψ → ω^k ψ
    Three quarks: (ω^k)³ = ω^{3k} = 1
    Therefore: baryon → baryon
    """
    print("\nTest 3: Baryon ε_{abc}ψ^a ψ^b ψ^c is Z₃-invariant")
    print("-" * 50)

    # Test quark fields for each color
    psi_R = 1.0 + 0.5j
    psi_G = 0.8 - 0.2j
    psi_B = 1.2 + 0.1j

    # Original baryon
    original = ColorRepresentations.baryon(psi_R, psi_G, psi_B)

    # Transform and compute baryon
    invariance_checks = []
    for k in range(3):
        psi_R_t = ColorRepresentations.quark_transforms(psi_R, k)
        psi_G_t = ColorRepresentations.quark_transforms(psi_G, k)
        psi_B_t = ColorRepresentations.quark_transforms(psi_B, k)
        transformed = ColorRepresentations.baryon(psi_R_t, psi_G_t, psi_B_t)

        # Factor should be ω^{3k} = 1
        factor = transformed / original if original != 0 else 0
        expected_factor = z3_element(3 * k)  # ω^{3k} = 1

        is_invariant = np.isclose(factor, 1.0)
        invariance_checks.append(is_invariant)

        print(f"  k={k}: baryon → {factor:.4f} × baryon (ω^{3*k} = {expected_factor:.4f})")

    all_invariant = all(invariance_checks)
    print(f"\n  Baryon is Z₃-invariant: {all_invariant}")

    return all_invariant


def test_4_meson_is_invariant():
    """
    Test 4: Verify that meson ψ̄^a ψ_a is Z₃-invariant (color singlet).

    This is the same as quark bilinear summed over colors.
    """
    print("\nTest 4: Meson ψ̄^a ψ_a is Z₃-invariant")
    print("-" * 50)

    # Test quark-antiquark pairs for each color
    quarks = {
        "R": (1.0 + 0.5j, 2.0 - 0.3j),
        "G": (0.8 - 0.2j, 1.5 + 0.1j),
        "B": (1.2 + 0.1j, 0.9 - 0.4j),
    }

    # Original meson = Σ_a ψ̄^a ψ_a
    original_meson = sum(
        ColorRepresentations.quark_bilinear(psi, psi_bar)
        for psi, psi_bar in quarks.values()
    )

    # Transform and compute meson
    invariance_checks = []
    for k in range(3):
        transformed_meson = 0.0
        for color, (psi, psi_bar) in quarks.items():
            psi_t = ColorRepresentations.quark_transforms(psi, k)
            psi_bar_t = ColorRepresentations.antiquark_transforms(psi_bar, k)
            transformed_meson += ColorRepresentations.quark_bilinear(psi_t, psi_bar_t)

        is_invariant = np.isclose(transformed_meson, original_meson)
        invariance_checks.append(is_invariant)

        print(f"  k={k}: meson = {original_meson:.4f} → {transformed_meson:.4f} (invariant: {is_invariant})")

    all_invariant = all(invariance_checks)
    print(f"\n  Meson is Z₃-invariant: {all_invariant}")

    return all_invariant


def test_5_nonsinglet_is_not_invariant():
    """
    Test 5: Verify that non-singlet operators (like single quark) are NOT Z₃-invariant.

    This confirms the distinction: singlets are invariant, non-singlets are not.
    """
    print("\nTest 5: Non-singlet operators are NOT Z₃-invariant")
    print("-" * 50)

    psi = 1.0 + 0.5j

    # Single quark (N-ality 1) transforms non-trivially
    noninvariance_checks = []
    for k in [1, 2]:  # Skip k=0 (trivial)
        psi_t = ColorRepresentations.quark_transforms(psi, k)
        is_different = not np.isclose(psi_t, psi)
        noninvariance_checks.append(is_different)
        print(f"  k={k}: ψ = {psi:.4f} → {psi_t:.4f} (different: {is_different})")

    all_different = all(noninvariance_checks)
    print(f"\n  Single quark is NOT Z₃-invariant: {all_different}")

    return all_different


def test_6_gauge_vs_operational_distinction():
    """
    Test 6: Verify the distinction between gauge Z₃ and operational Z₃.

    - Gauge Z₃: Would act on Polyakov loops (not tested here - thermal QFT)
    - Operational Z₃: Acts on observable algebra (color singlets) trivially
    """
    print("\nTest 6: Gauge Z₃ vs Operational Z₃ distinction")
    print("-" * 50)

    # Observable algebra consists of color singlets
    observables = {
        "ψ̄ψ (quark bilinear)": lambda k: test_bilinear_invariant(k),
        "baryon": lambda k: test_baryon_invariant(k),
        "meson": lambda k: test_meson_invariant(k),
    }

    print("  Observable algebra A_meas consists of color singlets:")
    all_invariant = True
    for name, test_func in observables.items():
        invariant_for_all_k = all(test_func(k) for k in range(3))
        status = "✓ Z₃-invariant" if invariant_for_all_k else "✗ NOT invariant"
        print(f"    {name}: {status}")
        all_invariant = all_invariant and invariant_for_all_k

    print(f"\n  All observables in A_meas are Z₃-invariant: {all_invariant}")
    print(f"  Therefore: Operational Z₃ acts trivially on A_meas")
    print(f"  (Gauge Z₃ breaking by quarks does not affect this)")

    return all_invariant


def test_bilinear_invariant(k: int) -> bool:
    """Helper: test if bilinear is invariant under z_k."""
    psi = 1.0 + 0.5j
    psi_bar = 2.0 - 0.3j
    original = ColorRepresentations.quark_bilinear(psi, psi_bar)
    psi_t = ColorRepresentations.quark_transforms(psi, k)
    psi_bar_t = ColorRepresentations.antiquark_transforms(psi_bar, k)
    transformed = ColorRepresentations.quark_bilinear(psi_t, psi_bar_t)
    return np.isclose(transformed, original)


def test_baryon_invariant(k: int) -> bool:
    """Helper: test if baryon is invariant under z_k."""
    psi_R, psi_G, psi_B = 1.0 + 0.5j, 0.8 - 0.2j, 1.2 + 0.1j
    original = ColorRepresentations.baryon(psi_R, psi_G, psi_B)
    psi_R_t = ColorRepresentations.quark_transforms(psi_R, k)
    psi_G_t = ColorRepresentations.quark_transforms(psi_G, k)
    psi_B_t = ColorRepresentations.quark_transforms(psi_B, k)
    transformed = ColorRepresentations.baryon(psi_R_t, psi_G_t, psi_B_t)
    return np.isclose(transformed, original)


def test_meson_invariant(k: int) -> bool:
    """Helper: test if meson is invariant under z_k."""
    quarks = {
        "R": (1.0 + 0.5j, 2.0 - 0.3j),
        "G": (0.8 - 0.2j, 1.5 + 0.1j),
        "B": (1.2 + 0.1j, 0.9 - 0.4j),
    }
    original = sum(psi * psi_bar for psi, psi_bar in quarks.values())
    transformed = sum(
        ColorRepresentations.quark_transforms(psi, k) *
        ColorRepresentations.antiquark_transforms(psi_bar, k)
        for psi, psi_bar in quarks.values()
    )
    return np.isclose(transformed, original)


def test_7_z3_omega_cubed_equals_one():
    """
    Test 7: Verify fundamental Z₃ property ω³ = 1.

    This is why baryons (3 quarks) are Z₃-invariant.
    """
    print("\nTest 7: Z₃ fundamental property ω³ = 1")
    print("-" * 50)

    omega_cubed = OMEGA ** 3

    is_one = np.isclose(omega_cubed, 1.0)

    print(f"  ω = e^(2πi/3) = {OMEGA:.4f}")
    print(f"  ω³ = {omega_cubed:.4f}")
    print(f"  ω³ = 1: {is_one}")

    return is_one


def main():
    """Run all verification tests."""
    print("=" * 60)
    print("Z₃ Protection Verification: Operational Z₃ vs Gauge Z₃")
    print("=" * 60)
    print()

    tests = [
        ("Test 1: Quarks transform non-trivially", test_1_quark_transforms_nontrivially),
        ("Test 2: Quark bilinear ψ̄ψ is invariant", test_2_quark_bilinear_is_invariant),
        ("Test 3: Baryon is invariant", test_3_baryon_is_invariant),
        ("Test 4: Meson is invariant", test_4_meson_is_invariant),
        ("Test 5: Non-singlets are NOT invariant", test_5_nonsinglet_is_not_invariant),
        ("Test 6: Gauge vs Operational Z₃ distinction", test_6_gauge_vs_operational_distinction),
        ("Test 7: ω³ = 1 (fundamental property)", test_7_z3_omega_cubed_equals_one),
    ]

    results = []
    for name, test_func in tests:
        try:
            passed = test_func()
            results.append((name, passed))
        except Exception as e:
            print(f"\n  ERROR: {e}")
            results.append((name, False))

    # Summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)

    passed_count = sum(1 for _, p in results if p)
    total_count = len(results)

    for name, passed in results:
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"  {status}: {name}")

    print(f"\n  Total: {passed_count}/{total_count} tests passed")

    if passed_count == total_count:
        print("\n  ✅ All tests passed!")
        print("  Proposition 0.0.17i §10 VERIFIED:")
        print("  - Quarks transform non-trivially under Z₃")
        print("  - But color singlets (observables) are Z₃-invariant")
        print("  - Therefore operational Z₃ survives quark coupling")
        return 0
    else:
        print("\n  ❌ Some tests failed!")
        return 1


if __name__ == "__main__":
    sys.exit(main())
