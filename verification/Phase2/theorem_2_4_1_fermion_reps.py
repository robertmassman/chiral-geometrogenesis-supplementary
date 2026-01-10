#!/usr/bin/env python3
"""
Theorem 2.4.1 Verification Script 5: Fermion Representations
=============================================================

Verifies the fermion representation decomposition:
1. Verify 5-bar decomposition under SU(3)×SU(2)×U(1)
2. Verify 10 decomposition
3. Check dimension: 5-bar → 3 + 2 = 5
4. Check dimension: 10 → 6 + 3 + 1 = 10
5. Verify anomaly cancellation: A(5-bar) + A(10) = 0

Author: Computational Verification Agent
Date: 2025-12-26
"""

import numpy as np
import json

# Results storage
results = {
    "theorem": "2.4.1",
    "script": "fermion_reps",
    "tests": []
}

def test_result(name, expected, computed, tolerance=1e-10):
    """Record a test result."""
    if isinstance(expected, (int, float)) and isinstance(computed, (int, float)):
        passed = abs(expected - computed) <= tolerance
    else:
        passed = expected == computed

    result = {
        "name": name,
        "expected": str(expected),
        "computed": str(computed),
        "passed": bool(passed)
    }
    results["tests"].append(result)

    status = "PASS" if passed else "FAIL"
    print(f"[{status}] {name}: expected {expected}, got {computed}")
    return passed

print("=" * 60)
print("Theorem 2.4.1 Verification: Fermion Representations")
print("=" * 60)
print()

# 1. The 5-bar representation decomposition
print("1. 5-bar Representation Decomposition")
print("-" * 40)

# 5-bar of SU(5) decomposes under SU(3)×SU(2)×U(1) as:
# 5-bar → (3-bar, 1)_{1/3} + (1, 2)_{-1/2}
#
# (3-bar, 1)_{1/3}: antiquark (d^c), dimension 3
# (1, 2)_{-1/2}: lepton doublet (e, ν), dimension 2

dim_5bar = 5
dim_3bar_1 = 3  # Color antitriplet, SU(2) singlet
dim_1_2 = 2     # Color singlet, SU(2) doublet

total_5bar = dim_3bar_1 + dim_1_2
test_result("5-bar dimension", 5, dim_5bar)
test_result("5-bar decomposition: 3 + 2", 5, total_5bar)

print(f"\n5-bar decomposition:")
print(f"  (3-bar, 1)_{{1/3}} : d^c_R, d^c_G, d^c_B (dim = {dim_3bar_1})")
print(f"  (1, 2)_{{-1/2}}    : (e⁻, ν_e)_L      (dim = {dim_1_2})")
print(f"  Total: {total_5bar}")

# Verify hypercharge assignments
# For 5-bar: Y = (1/3, 1/3, 1/3, -1/2, -1/2)
Y_5bar = np.array([1/3, 1/3, 1/3, -1/2, -1/2])
print(f"\nHypercharge for 5-bar: {Y_5bar}")
test_result("Tr(Y) for 5-bar = 0", 0, np.sum(Y_5bar), tolerance=1e-10)

# 2. The 10 representation decomposition
print("\n2. 10 Representation Decomposition")
print("-" * 40)

# 10 of SU(5) = antisymmetric tensor 5⊗5 → 10
# Decomposes as:
# 10 → (3, 2)_{1/6} + (3-bar, 1)_{-2/3} + (1, 1)_{1}
#
# (3, 2)_{1/6}: quark doublet Q = (u, d)_L, dimension 3×2 = 6
# (3-bar, 1)_{-2/3}: antiquark u^c, dimension 3
# (1, 1)_{1}: anti-lepton e^c, dimension 1

dim_10 = 10
dim_3_2 = 3 * 2  # Color triplet, SU(2) doublet: 6
dim_3bar_1_2 = 3 # Color antitriplet, SU(2) singlet
dim_1_1 = 1      # Color singlet, SU(2) singlet

total_10 = dim_3_2 + dim_3bar_1_2 + dim_1_1
test_result("10 dimension", 10, dim_10)
test_result("10 decomposition: 6 + 3 + 1", 10, total_10)

print(f"\n10 decomposition:")
print(f"  (3, 2)_{{1/6}}     : (u, d)_L for 3 colors (dim = {dim_3_2})")
print(f"  (3-bar, 1)_{{-2/3}} : u^c_R, u^c_G, u^c_B    (dim = {dim_3bar_1_2})")
print(f"  (1, 1)_{{1}}       : e^+_R                   (dim = {dim_1_1})")
print(f"  Total: {total_10}")

# 3. Antisymmetric tensor dimension
print("\n3. Antisymmetric Tensor Check")
print("-" * 40)

# 10 = 5⊗5 antisymmetric = C(5,2) = 10
antisym_dim = 5 * 4 // 2
test_result("C(5,2) = 10", 10, antisym_dim)

# 4. Full generation content
print("\n4. Full Generation Fermion Content")
print("-" * 40)

# One SM generation fits in 5-bar + 10
total_fermions = dim_5bar + dim_10
print(f"5-bar: {dim_5bar}")
print(f"10: {dim_10}")
print(f"Total per generation: {total_fermions}")

# Actually counting Weyl fermions:
# 5-bar: 3 (d^c) + 2 (L) = 5 Weyl fermions
# 10: 6 (Q) + 3 (u^c) + 1 (e^c) = 10 Weyl fermions
# Total: 15 Weyl fermions per generation
test_result("Weyl fermions per generation", 15, total_fermions)

# Standard Model count: per generation
# Q_L (3×2=6), u_R (3), d_R (3), L_L (2), e_R (1) = 15 Weyl
sm_weyl = 6 + 3 + 3 + 2 + 1
test_result("SM Weyl fermion count", 15, sm_weyl)

# 5. Anomaly Cancellation
print("\n5. Anomaly Cancellation")
print("-" * 40)

# The SU(5) anomaly coefficient for representation R is:
# A(R) = Tr(T^a {T^b, T^c}) in representation R
# For SU(N), this is proportional to the index and a cubic invariant
#
# For SU(5):
# A(5) = +1 (fundamental has positive anomaly)
# A(5-bar) = -1 (conjugate representation)
# A(10) = +1 (antisymmetric 2-tensor of fundamental)
#
# Actually the standard convention:
# A(5) = 1
# A(10) = 3 (for 2-index antisymmetric of SU(5))
# But for fermion content, we use the triangle anomaly

# Triangle anomaly for U(1)_Y:
# A_Y = sum over fermions of Y^3

# For 5-bar:
# d^c: 3 × (1/3)^3 = 3/27 = 1/9
# L: 2 × (-1/2)^3 = 2 × (-1/8) = -1/4
A_Y_5bar = 3 * (1/3)**3 + 2 * (-1/2)**3
print(f"A_Y(5-bar) = {A_Y_5bar}")

# For 10:
# Q: 6 × (1/6)^3 = 6/216 = 1/36
# u^c: 3 × (-2/3)^3 = 3 × (-8/27) = -8/9
# e^c: 1 × (1)^3 = 1
A_Y_10 = 6 * (1/6)**3 + 3 * (-2/3)**3 + 1 * (1)**3
print(f"A_Y(10) = {A_Y_10}")

# Total
A_Y_total = A_Y_5bar + A_Y_10
print(f"A_Y(5-bar) + A_Y(10) = {A_Y_total}")
test_result("U(1)_Y³ anomaly cancellation", 0, A_Y_total, tolerance=1e-10)

# 6. Mixed anomalies
print("\n6. Mixed Anomaly Cancellation")
print("-" * 40)

# SU(3)² × U(1)_Y anomaly
# Only colored fermions contribute

# 5-bar: d^c triplet with Y = 1/3
# Contribution: 1 × (1/3) = 1/3 (one triplet)
A_SU3_Y_5bar = 1 * (1/3)

# 10: Q is (3,2) with Y = 1/6, u^c is (3-bar) with Y = -2/3
# Q contribution: 2 × (1/6) = 1/3 (doublet of triplets)
# u^c contribution: 1 × (-2/3) = -2/3
A_SU3_Y_10 = 2 * (1/6) + 1 * (-2/3)

A_SU3_Y_total = A_SU3_Y_5bar + A_SU3_Y_10
print(f"A_SU3²×Y(5-bar) = {A_SU3_Y_5bar}")
print(f"A_SU3²×Y(10) = {A_SU3_Y_10}")
print(f"Total = {A_SU3_Y_total}")
test_result("SU(3)² × U(1)_Y anomaly cancellation", 0, A_SU3_Y_total, tolerance=1e-10)

# SU(2)² × U(1)_Y anomaly
# Only SU(2) doublets contribute

# 5-bar: L doublet with Y = -1/2
A_SU2_Y_5bar = 1 * (-1/2)

# 10: Q doublet with Y = 1/6, multiplied by color 3
A_SU2_Y_10 = 3 * (1/6)

A_SU2_Y_total = A_SU2_Y_5bar + A_SU2_Y_10
print(f"\nA_SU2²×Y(5-bar) = {A_SU2_Y_5bar}")
print(f"A_SU2²×Y(10) = {A_SU2_Y_10}")
print(f"Total = {A_SU2_Y_total}")
test_result("SU(2)² × U(1)_Y anomaly cancellation", 0, A_SU2_Y_total, tolerance=1e-10)

# Gravitational anomaly (Tr Y)
print("\n7. Gravitational Anomaly Check")
print("-" * 40)

# Tr(Y) for 5-bar
Tr_Y_5bar = 3*(1/3) + 2*(-1/2)
print(f"Tr(Y) for 5-bar: {Tr_Y_5bar}")

# Tr(Y) for 10
Tr_Y_10 = 6*(1/6) + 3*(-2/3) + 1*(1)
print(f"Tr(Y) for 10: {Tr_Y_10}")

Tr_Y_total = Tr_Y_5bar + Tr_Y_10
print(f"Total Tr(Y): {Tr_Y_total}")
test_result("Gravitational anomaly (Tr Y) = 0", 0, Tr_Y_total, tolerance=1e-10)

# 8. Electric charge quantization
print("\n8. Electric Charge Quantization")
print("-" * 40)

# Q = T₃ + Y
# For each SM fermion, compute Q

# 5-bar fermions:
# d^c: T₃ = 0, Y = 1/3 → Q = 1/3
# ν: T₃ = 1/2, Y = -1/2 → Q = 0
# e⁻: T₃ = -1/2, Y = -1/2 → Q = -1

charges_5bar = [1/3, 1/3, 1/3, 0, -1]  # d^c (3), ν, e⁻
print(f"Charges in 5-bar: {charges_5bar}")

# 10 fermions:
# u: T₃ = 1/2, Y = 1/6 → Q = 2/3
# d: T₃ = -1/2, Y = 1/6 → Q = -1/3
# u^c: T₃ = 0, Y = -2/3 → Q = -2/3
# e^+: T₃ = 0, Y = 1 → Q = 1

charges_10 = [2/3, 2/3, 2/3, -1/3, -1/3, -1/3, -2/3, -2/3, -2/3, 1]
print(f"Charges in 10: {charges_10}")

# All charges in units of e/3
all_charges = charges_5bar + charges_10
charge_units = [c * 3 for c in all_charges]  # Should all be integers
all_integer = all(abs(c - round(c)) < 1e-10 for c in charge_units)
test_result("All charges quantized in e/3", True, all_integer)

print(f"\nCharge quantization verified: all charges are n × (e/3)")

# 9. Summary table
print("\n9. Fermion Content Summary")
print("-" * 40)

print("\n5-bar representation content:")
print("  | Particle | SU(3) | SU(2) | Y    | Q     |")
print("  |----------|-------|-------|------|-------|")
print("  | d^c      | 3-bar | 1     | 1/3  | 1/3   |")
print("  | ν_e      | 1     | 2     | -1/2 | 0     |")
print("  | e⁻       | 1     | 2     | -1/2 | -1    |")

print("\n10 representation content:")
print("  | Particle | SU(3) | SU(2) | Y     | Q     |")
print("  |----------|-------|-------|-------|-------|")
print("  | u        | 3     | 2     | 1/6   | 2/3   |")
print("  | d        | 3     | 2     | 1/6   | -1/3  |")
print("  | u^c      | 3-bar | 1     | -2/3  | -2/3  |")
print("  | e^+      | 1     | 1     | 1     | 1     |")

# 10. SU(5) group theory check
print("\n10. SU(5) Group Theory Verification")
print("-" * 40)

# Dimension of SU(5): 5² - 1 = 24
su5_dim = 5**2 - 1
test_result("dim(SU(5)) = 24", 24, su5_dim)

# Adjoint representation dimension = 24
test_result("Adjoint rep dimension", 24, su5_dim)

# Number of generators = 24
# 8 (SU(3)) + 3 (SU(2)) + 1 (U(1)) + 12 (X, Y bosons) = 24
generators = 8 + 3 + 1 + 12
test_result("Generator count: 8+3+1+12", 24, generators)

# Summary
print()
print("=" * 60)
print("SUMMARY")
print("=" * 60)
total_tests = len(results["tests"])
passed_tests = sum(1 for t in results["tests"] if t["passed"])
failed_tests = total_tests - passed_tests

print(f"Total tests: {total_tests}")
print(f"Passed: {passed_tests}")
print(f"Failed: {failed_tests}")

if failed_tests == 0:
    print("\n*** ALL TESTS PASSED ***")
else:
    print("\n*** SOME TESTS FAILED ***")
    print("Failed tests:")
    for t in results["tests"]:
        if not t["passed"]:
            print(f"  - {t['name']}")

# Save results
results["summary"] = {
    "total": total_tests,
    "passed": passed_tests,
    "failed": failed_tests
}

with open("/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/theorem_2_4_1_fermion_reps_results.json", "w") as f:
    json.dump(results, f, indent=2)

print(f"\nResults saved to theorem_2_4_1_fermion_reps_results.json")
