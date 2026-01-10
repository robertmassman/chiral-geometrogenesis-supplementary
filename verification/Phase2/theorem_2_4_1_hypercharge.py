#!/usr/bin/env python3
"""
Theorem 2.4.1 Verification Script 6: Hypercharge Normalization
===============================================================

Verifies hypercharge properties:
1. Define Y = diag(-1/3, -1/3, -1/3, 1/2, 1/2)
2. Verify Tr(Y) = 0
3. Verify proper embedding in SU(5)
4. Check GUT normalization factor
5. Verify orthogonality to SU(3) and SU(2) generators

Author: Computational Verification Agent
Date: 2025-12-26
"""

import numpy as np
import matplotlib.pyplot as plt
import json

# Results storage
results = {
    "theorem": "2.4.1",
    "script": "hypercharge",
    "tests": []
}

def test_result(name, expected, computed, tolerance=1e-10):
    """Record a test result."""
    if isinstance(expected, (int, float)) and isinstance(computed, (int, float)):
        passed = abs(expected - computed) <= tolerance
    elif isinstance(expected, bool):
        passed = expected == computed
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

def gell_mann_matrices():
    """Return the 8 Gell-Mann matrices for SU(3)."""
    l1 = np.array([[0, 1, 0], [1, 0, 0], [0, 0, 0]], dtype=complex)
    l2 = np.array([[0, -1j, 0], [1j, 0, 0], [0, 0, 0]], dtype=complex)
    l3 = np.array([[1, 0, 0], [0, -1, 0], [0, 0, 0]], dtype=complex)
    l4 = np.array([[0, 0, 1], [0, 0, 0], [1, 0, 0]], dtype=complex)
    l5 = np.array([[0, 0, -1j], [0, 0, 0], [1j, 0, 0]], dtype=complex)
    l6 = np.array([[0, 0, 0], [0, 0, 1], [0, 1, 0]], dtype=complex)
    l7 = np.array([[0, 0, 0], [0, 0, -1j], [0, 1j, 0]], dtype=complex)
    l8 = np.array([[1, 0, 0], [0, 1, 0], [0, 0, -2]], dtype=complex) / np.sqrt(3)
    return [l1, l2, l3, l4, l5, l6, l7, l8]

def pauli_matrices():
    """Return the 3 Pauli matrices for SU(2)."""
    s1 = np.array([[0, 1], [1, 0]], dtype=complex)
    s2 = np.array([[0, -1j], [1j, 0]], dtype=complex)
    s3 = np.array([[1, 0], [0, -1]], dtype=complex)
    return [s1, s2, s3]

def embed_su3_in_su5(gell_mann):
    """Embed a 3×3 SU(3) generator in upper-left of 5×5 SU(5)."""
    embedded = np.zeros((5, 5), dtype=complex)
    embedded[:3, :3] = gell_mann
    return embedded

def embed_su2_in_su5(pauli):
    """Embed a 2×2 SU(2) generator in lower-right of 5×5 SU(5)."""
    embedded = np.zeros((5, 5), dtype=complex)
    embedded[3:, 3:] = pauli / 2  # Standard normalization T_a = σ_a/2
    return embedded

print("=" * 60)
print("Theorem 2.4.1 Verification: Hypercharge Normalization")
print("=" * 60)
print()

# 1. Hypercharge Definition
print("1. Hypercharge Generator Definition")
print("-" * 40)

# Hypercharge in SU(5) fundamental representation
# Y = diag(-1/3, -1/3, -1/3, 1/2, 1/2)
Y_diag = np.array([-1/3, -1/3, -1/3, 1/2, 1/2])
Y = np.diag(Y_diag)

print(f"Y diagonal elements: {Y_diag}")
print(f"Y matrix:\n{Y}")

# 2. Tracelessness
print("\n2. Tracelessness Verification")
print("-" * 40)

trace_Y = np.trace(Y)
print(f"Tr(Y) = {trace_Y}")

# Check: -1/3 - 1/3 - 1/3 + 1/2 + 1/2 = -1 + 1 = 0
manual_trace = -1/3 - 1/3 - 1/3 + 1/2 + 1/2
test_result("Tr(Y) = 0", 0, trace_Y, tolerance=1e-10)
test_result("Manual trace calculation", 0, manual_trace, tolerance=1e-10)

# 3. SU(5) embedding verification
print("\n3. SU(5) Embedding Verification")
print("-" * 40)

# Y must be hermitian
is_hermitian = np.allclose(Y, Y.conj().T)
test_result("Y is Hermitian", True, is_hermitian)

# Y must be traceless (already checked)

# Y must commute with SU(3) and SU(2) subgroup generators

# Get SU(3) generators embedded in SU(5)
gm = gell_mann_matrices()
su3_generators = [embed_su3_in_su5(g) for g in gm]

# Check that Y commutes with all SU(3) generators
print("\nChecking [Y, T_a^{SU(3)}] = 0:")
su3_commutes = True
for i, T in enumerate(su3_generators):
    comm = Y @ T - T @ Y
    if not np.allclose(comm, 0):
        su3_commutes = False
        print(f"  [Y, λ_{i+1}] ≠ 0")
    else:
        print(f"  [Y, λ_{i+1}] = 0 ✓")

test_result("Y commutes with SU(3)", True, su3_commutes)

# Get SU(2) generators embedded in SU(5)
pm = pauli_matrices()
su2_generators = [embed_su2_in_su5(p) for p in pm]

# Check that Y commutes with all SU(2) generators
print("\nChecking [Y, T_a^{SU(2)}] = 0:")
su2_commutes = True
for i, T in enumerate(su2_generators):
    comm = Y @ T - T @ Y
    if not np.allclose(comm, 0):
        su2_commutes = False
        print(f"  [Y, σ_{i+1}/2] ≠ 0")
    else:
        print(f"  [Y, σ_{i+1}/2] = 0 ✓")

test_result("Y commutes with SU(2)", True, su2_commutes)

# 4. Orthogonality check using Killing form
print("\n4. Orthogonality in Cartan-Killing Metric")
print("-" * 40)

# Y should be orthogonal to SU(3) and SU(2) generators
# in the sense that Tr(Y · T_a) = 0 for all SU(3) and SU(2) generators

print("\nTr(Y · λ_a) for SU(3) generators:")
for i, T in enumerate(su3_generators):
    inner = np.trace(Y @ T)
    print(f"  Tr(Y · λ_{i+1}) = {inner:.6f}")
    test_result(f"Tr(Y · λ_{i+1}) = 0", 0, np.abs(inner), tolerance=1e-10)

print("\nTr(Y · σ_a/2) for SU(2) generators:")
for i, T in enumerate(su2_generators):
    inner = np.trace(Y @ T)
    print(f"  Tr(Y · σ_{i+1}/2) = {inner:.6f}")
    test_result(f"Tr(Y · σ_{i+1}/2) = 0", 0, np.abs(inner), tolerance=1e-10)

# 5. GUT Normalization
print("\n5. GUT Normalization Factor")
print("-" * 40)

# Standard Model hypercharge coupling g' is related to SU(5) coupling by:
# g' = sqrt(3/5) g_5
#
# This comes from requiring Tr(Y²) = Tr(T_3²) at GUT scale
# (equal gauge couplings means equal trace normalization)

# T_3 in SU(5) basis: diag(0, 0, 0, 1/2, -1/2)
T3_diag = np.array([0, 0, 0, 1/2, -1/2])
T3 = np.diag(T3_diag)

trace_T3_sq = np.trace(T3 @ T3)
trace_Y_sq = np.trace(Y @ Y)

print(f"Tr(T₃²) = {trace_T3_sq}")
print(f"Tr(Y²) = {trace_Y_sq}")

# GUT normalization: Y_GUT = sqrt(3/5) Y_SM
# So that g_1 = sqrt(5/3) g'
normalization = np.sqrt(trace_T3_sq / trace_Y_sq)
expected_normalization = np.sqrt(3/5)

print(f"\nNormalization factor: {normalization:.6f}")
print(f"Expected sqrt(3/5): {expected_normalization:.6f}")
test_result("Normalization factor = sqrt(3/5)", expected_normalization, normalization, tolerance=1e-10)

# With GUT normalization
Y_GUT = expected_normalization * Y
trace_Y_GUT_sq = np.trace(Y_GUT @ Y_GUT)
test_result("Tr(Y_GUT²) = Tr(T₃²)", trace_T3_sq, trace_Y_GUT_sq, tolerance=1e-10)

# 6. Electric charge generator
print("\n6. Electric Charge Generator")
print("-" * 40)

# Q = T₃ + Y
Q = T3 + Y
Q_diag = np.diag(Q)
print(f"Q = T₃ + Y diagonal: {Q_diag}")

# Expected charges: d^c have Q = 1/3, (ν, e⁻) have Q = (0, -1)
# Wait, actually the 5 contains quarks with Q = -1/3 and leptons
# Let me reconsider: 5 of SU(5) in standard convention

# Actually for 5 representation:
# (d₁, d₂, d₃, e⁺, ν̄) or similar
# Y = (-1/3, -1/3, -1/3, 1/2, 1/2)
# T₃ = (0, 0, 0, 1/2, -1/2)
# Q = (-1/3, -1/3, -1/3, 1, 0)

expected_Q = np.array([-1/3, -1/3, -1/3, 1, 0])
print(f"Expected Q: {expected_Q}")

# But wait, this gives the positron charge (+1) not electron (-1)
# This is correct for the 5 representation
# The 5-bar has opposite charges

Q_match = np.allclose(Q_diag, expected_Q)
test_result("Q values match expected", True, Q_match)

# Verify Tr(Q) is not zero in general
trace_Q = np.trace(Q)
print(f"Tr(Q) = {trace_Q}")
# This should be -1/3 × 3 + 1 + 0 = 0

test_result("Tr(Q) = 0", 0, trace_Q, tolerance=1e-10)

# 7. Y² trace calculation detail
print("\n7. Detailed Trace Calculation")
print("-" * 40)

# Tr(Y²) = 3×(1/3)² + 2×(1/2)² = 3×(1/9) + 2×(1/4) = 1/3 + 1/2 = 5/6
manual_Y_sq = 3 * (1/3)**2 + 2 * (1/2)**2
print(f"Tr(Y²) by formula: 3×(1/9) + 2×(1/4) = {manual_Y_sq}")
test_result("Tr(Y²) = 5/6", 5/6, trace_Y_sq, tolerance=1e-10)

# Tr(T₃²) = 2 × (1/2)² = 1/2
manual_T3_sq = 2 * (1/2)**2
print(f"Tr(T₃²) by formula: 2×(1/4) = {manual_T3_sq}")
test_result("Tr(T₃²) = 1/2", 1/2, trace_T3_sq, tolerance=1e-10)

# 8. Create visualization
print("\n8. Creating Visualization")
print("-" * 40)

fig, axes = plt.subplots(1, 3, figsize=(15, 5))

# Left: Generator eigenvalues
ax1 = axes[0]
x = np.arange(5)
width = 0.25
ax1.bar(x - width, Y_diag, width, label='Y (hypercharge)', color='blue', alpha=0.7)
ax1.bar(x, T3_diag, width, label='T₃ (weak isospin)', color='red', alpha=0.7)
ax1.bar(x + width, Q_diag, width, label='Q = T₃ + Y (charge)', color='green', alpha=0.7)
ax1.set_xlabel('SU(5) fundamental index')
ax1.set_ylabel('Eigenvalue')
ax1.set_title('SU(5) Generator Eigenvalues')
ax1.legend()
ax1.set_xticks(x)
ax1.set_xticklabels(['1 (d)', '2 (d)', '3 (d)', '4 (L)', '5 (L)'])
ax1.axhline(y=0, color='black', linewidth=0.5)
ax1.grid(True, alpha=0.3)

# Middle: Trace squared contributions
ax2 = axes[1]
Y_sq_contrib = Y_diag ** 2
T3_sq_contrib = T3_diag ** 2
ax2.bar(x - width/2, Y_sq_contrib, width, label='Y² contributions', color='blue', alpha=0.7)
ax2.bar(x + width/2, T3_sq_contrib, width, label='T₃² contributions', color='red', alpha=0.7)
ax2.set_xlabel('SU(5) fundamental index')
ax2.set_ylabel('Squared eigenvalue')
ax2.set_title('Trace Contributions')
ax2.legend()
ax2.set_xticks(x)
ax2.axhline(y=0, color='black', linewidth=0.5)
ax2.grid(True, alpha=0.3)
ax2.annotate(f'Tr(Y²) = {trace_Y_sq:.4f}', xy=(0.5, 0.95), xycoords='axes fraction',
             ha='center', fontsize=10, bbox=dict(boxstyle='round', facecolor='blue', alpha=0.2))
ax2.annotate(f'Tr(T₃²) = {trace_T3_sq:.4f}', xy=(0.5, 0.85), xycoords='axes fraction',
             ha='center', fontsize=10, bbox=dict(boxstyle='round', facecolor='red', alpha=0.2))

# Right: SM gauge group structure
ax3 = axes[2]
# Illustrate the block structure of SU(5)
im = ax3.imshow(np.abs(Y), cmap='Blues', aspect='equal')
ax3.set_title('Hypercharge Y in SU(5)\n(diagonal structure)')
ax3.set_xlabel('SU(5) index')
ax3.set_ylabel('SU(5) index')

# Add grid lines to show SU(3) × SU(2) block structure
ax3.axhline(y=2.5, color='red', linewidth=2, label='SU(3)/SU(2) boundary')
ax3.axvline(x=2.5, color='red', linewidth=2)
ax3.set_xticks(range(5))
ax3.set_yticks(range(5))

# Add colorbar
plt.colorbar(im, ax=ax3, label='|Y_{ij}|')

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/theorem_2_4_1_hypercharge.png', dpi=150, bbox_inches='tight')
plt.close()
print("Saved plot to plots/theorem_2_4_1_hypercharge.png")

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

with open("/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/theorem_2_4_1_hypercharge_results.json", "w") as f:
    json.dump(results, f, indent=2)

print(f"\nResults saved to theorem_2_4_1_hypercharge_results.json")
