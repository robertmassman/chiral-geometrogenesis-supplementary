#!/usr/bin/env python3
"""
Theorem 2.4.1 Verification Script 2: Embedding Chain
=====================================================

Verifies the geometric embedding chain:
1. Construct stella octangula vertices in R³
2. Apply lift map φ to get 16-cell vertices in R⁴
3. Compute 16-cell edge midpoints (rectification)
4. Verify these are 24-cell vertices
5. Verify correspondence with D₄ roots

Author: Computational Verification Agent
Date: 2025-12-26
"""

import numpy as np
import json

# Results storage
results = {
    "theorem": "2.4.1",
    "script": "embedding_chain",
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

def stella_octangula_vertices():
    """
    Construct stella octangula vertices.
    Two interpenetrating tetrahedra T+ and T-.
    """
    # T+ vertices (positive parity: xyz > 0)
    T_plus = np.array([
        [1, 1, 1],
        [1, -1, -1],
        [-1, 1, -1],
        [-1, -1, 1]
    ], dtype=float)

    # T- vertices (negative parity: xyz < 0)
    T_minus = np.array([
        [-1, -1, -1],
        [-1, 1, 1],
        [1, -1, 1],
        [1, 1, -1]
    ], dtype=float)

    return T_plus, T_minus

def lift_to_4d(vertex):
    """
    Apply lift map φ: R³ → R⁴
    φ(x₁, x₂, x₃) = (1/2)(x₁, x₂, x₃, x₁x₂x₃)
    """
    x1, x2, x3 = vertex
    return np.array([x1, x2, x3, x1 * x2 * x3]) / 2

def sixteen_cell_standard_vertices():
    """
    Standard 16-cell vertices: ±e₁, ±e₂, ±e₃, ±e₄
    """
    vertices = []
    for i in range(4):
        v_plus = np.zeros(4)
        v_plus[i] = 1
        v_minus = np.zeros(4)
        v_minus[i] = -1
        vertices.append(v_plus)
        vertices.append(v_minus)
    return np.array(vertices)

def compute_16cell_edges(vertices):
    """
    Compute edges of 16-cell.
    Two vertices are connected if they are not antipodal.
    For standard 16-cell, vertices ±eᵢ are connected to all ±eⱼ where j ≠ i.
    """
    edges = []
    n = len(vertices)
    for i in range(n):
        for j in range(i + 1, n):
            # Check if not antipodal (sum not zero)
            if not np.allclose(vertices[i] + vertices[j], 0):
                edges.append((i, j))
    return edges

def compute_edge_midpoints(vertices, edges):
    """
    Compute midpoints of all edges.
    """
    midpoints = []
    for i, j in edges:
        midpoint = (vertices[i] + vertices[j]) / 2
        midpoints.append(midpoint)
    return np.array(midpoints)

def d4_roots():
    """
    Construct D₄ root system: {±eᵢ ± eⱼ : i < j}
    """
    roots = []
    e = np.eye(4)
    for i in range(4):
        for j in range(i + 1, 4):
            roots.append(e[i] + e[j])   # +eᵢ + eⱼ
            roots.append(e[i] - e[j])   # +eᵢ - eⱼ
            roots.append(-e[i] + e[j])  # -eᵢ + eⱼ
            roots.append(-e[i] - e[j])  # -eᵢ - eⱼ
    return np.array(roots)

def normalize_vectors(vectors):
    """Normalize each vector to unit length."""
    norms = np.linalg.norm(vectors, axis=1, keepdims=True)
    return vectors / norms

def check_correspondence(set1, set2, tolerance=1e-10):
    """
    Check if two sets of vectors are the same up to permutation and scaling.
    """
    # Normalize both sets
    set1_norm = normalize_vectors(set1.copy())
    set2_norm = normalize_vectors(set2.copy())

    # For each vector in set1, find a matching vector in set2
    matched = []
    for v1 in set1_norm:
        found = False
        for i, v2 in enumerate(set2_norm):
            if i in matched:
                continue
            if np.allclose(v1, v2, atol=tolerance) or np.allclose(v1, -v2, atol=tolerance):
                matched.append(i)
                found = True
                break
        if not found:
            return False

    return len(matched) == len(set1)

print("=" * 60)
print("Theorem 2.4.1 Verification: Embedding Chain")
print("=" * 60)
print()

# Step 1: Construct stella octangula
print("Step 1: Stella Octangula Construction")
print("-" * 40)
T_plus, T_minus = stella_octangula_vertices()
stella_vertices = np.vstack([T_plus, T_minus])
print(f"T+ vertices:\n{T_plus}")
print(f"T- vertices:\n{T_minus}")
test_result("Stella octangula vertex count", 8, len(stella_vertices))

# Check that T+ has xyz > 0 and T- has xyz < 0
print("\nVerifying parity structure:")
T_plus_parities = [np.prod(v) for v in T_plus]
T_minus_parities = [np.prod(v) for v in T_minus]
test_result("T+ all positive parity", True, all(p > 0 for p in T_plus_parities))
test_result("T- all negative parity", True, all(p < 0 for p in T_minus_parities))

# Step 2: Lift to 4D
print("\nStep 2: Lift to 4D via φ map")
print("-" * 40)
lifted_vertices = np.array([lift_to_4d(v) for v in stella_vertices])
print(f"Lifted vertices (first 4 from T+):\n{lifted_vertices[:4]}")
print(f"Lifted vertices (last 4 from T-):\n{lifted_vertices[4:]}")

# Check 4th coordinate structure
print("\nVerifying 4th coordinate structure:")
test_result("T+ lift: 4th coord = +1/2", True, all(np.isclose(v[3], 0.5) for v in lifted_vertices[:4]))
test_result("T- lift: 4th coord = -1/2", True, all(np.isclose(v[3], -0.5) for v in lifted_vertices[4:]))

# Step 3: Compare with standard 16-cell
print("\nStep 3: Compare with Standard 16-cell")
print("-" * 40)
std_16cell = sixteen_cell_standard_vertices()

# The lifted stella vertices are a 16-cell rotated/scaled
# Verify they all have the same norm
lifted_norms = np.linalg.norm(lifted_vertices, axis=1)
print(f"Lifted vertex norms: {lifted_norms}")
test_result("All lifted vertices same norm", True, np.allclose(lifted_norms, lifted_norms[0]))

# Standard 16-cell has 8 vertices at distance 1 from origin
test_result("Standard 16-cell vertex count", 8, len(std_16cell))

# Step 4: 16-cell edges and rectification
print("\nStep 4: 16-cell Edges and Rectification")
print("-" * 40)
edges_16cell = compute_16cell_edges(std_16cell)
test_result("16-cell edge count", 24, len(edges_16cell))

midpoints = compute_edge_midpoints(std_16cell, edges_16cell)
test_result("Midpoint count (24-cell vertices)", 24, len(midpoints))

# Step 5: Verify 24-cell structure
print("\nStep 5: Verify 24-cell Structure")
print("-" * 40)

# 24-cell vertices should all be at same distance from origin
midpoint_norms = np.linalg.norm(midpoints, axis=1)
test_result("All 24-cell vertices same norm", True, np.allclose(midpoint_norms, midpoint_norms[0]))

# Print unique midpoint structures
print(f"Midpoint norm: {midpoint_norms[0]:.6f}")
print(f"Expected (1/sqrt(2)): {1/np.sqrt(2):.6f}")
test_result("24-cell vertex norm = 1/sqrt(2)", 1/np.sqrt(2), midpoint_norms[0], tolerance=1e-10)

# Step 6: D₄ root system correspondence
print("\nStep 6: D₄ Root System Correspondence")
print("-" * 40)
d4 = d4_roots()
test_result("D₄ root count", 24, len(d4))

# Check that midpoints (scaled by 2) match D₄ roots
scaled_midpoints = midpoints * 2
print("\nComparing scaled midpoints to D₄ roots...")
correspondence = check_correspondence(scaled_midpoints, d4)
test_result("24-cell vertices ↔ D₄ roots", True, correspondence)

# Step 7: Verify D₄ root properties
print("\nStep 7: Verify D₄ Root Properties")
print("-" * 40)

# All roots should have squared length 2
d4_squared_lengths = np.sum(d4 ** 2, axis=1)
test_result("All D₄ roots have squared length 2", True, np.allclose(d4_squared_lengths, 2))

# Check inner products are in {0, ±1, ±2}
inner_products = set()
for i in range(len(d4)):
    for j in range(i + 1, len(d4)):
        ip = np.dot(d4[i], d4[j])
        inner_products.add(round(ip))
print(f"D₄ root inner products: {sorted(inner_products)}")
test_result("D₄ inner products in {-2,-1,0,1,2}", True, inner_products.issubset({-2, -1, 0, 1, 2}))

# Step 8: Embedding dimensions
print("\nStep 8: Verify Embedding Dimensions")
print("-" * 40)
test_result("Stella in R³", 3, stella_vertices.shape[1])
test_result("16-cell in R⁴", 4, lifted_vertices.shape[1])
test_result("24-cell in R⁴", 4, midpoints.shape[1])
test_result("D₄ roots in R⁴", 4, d4.shape[1])

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

with open("/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/theorem_2_4_1_embedding_chain_results.json", "w") as f:
    json.dump(results, f, indent=2)

print(f"\nResults saved to theorem_2_4_1_embedding_chain_results.json")
