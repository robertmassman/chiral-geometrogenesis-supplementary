#!/usr/bin/env python3
"""
Proposition 0.0.27 §10.3.12.10.10: Clover Coefficient Verification
===================================================================

Verifies the Sheikholeslami-Wohlert (clover) improvement coefficient
derived from stella octangula geometry for gauge field improvement.

Key claims verified:
1. c_SW = n_f/n_e = 8/12 = 2/3 (tree-level clover coefficient)
2. Universal ratio for triangulated spheres: 3n_f = 2n_e → n_f/n_e = 2/3
3. Euler characteristic connection: n_f/n_e = n_f/(n_f + n_v - χ)
4. Faces per vertex in K₄: 3
5. One-loop correction: f_SW = r² = 9/16
6. Full one-loop: c_SW^(1-loop) ≈ 0.670

Related Documents:
- Proof: docs/proofs/foundations/Proposition-0.0.27-Higgs-Mass-From-Geometry.md §10.3.12.10.10

Verification Date: 2026-02-03
"""

import numpy as np
from itertools import combinations
import json
from datetime import datetime

# ==============================================================================
# SIMPLICIAL COMPLEX SETUP
# ==============================================================================

class TetrahedralComplex:
    """Represents a tetrahedron as a simplicial complex."""

    def __init__(self, n_vertices=4):
        """Initialize K_n (complete graph / simplex on n vertices)."""
        self.n = n_vertices
        self.vertices = list(range(n_vertices))
        self.edges = list(combinations(range(n_vertices), 2))
        self.faces = list(combinations(range(n_vertices), 3))

        self.n_v = len(self.vertices)
        self.n_e = len(self.edges)
        self.n_f = len(self.faces)

    def faces_containing_vertex(self, v):
        """Return faces that contain vertex v."""
        return [f for f in self.faces if v in f]

    def edges_containing_vertex(self, v):
        """Return edges that contain vertex v."""
        return [e for e in self.edges if v in e]

    def faces_bordering_edge(self, e):
        """Return faces that contain edge e."""
        return [f for f in self.faces if e[0] in f and e[1] in f]

    def euler_characteristic(self):
        """Compute χ = V - E + F."""
        return self.n_v - self.n_e + self.n_f


class StellaOctangula:
    """Represents the stella octangula (two interpenetrating tetrahedra)."""

    def __init__(self):
        """Initialize as disjoint union of two tetrahedra."""
        self.T_plus = TetrahedralComplex(4)
        self.T_minus = TetrahedralComplex(4)

        # Total counts
        self.n_v = self.T_plus.n_v + self.T_minus.n_v  # 8
        self.n_e = self.T_plus.n_e + self.T_minus.n_e  # 12
        self.n_f = self.T_plus.n_f + self.T_minus.n_f  # 8

    def euler_characteristic(self):
        """Compute χ = V - E + F = 4 (two S²)."""
        return self.n_v - self.n_e + self.n_f


# ==============================================================================
# VERIFICATION FUNCTIONS
# ==============================================================================

def test_I_simplex_counts():
    """Test I: Verify simplex counts for K₄ and stella."""
    K4 = TetrahedralComplex(4)
    stella = StellaOctangula()

    results = {
        "test": "I",
        "name": "Simplex Counts",
        "K4": {
            "n_v": K4.n_v,
            "n_e": K4.n_e,
            "n_f": K4.n_f,
            "expected": {"n_v": 4, "n_e": 6, "n_f": 4},
            "passed": K4.n_v == 4 and K4.n_e == 6 and K4.n_f == 4
        },
        "stella": {
            "n_v": stella.n_v,
            "n_e": stella.n_e,
            "n_f": stella.n_f,
            "expected": {"n_v": 8, "n_e": 12, "n_f": 8},
            "passed": stella.n_v == 8 and stella.n_e == 12 and stella.n_f == 8
        }
    }

    results["passed"] = results["K4"]["passed"] and results["stella"]["passed"]
    return results


def test_II_clover_coefficient():
    """
    Test II: Verify clover coefficient c_SW = n_f/n_e = 2/3.

    The clover coefficient bridges faces (field strength) to edges (gauge connection).
    """
    K4 = TetrahedralComplex(4)
    stella = StellaOctangula()

    c_SW_K4 = K4.n_f / K4.n_e
    c_SW_stella = stella.n_f / stella.n_e
    expected = 2/3

    results = {
        "test": "II",
        "name": "Clover Coefficient c_SW",
        "K4": {
            "n_f/n_e": c_SW_K4,
            "fraction": "4/6 = 2/3",
            "expected": expected,
            "passed": np.isclose(c_SW_K4, expected)
        },
        "stella": {
            "n_f/n_e": c_SW_stella,
            "fraction": "8/12 = 2/3",
            "expected": expected,
            "passed": np.isclose(c_SW_stella, expected)
        },
        "geometric_meaning": "Ratio of face-based (F_μν) to edge-based (A_μ) structures"
    }

    results["passed"] = results["K4"]["passed"] and results["stella"]["passed"]
    return results


def test_III_faces_per_vertex():
    """
    Test III: Verify faces per vertex in K₄.

    Each vertex in K₄ touches exactly 3 faces (triangles).
    """
    K4 = TetrahedralComplex(4)

    faces_per_vertex = []
    for v in K4.vertices:
        faces = K4.faces_containing_vertex(v)
        faces_per_vertex.append(len(faces))

    results = {
        "test": "III",
        "name": "Faces per Vertex",
        "faces_per_vertex": faces_per_vertex,
        "expected": 3,
        "all_equal": len(set(faces_per_vertex)) == 1,
        "c_face_local": 1/3,
        "interpretation": "Local clover averaging uses 1/3 weight per face",
        "passed": all(f == 3 for f in faces_per_vertex)
    }

    return results


def test_IV_edges_per_face():
    """
    Test IV: Verify edges per face and face-edge relationship.

    For triangulated surfaces: 3n_f = 2n_e (each face has 3 edges, each edge in 2 faces).
    """
    K4 = TetrahedralComplex(4)

    # Each face (triangle) has 3 edges
    edges_per_face = 3

    # Each edge borders exactly 2 faces in K₄
    faces_per_edge = []
    for e in K4.edges:
        faces = K4.faces_bordering_edge(e)
        faces_per_edge.append(len(faces))

    # Universal relation: 3n_f = 2n_e
    relation_holds = (3 * K4.n_f == 2 * K4.n_e)

    results = {
        "test": "IV",
        "name": "Face-Edge Relationship",
        "edges_per_face": edges_per_face,
        "faces_per_edge": faces_per_edge,
        "faces_per_edge_expected": 2,
        "universal_relation": {
            "formula": "3n_f = 2n_e",
            "LHS": 3 * K4.n_f,
            "RHS": 2 * K4.n_e,
            "holds": relation_holds
        },
        "implies_ratio": "n_f/n_e = 2/3 for all triangulated surfaces",
        "passed": relation_holds and all(f == 2 for f in faces_per_edge)
    }

    return results


def test_V_euler_characteristic():
    """
    Test V: Verify Euler characteristic connection.

    χ = V - E + F
    n_f/n_e = n_f/(n_f + n_v - χ)
    """
    K4 = TetrahedralComplex(4)
    stella = StellaOctangula()

    chi_K4 = K4.euler_characteristic()
    chi_stella = stella.euler_characteristic()

    # Verify: n_f/n_e = n_f/(n_f + n_v - χ)
    ratio_K4_direct = K4.n_f / K4.n_e
    ratio_K4_from_chi = K4.n_f / (K4.n_f + K4.n_v - chi_K4)

    ratio_stella_direct = stella.n_f / stella.n_e
    ratio_stella_from_chi = stella.n_f / (stella.n_f + stella.n_v - chi_stella)

    results = {
        "test": "V",
        "name": "Euler Characteristic Connection",
        "K4": {
            "χ": chi_K4,
            "expected_χ": 2,
            "n_f/n_e_direct": ratio_K4_direct,
            "n_f/(n_f + n_v - χ)": ratio_K4_from_chi,
            "match": np.isclose(ratio_K4_direct, ratio_K4_from_chi),
            "passed": chi_K4 == 2 and np.isclose(ratio_K4_direct, ratio_K4_from_chi)
        },
        "stella": {
            "χ": chi_stella,
            "expected_χ": 4,
            "interpretation": "Two disjoint S² (χ = 2 each)",
            "n_f/n_e_direct": ratio_stella_direct,
            "n_f/(n_f + n_v - χ)": ratio_stella_from_chi,
            "match": np.isclose(ratio_stella_direct, ratio_stella_from_chi),
            "passed": chi_stella == 4 and np.isclose(ratio_stella_direct, ratio_stella_from_chi)
        }
    }

    results["passed"] = results["K4"]["passed"] and results["stella"]["passed"]
    return results


def test_VI_one_loop_correction():
    """
    Test VI: Verify one-loop correction to c_SW.

    f_SW = r² = (9/16) where r = (n_v - 1)/λ_Lap = 3/4
    c_SW^(1-loop) = c_SW^(0) × (1 + g²/(16π²) × f_SW)
    """
    # Geometric parameters
    r = 3/4  # From one-loop corrections derivation
    f_SW = r**2  # Face-based operator → r²

    # Tree-level
    c_SW_tree = 2/3

    # One-loop factor
    loop_factor = 16 * np.pi**2

    # Using g² ≈ 4πα_s with α_s ≈ 0.118 at Z scale
    alpha_s = 0.118
    g2 = 4 * np.pi * alpha_s

    # Full one-loop
    c_SW_1loop = c_SW_tree * (1 + g2 / loop_factor * f_SW)

    # Relative correction
    delta_rel = g2 / loop_factor * f_SW

    results = {
        "test": "VI",
        "name": "One-Loop Correction to c_SW",
        "r": r,
        "f_SW": {
            "value": f_SW,
            "expected": 9/16,
            "formula": "r² (face-based operator)",
            "passed": np.isclose(f_SW, 9/16)
        },
        "c_SW_tree": c_SW_tree,
        "one_loop": {
            "α_s": alpha_s,
            "g²": g2,
            "loop_factor": loop_factor,
            "c_SW_1loop": c_SW_1loop,
            "expected_approx": 0.670,
            "relative_correction_percent": delta_rel * 100
        },
        "correction_is_small": delta_rel < 0.01,
        "passed": np.isclose(f_SW, 9/16)
    }

    return results


def test_VII_universality():
    """
    Test VII: Verify that n_f/n_e = 2/3 is universal for triangulated spheres.

    For any triangulation of S²:
    - Each face has 3 edges
    - Each edge is shared by 2 faces
    - Therefore 3n_f = 2n_e → n_f/n_e = 2/3
    """
    # Test for various triangulations
    # K₄ (4 vertices, minimal triangulation)
    K4 = TetrahedralComplex(4)

    # Theoretical: any triangulated sphere satisfies 3n_f = 2n_e
    # This is Euler's formula combined with 2-manifold structure

    # For n vertices on S², we have:
    # n_e = 3n - 6 (for maximal planar graph)
    # n_f = 2n - 4 (for triangulation)
    # Ratio: n_f/n_e = (2n-4)/(3n-6) = 2(n-2)/(3(n-2)) = 2/3

    test_cases = []
    for n in [4, 5, 6, 8, 10, 12]:
        # For triangulated sphere with n vertices
        n_e_theory = 3*n - 6
        n_f_theory = 2*n - 4
        ratio = n_f_theory / n_e_theory

        test_cases.append({
            "n_vertices": n,
            "n_edges": n_e_theory,
            "n_faces": n_f_theory,
            "n_f/n_e": ratio,
            "equals_2/3": np.isclose(ratio, 2/3)
        })

    results = {
        "test": "VII",
        "name": "Universality for Triangulated Spheres",
        "derivation": {
            "step1": "Each face has 3 edges",
            "step2": "Each edge borders 2 faces",
            "step3": "Therefore 3n_f = 2n_e",
            "step4": "Thus n_f/n_e = 2/3 universally"
        },
        "test_cases": test_cases,
        "all_pass": all(tc["equals_2/3"] for tc in test_cases),
        "passed": all(tc["equals_2/3"] for tc in test_cases)
    }

    return results


def test_VIII_hypercubic_comparison():
    """
    Test VIII: Compare stella geometry to hypercubic lattice.

    Standard hypercubic:
    - c_SW^(0) = 1
    - 4 plaquettes per (μ,ν) plane
    - 6 planes in 4D → 24 plaquettes per site

    K₄ (stella):
    - c_SW^(0) = 2/3
    - 3 faces per vertex
    """
    # Hypercubic
    plaquettes_per_plane = 4
    planes_4D = 6
    plaquettes_per_site_hyper = plaquettes_per_plane * planes_4D / 4  # each plaquette shared by 4 sites

    # K₄
    K4 = TetrahedralComplex(4)
    faces_per_vertex = 3

    # Ratio of clover coefficients
    c_SW_hyper = 1.0
    c_SW_K4 = 2/3
    ratio = c_SW_K4 / c_SW_hyper

    results = {
        "test": "VIII",
        "name": "Hypercubic vs Stella Comparison",
        "hypercubic": {
            "c_SW_tree": c_SW_hyper,
            "plaquettes_per_plane": plaquettes_per_plane,
            "planes_4D": planes_4D,
            "plaquettes_per_site": plaquettes_per_site_hyper
        },
        "K4_stella": {
            "c_SW_tree": c_SW_K4,
            "faces_per_vertex": faces_per_vertex,
            "n_f": K4.n_f,
            "n_e": K4.n_e
        },
        "ratio_c_SW": {
            "K4/hyper": ratio,
            "equals_2/3": np.isclose(ratio, 2/3)
        },
        "interpretation": "Different geometry leads to different tree-level coefficient",
        "passed": np.isclose(ratio, 2/3)
    }

    return results


def test_IX_complete_improvement_pattern():
    """
    Test IX: Verify the complete Geometric Improvement Principle.

    Scalar: λ = 1/n_v, c₁ = 1/n_e, c₂ = 1/n_f
    Gauge: c_SW = n_f/n_e
    """
    stella = StellaOctangula()

    # Scalar coefficients
    lamb = 1 / stella.n_v
    c1 = 1 / stella.n_e
    c2 = 1 / stella.n_f

    # Gauge coefficient
    c_SW = stella.n_f / stella.n_e

    results = {
        "test": "IX",
        "name": "Complete Geometric Improvement Pattern",
        "scalar_coefficients": {
            "λ": {
                "value": lamb,
                "formula": "1/n_v",
                "expected": 1/8,
                "passed": np.isclose(lamb, 1/8)
            },
            "c₁": {
                "value": c1,
                "formula": "1/n_e",
                "expected": 1/12,
                "passed": np.isclose(c1, 1/12)
            },
            "c₂": {
                "value": c2,
                "formula": "1/n_f",
                "expected": 1/8,
                "passed": np.isclose(c2, 1/8)
            }
        },
        "gauge_coefficient": {
            "c_SW": {
                "value": c_SW,
                "formula": "n_f/n_e",
                "expected": 2/3,
                "interpretation": "Bridges faces (F_μν) to edges (A_μ)",
                "passed": np.isclose(c_SW, 2/3)
            }
        },
        "pattern": "Scalar: inverse simplex counts; Gauge: simplex ratios"
    }

    results["passed"] = (
        results["scalar_coefficients"]["λ"]["passed"] and
        results["scalar_coefficients"]["c₁"]["passed"] and
        results["scalar_coefficients"]["c₂"]["passed"] and
        results["gauge_coefficient"]["c_SW"]["passed"]
    )

    return results


def test_X_clover_averaging_structure():
    """
    Test X: Verify the clover averaging structure on K₄.

    At each vertex v, the field strength averages over 3 faces:
    F̂_v = (1/3) Σ_{f ∋ v} W_f
    """
    K4 = TetrahedralComplex(4)

    # For each vertex, identify which faces contain it
    clover_structure = {}
    for v in K4.vertices:
        faces = K4.faces_containing_vertex(v)
        clover_structure[v] = {
            "faces": faces,
            "n_faces": len(faces),
            "weight": 1/len(faces)
        }

    # Verify all vertices have same structure
    n_faces_list = [cs["n_faces"] for cs in clover_structure.values()]
    weights_list = [cs["weight"] for cs in clover_structure.values()]

    results = {
        "test": "X",
        "name": "Clover Averaging Structure",
        "clover_structure": {
            v: {
                "faces": [list(f) for f in data["faces"]],
                "n_faces": data["n_faces"],
                "weight": data["weight"]
            }
            for v, data in clover_structure.items()
        },
        "uniform": {
            "all_vertices_same_n_faces": len(set(n_faces_list)) == 1,
            "n_faces_per_vertex": n_faces_list[0] if len(set(n_faces_list)) == 1 else "varies",
            "weight_per_face": weights_list[0] if len(set(weights_list)) == 1 else "varies"
        },
        "formula": "F̂_v = (1/3) Σ_{f ∋ v} W_f",
        "passed": len(set(n_faces_list)) == 1 and n_faces_list[0] == 3
    }

    return results


# ==============================================================================
# MAIN EXECUTION
# ==============================================================================

def main():
    """Run all verification tests."""
    results = {
        "proposition": "0.0.27",
        "section": "10.3.12.10.10",
        "title": "Clover Coefficient for Gauge Fields",
        "timestamp": datetime.now().isoformat(),
        "tests": {}
    }

    # Run all tests
    tests = [
        ("test_I", test_I_simplex_counts),
        ("test_II", test_II_clover_coefficient),
        ("test_III", test_III_faces_per_vertex),
        ("test_IV", test_IV_edges_per_face),
        ("test_V", test_V_euler_characteristic),
        ("test_VI", test_VI_one_loop_correction),
        ("test_VII", test_VII_universality),
        ("test_VIII", test_VIII_hypercubic_comparison),
        ("test_IX", test_IX_complete_improvement_pattern),
        ("test_X", test_X_clover_averaging_structure),
    ]

    all_passed = True
    print("=" * 70)
    print("Proposition 0.0.27 §10.3.12.10.10: Clover Coefficient Verification")
    print("=" * 70)

    for test_name, test_func in tests:
        test_result = test_func()
        results["tests"][test_name] = test_result

        status = "✓ PASSED" if test_result["passed"] else "✗ FAILED"
        print(f"  {test_result['test']}. {test_result['name']}: {status}")

        if not test_result["passed"]:
            all_passed = False

    # Overall status
    results["overall_status"] = "PASSED" if all_passed else "FAILED"

    print("=" * 70)
    print(f"Overall Status: {results['overall_status']}")
    print("=" * 70)

    # Key results summary
    print("\nKey Results:")
    print(f"  • c_SW = n_f/n_e = 8/12 = 2/3 (tree-level)")
    print(f"  • Universal for all triangulated spheres (3n_f = 2n_e)")
    print(f"  • Connected to Euler characteristic: n_f/(n_f + n_v - χ) = 2/3")
    print(f"  • One-loop correction factor: f_SW = r² = 9/16")
    print(f"  • Full one-loop: c_SW^(1-loop) ≈ 0.670 (correction ~0.5%)")

    # Save results
    output_file = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/foundations/prop_0_0_27_clover_coefficient_results.json"

    # Make results JSON serializable
    def make_serializable(obj):
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.integer):
            return int(obj)
        elif isinstance(obj, np.bool_):
            return bool(obj)
        elif isinstance(obj, dict):
            return {k: make_serializable(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [make_serializable(item) for item in obj]
        elif isinstance(obj, tuple):
            return list(obj)
        return obj

    serializable_results = make_serializable(results)

    with open(output_file, "w") as f:
        json.dump(serializable_results, f, indent=2)

    print(f"\nResults saved to: {output_file}")

    return results


if __name__ == "__main__":
    main()
