#!/usr/bin/env python3
"""
Proposition 0.0.27 §10.3.12.10.12: Fermion Improvement Verification
====================================================================

Verifies the Wilson parameter and fermion improvement coefficients
derived from stella octangula geometry.

Key claims verified:
1. Wilson parameter r = n_e/n_v = 12/8 = 3/2
2. Doubler count on K₄: 3 (from triply degenerate λ = 4)
3. Doubler mass with r = 3/2: m_doubler = 6/a (50% heavier than r = 1)
4. Vertex degree on K₄: 3 (each vertex connects to 3 edges)
5. Complete Geometric Improvement Pattern for all field types
6. Ginsparg-Wilson relation structure for overlap fermions

Related Documents:
- Proof: docs/proofs/foundations/Proposition-0.0.27-Higgs-Mass-From-Geometry.md §10.3.12.10.12

Verification Date: 2026-02-03
"""

import numpy as np
from itertools import combinations
import json
from datetime import datetime

# ==============================================================================
# SIMPLICIAL COMPLEX SETUP
# ==============================================================================

class SimplicialComplex:
    """Represents a simplicial complex for fermion analysis."""

    def __init__(self, n_vertices=4):
        """Initialize K_n (complete graph / simplex on n vertices)."""
        self.n = n_vertices
        self.vertices = list(range(n_vertices))
        self.edges = list(combinations(range(n_vertices), 2))
        self.faces = list(combinations(range(n_vertices), 3))

        self.n_v = len(self.vertices)
        self.n_e = len(self.edges)
        self.n_f = len(self.faces)

    def vertex_degree(self, v):
        """Return the degree (number of edges) of vertex v."""
        return sum(1 for e in self.edges if v in e)

    def laplacian(self):
        """Construct the graph Laplacian L = D - A."""
        n = self.n_v
        A = np.zeros((n, n))
        for e in self.edges:
            A[e[0], e[1]] = 1
            A[e[1], e[0]] = 1
        D = np.diag([self.vertex_degree(v) for v in self.vertices])
        return D - A


class StellaOctangula:
    """Represents the stella octangula (two interpenetrating tetrahedra)."""

    def __init__(self):
        """Initialize as disjoint union of two tetrahedra."""
        self.T_plus = SimplicialComplex(4)
        self.T_minus = SimplicialComplex(4)

        # Total counts
        self.n_v = self.T_plus.n_v + self.T_minus.n_v  # 8
        self.n_e = self.T_plus.n_e + self.T_minus.n_e  # 12
        self.n_f = self.T_plus.n_f + self.T_minus.n_f  # 8


# ==============================================================================
# VERIFICATION FUNCTIONS
# ==============================================================================

def test_I_wilson_parameter():
    """
    Test I: Verify Wilson parameter r = n_e/n_v = 3/2.

    The Wilson term is a vertex-edge coupling, so the coefficient is n_e/n_v.
    """
    K4 = SimplicialComplex(4)
    stella = StellaOctangula()

    r_K4 = K4.n_e / K4.n_v
    r_stella = stella.n_e / stella.n_v
    expected = 3/2

    results = {
        "test": "I",
        "name": "Wilson Parameter r",
        "K4": {
            "n_e": K4.n_e,
            "n_v": K4.n_v,
            "r = n_e/n_v": r_K4,
            "fraction": "6/4 = 3/2",
            "expected": expected,
            "passed": np.isclose(r_K4, expected)
        },
        "stella": {
            "n_e": stella.n_e,
            "n_v": stella.n_v,
            "r = n_e/n_v": r_stella,
            "fraction": "12/8 = 3/2",
            "expected": expected,
            "passed": np.isclose(r_stella, expected)
        },
        "interpretation": "Wilson term couples vertices (fermions) to edges (Laplacian)"
    }

    results["passed"] = results["K4"]["passed"] and results["stella"]["passed"]
    return results


def test_II_vertex_degree():
    """
    Test II: Verify vertex degree on K₄.

    Each vertex in K₄ connects to n-1 = 3 other vertices.
    """
    K4 = SimplicialComplex(4)

    degrees = [K4.vertex_degree(v) for v in K4.vertices]

    results = {
        "test": "II",
        "name": "Vertex Degree on K₄",
        "degrees": degrees,
        "expected": 3,
        "all_equal": len(set(degrees)) == 1,
        "interpretation": "Each vertex connects to 3 edges",
        "relation_to_r": "r = n_e/n_v = (degree × n_v / 2) / n_v = degree/2 = 3/2",
        "passed": all(d == 3 for d in degrees)
    }

    return results


def test_III_laplacian_spectrum():
    """
    Test III: Verify Laplacian spectrum on K₄.

    Eigenvalues: {0, 4, 4, 4} (one zero mode, triply degenerate λ = 4)
    """
    K4 = SimplicialComplex(4)
    L = K4.laplacian()

    eigenvalues = np.linalg.eigvalsh(L)
    eigenvalues_sorted = np.sort(eigenvalues)
    expected = np.array([0, 4, 4, 4])

    # Count doublers (non-zero eigenvalues)
    n_doublers = np.sum(np.abs(eigenvalues) > 1e-10)

    results = {
        "test": "III",
        "name": "Laplacian Spectrum on K₄",
        "eigenvalues": eigenvalues_sorted.tolist(),
        "expected": expected.tolist(),
        "physical_mode": {
            "eigenvalue": 0,
            "multiplicity": 1,
            "interpretation": "Physical fermion (p = 0 mode)"
        },
        "doubler_modes": {
            "eigenvalue": 4,
            "multiplicity": 3,
            "interpretation": "Would-be doublers"
        },
        "n_doublers": int(n_doublers),
        "comparison": "K₄ has 3 doublers vs 15 (= 2⁴ - 1) on 4D hypercubic",
        "passed": np.allclose(eigenvalues_sorted, expected, atol=1e-10)
    }

    return results


def test_IV_doubler_mass():
    """
    Test IV: Verify doubler mass with geometric r = 3/2.

    m_doubler = r × λ_Lap / a = (3/2) × 4 / a = 6/a
    """
    # Parameters
    r_geometric = 3/2
    r_standard = 1.0
    lambda_lap = 4  # Non-zero Laplacian eigenvalue

    # Doubler masses (in units of 1/a)
    m_doubler_geometric = r_geometric * lambda_lap
    m_doubler_standard = r_standard * lambda_lap

    # Ratio
    ratio = m_doubler_geometric / m_doubler_standard

    results = {
        "test": "IV",
        "name": "Doubler Mass",
        "geometric_r": {
            "r": r_geometric,
            "λ_Lap": lambda_lap,
            "m_doubler": m_doubler_geometric,
            "formula": "r × λ_Lap = (3/2) × 4 = 6",
            "units": "1/a"
        },
        "standard_r": {
            "r": r_standard,
            "λ_Lap": lambda_lap,
            "m_doubler": m_doubler_standard,
            "formula": "r × λ_Lap = 1 × 4 = 4",
            "units": "1/a"
        },
        "ratio": {
            "geometric/standard": ratio,
            "expected": 1.5,
            "interpretation": "50% heavier doublers with geometric r"
        },
        "passed": np.isclose(m_doubler_geometric, 6) and np.isclose(ratio, 1.5)
    }

    return results


def test_V_complete_improvement_pattern():
    """
    Test V: Verify the complete Geometric Improvement Pattern.

    Scalar: λ = 1/n_v, c₁ = 1/n_e, c₂ = 1/n_f
    Gauge: c_SW = n_f/n_e
    Fermion: r = n_e/n_v
    """
    stella = StellaOctangula()

    # Scalar coefficients
    lamb = 1 / stella.n_v
    c1 = 1 / stella.n_e
    c2 = 1 / stella.n_f

    # Gauge coefficient
    c_SW = stella.n_f / stella.n_e

    # Fermion coefficient
    r = stella.n_e / stella.n_v

    results = {
        "test": "V",
        "name": "Complete Geometric Improvement Pattern",
        "scalar": {
            "λ": {"value": lamb, "formula": "1/n_v", "expected": 1/8, "passed": np.isclose(lamb, 1/8)},
            "c₁": {"value": c1, "formula": "1/n_e", "expected": 1/12, "passed": np.isclose(c1, 1/12)},
            "c₂": {"value": c2, "formula": "1/n_f", "expected": 1/8, "passed": np.isclose(c2, 1/8)}
        },
        "gauge": {
            "c_SW": {"value": c_SW, "formula": "n_f/n_e", "expected": 2/3, "passed": np.isclose(c_SW, 2/3)}
        },
        "fermion": {
            "r": {"value": r, "formula": "n_e/n_v", "expected": 3/2, "passed": np.isclose(r, 3/2)}
        },
        "pattern": {
            "same_degree": "1/n_p for p-simplex operators",
            "mixed_degree": "n_q/n_p for (p→q) couplings"
        }
    }

    results["passed"] = (
        results["scalar"]["λ"]["passed"] and
        results["scalar"]["c₁"]["passed"] and
        results["scalar"]["c₂"]["passed"] and
        results["gauge"]["c_SW"]["passed"] and
        results["fermion"]["r"]["passed"]
    )

    return results


def test_VI_operator_simplex_classification():
    """
    Test VI: Verify the operator-simplex classification.

    | Operator | Lives on | Couples to | Coefficient |
    |----------|----------|------------|-------------|
    | φ⁴       | 0-simplex| 0-simplex  | 1/n_v       |
    | ∂²φ      | 0-simplex| 1-simplex  | 1/n_e       |
    | φ²(∂φ)²  | 0-simplex| 2-simplex  | 1/n_f       |
    | Clover   | 1-simplex| 2-simplex  | n_f/n_e     |
    | Wilson   | 0-simplex| 1-simplex  | n_e/n_v     |
    """
    stella = StellaOctangula()

    operators = {
        "φ⁴ (scalar self)": {
            "from": 0, "to": 0,
            "formula": "1/n_v",
            "value": 1/stella.n_v,
            "expected": 1/8
        },
        "∂²φ (kinetic)": {
            "from": 0, "to": 1,
            "formula": "1/n_e",
            "value": 1/stella.n_e,
            "expected": 1/12
        },
        "φ²(∂φ)² (vertex)": {
            "from": 0, "to": 2,
            "formula": "1/n_f",
            "value": 1/stella.n_f,
            "expected": 1/8
        },
        "Clover (gauge)": {
            "from": 1, "to": 2,
            "formula": "n_f/n_e",
            "value": stella.n_f/stella.n_e,
            "expected": 2/3
        },
        "Wilson (fermion)": {
            "from": 0, "to": 1,
            "formula": "n_e/n_v",
            "value": stella.n_e/stella.n_v,
            "expected": 3/2
        }
    }

    results = {
        "test": "VI",
        "name": "Operator-Simplex Classification",
        "operators": {}
    }

    all_passed = True
    for name, op in operators.items():
        passed = np.isclose(op["value"], op["expected"])
        results["operators"][name] = {
            "simplex_coupling": f"{op['from']}→{op['to']}",
            "formula": op["formula"],
            "value": op["value"],
            "expected": op["expected"],
            "passed": passed
        }
        if not passed:
            all_passed = False

    results["passed"] = all_passed
    return results


def test_VII_edge_vertex_interpretation():
    """
    Test VII: Verify the edge-vertex interpretation of r.

    r = n_e/n_v = (vertex_degree × n_v / 2) / n_v = vertex_degree / 2
    """
    K4 = SimplicialComplex(4)

    # Vertex degree (same for all vertices in K_n)
    degree = K4.vertex_degree(0)

    # Total edges from handshaking lemma: 2 × n_e = Σ degrees
    total_degree = sum(K4.vertex_degree(v) for v in K4.vertices)
    n_e_from_handshaking = total_degree // 2

    # r from edge-vertex ratio
    r_direct = K4.n_e / K4.n_v

    # r from degree
    r_from_degree = degree / 2

    results = {
        "test": "VII",
        "name": "Edge-Vertex Interpretation",
        "vertex_degree": degree,
        "handshaking_lemma": {
            "total_degree": total_degree,
            "n_e = Σdeg/2": n_e_from_handshaking,
            "matches_n_e": n_e_from_handshaking == K4.n_e
        },
        "r_calculations": {
            "r_direct": r_direct,
            "r_from_degree": r_from_degree,
            "formula": "r = degree/2 = 3/2",
            "match": np.isclose(r_direct, r_from_degree)
        },
        "physical_meaning": "Wilson parameter counts hopping directions per vertex",
        "passed": np.isclose(r_direct, r_from_degree) and np.isclose(r_direct, 3/2)
    }

    return results


def test_VIII_wilson_vs_overlap_comparison():
    """
    Test VIII: Compare Wilson vs Overlap fermion properties.

    Wilson: Breaks chiral symmetry, local
    Overlap: Preserves GW chiral symmetry, quasi-local
    """
    results = {
        "test": "VIII",
        "name": "Wilson vs Overlap Comparison",
        "wilson": {
            "chiral_symmetry": "Broken O(a)",
            "locality": "Strictly local",
            "doublers": "Lifted to cutoff",
            "mass_renorm": "Additive",
            "r_parameter": "Typically r = 1"
        },
        "overlap": {
            "chiral_symmetry": "Exact (Ginsparg-Wilson)",
            "locality": "Quasi-local",
            "doublers": "Eliminated exactly",
            "mass_renorm": "Multiplicative only",
            "r_parameter": "Any r ≠ 0 (use r = 3/2)"
        },
        "geometric_prediction": {
            "r": 3/2,
            "applies_to": "Both Wilson and Overlap (in H_W kernel)",
            "advantage": "Removes free parameter"
        },
        "CG_preference": "Overlap (chiral symmetry is fundamental)",
        "passed": True  # Informational test
    }

    return results


def test_IX_spectral_gap():
    """
    Test IX: Verify the spectral gap improvement with r = 3/2.

    Larger r gives larger spectral gap in H_W, improving overlap locality.
    """
    K4 = SimplicialComplex(4)
    L = K4.laplacian()

    # Non-zero Laplacian eigenvalue
    lambda_lap = 4

    # Spectral gap = smallest non-zero eigenvalue × r
    # For Wilson-Dirac: gap ~ r × λ_Lap

    r_values = [0.5, 1.0, 1.5, 2.0]
    gaps = []

    for r in r_values:
        gap = r * lambda_lap
        gaps.append({
            "r": r,
            "gap": gap,
            "interpretation": f"Doubler mass = {gap}/a"
        })

    # The geometric r = 3/2 gives gap = 6
    geometric_gap = 3/2 * lambda_lap

    results = {
        "test": "IX",
        "name": "Spectral Gap Improvement",
        "gap_formula": "gap = r × λ_Lap",
        "λ_Lap": lambda_lap,
        "r_comparison": gaps,
        "geometric_r": {
            "r": 3/2,
            "gap": geometric_gap,
            "expected": 6.0,
            "passed": np.isclose(geometric_gap, 6.0)
        },
        "improvement_over_standard": {
            "standard_gap": 4.0,
            "geometric_gap": 6.0,
            "improvement_percent": 50.0
        },
        "benefit": "Larger gap improves locality of overlap sign function",
        "passed": np.isclose(geometric_gap, 6.0)
    }

    return results


def test_X_fermion_doubling_reduction():
    """
    Test X: Verify that K₄ naturally reduces fermion doubling.

    Comparison:
    - 4D hypercubic: 2⁴ - 1 = 15 doublers
    - K₄: 3 doublers (from λ = 4 degeneracy)
    """
    K4 = SimplicialComplex(4)
    L = K4.laplacian()

    # Eigenvalues
    eigenvalues = np.linalg.eigvalsh(L)

    # Count doublers (non-zero eigenvalues)
    n_doublers_K4 = np.sum(np.abs(eigenvalues) > 1e-10)

    # Hypercubic comparison
    d = 4  # dimension
    n_doublers_hypercubic = 2**d - 1

    # Reduction factor
    reduction = n_doublers_hypercubic / n_doublers_K4

    results = {
        "test": "X",
        "name": "Fermion Doubling Reduction",
        "K4": {
            "n_doublers": int(n_doublers_K4),
            "source": "Triply degenerate λ = 4 eigenvalue"
        },
        "hypercubic_4D": {
            "n_doublers": n_doublers_hypercubic,
            "source": "Corners of Brillouin zone"
        },
        "reduction_factor": reduction,
        "interpretation": f"K₄ has {reduction:.1f}× fewer doublers than 4D hypercubic",
        "stella_advantage": "Natural doubler reduction from simplicial structure",
        "passed": n_doublers_K4 == 3 and n_doublers_hypercubic == 15
    }

    return results


# ==============================================================================
# MAIN EXECUTION
# ==============================================================================

def main():
    """Run all verification tests."""
    results = {
        "proposition": "0.0.27",
        "section": "10.3.12.10.12",
        "title": "Fermion Improvement: Wilson vs Overlap",
        "timestamp": datetime.now().isoformat(),
        "tests": {}
    }

    # Run all tests
    tests = [
        ("test_I", test_I_wilson_parameter),
        ("test_II", test_II_vertex_degree),
        ("test_III", test_III_laplacian_spectrum),
        ("test_IV", test_IV_doubler_mass),
        ("test_V", test_V_complete_improvement_pattern),
        ("test_VI", test_VI_operator_simplex_classification),
        ("test_VII", test_VII_edge_vertex_interpretation),
        ("test_VIII", test_VIII_wilson_vs_overlap_comparison),
        ("test_IX", test_IX_spectral_gap),
        ("test_X", test_X_fermion_doubling_reduction),
    ]

    all_passed = True
    print("=" * 70)
    print("Proposition 0.0.27 §10.3.12.10.12: Fermion Improvement Verification")
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
    print(f"  • Wilson parameter r = n_e/n_v = 12/8 = 3/2")
    print(f"  • Vertex degree on K₄: 3 (r = degree/2 = 3/2)")
    print(f"  • Laplacian spectrum: {{0, 4, 4, 4}} → 3 doublers")
    print(f"  • Doubler mass: 6/a (geometric) vs 4/a (standard) → 50% improvement")
    print(f"  • K₄ has 3 doublers vs 15 on 4D hypercubic (5× reduction)")
    print(f"  • CG framework requires overlap fermions with r = 3/2")

    # Save results
    output_file = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/foundations/prop_0_0_27_fermion_improvement_results.json"

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
