#!/usr/bin/env python3
"""
Numerical Verification: Theorem 0.2.1 - Total Field from Superposition

This script verifies the mathematical claims in Theorem 0.2.1
(Theorem-0.2.1-Total-Field-Superposition.md)

The theorem establishes that the total chiral field arises from additive
superposition of three pressure-modulated color fields.

Key claims verified:
1. Section 2.2 - Total Field Expression: χ_total(x) = Σ_c a_c(x) e^(iφ_c)
2. Section 2.3 - Real and Imaginary Parts decomposition
3. Section 3.3 - Energy Density: ρ(x) = a₀² Σ_c P_c(x)² > 0
4. Section 4.2 - Alternative Form: |χ_total|² = (a₀²/2)[(P_R-P_G)² + (P_G-P_B)² + (P_B-P_R)²]
5. Section 4.3 - Vanishing at Center: χ_total(0) = 0 (cube roots of unity)
6. Section 4.4 - Energy non-zero at center: ρ(0) ≠ 0
7. Section 5.2 - Gradient at Center: ∇χ_total|₀ ≠ 0
8. Section 8.2 - Total Energy Convergence: E_total < ∞

Note: The "stella octangula" refers to two interlocked tetrahedra forming an 8-vertex
structure with 6 color vertices and 2 singlet vertices.

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import json
import os
from datetime import datetime
from typing import Dict, List, Tuple, Any, Optional
from scipy.integrate import quad, tplquad


# =============================================================================
# CONSTANTS AND CONFIGURATION
# =============================================================================

# Numerical tolerance
TOL = 1e-10
TOL_INTEGRAL = 1e-6

# Regularization parameter (visualization value)
EPSILON_VIS = 0.05

# Regularization parameter (physical value from Definition 0.1.1, §12.6)
EPSILON_PHYS = 0.50

# Default epsilon for calculations
EPSILON = EPSILON_VIS

# Normalization constant (set to 1 for abstract calculations)
A0 = 1.0

# Primitive cube root of unity
OMEGA = np.exp(2j * np.pi / 3)

# Color phases (Definition 0.1.2)
PHASES = {
    'R': 0.0,
    'G': 2 * np.pi / 3,
    'B': 4 * np.pi / 3,
}

# Phase exponentials
EXP_PHASES = {
    'R': np.exp(1j * PHASES['R']),  # = 1
    'G': np.exp(1j * PHASES['G']),  # = -1/2 + i√3/2
    'B': np.exp(1j * PHASES['B']),  # = -1/2 - i√3/2
}

# Stella octangula vertices - Tetrahedron T+ (quark colors R, G, B + singlet W)
VERTICES_PLUS = {
    'R': np.array([1, 1, 1]) / np.sqrt(3),
    'G': np.array([1, -1, -1]) / np.sqrt(3),
    'B': np.array([-1, 1, -1]) / np.sqrt(3),
    'W': np.array([-1, -1, 1]) / np.sqrt(3),
}

# Tetrahedron T- (anti-quark colors R̄, Ḡ, B̄ + anti-singlet W̄)
VERTICES_MINUS = {
    'R_bar': np.array([-1, -1, -1]) / np.sqrt(3),
    'G_bar': np.array([-1, 1, 1]) / np.sqrt(3),
    'B_bar': np.array([1, -1, 1]) / np.sqrt(3),
    'W_bar': np.array([1, 1, -1]) / np.sqrt(3),
}


# =============================================================================
# CORE FUNCTIONS (Definition 0.1.3)
# =============================================================================

def pressure_function(x: np.ndarray, x_c: np.ndarray, epsilon: float = EPSILON) -> float:
    """
    Compute the pressure function P_c(x) = 1 / (|x - x_c|² + ε²)
    
    Args:
        x: Point in 3D space
        x_c: Vertex position for color c
        epsilon: Regularization parameter
        
    Returns:
        Pressure value at point x from source at x_c
    """
    dist_squared = np.sum((x - x_c)**2)
    return 1.0 / (dist_squared + epsilon**2)


def pressure_gradient(x: np.ndarray, x_c: np.ndarray, epsilon: float = EPSILON) -> np.ndarray:
    """
    Compute the gradient of pressure function: ∇P_c(x) = -2(x - x_c) / (|x - x_c|² + ε²)²
    
    Args:
        x: Point in 3D space
        x_c: Vertex position for color c
        epsilon: Regularization parameter
        
    Returns:
        Gradient vector (3D)
    """
    diff = x - x_c
    dist_squared = np.sum(diff**2)
    denominator = (dist_squared + epsilon**2)**2
    return -2 * diff / denominator


def amplitude_function(x: np.ndarray, x_c: np.ndarray, a0: float = A0, 
                       epsilon: float = EPSILON) -> float:
    """
    Compute the field amplitude a_c(x) = a_0 * P_c(x)
    
    Args:
        x: Point in 3D space
        x_c: Vertex position for color c
        a0: Normalization constant
        epsilon: Regularization parameter
        
    Returns:
        Field amplitude at point x
    """
    return a0 * pressure_function(x, x_c, epsilon)


def amplitude_gradient(x: np.ndarray, x_c: np.ndarray, a0: float = A0,
                       epsilon: float = EPSILON) -> np.ndarray:
    """
    Compute the gradient of amplitude: ∇a_c(x) = a_0 * ∇P_c(x)
    
    Args:
        x: Point in 3D space
        x_c: Vertex position for color c
        a0: Normalization constant
        epsilon: Regularization parameter
        
    Returns:
        Gradient vector (3D)
    """
    return a0 * pressure_gradient(x, x_c, epsilon)


# =============================================================================
# THEOREM 0.2.1 FUNCTIONS
# =============================================================================

def chiral_field(x: np.ndarray, color: str, a0: float = A0, 
                 epsilon: float = EPSILON) -> complex:
    """
    Compute the individual chiral field χ_c(x) = a_c(x) * e^(iφ_c)
    
    From Section 2.1:
    χ_R(x) = a_0 / (|x - x_R|² + ε²) * e^(i·0)
    χ_G(x) = a_0 / (|x - x_G|² + ε²) * e^(i·2π/3)
    χ_B(x) = a_0 / (|x - x_B|² + ε²) * e^(i·4π/3)
    
    Args:
        x: Point in 3D space
        color: Color label ('R', 'G', or 'B')
        a0: Normalization constant
        epsilon: Regularization parameter
        
    Returns:
        Complex chiral field value
    """
    amplitude = amplitude_function(x, VERTICES_PLUS[color], a0, epsilon)
    phase = PHASES[color]
    return amplitude * np.exp(1j * phase)


def total_chiral_field(x: np.ndarray, a0: float = A0, 
                       epsilon: float = EPSILON) -> complex:
    """
    Compute total chiral field χ_total(x) = Σ_c χ_c(x) = Σ_c a_c(x) e^(iφ_c)
    
    From Section 2.2:
    χ_total(x) = a_0 [ P_R + P_G·e^(i2π/3) + P_B·e^(i4π/3) ]
    
    Args:
        x: Point in 3D space
        a0: Normalization constant
        epsilon: Regularization parameter
        
    Returns:
        Complex total field value
    """
    total = 0.0 + 0.0j
    for c in ['R', 'G', 'B']:
        total += chiral_field(x, c, a0, epsilon)
    return total


def total_chiral_field_components(x: np.ndarray, a0: float = A0, 
                                   epsilon: float = EPSILON) -> Tuple[float, float]:
    """
    Compute Real and Imaginary parts of χ_total separately.
    
    From Section 2.3:
    Re[χ_total] = a_0 [ P_R - (P_G + P_B)/2 ]
    Im[χ_total] = a_0 · (√3/2)(P_G - P_B)
    
    Args:
        x: Point in 3D space
        a0: Normalization constant
        epsilon: Regularization parameter
        
    Returns:
        Tuple of (Re[χ_total], Im[χ_total])
    """
    P_R = pressure_function(x, VERTICES_PLUS['R'], epsilon)
    P_G = pressure_function(x, VERTICES_PLUS['G'], epsilon)
    P_B = pressure_function(x, VERTICES_PLUS['B'], epsilon)
    
    real_part = a0 * (P_R - 0.5 * (P_G + P_B))
    imag_part = a0 * (np.sqrt(3) / 2) * (P_G - P_B)
    
    return real_part, imag_part


def energy_density(x: np.ndarray, a0: float = A0, 
                   epsilon: float = EPSILON) -> float:
    """
    Compute the energy density ρ(x) = Σ_c |a_c(x)|² = a_0² Σ_c P_c(x)²
    
    From Section 3.2:
    This is the INCOHERENT sum (no cross-terms), not |χ_total|².
    
    Args:
        x: Point in 3D space
        a0: Normalization constant
        epsilon: Regularization parameter
        
    Returns:
        Energy density at point x
    """
    total_rho = 0.0
    for c in ['R', 'G', 'B']:
        P_c = pressure_function(x, VERTICES_PLUS[c], epsilon)
        total_rho += P_c**2
    return a0**2 * total_rho


def coherent_field_magnitude_squared(x: np.ndarray, a0: float = A0,
                                      epsilon: float = EPSILON) -> float:
    """
    Compute |χ_total|² = Re[χ]² + Im[χ]² (COHERENT magnitude, includes interference)
    
    From Section 4.1:
    |χ_total|² = a_0² [ P_R² + P_G² + P_B² - P_R·P_G - P_R·P_B - P_G·P_B ]
    
    This is DIFFERENT from ρ(x) = Σ_c |a_c|² (no cross-terms).
    
    Args:
        x: Point in 3D space
        a0: Normalization constant
        epsilon: Regularization parameter
        
    Returns:
        |χ_total(x)|²
    """
    chi = total_chiral_field(x, a0, epsilon)
    return np.abs(chi)**2


def coherent_field_magnitude_alternative(x: np.ndarray, a0: float = A0,
                                          epsilon: float = EPSILON) -> float:
    """
    Alternative form of |χ_total|² from Section 4.2:
    |χ_total|² = (a_0²/2) [ (P_R - P_G)² + (P_G - P_B)² + (P_B - P_R)² ]
    
    Args:
        x: Point in 3D space
        a0: Normalization constant
        epsilon: Regularization parameter
        
    Returns:
        |χ_total(x)|² computed via alternative formula
    """
    P_R = pressure_function(x, VERTICES_PLUS['R'], epsilon)
    P_G = pressure_function(x, VERTICES_PLUS['G'], epsilon)
    P_B = pressure_function(x, VERTICES_PLUS['B'], epsilon)
    
    result = (a0**2 / 2) * ((P_R - P_G)**2 + (P_G - P_B)**2 + (P_B - P_R)**2)
    return result


def total_field_gradient(x: np.ndarray, a0: float = A0,
                          epsilon: float = EPSILON) -> np.ndarray:
    """
    Compute gradient of total field: ∇χ_total = Σ_c e^(iφ_c) ∇a_c(x)
    
    From Section 5.1:
    ∇χ_total = -2a_0 Σ_c [(x - x_c) e^(iφ_c)] / (|x - x_c|² + ε²)²
    
    Args:
        x: Point in 3D space
        a0: Normalization constant
        epsilon: Regularization parameter
        
    Returns:
        Complex gradient vector (3D array of complex values)
    """
    gradient = np.zeros(3, dtype=complex)
    for c in ['R', 'G', 'B']:
        phase_exp = EXP_PHASES[c]
        grad_a = amplitude_gradient(x, VERTICES_PLUS[c], a0, epsilon)
        gradient += phase_exp * grad_a
    return gradient


def gradient_energy_density(x: np.ndarray, a0: float = A0,
                             epsilon: float = EPSILON) -> float:
    """
    Compute the gradient energy density |∇χ_total|²
    
    Args:
        x: Point in 3D space
        a0: Normalization constant
        epsilon: Regularization parameter
        
    Returns:
        |∇χ_total(x)|²
    """
    grad = total_field_gradient(x, a0, epsilon)
    return np.sum(np.abs(grad)**2)


# =============================================================================
# VERIFICATION FUNCTIONS
# =============================================================================

def verify_cube_roots_of_unity() -> Dict[str, Any]:
    """
    Verify the fundamental identity: 1 + ω + ω² = 0 where ω = e^(i2π/3)
    
    This is used throughout the theorem to show χ_total(0) = 0.
    """
    results = {
        'test': 'Cube Roots of Unity Sum',
        'status': True,
        'checks': []
    }
    
    # Direct sum
    omega = np.exp(2j * np.pi / 3)
    sum_roots = 1 + omega + omega**2
    
    passed = np.abs(sum_roots) < TOL
    results['checks'].append({
        'name': '1 + ω + ω² = 0',
        'expected': 0.0,
        'computed_real': float(sum_roots.real),
        'computed_imag': float(sum_roots.imag),
        'magnitude': float(np.abs(sum_roots)),
        'passed': passed
    })
    results['status'] &= passed
    
    # Using phase exponentials
    sum_exp = EXP_PHASES['R'] + EXP_PHASES['G'] + EXP_PHASES['B']
    
    passed = np.abs(sum_exp) < TOL
    results['checks'].append({
        'name': 'e^(i·0) + e^(i·2π/3) + e^(i·4π/3) = 0',
        'expected': 0.0,
        'computed_real': float(sum_exp.real),
        'computed_imag': float(sum_exp.imag),
        'magnitude': float(np.abs(sum_exp)),
        'passed': passed
    })
    results['status'] &= passed
    
    # Verify individual values
    expected_G = -0.5 + 1j * np.sqrt(3) / 2
    expected_B = -0.5 - 1j * np.sqrt(3) / 2
    
    passed_G = np.abs(EXP_PHASES['G'] - expected_G) < TOL
    passed_B = np.abs(EXP_PHASES['B'] - expected_B) < TOL
    
    results['checks'].append({
        'name': 'e^(i·2π/3) = -1/2 + i√3/2',
        'expected_real': -0.5,
        'expected_imag': np.sqrt(3) / 2,
        'computed_real': float(EXP_PHASES['G'].real),
        'computed_imag': float(EXP_PHASES['G'].imag),
        'passed': passed_G
    })
    results['status'] &= passed_G
    
    results['checks'].append({
        'name': 'e^(i·4π/3) = -1/2 - i√3/2',
        'expected_real': -0.5,
        'expected_imag': -np.sqrt(3) / 2,
        'computed_real': float(EXP_PHASES['B'].real),
        'computed_imag': float(EXP_PHASES['B'].imag),
        'passed': passed_B
    })
    results['status'] &= passed_B
    
    return results


def verify_total_field_expression() -> Dict[str, Any]:
    """
    Verify Section 2.2-2.3: Total field expression and real/imaginary parts.
    
    Tests:
    1. χ_total(x) = Σ_c a_c(x) e^(iφ_c)
    2. Re[χ_total] = a_0 [ P_R - (P_G + P_B)/2 ]
    3. Im[χ_total] = a_0 · (√3/2)(P_G - P_B)
    """
    results = {
        'test': 'Total Field Expression (Section 2.2-2.3)',
        'status': True,
        'checks': []
    }
    
    # Test at several points
    test_points = [
        ('origin', np.array([0.0, 0.0, 0.0])),
        ('x_axis', np.array([0.3, 0.0, 0.0])),
        ('y_axis', np.array([0.0, 0.3, 0.0])),
        ('diagonal', np.array([0.2, 0.2, 0.2])),
        ('near_R', np.array([0.5, 0.5, 0.5])),
        ('random', np.array([0.15, -0.25, 0.1])),
    ]
    
    for name, x in test_points:
        # Method 1: Direct superposition
        chi_direct = total_chiral_field(x, A0, EPSILON)
        
        # Method 2: Real/Imag parts formula
        re_chi, im_chi = total_chiral_field_components(x, A0, EPSILON)
        chi_components = re_chi + 1j * im_chi
        
        # Compare
        diff = np.abs(chi_direct - chi_components)
        passed = diff < TOL
        
        results['checks'].append({
            'name': f'χ_total at {name}',
            'direct_real': float(chi_direct.real),
            'direct_imag': float(chi_direct.imag),
            'formula_real': float(re_chi),
            'formula_imag': float(im_chi),
            'difference': float(diff),
            'passed': passed
        })
        results['status'] &= passed
    
    return results


def verify_vanishing_at_center() -> Dict[str, Any]:
    """
    Verify Section 4.3: χ_total(0) = 0 due to cube roots of unity.
    
    At the center, P_R(0) = P_G(0) = P_B(0) = P_0, so:
    χ_total(0) = a_0 P_0 (1 + e^(i2π/3) + e^(i4π/3)) = a_0 P_0 · 0 = 0
    """
    results = {
        'test': 'Vanishing at Center (Section 4.3)',
        'status': True,
        'checks': []
    }
    
    origin = np.array([0.0, 0.0, 0.0])
    
    # Verify pressures are equal at center
    P_R = pressure_function(origin, VERTICES_PLUS['R'], EPSILON)
    P_G = pressure_function(origin, VERTICES_PLUS['G'], EPSILON)
    P_B = pressure_function(origin, VERTICES_PLUS['B'], EPSILON)
    
    P_0_expected = 1.0 / (1.0 + EPSILON**2)
    
    passed_R = np.abs(P_R - P_0_expected) < TOL
    passed_G = np.abs(P_G - P_0_expected) < TOL
    passed_B = np.abs(P_B - P_0_expected) < TOL
    passed_equal = np.abs(P_R - P_G) < TOL and np.abs(P_G - P_B) < TOL
    
    results['checks'].append({
        'name': 'P_R(0) = P_G(0) = P_B(0) = 1/(1+ε²)',
        'P_R': float(P_R),
        'P_G': float(P_G),
        'P_B': float(P_B),
        'expected': float(P_0_expected),
        'all_equal': passed_equal,
        'passed': passed_R and passed_G and passed_B and passed_equal
    })
    results['status'] &= (passed_R and passed_G and passed_B and passed_equal)
    
    # Verify χ_total(0) = 0
    chi_center = total_chiral_field(origin, A0, EPSILON)
    
    passed_vanish = np.abs(chi_center) < TOL
    results['checks'].append({
        'name': 'χ_total(0) = 0',
        'computed_real': float(chi_center.real),
        'computed_imag': float(chi_center.imag),
        'magnitude': float(np.abs(chi_center)),
        'expected': 0.0,
        'passed': passed_vanish
    })
    results['status'] &= passed_vanish
    
    # Also check |χ_total(0)|² = 0 via alternative formula
    chi_sq_alt = coherent_field_magnitude_alternative(origin, A0, EPSILON)
    
    passed_alt = np.abs(chi_sq_alt) < TOL
    results['checks'].append({
        'name': '|χ_total(0)|² via alternative formula = 0',
        'computed': float(chi_sq_alt),
        'expected': 0.0,
        'passed': passed_alt
    })
    results['status'] &= passed_alt
    
    return results


def verify_energy_density() -> Dict[str, Any]:
    """
    Verify Section 3.2-3.4: Energy density ρ(x) = a_0² Σ_c P_c(x)²
    
    Key points:
    1. ρ(x) > 0 for all x (positive definite)
    2. ρ(0) ≠ 0 even though χ_total(0) = 0
    3. ρ at vertices is much larger than at center
    """
    results = {
        'test': 'Energy Density (Section 3.2-3.4)',
        'status': True,
        'checks': []
    }
    
    origin = np.array([0.0, 0.0, 0.0])
    
    # Check 1: ρ(0) > 0 even though χ_total(0) = 0
    rho_center = energy_density(origin, A0, EPSILON)
    chi_center_sq = coherent_field_magnitude_squared(origin, A0, EPSILON)
    
    # Expected: ρ(0) = 3a_0²P_0² = 3/(1+ε²)²
    P_0 = 1.0 / (1.0 + EPSILON**2)
    expected_rho_center = 3 * A0**2 * P_0**2
    
    passed_rho = np.abs(rho_center - expected_rho_center) < TOL
    passed_chi = np.abs(chi_center_sq) < TOL  # should be zero
    
    results['checks'].append({
        'name': 'ρ(0) = 3a_0²P_0² > 0',
        'computed': float(rho_center),
        'expected': float(expected_rho_center),
        'passed': passed_rho
    })
    results['status'] &= passed_rho
    
    results['checks'].append({
        'name': '|χ_total(0)|² = 0 (but ρ(0) ≠ 0)',
        'rho_center': float(rho_center),
        'chi_sq_center': float(chi_center_sq),
        'rho_nonzero': rho_center > 0,
        'chi_sq_zero': chi_center_sq < TOL,
        'passed': passed_chi and rho_center > 0
    })
    results['status'] &= (passed_chi and rho_center > 0)
    
    # Check 2: ρ at vertex is much larger
    x_R = VERTICES_PLUS['R']
    rho_vertex = energy_density(x_R, A0, EPSILON)
    
    # At x_R: P_R(x_R) = 1/ε², so ρ(x_R) ≈ a_0²/ε⁴
    expected_rho_vertex_dominant = A0**2 / EPSILON**4
    
    # ρ(x_R) >> ρ(0)
    ratio = rho_vertex / rho_center
    
    results['checks'].append({
        'name': 'ρ(x_R) >> ρ(0)',
        'rho_vertex': float(rho_vertex),
        'rho_center': float(rho_center),
        'ratio': float(ratio),
        'passed': ratio > 10  # Should be much larger
    })
    results['status'] &= (ratio > 10)
    
    # Check 3: ρ(x) > 0 at random points
    random_points = [
        np.array([0.1, 0.2, 0.3]),
        np.array([-0.2, 0.1, -0.1]),
        np.array([0.4, -0.3, 0.2]),
    ]
    
    all_positive = True
    rho_values = []
    for pt in random_points:
        rho = energy_density(pt, A0, EPSILON)
        rho_values.append(float(rho))
        all_positive &= (rho > 0)
    
    results['checks'].append({
        'name': 'ρ(x) > 0 at random points',
        'rho_values': rho_values,
        'all_positive': all_positive,
        'passed': all_positive
    })
    results['status'] &= all_positive
    
    return results


def verify_alternative_form() -> Dict[str, Any]:
    """
    Verify Section 4.2: Alternative form of |χ_total|²
    
    |χ_total|² = (a_0²/2) [ (P_R - P_G)² + (P_G - P_B)² + (P_B - P_R)² ]
    
    This should equal |χ_total|² computed directly.
    """
    results = {
        'test': 'Alternative Form (Section 4.2)',
        'status': True,
        'checks': []
    }
    
    # Test at several points
    test_points = [
        ('origin', np.array([0.0, 0.0, 0.0])),
        ('x_axis', np.array([0.3, 0.0, 0.0])),
        ('diagonal', np.array([0.2, 0.2, 0.2])),
        ('near_R', np.array([0.5, 0.5, 0.5])),
        ('random', np.array([0.15, -0.25, 0.1])),
    ]
    
    for name, x in test_points:
        # Method 1: Direct |χ_total|²
        chi_sq_direct = coherent_field_magnitude_squared(x, A0, EPSILON)
        
        # Method 2: Alternative formula
        chi_sq_alt = coherent_field_magnitude_alternative(x, A0, EPSILON)
        
        # Compare
        diff = np.abs(chi_sq_direct - chi_sq_alt)
        # Use relative tolerance for non-zero values
        if chi_sq_direct > TOL:
            rel_diff = diff / chi_sq_direct
            passed = rel_diff < 1e-10
        else:
            passed = diff < TOL
        
        results['checks'].append({
            'name': f'|χ_total|² at {name}',
            'direct': float(chi_sq_direct),
            'alternative': float(chi_sq_alt),
            'difference': float(diff),
            'passed': passed
        })
        results['status'] &= passed
    
    return results


def verify_gradient_at_center() -> Dict[str, Any]:
    """
    Verify Section 5.2: Gradient at center is NON-ZERO.
    
    Even though χ_total(0) = 0, we have ∇χ_total|₀ ≠ 0.
    This is crucial for the phase-gradient mass generation mechanism.
    """
    results = {
        'test': 'Gradient at Center (Section 5.2)',
        'status': True,
        'checks': []
    }
    
    origin = np.array([0.0, 0.0, 0.0])
    
    # Compute gradient at center
    grad = total_field_gradient(origin, A0, EPSILON)
    grad_magnitude_sq = gradient_energy_density(origin, A0, EPSILON)
    
    # The gradient should be non-zero
    is_nonzero = grad_magnitude_sq > TOL
    
    results['checks'].append({
        'name': '|∇χ_total|₀|² > 0',
        'gradient_x_real': float(grad[0].real),
        'gradient_x_imag': float(grad[0].imag),
        'gradient_y_real': float(grad[1].real),
        'gradient_y_imag': float(grad[1].imag),
        'gradient_z_real': float(grad[2].real),
        'gradient_z_imag': float(grad[2].imag),
        'gradient_magnitude_sq': float(grad_magnitude_sq),
        'is_nonzero': is_nonzero,
        'passed': is_nonzero
    })
    results['status'] &= is_nonzero
    
    # Verify the analytical formula from Section 5.2
    # At x = 0: ∇χ_total = 2a_0 P_0² Σ_c x_c e^(iφ_c)
    P_0 = 1.0 / (1.0 + EPSILON**2)
    
    sum_x_weighted = np.zeros(3, dtype=complex)
    for c in ['R', 'G', 'B']:
        sum_x_weighted += VERTICES_PLUS[c] * EXP_PHASES[c]
    
    expected_grad = 2 * A0 * P_0**2 * sum_x_weighted
    
    diff = np.linalg.norm(grad - expected_grad)
    passed = diff < TOL
    
    results['checks'].append({
        'name': '∇χ_total|₀ = 2a_0 P_0² Σ_c x_c e^(iφ_c)',
        'computed_x': [float(grad[0].real), float(grad[0].imag)],
        'expected_x': [float(expected_grad[0].real), float(expected_grad[0].imag)],
        'difference': float(diff),
        'passed': passed
    })
    results['status'] &= passed
    
    return results


def verify_energy_integral_convergence() -> Dict[str, Any]:
    """
    Verify Section 8.2: Total energy integral converges.
    
    E_total = ∫_Ω d³x ρ(x) < ∞
    
    The integral converges because P_c² ~ 1/r⁴ at large r.
    """
    results = {
        'test': 'Energy Integral Convergence (Section 8.2)',
        'status': True,
        'checks': []
    }
    
    # Test the 1D integral for a single pressure source
    # ∫₀^R 4πr² dr / (r² + ε²)² = (π²/ε) as R → ∞
    
    def integrand_1d(r, eps):
        """Radial integrand: 4πr² / (r² + ε²)²"""
        return 4 * np.pi * r**2 / (r**2 + eps**2)**2
    
    # Numerical integration
    for eps in [EPSILON_VIS, EPSILON_PHYS]:
        # Integrate to large but finite R
        R_max = 100.0
        result, error = quad(integrand_1d, 0, R_max, args=(eps,))
        
        # Expected result: π²/ε
        expected = np.pi**2 / eps
        
        # Should approach expected as R_max → ∞
        rel_diff = np.abs(result - expected) / expected
        passed = rel_diff < 0.01  # Within 1%
        
        results['checks'].append({
            'name': f'∫₀^R 4πr²/(r²+ε²)² dr ≈ π²/ε (ε={eps})',
            'computed': float(result),
            'expected_limit': float(expected),
            'relative_difference': float(rel_diff),
            'passed': passed
        })
        results['status'] &= passed
    
    # Verify scaling: E_total ~ a_0²/ε
    eps1 = 0.05
    eps2 = 0.10
    
    R_max = 50.0
    E1, _ = quad(integrand_1d, 0, R_max, args=(eps1,))
    E2, _ = quad(integrand_1d, 0, R_max, args=(eps2,))
    
    # E ∝ 1/ε, so E1/E2 ≈ ε2/ε1
    expected_ratio = eps2 / eps1
    computed_ratio = E1 / E2
    
    rel_diff = np.abs(computed_ratio - expected_ratio) / expected_ratio
    passed = rel_diff < 0.1  # Within 10%
    
    results['checks'].append({
        'name': 'Energy scaling: E ∝ 1/ε',
        'E1': float(E1),
        'E2': float(E2),
        'computed_ratio': float(computed_ratio),
        'expected_ratio': float(expected_ratio),
        'passed': passed
    })
    results['status'] &= passed
    
    return results


def verify_coherent_vs_incoherent() -> Dict[str, Any]:
    """
    Verify the critical distinction between coherent and incoherent sums.
    
    - |χ_total|² includes interference (coherent)
    - ρ = Σ_c |a_c|² has no interference (incoherent)
    - At center: |χ_total(0)|² = 0 but ρ(0) ≠ 0
    """
    results = {
        'test': 'Coherent vs Incoherent Sums (Section 3.0)',
        'status': True,
        'checks': []
    }
    
    # Test at several points
    test_points = [
        ('center', np.array([0.0, 0.0, 0.0])),
        ('off_center', np.array([0.2, 0.0, 0.0])),
        ('diagonal', np.array([0.1, 0.1, 0.1])),
    ]
    
    for name, x in test_points:
        # Coherent: |χ_total|²
        chi_sq = coherent_field_magnitude_squared(x, A0, EPSILON)
        
        # Incoherent: ρ = Σ_c |a_c|²
        rho = energy_density(x, A0, EPSILON)
        
        # The difference is due to interference terms
        # ρ - |χ_total|² = interference contribution
        interference = rho - chi_sq
        
        results['checks'].append({
            'name': f'at {name}',
            'coherent_chi_sq': float(chi_sq),
            'incoherent_rho': float(rho),
            'interference_terms': float(interference),
            'rho_geq_zero': rho >= 0,
        })
    
    # Key check: at center, χ_total = 0 but ρ ≠ 0
    origin = np.array([0.0, 0.0, 0.0])
    chi_sq_center = coherent_field_magnitude_squared(origin, A0, EPSILON)
    rho_center = energy_density(origin, A0, EPSILON)
    
    passed = (chi_sq_center < TOL) and (rho_center > TOL)
    results['checks'].append({
        'name': 'Critical: |χ_total(0)|² = 0 but ρ(0) > 0',
        'chi_sq_center': float(chi_sq_center),
        'rho_center': float(rho_center),
        'passed': passed
    })
    results['status'] &= passed
    
    return results


def verify_time_independence() -> Dict[str, Any]:
    """
    Verify Section 6: All quantities defined without external time.
    
    Check that the construction uses only:
    1. Vertex positions (geometric)
    2. Pressure functions (spatial only)
    3. Relative phases (fixed constants)
    4. Normalization constant
    """
    results = {
        'test': 'Time Independence (Section 6)',
        'status': True,
        'checks': []
    }
    
    # Verify vertex positions are pure geometry (constant)
    all_const = True
    for c in ['R', 'G', 'B']:
        v = VERTICES_PLUS[c]
        # Check these are constant arrays
        all_const &= isinstance(v, np.ndarray) and v.shape == (3,)
    
    results['checks'].append({
        'name': 'Vertex positions are constant vectors',
        'passed': all_const
    })
    results['status'] &= all_const
    
    # Verify phases are constants
    phase_const = all(isinstance(p, (int, float)) for p in PHASES.values())
    results['checks'].append({
        'name': 'Phases are constants (no time dependence)',
        'phases': {k: float(v) for k, v in PHASES.items()},
        'passed': phase_const
    })
    results['status'] &= phase_const
    
    # Verify field at same point gives same result (no stochastic time dependence)
    x = np.array([0.2, 0.1, 0.3])
    chi1 = total_chiral_field(x, A0, EPSILON)
    chi2 = total_chiral_field(x, A0, EPSILON)
    
    passed = np.abs(chi1 - chi2) < TOL
    results['checks'].append({
        'name': 'Field at same point gives same value',
        'chi1': [float(chi1.real), float(chi1.imag)],
        'chi2': [float(chi2.real), float(chi2.imag)],
        'passed': passed
    })
    results['status'] &= passed
    
    return results


def verify_special_point_values() -> Dict[str, Any]:
    """
    Verify Section 3.4: Energy density at special points.
    
    - At center: ρ(0) = 3a_0² / (1 + ε²)²
    - At vertex: ρ(x_R) ≈ a_0² / ε⁴ >> ρ(0)
    """
    results = {
        'test': 'Special Point Values (Section 3.4)',
        'status': True,
        'checks': []
    }
    
    origin = np.array([0.0, 0.0, 0.0])
    
    # Center energy density
    rho_center = energy_density(origin, A0, EPSILON)
    P_0 = 1.0 / (1.0 + EPSILON**2)
    expected_center = 3 * A0**2 * P_0**2
    
    passed_center = np.abs(rho_center - expected_center) < TOL
    results['checks'].append({
        'name': 'ρ(0) = 3a_0² / (1 + ε²)²',
        'computed': float(rho_center),
        'expected': float(expected_center),
        'passed': passed_center
    })
    results['status'] &= passed_center
    
    # Vertex energy density
    x_R = VERTICES_PLUS['R']
    rho_vertex = energy_density(x_R, A0, EPSILON)
    
    # P_R(x_R) = 1/ε², other pressures are approximately 1/(8/3 + ε²)
    P_R_at_R = 1.0 / EPSILON**2
    # Distance from R to G is sqrt(8/3)
    dist_sq_RG = np.sum((VERTICES_PLUS['R'] - VERTICES_PLUS['G'])**2)
    P_G_at_R = 1.0 / (dist_sq_RG + EPSILON**2)
    P_B_at_R = 1.0 / (np.sum((VERTICES_PLUS['R'] - VERTICES_PLUS['B'])**2) + EPSILON**2)
    
    expected_vertex = A0**2 * (P_R_at_R**2 + P_G_at_R**2 + P_B_at_R**2)
    
    rel_diff = np.abs(rho_vertex - expected_vertex) / expected_vertex
    passed_vertex = rel_diff < 1e-10
    
    results['checks'].append({
        'name': 'ρ(x_R) at vertex',
        'computed': float(rho_vertex),
        'expected': float(expected_vertex),
        'passed': passed_vertex
    })
    results['status'] &= passed_vertex
    
    # Verify ρ(x_R) >> ρ(0)
    ratio = rho_vertex / rho_center
    passed_ratio = ratio > 100  # Should be much larger for small ε
    
    results['checks'].append({
        'name': 'ρ(x_R) >> ρ(0) for small ε',
        'ratio': float(ratio),
        'epsilon': float(EPSILON),
        'passed': passed_ratio
    })
    results['status'] &= passed_ratio
    
    return results


def verify_downstream_compatibility() -> Dict[str, Any]:
    """
    Verify Section 9 and 13: Compatibility with downstream theorems.
    
    Check that this theorem provides what downstream theorems need:
    - Theorem 0.2.2: χ_total superposition form
    - Theorem 0.2.3: Center node property
    - Theorem 0.2.4: Energy density ρ(x)
    - Theorem 3.1.1: Non-zero gradient at center
    """
    results = {
        'test': 'Downstream Compatibility (Section 9, 13)',
        'status': True,
        'checks': []
    }
    
    origin = np.array([0.0, 0.0, 0.0])
    
    # For Theorem 0.2.2: χ_total is well-defined complex field
    chi = total_chiral_field(origin, A0, EPSILON)
    passed_complex = isinstance(chi, (complex, np.complexfloating))
    results['checks'].append({
        'name': 'χ_total is complex (for Theorem 0.2.2)',
        'type': str(type(chi)),
        'passed': passed_complex
    })
    results['status'] &= passed_complex
    
    # For Theorem 0.2.3: Center node property
    passed_node = np.abs(chi) < TOL
    results['checks'].append({
        'name': 'χ_total(0) = 0 (for Theorem 0.2.3)',
        'chi_at_center': [float(chi.real), float(chi.imag)],
        'passed': passed_node
    })
    results['status'] &= passed_node
    
    # For Theorem 0.2.4: ρ(x) is positive definite
    rho = energy_density(origin, A0, EPSILON)
    passed_positive = rho > 0
    results['checks'].append({
        'name': 'ρ(0) > 0 (for Theorem 0.2.4)',
        'rho_at_center': float(rho),
        'passed': passed_positive
    })
    results['status'] &= passed_positive
    
    # For Theorem 3.1.1: Non-zero gradient enables phase-gradient mass
    grad = total_field_gradient(origin, A0, EPSILON)
    grad_mag_sq = np.sum(np.abs(grad)**2)
    passed_grad = grad_mag_sq > TOL
    results['checks'].append({
        'name': '|∇χ_total|₀ ≠ 0 (for Theorem 3.1.1)',
        'gradient_magnitude_sq': float(grad_mag_sq),
        'passed': passed_grad
    })
    results['status'] &= passed_grad
    
    return results


# =============================================================================
# MAIN EXECUTION
# =============================================================================

def convert_to_serializable(obj):
    """Convert numpy types to Python native types for JSON serialization."""
    if isinstance(obj, dict):
        return {k: convert_to_serializable(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [convert_to_serializable(v) for v in obj]
    elif isinstance(obj, (np.bool_, np.integer)):
        return int(obj)
    elif isinstance(obj, np.floating):
        return float(obj)
    elif isinstance(obj, np.ndarray):
        return obj.tolist()
    elif isinstance(obj, bool):
        return bool(obj)
    else:
        return obj


def run_all_verifications() -> Dict[str, Any]:
    """
    Run all verification tests for Theorem 0.2.1.
    """
    all_results = {
        'theorem': 'Theorem 0.2.1: Total Field from Superposition',
        'file': 'Theorem-0.2.1-Total-Field-Superposition.md',
        'timestamp': datetime.now().isoformat(),
        'epsilon_vis': EPSILON_VIS,
        'epsilon_phys': EPSILON_PHYS,
        'a0': A0,
        'overall_status': True,
        'tests': []
    }
    
    # Run all verification tests
    verifications = [
        verify_cube_roots_of_unity,
        verify_total_field_expression,
        verify_vanishing_at_center,
        verify_energy_density,
        verify_alternative_form,
        verify_gradient_at_center,
        verify_energy_integral_convergence,
        verify_coherent_vs_incoherent,
        verify_time_independence,
        verify_special_point_values,
        verify_downstream_compatibility,
    ]
    
    for verification in verifications:
        print(f"Running: {verification.__name__}...")
        result = verification()
        all_results['tests'].append(result)
        all_results['overall_status'] &= result['status']
        
        status_str = "✅ PASSED" if result['status'] else "❌ FAILED"
        print(f"  {status_str}: {result['test']}")
    
    return all_results


def main():
    """Main entry point."""
    print("=" * 70)
    print("Theorem 0.2.1: Total Field from Superposition - Verification")
    print("=" * 70)
    print()
    
    # Run all verifications
    results = run_all_verifications()
    
    print()
    print("=" * 70)
    overall = "✅ ALL TESTS PASSED" if results['overall_status'] else "❌ SOME TESTS FAILED"
    print(f"OVERALL RESULT: {overall}")
    print("=" * 70)
    
    # Save results to JSON
    output_dir = os.path.dirname(os.path.abspath(__file__))
    output_file = os.path.join(output_dir, 'theorem_0_2_1_total_field_superposition_results.json')
    
    # Convert to JSON-serializable format
    serializable_results = convert_to_serializable(results)
    
    with open(output_file, 'w') as f:
        json.dump(serializable_results, f, indent=2)
    
    print(f"\nResults saved to: {output_file}")
    
    return results


if __name__ == "__main__":
    main()
