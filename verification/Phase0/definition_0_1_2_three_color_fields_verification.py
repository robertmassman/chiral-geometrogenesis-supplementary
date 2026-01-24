#!/usr/bin/env python3
"""
Numerical Verification: Definition 0.1.2 - Three Color Fields with Relative Phases

This script verifies the mathematical claims in Definition 0.1.2
(Definition-0.1.2-Three-Color-Fields-Relative-Phases.md)

The stella octangula consists of two interlocked tetrahedra (dual simplices).

Key claims verified:
1. Section 2.3 - Weight Vector Geometry: 120° angular separation
2. Section 2.5 - Uniqueness Theorem: Phase assignment is unique
3. Section 3.1 - Cube Roots of Unity: Algebraic properties
4. Section 3.2 - Color Neutrality Condition: 1 + ω + ω² = 0
5. Section 4 - Anti-Color Phases: Complex conjugate relationships
6. Section 7 - SU(3) Generator Connection: Gell-Mann matrix eigenvalues
7. Section 8 - Key Theorems: Phase sum, product, cyclic symmetry

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


# =============================================================================
# CONSTANTS AND CONFIGURATION
# =============================================================================

# Numerical tolerance
TOL = 1e-12

# Primitive cube root of unity
OMEGA = np.exp(2j * np.pi / 3)

# Color phases (Definition 0.1.2)
PHASES = {
    'R': 0.0,
    'G': 2 * np.pi / 3,
    'B': 4 * np.pi / 3,
}

# Anti-color phases
ANTI_PHASES = {
    'R_bar': 0.0,
    'G_bar': 4 * np.pi / 3,  # -2π/3 mod 2π = 4π/3
    'B_bar': 2 * np.pi / 3,  # -4π/3 mod 2π = 2π/3
}

# SU(3) Weight vectors for fundamental representation (T₃, T₈ basis)
WEIGHT_VECTORS = {
    'R': np.array([0.5, 1 / (2 * np.sqrt(3))]),
    'G': np.array([-0.5, 1 / (2 * np.sqrt(3))]),
    'B': np.array([0.0, -1 / np.sqrt(3)]),
}

# Gell-Mann matrices (λ₁ through λ₈)
GELL_MANN = {
    'lambda_1': np.array([[0, 1, 0], [1, 0, 0], [0, 0, 0]], dtype=complex),
    'lambda_2': np.array([[0, -1j, 0], [1j, 0, 0], [0, 0, 0]], dtype=complex),
    'lambda_3': np.array([[1, 0, 0], [0, -1, 0], [0, 0, 0]], dtype=complex),
    'lambda_4': np.array([[0, 0, 1], [0, 0, 0], [1, 0, 0]], dtype=complex),
    'lambda_5': np.array([[0, 0, -1j], [0, 0, 0], [1j, 0, 0]], dtype=complex),
    'lambda_6': np.array([[0, 0, 0], [0, 0, 1], [0, 1, 0]], dtype=complex),
    'lambda_7': np.array([[0, 0, 0], [0, 0, -1j], [0, 1j, 0]], dtype=complex),
    'lambda_8': np.array([[1, 0, 0], [0, 1, 0], [0, 0, -2]], dtype=complex) / np.sqrt(3),
}

# Cartan generators T_a = λ_a / 2
T3 = GELL_MANN['lambda_3'] / 2
T8 = GELL_MANN['lambda_8'] / 2

# Color eigenstates
COLOR_STATES = {
    'R': np.array([1, 0, 0], dtype=complex),
    'G': np.array([0, 1, 0], dtype=complex),
    'B': np.array([0, 0, 1], dtype=complex),
}


# =============================================================================
# VERIFICATION FUNCTIONS
# =============================================================================

def verify_cube_roots_of_unity() -> Dict[str, Any]:
    """
    Verify Section 3.1: Algebraic Properties of Cube Roots of Unity.
    
    Properties to verify:
    1. Product: 1 · ω · ω² = 1
    2. Sum: 1 + ω + ω² = 0
    3. Conjugation: ω̄ = ω²
    4. Powers: ω³ = 1, ω⁴ = ω, etc.
    5. Explicit values: ω = -1/2 + i√3/2
    """
    results = {
        'test': 'Cube Roots of Unity (Section 3.1)',
        'status': True,
        'checks': []
    }
    
    # Define cube roots
    omega = OMEGA
    omega_sq = omega ** 2
    
    # Check 1: Product
    product = 1 * omega * omega_sq
    product_check = np.abs(product - 1.0) < TOL
    results['checks'].append({
        'name': 'Product: 1·ω·ω² = 1',
        'expected': 1.0,
        'computed': float(np.real(product)),
        'passed': product_check
    })
    results['status'] &= product_check
    
    # Check 2: Sum (Color Neutrality)
    sum_roots = 1 + omega + omega_sq
    sum_check = np.abs(sum_roots) < TOL
    results['checks'].append({
        'name': 'Sum: 1 + ω + ω² = 0',
        'expected': 0.0,
        'computed': float(np.abs(sum_roots)),
        'passed': sum_check
    })
    results['status'] &= sum_check
    
    # Check 3: Conjugation
    omega_conj = np.conj(omega)
    conj_check = np.abs(omega_conj - omega_sq) < TOL
    results['checks'].append({
        'name': 'Conjugation: ω̄ = ω²',
        'expected': f'{omega_sq:.6f}',
        'computed': f'{omega_conj:.6f}',
        'passed': conj_check
    })
    results['status'] &= conj_check
    
    # Check 4: Powers
    power_checks = []
    omega3 = omega ** 3
    power_checks.append(('ω³ = 1', omega3, 1.0))
    omega4 = omega ** 4
    power_checks.append(('ω⁴ = ω', omega4, omega))
    omega5 = omega ** 5
    power_checks.append(('ω⁵ = ω²', omega5, omega_sq))
    omega6 = omega ** 6
    power_checks.append(('ω⁶ = 1', omega6, 1.0))
    
    for name, computed, expected in power_checks:
        check_passed = np.abs(computed - expected) < TOL
        results['checks'].append({
            'name': f'Power: {name}',
            'expected': f'{expected:.6f}',
            'computed': f'{computed:.6f}',
            'passed': check_passed
        })
        results['status'] &= check_passed
    
    # Check 5: Explicit values
    omega_explicit = -0.5 + 1j * np.sqrt(3) / 2
    omega_sq_explicit = -0.5 - 1j * np.sqrt(3) / 2
    
    explicit_check1 = np.abs(omega - omega_explicit) < TOL
    explicit_check2 = np.abs(omega_sq - omega_sq_explicit) < TOL
    
    results['checks'].append({
        'name': 'Explicit ω = -1/2 + i√3/2',
        'expected': f'{omega_explicit:.6f}',
        'computed': f'{omega:.6f}',
        'passed': explicit_check1
    })
    results['checks'].append({
        'name': 'Explicit ω² = -1/2 - i√3/2',
        'expected': f'{omega_sq_explicit:.6f}',
        'computed': f'{omega_sq:.6f}',
        'passed': explicit_check2
    })
    results['status'] &= explicit_check1 and explicit_check2
    
    return results


def verify_weight_vector_geometry() -> Dict[str, Any]:
    """
    Verify Section 2.3: Weight Vector Geometry.
    
    Claims to verify:
    1. Weight vectors form equilateral triangle centered at origin
    2. All angles between weight vectors are 120°
    3. All weight vector magnitudes are equal (1/√3)
    """
    results = {
        'test': 'Weight Vector Geometry (Section 2.3)',
        'status': True,
        'checks': []
    }
    
    w_R = WEIGHT_VECTORS['R']
    w_G = WEIGHT_VECTORS['G']
    w_B = WEIGHT_VECTORS['B']
    
    # Check 1: Magnitudes
    mag_R = np.linalg.norm(w_R)
    mag_G = np.linalg.norm(w_G)
    mag_B = np.linalg.norm(w_B)
    expected_mag = 1 / np.sqrt(3)
    
    mag_check = (np.abs(mag_R - expected_mag) < TOL and 
                 np.abs(mag_G - expected_mag) < TOL and 
                 np.abs(mag_B - expected_mag) < TOL)
    
    results['checks'].append({
        'name': 'Weight magnitudes |w| = 1/√3 ≈ 0.5774',
        'expected': expected_mag,
        'computed': {'R': mag_R, 'G': mag_G, 'B': mag_B},
        'passed': mag_check
    })
    results['status'] &= mag_check
    
    # Check 2: Dot products
    dot_RG = np.dot(w_R, w_G)
    dot_GB = np.dot(w_G, w_B)
    dot_BR = np.dot(w_B, w_R)
    expected_dot = -1/6  # From document: w_R · w_G = -1/6
    
    dot_check = (np.abs(dot_RG - expected_dot) < TOL and
                 np.abs(dot_GB - expected_dot) < TOL and
                 np.abs(dot_BR - expected_dot) < TOL)
    
    results['checks'].append({
        'name': 'Weight dot products = -1/6',
        'expected': expected_dot,
        'computed': {'R·G': dot_RG, 'G·B': dot_GB, 'B·R': dot_BR},
        'passed': dot_check
    })
    results['status'] &= dot_check
    
    # Check 3: Angular separation
    cos_RG = dot_RG / (mag_R * mag_G)
    cos_GB = dot_GB / (mag_G * mag_B)
    cos_BR = dot_BR / (mag_B * mag_R)
    expected_cos = -0.5  # cos(120°) = -1/2
    
    angle_check = (np.abs(cos_RG - expected_cos) < TOL and
                   np.abs(cos_GB - expected_cos) < TOL and
                   np.abs(cos_BR - expected_cos) < TOL)
    
    angles = {
        'θ_RG': np.degrees(np.arccos(cos_RG)),
        'θ_GB': np.degrees(np.arccos(cos_GB)),
        'θ_BR': np.degrees(np.arccos(cos_BR)),
    }
    
    results['checks'].append({
        'name': 'Angular separation = 120° (cos θ = -1/2)',
        'expected': {'cos': expected_cos, 'angle_deg': 120.0},
        'computed': {'cos_values': {'RG': cos_RG, 'GB': cos_GB, 'BR': cos_BR}, 
                     'angles_deg': angles},
        'passed': angle_check
    })
    results['status'] &= angle_check
    
    # Check 4: Centroid at origin
    centroid = (w_R + w_G + w_B) / 3
    centroid_check = np.linalg.norm(centroid) < TOL
    
    results['checks'].append({
        'name': 'Centroid at origin',
        'expected': [0.0, 0.0],
        'computed': centroid.tolist(),
        'passed': centroid_check
    })
    results['status'] &= centroid_check
    
    return results


def verify_phase_uniqueness() -> Dict[str, Any]:
    """
    Verify Section 2.5: Uniqueness Theorem.
    
    The phase assignment (0, 2π/3, 4π/3) is unique up to:
    1. Overall phase rotation
    2. Choice of reference color
    
    Must satisfy three axioms:
    1. Z₃ cyclic symmetry: φ_{c+1} - φ_c = const
    2. Color neutrality: Σ e^{iφ_c} = 0
    3. Minimality: smallest non-trivial angles
    """
    results = {
        'test': 'Phase Uniqueness (Section 2.5)',
        'status': True,
        'checks': []
    }
    
    phi_R = PHASES['R']
    phi_G = PHASES['G']
    phi_B = PHASES['B']
    
    # Check 1: Z₃ cyclic symmetry - equal spacing
    delta_GR = phi_G - phi_R
    delta_BG = phi_B - phi_G
    delta_RB = (phi_R - phi_B) % (2 * np.pi)  # Wrap to [0, 2π)
    
    spacing_check = (np.abs(delta_GR - 2*np.pi/3) < TOL and
                     np.abs(delta_BG - 2*np.pi/3) < TOL and
                     np.abs(delta_RB - 2*np.pi/3) < TOL)
    
    results['checks'].append({
        'name': 'Z₃ symmetry: equal phase spacing Δφ = 2π/3',
        'expected': 2*np.pi/3,
        'computed': {'G-R': delta_GR, 'B-G': delta_BG, 'R-B (mod 2π)': delta_RB},
        'passed': spacing_check
    })
    results['status'] &= spacing_check
    
    # Check 2: Color neutrality
    phase_sum = np.exp(1j * phi_R) + np.exp(1j * phi_G) + np.exp(1j * phi_B)
    neutrality_check = np.abs(phase_sum) < TOL
    
    results['checks'].append({
        'name': 'Color neutrality: e^{iφ_R} + e^{iφ_G} + e^{iφ_B} = 0',
        'expected': 0.0,
        'computed': float(np.abs(phase_sum)),
        'passed': neutrality_check
    })
    results['status'] &= neutrality_check
    
    # Check 3: Verify the algebraic derivation from document
    # The sum 1 + e^{iΔφ} + e^{2iΔφ} = 0 only for Δφ = 2πk/3, k=1,2
    def check_neutrality_for_delta(delta):
        return np.abs(1 + np.exp(1j * delta) + np.exp(2j * delta)) < TOL
    
    # Test multiple values
    delta_values = {
        '2π/3 (k=1)': 2*np.pi/3,
        '4π/3 (k=2)': 4*np.pi/3,
        'π/3 (invalid)': np.pi/3,
        'π/2 (invalid)': np.pi/2,
        'π (invalid)': np.pi,
    }
    
    for name, delta in delta_values.items():
        is_valid = check_neutrality_for_delta(delta)
        expected_valid = 'invalid' not in name
        check_passed = is_valid == expected_valid
        
        results['checks'].append({
            'name': f'Δφ = {name}: satisfies neutrality = {expected_valid}',
            'expected': expected_valid,
            'computed': is_valid,
            'passed': check_passed
        })
        results['status'] &= check_passed
    
    # Check 4: k=1 and k=2 are equivalent (reversed ordering)
    # k=2 gives R→B→G instead of R→G→B
    k1_phases = (0, 2*np.pi/3, 4*np.pi/3)
    k2_phases = (0, 4*np.pi/3, 2*np.pi/3)  # Reversed order
    
    # Both satisfy color neutrality
    sum_k1 = sum(np.exp(1j * p) for p in k1_phases)
    sum_k2 = sum(np.exp(1j * p) for p in k2_phases)
    
    equiv_check = np.abs(sum_k1) < TOL and np.abs(sum_k2) < TOL
    
    results['checks'].append({
        'name': 'k=1 and k=2 both satisfy neutrality (opposite chiralities)',
        'expected': True,
        'computed': {'|sum_k1|': np.abs(sum_k1), '|sum_k2|': np.abs(sum_k2)},
        'passed': equiv_check
    })
    results['status'] &= equiv_check
    
    return results


def verify_cartan_eigenvalues() -> Dict[str, Any]:
    """
    Verify Section 2.2: Cartan Generator Eigenvalues.
    
    Color states are eigenstates of T₃ and T₈ with eigenvalues:
    |R⟩: (T₃=+1/2, T₈=+1/(2√3))
    |G⟩: (T₃=-1/2, T₈=+1/(2√3))
    |B⟩: (T₃=0, T₈=-1/√3)
    """
    results = {
        'test': 'Cartan Generator Eigenvalues (Section 2.2)',
        'status': True,
        'checks': []
    }
    
    expected_eigenvalues = {
        'R': {'T3': 0.5, 'T8': 1 / (2 * np.sqrt(3))},
        'G': {'T3': -0.5, 'T8': 1 / (2 * np.sqrt(3))},
        'B': {'T3': 0.0, 'T8': -1 / np.sqrt(3)},
    }
    
    for color, state in COLOR_STATES.items():
        # T₃ eigenvalue
        t3_result = T3 @ state
        t3_eigenvalue = np.real(t3_result[np.argmax(np.abs(state))])
        t3_expected = expected_eigenvalues[color]['T3']
        t3_check = np.abs(t3_eigenvalue - t3_expected) < TOL
        
        results['checks'].append({
            'name': f'T₃|{color}⟩ eigenvalue',
            'expected': t3_expected,
            'computed': t3_eigenvalue,
            'passed': t3_check
        })
        results['status'] &= t3_check
        
        # T₈ eigenvalue
        t8_result = T8 @ state
        t8_eigenvalue = np.real(t8_result[np.argmax(np.abs(state))])
        t8_expected = expected_eigenvalues[color]['T8']
        t8_check = np.abs(t8_eigenvalue - t8_expected) < TOL
        
        results['checks'].append({
            'name': f'T₈|{color}⟩ eigenvalue',
            'expected': t8_expected,
            'computed': t8_eigenvalue,
            'passed': t8_check
        })
        results['status'] &= t8_check
    
    # Verify T₃ and T₈ commute (Cartan subalgebra)
    commutator = T3 @ T8 - T8 @ T3
    commute_check = np.allclose(commutator, 0, atol=TOL)
    
    results['checks'].append({
        'name': '[T₃, T₈] = 0 (Cartan subalgebra commutes)',
        'expected': 0.0,
        'computed': np.max(np.abs(commutator)),
        'passed': commute_check
    })
    results['status'] &= commute_check
    
    # Verify normalization Tr(T_a T_b) = δ_ab / 2
    trace_t3_t3 = np.trace(T3 @ T3)
    trace_t8_t8 = np.trace(T8 @ T8)
    trace_t3_t8 = np.trace(T3 @ T8)
    
    norm_check = (np.abs(trace_t3_t3 - 0.5) < TOL and
                  np.abs(trace_t8_t8 - 0.5) < TOL and
                  np.abs(trace_t3_t8) < TOL)
    
    results['checks'].append({
        'name': 'Normalization: Tr(T_a T_b) = δ_ab/2',
        'expected': {'T3·T3': 0.5, 'T8·T8': 0.5, 'T3·T8': 0.0},
        'computed': {'T3·T3': trace_t3_t3, 'T8·T8': trace_t8_t8, 'T3·T8': trace_t3_t8},
        'passed': norm_check
    })
    results['status'] &= norm_check
    
    return results


def verify_anti_color_phases() -> Dict[str, Any]:
    """
    Verify Section 4: Anti-Color Phases.
    
    Anti-colors have phases that are complex conjugates (negatives) of colors:
    φ_R̄ = -φ_R = 0
    φ_Ḡ = -φ_G = -2π/3 ≡ 4π/3 (mod 2π)
    φ_B̄ = -φ_B = -4π/3 ≡ 2π/3 (mod 2π)
    """
    results = {
        'test': 'Anti-Color Phases (Section 4)',
        'status': True,
        'checks': []
    }
    
    for color in ['R', 'G', 'B']:
        anti_color = f'{color}_bar'
        phi_c = PHASES[color]
        phi_c_bar = ANTI_PHASES[anti_color]
        
        # Check: φ_c̄ = -φ_c (mod 2π)
        expected_anti = (-phi_c) % (2 * np.pi)
        check_passed = np.abs(phi_c_bar - expected_anti) < TOL
        
        results['checks'].append({
            'name': f'φ_{anti_color} = -φ_{color} (mod 2π)',
            'expected': expected_anti,
            'computed': phi_c_bar,
            'passed': check_passed
        })
        results['status'] &= check_passed
        
        # Check: e^{iφ_c} · e^{iφ_c̄} = e^{iφ_c} · e^{-iφ_c} = 1
        product = np.exp(1j * phi_c) * np.exp(1j * phi_c_bar)
        # Note: This equals e^{i(φ_c + (-φ_c))} = e^0 = 1
        product_check = np.abs(product - 1.0) < TOL
        
        results['checks'].append({
            'name': f'e^{{iφ_{color}}} · e^{{iφ_{anti_color}}} = 1',
            'expected': 1.0,
            'computed': float(np.abs(product)),
            'passed': product_check
        })
        results['status'] &= product_check
    
    # Check: Anti-colors also satisfy neutrality
    anti_sum = sum(np.exp(1j * ANTI_PHASES[c]) for c in ANTI_PHASES)
    anti_neutral_check = np.abs(anti_sum) < TOL
    
    results['checks'].append({
        'name': 'Anti-color neutrality: Σ e^{iφ_c̄} = 0',
        'expected': 0.0,
        'computed': float(np.abs(anti_sum)),
        'passed': anti_neutral_check
    })
    results['status'] &= anti_neutral_check
    
    # Observation from document: Ḡ has same phase as B, B̄ has same phase as G
    gb_match = np.abs(ANTI_PHASES['G_bar'] - PHASES['B']) < TOL
    bg_match = np.abs(ANTI_PHASES['B_bar'] - PHASES['G']) < TOL
    
    results['checks'].append({
        'name': 'φ_Ḡ = φ_B and φ_B̄ = φ_G (phase matching)',
        'expected': True,
        'computed': {'Ḡ=B': gb_match, 'B̄=G': bg_match},
        'passed': gb_match and bg_match
    })
    results['status'] &= gb_match and bg_match
    
    return results


def verify_key_theorems() -> Dict[str, Any]:
    """
    Verify Section 8: Key Theorems.
    
    8.1: Phase-locked sum vanishes
    8.2: Product of phases is unity
    8.3: Z₃ cyclic permutation symmetry
    8.4: Orientation from phase ordering
    """
    results = {
        'test': 'Key Theorems (Section 8)',
        'status': True,
        'checks': []
    }
    
    phi_R = PHASES['R']
    phi_G = PHASES['G']
    phi_B = PHASES['B']
    
    e_R = np.exp(1j * phi_R)
    e_G = np.exp(1j * phi_G)
    e_B = np.exp(1j * phi_B)
    
    # Theorem 8.1: Phase-locked sum vanishes
    phase_sum = e_R + e_G + e_B
    sum_check = np.abs(phase_sum) < TOL
    
    results['checks'].append({
        'name': 'Thm 8.1: e^{iφ_R} + e^{iφ_G} + e^{iφ_B} = 0',
        'expected': 0.0,
        'computed': float(np.abs(phase_sum)),
        'passed': sum_check
    })
    results['status'] &= sum_check
    
    # Verify geometric series formula
    r = np.exp(2j * np.pi / 3)
    geometric_sum = (1 - r**3) / (1 - r)
    # Since r³ = 1, this is 0/something = 0 (need L'Hopital or direct)
    # Direct: 1 + r + r² 
    direct_sum = 1 + r + r**2
    geo_check = np.abs(direct_sum) < TOL
    
    results['checks'].append({
        'name': 'Geometric series: Σ_{k=0}^{2} r^k = 0 for r=e^{2πi/3}',
        'expected': 0.0,
        'computed': float(np.abs(direct_sum)),
        'passed': geo_check
    })
    results['status'] &= geo_check
    
    # Theorem 8.2: Product of phases is unity
    phase_product = e_R * e_G * e_B
    product_check = np.abs(phase_product - 1.0) < TOL
    
    results['checks'].append({
        'name': 'Thm 8.2: e^{iφ_R} · e^{iφ_G} · e^{iφ_B} = 1',
        'expected': 1.0,
        'computed': float(np.real(phase_product)),
        'passed': product_check
    })
    results['status'] &= product_check
    
    # Verify via exponent sum
    exponent_sum = phi_R + phi_G + phi_B
    expected_sum = 0 + 2*np.pi/3 + 4*np.pi/3  # = 2π
    sum_exp_check = np.abs(exponent_sum - 2*np.pi) < TOL
    
    results['checks'].append({
        'name': 'Exponent sum: φ_R + φ_G + φ_B = 2π',
        'expected': 2*np.pi,
        'computed': exponent_sum,
        'passed': sum_exp_check
    })
    results['status'] &= sum_exp_check
    
    # Theorem 8.3: Z₃ cyclic permutation symmetry
    # σ: (R,G,B) → (G,B,R) equivalent to overall phase shift by 2π/3
    permuted = (e_G, e_B, e_R)
    shifted = (e_R * np.exp(2j*np.pi/3), e_G * np.exp(2j*np.pi/3), e_B * np.exp(2j*np.pi/3))
    
    perm_check = all(np.abs(p - s) < TOL for p, s in zip(permuted, shifted))
    
    results['checks'].append({
        'name': 'Thm 8.3: Cyclic permutation = overall phase shift by 2π/3',
        'expected': True,
        'computed': perm_check,
        'passed': perm_check
    })
    results['status'] &= perm_check
    
    # Theorem 8.4: Orientation from phase ordering
    # R→G→B follows counterclockwise direction (phases increase: 0 → 2π/3 → 4π/3)
    # This is verified by checking that phase increments are positive
    
    # Check phase progression is counterclockwise (increasing angles mod 2π)
    delta_RG = (phi_G - phi_R) % (2 * np.pi)  # Should be 2π/3
    delta_GB = (phi_B - phi_G) % (2 * np.pi)  # Should be 2π/3
    delta_BR = (phi_R + 2*np.pi - phi_B) % (2 * np.pi)  # Should be 2π/3
    
    # Counterclockwise means positive angular increments
    ccw_check = (np.abs(delta_RG - 2*np.pi/3) < TOL and 
                 np.abs(delta_GB - 2*np.pi/3) < TOL and
                 np.abs(delta_BR - 2*np.pi/3) < TOL)
    
    results['checks'].append({
        'name': 'Thm 8.4: R→G→B is counterclockwise (phases increase by 2π/3)',
        'expected': 'Δφ = 2π/3 for each step',
        'computed': {'R→G': delta_RG, 'G→B': delta_GB, 'B→R': delta_BR},
        'passed': ccw_check
    })
    results['status'] &= ccw_check
    
    # Verify opposite ordering R→B→G is clockwise (phases decrease)
    # R→B: 0 → 4π/3 is +4π/3 ≡ -2π/3 (clockwise)
    # B→G: 4π/3 → 2π/3 is -2π/3 (clockwise)
    delta_RB = (phi_B - phi_R) % (2 * np.pi)  # 4π/3 (or equiv. -2π/3 clockwise)
    
    # Going R→B→G means we go the "wrong way" - 4π/3 increments instead of 2π/3
    # This is equivalent to clockwise (negative direction)
    cw_check = np.abs(delta_RB - 4*np.pi/3) < TOL  # Going clockwise = 4π/3 = -2π/3
    
    results['checks'].append({
        'name': 'R→B→G is clockwise (phase step = 4π/3 ≡ -2π/3)',
        'expected': 4*np.pi/3,
        'computed': delta_RB,
        'passed': cw_check
    })
    results['status'] &= cw_check
    
    return results


def verify_z3_center_symmetry() -> Dict[str, Any]:
    """
    Verify Section 2.1: Z₃ Center of SU(3).
    
    The center Z(SU(3)) = {ω^k · I : k = 0,1,2} ≅ Z₃
    """
    results = {
        'test': 'Z₃ Center of SU(3) (Section 2.1)',
        'status': True,
        'checks': []
    }
    
    omega = OMEGA
    I = np.eye(3, dtype=complex)
    
    # Define center elements
    z0 = I
    z1 = omega * I
    z2 = omega**2 * I
    
    center_elements = [z0, z1, z2]
    
    # Check 1: All center elements are scalar matrices
    for k, z in enumerate(center_elements):
        is_scalar = np.allclose(z, z[0, 0] * I, atol=TOL)
        results['checks'].append({
            'name': f'z_{k} = ω^{k}·I is scalar matrix',
            'expected': True,
            'computed': is_scalar,
            'passed': is_scalar
        })
        results['status'] &= is_scalar
    
    # Check 2: Center elements commute with all SU(3) generators
    for lambda_name, lambda_mat in GELL_MANN.items():
        for k, z in enumerate(center_elements):
            commutator = z @ lambda_mat - lambda_mat @ z
            commutes = np.allclose(commutator, 0, atol=TOL)
            results['checks'].append({
                'name': f'[z_{k}, {lambda_name}] = 0',
                'expected': True,
                'computed': commutes,
                'passed': commutes
            })
            results['status'] &= commutes
    
    # Check 3: Center is closed under multiplication (group property)
    # z_i * z_j = z_{(i+j) mod 3}
    for i in range(3):
        for j in range(3):
            product = center_elements[i] @ center_elements[j]
            expected_idx = (i + j) % 3
            expected = center_elements[expected_idx]
            closure_check = np.allclose(product, expected, atol=TOL)
            if not closure_check:  # Only report failures or sample successes
                results['checks'].append({
                    'name': f'z_{i} · z_{j} = z_{expected_idx}',
                    'expected': True,
                    'computed': closure_check,
                    'passed': closure_check
                })
            results['status'] &= closure_check
    
    # Summary check for group closure
    results['checks'].append({
        'name': 'Center forms group: z_i · z_j = z_{(i+j) mod 3} for all i,j',
        'expected': True,
        'computed': True,  # If we got here, all checks passed
        'passed': results['status']
    })
    
    return results


def verify_color_field_structure() -> Dict[str, Any]:
    """
    Verify Section 5: Complete Field Specification.
    
    χ_c(x) = a_c(x) · e^{iφ_c}
    
    With explicit complex forms using e^{i2π/3} = -1/2 + i√3/2
    """
    results = {
        'test': 'Color Field Structure (Section 5)',
        'status': True,
        'checks': []
    }
    
    # Test at a sample point (origin)
    x = np.array([0, 0, 0])
    eps = 0.1  # Regularization parameter
    
    # Define pressure function
    def pressure(x, x_c, eps):
        r_sq = np.sum((x - x_c)**2)
        return 1.0 / (r_sq + eps**2)
    
    # Stella octangula vertex positions (unit circumradius)
    vertices = {
        'R': np.array([1, 1, 1]) / np.sqrt(3),
        'G': np.array([1, -1, -1]) / np.sqrt(3),
        'B': np.array([-1, 1, -1]) / np.sqrt(3),
    }
    
    # Compute color fields
    chi = {}
    for c in ['R', 'G', 'B']:
        P_c = pressure(x, vertices[c], eps)
        phase_factor = np.exp(1j * PHASES[c])
        chi[c] = P_c * phase_factor
    
    # Check: Fields have correct phases
    for c in ['R', 'G', 'B']:
        computed_phase = np.angle(chi[c])
        expected_phase = PHASES[c]
        # Handle phase wrapping
        phase_diff = (computed_phase - expected_phase + np.pi) % (2*np.pi) - np.pi
        phase_check = np.abs(phase_diff) < TOL
        
        results['checks'].append({
            'name': f'χ_{c} has phase φ_{c} = {expected_phase:.4f}',
            'expected': expected_phase,
            'computed': computed_phase,
            'passed': phase_check
        })
        results['status'] &= phase_check
    
    # Check: Explicit complex forms (Section 5.2)
    # χ_G = P_G · (-1/2 + i√3/2), χ_B = P_B · (-1/2 - i√3/2)
    exp_2pi3 = -0.5 + 1j * np.sqrt(3) / 2
    exp_4pi3 = -0.5 - 1j * np.sqrt(3) / 2
    
    P_G = pressure(x, vertices['G'], eps)
    P_B = pressure(x, vertices['B'], eps)
    
    chi_G_explicit = P_G * exp_2pi3
    chi_B_explicit = P_B * exp_4pi3
    
    explicit_G_check = np.abs(chi['G'] - chi_G_explicit) < TOL
    explicit_B_check = np.abs(chi['B'] - chi_B_explicit) < TOL
    
    results['checks'].append({
        'name': 'χ_G = P_G · (-1/2 + i√3/2)',
        'expected': chi_G_explicit,
        'computed': chi['G'],
        'passed': explicit_G_check
    })
    results['checks'].append({
        'name': 'χ_B = P_B · (-1/2 - i√3/2)',
        'expected': chi_B_explicit,
        'computed': chi['B'],
        'passed': explicit_B_check
    })
    results['status'] &= explicit_G_check and explicit_B_check
    
    # Check: Total field formula (Section 5.3)
    # χ_total = a_0 [P_R - (1/2)(P_G + P_B) + i(√3/2)(P_G - P_B)]
    P_R = pressure(x, vertices['R'], eps)
    chi_total_direct = chi['R'] + chi['G'] + chi['B']
    
    real_part = P_R - 0.5 * (P_G + P_B)
    imag_part = (np.sqrt(3) / 2) * (P_G - P_B)
    chi_total_formula = real_part + 1j * imag_part
    
    total_check = np.abs(chi_total_direct - chi_total_formula) < TOL
    
    results['checks'].append({
        'name': 'Total field: χ_total = P_R - (P_G+P_B)/2 + i√3(P_G-P_B)/2',
        'expected': chi_total_formula,
        'computed': chi_total_direct,
        'passed': total_check
    })
    results['status'] &= total_check
    
    return results


def verify_meson_baryon_structure() -> Dict[str, Any]:
    """
    Verify Section 3.2-3.3 and Section 9: Hadron Color Structure.
    
    Mesons: q̄q with color singlet Σ_c |cc̄⟩
    Baryons: qqq with ε^{abc} color structure
    """
    results = {
        'test': 'Hadron Color Structure (Sections 3.2, 9)',
        'status': True,
        'checks': []
    }
    
    # Baryon color neutrality
    # Three quarks (RGB): 1 + ω + ω² = 0
    baryon_sum = sum(np.exp(1j * PHASES[c]) for c in ['R', 'G', 'B'])
    baryon_check = np.abs(baryon_sum) < TOL
    
    results['checks'].append({
        'name': 'Baryon (qqq): e^{iφ_R} + e^{iφ_G} + e^{iφ_B} = 0',
        'expected': 0.0,
        'computed': float(np.abs(baryon_sum)),
        'passed': baryon_check
    })
    results['status'] &= baryon_check
    
    # Meson color structure
    # Color singlet: (1/√3)(|RR̄⟩ + |GḠ⟩ + |BB̄⟩)
    # Each term: e^{iφ_c} · e^{-iφ_c} = 1
    meson_contributions = []
    for c in ['R', 'G', 'B']:
        phi_c = PHASES[c]
        # Meson: quark × antiquark
        contribution = np.exp(1j * phi_c) * np.exp(-1j * phi_c)
        meson_contributions.append(contribution)
    
    # All contributions should be 1
    all_one = all(np.abs(m - 1.0) < TOL for m in meson_contributions)
    
    results['checks'].append({
        'name': 'Meson (qq̄): each |cc̄⟩ contributes e^{iφ_c}·e^{-iφ_c} = 1',
        'expected': [1.0, 1.0, 1.0],
        'computed': [float(np.real(m)) for m in meson_contributions],
        'passed': all_one
    })
    results['status'] &= all_one
    
    # Verify Levi-Civita structure for baryon (ε^{RGB} = 1)
    # The antisymmetric combination ensures color singlet
    
    def levi_civita(i, j, k):
        """Return Levi-Civita symbol ε_{ijk}"""
        indices = (i, j, k)
        if len(set(indices)) < 3:
            return 0
        # Count inversions
        inversions = sum(1 for a, b in [(i,j), (i,k), (j,k)] if a > b)
        return 1 if inversions % 2 == 0 else -1
    
    # The baryon color singlet uses ε^{abc}
    # ε^{012} = ε^{RGB} = +1 (even permutation)
    # This gives the totally antisymmetric color wavefunction
    
    # Verify ε values
    eps_RGB = levi_civita(0, 1, 2)  # R=0, G=1, B=2
    eps_RBG = levi_civita(0, 2, 1)  # Should be -1
    eps_GRB = levi_civita(1, 0, 2)  # Should be -1
    
    lc_check = (eps_RGB == 1 and eps_RBG == -1 and eps_GRB == -1)
    
    results['checks'].append({
        'name': 'Levi-Civita: ε^{RGB}=+1, ε^{RBG}=-1 (antisymmetric)',
        'expected': {'RGB': 1, 'RBG': -1, 'GRB': -1},
        'computed': {'RGB': eps_RGB, 'RBG': eps_RBG, 'GRB': eps_GRB},
        'passed': lc_check
    })
    results['status'] &= lc_check
    
    # The total phase of the baryon is e^{i(φ_R + φ_G + φ_B)} = e^{2πi} = 1
    # This confirms baryon is phase-neutral (Theorem 8.2)
    baryon_total_phase = np.exp(1j * (PHASES['R'] + PHASES['G'] + PHASES['B']))
    baryon_phase_check = np.abs(baryon_total_phase - 1.0) < TOL
    
    results['checks'].append({
        'name': 'Baryon total phase: e^{i(φ_R+φ_G+φ_B)} = 1 (phase-neutral)',
        'expected': 1.0,
        'computed': float(np.real(baryon_total_phase)),
        'passed': baryon_phase_check
    })
    results['status'] &= baryon_phase_check
    
    return results


# =============================================================================
# MAIN VERIFICATION SUITE
# =============================================================================

def run_all_verifications() -> Dict[str, Any]:
    """Run all verification tests and compile results."""
    
    all_results = {
        'title': 'Definition 0.1.2: Three Color Fields with Relative Phases',
        'document': 'Definition-0.1.2-Three-Color-Fields-Relative-Phases.md',
        'date': datetime.now().isoformat(),
        'overall_status': True,
        'tests': []
    }
    
    # Run all verification functions
    verifications = [
        verify_cube_roots_of_unity,
        verify_weight_vector_geometry,
        verify_phase_uniqueness,
        verify_cartan_eigenvalues,
        verify_anti_color_phases,
        verify_key_theorems,
        verify_z3_center_symmetry,
        verify_color_field_structure,
        verify_meson_baryon_structure,
    ]
    
    for verify_func in verifications:
        print(f"\nRunning: {verify_func.__name__}...")
        result = verify_func()
        all_results['tests'].append(result)
        all_results['overall_status'] &= result['status']
        
        status = "✅ PASSED" if result['status'] else "❌ FAILED"
        print(f"  {result['test']}: {status}")
    
    return all_results


def print_summary(results: Dict[str, Any]) -> None:
    """Print a summary of all verification results."""
    
    print("\n" + "=" * 80)
    print(f"VERIFICATION SUMMARY: {results['title']}")
    print("=" * 80)
    
    passed = sum(1 for t in results['tests'] if t['status'])
    total = len(results['tests'])
    
    for test in results['tests']:
        status = "✅" if test['status'] else "❌"
        print(f"  {status} {test['test']}")
        
        # Print failed checks
        if not test['status']:
            for check in test['checks']:
                if not check['passed']:
                    print(f"      ❌ {check['name']}")
                    print(f"         Expected: {check['expected']}")
                    print(f"         Computed: {check['computed']}")
    
    print("\n" + "-" * 80)
    overall = "✅ ALL TESTS PASSED" if results['overall_status'] else "❌ SOME TESTS FAILED"
    print(f"OVERALL: {overall} ({passed}/{total} tests passed)")
    print("-" * 80)


def save_results(results: Dict[str, Any], output_path: str) -> None:
    """Save results to JSON file."""
    
    # Convert numpy types for JSON serialization
    def convert_numpy(obj):
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, (np.integer, np.floating)):
            return float(obj)
        elif isinstance(obj, np.bool_):
            return bool(obj)
        elif isinstance(obj, complex):
            return {'real': obj.real, 'imag': obj.imag}
        elif isinstance(obj, dict):
            return {k: convert_numpy(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [convert_numpy(v) for v in obj]
        return obj
    
    serializable = convert_numpy(results)
    
    with open(output_path, 'w') as f:
        json.dump(serializable, f, indent=2)
    
    print(f"\nResults saved to: {output_path}")


if __name__ == '__main__':
    # Run all verifications
    results = run_all_verifications()
    
    # Print summary
    print_summary(results)
    
    # Save results
    script_dir = os.path.dirname(os.path.abspath(__file__))
    output_path = os.path.join(script_dir, 'definition_0_1_2_three_color_fields_results.json')
    save_results(results, output_path)
    
    # Exit with appropriate code
    exit_code = 0 if results['overall_status'] else 1
    exit(exit_code)
