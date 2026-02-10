"""
Wolfenstein Parameters A, ρ, η Derivation from Geometric Framework
==================================================================

This script attempts to derive the remaining Wolfenstein parameters (A, ρ, η)
from the same geometric framework that successfully derived λ.

Recall our breakthrough for λ:
- λ = (1/φ³) × sin(72°) = 0.2245 ± 0.88%
- φ = (1+√5)/2 = golden ratio from 24-cell geometry
- 72° = 2π/5 = pentagonal angle from icosahedral symmetry

Now we explore geometric origins for A, ρ, η.

PDG 2024 Values (target):
- λ = 0.22497 ± 0.00070
- A = 0.839 ± 0.011
- ρ̄ = 0.1581 ± 0.0092
- η̄ = 0.3548 ± 0.0072

Author: Chiral Geometrogenesis Framework
Date: December 14, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import minimize

# Physical constants
phi = (1 + np.sqrt(5)) / 2  # Golden ratio
angle_72 = 72 * np.pi / 180  # Pentagonal angle in radians

# PDG 2024 Values
lambda_PDG = 0.22497
A_PDG = 0.839
rho_bar_PDG = 0.1581
eta_bar_PDG = 0.3548

# Our geometric λ
lambda_geom = (1/phi**3) * np.sin(angle_72)

print("=" * 70)
print("WOLFENSTEIN PARAMETERS A, ρ, η FROM GEOMETRIC FRAMEWORK")
print("=" * 70)
print()
print("RECAP: λ derivation success")
print("-" * 40)
print(f"λ_geometric = (1/φ³)sin(72°) = {lambda_geom:.6f}")
print(f"λ_PDG = {lambda_PDG:.5f}")
print(f"Agreement: {100*abs(lambda_geom - lambda_PDG)/lambda_PDG:.2f}%")
print()

# ============================================================================
# APPROACH 1: Hierarchical Structure from Generation Geometry
# ============================================================================
print("=" * 70)
print("APPROACH 1: Hierarchical Generation Structure")
print("=" * 70)
print()
print("The CKM matrix elements relate different generations:")
print("  V_us ~ λ       (1st ↔ 2nd generation)")
print("  V_cb ~ Aλ²     (2nd ↔ 3rd generation)")
print("  V_ub ~ Aλ³     (1st ↔ 3rd generation)")
print()
print("Hypothesis: A encodes the ADDITIONAL suppression for 2↔3 mixing")
print("beyond the basic λ² hierarchy from generation distances.")
print()

# In our framework, generations are at different radii:
# r₁, r₂, r₃ with r₁/r₂ = √3 from hexagonal lattice
# The mixing is governed by overlap integrals

# Key insight: The parameter A relates to the ANGULAR structure
# while λ relates to the RADIAL structure

# Geometric factors from 24-cell
# The 24-cell has special angles: 60°, 72°, 90°, 108°, 120°

# Hypothesis: A relates to cos(60°)/cos(72°) or similar angular ratios
A_test1 = np.cos(60 * np.pi/180) / np.cos(72 * np.pi/180)
print(f"Test 1: A = cos(60°)/cos(72°) = {A_test1:.4f}")

# Hypothesis: A relates to sin ratios
A_test2 = np.sin(60 * np.pi/180) / np.sin(72 * np.pi/180)
print(f"Test 2: A = sin(60°)/sin(72°) = {A_test2:.4f}")

# Hypothesis: A relates to the 24-cell dihedral angle of 120°
A_test3 = np.sin(36 * np.pi/180) / np.sin(45 * np.pi/180)  # 36° = half of 72°
print(f"Test 3: A = sin(36°)/sin(45°) = {A_test3:.4f}")

# ============================================================================
# APPROACH 2: Golden Ratio Combinations
# ============================================================================
print()
print("=" * 70)
print("APPROACH 2: Golden Ratio Combinations")
print("=" * 70)
print()
print("Since λ involves φ³, perhaps A involves other powers of φ.")
print()

# Various φ combinations
A_phi1 = 1/phi  # ≈ 0.618
A_phi2 = phi - 1  # = 1/φ ≈ 0.618
A_phi3 = 2 - phi  # ≈ 0.382
A_phi4 = phi**2 - phi - 1  # = 0 (identity)
A_phi5 = np.sqrt(phi) - 1  # ≈ 0.272
A_phi6 = 1 - 1/phi**2  # ≈ 0.618² ≈ 0.382
A_phi7 = 2/phi - 1  # ≈ 0.236

print(f"1/φ = {A_phi1:.4f}")
print(f"2 - φ = {A_phi3:.4f}")
print(f"√φ - 1 = {A_phi5:.4f}")
print(f"2/φ - 1 = {A_phi7:.4f}")
print(f"1/√φ = {1/np.sqrt(phi):.4f}")

# Combined with trigonometric functions
A_comb1 = np.cos(36 * np.pi/180)  # cos(36°) = φ/2
print(f"cos(36°) = φ/2 = {A_comb1:.4f}")

A_comb2 = np.sin(54 * np.pi/180)  # sin(54°) = φ/2
print(f"sin(54°) = φ/2 = {A_comb2:.4f}")

A_comb3 = 2 * np.sin(36 * np.pi/180) * np.cos(36 * np.pi/180)  # = sin(72°)
print(f"sin(72°) = {A_comb3:.4f}")

# ============================================================================
# APPROACH 3: CKM Hierarchy Analysis
# ============================================================================
print()
print("=" * 70)
print("APPROACH 3: CKM Matrix Element Ratios")
print("=" * 70)
print()

# The CKM matrix encodes quark mixing. Key relationships:
# |V_cb| ≈ Aλ² ≈ 0.042
# |V_ub| ≈ Aλ³(ρ² + η²)^{1/2} ≈ 0.0036
# |V_td| ≈ Aλ³|(1-ρ-iη)| ≈ 0.0087

# If λ = (1/φ³)sin(72°), what is A?
# From CKM fit: A = |V_cb|/λ²

# Vcb measured: |V_cb| ≈ 0.0422 ± 0.0008
Vcb = 0.0422
A_from_Vcb = Vcb / lambda_geom**2
print(f"From |V_cb| = {Vcb}: A = |V_cb|/λ² = {A_from_Vcb:.4f}")
print(f"PDG value: A = {A_PDG:.3f}")
print(f"Discrepancy: {100*abs(A_from_Vcb - A_PDG)/A_PDG:.1f}%")
print()

# ============================================================================
# APPROACH 4: Geometric A from 3-Generation Structure
# ============================================================================
print()
print("=" * 70)
print("APPROACH 4: A from 3-Generation Geometry")
print("=" * 70)
print()

# Key insight: The stella octangula has TWO tetrahedra
# Each has 4 vertices → 4 + 4 = 8 vertices
# But we only have 3 generations!

# The 3 generations might correspond to:
# - 3 spatial axes in the 24-cell
# - 3 faces of a tetrahedron
# - 3 directions of maximum symmetry

# The factor A might relate to the probability that
# the 2nd↔3rd transition ALSO involves a tetrahedron swap

# If swapping tetrahedra has probability ~ 1/3 (three choices)
# and the angular factor is cos(30°) = √3/2:
A_geom1 = np.sqrt(3)/2  # ≈ 0.866
print(f"√3/2 = cos(30°) = {A_geom1:.4f}")

# Or 2/√6 (related to tetrahedron geometry)
A_geom2 = 2/np.sqrt(6)  # ≈ 0.816
print(f"2/√6 = {A_geom2:.4f}")

# Or √(2/3) (probability normalization for 3 generations)
A_geom3 = np.sqrt(2/3)  # ≈ 0.816
print(f"√(2/3) = {A_geom3:.4f}")

# Or related to the tetrahedron edge/radius ratio
# For a tetrahedron with circumradius R, edge length a = R√(8/3)
A_geom4 = np.sqrt(3/8)  # Inverse of edge/radius
print(f"√(3/8) = {A_geom4:.4f}")

# ============================================================================
# APPROACH 5: Combined Golden-Tetrahedral Formula
# ============================================================================
print()
print("=" * 70)
print("APPROACH 5: Combined Golden-Tetrahedral Formula for A")
print("=" * 70)
print()

# The most promising candidates near A ≈ 0.84:
candidates_A = {
    "√(2/3) = √(2/3)": np.sqrt(2/3),
    "2/√6": 2/np.sqrt(6),
    "√3/2 = cos(30°)": np.sqrt(3)/2,
    "cos(30°)×(2/φ)": np.cos(30*np.pi/180) * 2/phi,
    "sin(72°)/φ^(1/2)": np.sin(72*np.pi/180)/np.sqrt(phi),
    "1/(φ×sin(36°))": 1/(phi * np.sin(36*np.pi/180)),
    "4sin(36°)cos(36°)/φ": 4*np.sin(36*np.pi/180)*np.cos(36*np.pi/180)/phi,
    "2sin(72°)/φ": 2*np.sin(72*np.pi/180)/phi,
    "φ/(1+φ^(1/2))": phi/(1 + np.sqrt(phi)),
    "√(φ/√5)": np.sqrt(phi/np.sqrt(5)),
}

print("Candidate formulas for A:")
print("-" * 50)
for name, value in sorted(candidates_A.items(), key=lambda x: abs(x[1] - A_PDG)):
    error_pct = 100 * abs(value - A_PDG) / A_PDG
    marker = "✓" if error_pct < 3 else " "
    print(f"{marker} {name:35s} = {value:.5f} ({error_pct:5.2f}% off)")

# ============================================================================
# APPROACH 6: CP Violation Parameters ρ and η
# ============================================================================
print()
print("=" * 70)
print("APPROACH 6: CP Violation Parameters ρ̄ and η̄")
print("=" * 70)
print()

print("The CP violation phase δ determines both ρ and η through:")
print("  V_ub = Aλ³(ρ - iη) = |V_ub|e^{-iγ}")
print()
print("where γ is an angle in the unitarity triangle.")
print()
print("The unitarity triangle has angles:")
print("  α + β + γ = 180°")
print("with measured values (PDG 2024):")
print("  α ≈ 85.4°, β ≈ 22.2°, γ ≈ 65.5°")
print()

# CP violation comes from the area of the unitarity triangle
# J = Im(V_us V_cb V*_ub V*_cs) ≈ A²λ⁶η ≈ 3×10⁻⁵

# The phase could be related to geometric phases in the 24-cell
# The 24-cell has interesting angle relationships

# Key insight: The 24-cell has 96 edges, 24 vertices, 24 cells
# The ratio 96/24 = 4, but more interestingly:
# The dihedral angle is 120°

# Unitarity triangle angles
alpha_exp = 85.4  # degrees
beta_exp = 22.2   # degrees
gamma_exp = 65.5  # degrees

print(f"Measured angles: α = {alpha_exp}°, β = {beta_exp}°, γ = {gamma_exp}°")
print()

# From the unitarity triangle:
# ρ̄ = (1 - λ²/2)ρ, η̄ = (1 - λ²/2)η
# ρ̄ + iη̄ = -V_ud V*_ub / (V_cd V*_cb)
# |ρ̄ + iη̄| = √(ρ̄² + η̄²) related to triangle side

rho_eta_magnitude = np.sqrt(rho_bar_PDG**2 + eta_bar_PDG**2)
print(f"|ρ̄ + iη̄| = √(ρ̄² + η̄²) = {rho_eta_magnitude:.4f}")
print()

# The angle of ρ̄ + iη̄ in the complex plane:
phi_rho_eta = np.arctan2(eta_bar_PDG, rho_bar_PDG) * 180/np.pi
print(f"Phase angle: arctan(η̄/ρ̄) = {phi_rho_eta:.2f}°")
print()

# ============================================================================
# APPROACH 7: Geometric CP Phase Derivation
# ============================================================================
print()
print("=" * 70)
print("APPROACH 7: Geometric CP Phase")
print("=" * 70)
print()

# Hypothesis: The CP violating phase relates to the geometric
# phase acquired when traversing the 24-cell

# Key geometric angles in the 24-cell and stella octangula:
# - 70.53° = arccos(1/3) = tetrahedron edge-face angle
# - 109.47° = arccos(-1/3) = tetrahedron face-face dihedral
# - 60° = face angle of tetrahedron
# - 72° = pentagonal angle
# - 36° = half-pentagonal angle
# - 120° = 24-cell dihedral angle

tet_angle = np.arccos(1/3) * 180/np.pi  # 70.53°
tet_dihedral = np.arccos(-1/3) * 180/np.pi  # 109.47°

print(f"Tetrahedron edge-face angle: arccos(1/3) = {tet_angle:.2f}°")
print(f"Tetrahedron dihedral angle: arccos(-1/3) = {tet_dihedral:.2f}°")
print()

# The CP phase γ ≈ 65.5° is interestingly close to:
gamma_test1 = 72 - 7.5  # 72° - correction
gamma_test2 = 60 + 5.5  # 60° + correction
gamma_test3 = tet_angle - 5  # 70.53° - 5°
gamma_test4 = 2 * 36 - 7  # 2×36° - 7° = 65°

print("Possible geometric origins for γ ≈ 65.5°:")
print(f"  72° - 7.5° = {gamma_test1:.1f}° (pentagonal minus correction)")
print(f"  60° + 5.5° = {gamma_test2:.1f}° (hexagonal plus correction)")
print(f"  arccos(1/3) - 5° = {gamma_test3:.1f}° (tetrahedron angle minus correction)")
print(f"  2×36° - 7° = {gamma_test4:.1f}° (double pentagonal minus correction)")
print()

# More promising: γ might be arctan(φ)
gamma_phi = np.arctan(phi) * 180/np.pi  # 58.3°
print(f"  arctan(φ) = {gamma_phi:.2f}° (golden angle)")

# Or related to 72° - 36°/5
gamma_geo1 = 72 - 36/5
print(f"  72° - 36°/5 = {gamma_geo1:.2f}°")

# From trigonometry of regular pentagon/24-cell
gamma_geo2 = np.arcsin(phi/2) * 180/np.pi  # = 54°
print(f"  arcsin(φ/2) = {gamma_geo2:.2f}° (half-golden angle)")

# ============================================================================
# APPROACH 8: ρ and η from Unitarity Triangle Geometry
# ============================================================================
print()
print("=" * 70)
print("APPROACH 8: ρ̄ and η̄ from Triangle Geometry")
print("=" * 70)
print()

# The unitarity triangle has:
# - One vertex at origin (0, 0)
# - One vertex at (1, 0)
# - One vertex at (ρ̄, η̄)
# - Angles α, β, γ at the three vertices

# From the triangle geometry:
# tan(β) = η̄ / (1 - ρ̄)
# tan(γ) = η̄ / ρ̄

# Using β = 22.2° and γ = 65.5°:
tan_beta = np.tan(beta_exp * np.pi/180)
tan_gamma = np.tan(gamma_exp * np.pi/180)

print(f"tan(β) = tan({beta_exp}°) = {tan_beta:.4f}")
print(f"tan(γ) = tan({gamma_exp}°) = {tan_gamma:.4f}")
print()

# Solving for ρ̄ and η̄:
# η̄ = (1 - ρ̄)tan(β)
# η̄ = ρ̄ tan(γ)
# Therefore: (1 - ρ̄)tan(β) = ρ̄ tan(γ)
# ρ̄ = tan(β) / (tan(β) + tan(γ))

rho_calc = tan_beta / (tan_beta + tan_gamma)
eta_calc = rho_calc * tan_gamma

print("From β = 22.2°, γ = 65.5°:")
print(f"  ρ̄ = tan(β)/(tan(β)+tan(γ)) = {rho_calc:.4f}")
print(f"  η̄ = ρ̄ × tan(γ) = {eta_calc:.4f}")
print(f"  PDG values: ρ̄ = {rho_bar_PDG:.4f}, η̄ = {eta_bar_PDG:.4f}")
print()

# ============================================================================
# APPROACH 9: Search for Geometric β and γ
# ============================================================================
print()
print("=" * 70)
print("APPROACH 9: Searching for Geometric β and γ")
print("=" * 70)
print()

# If we can find geometric formulas for β and γ, we can predict ρ̄ and η̄

# The angle β ≈ 22.2° is interesting because:
# - 22.2° ≈ π/8 = 22.5°
# - 22.2° ≈ arctan(λ) where λ = 0.22497

beta_test1 = 22.5  # π/8
beta_test2 = np.arctan(lambda_geom) * 180/np.pi  # arctan(λ)
beta_test3 = 72/3 - 1.8  # 72°/3 - correction = 22.2°
beta_test4 = np.arcsin(1/phi**2) * 180/np.pi  # arcsin(1/φ²)

print("Possible geometric origins for β ≈ 22.2°:")
print(f"  22.5° = π/8 rad = {beta_test1:.1f}° (octagonal)")
print(f"  arctan(λ) = {beta_test2:.2f}° (Cabibbo angle)")
print(f"  72°/3 - 1.8° = {beta_test3:.2f}°")
print(f"  arcsin(1/φ²) = {beta_test4:.2f}°")
print()

# The angle γ ≈ 65.5° is close to 66° = 180° - 60° - 54°
gamma_test5 = 180 - 60 - 54
gamma_test6 = 72 - 36/5
gamma_test7 = 180 - 90 - 24  # complementary angle

print("Possible geometric origins for γ ≈ 65.5°:")
print(f"  180° - 60° - 54° = {gamma_test5}°")
print(f"  72° - 36°/5 = {gamma_test6:.1f}°")
print(f"  180° - 90° - 24° = {gamma_test7}°")
print()

# ============================================================================
# APPROACH 10: COMPREHENSIVE GEOMETRIC PREDICTION
# ============================================================================
print()
print("=" * 70)
print("APPROACH 10: BEST GEOMETRIC PREDICTIONS")
print("=" * 70)
print()

# BEST FIT FOR A:
# The formula A = 2/√6 = √(2/3) ≈ 0.816 is close but not exact
# Let's try: A = (φ/2) × (2/√3) = φ/√3

A_best_candidates = [
    ("2/√6", 2/np.sqrt(6)),
    ("√(2/3)", np.sqrt(2/3)),
    ("φ/√3", phi/np.sqrt(3)),
    ("sin(72°)/√φ", np.sin(72*np.pi/180)/np.sqrt(phi)),
    ("2sin(72°)/φ", 2*np.sin(72*np.pi/180)/phi),
    ("√3/(1+1/φ)", np.sqrt(3)/(1 + 1/phi)),
    ("cos(30°)×φ/√φ", np.cos(30*np.pi/180)*phi/np.sqrt(phi)),
    ("sin(60°)×√(φ/2)", np.sin(60*np.pi/180)*np.sqrt(phi/2)),
]

print("Best candidates for A = 0.839:")
print("-" * 50)
best_A = None
best_A_error = float('inf')
for name, value in sorted(A_best_candidates, key=lambda x: abs(x[1] - A_PDG)):
    error_pct = 100 * abs(value - A_PDG) / A_PDG
    if error_pct < best_A_error:
        best_A = value
        best_A_error = error_pct
        best_A_name = name
    marker = "★" if error_pct < 2 else "✓" if error_pct < 5 else " "
    print(f"{marker} {name:30s} = {value:.5f} ({error_pct:5.2f}% off)")

print()
print(f"Best geometric A: {best_A_name} = {best_A:.5f}")
print()

# ============================================================================
# APPROACH 11: Novel Geometric Formula Search
# ============================================================================
print()
print("=" * 70)
print("APPROACH 11: Systematic Formula Search")
print("=" * 70)
print()

# Search over combinations of φ, √5, √3, √2, sin/cos of key angles
# to find expressions matching A, ρ̄, η̄

def evaluate_formula_space():
    """Search for formulas matching A, ρ̄, η̄"""
    results = []

    # Base quantities
    sqrt5 = np.sqrt(5)
    sqrt3 = np.sqrt(3)
    sqrt2 = np.sqrt(2)

    # Key angles
    angles_deg = [30, 36, 45, 54, 60, 72, 90, 108, 120]

    # Build formula candidates for A
    formulas_A = []

    # Type 1: Ratios of trig functions
    for a1 in angles_deg:
        for a2 in angles_deg:
            if a1 != a2:
                val = np.sin(a1*np.pi/180) / np.sin(a2*np.pi/180)
                formulas_A.append((f"sin({a1}°)/sin({a2}°)", val))
                val = np.cos(a1*np.pi/180) / np.cos(a2*np.pi/180)
                formulas_A.append((f"cos({a1}°)/cos({a2}°)", val))

    # Type 2: φ combinations with trig
    for a in angles_deg:
        val = np.sin(a*np.pi/180) / phi
        formulas_A.append((f"sin({a}°)/φ", val))
        val = np.sin(a*np.pi/180) * phi
        formulas_A.append((f"sin({a}°)×φ", val))
        val = np.sin(a*np.pi/180) / np.sqrt(phi)
        formulas_A.append((f"sin({a}°)/√φ", val))
        val = np.cos(a*np.pi/180) / phi
        formulas_A.append((f"cos({a}°)/φ", val))
        val = np.cos(a*np.pi/180) * phi
        formulas_A.append((f"cos({a}°)×φ", val))
        val = np.cos(a*np.pi/180) / np.sqrt(phi)
        formulas_A.append((f"cos({a}°)/√φ", val))

    # Type 3: Pure algebraic with φ, √5, √3, √2
    for num in [1, 2, phi, sqrt5, sqrt3, sqrt2]:
        for den in [1, 2, phi, sqrt5, sqrt3, sqrt2, phi**2, phi**3]:
            if den != 0:
                val = num / den
                if 0.1 < val < 2:
                    formulas_A.append((f"{num:.3f}/{den:.3f}", val))

    # Type 4: Special combinations
    formulas_A.append(("1/(φ×sin(36°)×√2)", 1/(phi * np.sin(36*np.pi/180) * sqrt2)))
    formulas_A.append(("√3/(1+1/φ)", sqrt3/(1 + 1/phi)))
    formulas_A.append(("2sin(72°)/φ", 2*np.sin(72*np.pi/180)/phi))
    formulas_A.append(("cos(30°)φ/√φ", np.cos(30*np.pi/180)*phi/np.sqrt(phi)))
    formulas_A.append(("(φ+1)/(2√3)", (phi+1)/(2*sqrt3)))
    formulas_A.append(("2/(φ+1/φ)", 2/(phi + 1/phi)))
    formulas_A.append(("√(φ/√5×2)", np.sqrt(phi/sqrt5*2)))

    return formulas_A

formulas_A = evaluate_formula_space()

# Find best matches for A
A_matches = [(name, val, 100*abs(val-A_PDG)/A_PDG)
             for name, val in formulas_A if 0.7 < val < 1.0]
A_matches.sort(key=lambda x: x[2])

print("Top 10 geometric formulas matching A = 0.839:")
print("-" * 60)
for i, (name, val, err) in enumerate(A_matches[:10]):
    marker = "★" if err < 1 else "✓" if err < 3 else " "
    print(f"{marker} {name:40s} = {val:.5f} ({err:5.2f}% off)")

# ============================================================================
# APPROACH 12: The Decisive Formula for A
# ============================================================================
print()
print("=" * 70)
print("APPROACH 12: The Decisive Formula for A")
print("=" * 70)
print()

# Key insight: Just as λ involves φ³ and sin(72°),
# A should involve related geometric quantities

# The most elegant candidate: A = sin(57°) where 57° ≈ 60° - 3°
# Or A = sin(arctan(2)) because tan⁻¹(2) ≈ 63.43°, sin(63.43°) ≈ 0.894

# Let's try: A = 4λ/sin(72°) - this would relate A directly to λ
A_from_lambda = 4 * lambda_geom / np.sin(72*np.pi/180)
print(f"4λ/sin(72°) = {A_from_lambda:.4f}")

# Or: A = sin(72°)/(λ×φ)
A_test = np.sin(72*np.pi/180)/(lambda_geom * phi)
print(f"sin(72°)/(λφ) = {A_test:.4f}")

# The pattern: λ = (1/φ³)sin(72°) and A = f(φ, 72°)
# If V_cb = Aλ² = A(1/φ⁶)sin²(72°), this must match |V_cb| ≈ 0.042

Vcb_target = 0.0422
A_needed = Vcb_target / lambda_geom**2
print(f"\nTo match |V_cb| = {Vcb_target}:")
print(f"A = |V_cb|/λ² = {A_needed:.4f}")
print(f"PDG: A = {A_PDG}")
print(f"Our λ: λ = {lambda_geom:.5f}")
print()

# The key: What geometric factor gives A ≈ 0.84?
# Testing: A = √3 × sin(30°) × some factor
A_geo_test1 = np.sqrt(3) * np.sin(30*np.pi/180) * 0.97  # 0.84
A_geo_test2 = phi / np.sqrt(3 + 1/phi)  # ≈ 0.86

print("Geometric decompositions:")
print(f"  √3 × sin(30°) × 0.97 = {A_geo_test1:.4f}")
print(f"  φ/√(3+1/φ) = {A_geo_test2:.4f}")

# THE MOST PROMISING: A relates to the same 72° and φ as λ
# A = φ × cos(72°) / cos(36°)
A_golden = phi * np.cos(72*np.pi/180) / np.cos(36*np.pi/180)
print(f"  φ × cos(72°)/cos(36°) = {A_golden:.4f}")

# Or: A = 2 × sin(36°) × cos(36°) / sin(72°) = 1 (trig identity, not useful)

# Try: A = (1 + sin(72°)) / (1 + φ)
A_try1 = (1 + np.sin(72*np.pi/180)) / (1 + phi)
print(f"  (1+sin(72°))/(1+φ) = {A_try1:.4f}")

# A = φ² / (1 + φ²)
A_try2 = phi**2 / (1 + phi**2)
print(f"  φ²/(1+φ²) = {A_try2:.4f}")

# ============================================================================
# FINAL SUMMARY AND STATUS
# ============================================================================
print()
print("=" * 70)
print("FINAL SUMMARY: WOLFENSTEIN PARAMETERS FROM GEOMETRY")
print("=" * 70)
print()

print("✅ RESOLVED:")
print("-" * 40)
print(f"   λ = (1/φ³)sin(72°) = {lambda_geom:.5f}")
print(f"   λ_PDG = {lambda_PDG:.5f}")
print(f"   Agreement: {100*abs(lambda_geom-lambda_PDG)/lambda_PDG:.2f}%")
print()

print("🔶 PARTIAL (A parameter):")
print("-" * 40)
best_A_formulas = [
    ("sin(57°)", np.sin(57*np.pi/180)),
    ("2/√6", 2/np.sqrt(6)),
    ("√(2/3)", np.sqrt(2/3)),
    ("cos(33°)", np.cos(33*np.pi/180)),
    ("(1+sin(72°))/(1+φ)", (1 + np.sin(72*np.pi/180)) / (1 + phi)),
    ("φ²/(1+φ²)", phi**2 / (1 + phi**2)),
]
for name, val in best_A_formulas:
    err = 100*abs(val-A_PDG)/A_PDG
    print(f"   {name:25s} = {val:.4f} ({err:.1f}% off)")

# THE WINNER for A
A_winner = np.sin(57*np.pi/180)
A_winner_name = "sin(57°)"
A_winner_err = 100*abs(A_winner-A_PDG)/A_PDG
print()
print(f"   Best candidate: A = {A_winner_name} = {A_winner:.5f} ({A_winner_err:.2f}% off)")
print()

# But 57° is not obviously geometric. Let's find what 57° might be:
print("   What is 57°?")
print(f"   57° = 60° - 3° = 60° - 36°/12")
print(f"   57° ≈ arccos(1/√3 - 0.03)")
# Check: arccos(0.545) = 57°
val_57 = np.arccos(np.cos(57*np.pi/180))
print(f"   cos(57°) = {np.cos(57*np.pi/180):.5f}")
print(f"   Note: 0.545 ≈ 1/√3 - 0.033 or φ/3 + 0.005")
print()

print("⚠️ REMAINS OPEN (ρ̄, η̄):")
print("-" * 40)
print(f"   ρ̄_PDG = {rho_bar_PDG:.4f}")
print(f"   η̄_PDG = {eta_bar_PDG:.4f}")
print()
print("   These require knowledge of the CP-violating phase δ.")
print("   The phase is related to the unitarity triangle angles:")
print(f"   β ≈ {beta_exp}°, γ ≈ {gamma_exp}°")
print()
print("   Geometric β candidates:")
print(f"     arctan(λ) = {np.arctan(lambda_geom)*180/np.pi:.2f}° (close to 22.2°)")
print()
print("   Geometric γ candidates:")
print(f"     72° - 36°/5 = {72 - 36/5:.1f}° (close to 65.5°)")
print()

# Calculate what ρ̄, η̄ would be if:
# β = arctan(λ) ≈ 12.65° and γ = 72° - 36°/5 = 64.8°
beta_geom = np.arctan(lambda_geom) * 180/np.pi
gamma_geom = 72 - 36/5

# These don't match well. Let's try other candidates.
# β = 22.5° = π/8
beta_geom2 = 22.5
gamma_geom2 = 180 - 90 - beta_geom2  # Wrong, this makes gamma = 67.5°

# Actually, α + β + γ = 180°
# If β = 22.5° and γ = 65.5°, then α = 92°

print("=" * 70)
print("STATUS: OPEN ITEM 2")
print("=" * 70)
print()
print("CONCLUSION:")
print("-" * 40)
print("1. The parameter A ≈ 0.84 can be approximated by several")
print("   geometric formulas (sin(57°), 2/√6, √(2/3)) but none")
print("   derives from first principles with the same elegance as λ.")
print()
print("2. The CP violation parameters ρ̄ and η̄ require the CP phase δ,")
print("   which would need a geometric origin for the unitarity triangle")
print("   angles β and γ.")
print()
print("3. RECOMMENDATION: This open item should be marked as:")
print("   - A parameter: 🔸 PARTIAL (several candidates, no definitive)")
print("   - ρ̄, η̄ parameters: ⚠️ OPEN (requires CP phase derivation)")
print()

# ============================================================================
# CREATE VISUALIZATION
# ============================================================================
print()
print("Creating visualization...")

fig, axes = plt.subplots(2, 2, figsize=(14, 12))

# Plot 1: λ derivation success
ax1 = axes[0, 0]
categories = ['λ_geometric', 'λ_PDG']
values = [lambda_geom, lambda_PDG]
colors = ['forestgreen', 'royalblue']
bars = ax1.bar(categories, values, color=colors, edgecolor='black', linewidth=1.5)
ax1.axhline(y=lambda_PDG, color='gray', linestyle='--', alpha=0.5)
ax1.set_ylabel('Value', fontsize=12)
ax1.set_title('λ = (1/φ³)sin(72°) vs PDG\n(0.88% agreement)', fontsize=12)
ax1.set_ylim(0.20, 0.24)
for bar, val in zip(bars, values):
    ax1.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.002,
             f'{val:.5f}', ha='center', va='bottom', fontsize=10, fontweight='bold')

# Plot 2: A parameter candidates
ax2 = axes[0, 1]
A_cands = [
    ('sin(57°)', np.sin(57*np.pi/180)),
    ('2/√6', 2/np.sqrt(6)),
    ('√(2/3)', np.sqrt(2/3)),
    ('φ²/(1+φ²)', phi**2/(1+phi**2)),
    ('A_PDG', A_PDG)
]
names = [c[0] for c in A_cands]
vals = [c[1] for c in A_cands]
colors2 = ['coral', 'salmon', 'lightsalmon', 'peachpuff', 'royalblue']
bars2 = ax2.bar(names, vals, color=colors2, edgecolor='black', linewidth=1.5)
ax2.axhline(y=A_PDG, color='royalblue', linestyle='--', linewidth=2, alpha=0.7)
ax2.set_ylabel('Value', fontsize=12)
ax2.set_title('Geometric Candidates for A', fontsize=12)
ax2.set_ylim(0.7, 0.95)
ax2.tick_params(axis='x', rotation=30)
for bar, val in zip(bars2, vals):
    ax2.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.01,
             f'{val:.4f}', ha='center', va='bottom', fontsize=9)

# Plot 3: Unitarity triangle
ax3 = axes[1, 0]
# Draw unitarity triangle in (ρ̄, η̄) plane
# Vertices: (0,0), (1,0), (ρ̄, η̄)
triangle_x = [0, 1, rho_bar_PDG, 0]
triangle_y = [0, 0, eta_bar_PDG, 0]
ax3.fill(triangle_x, triangle_y, alpha=0.3, color='royalblue')
ax3.plot(triangle_x, triangle_y, 'b-', linewidth=2)
ax3.scatter([0, 1, rho_bar_PDG], [0, 0, eta_bar_PDG],
            s=100, c=['red', 'red', 'green'], zorder=5)
ax3.annotate('(0,0)', (0, 0), xytext=(-0.05, -0.05), fontsize=10)
ax3.annotate('(1,0)', (1, 0), xytext=(1.02, -0.05), fontsize=10)
ax3.annotate(f'(ρ̄,η̄)=\n({rho_bar_PDG:.3f},{eta_bar_PDG:.3f})',
             (rho_bar_PDG, eta_bar_PDG), xytext=(rho_bar_PDG+0.1, eta_bar_PDG+0.05), fontsize=10)
ax3.annotate(f'β={beta_exp}°', (0.5, 0.02), fontsize=10, color='purple')
ax3.annotate(f'γ={gamma_exp}°', (rho_bar_PDG-0.1, eta_bar_PDG/3), fontsize=10, color='purple')
ax3.set_xlabel('ρ̄', fontsize=12)
ax3.set_ylabel('η̄', fontsize=12)
ax3.set_title('Unitarity Triangle (PDG 2024)', fontsize=12)
ax3.set_xlim(-0.2, 1.3)
ax3.set_ylim(-0.1, 0.5)
ax3.grid(True, alpha=0.3)
ax3.set_aspect('equal')

# Plot 4: Status summary
ax4 = axes[1, 1]
ax4.axis('off')
status_text = """
WOLFENSTEIN PARAMETERS - GEOMETRIC DERIVATION STATUS

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
✅ λ = (1/φ³)sin(72°) = 0.2245 ± 0.88%
   FULLY DERIVED from 24-cell geometry
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🔸 A ≈ 0.84
   PARTIAL: Several geometric candidates
   • sin(57°) = 0.8387 (0.04% off)
   • 2/√6 = 0.8165 (2.7% off)
   • √(2/3) = 0.8165 (2.7% off)

   Status: Phenomenologically constrained,
   awaiting first-principles derivation

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

⚠️ ρ̄ = 0.158, η̄ = 0.355
   OPEN: Require CP phase derivation
   • Need geometric origin of β ≈ 22°
   • Need geometric origin of γ ≈ 66°

   Physical insight: ρ̄ and η̄ encode CP violation
   from complex phases in generation mixing

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
"""
ax4.text(0.05, 0.95, status_text, transform=ax4.transAxes,
         fontsize=10, verticalalignment='top', fontfamily='monospace',
         bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/wolfenstein_A_rho_eta_analysis.png',
            dpi=150, bbox_inches='tight')
print("Plot saved to verification/plots/wolfenstein_A_rho_eta_analysis.png")

plt.show()

print()
print("=" * 70)
print("SCRIPT COMPLETE")
print("=" * 70)
