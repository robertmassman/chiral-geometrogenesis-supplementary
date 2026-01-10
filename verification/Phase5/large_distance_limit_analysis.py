"""
Large-Distance Limit Analysis for Theorem 3.0.3
================================================

Issue C2: The theorem claims VEV → constant at |x| → ∞
Reality: VEV → 0 at large distances

This script analyzes the actual behavior.

Date: 2025-12-23
"""

import numpy as np
import matplotlib.pyplot as plt

print("=" * 70)
print("LARGE-DISTANCE LIMIT ANALYSIS")
print("=" * 70)

# Define vertices (unnormalized for clarity)
R = np.array([1, -1, -1])
G = np.array([-1, 1, -1])
B = np.array([-1, -1, 1])

def pressure(x, x_c, epsilon=0.1):
    """Pressure function P_c(x) = 1/(|x - x_c|² + ε²)"""
    r_sq = np.sum((x - x_c)**2)
    return 1.0 / (r_sq + epsilon**2)

def compute_vev_squared(x, a0=1.0, epsilon=0.1):
    """
    Compute v_χ²(x) = (a₀²/2)[(P_R-P_G)² + (P_G-P_B)² + (P_B-P_R)²]
    """
    P_R = pressure(x, R, epsilon)
    P_G = pressure(x, G, epsilon)
    P_B = pressure(x, B, epsilon)
    vev_sq = (a0**2 / 2) * ((P_R - P_G)**2 + (P_G - P_B)**2 + (P_B - P_R)**2)
    return vev_sq, P_R, P_G, P_B

print("\n" + "=" * 70)
print("ANALYSIS 1: VEV behavior along different directions")
print("=" * 70)

# Test along x-axis (away from all vertices)
print("\nAlong x-axis (1,0,0):")
print("-" * 50)
print(f"{'|x|':<10} {'VEV':<15} {'P_R':<15} {'P_G':<15} {'P_B':<15}")
print("-" * 50)

for r in [1, 2, 5, 10, 20, 50, 100, 1000]:
    x = np.array([r, 0, 0])
    vev_sq, P_R, P_G, P_B = compute_vev_squared(x)
    vev = np.sqrt(vev_sq)
    print(f"{r:<10} {vev:<15.6e} {P_R:<15.6e} {P_G:<15.6e} {P_B:<15.6e}")

print("\n" + "=" * 70)
print("ANALYSIS 2: Asymptotic behavior")
print("=" * 70)

# At large |x|, all pressures → 1/|x|² (since |x-x_c| ≈ |x|)
# But the DIFFERENCES matter for VEV

print("""
Asymptotic analysis:

For large |x| with x = r·n̂ (unit direction n̂):
  |x - x_c|² = r² - 2r(n̂·x_c) + |x_c|²
             ≈ r² (1 - 2(n̂·x_c)/r)   for large r

So:
  P_c(x) = 1/(r² - 2r(n̂·x_c) + |x_c|² + ε²)
         ≈ 1/r² · [1 + 2(n̂·x_c)/r + O(1/r²)]
         = 1/r² + 2(n̂·x_c)/r³ + O(1/r⁴)

For the difference P_R - P_G:
  P_R - P_G ≈ 2(n̂·R - n̂·G)/r³ = 2n̂·(R-G)/r³

Since R-G = (2,-2,0), G-B = (0,2,-2), B-R = (-2,0,2):
  P_R - P_G ≈ 2n̂·(2,-2,0)/r³ = 4(n_x - n_y)/r³
  P_G - P_B ≈ 2n̂·(0,2,-2)/r³ = 4(n_y - n_z)/r³
  P_B - P_R ≈ 2n̂·(-2,0,2)/r³ = 4(n_z - n_x)/r³

Therefore:
  v_χ² = (a₀²/2)[(P_R-P_G)² + ...]
       ∝ 1/r⁶ × [(n_x-n_y)² + (n_y-n_z)² + (n_z-n_x)²]

So:
  v_χ ∝ 1/r³ → 0 as r → ∞

This is MUCH faster than VEV → constant!
""")

# Verify numerically
print("\nNumerical verification of VEV ∝ 1/r³:")
print("-" * 40)
print(f"{'r':<10} {'VEV':<15} {'VEV × r³':<15}")
print("-" * 40)

direction = np.array([1, 0, 0])  # Along x-axis
for r in [10, 20, 50, 100, 200, 500, 1000]:
    x = r * direction
    vev_sq, _, _, _ = compute_vev_squared(x)
    vev = np.sqrt(vev_sq)
    scaled = vev * r**3
    print(f"{r:<10} {vev:<15.6e} {scaled:<15.4f}")

print("\nThe product VEV × r³ approaches a constant, confirming VEV ∝ 1/r³")

print("\n" + "=" * 70)
print("ANALYSIS 3: Special case - along W-axis")
print("=" * 70)

W = np.array([1, 1, 1]) / np.sqrt(3)
print("\nAlong W-axis (1,1,1)/√3:")
print("For points on W-axis, n_x = n_y = n_z, so:")
print("  (n_x-n_y)² + (n_y-n_z)² + (n_z-n_x)² = 0")
print("Therefore VEV = 0 identically on W-axis (all distances, not just large)")
print("\nNumerical verification:")
for r in [1, 10, 100]:
    x = r * W
    vev_sq, P_R, P_G, P_B = compute_vev_squared(x)
    print(f"  r={r}: VEV² = {vev_sq:.2e}, P_R={P_R:.4f}, P_G={P_G:.4f}, P_B={P_B:.4f}")

print("\n" + "=" * 70)
print("CORRECTION NEEDED FOR THEOREM 3.0.3 §9.3")
print("=" * 70)

print("""
CURRENT CLAIM (§9.3 "Limit 2"):
  "As |x| → ∞: Pressures P_c → 0, VEV approaches constant value"

CORRECT BEHAVIOR:
  As |x| → ∞:
  - Individual pressures: P_c → 1/|x|² → 0 ✓
  - Pressure differences: (P_R - P_G) → 1/|x|³ → 0
  - VEV magnitude: v_χ → 1/|x|³ → 0

The VEV does NOT approach a constant - it decays to zero.

PHYSICAL INTERPRETATION:
  - At large distances, all three color pressures become nearly equal
  - The pressure ASYMMETRY (which determines VEV) vanishes
  - VEV ∝ 1/r³ means chiral symmetry is restored at large distances
  - This is consistent with confinement: chiral dynamics localized

NOTE: This is actually BETTER physics than "VEV → constant" because:
  - Confinement localizes chiral dynamics within ~1 fm
  - Asymptotic freedom at short distances, restoration at large distances
  - The pressure geometry naturally provides this behavior
""")

# Create visualization
fig, axes = plt.subplots(1, 2, figsize=(12, 5))

# Plot 1: VEV vs distance
r_vals = np.logspace(0, 3, 100)
vev_vals = []
for r in r_vals:
    x = r * np.array([1, 0, 0])
    vev_sq, _, _, _ = compute_vev_squared(x)
    vev_vals.append(np.sqrt(vev_sq))

axes[0].loglog(r_vals, vev_vals, 'b-', linewidth=2, label='VEV(r)')
axes[0].loglog(r_vals, 0.1/r_vals**3, 'r--', linewidth=1, label='∝ 1/r³ reference')
axes[0].set_xlabel('Distance |x|')
axes[0].set_ylabel('VEV magnitude v_χ')
axes[0].set_title('VEV decays as 1/r³ at large distances')
axes[0].legend()
axes[0].grid(True, alpha=0.3)

# Plot 2: Pressures vs distance
P_vals = {'R': [], 'G': [], 'B': []}
for r in r_vals:
    x = r * np.array([1, 0, 0])
    _, P_R, P_G, P_B = compute_vev_squared(x)
    P_vals['R'].append(P_R)
    P_vals['G'].append(P_G)
    P_vals['B'].append(P_B)

axes[1].loglog(r_vals, P_vals['R'], 'r-', linewidth=2, label='P_R')
axes[1].loglog(r_vals, P_vals['G'], 'g-', linewidth=2, label='P_G')
axes[1].loglog(r_vals, P_vals['B'], 'b-', linewidth=2, label='P_B')
axes[1].loglog(r_vals, 1/r_vals**2, 'k--', linewidth=1, label='∝ 1/r²')
axes[1].set_xlabel('Distance |x|')
axes[1].set_ylabel('Pressure P_c')
axes[1].set_title('Individual pressures decay as 1/r²')
axes[1].legend()
axes[1].grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/plots/large_distance_limit.png',
            dpi=150, bbox_inches='tight')
print("\nSaved: plots/large_distance_limit.png")

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print("""
✅ CONFIRMED: VEV → 0 as |x| → ∞ (decays as 1/r³)
❌ INCORRECT: The claim "VEV approaches constant value" is wrong

The theorem must be corrected to state:
  "As |x| → ∞: VEV → 0 (chiral symmetry restoration at large distances)"
""")
