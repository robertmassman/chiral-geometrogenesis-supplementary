"""
Issue 7: UV Regime (L < a) Discussion

The theorem addresses L >> a (IR limit) but doesn't discuss what happens
when L approaches or becomes smaller than a. Let's analyze this regime.
"""

import numpy as np
import matplotlib.pyplot as plt
import os

os.makedirs('plots', exist_ok=True)

print("=" * 70)
print("ISSUE 7: UV REGIME (L ≲ a) ANALYSIS")
print("=" * 70)
print()

# The spherical averaging formula
def spherical_average(G, L):
    """⟨exp(iG·x)⟩_L = 3(sin(GL) - GL cos(GL))/(GL)³"""
    u = G * L
    if np.abs(u) < 1e-10:
        return 1.0
    return 3 * (np.sin(u) - u * np.cos(u)) / (u**3)

print("1. BEHAVIOR OF AVERAGING FORMULA")
print("=" * 70)
print()

print("The spherical averaging formula:")
print("  ⟨exp(iG·x)⟩_L = 3(sin(GL) - GL cos(GL))/(GL)³")
print()

# Analyze behavior as GL → 0
print("Taylor expansion for GL << 1 (i.e., L << a since G ~ 1/a):")
print()
print("  sin(u) ≈ u - u³/6 + u⁵/120 - ...")
print("  cos(u) ≈ 1 - u²/2 + u⁴/24 - ...")
print()
print("  sin(u) - u cos(u) = u - u³/6 - u + u³/2 + O(u⁵)")
print("                    = u³/3 + O(u⁵)")
print()
print("  ⟨exp(iG·x)⟩_L = 3(u³/3 + O(u⁵))/u³")
print("                = 1 + O(u²)")
print("                = 1 - (GL)²/10 + O((GL)⁴)")
print()

# Verify numerically
print("Numerical verification:")
print(f"  {'GL':<10} {'Exact':<15} {'1 - (GL)²/10':<15} {'Difference'}")
print("-" * 55)
for gl in [0.01, 0.1, 0.5, 1.0, 2.0]:
    exact = spherical_average(1, gl)  # G=1, L=gl
    approx = 1 - (gl)**2 / 10
    diff = exact - approx
    print(f"  {gl:<10.2f} {exact:<15.6f} {approx:<15.6f} {diff:<15.6f}")

print()
print("Key insight: For L << a (GL << 1), the average → 1")
print("This means NO suppression of anisotropic components!")
print()

# Physical interpretation
print("2. PHYSICAL INTERPRETATION")
print("=" * 70)
print()

print("The effective theory breaks down for L ≲ a:")
print()
print("• For L >> a: Averaging smooths out lattice structure → SO(3) emerges")
print("• For L ~ a:  Averaging volume contains few lattice cells → O_h visible")
print("• For L < a:  Subatomic scale, below lattice resolution → undefined")
print()

print("In the Chiral Geometrogenesis framework:")
print()
print("  If a = ℓ_P (Planck scale):")
print("    L < ℓ_P is trans-Planckian physics — the effective theory doesn't apply.")
print("    The underlying pre-geometric structure (chiral oscillations) takes over.")
print()
print("  If a ~ 0.5 fm (QCD scale):")
print("    L < 0.5 fm means sub-hadronic physics — inside individual hadrons.")
print("    The lattice picture is replaced by the single stella octangula picture.")
print()

# Plot the behavior
print("3. CREATING VISUALIZATION")
print("=" * 70)
print()

fig, axes = plt.subplots(1, 2, figsize=(14, 5))

# Left plot: suppression vs L/a
L_over_a = np.logspace(-1, 3, 200)
G = 2 * np.pi  # G_min ~ 2π/a, so G*a ~ 2π
GL_values = G * L_over_a  # This is G*L when a=1

suppression = np.array([np.abs(spherical_average(1, gl)) for gl in GL_values])

ax1 = axes[0]
ax1.loglog(L_over_a, suppression, 'b-', linewidth=2, label='Exact formula')
ax1.loglog(L_over_a, 1/(G * L_over_a)**2, 'r--', linewidth=1.5, label=r'$(a/L)^2$ asymptotic', alpha=0.7)
ax1.axvline(x=1, color='green', linestyle=':', linewidth=2, label='L = a')
ax1.axhline(y=1, color='gray', linestyle='--', alpha=0.5)

ax1.fill_between([0.1, 1], [1e-6, 1e-6], [10, 10], alpha=0.2, color='red',
                  label='UV regime: L < a')
ax1.fill_between([1, 1000], [1e-6, 1e-6], [10, 10], alpha=0.1, color='green',
                  label='IR regime: L > a')

ax1.set_xlabel(r'$L/a$', fontsize=12)
ax1.set_ylabel(r'Anisotropic component magnitude', fontsize=12)
ax1.set_title('Theorem 0.0.9: IR vs UV Regimes', fontsize=14)
ax1.set_xlim([0.1, 1000])
ax1.set_ylim([1e-6, 2])
ax1.legend(loc='upper right', fontsize=9)
ax1.grid(True, which='both', alpha=0.3)

# Right plot: linear scale near L ~ a
L_over_a_lin = np.linspace(0.1, 5, 200)
GL_lin = G * L_over_a_lin
suppression_lin = np.array([np.abs(spherical_average(1, gl)) for gl in GL_lin])

ax2 = axes[1]
ax2.plot(L_over_a_lin, suppression_lin, 'b-', linewidth=2, label='Exact formula')
ax2.axvline(x=1, color='green', linestyle=':', linewidth=2, label='L = a')
ax2.axhline(y=1, color='gray', linestyle='--', alpha=0.5)
ax2.axhline(y=0, color='gray', linestyle='-', alpha=0.3)

ax2.fill_between([0.1, 1], [-0.1, -0.1], [1.2, 1.2], alpha=0.2, color='red')
ax2.fill_between([1, 5], [-0.1, -0.1], [1.2, 1.2], alpha=0.1, color='green')

ax2.set_xlabel(r'$L/a$', fontsize=12)
ax2.set_ylabel(r'$\langle e^{iG \cdot x} \rangle_L$', fontsize=12)
ax2.set_title('Transition Region (linear scale)', fontsize=14)
ax2.set_xlim([0.1, 5])
ax2.set_ylim([-0.1, 1.1])
ax2.legend(loc='upper right', fontsize=10)
ax2.grid(True, alpha=0.3)

# Add annotations
ax2.annotate('UV: Effective theory\nbreaks down',
             xy=(0.5, 0.9), fontsize=10, ha='center',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
ax2.annotate('IR: SO(3)\nemerges',
             xy=(3, 0.2), fontsize=10, ha='center',
             bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.5))

plt.tight_layout()
plt.savefig('plots/theorem_0_0_9_uv_regime.png', dpi=150)
plt.close()

print("Plot saved to plots/theorem_0_0_9_uv_regime.png")
print()

# Proposed text
print("4. PROPOSED ADDITION TO SECTION 5.3 OR NEW SUBSECTION")
print("=" * 70)
print()
print("""
### 5.X UV Regime and Effective Theory Validity

The emergence mechanism described in this theorem is valid only for $L \\gg a$.
At scales $L \\lesssim a$, the effective theory breaks down:

**Mathematical behavior:** For small $GL$ (i.e., $L \\ll a$), the averaging formula
Taylor-expands as:
$$\\langle e^{i\\mathbf{G} \\cdot \\mathbf{x}} \\rangle_L = 1 - \\frac{(GL)^2}{10} + O((GL)^4)$$

This approaches unity rather than zero, meaning anisotropic components are
*not* suppressed when $L < a$.

**Physical interpretation:**
- **For $L \\gg a$:** Coarse-graining averages over many lattice cells;
  effective SO(3) symmetry emerges.
- **For $L \\sim a$:** The averaging volume contains $O(1)$ lattice cells;
  discrete $O_h$ structure is directly visible.
- **For $L < a$:** The observation scale is below the lattice spacing.
  The effective field theory picture breaks down entirely.

**In the Chiral Geometrogenesis framework:**

When $a = \\ell_P$ (Planck-scale lattice), scales $L < \\ell_P$ represent
trans-Planckian physics where the entire continuum spacetime description
fails. The underlying pre-geometric structure—chiral field oscillations on
the stella octangula—provides the more fundamental description at these scales.

This is analogous to how fluid mechanics breaks down at molecular scales:
the effective theory is not "wrong" but simply not applicable beyond its
domain of validity.
""")
