"""
SU(3) Weight Normalization: Stella Octangula Vertex Mapping

Question: What scaling factor on hypercharge Y makes the fundamental
representation weight vectors form an equilateral triangle?

Standard SU(3) fundamental weights (T3, Y):
  u = (+1/2, +1/3)
  d = (-1/2, +1/3)
  s = (0,   -2/3)
"""

import numpy as np

# ============================================================
# Step 1: Standard (unscaled) weight vectors
# ============================================================
u = np.array([+1/2, +1/3])
d = np.array([-1/2, +1/3])
s = np.array([0,   -2/3])

print("=" * 60)
print("STEP 1: Standard SU(3) fundamental weights (T3, Y)")
print("=" * 60)
print(f"  u = ({u[0]:+.4f}, {u[1]:+.4f})")
print(f"  d = ({d[0]:+.4f}, {d[1]:+.4f})")
print(f"  s = ({s[0]:+.4f}, {s[1]:+.4f})")

# Compute side lengths
d_ud = np.linalg.norm(u - d)
d_us = np.linalg.norm(u - s)
d_ds = np.linalg.norm(d - s)

print(f"\nSide lengths (unscaled):")
print(f"  |u - d| = {d_ud:.6f}")
print(f"  |u - s| = {d_us:.6f}")
print(f"  |d - s| = {d_ds:.6f}")
print(f"\nRatio |u-s| / |u-d| = {d_us / d_ud:.6f}")
print(f"For equilateral, this ratio must = 1.0")

# ============================================================
# Step 2: Analytical derivation of scaling factor
# ============================================================
print("\n" + "=" * 60)
print("STEP 2: Analytical derivation")
print("=" * 60)

print("""
Let alpha be the scaling factor applied to Y, so we use (T3, alpha * Y).

Scaled vertices:
  u' = (+1/2,  alpha/3)
  d' = (-1/2,  alpha/3)
  s' = (0,    -2*alpha/3)

Side lengths:
  |u' - d'| = sqrt((1)^2 + (0)^2) = 1   [always, independent of alpha]

  |u' - s'| = sqrt((1/2)^2 + (alpha/3 + 2*alpha/3)^2)
             = sqrt(1/4 + alpha^2)

For equilateral: |u' - s'| = |u' - d'| = 1
  sqrt(1/4 + alpha^2) = 1
  1/4 + alpha^2 = 1
  alpha^2 = 3/4
  alpha = sqrt(3)/2
""")

alpha_analytic = np.sqrt(3) / 2
print(f"  Analytical result: alpha = sqrt(3)/2 = {alpha_analytic:.6f}")

# ============================================================
# Step 3: Verify with alpha = sqrt(3)/2
# ============================================================
print("\n" + "=" * 60)
print("STEP 3: Verify with alpha = sqrt(3)/2")
print("=" * 60)

alpha = np.sqrt(3) / 2
u_s = np.array([+1/2, alpha * (+1/3)])
d_s = np.array([-1/2, alpha * (+1/3)])
s_s = np.array([0,    alpha * (-2/3)])

print(f"  u' = ({u_s[0]:+.6f}, {u_s[1]:+.6f})")
print(f"  d' = ({d_s[0]:+.6f}, {d_s[1]:+.6f})")
print(f"  s' = ({s_s[0]:+.6f}, {s_s[1]:+.6f})")

d_ud_s = np.linalg.norm(u_s - d_s)
d_us_s = np.linalg.norm(u_s - s_s)
d_ds_s = np.linalg.norm(d_s - s_s)

print(f"\n  |u' - d'| = {d_ud_s:.10f}")
print(f"  |u' - s'| = {d_us_s:.10f}")
print(f"  |d' - s'| = {d_ds_s:.10f}")
print(f"\n  All equal? {np.allclose(d_ud_s, d_us_s) and np.allclose(d_us_s, d_ds_s)}")
print(f"  Side length = {d_ud_s:.10f}")

# ============================================================
# Step 4: Check the WRONG answer alpha = 2/sqrt(3)
# ============================================================
print("\n" + "=" * 60)
print("STEP 4: Check the WRONG candidate alpha = 2/sqrt(3)")
print("=" * 60)

alpha_wrong = 2 / np.sqrt(3)
u_w = np.array([+1/2, alpha_wrong * (+1/3)])
d_w = np.array([-1/2, alpha_wrong * (+1/3)])
s_w = np.array([0,    alpha_wrong * (-2/3)])

print(f"  alpha = 2/sqrt(3) = {alpha_wrong:.6f}")
print(f"  u' = ({u_w[0]:+.6f}, {u_w[1]:+.6f})")
print(f"  d' = ({d_w[0]:+.6f}, {d_w[1]:+.6f})")
print(f"  s' = ({s_w[0]:+.6f}, {s_w[1]:+.6f})")

d_ud_w = np.linalg.norm(u_w - d_w)
d_us_w = np.linalg.norm(u_w - s_w)
d_ds_w = np.linalg.norm(d_w - s_w)

print(f"\n  |u' - d'| = {d_ud_w:.10f}")
print(f"  |u' - s'| = {d_us_w:.10f}")
print(f"  |d' - s'| = {d_ds_w:.10f}")
print(f"\n  All equal? {np.allclose(d_ud_w, d_us_w) and np.allclose(d_us_w, d_ds_w)}")
print(f"  Ratio |u'-s'|/|u'-d'| = {d_us_w / d_ud_w:.6f}  (should be 1.0 for equilateral)")

# ============================================================
# Step 5: What does alpha = 2/sqrt(3) actually do?
# ============================================================
print("\n" + "=" * 60)
print("STEP 5: What alpha = 2/sqrt(3) actually produces")
print("=" * 60)

print(f"""
  With alpha = 2/sqrt(3):
    Side u-d = {d_ud_w:.6f}
    Side u-s = {d_us_w:.6f}
    Side d-s = {d_ds_w:.6f}

  This is NOT equilateral. The u-s and d-s sides are longer than u-d.

  Note: 2/sqrt(3) = sqrt(3)/2 * (4/3).  It overshoots.

  With alpha = 2/sqrt(3), the triangle has side ratio:
    |u-s|/|u-d| = {d_us_w/d_ud_w:.6f}
""")

# ============================================================
# Step 6: Relationship between the two factors
# ============================================================
print("=" * 60)
print("STEP 6: Relationship between sqrt(3)/2 and 2/sqrt(3)")
print("=" * 60)

print(f"""
  sqrt(3)/2  = {np.sqrt(3)/2:.10f}
  2/sqrt(3)  = {2/np.sqrt(3):.10f}

  They are reciprocals of each other (up to a factor):
    sqrt(3)/2 * 2/sqrt(3) = {(np.sqrt(3)/2) * (2/np.sqrt(3)):.10f}

  So they are EXACT RECIPROCALS.

  sqrt(3)/2 = cos(30 deg) ~ 0.866
  2/sqrt(3) = sec(30 deg) ~ 1.155
""")

# ============================================================
# Step 7: Alternative normalization convention
# ============================================================
print("=" * 60)
print("STEP 7: Alternative convention — using Y' = (sqrt(3)/2) * Y")
print("=" * 60)

print("""
Some textbooks define a rescaled hypercharge:

    Y' = (sqrt(3)/2) * Y

so that the weight diagram naturally forms equilateral triangles.

This is equivalent to plotting in the (T3, Y') plane where:
    u = (+1/2, +sqrt(3)/6)   since sqrt(3)/2 * 1/3 = sqrt(3)/6
    d = (-1/2, +sqrt(3)/6)
    s = (0,    -sqrt(3)/3)   since sqrt(3)/2 * (-2/3) = -sqrt(3)/3

Let's verify these form a unit equilateral triangle:
""")

u_alt = np.array([+1/2, np.sqrt(3)/6])
d_alt = np.array([-1/2, np.sqrt(3)/6])
s_alt = np.array([0,   -np.sqrt(3)/3])

print(f"  u = ({u_alt[0]:+.6f}, {u_alt[1]:+.6f})")
print(f"  d = ({d_alt[0]:+.6f}, {d_alt[1]:+.6f})")
print(f"  s = ({s_alt[0]:+.6f}, {s_alt[1]:+.6f})")

d1 = np.linalg.norm(u_alt - d_alt)
d2 = np.linalg.norm(u_alt - s_alt)
d3 = np.linalg.norm(d_alt - s_alt)

print(f"\n  |u - d| = {d1:.10f}")
print(f"  |u - s| = {d2:.10f}")
print(f"  |d - s| = {d3:.10f}")
print(f"  Equilateral? {np.allclose(d1, d2) and np.allclose(d2, d3)}")
print(f"  Side length = 1.0? {np.isclose(d1, 1.0)}")

# ============================================================
# FINAL ANSWER
# ============================================================
print("\n" + "=" * 60)
print("FINAL ANSWER")
print("=" * 60)
print(f"""
The correct scaling factor for Y to make the fundamental
representation weight vectors form an equilateral triangle is:

    alpha = sqrt(3)/2 = {np.sqrt(3)/2:.6f}

NOT 2/sqrt(3) = {2/np.sqrt(3):.6f}.

These are reciprocals of each other. Using 2/sqrt(3) OVERSHOOTS
and produces a triangle with sides in ratio 1 : {d_us_w/d_ud_w:.4f} : {d_ds_w/d_ud_w:.4f}.

The convention Y' = (sqrt(3)/2) * Y is standard in many textbooks
(e.g., Georgi "Lie Algebras in Particle Physics", Cahn "Semi-Simple
Lie Algebras and Their Representations"). It ensures that the roots
and weights of SU(3) live on a triangular lattice with uniform spacing.
""")
