#!/usr/bin/env python3
"""Final clarification on Section 5.3 arithmetic error."""
import numpy as np

# The FORMULA is correct:
# Gamma = G_F^2 * M_W^2 * alpha * m_H^3 / (64*pi^4) * (1-MZ^2/mH^2)^3 * |A|^2

G_F = 1.1664e-5
M_W = 80.37
alpha = 1/137.036
m_H = 125.20
M_Z = 91.19

print("SECTION 5.3 STEP 1 ERROR ANALYSIS")
print("="*60)
print()
print("Prop writes:")
print("  G_F^2 M_W^2 alpha / (64 pi^4)")
print(f"  = (1.1664e-5)^2 * (80.37)^2 * (1/137.036) / (64 * pi^4)")
print()

# Line 2 of the prop:
print("Prop line 2:")
print("  = {1.360e-10 * 6459 * 7.297e-3} / {64 * 97.41}")
print()
print("Analysis of numerator: 1.360e-10 * 6459 * 7.297e-3")
step1 = 1.360e-10 * 6459
print(f"  1.360e-10 * 6459 = {step1:.4e}")
step2 = step1 * 7.297e-3
print(f"  * 7.297e-3 = {step2:.4e}")
print()
print("Prop line 3:")
print("  = {6.412e-10} / {6234} = 1.029e-13 GeV^-2")
print()
print(f"  ACTUAL numerator: {step2:.4e}")
print(f"  Prop claims: 6.412e-10")
print(f"  Correct value: 6.410e-9")
print()
print("  *** The Prop wrote 6.412e-10 instead of 6.412e-9 ***")
print("  *** This is a factor of 10 error in the INTERMEDIATE step ***")
print()
print("  However, the FINAL answer 1.029e-13 is also wrong:")
print(f"  6.412e-10 / 6234 = {6.412e-10/6234:.4e} (what Prop gets)")
print(f"  6.412e-9 / 6234 = {6.412e-9/6234:.4e} (correct)")
print()

# Now check the full width with correct prefactor
pf_correct = G_F**2 * M_W**2 * alpha / (64 * np.pi**4)
ps = (1 - M_Z**2/m_H**2)**3
mH3 = m_H**3
A2 = 29.9

print("FULL WIDTH CHECK:")
print(f"  Correct prefactor: {pf_correct:.4e} GeV^-2")
print(f"  Phase space: {ps:.4f}")
print(f"  m_H^3: {mH3:.3e} GeV^3")
print(f"  |A|^2: {A2}")
print(f"  Width = {pf_correct:.4e} * {ps:.4f} * {mH3:.3e} * {A2}")
print(f"        = {pf_correct * ps * mH3 * A2:.4e} GeV")
print(f"        = {pf_correct * ps * mH3 * A2 * 1e6:.2f} keV")
print()

# With Prop's wrong prefactor
pf_wrong = 1.029e-13
width_wrong = pf_wrong * ps * mH3 * A2
print(f"  With Prop prefactor (1.029e-13):")
print(f"  Width = {width_wrong:.4e} GeV = {width_wrong*1e6:.3f} keV")
print(f"  *** This gives 0.6 keV, not 6 keV! ***")
print()

# But the Prop then writes in Step 5:
# Width = 1.029e-13 * 0.103 * 1.963e6 * 29.9 = 6.23e-6 GeV
# Let me check: 1.029e-13 * 0.103 * 1.963e6 * 29.9
wrong_calc = 1.029e-13 * 0.103 * 1.963e6 * 29.9
print(f"  Prop Step 5: 1.029e-13 * 0.103 * 1.963e6 * 29.9 = {wrong_calc:.4e}")
print(f"  = {wrong_calc*1e6:.3f} keV")
print(f"  *** This is 0.6 keV, not 6.23e-6 GeV as the Prop claims! ***")
print()
print(f"  Prop writes the answer as 6.23e-6 GeV = 6.2 keV")
print(f"  But 1.029e-13 * 0.103 * 1.963e6 * 29.9 = {wrong_calc:.3e} GeV = {wrong_calc*1e6:.3f} keV")
print()
print("  The error chain:")
print("  1. Numerator computed correctly but written as e-10 instead of e-9")
print("  2. Prefactor written as 1.029e-13 instead of 1.029e-12")
print("  3. Final multiplication somehow gets the right answer 6.23e-6")
print("  4. Consistent explanation: Prop meant 1.029e-12 but typed e-13")
print()

# Verify with 1.029e-12
width_right = 1.029e-12 * 0.103 * 1.963e6 * 29.9
print(f"  With 1.029e-12: {width_right:.4e} GeV = {width_right*1e6:.2f} keV")
print(f"  YES: this gives 6.2 keV, matching the Prop's final answer")
print()

print("CONCLUSION:")
print("  The FORMULA and FINAL ANSWER are correct.")
print("  The prefactor should be ~1.03e-12, not 1.029e-13.")
print("  This is a TYPOGRAPHICAL ERROR in the exponent (-13 should be -12)")
print("  that propagates from the earlier error (6.412e-10 should be 6.412e-9).")
print("  The final answer 6.2 keV is correct and matches independent calculation.")
