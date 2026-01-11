# Hawking Temperature Formula Verification

## Issue

The document Derivation-5.2.5a-Surface-Gravity.md writes (line 125):
```
T_H = ℏκ/(2πk_Bc)
```

But standard references give:
```
T_H = ℏκ/(2πk_B)  (Wald, Carroll, MTW)
```

Is there an extra c or not?

## Dimensional Analysis

### Option 1: T_H = ℏκ/(2πk_B)

**Dimensions:**
- [ℏ] = J·s = kg·m²/s
- [κ] = 1/s
- [k_B] = J/K = kg·m²/(s²·K)
- [ℏκ/k_B] = (kg·m²/s × 1/s) / (kg·m²/(s²·K)) = (kg·m²/s²) / (kg·m²/(s²·K)) = K ✅

**Result:** Dimensionally correct ✅

### Option 2: T_H = ℏκ/(2πk_Bc)

**Dimensions:**
- [ℏκ/(k_Bc)] = (kg·m²/s × 1/s) / ((kg·m²/(s²·K)) × m/s)
- = (kg·m²/s²) / (kg·m³/(s³·K))
- = (kg·m²/s²) × (s³·K)/(kg·m³)
- = K·s/m
- This is NOT temperature! ❌

**Result:** Dimensionally INCORRECT ❌

## Derivation from Surface Gravity

Surface gravity: κ = c³/(4GM)

**Method 1: Using κ directly**
```
T_H = ℏκ/(2πk_B)
    = ℏ/(2πk_B) × c³/(4GM)
    = ℏc³/(8πk_BG M)
```

This matches Hawking's formula! ✅

**Method 2: Trying to use extra c**
```
T_H = ℏκ/(2πk_Bc)  [claimed in document]
    = ℏ/(2πk_Bc) × c³/(4GM)
    = ℏc²/(8πk_BG M)
```

This has c² instead of c³, which is WRONG! ❌

## Literature Check

**Hawking (1975):** T = ℏc³/(8πk_BG M) for Schwarzschild

**From κ definition:**
- κ = c³/(4GM)
- Therefore: T = ℏκ/(2πk_B) ✅ (no extra c)

**Carroll "Spacetime and Geometry":** T = ℏκ/(2πk_B)

**Wald "General Relativity":** T = ℏκ/(2π) in units where k_B=1

**MTW "Gravitation":** κ/2π gives temperature in geometrized units

## Natural Units Confusion

In natural units where ℏ = c = k_B = 1:
```
T_H = κ/(2π)
```

Restoring ALL units:
```
T_H = ℏκ/(2πk_B)
```

NOT:
```
T_H = ℏκ/(2πk_Bc)  ← WRONG
```

The confusion might arise because κ already has the correct c dependence built in.

## Conclusion

**CORRECT formula:** T_H = ℏκ/(2πk_B)

**INCORRECT formula:** T_H = ℏκ/(2πk_Bc) ← This is what the document says

**Error type:** Extra c in denominator

**Impact:** Formula as written is dimensionally inconsistent, but numerical calculations in Python script are correct (they use the right formula)

**Recommendation:** Remove the extra c from lines 125 and 241 in Derivation-5.2.5a-Surface-Gravity.md

## Numerical Verification

Using Python:
```python
M = M_sun = 1.989e30  # kg
kappa = c**3 / (4 * G * M) = 5.074e4  # s^-1

# Correct formula:
T_H = hbar * kappa / (2 * pi * k_B)
    = 1.054e-34 * 5.074e4 / (2 * 3.14159 * 1.381e-23)
    = 6.168e-8 K  ✅

# If we used the document's formula:
T_H_wrong = hbar * kappa / (2 * pi * k_B * c)
    = 6.168e-8 / 2.998e8
    = 2.058e-16 K/m  ← NOT TEMPERATURE! ❌
```

**Verified:** The correct formula has NO extra c in denominator.
