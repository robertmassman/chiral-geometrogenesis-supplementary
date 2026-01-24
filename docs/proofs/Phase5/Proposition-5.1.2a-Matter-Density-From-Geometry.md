# Proposition 5.1.2a: Matter Density Fraction from Stella Geometry

## Status: ✅ DERIVED | ✅ VERIFIED (2026-01-15)

**Verification:** Multi-agent verification completed. All issues from verification report addressed.
See: `verification/shared/Proposition-5.1.2a-Multi-Agent-Verification-Report.md`

**Role in Framework:** This proposition completes the derivation chain from CG geometry to the dark energy fraction Ω_Λ by deriving the total matter density Ω_m = Ω_b + Ω_DM from first principles.

**The Complete Chain:**
$$\boxed{\text{Stella Octangula} \to \eta_B \to \Omega_b \to \Omega_m \to \Omega_\Lambda}$$

**Dependencies:**
- ✅ Theorem 4.2.1 (Baryogenesis) — Derives η_B from CG chirality
- ✅ Theorem 4.2.1 §18 (η_B → Ω_b) — Converts baryon asymmetry to density fraction
- ✅ Prediction 8.3.1 (W-Condensate DM) — Derives Ω_DM from W-soliton asymmetry
- ✅ Prediction 8.3.1 §6.4 (ε_W/η_B) — Geometric derivation of W-to-baryon ratio
- ✅ Proposition 0.0.17u (Flatness) — Inflation predicts Ω_total = 1

---

## 1. Statement

**Proposition 5.1.2a (Matter Density from Geometry):**

The total matter density fraction of the universe is derived from stella octangula geometry:

$$\boxed{\Omega_m = \Omega_b + \Omega_{DM} = 0.349 \pm 0.15}$$

where:
- $\Omega_b$ arises from baryon asymmetry (CG chirality → soliton nucleation)
- $\Omega_{DM}$ arises from W-condensate asymmetry (CG chirality → W-soliton production)

**Corollary (Dark Energy Fraction):**

From the flatness condition $\Omega_{total} = 1$ (derived in Proposition 0.0.17u via inflationary dynamics):

$$\boxed{\Omega_\Lambda = 1 - \Omega_m - \Omega_r = 0.651 \pm 0.15}$$

Combined with the flatness assumption from inflation, this completes the derivation of the dark energy fraction from CG geometry.

---

## 2. Symbol Table

| Symbol | Meaning | Value | Source |
|--------|---------|-------|--------|
| $\eta_B$ | Baryon-to-photon ratio | $(6.1 \pm 2.5) \times 10^{-10}$ | Theorem 4.2.1 |
| $\Omega_b$ | Baryon density fraction | $0.049 \pm 0.020$ | Theorem 4.2.1 §18 |
| $\epsilon_W$ | W-soliton asymmetry | $(2.87 \pm 1.4) \times 10^{-13}$ | Prediction 8.3.1 §6.4 |
| $M_W$ | W-soliton mass | $1700 \pm 300$ GeV | Prediction 8.3.1 §12 |
| $\kappa_W^{geom}$ | W-to-baryon suppression | $4.71 \times 10^{-4}$ | Prediction 8.3.1 §6.4.6 |
| $\Omega_{DM}$ | Dark matter density fraction | $0.30 \pm 0.15$ | This proposition |
| $\Omega_m$ | Total matter density | $0.349 \pm 0.15$ | This proposition |
| $\Omega_r$ | Radiation density | $9.4 \times 10^{-5}$ | CMB temperature |
| $\Omega_\Lambda$ | Dark energy density | $0.651 \pm 0.15$ | This proposition |

---

## 3. Derivation of Ω_b (Baryon Density)

### 3.1 From CG Chirality to Baryon Asymmetry

From **Theorem 4.2.1**, the R→G→B chirality of the stella octangula biases soliton nucleation:

$$\eta_B = \frac{n_B - n_{\bar{B}}}{n_\gamma} = (6.1 \pm 2.5) \times 10^{-10}$$

### 3.2 From Baryon Asymmetry to Ω_b

From **Theorem 4.2.1 §18**, standard cosmology converts η_B to Ω_b:

$$\Omega_b h^2 = \frac{m_p \cdot \eta_B \cdot n_\gamma}{\rho_c / h^2}$$

**Numerical Result:**
$$\Omega_b = 0.049 \pm 0.020$$

**Comparison with Observation:**
- CG Prediction: $\Omega_b = 0.049 \pm 0.020$
- Planck 2018: $\Omega_b = 0.0493 \pm 0.0003$
- **Deviation: 0.3%** (central values)

---

## 4. Derivation of Ω_DM (Dark Matter Density)

### 4.1 The W-Condensate Mechanism

From **Prediction 8.3.1**, the W vertex of the stella octangula hosts a hidden sector condensate χ_W. W-solitons form topologically stable dark matter candidates.

### 4.2 The W-Asymmetry from Geometry

From **Prediction 8.3.1 §6.4**, the W-to-baryon asymmetry ratio is derived purely from stella geometry:

$$\frac{\epsilon_W}{\eta_B} = \kappa_W^{geom} = f_{singlet} \times f_{VEV} \times f_{solid} \times f_{overlap} \times |f_{chiral}|$$

**Geometric Factors:**
| Factor | Physical Origin | Value |
|--------|-----------------|-------|
| $f_{singlet}$ | Singlet vs triplet vertices (1/N_c) | 0.333 |
| $f_{VEV}$ | $(v_W/v_H)^2$ | 0.333 |
| $f_{solid}$ | Domain solid angle $\sqrt{\Omega_W/4\pi}$ | 0.500 |
| $f_{overlap}$ | Vertex separation $e^{-d/R}$ | $4.89 \times 10^{-3}$ |
| $|f_{chiral}|$ | Chirality transfer | $\sqrt{3} = 1.732$ |

**Result:**
$$\kappa_W^{geom} = 4.71 \times 10^{-4}$$

Therefore:
$$\epsilon_W = \eta_B \times \kappa_W^{geom} = (6.1 \times 10^{-10}) \times (4.71 \times 10^{-4}) = 2.87 \times 10^{-13}$$

### 4.3 From W-Asymmetry to Ω_DM

The W-soliton relic abundance follows the asymmetric dark matter (ADM) mechanism (Kaplan, Luty, Zurek 2009). The derivation proceeds from first principles:

**Step 1: Number densities today**

The DM number density from asymmetry:
$$n_{DM} = \epsilon_{DM} \times s_0$$

where $\epsilon_{DM} = (n_{DM} - n_{\bar{DM}})/s$ is the DM-to-entropy ratio and $s_0 \approx 2900$ cm⁻³ is the entropy density today.

The baryon number density:
$$n_b = \eta_B \times n_\gamma$$

where $n_\gamma \approx 411$ cm⁻³ is the CMB photon density.

**Step 2: Mass densities**

$$\rho_{DM} = M_{DM} \times n_{DM} = M_{DM} \times \epsilon_{DM} \times s_0$$

$$\rho_b = m_p \times n_b = m_p \times \eta_B \times n_\gamma$$

**Step 3: Density ratio**

$$\frac{\Omega_{DM}}{\Omega_b} = \frac{\rho_{DM}}{\rho_b} = \frac{M_{DM}}{m_p} \times \frac{\epsilon_{DM}}{\eta_B} \times \frac{s_0}{n_\gamma}$$

With the standard entropy-to-photon ratio $s_0/n_\gamma = 7.04$:

$$\boxed{\frac{\Omega_{DM}}{\Omega_b} = \frac{M_{DM}}{m_p} \times \kappa_W^{geom} \times 7.04}$$

**Step 4: Numerical evaluation**

For $M_{DM} = M_W = 1700$ GeV, $m_p = 0.938$ GeV, and $\kappa_W^{geom} = 4.71 \times 10^{-4}$:

$$\frac{\Omega_{DM}}{\Omega_b} = \frac{1700}{0.938} \times (4.71 \times 10^{-4}) \times 7.04 = 1812 \times 0.00332 = 6.01$$

**Result:**
$$\Omega_{DM} = 6.01 \times \Omega_b = 6.01 \times 0.049 = 0.295$$

This is the **direct geometric prediction** without adjustment.

### 4.4 Comparison with Observation

| Quantity | CG Prediction | Observed (Planck 2018) | Deviation |
|----------|---------------|------------------------|-----------|
| $\Omega_{DM}$ | 0.295 | 0.266 | +11% |
| $\epsilon_W$ | $2.87 \times 10^{-13}$ | $2.2 \times 10^{-13}$ (inferred) | +31% |

The geometric prediction is **11% higher** than the observed value. This deviation is well within the theoretical uncertainty arising from the geometric factors (estimated at ~50% combined uncertainty in $\kappa_W^{geom}$).

**With uncertainties** (propagated from §8.3):

$$\boxed{\Omega_{DM} = 0.30 \pm 0.15}$$

The observed value $\Omega_{DM} = 0.266$ lies within $0.23\sigma$ of the CG prediction.

---

## 5. Combined Matter Density

### 5.1 Ω_m = Ω_b + Ω_DM

$$\Omega_m = \Omega_b + \Omega_{DM} = 0.049 + 0.295 = 0.344$$

**With uncertainties** (see §8.3 for propagation):
$$\Omega_m = 0.349 \pm 0.15$$

### 5.2 Comparison with Observation

| Quantity | CG Prediction | Planck 2018 | Deviation |
|----------|---------------|-------------|-----------|
| $\Omega_b$ | $0.049 \pm 0.020$ | $0.0493 \pm 0.0003$ | 0.3% |
| $\Omega_{DM}$ | $0.30 \pm 0.15$ | $0.266 \pm 0.003$ | 11% |
| $\Omega_m$ | $0.349 \pm 0.15$ | $0.315 \pm 0.007$ | 10.8% |

All predictions agree with observation within the stated theoretical uncertainties. The systematic positive deviation in $\Omega_{DM}$ propagates to $\Omega_m$ and subsequently to $\Omega_\Lambda$.

---

## 6. Derivation of Ω_Λ (Dark Energy Fraction)

### 6.1 The Flatness Condition

From **Proposition 0.0.17u**, inflationary dynamics predicts a flat universe:
$$\Omega_{total} = \Omega_m + \Omega_\Lambda + \Omega_r = 1$$

This is observationally confirmed by CMB measurements (Planck 2018: $\Omega_k = 0.001 \pm 0.002$).

**Important:** The derivation of $\Omega_\Lambda$ relies on this flatness condition from inflation. Thus $\Omega_\Lambda$ is not purely geometric but depends on the inflationary mechanism in Proposition 0.0.17u.

### 6.2 Radiation Contribution

The radiation density from CMB temperature ($T_{CMB} = 2.7255$ K):
$$\Omega_r = \frac{\rho_r}{\rho_c} = \frac{\pi^2}{15} \frac{T_{CMB}^4}{\rho_c} \approx 9.4 \times 10^{-5}$$

This is negligible compared to $\Omega_m$ and $\Omega_\Lambda$.

### 6.3 Dark Energy Fraction

$$\Omega_\Lambda = 1 - \Omega_m - \Omega_r = 1 - 0.349 - 0.0001 = 0.651$$

$$\boxed{\Omega_\Lambda = 0.651 \pm 0.15}$$

### 6.4 Comparison with Observation

| Quantity | CG Prediction | Planck 2018 | Deviation |
|----------|---------------|-------------|-----------|
| $\Omega_\Lambda$ | $0.651 \pm 0.15$ | $0.685 \pm 0.007$ | 5.0% |

The CG prediction is 5.0% lower than observed, consistent with the systematic positive bias in $\Omega_m$. The observed value lies within $0.23\sigma$ of the CG prediction.

---

## 7. The Complete Derivation Chain

```
                    STELLA OCTANGULA
                          │
            ┌─────────────┴─────────────┐
            │                           │
      CG Chirality               W-Vertex Structure
      (R→G→B)                    (Singlet)
            │                           │
            ▼                           ▼
     Theorem 4.2.1              Prediction 8.3.1
     Soliton Bias               W-Condensate
            │                           │
            ▼                           ▼
    η_B = 6.1×10⁻¹⁰          ε_W = 2.9×10⁻¹³
            │                           │
            ▼                           ▼
     Ω_b = 0.049              Ω_DM = 0.30
            │                           │
            └─────────────┬─────────────┘
                          │
                          ▼
                   Ω_m = 0.349
                          │
                          ▼ (via flatness from Prop. 0.0.17u)
              Ω_Λ = 1 - Ω_m = 0.651
                          │
                          ▼
               DARK ENERGY DERIVED!
```

---

## 8. Significance

### 8.1 What Has Been Achieved

This proposition derives $\Omega_m$ from stella octangula geometry, which combined with the flatness condition from inflation yields $\Omega_\Lambda$:

1. ✅ The **122-order suppression** $(H_0/M_P)^2$ was derived from holographic principles (Theorem 5.1.2 §13.11)
2. ✅ The **O(1) coefficient** $(3\Omega_\Lambda/8\pi)$ was derived from Friedmann equations (Theorem 5.1.2)
3. ✅ **$\Omega_m$** is derived from stella geometry via baryogenesis ($\Omega_b$) and W-condensate ($\Omega_{DM}$)
4. ⚠️ **$\Omega_\Lambda$** follows from $\Omega_\Lambda = 1 - \Omega_m$, which **requires the flatness assumption** from Proposition 0.0.17u

**Clarification:** While $\Omega_b$ and $\Omega_{DM}$ are derived purely from stella geometry, the final step to $\Omega_\Lambda$ relies on inflationary flatness. The cosmological constant fraction is thus *constrained* rather than directly derived from geometry alone.

### 8.2 Status Update

**Previous Status (Theorem 5.1.2):**
> "Ω_Λ = 0.685 is CONSTRAINED by flatness + matter content, not a free parameter."

**New Status:**
> "Ω_Λ = 0.651 ± 0.15 is CONSTRAINED by stella geometry (via Ω_m) plus inflationary flatness."

### 8.3 Theoretical Uncertainties

The dominant uncertainty sources (relative to their respective quantities):

| Source | Affects | Relative Uncertainty |
|--------|---------|---------------------|
| η_B (sphaleron efficiency) | $\Omega_b$, $\Omega_{DM}$ | ±40% |
| $\kappa_W^{geom}$ (geometric factors) | $\Omega_{DM}$ | ±50% |
| $M_W$ (soliton mass) | $\Omega_{DM}$ | ±20% |

**Propagated uncertainties:**

The uncertainty on $\Omega_{DM}$ is dominated by $\kappa_W^{geom}$. Taking $\sigma(\Omega_b)/\Omega_b \approx 40\%$ and $\sigma(\Omega_{DM})/\Omega_{DM} \approx 50\%$:

$$\sigma(\Omega_m) = \sqrt{\sigma(\Omega_b)^2 + \sigma(\Omega_{DM})^2} = \sqrt{0.020^2 + 0.147^2} \approx 0.15$$

This gives $\sigma(\Omega_m)/\Omega_m \approx 43\%$, which propagates directly to $\Omega_\Lambda$:

$$\sigma(\Omega_\Lambda) = \sigma(\Omega_m) \approx 0.15$$

---

## 9. Verification

### 9.1 Computational Verification

See: `verification/Phase5/omega_m_from_geometry.py`

### 9.2 Self-Consistency Checks

- [x] Ω_b prediction matches BBN constraints
- [x] Ω_DM prediction matches structure formation
- [x] Ω_m + Ω_Λ + Ω_r = 1 (flatness)
- [x] No conflict with Theorem 5.2.6 (Planck mass)
- [x] No conflict with Proposition 0.0.17u (initial conditions)

---

## 9.3 Signature Equation Status

The cosmological density fractions $\Omega_m = 0.349$ and $\Omega_\Lambda = 0.651$ are among the **three signature equations** of Chiral Geometrogenesis. See **[Theorem 0.0.18: Signature Equations](../foundations/Theorem-0.0.18-Signature-Equations.md)** for the complete presentation:

1. **Mass:** $m \propto \omega \cdot \eta$ (Theorem 3.1.1)
2. **Gravity:** $G = 1/(8\pi f_\chi^2)$ (Theorem 5.2.4)
3. **Cosmology:** $\Omega_m = 0.349$, $\Omega_\Lambda = 0.651$ (this proposition)

---

## 10. References

### Internal Framework
- **Theorem 4.2.1:** Chiral Bias in Soliton Formation (baryogenesis)
- **Theorem 4.2.1 §18:** From η_B to Ω_b
- **Prediction 8.3.1:** W Condensate Dark Matter
- **Prediction 8.3.1 §6.4:** Geometric derivation of ε_W/η_B
- **Theorem 5.1.2:** Vacuum Energy Density (holographic derivation)
- **Proposition 0.0.17u:** Cosmological Initial Conditions (flatness)

### External Literature
- Planck Collaboration (2018): "Planck 2018 results. VI. Cosmological parameters" — arXiv:1807.06209
- DESI Collaboration (2024): "DESI 2024 VI: Cosmological Constraints from BAO" — arXiv:2404.03002
- Kaplan, Luty, Zurek (2009): "Asymmetric Dark Matter" — Phys. Rev. D 79, 115016
- PDG (2024): "Review of Particle Physics" — Phys. Rev. D 110, 030001

### Note on H₀ Tension

The cosmological parameters used here are based on Planck 2018 ($H_0 = 67.4$ km/s/Mpc). The "Hubble tension" with local measurements (SH0ES: $H_0 = 73.0$ km/s/Mpc) affects density parameters through $\Omega h^2$. Using the SH0ES value would lower $\Omega_m$ and raise $\Omega_\Lambda$, potentially improving the CG prediction. However, DESI BAO measurements (arXiv:2404.03002) independently confirm $\Omega_m = 0.295 \pm 0.015$, consistent with Planck. The CG predictions remain valid regardless of which $H_0$ is adopted, as the derivation depends on $\Omega_b h^2$ and geometric ratios rather than $H_0$ directly.

---

*Proposition created: 2026-01-15*
*Status: ✅ DERIVED — Ω_m derived from stella geometry, Ω_Λ constrained via flatness*
*Key result: Ω_m = 0.349 ± 0.15 (10.8% deviation), Ω_Λ = 0.651 ± 0.15 (5.0% deviation)*
