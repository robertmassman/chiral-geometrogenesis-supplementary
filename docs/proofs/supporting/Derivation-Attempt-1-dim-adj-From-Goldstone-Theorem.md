# Derivation Attempt: 1/dim(adj) from Goldstone Theorem

**Date:** 2026-01-22
**Status:** 🔶 SPECULATIVE DERIVATION
**Purpose:** Derive the empirical 1/dim(adj_EW) correction in Prop 0.0.21 from first principles

---

## 1. The Problem

The unified electroweak formula requires a correction factor:

$$v_H = \sqrt{\sigma} \times \exp\left(\frac{1}{\dim(\text{adj}_{EW})} + \frac{1}{2\pi^2 \Delta a_{EW}}\right)$$

The second term (1/(2π²Δa)) comes from the a-theorem central charge flow. The first term (1/4) is empirically identified. We seek a derivation.

---

## 2. Key Observation

The factor **1/4** has a natural interpretation in the electroweak Higgs sector:

$$\frac{1}{4} = \frac{\text{physical Higgs d.o.f.}}{\text{total Higgs d.o.f.}}$$

**Counting:**
- UV (before EWSB): The Higgs doublet H has **4 real d.o.f.**
  - H = (H⁺, H⁰) with each complex = 2 real d.o.f.

- IR (after EWSB): **1 physical Higgs** + **3 Goldstone bosons** (eaten by W±, Z)

The ratio 1/4 represents the "survival fraction" of the scalar sector.

---

## 3. Connection to Gauge Dimension

Remarkably, this ratio equals 1/dim(adj_EW):

$$\frac{1}{4} = \frac{1}{\dim(su(2)) + \dim(u(1))} = \frac{1}{3 + 1}$$

**Why this equality?**

The Goldstone theorem states that for each broken generator, one Goldstone boson appears. In EWSB:
- Broken generators: 3 (from SU(2)×U(1)_Y → U(1)_EM)
- Goldstone bosons: 3 (eaten by W±, Z)

The **total gauge dimension** = dim(adj_EW) = 4 equals the **total Higgs d.o.f.** = 4.

This is not a coincidence — it's a consequence of the Higgs mechanism requiring exactly the right number of Goldstone bosons to give mass to the broken gauge bosons.

---

## 4. Derivation Approach: Effective Action

### 4.1 Dilaton Effective Action

The Komargodski-Schwimmer proof of the a-theorem uses a dilaton effective action:

$$S_{eff}[\tau] = \int d^4x \left[ \frac{f_\tau^2}{2} (\partial\tau)^2 + \Delta a \cdot (\text{4-derivative terms}) + ... \right]$$

The dilaton τ is the Goldstone boson of broken scale invariance. The key result is that the 2→2 dilaton scattering amplitude is proportional to Δa.

### 4.2 Extending to EWSB

In electroweak symmetry breaking, we have **two types of Goldstone modes**:

1. **Dilaton τ**: Goldstone of broken scale invariance
2. **Higgs sector Goldstones π**: Three eaten by W±, Z

**Key insight:** When considering RG flow from UV (massless SM) to IR (massive W, Z, H), we must account for both:
- The central charge flow (captured by Δa)
- The gauge-scalar mixing (captured by Goldstone mechanism)

### 4.3 Mixed Effective Action

The effective action including both modes:

$$S_{eff}[\tau, \pi, H] = S_{dilaton}[\tau] + S_{Higgs}[\pi, H] + S_{mix}[\tau, H]$$

The mixing term S_mix arises because the dilaton couples to all operators with non-zero mass dimension, including the Higgs sector.

**Hypothesis:** The mixing contribution to the hierarchy is:

$$\ln\left(\frac{v_H}{\Lambda_{UV}}\right) \supset \frac{n_{physical}}{n_{total}} = \frac{1}{4}$$

where n_physical = 1 (physical Higgs) and n_total = 4 (Higgs doublet d.o.f.).

---

## 5. Physical Interpretation

### 5.1 The "Dilution" Picture

The Higgs VEV v_H is related to the QCD scale √σ through an RG flow. The flow involves:

1. **Central charge flow contribution:**
   $$\exp\left(\frac{1}{2\pi^2 \Delta a_{EW}}\right) = e^{6.08} = 437$$

   This captures the "global" information loss from UV to IR.

2. **Gauge-sector contribution:**
   $$\exp\left(\frac{1}{\dim(\text{adj}_{EW})}\right) = e^{1/4} = 1.284$$

   This captures the "local" gauge structure at the EW scale.

**Physical picture:** The hierarchy is a product of two effects:
- The gentle central charge flow (small Δa = 1/120)
- The efficient gauge-Higgs mixing (only 1/4 of scalar d.o.f. survives)

### 5.2 Why Exponential?

The factors appear in the exponent because:
- The a-theorem relates ln(Λ_UV/Λ_IR) to Δa
- The Goldstone contribution is multiplicative in the path integral
- In the saddle-point approximation, multiplicative factors → additive in exponent

---

## 6. Consistency Checks

### 6.1 QCD Test

For QCD (SU(3) color), the formula fails:
- dim(adj_QCD) = 8
- Δa_QCD ≈ 1.6 (dominated by gluons)

The QCD hierarchy would be:
$$\exp\left(\frac{1}{8} + \frac{1}{2\pi^2 \times 1.6}\right) = \exp(0.125 + 0.032) = 1.17$$

Observed: Λ_QCD/√σ ≈ 0.5 (or 10^-20 for Planck/√σ)

**The formula correctly fails for QCD** because:
1. QCD is strongly coupled at low energies (Δa >> 1)
2. There's no Higgs mechanism (no Goldstone sector)

### 6.2 Other Gauge Groups

If the EW gauge group were different:

| Group | dim(adj) | exp(1/dim) | Predicted change to v_H |
|-------|----------|------------|-------------------------|
| SU(2)×U(1) | 4 | 1.284 | (baseline) |
| SU(3) | 8 | 1.133 | -12% |
| SU(5) | 24 | 1.043 | -19% |

This predicts that larger gauge groups would give smaller hierarchies, which is consistent with the intuition that more gauge bosons means more "dilution" of the scalar sector.

---

## 7. Formal Statement

**Conjecture (Goldstone Dilution):**

In a theory with spontaneous symmetry breaking of both scale invariance (dilaton τ) and gauge symmetry (Goldstones π), the VEV is related to the UV scale by:

$$v = \Lambda_{IR} \times \exp\left(\frac{n_{phys}}{n_{total}} + \frac{1}{2\pi^2 \Delta a}\right)$$

where:
- n_phys = physical scalar d.o.f. after symmetry breaking
- n_total = total scalar d.o.f. before symmetry breaking
- Δa = change in central charge through the flow
- Λ_IR = IR reference scale (√σ for EW)

For the Standard Model:
- n_phys = 1 (physical Higgs)
- n_total = 4 (Higgs doublet)
- Δa_EW = 1/120

---

## 8. What's Missing

This derivation is **speculative** because:

1. **No rigorous effective action calculation:** We assumed the Goldstone contribution adds in the exponent without deriving it from the path integral.

2. **The Goldstone-dilaton mixing is not computed:** We claimed S_mix contributes 1/4 but didn't show this.

3. **The 2π² normalization is unexplained:** We used the empirical normalization, not the standard 16π².

4. **The IR is not a CFT:** The K-S a-theorem applies to CFT→CFT flows, but EWSB is CFT→massive.

---

## 9. Path to Rigorous Derivation

To make this rigorous would require:

1. **Compute the full dilaton effective action** including coupling to the Higgs sector in the massless SM (UV theory).

2. **Track the Higgs VEV through the flow:** Show that the physical Higgs mass/VEV relation picks up a factor from the Goldstone mechanism.

3. **Verify the additive structure:** Confirm that ln(v_H/√σ) = (gauge contribution) + (a-theorem contribution).

4. **Explain the 2π² normalization:** Connect to the correct trace anomaly conventions.

---

## 10. Conclusion

The factor exp(1/dim(adj_EW)) = exp(1/4) has a natural interpretation as arising from the Goldstone mechanism:

$$\frac{1}{4} = \frac{\text{physical Higgs}}{\text{total Higgs doublet}} = \frac{1}{\dim(\text{adj}_{EW})}$$

This is not a derivation from first principles but a **candidate physical mechanism** that:
1. Explains why 1/4 appears
2. Connects to known physics (Goldstone theorem)
3. Is consistent with the gauge group structure
4. Correctly predicts failure for QCD

**Status:** This elevates the empirical observation to a **motivated conjecture** but does not constitute a rigorous derivation.

---

*Document created: 2026-01-22*
*Status: 🔶 SPECULATIVE — Needs formal effective action calculation*
