# Definition 4.3.1: W-Sector Field Theory — Adversarial Physics Verification Report

**Verification Date:** 2026-02-25
**Reviewer:** Independent Physics Verification Agent (Adversarial)
**Document:** `docs/proofs/Phase4/Definition-4.3.1-W-Sector-Field-Theory.md`
**Related Files:** Theorem 4.3.2, Prediction 8.3.1, Definition 0.1.1, Definition 0.1.2

---

## Executive Summary

**VERIFIED: PARTIAL**

The W-sector field theory is an interesting and largely self-consistent extension of the CG framework. However, this adversarial review has identified **one critical issue** (Higgs exotic decay constraint), **two significant issues** (electroweak singlet justification and phase derivation), and **several moderate concerns** that must be addressed before the definition can be considered fully verified.

| Category | Assessment |
|----------|-----------|
| Overall Verdict | **PARTIAL** — Critical Higgs constraint unaddressed |
| Physical Issues Found | 1 CRITICAL, 2 SIGNIFICANT, 4 MODERATE |
| Limiting Cases | 3/4 pass, 1 problematic |
| Experimental Tensions | 1 CRITICAL (Higgs signal strength), 1 MODERATE (direct detection) |
| Framework Consistency | Mostly consistent, some gaps |
| Confidence | **MEDIUM** — Resolvable issues, but resolution needed |

---

## 1. CRITICAL ISSUE: Higgs Exotic Decay Constraint (NEW FINDING)

### 1.1 The Problem

The W-sector potential with parameters $\lambda_W = 0.101$ and $v_W = 123$ GeV produces a scalar excitation ("dark Higgs" $h_W$) with mass:

$$m_{h_W} = \sqrt{2 \lambda_W} \cdot v_W = \sqrt{2 \times 0.101} \times 123 \approx 55.3 \text{ GeV}$$

Since $m_{h_W} = 55.3$ GeV $< m_h/2 = 62.6$ GeV, the SM Higgs boson can decay to pairs of dark scalars:

$$h \to h_W \, h_W$$

### 1.2 Quantitative Analysis

The partial width for this decay, using the portal coupling vertex $g = \lambda_{H\Phi} v_H$:

$$\Gamma(h \to h_W h_W) = \frac{(\lambda_{H\Phi} v_H)^2}{32\pi m_h} \sqrt{1 - \frac{4 m_{h_W}^2}{m_h^2}} \approx 3.1 \text{ MeV}$$

This gives a branching ratio:

$$\text{BR}(h \to h_W h_W) = \frac{3.1 \text{ MeV}}{4.1 \text{ MeV} + 3.1 \text{ MeV}} \approx 43\%$$

The dark scalar $h_W$ decays promptly (c$\tau \sim 10^{-9}$ cm) via its Higgs mixing ($\sin^2\theta \approx 0.007$) to $b\bar{b}$, $\tau^+\tau^-$, etc. The decay is NOT invisible, but it IS an exotic Higgs decay.

### 1.3 Experimental Constraint

The LHC measures the Higgs signal strength:

$$\mu = \cos^2\theta \times (1 - \text{BR}_{\text{exotic}}) = 0.993 \times 0.569 \approx 0.565$$

The measured value is $\mu = 1.00 \pm 0.06$. The predicted value of $\mu = 0.565$ is **excluded at $> 7\sigma$**.

### 1.4 Resolution Options

| Resolution | Required Change | Feasibility | Impact |
|-----------|----------------|-------------|--------|
| Increase $\lambda_W$ to $> 0.130$ | +28% increase | **Feasible** | Pushes $m_{h_W} > m_h/2$, closing the channel |
| Reduce $\lambda_{H\Phi}$ to $< 0.01$ | Factor 3.6 reduction | Violates geometric derivation | Would weaken all portal predictions |
| Chiral Lagrangian description | Different scalar spectrum | **Plausible** — Skyrme model has no light scalar | Would require reworking the portal |
| Running coupling suppression | $\lambda_{H\Phi}(m_h) < \lambda_{H\Phi}(\Lambda)$ | Moderate | Quantitative analysis needed |

**Recommendation:** The most natural resolution is to increase $\lambda_W$ from 0.101 to $\geq 0.130$. This requires only a 28% shift, which is within the stated 20% uncertainty. Alternatively, the Skyrme Lagrangian description of the W sector may not support light scalar excitations at all (the Skyrme model famously does not have a sigma meson as a propagating degree of freedom), which would eliminate this problem entirely but requires explicit discussion.

### 1.5 Location in Document

This issue is NOT addressed in Definition 4.3.1, Theorem 4.3.2, or Prediction 8.3.1. Section 8.4 of Definition 4.3.1 discusses direct detection and relic abundance but does not mention the Higgs exotic decay constraint.

---

## 2. SIGNIFICANT ISSUE: Electroweak Singlet Justification (Section 7.2)

### 2.1 The Claim

Section 7.2 claims the W condensate is an SU(2)$_L$ singlet because it "does not participate in the electroweak SU(2)$_L \times$ U(1)$_Y$ structure that emerges from the 24-cell extension."

### 2.2 The Problem

Being a color singlet under SU(3)$_c$ does NOT automatically imply singlet status under SU(2)$_L$ or U(1)$_Y$. These are **independent** gauge groups. A concrete counterexample from the Standard Model: the Higgs boson is an SU(3)$_c$ singlet but an SU(2)$_L$ doublet with $Y = 1$.

The document references Proposition 0.0.22, which derives SU(2)$_L$ from the 24-cell root system decomposition. However, this reference establishes that SU(2)$_L$ exists as a gauge group, not that the W field is necessarily a singlet under it. The missing step is: **why does the W-sector field, which lives at the singlet vertex of SU(3), not carry any SU(2)$_L$ charge?**

### 2.3 What Would Be Needed

A rigorous derivation would need to show one of:
1. The W vertex in the 24-cell decomposition does not transform under the SU(2)$_L$ subalgebra roots
2. The representations assigned to the W field from the geometry are trivial under SU(2)$_L$
3. An explicit group-theoretic argument connecting the SU(3) singlet direction to the SU(2)$_L \times$ U(1)$_Y$ trivial representation

### 2.4 Assessment

The claim may well be correct within the CG framework, but the proof is incomplete. The current argument is essentially "W is a color singlet, therefore it's also an EW singlet," which is logically insufficient.

**Location:** Section 7.2 of Definition 4.3.1

---

## 3. SIGNIFICANT ISSUE: Phase $\phi_W = \pi$ Derivation (Section 4.2)

### 3.1 The Claimed Proof

The proof proceeds as:
1. $x_R + x_G + x_B = -x_W$ (correct geometric identity)
2. $e^{i\phi_W} = -e^{i(\phi_R + \phi_G + \phi_B)/3}$
3. Since $(\phi_R + \phi_G + \phi_B)/3 = 2\pi/3$, the RHS is $-e^{i \cdot 2\pi/3} = e^{i \cdot 5\pi/3}$
4. But then the document says "the average phase has amplitude zero" and concludes $\phi_W = \pi$

### 3.2 The Logical Gap

Step 3 would give $\phi_W = 5\pi/3$, not $\pi$. The document acknowledges that $e^{i\phi_R} + e^{i\phi_G} + e^{i\phi_B} = 0$ (the three phases sum to zero), which makes the "average phase" undefined. The proof then jumps to the conclusion that the "sign of opposition" gives $e^{i\phi_W} = -1$.

The core issue is that the vector sum $\sum e^{i\phi_c} = 0$ means there is no well-defined "average direction" for the RGB sector. The geometric opposition $x_{RGB} = -x_W$ constrains the real-space positions, not the complex phases.

### 3.3 Assessment

The result $\phi_W = \pi$ is physically reasonable (it represents maximum opposition) and may be correct as a **choice** motivated by the geometry. However, the proof as written has a logical gap. The argument from geometric opposition to phase opposition needs an additional axiom or a more rigorous derivation.

**Alternative rigorous argument:** The W phase must be Z$_3$-invariant (Section 4.1 constraint). The only $\mathbb{Z}_3$-invariant phases are $\phi_W = 0$ and $\phi_W = \pi$. The choice $\phi_W = 0$ would align W with the R field, breaking the geometric symmetry. Therefore $\phi_W = \pi$ is the unique non-trivial Z$_3$-invariant choice. This argument is simpler and actually rigorous.

**Location:** Section 4.2 of Definition 4.3.1

---

## 4. Detailed Physics Claim Verification

### 4.1 Dark by Construction (Section 7) — PARTIAL

| Gauge Group | Singlet Claimed | Justification Quality | Verdict |
|------------|----------------|----------------------|---------|
| SU(3)$_c$ | Yes | Strong — follows from weight space projection | **VERIFIED** |
| SU(2)$_L$ | Yes | Weak — references Prop 0.0.22 without deriving singlet status | **INCOMPLETE** |
| U(1)$_Y$ | Yes | Depends on SU(2)$_L$ result | **INCOMPLETE** |

### 4.2 Higgs Portal Coupling $\lambda_{H\Phi} = 0.036$ (Section 8) — VERIFIED WITH CAVEATS

The geometric derivation of the portal coupling is internally consistent:

$$\lambda_{H\Phi}^{\text{geom}} = \frac{g_0^2}{4} \cdot \frac{3\sqrt{3}}{8\pi} \cdot \ln\left(\frac{1}{\varepsilon}\right) = \frac{1}{4} \times 0.2067 \times 0.693 = 0.036$$

This matches the claimed value. The coupling is technically natural ($\lambda_{H\Phi} = 0$ restores a $\mathbb{Z}_2$ symmetry for $\Phi_W$). However:

- The parameter $\varepsilon \sim 0.5$ carries $\sim$50% uncertainty, giving $\lambda_{H\Phi} \in [0.02, 0.05]$
- The formula involves $g_0 \sim g_{QCD} \approx 1$, but $g_{QCD}$ runs; at what scale is it evaluated?

**LHC Higgs Invisible Width:** If the scalar spectrum is as described ($m_{h_W} \approx 55$ GeV), the portal coupling is **EXCLUDED** by Higgs signal strength measurements (see Critical Issue above).

### 4.3 VEV Scale $v_W = 123 \pm 15$ GeV (Section 5) — VERIFIED (self-consistency)

The self-consistency of the VEV derivation was independently verified:

$$v_W = \sqrt{\frac{\mu_W^2 - \lambda_{H\Phi} v_H^2}{2\lambda_W}} = \sqrt{\frac{5225 - 2182}{0.202}} = 122.7 \text{ GeV}$$

This matches the claimed value of 123 GeV to within 0.4%.

**Concern:** The geometric constraint $\mu_W^2/\mu_H^2 = 1/3$ is stated but not derived in this document. The derivation is deferred to Proposition 5.1.2b. The $1/3$ factor from "stella vertex counting" (1 singlet vertex out of 3+1 = 4 total) is a plausible geometric argument but lacks a rigorous field-theoretic derivation.

### 4.4 Direct Detection $\sigma_{SI} \approx 1.5 \times 10^{-47}$ cm$^2$ (Section 8.4) — VERIFIED

Independent calculation gives $\sigma_{SI} = 1.74 \times 10^{-47}$ cm$^2$, within 16% of the claimed value (the difference comes from slightly different input parameters). At $M_W \approx 1620$ GeV, the LZ 2024 limit is approximately $1.0 \times 10^{-46}$ cm$^2$, so the prediction is safely below current bounds by a factor of $\sim$6.

The claim that this is "at LZ sensitivity threshold" (Section 8.4) is slightly misleading at $M_{DM} \sim 1.6$ TeV. At this mass, LZ limits are much weaker than at the optimal mass of 40 GeV.

**DARWIN (2030s)** projected sensitivity at $\sim$1.6 TeV is $\sim 10^{-47}$ cm$^2$, which would be a decisive test.

### 4.5 Thermal Relic Abundance $\Omega h^2 \approx 23$ (Section 8.4) — VERIFIED

Independent estimate: $\langle\sigma v\rangle \sim \lambda_{H\Phi}^2/(16\pi M_W^2) \sim 1.1 \times 10^{-28}$ cm$^3$/s, giving $\Omega h^2 \sim 31$ (within factor 1.3 of the document's claim of $\Omega h^2 \approx 23$). The over-abundance by $\sim 200\times$ is confirmed.

The resolution via asymmetric dark matter (ADM) is physically reasonable and well-motivated by the CG framework's inherent chirality.

### 4.6 Soliton Mass Formula $M_W = 6\pi^2 v_W/e_W$ (Section 5.2) — VERIFIED WITH CAVEAT

The analytical coefficient $6\pi^2 \approx 59.22$ is the Bogomolny bound for the hedgehog ansatz. The numerically-optimized Adkins-Nappi-Witten coefficient is 72.92, which is 23% larger. The document acknowledges this in Theorem 4.3.2 Section 4 (Note). Using the ANW coefficient would give $M_W \approx 1993$ GeV instead of 1619 GeV.

| Formula | Coefficient | $M_W$ (GeV) | Status |
|---------|-----------|-------------|--------|
| Analytical (Bogomolny) | $6\pi^2 = 59.22$ | 1619 | Used in document |
| Numerical (ANW) | 72.92 | 1993 | Standard Skyrme result |
| Skyrme model accuracy | $\pm 30\%$ | 1130–2600 | Expected range |

The 19% discrepancy is within the Skyrme model's known 30% uncertainty. This is not a fatal flaw but should be more prominently discussed.

### 4.7 Skyrme Parameter $e_W = 4.5 \pm 0.3$ (Section 5.2) — WEAKLY JUSTIFIED

In the standard Skyrme model, $e = 4.84$ is fixed by fitting to the $N$-$\Delta$ mass splitting (1232 - 938 = 294 MeV). For the W sector, there is no analogous observable. The claim that $e_W = 4.5$ comes "from stella geometry" (deferred to Proposition 5.1.2b), but the derivation is not shown in this document. The 7% difference from the visible-sector value ($e_W/e = 0.93$) is small but unexplained.

### 4.8 Cosmological Consistency — VERIFIED

| Check | Result | Status |
|-------|--------|--------|
| BBN ($T_f \approx 81$ GeV $\gg T_{BBN} \sim 1$ MeV) | Safe | **PASS** |
| CMB (no late-time injection) | Safe | **PASS** |
| $\Delta N_{\text{eff}}$ (1 complex scalar at $T > v_W$) | $\Delta g_* = 2$ out of 106.75 | **PASS** |
| Structure formation (CDM at $z_{eq}$) | $v/c \ll 1$ for $M_W \sim 1.6$ TeV | **PASS** |
| Gravitational wave from PT | Not discussed | **OPEN** |

**Missing prediction:** A dark sector phase transition at $T \sim 100$ GeV could produce gravitational waves detectable at LISA. This is not discussed in the document.

---

## 5. Limiting Cases

| Limit | Expected Behavior | Actual Behavior | Status |
|-------|-------------------|-----------------|--------|
| $\lambda_{H\Phi} \to 0$ | Full decoupling | $\sigma_{SI} \to 0$, no thermal equilibrium, but ADM asymmetry transfer also vanishes | **ISSUE** — ADM mechanism requires portal |
| $v_W \to 0$ | Recover pure SM | W sector trivial, no solitons | **PASS** |
| $v_W \to v_H$ | Degenerate limit | $M_W \to 3.2$ TeV, cosmology inconsistent without retuning | **PASS** (expected) |
| $M_{DM} \to \infty$ | Decouple from detection | $\sigma_{SI} \propto 1/M^2 \to 0$ | **PASS** |

**Note on $\lambda_{H\Phi} \to 0$:** The ADM mechanism requires the portal for asymmetry transfer from the visible sector. If $\lambda_{H\Phi} = 0$, there is no communication channel, and no W-asymmetry is generated. The document's geometric derivation of $\kappa_W^{\text{geom}}$ (Prediction 8.3.1 Section 6.4) relies on overlap integrals at domain boundaries, which implicitly require nonzero portal coupling. This limit is therefore consistent.

---

## 6. Experimental Tensions

| Observable | CG Prediction | Experimental Bound | Tension |
|-----------|--------------|-------------------|---------|
| $\sigma_{SI}$ at 1.6 TeV | $1.7 \times 10^{-47}$ cm$^2$ | LZ: $\sim 10^{-46}$ cm$^2$ | **NONE** |
| Higgs signal strength $\mu$ | 0.565 (if $m_{h_W} < m_h/2$) | $1.00 \pm 0.06$ | **CRITICAL** ($>7\sigma$) |
| BR(h $\to$ invisible) | 0% (not invisible, but exotic) | $< 15\%$ | See Higgs $\mu$ above |
| Bullet Cluster $\sigma/m$ | $2 \times 10^{-4}$ cm$^2$/g | $< 1$ cm$^2$/g | **NONE** |
| BBN $\Delta N_{\text{eff}}$ | $\sim 0.02$ | $< 0.3$ | **NONE** |

---

## 7. Framework Consistency

### 7.1 Cross-References Checked

| Reference | Consistency | Notes |
|-----------|-------------|-------|
| Definition 0.1.1 (Stella topology) | **Consistent** | W vertex structure correctly used |
| Definition 0.1.2 (Color fields) | **Consistent** | Phase conventions match |
| Theorem 4.1.2 (Soliton mass) | **Consistent** | Same formula structure |
| Prediction 8.3.1 (Dark matter) | **Consistent** | Parameters align |
| Prop 0.0.22 (SU(2) structure) | **Incomplete** | W singlet status not fully derived |

### 7.2 Notation Consistency

No notation conflicts detected. The symbol $\chi_W$ is used consistently for the W-sector chiral field, $v_W$ for the VEV, and $\lambda_{H\Phi}$ for the portal coupling throughout the document and its downstream references.

### 7.3 Unification Point Compliance

The document correctly identifies that the W-sector mass generation is "the same mechanism" as the visible sector (Unification Point 5). The soliton stabilization by the Skyrme term is consistently applied.

---

## 8. Summary of Issues

### CRITICAL (must fix)
1. **Higgs exotic decay constraint** (Section 1 above): The dark scalar at 55 GeV with $\lambda_{H\Phi} = 0.036$ produces BR(h $\to$ exotic) $\approx 43\%$, excluded at $> 7\sigma$ by LHC data. Resolution: increase $\lambda_W$ to $> 0.130$, or argue the Skyrme Lagrangian does not support light scalar excitations.

### SIGNIFICANT (should fix)
2. **SU(2)$_L$ singlet justification** (Section 2 above): The argument for electroweak singlet status is logically incomplete. Color singlet $\not\Rightarrow$ electroweak singlet.
3. **Phase $\phi_W = \pi$ derivation** (Section 3 above): The proof has a logical gap. The Z$_3$-invariance argument provides a simpler and rigorous alternative.

### MODERATE (should address)
4. **Skyrme parameter $e_W = 4.5$**: Not derived in this document. Needs explicit justification or a wider uncertainty range.
5. **Soliton mass coefficient**: The 19% discrepancy between $6\pi^2$ and 72.92 should be more prominently discussed, with both values given.
6. **Geometric constraint $\mu_W^2/\mu_H^2 = 1/3$**: Stated without derivation. The "vertex counting" argument needs formalization.
7. **Gravitational wave prediction**: A dark sector phase transition at $T \sim v_W$ could produce GW signals at LISA. This testable prediction is not discussed.

### MINOR
8. **Direct detection claim**: The statement "at LZ sensitivity threshold" is slightly misleading at 1.6 TeV; LZ limits are much weaker at high mass. Should say "below current LZ bounds, testable at DARWIN."
9. **ADM mechanism in $\lambda_{H\Phi} \to 0$ limit**: The asymmetry transfer mechanism implicitly requires nonzero portal; this should be noted.

---

## 9. Confidence Assessment

**Overall Confidence: MEDIUM**

The W-sector field theory is a creative and largely self-consistent extension of the CG framework. The core ideas are sound:
- The fourth vertex naturally suggests a hidden sector
- Color singlet status is well-justified
- The Skyrme soliton construction is standard physics
- The ADM mechanism elegantly resolves the relic abundance tension

However, the critical Higgs constraint issue must be resolved before the model can be considered viable. The most likely resolution (increasing $\lambda_W$ or adopting a Skyrme Lagrangian description) is straightforward and does not require fundamental changes to the framework.

The electroweak singlet justification gap is conceptually important but may be resolvable within the existing framework structure (via Proposition 0.0.22).

---

## 10. Recommendations

1. **Immediate:** Address the Higgs exotic decay constraint. Either:
   - (a) Increase $\lambda_W$ to $\geq 0.130$ and recompute all downstream quantities
   - (b) Explicitly argue that the Skyrme Lagrangian for the W sector does not support a light scalar excitation below $m_h/2$, and explain why the simple scalar potential is not the correct description
   - (c) Include a computation of $\text{BR}(h \to h_W h_W)$ and demonstrate compatibility with LHC data

2. **Short-term:** Strengthen the SU(2)$_L$ singlet derivation by explicitly connecting Proposition 0.0.22 to the W field's representation.

3. **Short-term:** Replace the $\phi_W = \pi$ proof with the Z$_3$-invariance argument (only $\phi_W = 0$ and $\phi_W = \pi$ are invariant; $\phi_W = 0$ is excluded by symmetry).

4. ~~**Medium-term:** Derive $e_W = 4.5$ from first principles or widen the uncertainty to include $e_W = 4.84$ (visible-sector value) as a baseline.~~ → **✅ DONE** — [Proposition 4.3.5](../Phase4/Proposition-4.3.5-Skyrme-Parameter-First-Principles-Derivation.md) provides the first-principles derivation via pressure-curvature integral ($I_4 = 2.09$, $e_W = 4.5 \pm 0.3$).

5. ~~**Medium-term:** Add a prediction for gravitational wave signals from the W-sector phase transition at $T \sim v_W$.~~ → **✅ DONE** — [Prediction 8.2.4](../Phase8/Prediction-8.2.4-W-Sector-Gravitational-Waves.md) derives the full GW spectrum: $f_{peak} \sim 0.5$–$5$ mHz, $\Omega_{GW} h^2 \sim 10^{-13}$ to $10^{-11}$.

---

## References

**Experimental Data:**
- [LZ 2024 Results (arXiv:2410.17036)](https://arxiv.org/abs/2410.17036) — Dark Matter Search Results from 4.2 Tonne-Years
- [LZ 2025 Update](https://newscenter.lbl.gov/2025/12/08/lz-sets-a-worlds-best-in-the-hunt-for-galactic-dark-matter/) — Latest LZ results
- [ATLAS Higgs invisible search](https://atlas.cern/updates/briefing/invisible-Higgs-search) — BR(h->inv) < 15%
- [CMS Higgs invisible (CDS)](https://cds.cern.ch/record/2800581/files/CMS-HIG-20-003-arXiv.pdf) — BR(h->inv) < 10%

**Higgs Portal Dark Matter:**
- [Status of singlet scalar DM model (PMC)](https://pmc.ncbi.nlm.nih.gov/articles/PMC6959423/) — Global analysis
- [GAMBIT Higgs portal analysis (Springer)](https://link.springer.com/article/10.1140/epjc/s10052-018-6513-6) — Global fits

**Skyrme Model:**
- [Adkins, Nappi, Witten (1983)](https://www.sciencedirect.com/science/article/abs/pii/055032138390559X) — Static properties of nucleons in the Skyrme model
- Skyrme, T.H.R. (1962). Nucl. Phys. 31, 556-569.

**Higgs Portal References:**
- Patt, B. & Wilczek, F. (2006). [arXiv:hep-ph/0605188]
- Silveira, V. & Zee, A. (1985). Phys. Lett. B 161, 136-140.

---

*Verification Agent: Independent Adversarial Physics Review*
*Date: 2026-02-25*
*Confidence: MEDIUM*
*Status: PARTIAL — Critical issue requires resolution*
