# Proposition 7.8.4: V-Scheme BLM Scale-Setting for Glueball Mass Ratio

## Status: 🔶 NOVEL ✅ VERIFIED — V-SCHEME COUPLING IDENTIFICATION AND PRECISION GLUEBALL RATIO

**Role in Framework:** Identifies the Coulomb coupling in the Salpeter Hamiltonian as the V-scheme coupling $\alpha_V$ (not $\alpha_{\overline{\text{MS}}}$), exploits BLM/PMC scale-setting as a consistency check, and uses direct lattice $\alpha_V$ determinations (two quenched, one $N_f = 2+1$) to tighten the coupling uncertainty from $\pm 0.06$ (Prop 7.8.3) to $\pm 0.010$, reducing the Bethe-Salpeter glueball ratio uncertainty from 10.5% to 1.7%.

**Classification:** 🔶 NOVEL (V-scheme identification for Salpeter Hamiltonian, BLM scale relation at glueball momentum scale, lattice $\alpha_V$ compilation and weighted average) + ✅ ESTABLISHED (V-scheme definition [Peter 1997, Schroder 1999], BLM prescription [Brodsky, Lepage, Mackenzie 1983], PMC [Brodsky & Di Giustino 2012], lattice $\alpha_V$ measurements [Necco & Sommer 2002, Bali 2000, TUMQCD 2019])

**Key Result:**

$$\boxed{R_V = 3\sqrt{\frac{3(2 - 3\alpha_V)}{2}} = 3.45 \pm 0.06 \quad (1.7\%)} \tag{1.1}$$

with $\alpha_V = 0.373 \pm 0.010$ from three independent lattice determinations.

**Combined with Prop 7.8.2:**

$$\boxed{R_\text{combined} = 3.45 \pm 0.057 \quad (1.7\%)} \tag{1.2}$$

$$c_\text{FI}^{(\text{combined})} = 6.87 \pm 0.14 \quad (2.0\%) \tag{1.3}$$

**Dependencies:**
- ✅ Proposition 7.8.3 — Bethe-Salpeter formula $R_\text{BS} = 3\sqrt{3(2-3\alpha_s)/2}$ (provides the closed-form to be refined)
- ✅ Proposition 7.8.2 — Framework-Internal Glueball Mass Ratio ($R_\text{cont}^{\text{FI}} = 3.38 \pm 0.27$; to be combined)
- ✅ Proposition 0.0.38 — Exact FCC Partition Function (Casimir invariants)
- ✅ Theorem 7.5.2 — Perturbative Universality (one-loop beta function)
- ✅ Theorem 7.7.3 — Quantitative Mass Gap Lower Bound (to be upgraded with combined $c_\text{FI}$)
- ✅ External: Peter, NPB 501 (1997) 471 — NLO static potential and V-scheme definition [2]
- ✅ External: Schroder, PLB 447 (1999) 321 — Corrected NNLO coefficient [3]
- ✅ External: Necco & Sommer, NPB 622 (2002) 328 — Lattice $\alpha_V$ and scale ratio [4]
- ✅ External: Bali, PRD 62 (2000) 114503 — Lattice Casimir scaling and $\alpha_V$ [5]
- ✅ External: Bazavov et al. (TUMQCD), PRD 100 (2019) 114511 — Modern lattice $\alpha_V$ [6]
- ✅ External: Brodsky, Lepage, Mackenzie, PRD 28 (1983) 228 — BLM scale-setting [1]
- ✅ External: Athenodorou & Teper, JHEP 11 (2020) 172 — $R_\text{cont} = 3.405 \pm 0.021$ [8] (CHECK only)

**Enables:**
- Theorem 7.7.3 — Updated bound: $c_\text{FI} = 6.87 \pm 0.14$ (improved from $6.76 \pm 0.45$)
- Plan §12.2 Item F — Resolves aspiration target: 1.7% $\leq$ 2%

---

## File Structure

This proposition uses the **3-file academic structure**:

| File | Purpose | Sections | Verification Focus |
|------|---------|----------|-------------------|
| **Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio.md** (this file) | Statement & motivation | §0–4, References | Conceptual correctness |
| **[Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio-Derivation.md](./Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio-Derivation.md)** | Complete derivation | §5–10 | Mathematical rigor |
| **[Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio-Applications.md](./Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio-Applications.md)** | Impact & verification | §11–14 | Physical validity |

**Quick Links:**
- [→ See the complete derivation](./Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio-Derivation.md)
- [→ See applications and verification](./Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio-Applications.md)

---

## Verification Status

**Last Verified:** 2026-02-23
**Status:** 🔶 NOVEL ✅ VERIFIED (multi-agent adversarial review + Lean 4 formalization complete)

### Verification Checklist
- [x] All symbols defined in symbol table (§2)
- [x] Dimensional consistency verified (C-13)
- [x] Dependencies on prerequisite theorems valid
- [x] No circular references
- [x] V-scheme definition: $\tilde{V}(q) = -C_F \cdot 4\pi\alpha_V(q)/q^2$ — C-1
- [x] NLO coefficient $a_1 = 31$ for $N_f = 0$ SU(3) — C-2
- [x] BLM scale: $\mu_\text{BLM} = q \cdot \exp(-31/22)$ — C-3
- [x] Beta function: $\beta_0 = 11$, $\beta_1 = 102$ — C-4
- [x] Two-loop running formula verified — C-5
- [x] Scale ratio: $\Lambda_V/\Lambda_{\overline{\text{MS}}} = \exp(31/22) \approx 4.10$ — C-6
- [x] Lattice $\alpha_V(862\text{ MeV}) = 0.373 \pm 0.010$ — C-7
- [x] $R_V = 3\sqrt{3(2-3 \cdot 0.373)/2} = 3.45$ — C-8
- [x] $\delta R_V = 5.87 \times 0.010 = 0.059$ — C-9
- [x] V-scheme convergence (NLO correction absorbed) — C-10
- [x] Updated weighted average with Prop 7.8.2 — C-11
- [x] Updated $c_\text{FI} = 6.87 \pm 0.14$ — C-12
- [x] Dimensional consistency of all formulas — C-13
- [x] BLM-converted $\alpha_{\overline{\text{MS}}}(M_Z)$ consistent with lattice $\alpha_V$ — C-14
- [x] Tension with lattice $R_\text{cont}$: $0.70\sigma$ — C-15
- [x] Improvement factor: 6.3% → 1.7% — C-16

### Verification Reports
- [`Proposition-7.8.4-Multi-Agent-Verification-2026-02-23.md`](../verification-records/Proposition-7.8.4-Multi-Agent-Verification-2026-02-23.md) — Multi-agent adversarial review (3 agents: Literature, Mathematics, Physics). **Overall: PARTIAL — correctable issues found, no fatal errors.** Core result confirmed correct. All issues addressed in post-review corrections (2026-02-23).

### Verification Scripts
- `verification/Phase7/prop_7_8_4_v_scheme_blm_glueball_ratio.py` — Standard + adversarial verification (C-1 through C-16, ADV-1 through ADV-8): **24/24 PASS**
- [`verification/Phase7/prop_7_8_4_adversarial_verification.py`](../../../verification/Phase7/prop_7_8_4_adversarial_verification.py) — Multi-agent follow-up adversarial verification (MAV-1 through MAV-10): **10/10 PASS**

### Lean 4 Formalization
- [`Phase7/Proposition_7_8_4.lean`](../../../lean/ChiralGeometrogenesis/Phase7/Proposition_7_8_4.lean) — Machine-verified formalization (96 definitions/theorems, **0 sorry, 0 axioms** at this level)
  - **Parts (a)–(d):** V-scheme identification, BLM scale relation, lattice $\alpha_V$, final $R_V$
  - **Parts (e)–(f):** Combined analysis with Prop 7.8.2, mass gap bound update
  - **Consistency checks:** C-1 through C-16 all formalized
  - **Lattice weighted average:** Three individual measurements defined; inverse-variance weighted average proven to yield $\alpha_V = 0.373 \pm 0.010$; $\chi^2 < 1$ for 2 dof (internal consistency)
  - **Tension checks:** Both simple ($|R_V - R_\text{lat}|/\delta R_V < 1$) and proper quadrature ($t^2 = \Delta R^2/(\delta R_V^2 + \delta R_\text{lat}^2) < 1$) formalized
  - **Transitive axiom dependency:** `Proposition_7_8_3.exponential_wavefunction_matrix_elements` (✅ ESTABLISHED — standard QM integrals)

### Verification Plots
- `verification/plots/prop_7_8_4_v_scheme_blm_summary.png` — 4-panel summary ($\alpha_V$ compilation, method comparison, uncertainty improvement, BLM consistency)
- [`verification/plots/prop_7_8_4_v_scheme_adversarial.png`](../../../verification/plots/prop_7_8_4_v_scheme_adversarial.png) — 4-panel adversarial summary (lattice compilation, coupling sensitivity, method comparison, MC bootstrap)

---

## §0. Context and Motivation

### §0.1 The Coupling Precision Bottleneck

Proposition 7.8.3 derives a closed-form glueball mass ratio $R_\text{BS} = 3\sqrt{3(2-3\alpha_s)/2}$ via the spinless Salpeter equation with Cornell potential. The dominant uncertainty is the strong coupling $\alpha_s = 0.38 \pm 0.06$, which contributes 10.5% relative uncertainty through the steep derivative $|dR/d\alpha_s| \approx 5.87$. Combined with Prop 7.8.2, the overall precision reaches 6.3% — but the aspiration target (Plan §12.2.F) is $\leq 2\%$.

To reach 2%, we need $\delta\alpha_s \leq 0.012$. The current $\delta\alpha_s = 0.06$ spans the range between one-loop and two-loop $\overline{\text{MS}}$ evaluations at the glueball scale, reflecting a genuine **scheme and scale ambiguity**.

### §0.2 The V-Scheme Insight

The key observation (already noted in Prop 7.8.3 §9.6 but not exploited) is that the Coulomb term $-3\alpha_s/r$ in the Salpeter Hamiltonian IS the static potential by definition. The coupling appearing in this term is therefore the V-scheme coupling $\alpha_V$, defined directly from the static quark-antiquark potential:

$$\tilde{V}(q) = -C_F \cdot \frac{4\pi\alpha_V(q)}{q^2} \tag{0.1}$$

This identification has three consequences:

1. **No scheme conversion needed:** The Salpeter formula already uses $\alpha_V$, not $\alpha_{\overline{\text{MS}}}$. The large scheme conversion uncertainty that inflated $\delta\alpha_s$ to 0.06 is eliminated.

2. **Direct lattice access:** $\alpha_V$ is a physical (gauge-invariant) observable, directly measurable from the lattice static force $F(r) = dV/dr$ without perturbative matching.

3. **BLM/PMC consistency:** The BLM prescription provides the relationship $\alpha_V(q) \leftrightarrow \alpha_{\overline{\text{MS}}}(\mu_\text{BLM})$, which serves as a cross-check (but is not needed as the primary input).

### §0.3 Strategy

1. **Part (a):** Rigorously identify the coupling in the Salpeter Hamiltonian as $\alpha_V$ (§5)
2. **Part (b):** Derive the BLM scale relation $\mu_\text{BLM} = q \cdot e^{-a_1/(2\beta_0)}$ as a consistency check (§6)
3. **Part (c):** Compile lattice $\alpha_V$ determinations at the glueball scale and form weighted average (§7–8)
4. **Part (d):** Compute $R_V = 3.45 \pm 0.06$ (1.7%) and combine with Prop 7.8.2 (§9)

### §0.4 Prerequisites

| Result | Source | What It Provides |
|--------|--------|-----------------|
| Bethe-Salpeter formula | Prop 7.8.3 | $R_\text{BS} = 3\sqrt{3(2-3\alpha_s)/2}$ (same formula, tighter coupling) |
| V-scheme definition | Peter (1997) [2] | Static potential $\to$ $\alpha_V(q)$ |
| BLM prescription | Brodsky et al. (1983) [1] | Scale-setting: $\mu_\text{BLM} = q \cdot e^{-a_1/(2\beta_0)}$ |
| NLO static potential | Peter (1997) [2], Schroder (1999) [3] | $a_1 = 31/3 \cdot C_A = 31$ for $N_f = 0$ |
| Lattice $\alpha_V$ | Necco & Sommer [4], Bali [5], TUMQCD [6] | $\alpha_V(862\text{ MeV}) = 0.373 \pm 0.010$ |
| Prop 7.8.2 result | Prop 7.8.2 | $R_\text{cont}^{\text{FI}} = 3.38 \pm 0.27$ (for combination) |

---

## §1. Formal Statement

**Proposition 7.8.4** (V-Scheme BLM Scale-Setting for Glueball Mass Ratio)

*The Coulomb coupling in the Salpeter Hamiltonian for the $0^{++}$ glueball (Prop 7.8.3) is the V-scheme coupling $\alpha_V$ by definition. Using the BLM/PMC scale relation as a consistency check and three independent lattice determinations of $\alpha_V$ at the glueball momentum scale, we establish:*

**Part (a)** — V-Scheme Identification:

*The Salpeter Hamiltonian*

$$H = 2|p| + \frac{9}{4}\sigma_3 r - 3\alpha_V(q^*) \cdot \frac{1}{r} \tag{1.4}$$

*uses the V-scheme coupling $\alpha_V(q^*)$ at the characteristic glueball momentum scale $q^* = \beta^* \sqrt{\sigma} \approx 862$ MeV, where $\beta^* = \sqrt{27/(8(2-3\alpha_V))} \approx 1.96$ is the optimized variational parameter.*

**Part (b)** — BLM Scale Relation:

*The BLM/PMC prescription relates $\alpha_V$ and $\alpha_{\overline{\text{MS}}}$ via:*

$$\alpha_V(q) = \alpha_{\overline{\text{MS}}}(\mu) \left[1 + \frac{\alpha_{\overline{\text{MS}}}}{4\pi}(a_1 + \beta_0 \ln(\mu^2/q^2)) + \cdots\right] \tag{1.5}$$

*Setting the NLO correction to zero determines $\mu_\text{BLM} = q \cdot e^{-a_1/(2\beta_0)}$. For $N_f = 0$ SU(3): $a_1 = 31$, $\beta_0 = 11$, giving $\mu_\text{BLM} = 0.244 \, q$.*

**Part (c)** — Precision $\alpha_V$ from Lattice:

*Three independent lattice determinations (two quenched, one $N_f = 2+1$; see §7 of the [Derivation](./Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio-Derivation.md)) at $q \sim 862$ MeV yield a weighted average:*

$$\boxed{\alpha_V(862 \text{ MeV}) = 0.373 \pm 0.010} \tag{1.6}$$

**Part (d)** — Final Result:

*Using $\alpha_V = 0.373 \pm 0.010$ in the Prop 7.8.3 closed-form formula:*

$$R_V = 3\sqrt{\frac{3(2 - 3 \times 0.373)}{2}} = 3\sqrt{\frac{3 \times 0.881}{2}} = 3\sqrt{1.3215} = 3.45 \tag{1.7}$$

$$\delta R_V = |dR/d\alpha_V| \times \delta\alpha_V = 5.87 \times 0.010 = 0.059 \tag{1.8}$$

$$\boxed{R_V = 3.45 \pm 0.06 \quad (1.7\%)} \tag{1.1}$$

*Consistency check against lattice Monte Carlo:*

$$\frac{|R_V - R_\text{cont}^{\text{lat}}|}{\sqrt{\delta R_V^2 + \delta R_\text{lat}^2}} = \frac{|3.45 - 3.405|}{\sqrt{0.059^2 + 0.021^2}} = \frac{0.045}{0.063} = 0.70\sigma \tag{1.9}$$

*Prop 7.8.4 supersedes Prop 7.8.3 for the Salpeter-based estimate. Two-way combination with Prop 7.8.2:*

$$\boxed{R_\text{combined} = 3.45 \pm 0.057 \quad (1.7\%)} \tag{1.2}$$

$$c_\text{FI}^{(\text{combined})} = R_\text{combined} \times \frac{\sqrt{\sigma}}{\Lambda_{\overline{\text{MS}}}} = 3.45 \times 1.994 = 6.87 \pm 0.14 \tag{1.3}$$

---

## §2. Symbol and Dimension Table

| Symbol | Meaning | Dimension | Value / Source |
|--------|---------|-----------|---------------|
| $\alpha_V(q)$ | V-scheme coupling at scale $q$ | Dimensionless | $0.373 \pm 0.010$ at $q \approx 862$ MeV (§8) |
| $\alpha_{\overline{\text{MS}}}(\mu)$ | $\overline{\text{MS}}$ coupling at scale $\mu$ | Dimensionless | $0.1180 \pm 0.0009$ at $M_Z$ (PDG 2024) |
| $a_1$ | NLO coefficient in $\alpha_V / \alpha_{\overline{\text{MS}}}$ | Dimensionless | $31$ for $N_f = 0$ SU(3) [2, 3] |
| $\beta_0$ | One-loop beta function coefficient | Dimensionless | $11$ for $N_f = 0$ SU(3) |
| $\beta_1$ | Two-loop beta function coefficient | Dimensionless | $102$ for $N_f = 0$ SU(3) |
| $\mu_\text{BLM}$ | BLM optimal scale | $[\text{mass}]$ | $0.244 \, q$ |
| $q^*$ | Characteristic glueball momentum | $[\text{mass}]$ | $\beta^* \sqrt{\sigma} \approx 862$ MeV |
| $\beta^*$ | Optimized variational parameter (dimensionless) | Dimensionless | $\sqrt{27/(8(2-3\alpha_V))} \approx 1.96$ |
| $\Lambda_V$ | V-scheme Lambda parameter | $[\text{mass}]$ | $\Lambda_{\overline{\text{MS}}} \cdot e^{a_1/(2\beta_0)}$ |
| $\Lambda_{\overline{\text{MS}}}$ | $\overline{\text{MS}}$ Lambda parameter ($N_f = 0$) | $[\text{mass}]$ | $\approx 220$ MeV [4] |
| $R_V$ | V-scheme Salpeter glueball ratio | Dimensionless | $3.45 \pm 0.06$ |
| $R_\text{cont}^{\text{FI}}$ | Prop 7.8.2 framework-internal ratio | Dimensionless | $3.38 \pm 0.27$ |
| $R_\text{combined}$ | Weighted average | Dimensionless | $3.45 \pm 0.057$ |
| $R_\text{cont}^{\text{lat}}$ | Lattice MC glueball ratio | Dimensionless | $3.405 \pm 0.021$ [8] |
| $c_\text{FI}$ | Combined mass gap coefficient | Dimensionless | $6.87 \pm 0.14$ |
| $\sigma_3$ | Fundamental string tension | $[\text{mass}^2]$ | Input parameter |
| $C_F$ | Fundamental Casimir | Dimensionless | $4/3$ |
| $C_A$ | Adjoint Casimir | Dimensionless | $3$ |
| $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}}$ | Scale ratio | Dimensionless | $1.994 \pm 0.021$ [4] |

---

## §3. Physical Interpretation

### §3.1 Why V-Scheme Is Natural for Bound States

The V-scheme coupling $\alpha_V$ is defined to absorb all radiative corrections to the static potential into the coupling. This means:

1. **The Coulomb term in the Cornell potential IS $\alpha_V$ by definition** — no perturbative matching is needed
2. **$\alpha_V$ is a physical observable** — it can be extracted directly from lattice simulations of the static force $F(r) = dV/dr$, without perturbative conversion
3. **Better perturbative convergence** — the NLO correction, which is $\sim 33\%$ in $\overline{\text{MS}}$ at the glueball scale, is absorbed by definition in V-scheme

### §3.2 The BLM Connection

The BLM/PMC prescription [1, 7] determines the optimal $\overline{\text{MS}}$ scale for each physical process by absorbing the $n_f$-dependent part of the NLO correction into the running coupling. For the static potential, this gives $\mu_\text{BLM} = q \cdot e^{-a_1/(2\beta_0)}$. At the glueball scale $q^* \approx 862$ MeV, this yields $\mu_\text{BLM} \approx 210$ MeV — uncomfortably close to $\Lambda_{\overline{\text{MS}}} \approx 220$ MeV. This reflects the well-known fact that $\overline{\text{MS}}$ perturbation theory is problematic at low scales, and motivates using $\alpha_V$ directly from lattice data rather than converting from $\alpha_{\overline{\text{MS}}}(M_Z)$.

### §3.3 Supersession of Prop 7.8.3

Prop 7.8.4 uses the **same formula** as Prop 7.8.3 ($R = 3\sqrt{3(2-3\alpha)/2}$) but with a **tighter coupling determination**. The improvement comes entirely from recognizing that:
- The coupling is $\alpha_V$ (not $\alpha_{\overline{\text{MS}}}$)
- $\alpha_V$ is directly measurable from lattice data with $\pm 0.010$ precision
- No scheme conversion is needed, eliminating the dominant source of uncertainty in Prop 7.8.3

---

## §4. Derivation Structure

The complete derivation is in the [Derivation file](./Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio-Derivation.md):

- **§5:** V-scheme coupling definition and properties — momentum-space static potential, gauge invariance, scheme independence
- **§6:** BLM/PMC scale-setting for the static potential — NLO relation, BLM scale, consistency check
- **§7:** Lattice $\alpha_V$ determinations — compilation of three independent measurements
- **§8:** Weighted average $\alpha_V = 0.373 \pm 0.010$ with uncertainty budget
- **§9:** $R_V$ computation and comparison with lattice $R_\text{cont}$
- **§10:** Uncertainty budget — $\alpha_V$ dominant, AFM subdominant, Casimir scaling negligible

---

## References

[1] Brodsky, S.J., Lepage, G.P. & Mackenzie, P.B. "On the elimination of scale ambiguities in perturbative quantum chromodynamics." PRD 28 (1983) 228.

[2] Peter, M. "The static potential in QCD — a full two-loop calculation." NPB 501 (1997) 471. [arXiv:hep-ph/9702245]

[3] Schroder, Y. "The static potential in QCD to two loops." PLB 447 (1999) 321. [arXiv:hep-ph/9812205]

[4] Necco, S. & Sommer, R. "The N_f = 0 heavy quark potential from short to intermediate distances." Nucl. Phys. B 622 (2002) 328. [arXiv:hep-lat/0108008]

[5] Bali, G.S. "Casimir scaling of SU(3) static potentials." PRD 62 (2000) 114503. [arXiv:hep-lat/0006022]

[6] Bazavov, A. et al. (TUMQCD Collaboration). "Determination of $\alpha_s$ from the static energy." PRD 100 (2019) 114511. [arXiv:1907.11747]

[7] Brodsky, S.J. & Di Giustino, L. "Setting the renormalization scale in QCD: The principle of maximum conformality." PRD 86 (2012) 085026. [arXiv:1107.0338]

[8] Athenodorou, A. & Teper, M. "The glueball spectrum of SU(3) gauge theory in 3+1 dimensions." JHEP 11 (2020) 172. [arXiv:2007.06422]

[9] PDG 2024: $\alpha_s(M_Z) = 0.1180 \pm 0.0009$.
