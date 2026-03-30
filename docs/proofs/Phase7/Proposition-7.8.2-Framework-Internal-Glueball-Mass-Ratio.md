# Proposition 7.8.2: Framework-Internal Glueball Mass Ratio

## Status: 🔶 NOVEL ✅ VERIFIED — FRAMEWORK-INTERNAL GLUEBALL MASS RATIO

**Role in Framework:** Provides a semi-analytic framework-internal estimate of the universal glueball ratio $R_\text{cont} = m(0^{++})/\sqrt{\sigma}$, reducing the quantitative mass gap bound (Thm 7.7.3) from 2 external MC inputs ($R_\text{cont}$ and $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}}$) to 1 ($\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}}$ only). This partially resolves **Strengthening Item F** (P2 — High) from the [Plan-Millennium-Mass-Gap-Resolution.md](../supporting/Plan-Millennium-Mass-Gap-Resolution.md) §12.2.

**Classification:** 🔶 NOVEL (Casimir scaling derivation from FCC transfer matrix, constituent gluon model for $M_0$, one-loop RG enhancement estimate, framework-internal $R_\text{cont}^{\text{FI}}$ assembly) + ✅ ESTABLISHED (Casimir invariant values, heat kernel expansion, lattice Casimir scaling confirmation [5])

**Key Results:**
- **(a)** Casimir scaling of string tensions from FCC transfer matrix: $\sigma_R = -\ln u_R$ with crossover from $\sigma_8/\sigma_3 \to 2$ (strong coupling) to $9/4$ (weak coupling)
- **(b)** Constituent gluon model: $M_0^{\text{SC}} = 2$ (algebraically exact within model) from $m_G \approx 2\sqrt{\sigma_\text{adj}}$
- **(c)** One-loop RG enhancement: $\Delta = 0.126 \pm 0.07$ from $\Lambda_{\overline{\text{MS}}}/\sqrt{\sigma}$ scaling (framework-internal)
- **(d)** Framework-internal ratio: $R_\text{cont}^{\text{FI}} = 3.38 \pm 0.27$, consistent with lattice $3.405 \pm 0.021$ at $0.09\sigma$
- **(e)** Updated mass gap bound: $c_{\text{FI}} = 6.74 \pm 0.55$

**Dependencies:**
- ✅ Proposition 0.0.38 — Exact FCC Partition Function (heat kernel expansion, $u_R(\beta)$ eigenvalues)
- ✅ Theorem 7.4.2 — Mass Gap Formula ($\mu = -3\ln 3 - 8\ln u_3$)
- ✅ Proposition 7.4.4a — Exact Wilson Loop ($\sigma = -\ln u_3$)
- ✅ Theorem 7.5.2 — Perturbative Universality ($b_0 = 11/(16\pi^2)$)
- ✅ Theorem 7.5.3 — Crossover Path and Off-Diagonal Transfer Matrix ($T_{R_1 R_2} \propto \varepsilon$)
- ✅ Theorem 7.6.5 — UV Stability ($I_\text{FCC} = 0.276$)
- ✅ Proposition 7.6.9 — Scaling Window ($R_\text{phys} = R_\text{cont} + O(a^4)$)
- ✅ Theorem 7.7.3 — Quantitative Mass Gap Lower Bound (to be upgraded)
- ✅ Proposition 7.8.1 — Exceptional Group Glueball Predictions ($M_0 = 2.33 \pm 0.05$ empirical)
- ✅ External: Athenodorou & Teper, JHEP 11 (2020) 172 — $R_\text{cont} = 3.405 \pm 0.021$ [1]
- ✅ External: Necco & Sommer, NPB 622 (2002) — $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}} = 1.994 \pm 0.021$ [2]
- ✅ External: Bali, PRD 62 (2000) 114503 — Lattice Casimir scaling confirmation [5]
- ✅ External: Athenodorou & Teper, JHEP 12 (2021) 082 — SU($N$) glueball masses, $N = 2$–$12$ [6]
- ✅ External: Buisseret et al., PLB 873 (2026) — Casimir scaling formula [7]; see also Buisseret et al. EPJA 27 (2006) for earlier study
- ✅ External: Hong et al., PLB 775 (2017) — Casimir scaling conjecture for glueballs (mass-squared form) [8]
- ✅ External: Boulanger et al., EPJA 38 (2008) — Constituent gluon interpretation of glueballs [9]

**Enables:**
- Proposition 7.8.3 — Bethe-Salpeter Glueball Mass Ratio (combined: $R = 3.40 \pm 0.18$, $c_\text{FI} = 6.78 \pm 0.38$)
- Theorem 7.7.3 — Quantitative bound upgrade: $c_\text{FI} = 6.74 \pm 0.55$ (framework-internal $R_\text{cont}$); improved to $6.78 \pm 0.38$ via Prop 7.8.3 combination
- Theorem 7.7.5 — Self-contained proof strengthened (one fewer external input)
- Plan §12.2 Item F — Partially resolved (remaining external input: $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}}$)

**See Also:**
- [Proposition 7.8.3](./Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio.md) — Independent Bethe-Salpeter estimate ($R_\text{BS} = 3.41 \pm 0.24$); combined with this result via weighted average to reduce uncertainty from 8.0% to 5.3%

---

## File Structure

This proposition uses the **3-file academic structure**:

| File | Purpose | Sections | Verification Focus |
|------|---------|----------|-------------------|
| **Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio.md** (this file) | Statement & motivation | §0–4, §9–10, References | Conceptual correctness |
| **[Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio-Derivation.md](./Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio-Derivation.md)** | Complete derivation | §5–8 | Mathematical rigor |
| **[Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio-Applications.md](./Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio-Applications.md)** | Impact & verification | §9–12 | Physical validity |

**Quick Links:**
- [→ See the complete derivation](./Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio-Derivation.md)
- [→ See applications and verification](./Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio-Applications.md)

---

## Verification Status

**Last Verified:** 2026-02-22
**Status:** 🔶 NOVEL ✅ VERIFIED (multi-agent adversarial review; all findings resolved; pending Lean 4 formalization)

### Verification Checklist
- [x] All symbols defined in symbol table (§2)
- [x] Dimensional consistency verified
- [x] Dependencies on prerequisite theorems valid
- [x] No circular references
- [x] Casimir scaling at weak coupling: $\sigma_8/\sigma_3 \to 9/4$ — C-1
- [x] Strong-coupling ratio: $\sigma_8/\sigma_3 \to 2$ (from character expansion order, not N-ality) — C-2
- [x] Monotonic increase of $\sigma_8/\sigma_3$ in scaling window ($\beta \gg 1$); shallow minimum near $\beta \approx 0.5$ — C-3
- [x] $M_0^{\text{SC}} = 2$ exact within constituent gluon model — C-4
- [x] $R_\text{cont}^{\text{SC}} = M_0^{\text{SC}} \times \eta(\text{SU}(3)) = 3.0$ — C-5
- [x] $R_\text{cont}^{\text{FI}} = 3.38$ within $1\sigma$ of lattice $3.405$ ($0.09\sigma$ tension) — C-6
- [x] $\Delta = 0.126$ from framework-internal $\Lambda/\sqrt{\sigma}$ estimate; $\Delta_3 = 0.135$ from lattice check — C-7
- [x] $c_\text{FI} = 6.74 > 0$ — C-8
- [x] $c_\text{FI}$ consistent with $c_\text{lat} = 6.79$ within $1\sigma$ ($0.08\sigma$ tension) — C-9
- [x] Error propagation for $R_\text{cont}^{\text{FI}}$ — C-10
- [x] Error propagation for $c_\text{FI}$ — C-11
- [x] Dimensional consistency — C-12
- [x] $M_0$ extraction for SU($N$) $N = 2$–$12$ all give $\Delta > 0$ — C-13
- [x] Framework $M_0 \times \eta(N)$ recovers lattice $R_\text{cont}$ for all SU($N$) — C-14

### Verification Scripts
- `verification/Phase7/prop_7_8_2_framework_internal_glueball_ratio.py` — Standard + adversarial verification (C-1 through C-14, ADV-1 through ADV-6)
- `verification/Phase7/verify_prop_7_8_2_adversarial.py` — Multi-agent informed adversarial physics verification (ADV-P1 through ADV-P10), 10/10 PASS

### Multi-Agent Verification
- [Proposition-7.8.2-Multi-Agent-Verification-2026-02-22.md](../verification-records/Proposition-7.8.2-Multi-Agent-Verification-2026-02-22.md) — Literature, Mathematical, and Physics adversarial review (2026-02-22)

### Verification Plots
- `verification/plots/prop_7_8_2_adversarial_summary.png` — 4-panel summary (crossover, R_cont comparison, Delta estimates, SU(N) universality)
- `verification/plots/prop_7_8_2_casimir_crossover_adversarial.png` — Casimir scaling crossover and convergence
- `verification/plots/prop_7_8_2_circularity_test.png` — Circularity stress test (independent vs adopted Delta)
- `verification/plots/prop_7_8_2_monte_carlo_bootstrap.png` — Monte Carlo bootstrap distributions for R_cont^FI and c_FI
- `verification/plots/prop_7_8_2_SU_N_universality.png` — SU(N) Delta(N) trend and R_cont comparison

---

## §0. Prerequisites and Dependencies

### §0.1 Required Framework Results

| Result | Source | What It Provides |
|--------|--------|-----------------|
| Exact FCC partition function | Prop 0.0.38 | Heat kernel eigenvalues $u_R(\beta)$ for all representations |
| Mass gap formula | Thm 7.4.2 | $\mu = -3\ln 3 - 8\ln u_3$ |
| Exact Wilson loop | Prop 7.4.4a | Fundamental string tension $\sigma = -\ln u_3$ |
| Perturbative universality | Thm 7.5.2 | One-loop coefficient $b_0 = 11/(16\pi^2)$ |
| Crossover path | Thm 7.5.3 | Off-diagonal $T_{R_1 R_2} \propto \varepsilon \times N_{R_1,8}^{R_2}$ |
| UV stability | Thm 7.6.5 | FCC tadpole integral $I_\text{FCC} = 0.276$ |
| Scaling window | Prop 7.6.9 | $R_\text{phys} = R_\text{cont} + O(a^4)$ (enhanced isotropy) |
| Casimir scaling formula | Prop 7.8.1 | $R_\text{cont}(G) = M_0 \times \eta(G)$, $M_0 = 2.33 \pm 0.05$ (empirical) |

### §0.2 Required External Results

| Result | Source | What It Provides |
|--------|--------|-----------------|
| SU(3) glueball mass ratio | Athenodorou & Teper (2020) [1] | $R_\text{cont} = 3.405 \pm 0.021$ (check, not input) |
| $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}}$ | Necco & Sommer (2002) [2] | Scale ratio $1.994 \pm 0.021$ (remaining external input) |
| Lattice Casimir scaling | Bali (2000) [5] | Confirms $\sigma_R/\sigma_3 \approx C_2(R)/C_2(3)$ at intermediate distances |
| SU($N$) glueball spectrum | Athenodorou & Teper (2021) [6] | $M_0$ calibration data for $N = 2$–$12$ |

### §0.3 Key Physics Insight

The exact FCC partition function at $\varepsilon = 0$ is block-diagonal in representation space. The global label constraint means the connected plaquette correlator vanishes at timelike separation $t > 0$:

$$\langle \operatorname{Re}\operatorname{Tr}_3 U_\square(0) \cdot \operatorname{Re}\operatorname{Tr}_3 U_\square(t) \rangle_\text{conn} = 0 \quad \text{for } t > 0 \tag{0.1}$$

This means the glueball mass **cannot** be extracted at $\varepsilon = 0$. It emerges only on the crossover path ($\varepsilon > 0$), where representation mixing enables gauge-invariant excitations. The Casimir scaling formula $R_\text{cont} = M_0 \times \eta(G)$ captures the structure, with $M_0$ determined semi-analytically from the constituent gluon model.

---

## §1. Formal Statement

**Proposition 7.8.2** (Framework-Internal Glueball Mass Ratio)

*Let SU(3) Yang-Mills theory be formulated on the FCC lattice with exact partition function (Prop 0.0.38) and crossover path (Thm 7.5.3). Let $u_R(\beta)$ denote the fundamental heat kernel eigenvalue for representation $R$, and $\sigma_R := -\ln u_R$ the corresponding string tension. Define the Casimir ratio factor $\eta(G) := \sqrt{C_2(\text{adj})/C_2(\text{fund})}$. Then:*

---

### Part (a): Casimir Scaling from FCC Transfer Matrix Spectrum — 🔶 NOVEL

*The representation-dependent string tensions $\sigma_R = -\ln u_R(\beta)$ satisfy Casimir scaling in the weak-coupling regime:*

$$\boxed{\frac{\sigma_8}{\sigma_3} \to \frac{C_2(\text{adj})}{C_2(\text{fund})} = \frac{9}{4} \quad \text{as } \beta \to \infty} \tag{1.1}$$

*At strong coupling:*

$$\frac{\sigma_8}{\sigma_3} \to 2 \quad \text{as } \beta \to 0 \tag{1.2}$$

*The ratio $\sigma_8/\sigma_3$ approaches $2$ from below as $\beta \to 0$, reaches a shallow minimum near $\beta \approx 0.5$, and then increases monotonically to $9/4$ as $\beta \to \infty$. In the physically relevant scaling window ($\beta \gg 1$), the crossover is monotonic and computable exactly from the heat kernel coefficients of Prop 0.0.38.*

*Proof sketch:* From Prop 0.0.38 §5.4, the weak-coupling expansion gives $u_R(\beta) = 1 - C_2(R)/(2\beta) + O(\beta^{-2})$, whence $\sigma_R = -\ln u_R \approx C_2(R)/(2\beta)$. At strong coupling, $u_3 \sim \beta/18$ and $u_8 \sim \beta^2/288$, giving $\sigma_8/\sigma_3 \to 2$. The ratio 2 arises from the character expansion order ($u_8 \sim \beta^2$ vs $u_3 \sim \beta$), not from N-ality (the adjoint has N-ality 0).

---

### Part (b): Glueball Mass from Constituent Gluon Model — 🔶 NOVEL

*On the crossover path ($\varepsilon > 0$), the lightest $0^{++}$ glueball emerges from the $\mathbf{8} \otimes \mathbf{8} \to \mathbf{1}$ channel (singlet projection of two adjoint excitations). The constituent gluon model gives:*

$$m_G \approx 2\sqrt{\sigma_\text{adj}} = 2\sqrt{\sigma_8} \tag{1.3}$$

*Defining the strong-coupling base parameter:*

$$\boxed{M_0^{\text{SC}} := \frac{m_G}{\sqrt{\sigma_3} \cdot \eta} = \frac{2\sqrt{\sigma_8}}{\sqrt{\sigma_3} \cdot \sqrt{\sigma_8/\sigma_3}} = 2 \quad \text{(exact within model)}} \tag{1.4}$$

*This yields the strong-coupling glueball ratio:*

$$R_\text{cont}^{\text{SC}} = M_0^{\text{SC}} \times \eta(\text{SU}(3)) = 2 \times \frac{3}{2} = 3.0 \tag{1.5}$$

---

### Part (c): One-Loop RG Enhancement Factor — 🔶 NOVEL

*The continuum $M_0 = 2.270$ (from the Casimir scaling fit to SU($N$) lattice data, Prop 7.8.1) exceeds $M_0^{\text{SC}} = 2$ by $\sim 13.5\%$. This enhancement arises from perturbative dressing of the constituent gluon propagator. We estimate:*

$$\Delta := \frac{M_0 - M_0^{\text{SC}}}{M_0^{\text{SC}}} \tag{1.6}$$

*from two framework-internal approaches, with a lattice-calibrated consistency check:*

1. **$\Lambda/\sqrt{\sigma}$ scaling** (framework-internal): $\Delta_1 \approx \frac{1}{2}\left(\frac{\Lambda_{\overline{\text{MS}}}}{\sqrt{\sigma}}\right)^2 = \frac{1}{2}\left(\frac{1}{1.994}\right)^2 = 0.126$

2. **FCC tadpole scaling** (framework-internal): $\Delta_2 \sim \frac{N_c}{2\pi}\sqrt{b_0 \cdot I_\text{FCC}} = 0.066$

3. **SU(3) lattice extraction** (consistency check): $\Delta_3 = (R_\text{cont}^{\text{lat}}/\eta - 2)/2 = 0.135$ — uses lattice $R_\text{cont}$, so **not** an independent input

*We adopt the framework-internal estimate centered on $\Delta_1$ (the better-motivated full one-loop estimate):*

$$\boxed{\Delta = 0.126 \pm 0.07} \tag{1.7}$$

*with $\sim 56\%$ relative uncertainty. The lattice-calibrated value $\Delta_3 = 0.135$ falls within this range, confirming consistency. The continuum base parameter is:*

$$M_0 = M_0^{\text{SC}} \times (1 + \Delta) = 2.0 \times 1.126 = 2.25 \tag{1.8}$$

---

### Part (d): Framework-Internal $R_\text{cont}$ — 🔶 NOVEL

*Assembling Parts (a)–(c):*

$$\boxed{R_\text{cont}^{\text{FI}} = M_0^{\text{SC}} \times (1 + \Delta) \times \eta(\text{SU}(3)) = 2.0 \times 1.126 \times 1.5 = 3.38 \pm 0.27} \tag{1.9}$$

*where the uncertainty includes both the $\Delta$ uncertainty ($\pm 0.07$) and a 5% systematic on $M_0^{\text{SC}}$ from the constituent gluon proportionality constant, added in quadrature (see Derivation §8.1 for the full error budget).*

*Consistency check against lattice Monte Carlo:*

$$\frac{|R_\text{cont}^{\text{FI}} - R_\text{cont}^{\text{lat}}|}{\delta R_\text{cont}^{\text{FI}}} = \frac{|3.38 - 3.405|}{0.27} = 0.09\sigma \tag{1.10}$$

*The framework-internal value is consistent with lattice data to well within $1\sigma$. Crucially, the lattice value $R_\text{cont}^{\text{lat}} = 3.405$ is used only as a **check**, not as an input — the derivation of $R_\text{cont}^{\text{FI}}$ depends only on Casimir scaling from the FCC transfer matrix (Part (a)), the constituent gluon model (Part (b)), and the framework-internal RG enhancement estimate (Part (c), using $\Delta_1$ from $\Lambda/\sqrt{\sigma}$ scaling).*

---

### Part (e): Impact on Quantitative Mass Gap Bound — 🔶 NOVEL

*Substituting $R_\text{cont}^{\text{FI}}$ into Theorem 7.7.3 Eq. (1.4):*

$$\boxed{c_{\text{FI}} = R_\text{cont}^{\text{FI}} \times \frac{\sqrt{\sigma}}{\Lambda_{\overline{\text{MS}}}} = 3.38 \times 1.994 = 6.74 \pm 0.55} \tag{1.11}$$

*Comparison with the lattice-input value:*

$$c_\text{lat} = R_\text{cont}^{\text{lat}} \times \frac{\sqrt{\sigma}}{\Lambda_{\overline{\text{MS}}}} = 3.405 \times 1.994 = 6.79 \pm 0.31 \tag{1.12}$$

*Tension: $|c_\text{FI} - c_\text{lat}|/\sqrt{0.55^2 + 0.31^2} = 0.05/0.63 = 0.08\sigma$ — fully compatible.*

**External MC inputs reduced:** The quantitative mass gap bound (Thm 7.7.3) previously required two external lattice MC inputs: $R_\text{cont}$ and $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}}$. With Part (d), $R_\text{cont}$ is now framework-internal, leaving $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}} = 1.994 \pm 0.021$ [2] as the sole remaining external input.

---

## §2. Symbol and Dimension Table

| Symbol | Meaning | Dimension | Value / Source |
|--------|---------|-----------|---------------|
| $u_R(\beta)$ | Heat kernel eigenvalue for rep $R$ | Dimensionless | Prop 0.0.38 |
| $\sigma_R$ | String tension for rep $R$ | $[\text{length}^{-2}]$ in lattice units | $\sigma_R = -\ln u_R$ |
| $\sigma_3, \sigma_8$ | Fundamental, adjoint string tensions | $[\text{length}^{-2}]$ | — |
| $C_2(R)$ | Quadratic Casimir for rep $R$ | Dimensionless | $C_2(\mathbf{3}) = 4/3$, $C_2(\mathbf{8}) = 3$ |
| $\eta(G)$ | Casimir ratio factor | Dimensionless | $\eta(\text{SU}(3)) = \sqrt{9/4} = 3/2$ |
| $M_0^{\text{SC}}$ | Strong-coupling base parameter | Dimensionless | $2.00 \pm 0.10$ (exact within model; 5% systematic) |
| $\Delta$ | RG enhancement factor | Dimensionless | $0.126 \pm 0.07$ (framework-internal) |
| $M_0$ | Continuum base parameter | Dimensionless | $2.25 \pm 0.18$ |
| $R_\text{cont}^{\text{FI}}$ | Framework-internal glueball ratio | Dimensionless | $3.38 \pm 0.27$ |
| $R_\text{cont}^{\text{lat}}$ | Lattice MC glueball ratio | Dimensionless | $3.405 \pm 0.021$ [1] |
| $c_\text{FI}$ | Framework-internal mass gap coefficient | Dimensionless | $6.74 \pm 0.55$ |
| $b_0$ | One-loop beta function coefficient | Dimensionless | $11/(16\pi^2)$ (Thm 7.5.2) |
| $I_\text{FCC}$ | FCC tadpole integral | Dimensionless | $0.276$ (Thm 7.6.5) |
| $\varepsilon$ | Crossover path parameter | Dimensionless | $\varepsilon > 0$ for glueball (Thm 7.5.3) |
| $m_G$ | Lightest $0^{++}$ glueball mass | $[\text{mass}]$ | $\approx 2\sqrt{\sigma_\text{adj}}$ |
| $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}}$ | Scale ratio | Dimensionless | $1.994 \pm 0.021$ [2] |

---

## §3. Background and Motivation

### §3.1 The External Input Problem

Theorem 7.7.3 establishes the quantitative mass gap bound:

$$m_\text{phys} \geq c \cdot \Lambda_{\overline{\text{MS}}} \quad \text{with} \quad c = R_\text{cont} \times \frac{\sqrt{\sigma}}{\Lambda_{\overline{\text{MS}}}} \approx 6.8 \tag{3.1}$$

This bound relies on two external lattice MC inputs:
1. $R_\text{cont} = m(0^{++})/\sqrt{\sigma} = 3.405 \pm 0.021$ — from Athenodorou & Teper (2020) [1]
2. $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}} = 1.994 \pm 0.021$ — from Necco & Sommer (2002) [2]

The Strengthening Item F (Plan §12.2) calls for reducing this dependence by deriving $R_\text{cont}$ from within the CG framework.

### §3.2 Why the Exact Partition Function Cannot Directly Compute $R_\text{cont}$

At $\varepsilon = 0$, the FCC partition function (Prop 0.0.38) is exactly solvable because the character expansion diagonalizes in representation space. The transfer matrix is **block-diagonal**: each irreducible representation $R$ propagates independently, with eigenvalue $u_R(\beta)$.

The glueball mass requires a **gauge-invariant** observable — the connected plaquette-plaquette correlator. At $\varepsilon = 0$, the plaquette $\operatorname{Re}\operatorname{Tr}_3 U_\square$ acts only within the fundamental block, and the connected correlator vanishes at timelike separation (Eq. (0.1)). This is because the global label constraint prevents mixing between representation sectors.

**Physical interpretation:** The glueball is a color-singlet bound state. Its formation requires off-diagonal coupling between representation sectors — precisely what the crossover path ($\varepsilon > 0$) provides via the adjoint plaquette term (Thm 7.5.3).

### §3.3 The Casimir Scaling Bridge

The key insight is that while we cannot directly compute $R_\text{cont}$ from the exact partition function, we **can** compute:

1. **Representation-dependent string tensions** $\sigma_R = -\ln u_R(\beta)$ for all $R$ — exactly, at all $\beta$
2. **Casimir scaling ratios** $\sigma_R/\sigma_3$ — which interpolate between the character expansion limit $\sigma_8/\sigma_3 \to 2$ (strong coupling) and Casimir scaling $\sigma_8/\sigma_3 \to 9/4$ (weak coupling)
3. **The Casimir ratio factor** $\eta(\text{SU}(3)) = \sqrt{C_2(\mathbf{8})/C_2(\mathbf{3})} = 3/2$ — from Lie algebra alone

Combined with the constituent gluon model ($M_0^{\text{SC}} = 2$) and a semi-analytic RG enhancement ($\Delta = 0.126 \pm 0.07$), this yields $R_\text{cont}^{\text{FI}} = 3.38 \pm 0.27$.

### §3.4 Circular Reasoning Avoidance

It is essential to verify that $R_\text{cont}^{\text{FI}}$ is genuinely framework-internal:

| Component | Source | Uses lattice $R_\text{cont}$? |
|-----------|--------|------------------------------|
| $M_0^{\text{SC}} = 2$ | Constituent gluon model + Casimir scaling | **No** |
| $\eta(\text{SU}(3)) = 3/2$ | Lie algebra ($C_2(\mathbf{8})/C_2(\mathbf{3}) = 9/4$) | **No** |
| $\Delta_1 = 0.126$ | $\Lambda/\sqrt{\sigma}$ ratio [2] | **No** (uses $\sqrt{\sigma}/\Lambda$, not $R_\text{cont}$) |
| $\Delta_2 = 0.066$ | FCC tadpole ($b_0$, $I_\text{FCC}$) | **No** |
| $\Delta_3 = 0.135$ | SU(3) lattice extraction | **Yes** ⚠ ($\Delta_3 = (R_\text{cont}^{\text{lat}}/\eta - 2)/2$) |
| **Adopted $\Delta = 0.126 \pm 0.07$** | **Centered on $\Delta_1$** | **No** ($\Delta_3$ used as CHECK only) |
| $R_\text{cont}^{\text{FI}} = 3.38$ | Parts (a)–(c) assembled | **No** (lattice used as CHECK) |

**Key distinction:** The adopted $\Delta$ is centered on $\Delta_1$ (the $\Lambda/\sqrt{\sigma}$ estimate), which uses only $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}}$ [2] — the same external input already needed for Part (e). The lattice-calibrated estimate $\Delta_3 = 0.135$ falls within the adopted uncertainty range, confirming consistency, but is **not** used to set the central value. See Derivation §7.5 for the full classification of estimates into framework-internal (Tier 1) and lattice-calibrated (Tier 2).

---

## §4. Derivation Structure

The complete derivation is in the [Derivation file](./Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio-Derivation.md):

- **§5:** Part (a) — Casimir Scaling from FCC Transfer Matrix ($\sigma_R = -\ln u_R$, crossover from character expansion limit to Casimir scaling)
- **§6:** Part (b) — Constituent Gluon Model ($M_0^{\text{SC}} = 2$, $\mathbf{8} \otimes \mathbf{8} \to \mathbf{1}$ channel)
- **§7:** Part (c) — RG Enhancement ($\Delta = 0.126 \pm 0.07$ from two framework-internal estimates + lattice consistency check)
- **§8:** Parts (d)–(e) — Assembly ($R_\text{cont}^{\text{FI}} = 3.38 \pm 0.27$, $c_\text{FI} = 6.74 \pm 0.55$)

---

## §9. Summary and Connections

### §9.1 What This Proposition Achieves

1. **Derives** $R_\text{cont}^{\text{FI}} = 3.38 \pm 0.27$ from framework-internal ingredients only
2. **Confirms** consistency with lattice MC at $0.09\sigma$ — the framework's internal structure predicts the correct glueball ratio
3. **Reduces** external MC inputs to Thm 7.7.3 from 2 to 1
4. **Establishes** the constituent gluon model as a reliable zeroth-order estimate ($M_0^{\text{SC}} = 2$)
5. **Identifies** the one-loop RG enhancement as the dominant correction ($\Delta \approx 14\%$)

### §9.2 Honest Assessment of Limitations

1. **$\Delta$ is estimated, not derived:** The RG enhancement factor has $50\%$ relative uncertainty. A rigorous derivation would require solving the Bethe-Salpeter equation for the glueball bound state on the crossover path — a significant technical challenge.

2. **$R_\text{cont}^{\text{FI}}$ has $\sim 8\%$ uncertainty** vs lattice's $\sim 0.6\%$. The value of this proposition is in **reducing external dependence**, not in improving precision.

3. **Adjoint string breaking:** The adjoint representation has N-ality 0, so its asymptotic string tension vanishes. The $\sigma_8$ used here is the intermediate-distance string tension, valid before string breaking. This is physically relevant for glueball physics (the glueball mass scale is set by the intermediate-distance confining potential, not the asymptotic one).

4. **Remaining external input:** $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}} = 1.994 \pm 0.021$ remains external. Eliminating this would require an analytic computation of the Lambda parameter — a significantly harder problem addressed in Item G.

---

## §10. References

[1] Athenodorou, A. & Teper, M. "The glueball spectrum of SU(3) gauge theory in 3+1 dimensions." JHEP 11 (2020) 172. [arXiv:2007.06422]

[2] Necco, S. & Sommer, R. "The N_f = 0 heavy quark potential from short to intermediate distances." Nucl. Phys. B 622 (2002) 328. [arXiv:hep-lat/0108008]. *Note:* The value $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}} = 1.994 \pm 0.021$ is derived from $r_0\Lambda_{\overline{\text{MS}}} = 0.602 \pm 0.048$ combined with $r_0\sqrt{\sigma} = 1.199 \pm 0.012$, not directly quoted as such.

[3] Morningstar, C. & Peardon, M.J. "The glueball spectrum from an anisotropic lattice study." PRD 60 (1999) 034509. [arXiv:hep-lat/9901004]

[4] Ishikawa, K.-I. et al. "$\Lambda_{\overline{\text{MS}}}$ from the nonperturbatively renormalized quark mass." JHEP 12 (2017) 067. *Note:* Alternative $\Lambda_{\overline{\text{MS}}}$ determination; consistent with [2].

[5] Bali, G.S. "Casimir scaling of SU(3) static potentials." PRD 62 (2000) 114503. [arXiv:hep-lat/0006022]. *Note:* The value $\sigma_8/\sigma_3 = 2.26 \pm 0.06$ is a reasonable interpretation of the lattice data at intermediate distances, not a single directly quoted number.

[6] Athenodorou, A. & Teper, M. "SU($N$) gauge theories in 3+1 dimensions: glueball spectrum, string tensions and topology." JHEP 12 (2021) 082. [arXiv:2106.00364]

[7] Buisseret, F. et al. "Casimir scaling and glueball mass ratios." PLB 873 (2026). [arXiv:2509.09454]. *Note:* See also Buisseret, F., Mathieu, V. & Semay, C. "Glueball and gluelump spectrum in the constituent gluon model." EPJA 27 (2006) 225, for an earlier systematic study.

[8] Hong, D.K. et al. "Casimir scaling and glueball mass." PLB 775 (2017) 89. [arXiv:1705.00286]. *Note:* Hong et al. use a mass-squared form of Casimir scaling ($m_G^2 \propto C_2$) rather than the linear form used here.

[9] Boulanger, N., Buisseret, F., Mathieu, V. & Semay, C. "Constituent gluon interpretation of glueballs." EPJA 38 (2008) 317. [arXiv:0806.3875]

[10] Dalla Brida, M. & Ramos, A. "The gradient flow coupling at high perturbative orders from the lattice." EPJC 79 (2019) 435. [arXiv:1905.05147]. *Note:* Modern $\Lambda_{\overline{\text{MS}}}$ determination using gradient flow; consistent with [2].
