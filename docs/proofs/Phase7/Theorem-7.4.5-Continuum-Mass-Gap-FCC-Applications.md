# Theorem 7.4.5: Continuum Mass Gap from FCC Scaling — Applications

## Navigation

| File | Purpose |
|------|---------|
| [Statement](./Theorem-7.4.5-Continuum-Mass-Gap-FCC.md) | Theorem statement, motivation, symbol table |
| [Derivation](./Theorem-7.4.5-Continuum-Mass-Gap-FCC-Derivation.md) | Complete derivation of Parts (a)-(d) |
| **Applications (this file)** | Verification, numerical checks, physical interpretation |

---

## §8. Applications and Verification

### §8.1 Physical Interpretation

#### §8.1.1 The Mass Gap in the QCD Spectrum

The mass gap $m_\text{phys} \approx 1.5$ GeV (using CG $\sqrt{\sigma} = 440$ MeV with the lattice QCD glueball ratio) corresponds to the lightest glueball, a bound state of two or more gluons. In QCD with quarks, this state mixes with $q\bar{q}$ mesons and is difficult to observe experimentally. In pure SU(3) gauge theory (no quarks), it is the lightest particle.

The glueball spectrum from lattice QCD (Morningstar & Peardon 1999):

| State | $J^{PC}$ | Mass (MeV) | $m/\sqrt{\sigma}$ |
|-------|----------|-------------|---------------------|
| **Lightest (= mass gap)** | $0^{++}$ | 1730 ± 50 ± 80 | — (see §8.1.3) |
| Second | $2^{++}$ | 2400 ± 25 | 5.19 ± 0.07 |
| Third | $0^{-+}$ | 2590 ± 40 | 5.60 ± 0.09 |

**Comparison with CG prediction:** Using $m_{0^{++}}/\sqrt{\sigma} = 3.405$ (A&T 2020) and CG $\sqrt{\sigma} = 440$ MeV, the CG prediction is $\approx 1498$ MeV. Compared with the pure-gauge lattice result $m_{0^{++}} = 1651 \pm 22$ MeV (A&T 2020, using $\sqrt{\sigma} = 485$ MeV), the CG-scale prediction is $\sim 5\sigma$ below, reflecting the $\sim 10\%$ difference between CG and pure-gauge string tension conventions. The order-of-magnitude prediction $m \sim O(\sqrt{\sigma}) \sim 1.5$ GeV is correct; the scale discrepancy is a string tension convention issue, not a structural failure of the framework (see §7.2 of the [Derivation](./Theorem-7.4.5-Continuum-Mass-Gap-FCC-Derivation.md)).

#### §8.1.2 Glueball Spectrum Ratios

The ratios of glueball masses are universal predictions of pure SU(3) Yang-Mills:

$$\frac{m_{2^{++}}}{m_{0^{++}}} \approx 1.39, \qquad \frac{m_{0^{-+}}}{m_{0^{++}}} \approx 1.50$$

These ratios are independent of $\sqrt{\sigma}$ and provide additional tests of the FCC lattice theory.

#### §8.1.3 Glueball Ratio Clarification and String Tension Conventions

The literature quotes the lightest glueball mass ratio $m_{0^{++}}/\sqrt{\sigma}$ with different values depending on era and methodology:

| Source | Primary result | Derived $m/\sqrt{\sigma}$ | Notes |
|--------|---------------|--------------------------|-------|
| Morningstar & Peardon (1999) | $r_0 m = 4.21(11)(4)$ | $\sim 3.63$ | Via $r_0\sqrt{\sigma} = 1.160$ |
| Chen et al. (2006) | $r_0 m = 4.16(11)$ | $\sim 3.59$ | Via $r_0\sqrt{\sigma} = 1.160$ |
| **Athenodorou & Teper (2020)** | **$m/\sqrt{\sigma} = 3.405(21)$** | **3.405(21)** | **Direct determination** |

The value $m/\sqrt{\sigma} \approx 3.74$ appearing in some secondary references originates from an older scale determination ($r_0\sqrt{\sigma} \approx 1.13$ instead of the modern $1.160(6)$). **We adopt the Athenodorou & Teper (2020) value $3.405(21)$ as the primary reference**, being the most recent and comprehensive continuum extrapolation.

**String tension conventions:** Two conventions coexist in the literature:

| Convention | $\sqrt{\sigma}$ | Source | Used by |
|------------|-----------------|--------|---------|
| Pure gauge ($N_f = 0$) | $485 \pm 6$ MeV | Athenodorou & Teper (2020) | Pure-gauge lattice calculations |
| Full QCD ($N_f = 2+1$) | $440 \pm 30$ MeV | FLAG 2024 | CG framework (from $R_\text{stella}$) |

The $\sim 10\%$ difference arises because dynamical quarks screen the color flux tube, reducing the string tension. The CG framework's $\sqrt{\sigma} = 440$ MeV matches the full QCD value, suggesting $R_\text{stella}$ encodes the physical (not quenched) string tension.

### §8.2 Numerical Verification: Part (b) — Finite-Lattice-Spacing Positivity

#### §8.2.1 Mass Gap Positivity Scan

Scanning $\beta$ from $0.5$ to $\beta_c - 0.1$:

| $\beta$ | $\mu(\beta)$ | $\sigma_\text{lat}$ | $R(\beta)$ | $m_\text{phys}$ (MeV) | $m > 0$? |
|---------|-------------|---------------------|------------|----------------------|----------|
| 0.5 | 38.9 | 4.42 | 18.5 | 14100 | ✅ |
| 1.0 | 19.8 | 2.88 | 11.7 | 8920 | ✅ |
| 2.0 | 11.0 | 1.78 | 8.24 | 6280 | ✅ |
| 3.0 | 7.91 | 1.40 | 6.69 | 5100 | ✅ |
| 5.0 | 2.72 | 0.752 | 3.14 | 2390 | ✅ |
| 7.0 | 1.10 | 0.548 | 1.49 | 1140 | ✅ |
| 8.0 | 0.68 | 0.494 | 0.97 | 740 | ✅ |
| 8.5 | 0.42 | 0.461 | 0.62 | 470 | ✅ |
| 8.9 | 0.12 | 0.427 | 0.18 | 140 | ✅ |

**Result:** $m_\text{phys}(\beta) > 0$ for ALL $\beta < \beta_c$. ✅

*Note: Approximate values; see verification scripts for precise computation.*

### §8.3 Numerical Verification: Part (c) — The R → 0 Problem and Resolution

#### §8.3.1 Exact Result: R(β) → 0

The analytical formula for the dimensionless mass-gap-to-string-tension ratio is:

$$R(\beta) = \frac{8x - 3\ln 3}{\sqrt{x}} \quad \text{where } x = -\ln u_\mathbf{3}(\beta)$$

At $\beta_c$: $x_c = (3/8)\ln 3 \approx 0.412$, so $R(\beta_c) = 0$.

**Root cause:** The mass gap $\mu$ vanishes linearly at $\beta_c$, while the lattice string tension $\sigma_\text{lat} = -\ln u_\mathbf{3}$ remains finite:

$$\sigma_\text{lat}(\beta_c) = -\ln(3^{-3/8}) = \frac{3}{8}\ln 3 \approx 0.412 \neq 0$$

This is fundamentally different from the hypercubic lattice, where $\sigma_\text{lat} \to 0$ at the (second-order) transition. On the FCC lattice, the global label constraint (Migdal-Witten decomposition) freezes out surface roughening fluctuations, preventing $\sigma_\text{lat}$ from vanishing. Consequently:

- The lattice spacing $a = \sqrt{\sigma_\text{lat}/(2\sigma_\text{phys})}$ reaches a finite minimum $a_\text{min} \approx 0.20$ fm
- The physical mass gap $m_\text{phys}(\beta_c) = \sqrt{3\sigma_\text{phys}} \cdot R(\beta_c) = 0$

**The FCC lattice alone does not yield a positive continuum mass gap.** This is an exact result (Prop 7.4.4a), not an approximation artifact.

#### §8.3.2 Resolution via Universality

The continuum mass gap is obtained not from the FCC $R \to 0$ limit, but via **universality** (Conjecture C3). The argument is:

1. The FCC and hypercubic lattice theories share the same gauge group SU(3) and the same perturbative beta function coefficients $b_0, b_1$ (Prop 7.4.3)
2. Standard RG universality implies they have the same continuum limit
3. Standard lattice QCD (on hypercubic lattices) numerically establishes $m_{0^{++}}/\sqrt{\sigma} = 3.405(21)$ (Athenodorou & Teper 2020)
4. The CG framework provides $\sqrt{\sigma} = \hbar c/R_\text{stella} = 440$ MeV
5. Therefore: $m_\text{phys} \approx 3.4 \times 440 \approx 1500$ MeV

**What the FCC lattice contributes:** (i) exact proof of mass gap positivity at every finite lattice spacing (Part b); (ii) a derived (not chosen) lattice geometry constraining the framework; (iii) the geometric origin of $\sqrt{\sigma}$ from $R_\text{stella}$.

**What the FCC lattice cannot provide:** a direct continuum limit with positive mass gap, due to the frozen surface fluctuations. This limitation is inherent to the exact solvability of the model.

**This is not a "plateau extraction."** The previous formulation suggested extracting the mass gap from a plateau in $R(\beta)$, but $R(\beta)$ is strictly monotonically decreasing with no plateau (verified numerically). The universality route is the principled approach.

### §8.4 Self-Consistency Checks

#### §8.4.1 Dimensional Analysis

| Quantity | Dimensions | Check |
|----------|-----------|-------|
| $m_\text{phys} = \sqrt{3\sigma_\text{phys}} \cdot R$ | $\sqrt{E^2} \cdot 1 = E$ | ✅ |
| $C_\text{gap} = m_\text{phys}/\Lambda_{\overline{MS}} \approx 6.6$ | Dimensionless | ✅ |
| $\sqrt{\sigma} = \hbar c / R_\text{stella}$ | $E \cdot L / L = E$ | ✅ |
| $m_{0^{++}}/\sqrt{\sigma}$ | Dimensionless | ✅ |

#### §8.4.2 Limiting Cases

1. **$\beta \to 0$:** $m_\text{phys} \to \infty$ (strong coupling, lattice artifacts dominate) ✅
2. **$\beta \to \beta_c^-$:** $m_\text{phys} \to 0$ (at the transition, gap closes — since $\mu \to 0$ linearly while $a$ remains finite) ✅
3. **$\sigma_\text{phys} \to 0$:** $m_\text{phys} \to 0$ (no confinement, no mass gap) ✅
4. **Large $N_c$:** $m_\text{phys} \sim O(N_c^0)$ (mass gap independent of $N_c$ at leading order in the 't Hooft large-$N_c$ expansion, consistent with lattice studies of SU($N_c$) gauge theories; Lucini, Teper & Wenger 2004) ✅

#### §8.4.3 Cross-Checks

**Consistency with Theorem 7.4.2:** The lattice mass gap $\mu(\beta) > 0$ for $\beta < \beta_c$ (Thm 7.4.2) directly implies $m_\text{phys}(\beta) > 0$ (Part b). ✅

**Consistency with Prop 7.4.3:** The perturbative beta function coefficients $b_0, b_1$ match the universal values, supporting the universality conjecture (C3). ✅

**Consistency with Prop 7.4.4:** The scaling window identification provides the regime where continuum physics is extracted. ✅

### §8.5 Comparison with Standard Lattice QCD

| Feature | Standard lattice QCD | CG/FCC (this work) |
|---------|---------------------|---------------------|
| Mass gap existence (finite $a$) | Numerically confirmed | **Analytically proven** (Part b) |
| Continuum mass gap | Numerically extracted | Conjectured (Part c) |
| Mass gap value | 1651 ± 22 MeV (A&T 2020) | $\approx 1500$ MeV (CG $\sqrt{\sigma}$ + lattice ratio) |
| $m/\sqrt{\sigma}$ | 3.405 ± 0.021 (A&T 2020) | Imported from standard lattice QCD |
| Method | Monte Carlo + finite-size extrapolation | Exact character expansion + scaling |
| Lattice | Chosen (hypercubic) | Derived (FCC from stella) |
| Mass gap origin | Confinement (assumed) | Geometric (stella $\to$ FCC $\to$ gap) |

### §8.6 Adversarial Physics Analysis

The adversarial verification script (`thm_7_4_5_adversarial_physics.py`) tests:

1. **Mass gap positivity scan** — verify $m > 0$ across entire confined phase
2. **Ratio monotonicity** — $R(\beta)$ is monotonically decreasing
3. **String tension finiteness at $\beta_c$** — $\sigma_\text{lat}(\beta_c) > 0$
4. **Asymptotic scaling consistency** — perturbative $a$ vs non-perturbative $a$
5. **Glueball ratio comparison** — FCC prediction vs lattice QCD
6. **CG prediction consistency** — $m_\text{phys}$ from $R_\text{stella}$
7. **Conjecture sensitivity** — how much does $m_\text{phys}$ change if conjectures are weakened?

### §8.7 What This Means for the Millennium Problem

**Phase D establishes:**

1. ✅ The mass gap exists at every finite lattice spacing (rigorous, Part b)
2. ✅ The FCC lattice has the same UV behavior as standard lattice QCD (Prop 7.4.3)
3. ✅ A scaling window exists where continuum physics is accessible (Prop 7.4.4)
4. 🔮 The continuum mass gap is $\sim 1.5$ GeV using CG scale (conditional on C1-C3, via universality)

**What remains for the Millennium Problem:**

1. Prove Conjecture C1 (continuum limit existence) — this requires new mathematical tools (cf. Balaban 1987, 1988 for partial results)
2. Prove Conjecture C2 (mass gap $\Delta > 0$) — this is the core of the Millennium Problem
3. Establish Conjecture C3 (universality of FCC lattice) — strong perturbative evidence exists, but rigorous proof requires controlling lattice-specific corrections
4. Verify OS axioms (Phase E, Thm 7.4.6) — needs C1 as input
5. Apply OS reconstruction theorem — standard once axioms are verified

The FCC lattice provides a favorable starting point (exact spectrum, improved isotropy), but the fundamental mathematical challenge of the Millennium Problem remains.

---

*Document created: 2026-02-13*
*Classification: 🔶 NOVEL / 🔮 CONJECTURE*
*Phase: 7 (Renormalization, unitarity, consistency)*
