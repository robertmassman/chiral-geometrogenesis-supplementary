# Proposition 7.8.7: Three-Gluon Glueball Spectrum (C = -1 Oddballs)

## Status: 🔶 NOVEL ✅ VERIFIED — THREE-GLUON GLUEBALL SPECTRUM FROM THREE-BODY SALPETER EQUATION

**Role in Framework:** Extends the glueball program (Props 7.8.1-7.8.6) from two-gluon ($C = +1$) states to three-gluon ($C = -1$) states. Derives K-centroid mass ratios from a hyperradial variational ansatz in the three-body Salpeter equation with Y-junction confinement, determines allowed $J^{PC}$ quantum numbers from transverse gluon Bose symmetry, and predicts the odderon Regge trajectory. Resolves the sole remaining open item in Gap 6, transitioning it from "near-complete" to **fully complete**.

**Classification:** 🔶 NOVEL (K-centroid formula $R_K^{(3g)}$, helicity-based quantum number classification for three transverse gluons, odderon Regge trajectory, $0^{--}$ exotic prediction) + ✅ ESTABLISHED (three-body Salpeter equation, Y-junction confinement [6, 7], Casimir scaling, AFM method [11, 12], helicity formalism [9, 10], $d^{abc}$ color structure)

> **Erratum (2⁻⁻ exotic status):** The $2^{--}$ state was previously labeled exotic. This is incorrect: $2^{--}$ is qqbar-accessible via the $^3D_2$ state ($L=2, S=1$, giving $P = (-1)^3 = -1$, $C = (-1)^3 = -1$, $J \in \{1,2,3\}$). Only $0^{--}$ is truly exotic in the $K=1$ shell. The standard exotic $J^{PC}$ series is $0^{+-}, 0^{--}, 1^{-+}, 2^{+-}, 3^{-+}, \ldots$ (PDG Quark Model review). All numerical predictions and lattice comparisons for the $2^{--}$ state remain valid — only the "exotic" label is removed.

**Key Result:**

$$\boxed{R_K^{(3g)} = 3\sqrt{(K+3)\left(\sqrt{3} - \frac{3\,f_\text{hyp}\,\alpha_V}{2K+5}\right)}} \tag{1.1}$$

where $f_\text{hyp} \approx 0.85$ is the hyperangular averaging factor for inverse pair distances, and $K$ is the grand angular momentum quantum number. The prefactor $3 = \sqrt{9}$ arises from the adjoint Casimir scaling $\tilde{\sigma}_{3g} = (9/4)\sigma_3$, and $\sqrt{3}$ is the kinetic coefficient from the AFM with $\langle p^2 \rangle_K = \beta^2$.

At $\alpha_V = 0.373 \pm 0.010$ (zero new free parameters):

| $K$ | $R_K^{(3g)}$ (centroid) | $\delta R_K$ (sys, $13\%$) | Dominant $J^{PC}$ states |
|-----|--------------------------|---------------------------|--------------------------|
| 0 | $6.45$ | $\pm 0.84$ | $1^{+-}$, $3^{+-}$ |
| 1 | $7.58$ | $\pm 0.99$ | $0^{--}$ (exotic), $1^{--}$, $2^{--}$ |
| 2 | $8.55$ | $\pm 1.11$ | $2^{+-}$, higher $P = +$ states |
| 3 | $9.43$ | $\pm 1.23$ | $3^{--}$, higher $P = -$ states |

Note: The $\alpha_V$ parametric uncertainty is very small ($\sim 0.01$) because the Coulomb interaction is subdominant in the three-body system. The dominant uncertainties are systematic ($\sim 13\%$ for centroids): hyperradial approximation ($10\%$), Y-junction vs $\Delta$-model ($7\%$), and AFM ($5\%$), added in quadrature. Individual $J^{PC}$ predictions have $\sim 20\%$ total uncertainty (adds helicity splitting $15\%$).

Full $J^{PC}$ spectrum comparison with lattice:

| $J^{PC}$ | Predicted $R$ | Lattice $R$ [1, 2] | Deviation |
|-----------|---------------|---------------------|-----------|
| $1^{+-}$ | $5.63 \pm 1.13$ | $6.23 \pm 0.11$ | $0.5\sigma$ |
| $3^{+-}$ | $6.80 \pm 1.36$ | $7.53 \pm 0.15$ | $0.5\sigma$ |
| $1^{--}$ | $7.16 \pm 1.43$ | $8.08 \pm 0.12$ | $0.6\sigma$ |
| $2^{--}$ | $7.58 \pm 1.52$ | $8.32 \pm 0.14$ | $0.5\sigma$ |
| $2^{+-}$ | $8.38 \pm 1.68$ | $8.71 \pm 0.11$ | $0.2\sigma$ |
| $3^{--}$ | $9.05 \pm 1.81$ | $8.75 \pm 0.28$ | $0.2\sigma$ |

**Dependencies:**
- ✅ Proposition 7.8.4 — V-scheme coupling $\alpha_V = 0.373 \pm 0.010$ and Salpeter formula
- ✅ Proposition 7.8.6 — Two-gluon spectrum (predecessor; template for 3-file structure)
- ✅ Proposition 0.0.38 — Exact FCC Partition Function (Casimir invariants)
- ✅ Definition 0.1.2 — Three color fields with relative phases $2\pi/3$ (Y-junction geometry)
- ✅ External: Morningstar & Peardon, PRD 60 (1999) 034509 — Lattice glueball spectrum [1]
- ✅ External: Chen et al., PRD 73 (2006) 014516 — Updated lattice spectrum [2]
- ✅ External: Mathieu, Semay & Silvestre-Brac, PRD 74 (2006) 054002 — Three-gluon constituent model [6]
- ✅ External: Mathieu, Buisseret, Semay & Silvestre-Brac, arXiv:0811.2710 — Glueball spectrum from constituent models [9]
- ✅ External: Silvestre-Brac & Semay, J. Math. Phys. 52 (2011) 052107 — AFM three-body extension [12]

**Enables:**
- Gap 6 resolution — Complete glueball spectrum (two-gluon AND three-gluon sectors)
- Odderon Regge trajectory prediction (testable via TOTEM/D0 [17])
- Independent prediction of exotic $0^{--}$ glueball mass; $2^{--}$ prediction (non-exotic but glueball-dominant)

---

## File Structure

This proposition uses the **3-file academic structure**:

| File | Purpose | Sections | Verification Focus |
|------|---------|----------|-------------------|
| **Proposition-7.8.7-Three-Gluon-Glueball-Spectrum.md** (this file) | Statement & motivation | §0-4, References | Conceptual correctness |
| **[Proposition-7.8.7-Three-Gluon-Glueball-Spectrum-Derivation.md](./Proposition-7.8.7-Three-Gluon-Glueball-Spectrum-Derivation.md)** | Complete derivation | §5-14 | Mathematical rigor |
| **[Proposition-7.8.7-Three-Gluon-Glueball-Spectrum-Applications.md](./Proposition-7.8.7-Three-Gluon-Glueball-Spectrum-Applications.md)** | Impact & verification | §15-18 | Physical validity |

**Quick Links:**
- [→ See the complete derivation](./Proposition-7.8.7-Three-Gluon-Glueball-Spectrum-Derivation.md)
- [→ See applications and verification](./Proposition-7.8.7-Three-Gluon-Glueball-Spectrum-Applications.md)

---

## Verification Status

**Last Verified:** 2026-02-28
**Status:** 🔶 NOVEL ✅ VERIFIED (computational verification completed; multi-agent adversarial review completed 2026-02-28; Lean 4 formalization complete)

**Lean 4 Formalization:** [`Proposition_7_8_7.lean`](../../../lean/ChiralGeometrogenesis/Phase7/Proposition_7_8_7.lean)

### Verification Checklist
- [x] All symbols defined in symbol table (§2)
- [x] Dimensional consistency verified (C-12)
- [x] Dependencies on prerequisite theorems valid
- [x] No circular references
- [x] Three-boson Bose symmetry with $d^{abc}$ color → $C = -1$ — C-1
- [x] Matrix element $\langle p^2 \rangle_K = \beta^2$ independent of $K$ (6D; verified numerically to $< 10^{-15}$) — C-2
- [x] Matrix element $\langle R \rangle_K = (2K+6)/(2\beta)$ — C-3
- [x] Matrix element $\langle 1/R \rangle_K = \beta/(K+5/2)$ — C-4
- [x] AFM optimization $\nu^* = \beta/\sqrt{3}$ ($K$-independent) — C-5
- [x] Closed-form K-centroid formula — C-6
- [x] Color factor: $d^{abc}$ symmetric → $C = -1$ — C-7
- [x] Pair Casimir sum rule $\sum_{i<j}\langle F_i \cdot F_j \rangle = -9/2$ — C-8
- [x] Mass ordering matches lattice — C-9
- [x] $R^{(3g)} > R^{(2g)}$ (three-gluon heavier than two-gluon) — C-10
- [x] Odderon Regge slope positive — C-11
- [x] Dimensional consistency of all formulas — C-12

### Multi-Agent Verification
- [`Proposition-7.8.7-Multi-Agent-Verification-2026-02-28.md`](../verification-records/Proposition-7.8.7-Multi-Agent-Verification-2026-02-28.md) — Literature, Mathematics, and Physics agent adversarial review

### Verification Scripts
- `verification/Phase7/prop_7_8_7_three_gluon_glueball_spectrum.py` — Standard + adversarial verification (C-1 through C-12, ADV-1 through ADV-6): **18/18 PASS**
- `verification/Phase7/prop_7_8_7_adversarial_physics.py` — Extended adversarial physics verification (MAV-1 through MAV-12): **12/12 PASS**

### Verification Plots
- `verification/plots/prop_7_8_7_three_gluon_glueball_spectrum.png` — 4-panel summary (K-centroids vs lattice, full $J^{PC}$ spectrum, odderon trajectory, residuals)
- `verification/plots/prop_7_8_7_adversarial_physics.png` — 6-panel adversarial verification (spectrum comparison, centroids vs lattice, Regge trajectories, Y-junction vs Delta, $\alpha_V$ sensitivity, residual tensions)

---

## §0. Context and Motivation

### §0.1 The Missing Sector: C = -1 Glueballs

Proposition 7.8.6 established the complete two-gluon ($C = +1$) glueball spectrum, with 7 $J^{PC}$ states all within $1\sigma$ of lattice QCD. However, the two-body Salpeter equation cannot describe $C = -1$ states, which require **three or more gluons**.

The $C = -1$ sector ("oddballs") is physically important because:
1. It contains the **exotic** $J^{PC}$ quantum number $0^{--}$ that cannot be formed from $q\bar{q}$ (note: $2^{--}$ is qqbar-accessible via $^3D_2$)
2. It includes the **odderon** ($1^{--}$), the $C = -1$ partner of the pomeron, experimentally observed by TOTEM/D0 [17]
3. It is the **sole remaining open item** in Gap 6 of the Research-Remaining-Gaps-Worksheet

### §0.2 Scope: Three-Gluon States Only

This proposition treats **three-gluon glueball states** exclusively:
- **Charge conjugation $C = -1$** — three gluons with $d^{abc}$ (symmetric) color contraction give $C = (-1)^3 = -1$
- The $f^{abc}$ (antisymmetric) color contraction also gives $C = -1$ states with different selection rules; these are treated as a secondary channel
- Four-gluon and higher states are beyond the scope of this work

### §0.3 Two-Layer Strategy

The predictions are organized in two layers of decreasing rigor:

1. **Layer 1 (K-centroids, parameter-free):** Spin-averaged mass for each grand angular momentum shell $K$, from the hyperradial Salpeter equation with $\alpha_V$ as the sole input. Independent of spin formalism.
2. **Layer 2 (helicity-informed, parameter-free):** $J^{PC}$ quantum number assignments from transverse gluon Bose symmetry under $S_3$. Uses the helicity formalism [9, 10] rather than spin-1, following Mathieu et al.'s demonstration that the spin-1 model fails for $C = -1$ states.

### §0.4 Critical Literature Insight

Mathieu, Semay & Silvestre-Brac [9] demonstrated a fundamental result: the spin-1 constituent gluon model **fails** for $C = -1$ states (all $J^{P-}$ become degenerate, contradicting lattice), while the helicity formalism (transverse gluons with $\lambda = \pm 1$ only) naturally splits the degeneracies and matches lattice hierarchy. Our approach inherits this insight: K-centroids are formalism-independent (Layer 1), while quantum number assignments use the helicity basis (Layer 2).

### §0.5 Prerequisites

| Result | Source | What It Provides |
|--------|--------|-----------------|
| V-scheme coupling | Prop 7.8.4 | $\alpha_V = 0.373 \pm 0.010$ (zero new parameters) |
| Two-gluon spectrum | Prop 7.8.6 | Template, $C = +1$ comparison baseline |
| Casimir invariants | Prop 0.0.38 | Color factors for $\mathbf{8} \otimes \mathbf{8} \otimes \mathbf{8} \to \mathbf{1}$ |
| Color field phases | Def 0.1.2 | $2\pi/3$ separation → Y-junction geometry |
| AFM method | Semay [11, 12] | Variational replacement for relativistic kinetic energy |
| Lattice spectrum | M&P (1999) [1], Chen (2006) [2] | Benchmark data for $C = -1$ states |
| Helicity formalism | Mathieu et al. [9, 10] | Three-gluon quantum number classification |

---

## §1. Formal Statement

**Proposition 7.8.7** (Three-Gluon Glueball Spectrum)

### Part (a) — Quantum Number Classification

*Three identical transverse gluons (helicity $\lambda = \pm 1$) forming a color singlet via $d^{abc}$ contraction (totally symmetric in color) must satisfy Bose symmetry. Since the color state is symmetric, the combined spatial $\times$ helicity wavefunction must also be symmetric under $S_3$ permutations.*

*Charge conjugation: Since each gluon has $C_g = -1$, the three-gluon state has $C = (-1)^3 = -1$.*

*The allowed $C = -1$ quantum numbers, organized by grand angular momentum $K$, are:*

| $K$ | Parity $P = (-1)^{l_\rho + l_\lambda}$ | Allowed $J^{PC}$ | Notes |
|-----|----------------------------------------|-------------------|-------|
| *0* | *$+$* | *$1^{+-}$, $3^{+-}$* | *Lowest-lying oddballs* |
| *1* | *$-$* | *$0^{--}$ (exotic), $1^{--}$, $2^{--}$* | *Odderon sector; $0^{--}$ exotic* |
| *2* | *$+$* | *$2^{+-}$, $3^{+-*}$, higher $P = +$* | *Higher excitations ($P = +$ only)* |
| *3* | *$-$* | *$3^{--}$, higher $P = -$* | *Highest shell treated here* |

*The state $0^{--}$ is exotic: it cannot be formed from $q\bar{q}$. The $2^{--}$ state is qqbar-accessible via $^3D_2$ ($L=2, S=1$) and is not exotic.*

### Part (b) — K-Centroid Formula

*For the 6D hyperradial trial wavefunction $\psi_K(R) = N_K R^K e^{-\beta R}$, the spinless three-body Salpeter equation with Y-junction confinement and AFM yields the spin-averaged K-centroid mass ratio:*

$$\boxed{R_K^{(3g)} = 3\sqrt{(K+3)\left(\sqrt{3} - \frac{3\,f_\text{hyp}\,\alpha_V}{2K+5}\right)}} \tag{1.1}$$

*where $f_\text{hyp} \approx 0.85$ is the hyperangular averaging factor for the sum of inverse pair distances. The prefactor 3 arises from $\sqrt{4 \tilde{\sigma}_{3g}/\sigma_3} = \sqrt{9} = 3$ with $\tilde{\sigma}_{3g} = (9/4)\sigma_3$ from adjoint Casimir scaling. The kinetic coefficient $\sqrt{3}$ follows from $\langle p^2 \rangle_K = \beta^2$ (K-independent, §6.3) and the three-body AFM ($\nu^* = \beta/\sqrt{3}$, §9.3).*

*Numerical K-centroids at $\alpha_V = 0.373$:*

| $K$ | $R_K^{(3g)}$ | $\delta R_K$ (systematic) |
|-----|--------------|--------------------------|
| *0* | *$6.45$* | *$\pm 0.84$ ($13\%$)* |
| *1* | *$7.58$* | *$\pm 0.99$ ($13\%$)* |
| *2* | *$8.55$* | *$\pm 1.11$ ($13\%$)* |
| *3* | *$9.43$* | *$\pm 1.23$ ($13\%$)* |

### Part (c) — Full $J^{PC}$ Spectrum

*Using helicity selection rules and spin-orbit estimates for the splitting within each K-shell:*

| $J^{PC}$ | $K$ | Type | Predicted $R$ | Lattice $R$ [1, 2] |
|-----------|-----|------|---------------|---------------------|
| *$1^{+-}$* | *0* | *Non-exotic* | *$5.63 \pm 1.13$* | *$6.23 \pm 0.11$* |
| *$3^{+-}$* | *0* | *Non-exotic* | *$6.80 \pm 1.36$* | *$7.53 \pm 0.15$* |
| *$1^{--}$* | *1* | *Non-exotic (odderon)* | *$7.16 \pm 1.43$* | *$8.08 \pm 0.12$* |
| *$2^{--}$* | *1* | *Non-exotic* | *$7.58 \pm 1.52$* | *$8.32 \pm 0.14$* |
| *$0^{--}$* | *1* | ***Exotic*** | *$7.91 \pm 1.58$* | *Not measured* |
| *$2^{+-}$* | *2* | *Non-exotic* | *$8.38 \pm 1.68$* | *$8.71 \pm 0.11$* |
| *$3^{--}$* | *3* | *Non-exotic* | *$9.05 \pm 1.81$* | *$8.75 \pm 0.28$* |

### Part (d) — Odderon Regge Trajectory

*The large-$K$ asymptotics yield an odderon Regge trajectory:*

$$R_K^2 \to 9\sqrt{3}\,K \approx 15.6\,K \quad (K \to \infty) \tag{1.2}$$

*The odderon Regge slope $dR^2/dK = 9\sqrt{3} \approx 15.6$ is shallower than the pomeron slope ($dR^2/dL = 18$ from Prop 7.8.6 Eq. 11.1). The ratio $\alpha'_\text{odd}/\alpha'_\text{pom} = \sqrt{3}/2 \approx 0.87$ reflects the lower kinetic coefficient ($\sqrt{3}$ vs $2$) from the three-body AFM. The odderon intercept lies below the pomeron intercept, consistent with the experimental observation that odderon exchange is suppressed relative to pomeron exchange [17].*

---

## §2. Symbol and Dimension Table

| Symbol | Meaning | Dimension | Value / Source |
|--------|---------|-----------|---------------|
| $K$ | Grand angular momentum $= 2n + l_\rho + l_\lambda$ | Dimensionless | $0, 1, 2, \ldots$ |
| $l_\rho, l_\lambda$ | Orbital angular momenta in Jacobi coordinates | Dimensionless | $\geq 0$ |
| $n$ | Hyperradial quantum number | Dimensionless | $\geq 0$ |
| $R$ | Hyperradius $= \sqrt{\rho^2 + \lambda^2}$ | [length] | — |
| $\boldsymbol{\rho}$ | Jacobi coordinate $= (\mathbf{r}_1 - \mathbf{r}_2)/\sqrt{2}$ | [length] | — |
| $\boldsymbol{\lambda}$ | Jacobi coordinate $= (\mathbf{r}_1 + \mathbf{r}_2 - 2\mathbf{r}_3)/\sqrt{6}$ | [length] | — |
| $\beta$ | Variational parameter (inverse hyperradial size) | [mass] | Optimized per $K$ |
| $\alpha_V$ | V-scheme coupling at glueball scale | Dimensionless | $0.373 \pm 0.010$ (Prop 7.8.4) |
| $\sigma_3$ | Fundamental string tension | $[\text{mass}^2]$ | Input parameter |
| $R_K^{(3g)}$ | K-centroid mass ratio $m_K / \sqrt{\sigma_3}$ | Dimensionless | Eq. (1.1) |
| $C$ | Charge conjugation | $\pm 1$ | $-1$ (three gluons) |
| $d^{abc}$ | Symmetric SU(3) color structure constant | Dimensionless | Standard |
| $f_Y$ | Y-junction geometric factor (Steiner correction) | Dimensionless | $0.9515$ (Mathieu et al. [6]); absorbed into $\tilde{\sigma}_{3g}$ |
| $f_\text{hyp}$ | Hyperangular averaging factor for $\sum_{i<j} 1/r_{ij}$ | Dimensionless | $\approx 0.85$ |
| $\tilde{\sigma}_{3g}$ | Effective three-body confinement coefficient | $[\text{mass}^2]$ | $(9/4)\sigma_3$ (Casimir scaling) |
| $\langle p^2 \rangle_K$ | Momentum-squared expectation value (6D) | $[\text{mass}^2]$ | $\beta^2$ (all $K$; §6.3) |
| $\langle R \rangle_K$ | Hyperradius expectation value | [length] | $(2K+6)/(2\beta)$ |
| $\langle 1/R \rangle_K$ | Inverse hyperradius expectation value | [mass] | $\beta/(K+5/2)$ |

---

## §3. Physical Interpretation

### §3.1 Y-Junction and Stella Geometry

The stella octangula's three color fields (Definition 0.1.2) have phases separated by $2\pi/3 = 120°$. This is **exactly** the angle at a Steiner (Fermat) point for three equal sources. The Y-junction confining string topology:
- Minimizes total string length: three strings from gluon positions to a central junction point
- At equilibrium: all angles between strings are $120° = 2\pi/3$
- Directly encodes the SU(3) phase structure $\alpha = 2\pi/3$ from the stella geometry

For equilateral configurations: $L_Y = \sqrt{3} \times r$ vs $\Delta$-model $L_\Delta = 3r/2$, giving $L_Y/L_\Delta = 2\sqrt{3}/3 \approx 0.866$. This $\sim 13\%$ difference between Y-junction and $\Delta$-model potentials is a quantified systematic.

### §3.2 Why the Spin-1 Model Fails for C = -1

Mathieu et al. [9] showed that treating constituent gluons as spin-1 particles (with three polarization states: $\lambda = -1, 0, +1$) produces degenerate $J^{P-}$ states that contradict the lattice hierarchy. Physical gluons are **transverse** ($\lambda = \pm 1$ only), and the helicity formalism correctly:
1. Eliminates spurious longitudinal states
2. Naturally splits degeneracies through helicity-orbital coupling
3. Matches the lattice hierarchy without OGE calibration

Our K-centroid formula (Layer 1) is independent of this distinction — it gives spin-averaged masses. The helicity formalism enters only in Layer 2 for quantum number assignments and splitting estimates.

### §3.3 Odderon Connection

The $1^{--}$ three-gluon glueball is the lowest-lying state of the **odderon** — the $C = -1$ partner of the pomeron ($C = +1$). The TOTEM and D0 collaborations [17] reported the first experimental observation of odderon exchange by comparing elastic $pp$ scattering at $\sqrt{s} = 2.76$ and $13$ TeV (TOTEM at LHC) with $p\bar{p}$ scattering at $\sqrt{s} = 1.96$ TeV (D0 at Tevatron). Our prediction $R(1^{--}) = 7.16 \pm 1.43$ corresponds to $m_\text{odderon} \approx 3150 \pm 630$ MeV, consistent with the constituent model estimates of Mathieu et al. [6] ($\sim 3700$ MeV).

### §3.4 Prediction Quality

The three-gluon predictions have larger uncertainties than the two-gluon Prop 7.8.6 (13-20% vs 1.7-15%) because:
1. Three-body hyperradial approximation introduces $\sim 10$-$15\%$ systematic
2. Y-junction vs $\Delta$-model potential ambiguity $\sim 13\%$
3. Helicity splittings are approximate (no OGE calibration)
4. Lattice uncertainties for $C = -1$ are 3-7% (vs 0.5-2% for $C = +1$)

Despite larger individual uncertainties, the spectrum provides **six independent mass predictions** from zero new parameters, testing the framework's three-body extension.

---

## §4. Derivation Structure

The complete derivation is in the [Derivation file](./Proposition-7.8.7-Three-Gluon-Glueball-Spectrum-Derivation.md):

- **§5:** Jacobi coordinates and hyperradial framework — $\boldsymbol{\rho}$, $\boldsymbol{\lambda}$, hyperradius $R$, 6D angular momentum $K$
- **§6:** 6D matrix elements — $\langle p^2 \rangle_K$, $\langle R \rangle_K$, $\langle 1/R \rangle_K$ (all derived analytically)
- **§7:** Color structure — $d^{abc}$ symmetric singlet, pair Casimir $= -3/2$, $C = -1$ proof
- **§8:** Y-junction confinement — hyperradial potential, geometric factor $f_Y$, stella $120°$ connection
- **§9:** Three-body AFM optimization — closed-form K-centroid formula
- **§10:** Helicity formalism — Jacob-Wick construction, Bose symmetry under $S_3$, selection rules
- **§11:** $J^{PC}$ assignment — helicity families mapped to K-shells, exotic states
- **§12:** Odderon Regge trajectory — large-$K$ asymptotics, slope vs pomeron
- **§13:** Uncertainty budget — $\alpha_V$, AFM, three-body, helicity, potential model
- **§14:** Self-consistency checks — two-body limit, mass ordering, $C = -1 > C = +1$, color factor sum rule

---

## References

[1] Morningstar, C. & Peardon, M.J. "The glueball spectrum from an anisotropic lattice study." PRD 60 (1999) 034509. [arXiv:hep-lat/9901004]

[2] Chen, Y. et al. "Glueball spectrum and matrix elements on anisotropic lattices." PRD 73 (2006) 014516. [arXiv:hep-lat/0510074]

[3] Athenodorou, A. & Teper, M. "The glueball spectrum of SU(3) gauge theory in 3+1 dimensions." JHEP 11 (2020) 172. [arXiv:2007.06422]

[6] Mathieu, V., Semay, C. & Silvestre-Brac, B. "Semirelativistic potential model for low-lying three-gluon glueballs." PRD 74 (2006) 054002. [arXiv:hep-ph/0605205]

[7] Boulanger, N., Buisseret, F., Mathieu, V. & Semay, C. "Constituent gluon interpretation of glueballs and gluelumps." Eur. Phys. J. A 38 (2008) 317. [arXiv:0806.3174]

[8] Mathieu, V., Buisseret, F., Semay, C. & Silvestre-Brac, B. "Gluons in glueballs: spin or helicity?" PRD 77 (2008) 114022. [arXiv:0802.0088]

[9] Mathieu, V., Buisseret, F., Semay, C. & Silvestre-Brac, B. "The Glueball Spectrum from Constituent Models." arXiv:0811.2710.

[10] Chevalier, C. & Mathieu, V. "Two- and Three-gluon Glueballs within the Helicity Formalism." PRD 112 (2025) 014015. [arXiv:2503.15146]

[11] Semay, C. & Silvestre-Brac, B. "The auxiliary field method and approximate analytical solutions of the Schrodinger equation with exponential potentials." J. Phys. A 41 (2008) 435202.

[12] Silvestre-Brac, B. & Semay, C. "Duality relations in the auxiliary field method." J. Math. Phys. 52 (2011) 052107. [arXiv:1102.1321]

[13] Jacob, M. & Wick, G.C. "On the general theory of collisions for particles with spin." Ann. Phys. 7 (1959) 404.

[14] Brau, F. & Semay, C. "Semirelativistic potential model for glueball states." PRD 70 (2004) 014017. [arXiv:hep-ph/0412173]

[15] Silvestre-Brac, B. & Semay, C. "The auxiliary field method applied to three-body systems." Few-Body Syst. 52 (2012) 245.

[17] TOTEM/D0 Collaboration. "Comparison of pp and p-pbar differential elastic cross sections and observation of the exchange of a colorless C-odd gluonic compound." PRL 127 (2021) 062003.
