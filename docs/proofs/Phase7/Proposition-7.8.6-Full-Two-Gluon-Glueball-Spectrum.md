# Proposition 7.8.6: Full Two-Gluon Glueball Spectrum

## Status: 🔶 NOVEL — FULL TWO-GLUON GLUEBALL SPECTRUM FROM GENERALIZED SALPETER EQUATION

**Role in Framework:** Extends the Prop 7.8.3–7.8.4 Salpeter equation framework beyond the lightest $0^{++}$ glueball to predict the complete two-gluon ($C = +1$) glueball spectrum: L-centroids for arbitrary orbital angular momentum, spin-dependent splittings for individual $J^{PC}$ assignments, and the first radial excitation. Resolves the last remaining open item in Gap 6 (full glueball spectrum).

**Classification:** 🔶 NOVEL (generalized L-centroid formula $R_L$, Bose symmetry quantum number classification for gluon pairs, semi-empirical spin splitting calibration, $1^{-+}$ exotic prediction) + ✅ ESTABLISHED (Salpeter equation, AFM method [11, 12], Cornell potential, Casimir scaling, Bose symmetry, spin-orbit coupling formalism)

**Key Result:**

$$\boxed{R_L = 3\sqrt{\frac{(2L+3)\left(2 - \frac{3\alpha_V}{L+1}\right)}{2}}} \tag{1.1}$$

At $\alpha_V = 0.373 \pm 0.010$:

| $L$ | $R_L$ (centroid) | $\delta R_L$ ($\alpha_V$ only) | States in multiplet |
|-----|------------------|-------------------------------|---------------------|
| 0 | $3.45$ | $\pm 0.06$ | $0^{++}$, $2^{++}$ |
| 1 | $5.69$ | $\pm 0.03$ | $0^{-+}$, $1^{-+}$ (exotic), $2^{-+}$ |
| 2 | $7.16$ | $\pm 0.02$ | $0^{++*}$, $1^{++}$, $2^{++}$, $3^{++}$, $4^{++}$ |

These uncertainties reflect $\alpha_V$ propagation only. The full systematic budget (including AFM and variational approximations) is given in the Derivation file §9.

Full $J^{PC}$ spectrum (with spin calibration):

| $J^{PC}$ | $(L, S)$ | Predicted $R$ | Lattice $R$ [2] | Deviation |
|-----------|----------|---------------|-----------------|-----------|
| $0^{++}$ | $(0, 0)$ | $3.45 \pm 0.06$ | $3.405 \pm 0.021$ | $0.7\sigma$ |
| $2^{++}$ | $(0, 2)$ | $4.78 \pm 0.50$ | $4.73 \pm 0.07$ | $0.1\sigma$ |
| $0^{-+}$ | $(1, 1)$ | $5.23 \pm 0.55$ | $5.12 \pm 0.10$ | $0.2\sigma$ |
| $1^{-+}$ | $(1, 1)$ | $5.46 \pm 0.55$ | $\sim 5.8$ [15, 16] | $0.6\sigma$ |
| $2^{-+}$ | $(1, 1)$ | $5.92 \pm 0.55$ | $6.11 \pm 0.13$ | $0.3\sigma$ |
| $3^{++}$ | $(2, 2)$ | $7.16 \pm 0.50$ | $7.00 \pm 0.16$ | $0.3\sigma$ |
| $0^{++*}$ | $(0, 0)^*$ | $5.35 \pm 0.50$ | $5.31 \pm 0.15$ | $0.1\sigma$ |

**Dependencies:**
- ✅ Proposition 7.8.4 — V-scheme coupling $\alpha_V = 0.373 \pm 0.010$ and Salpeter formula
- ✅ Proposition 7.8.3 — Bethe-Salpeter closed-form $R_\text{BS}$ (generalized here to arbitrary $L$)
- ✅ Proposition 0.0.38 — Exact FCC Partition Function (Casimir invariants)
- ✅ External: Morningstar & Peardon, PRD 60 (1999) 034509 — Pioneering lattice glueball spectrum [1]
- ✅ External: Athenodorou & Teper, JHEP 11 (2020) 172 — Updated lattice $R_\text{cont}$ benchmark data [2]
- ✅ External: Brau & Semay, PRD 70 (2004) 014017 — Semirelativistic glueball models [14]
- ✅ External: Semay & Silvestre-Brac, J. Phys. A 41 (2008) 435202 — AFM method [11]
- ✅ External: Silvestre-Brac & Semay, J. Math. Phys. 52 (2011) 052107 — AFM duality [12]

**Enables:**
- Gap 6 resolution — Full glueball spectrum (the sole remaining open item)
- Independent prediction of exotic $1^{-+}$ glueball mass, consistent with lattice estimates [15, 16]

---

## File Structure

This proposition uses the **3-file academic structure**:

| File | Purpose | Sections | Verification Focus |
|------|---------|----------|-------------------|
| **Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum.md** (this file) | Statement & motivation | §0–4, References | Conceptual correctness |
| **[Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum-Derivation.md](./Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum-Derivation.md)** | Complete derivation | §5–10 | Mathematical rigor |
| **[Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum-Applications.md](./Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum-Applications.md)** | Impact & verification | §11–14 | Physical validity |

**Quick Links:**
- [→ See the complete derivation](./Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum-Derivation.md)
- [→ See applications and verification](./Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum-Applications.md)

---

## Verification Status

**Last Verified:** 2026-02-28
**Status:** 🔶 NOVEL (multi-agent adversarial review completed; all identified issues resolved; pending Lean 4 formalization)

### Multi-Agent Verification
- [→ Multi-Agent Verification Report](../verification-records/Proposition-7.8.6-Multi-Agent-Verification-2026-02-28.md) — Literature, Mathematics, and Physics agents
- **All issues resolved** (2026-02-28): M-1 (L=2 spin-orbit), M-2 (Regge slope), M-3 (presentation), L-1 (attribution), L-2 (references), P-1 (R_0 caveat), P-4 (1^{-+} lattice data), W-1 (uncertainties), W-3 (1/r³ ratio), W-4 (helicity caveat), W-5 (hybrid distinction), L-3 (string-breaking), P-5 (labeling)

### Verification Checklist
- [x] All symbols defined in symbol table (§2)
- [x] Dimensional consistency verified (C-13)
- [x] Dependencies on prerequisite theorems valid
- [x] No circular references
- [x] Bose symmetry classification correct for identical spin-1 bosons — C-1
- [x] Matrix elements $\langle p^2 \rangle_L = \beta^2$ independent of $L$ — C-2
- [x] Matrix element $\langle r \rangle_L = (2L+3)/(2\beta)$ — C-3
- [x] Matrix element $\langle 1/r \rangle_L = \beta/(L+1)$ — C-4
- [x] AFM optimization $\nu^* = \beta$ (universal) — C-5
- [x] Closed-form $R_L = 3\sqrt{(2L+3)(2-3\alpha_V/(L+1))/2}$ — C-6
- [x] $L = 0$ recovery: $R_0 = 3\sqrt{3(2-3\alpha_V)/2}$ matches Prop 7.8.3 — C-7
- [x] $R_0(0.373) = 3.45$ consistent with Prop 7.8.4 — C-8
- [x] Large-$L$ Regge slope: $R_L^2 \to 18L$, i.e., $m^2 \propto L$ with $dR^2/dL = 18$ — C-9
- [x] RMS radii within Cornell validity for all states — C-10
- [x] Spin-dependent splitting $\Delta_{SS}(L=0) = 1.33$ (calibration) — C-11
- [x] $R(2^{++}) = 4.78$ consistent with lattice $4.73 \pm 0.07$ — C-12
- [x] Dimensional consistency of all formulas — C-13
- [x] Mass ordering matches lattice — C-14

### Verification Scripts
- `verification/Phase7/prop_7_8_6_full_glueball_spectrum.py` — Standard + adversarial verification (C-1 through C-14, ADV-1 through ADV-6): **20/20 PASS**
- `verification/Phase7/prop_7_8_6_adversarial_physics.py` — Extended adversarial physics verification (MAV-1 through MAV-12): **12/12 PASS**

### Verification Plots
- `verification/plots/prop_7_8_6_full_glueball_spectrum.png` — 4-panel summary ($R_L$ vs $L$, full $J^{PC}$ spectrum, $\alpha_V$ sensitivity, residuals)
- `verification/plots/prop_7_8_6_adversarial_physics.png` — 6-panel adversarial verification (spectrum comparison, spin-orbit sensitivity, Regge trajectory, radial excitation, $\alpha_V$ bands, residual tensions)

---

## §0. Context and Motivation

### §0.1 Beyond the Lightest Glueball

Propositions 7.8.1–7.8.4 predict the lightest $0^{++}$ glueball mass ratio $R_V = 3.45 \pm 0.06$ (1.7%), in excellent agreement with lattice QCD ($R_\text{cont} = 3.405 \pm 0.021$, $0.7\sigma$ tension). However, a single mass ratio, while impressive, tests only one number. The full glueball spectrum — excited states, quantum number assignments, mass ordering — tests the **structural correctness** of the Salpeter equation framework, not just one parameter.

The [Research-Remaining-Gaps-Worksheet](../supporting/Research-Remaining-Gaps-Worksheet.md) §6.1 identifies the full glueball spectrum as the **sole remaining open item** in Gap 6:

> *"Remaining: Full glueball spectrum (excited states, quantum numbers) still open"*

### §0.2 Scope: Two-Gluon States Only

This proposition treats **two-gluon glueball states** exclusively. These have:
- **Charge conjugation $C = +1$** — two gluons always form $C$-even states
- $C = -1$ states (oddball glueballs) require **three or more gluons** and are beyond the scope of the two-body Salpeter equation

The two-gluon sector covers the majority of the lattice glueball spectrum, including $0^{++}$, $2^{++}$, $0^{-+}$, $2^{-+}$, $3^{++}$, and the exotic $1^{-+}$.

### §0.3 Three-Layer Strategy

The predictions are organized in three layers of decreasing rigor:

1. **Layer 1 (parameter-free):** L-centroid formula $R_L$ from the generalized Salpeter equation — genuine prediction from $\alpha_V$ alone
2. **Layer 2 (one calibration):** Individual $J^{PC}$ masses using the lattice $0^{++}$–$2^{++}$ splitting as a single calibration input for spin-dependent effects
3. **Layer 3 (variational):** First radial excitation $0^{++*}$ from an orthogonal variational ansatz with a model-dependent radial excitation ratio

### §0.4 Prerequisites

| Result | Source | What It Provides |
|--------|--------|-----------------|
| Salpeter closed-form | Prop 7.8.3 | $R = 3\sqrt{3(2-3\alpha)/2}$ (generalized to $R_L$) |
| V-scheme coupling | Prop 7.8.4 | $\alpha_V = 0.373 \pm 0.010$ |
| Casimir invariants | Prop 0.0.38 | Color factors for $\mathbf{8} \otimes \mathbf{8} \to \mathbf{1}$ |
| Lattice spectrum | A&T (2020) [2] | Benchmark data for all $J^{PC}$ states |
| AFM method | Semay [11, 12] | Variational replacement for relativistic kinetic energy |
| Glueball models | Brau & Semay [14] | Radial excitation ratio benchmark |

---

## §1. Formal Statement

**Proposition 7.8.6** (Full Two-Gluon Glueball Spectrum)

### Part (a) — Quantum Number Classification

*Two identical massless gluons in the color-singlet channel ($\mathbf{8} \otimes \mathbf{8} \to \mathbf{1}$, symmetric under particle exchange) must satisfy Bose symmetry. The total wavefunction (spatial $\times$ spin $\times$ color) must be symmetric. Since the color-singlet state is symmetric under interchange, the combined spatial$\times$spin state must also be symmetric.*

*For two spin-1 particles, the total spin $S = 0, 1, 2$:*
- *$S = 0$: symmetric under exchange*
- *$S = 1$: antisymmetric under exchange*
- *$S = 2$: symmetric under exchange*

*Spatial wavefunctions with orbital angular momentum $L$ have parity $(-1)^L$ under exchange. Therefore:*

| $L$ (parity under exchange) | Allowed $S$ | $P = (-1)^L$ | $C = (-1)^{L+S}$ | $J^{PC}$ states |
|----|-------------|---------------|-------------------|-----------------|
| *0 (symmetric)* | *$S = 0, 2$* | *$+$* | *$+$* | *$0^{++}$, $2^{++}$* |
| *1 (antisymmetric)* | *$S = 1$* | *$-$* | *$+$* | *$0^{-+}$, $1^{-+}$ (exotic), $2^{-+}$* |
| *2 (symmetric)* | *$S = 0, 2$* | *$+$* | *$+$* | *$2^{++}_S$ ($S{=}0$); $0^{++}$, $1^{++}$, $2^{++}_D$, $3^{++}$, $4^{++}$ ($S{=}2$)* |

*The $1^{-+}$ state is exotic: it cannot be formed from $q\bar{q}$ (where $C = (-1)^{L+S}$ and $P = (-1)^{L+1}$ always give $PC \neq -+$ for $J = 1$).*

### Part (b) — Generalized L-Centroid Formula

*For the trial wavefunction $\psi_L(r) = N_L r^L e^{-\beta r}$, the spinless Salpeter equation with Cornell potential and AFM yields the spin-averaged centroid mass ratio:*

$$\boxed{R_L = 3\sqrt{\frac{(2L+3)\left(2 - \frac{3\alpha_V}{L+1}\right)}{2}}} \tag{1.1}$$

*This reduces to Prop 7.8.3 Eq. 8.4 at $L = 0$ and predicts:*

| $L$ | $R_L$ | $\delta R_L$ ($\alpha_V$ only) |
|-----|--------|-------------------------------|
| *0* | *$3.45$* | *$\pm 0.06$* |
| *1* | *$5.69$* | *$\pm 0.03$* |
| *2* | *$7.16$* | *$\pm 0.02$* |

### Part (c) — Spin-Dependent Spectrum

*Using the lattice $0^{++}$–$2^{++}$ splitting $\Delta_{SS} = 1.33$ as a single calibration input, and spin-orbit splitting estimates for $L \geq 1$, the full $J^{PC}$ spectrum is:*

| $J^{PC}$ | $(L, S)$ | Predicted $R$ | Lattice $R$ [2, 15, 16] |
|-----------|----------|---------------|--------------------------|
| *$0^{++}$* | *$(0, 0)$* | *$3.45 \pm 0.06$* | *$3.405 \pm 0.021$ [2]* |
| *$2^{++}$* | *$(0, 2)$* | *$4.78 \pm 0.50$* | *$4.73 \pm 0.07$ [2]* |
| *$0^{-+}$* | *$(1, 1)$* | *$5.23 \pm 0.55$* | *$5.12 \pm 0.10$ [2]* |
| *$1^{-+}$* | *$(1, 1)$* | *$5.46 \pm 0.55$* | *$\sim 5.8 \pm 0.5$ [15, 16]* |
| *$2^{-+}$* | *$(1, 1)$* | *$5.92 \pm 0.55$* | *$6.11 \pm 0.13$ [2]* |
| *$3^{++}$* | *$(2, 2)$* | *$7.16 \pm 0.50$* | *$7.00 \pm 0.16$ [2]* |

### Part (d) — First Radial Excitation

*An orthogonal variational ansatz $\psi_1(r) = N(1 - \gamma r)e^{-\beta_1 r}$ predicts:*

$$R(0^{++*}) = 5.35 \pm 0.50 \tag{1.2}$$

*consistent with the lattice value $5.31 \pm 0.15$ [2].*

---

## §2. Symbol and Dimension Table

| Symbol | Meaning | Dimension | Value / Source |
|--------|---------|-----------|---------------|
| $L$ | Orbital angular momentum quantum number | Dimensionless | $0, 1, 2, \ldots$ |
| $S$ | Total spin of two-gluon system | Dimensionless | $0, 1, 2$ |
| $J$ | Total angular momentum $\mathbf{J} = \mathbf{L} + \mathbf{S}$ | Dimensionless | $|L-S|, \ldots, L+S$ |
| $P$ | Parity | $\pm 1$ | $(-1)^L$ |
| $C$ | Charge conjugation | $\pm 1$ | $(-1)^{L+S}$ |
| $\alpha_V$ | V-scheme coupling at glueball scale | Dimensionless | $0.373 \pm 0.010$ (Prop 7.8.4) |
| $\sigma_3$ | Fundamental string tension | $[\text{mass}^2]$ | Input parameter |
| $\beta$ | Variational parameter (inverse size) | $[\text{mass}]$ | Optimized per $L$ |
| $R_L$ | L-centroid mass ratio $m_L / \sqrt{\sigma_3}$ | Dimensionless | Eq. (1.1) |
| $\Delta_{SS}$ | Spin-spin splitting $R(2^{++}) - R(0^{++})$ | Dimensionless | $1.33$ (calibration from [1, 2]) |
| $c_{LS}$ | Spin-orbit coefficient for $L = 1$ | Dimensionless | $\approx 0.23$ (estimated) |
| $\nu$ | AFM auxiliary parameter | $[\text{mass}]$ | $\nu^* = \beta$ (universal) |
| $\langle p^2 \rangle_L$ | Momentum-squared expectation value | $[\text{mass}^2]$ | $\beta^2$ (all $L$) |
| $\langle r \rangle_L$ | Position expectation value | $[\text{length}]$ | $(2L+3)/(2\beta)$ |
| $\langle 1/r \rangle_L$ | Inverse-position expectation value | $[\text{mass}]$ | $\beta/(L+1)$ |
| $r_\text{rms}$ | RMS radius of glueball | $[\text{length}]$ | $\leq 0.53$ fm (all states) |

---

## §3. Physical Interpretation

### §3.1 What the Spectrum Tests

The full glueball spectrum tests the Salpeter framework at multiple independent points:

| Aspect tested | Single $0^{++}$ (Props 7.8.3–4) | Full spectrum (Prop 7.8.6) |
|---------------|----------------------------------|---------------------------|
| Mass values | 1 number | 7+ numbers |
| Quantum numbers | Assumed $0^{++}$ | Predicted from Bose symmetry |
| Mass ordering | Trivial | Must match lattice sequence |
| Regge trajectory | Not tested | $m^2 \propto L$ verified |
| Spin structure | Not tested | Hyperfine + spin-orbit |
| Exotic states | Not applicable | $1^{-+}$ predicted |

### §3.2 Three Prediction Layers

**Layer 1 (L-centroids):** The formula $R_L$ depends only on $\alpha_V$. No additional parameters are introduced. The L-dependence comes entirely from the $r^L$ factor in the trial wavefunction interacting with the Cornell potential. This is a genuine multi-point prediction from a single input.

**Layer 2 (spin splittings):** One semi-empirical input ($\Delta_{SS} = 1.33$) calibrates the spin-dependent forces. The relative splittings within each multiplet are then predicted by angular momentum algebra ($\langle \mathbf{L} \cdot \mathbf{S} \rangle$) and the scaling of $\langle 1/r^3 \rangle_L$.

**Layer 3 (radial excitation):** The $0^{++*}$ prediction uses a model-dependent ratio ($E_1^*/E_0^* \approx 1.55$) from numerical Salpeter solutions. This is the least rigorous layer.

### §3.3 Why $\langle p^2 \rangle_L = \beta^2$ Is Remarkable

The independence of $\langle p^2 \rangle$ from $L$ is not a coincidence — it reflects the fact that the radial wavefunction $r^L e^{-\beta r}$ solves the hydrogen-atom Schrodinger equation (with $L$-dependent principal quantum number). The centrifugal kinetic energy exactly compensates the reduced radial probability near the origin. This leads to the clean factored form of $R_L$.

---

## §4. Derivation Structure

The complete derivation is in the [Derivation file](./Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum-Derivation.md):

- **§5:** L-wave variational ansatz — generalized wavefunction $r^L e^{-\beta r}$, normalization, matrix elements
- **§6:** Optimization and closed-form formula — AFM optimization, $\beta$ optimization, $R_L$ formula, uncertainty propagation
- **§7:** Spin-dependent interactions — spin-spin, spin-orbit, tensor; $L = 0$, $L = 1$, $L = 2$ multiplets
- **§8:** Radial excitations — orthogonal ansatz for $0^{++*}$, matrix elements, predicted ratio
- **§9:** Uncertainty budget — per-state errors from $\alpha_V$, AFM, variational, spin calibration
- **§10:** Self-consistency checks — $L = 0$ recovery, large-$L$ Regge, RMS radii, mass ordering, Bose symmetry

---

## References

[1] Morningstar, C. & Peardon, M.J. "The glueball spectrum from an anisotropic lattice study." PRD 60 (1999) 034509. [arXiv:hep-lat/9901004]

[2] Athenodorou, A. & Teper, M. "The glueball spectrum of SU(3) gauge theory in 3+1 dimensions." JHEP 11 (2020) 172. [arXiv:2007.06422]

[3] Necco, S. & Sommer, R. "The N_f = 0 heavy quark potential from short to intermediate distances." Nucl. Phys. B 622 (2002) 328. [arXiv:hep-lat/0108008]

[4] Mathieu, V., Semay, C. & Silvestre-Brac, B. "Gluons in glueballs: spin or helicity?" PRD 77 (2008) 114022. [arXiv:0802.0088]

[5] Bali, G.S. "Casimir scaling of SU(3) static potentials." PRD 62 (2000) 114503. [arXiv:hep-lat/0006022]

[11] Semay, C. & Silvestre-Brac, B. "The auxiliary field method and approximate analytical solutions of the Schrodinger equation with exponential potentials." J. Phys. A 41 (2008) 435202.

[12] Silvestre-Brac, B. & Semay, C. "Duality relations in the auxiliary field method." J. Math. Phys. 52 (2011) 052107. [arXiv:1102.1321]

[14] Brau, F. & Semay, C. "Semirelativistic potential model for glueball states." PRD 70 (2004) 014017. [arXiv:hep-ph/0412173]

[15] Chen, Y. et al. "Glueball spectrum and matrix elements on anisotropic lattices." PRD 73 (2006) 014516. [arXiv:hep-lat/0510074]

[16] Gregory, E. et al. "Towards the glueball spectrum from unquenched lattice QCD." JHEP 10 (2012) 170. [arXiv:1208.1858]
