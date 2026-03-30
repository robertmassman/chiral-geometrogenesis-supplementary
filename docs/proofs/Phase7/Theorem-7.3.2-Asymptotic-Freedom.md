# Theorem 7.3.2: Asymptotic Freedom in Chiral Geometrogenesis

## Status: 🔶 NOVEL ✅ VERIFIED — Unified Presentation of UV Behavior

**Phase:** 7 — Mathematical Consistency Checks
**Role:** Establishes that CG exhibits asymptotic freedom through two independent mechanisms: standard QCD and the phase-gradient sector.

**Created:** 2026-01-17
**Last Updated:** 2026-01-17

**Dependencies:**
- ✅ Theorem 3.0.1 (Pressure Modulated Superposition)
- ✅ Proposition 0.0.17ac (Edge Mode Decomposition UV Coupling)
- ✅ Proposition 3.1.1a (Lagrangian Form From Symmetry)

---

## File Structure

This theorem uses the **3-file academic structure** plus a supplementary two-loop calculation:

| File | Purpose | Sections |
|------|---------|----------|
| **Theorem-7.3.2-Asymptotic-Freedom.md** (this file) | Statement & motivation | §1-5 |
| [Theorem-7.3.2-Asymptotic-Freedom-Derivation.md](./Theorem-7.3.2-Asymptotic-Freedom-Derivation.md) | Complete proofs | §6-9 |
| [Theorem-7.3.2-Asymptotic-Freedom-Applications.md](./Theorem-7.3.2-Asymptotic-Freedom-Applications.md) | Verification & predictions | §10-14 |
| [Theorem-7.3.2-Two-Loop-Calculation.md](./Theorem-7.3.2-Two-Loop-Calculation.md) | Two-loop β-function (NEW) | Supplement |

---

## Verification Status

**Status:** 🔶 NOVEL ✅ VERIFIED (2026-01-17, updated with corrections)

### Verification Checklist
- [x] Dependencies on prerequisite theorems valid
- [x] All symbols defined in symbol table
- [x] No circular references
- [x] Connects to existing verified propositions (3.1.1b, 3.1.1c, 2.4.2, 0.0.17s)
- [x] Falsification criteria specified (Applications §12)
- [x] Numerical verification script (7/7 tests pass)
- [x] Multi-agent peer review (2026-01-17)
- [x] **Corrections applied from verification report (2026-01-17):**
  - Fixed ln(M_P/m_t) = 38.8 (was ~40)
  - Corrected "focusing" → "sensitive dependence" terminology
  - Clarified FLAG/lattice comparison limitations
  - Updated top mass to PDG 2024 direct measurement value (172.57 ± 0.29 GeV)
  - Added missing two-loop β-function references
- [x] **Second review findings addressed (2026-01-17):**
  - β-function coefficient derivation completed with Feynman integrals (Derivation §2.6)
  - Topological UV formula derived from first principles (Applications §14.3.3.11)
  - EFT validity clarified for dimension-5 operator (Derivation §2.1.1)
  - Two-loop calculation document reviewed and verified
- [x] **g_χ(M_P) derivation clarified (2026-01-17):**
  - Connected to Prop 3.1.1c geometric derivation (g_χ = 4π/9)
  - UV value derived via inverse RG running, not merely fitted
- [x] **Alternative UV derivation developed (2026-01-17):**
  - Topological formula: g_χ^{UV} = χ·N_c/4π = 3/(2π) ≈ 0.4775
  - Matches RG-required value within 1.6%
  - Verification: `verification/Phase7/theorem_7_3_2_topological_uv_derivation.py` (8/8 tests pass)
- [x] **Phenomenological degeneracy RESOLVED (2026-01-17):**
  - Strategy 2 (axial current matching) provides independent verification of g_χ = 4π/9
  - CG prediction: g_A = 1.263 vs experimental 1.2756 (99% agreement)
  - Extracted g_χ = 1.411 vs geometric 4π/9 = 1.396 (98.9% agreement)
  - Verification: `verification/Phase7/theorem_7_3_2_axial_current_matching.py` (8/8 tests pass)
  - See [Applications §14.2](./Theorem-7.3.2-Asymptotic-Freedom-Applications.md#142-breaking-the-phenomenological-degeneracy)
- [x] **Lattice QCD determination question RESOLVED (2026-01-17):**
  - Direct lattice QCD computation of g_χ not required — axial current matching suffices
  - Geometric 4π/9 = 1.396 consistent with extracted 1.411 ± 0.071 (0.2σ tension)
  - Alternative candidates ruled out: π/2 at 2.3σ, √3 at 4.6σ
  - Verification: `verification/Phase7/theorem_7_3_2_section_14_1_lattice_determination.py` (all tests pass)
  - See [Applications §14.1](./Theorem-7.3.2-Asymptotic-Freedom-Applications.md#141-lattice-qcd-determination-of-g_χ)
- [x] **Two-class UV derivation structure identified (2026-01-17):**
  - Class 1 (Topological/Gauss-Bonnet): g_χ = χ·N_c/(4π) — for topological defect couplings
  - Class 2 (Representation/Equipartition): 1/α_s = (N_c²-1)² — for gauge couplings
  - Different geometric origins explain why formulas have different structures
  - See [Applications §14.3.7](./Theorem-7.3.2-Asymptotic-Freedom-Applications.md#1437-open-questions) Question 3

### Dependencies

| Prerequisite | Role | Status |
|--------------|------|--------|
| Proposition 3.1.1b | β-function for g_χ, RG running | ✅ VERIFIED |
| Proposition 3.1.1c | Geometric derivation of g_χ = 4π/9 | ✅ DERIVED |
| Proposition 2.4.2 | E₆ → E₈ cascade unification | ✅ VERIFIED |
| Proposition 0.0.17s | Strong coupling from gauge unification | ✅ VERIFIED |
| Theorem 2.1.1 | Bag model equilibrium | ✅ ESTABLISHED |
| Theorem 2.5.2 | Dynamical confinement | ✅ VERIFIED |
| Theorem 3.0.1 | Pressure-modulated VEV | ✅ COMPLETE |
| **Proposition 7.3.2a** | **Pressure balance origin of asymptotic freedom** | 🔶 NOVEL |
| Standard QCD | One-loop β-function | ✅ ESTABLISHED |

---

## 1. Statement

**Theorem 7.3.2 (Asymptotic Freedom in Chiral Geometrogenesis)**

> The Chiral Geometrogenesis framework exhibits asymptotic freedom: the effective couplings $\alpha_s(\mu)$ and $g_\chi(\mu)$ decrease as the energy scale $\mu$ increases, ensuring perturbative control in the UV while generating strong coupling phenomena (confinement, chiral symmetry breaking) in the IR.

### 1.1 Two Sources of Asymptotic Freedom

**Source 1: Standard QCD Sector**

The SU(3) gauge coupling $\alpha_s(\mu)$ obeys the one-loop β-function:

$$\boxed{\beta_{\alpha_s} = \mu\frac{d\alpha_s}{d\mu} = -\frac{\alpha_s^2}{2\pi}\left(\frac{11N_c - 2N_f}{3}\right) < 0}$$

for $N_f < 16.5$ (satisfied for all physical quark flavors). This is standard QCD asymptotic freedom.

**Source 2: Phase-Gradient Sector**

From Proposition 3.1.1b, the chiral coupling $g_\chi$ has β-function:

$$\boxed{\beta_{g_\chi} = \mu\frac{dg_\chi}{d\mu} = \frac{g_\chi^3}{16\pi^2}\left(2 - \frac{N_c N_f}{2}\right) < 0}$$

for $N_f > 4/3$ (satisfied for all physical cases), also exhibiting asymptotic freedom.

### 1.2 Physical Interpretation

| Energy Scale | QCD Coupling $\alpha_s$ | Chiral Coupling $g_\chi$ | Physics |
|-------------|-------------------------|--------------------------|---------|
| $\mu \gg \Lambda_{QCD}$ | Small ($\lesssim 0.1$) | Small ($\sim 0.5$) | Quarks nearly free, perturbative QCD |
| $\mu \sim \Lambda_{QCD}$ | O(1) | O(1) | Confinement, chiral symmetry breaking |
| $\mu \ll \Lambda_{QCD}$ | Non-perturbative | Frozen at $v_\chi$ | Hadronic physics |

**The chiral scale $v_\chi$ provides the transition:**
- Inside hadrons: $\chi \to 0$ (chiral symmetry partially restored)
- Outside hadrons: $\chi \to v_\chi$ (chiral symmetry broken)

### 1.3 Key Result: UV to IR Running

From Proposition 3.1.1b §4.5:

$$g_\chi(M_P) \approx 0.48 \xrightarrow{\text{RG flow}} g_\chi(\Lambda_{QCD}) \approx 1.3-1.4$$

This explains why $g_\chi \sim O(1)$ at the QCD scale without fine-tuning: asymptotic freedom naturally produces order-unity couplings in the IR from perturbatively small UV values.

### 1.4 Derivation Status of g_χ(M_P)

**The UV coupling g_χ(M_P) ≈ 0.48 is now derived** (not fitted) via **two independent paths**:

#### Path 1: IR Geometric + Inverse RG (Original)

| Step | Source | Result |
|------|--------|--------|
| 1. IR geometric value | [Proposition 3.1.1c](../Phase3/Proposition-3.1.1c-Geometric-Coupling-Formula.md) | $g_\chi^{IR} = \frac{4\pi}{N_c^2} = \frac{4\pi}{9} \approx 1.396$ |
| 2. Inverse RG running | [Proposition 3.1.1b](../Phase3/Proposition-3.1.1b-RG-Fixed-Point-Analysis.md) | $g_\chi(M_P) \approx 0.47$ |

#### Path 2: Direct UV Topological Derivation (NEW)

| Step | Source | Result |
|------|--------|--------|
| Gauss-Bonnet normalization | [Applications §14.3](./Theorem-7.3.2-Asymptotic-Freedom-Applications.md#143-alternative-uv-derivation) | $g_\chi^{UV} = \frac{\chi \cdot N_c}{4\pi} = \frac{3}{2\pi} \approx 0.4775$ |

**Physical interpretation:** "Color-weighted Euler density per unit solid angle"
- χ = 2: Euler characteristic of tetrahedron boundary (S²)
- N_c = 3: Color factor from SU(3)
- 4π: Total solid angle (Gauss-Bonnet normalization)

**Agreement between paths:** 1.6% (0.477 vs 0.470), within theoretical uncertainty.

---

**Prop 3.1.1c derivation:** The IR value g_χ ≈ 4π/9 follows from three converging arguments:
1. **Holonomy:** Gauss-Bonnet theorem gives 4π for any χ = 2 surface
2. **Anomaly matching:** Color-singlet coupling requires N_c² = 9 normalization
3. **Topological invariants:** (111) boundary structure combines both constraints

**Consistency check:** The geometric prediction g_χ(Λ_QCD) = 4π/9 ≈ 1.396 compared to RG-evolved values:

| Level | g_χ(Λ_QCD) | Discrepancy |
|-------|------------|-------------|
| One-loop RG | 1.156 | 17.2% |
| **Two-loop RG** | **1.329** | **4.8%** |
| Geometric | 1.396 | — |

The two-loop calculation reduces the discrepancy by 12.4 percentage points. See [Two-Loop-Calculation.md](./Theorem-7.3.2-Two-Loop-Calculation.md) for the complete derivation.

### 1.5 Two Classes of UV Coupling Derivations

The UV derivations for g_χ and α_s follow **fundamentally different patterns**:

| Class | Pattern | Origin | Applies To |
|-------|---------|--------|------------|
| **Topological** | $g_X = \frac{\chi \cdot C_X}{4\pi}$ | Gauss-Bonnet curvature integral | Couplings to topological defects |
| **Representation** | $\frac{1}{\alpha_X} = (\dim R_X)^n$ | Maximum entropy equipartition | Gauge couplings |

**Examples:**
- **g_χ (Class 1):** $g_\chi^{UV} = \frac{\chi \cdot N_c}{4\pi} = \frac{2 \cdot 3}{4\pi} = \frac{3}{2\pi} \approx 0.48$ — Linear in $N_c$, involves topology (χ = 2)
- **α_s (Class 2):** $\frac{1}{\alpha_s^{geom}} = (N_c^2 - 1)^2 = 64$ — Quartic in $N_c$, pure representation theory (adj⊗adj decomposition); decomposes as 52 running + 12 holonomy ([Prop 0.0.17ac](../foundations/Proposition-0.0.17ac-Edge-Mode-Decomposition-UV-Coupling.md))

**Physical distinction:**
- Class 1 (topological): Coupling strength set by **boundary curvature** of stella octangula
- Class 2 (representation): Coupling strength set by **representation dimension** of gauge group

This explains why attempting to fit α_s to a χ·C/4π formula fails: gauge couplings and topological defect couplings have different geometric origins.

**See:** [Applications §14.3.7](./Theorem-7.3.2-Asymptotic-Freedom-Applications.md#1437-open-questions) for complete analysis.

### 1.6 Unification Insight

Both QCD and CG exhibit asymptotic freedom for the **same fundamental reason**: fermion loops dominate over vertex corrections when $N_f$ is large enough.

| Coupling | Coefficient Structure | Sign of β | Behavior |
|----------|----------------------|-----------|----------|
| $\alpha_s$ | $\frac{11N_c - 2N_f}{3}$ | Negative for $N_f < 16.5$ | Asymptotic freedom |
| $g_\chi$ | $2 - \frac{N_c N_f}{2}$ | Negative for $N_f > 4/3$ | Asymptotic freedom |

The fermion loop contributions ($-2N_f$ for QCD, $-\frac{N_c N_f}{2}$ for CG) drive both couplings to zero in the UV.

---

## 2. Symbol Table

| Symbol | Name | Dimension | Physical Meaning | Value/Source |
|--------|------|-----------|------------------|--------------|
| **Couplings** | | | | |
| $\alpha_s$ | Strong coupling | [1] | QCD gauge coupling | $\alpha_s(M_Z) = 0.1180$ (PDG) |
| $g_\chi$ | Chiral coupling | [1] | Phase-gradient coupling | $g_\chi(\Lambda_{QCD}) \approx 1.3$ |
| $\beta_{\alpha_s}$ | QCD β-function | [1] | $\mu \, d\alpha_s/d\mu$ | Standard QCD |
| $\beta_{g_\chi}$ | Chiral β-function | [1] | $\mu \, dg_\chi/d\mu$ | Prop 3.1.1b |
| **Scales** | | | | |
| $\mu$ | Renormalization scale | $[M]$ | Running parameter | — |
| $\Lambda_{QCD}$ | QCD scale | $[M]$ | Confinement scale | $\sim 200$ MeV |
| $M_P$ | Planck mass | $[M]$ | Gravitational scale | $1.22 \times 10^{19}$ GeV |
| $v_\chi$ | Chiral VEV | $[M]$ | Symmetry breaking scale | $\approx f_\pi = 92.2$ MeV |
| **Group Theory** | | | | |
| $N_c$ | Number of colors | [1] | SU(3) rank + 1 | 3 |
| $N_f$ | Number of flavors | [1] | Active quark flavors | 3-6 (scale-dependent) |
| $b_0$ | One-loop coefficient | [1] | $\frac{11N_c - 2N_f}{12\pi}$ | Scale-dependent |
| **β-Function Coefficients** | | | | |
| $A_\psi$ | Fermion loop (per flavor) | [1] | $-N_c/2 = -3/2$ | Prop 3.1.1b §2 |
| $A_\chi$ | Vertex + self-energy | [1] | $+2$ | Prop 3.1.1b §2 |

---

## 3. Background: Asymptotic Freedom in QFT

### 3.1 The General Principle

Asymptotic freedom means that the effective coupling constant of a gauge theory **decreases** at high energies (short distances). This occurs when the β-function is **negative**:

$$\beta_g = \mu\frac{dg}{d\mu} < 0 \quad \Rightarrow \quad g(\mu \to \infty) \to 0$$

**Physical mechanism:** Quantum fluctuations **anti-screen** the charge rather than screening it (unlike QED).

### 3.2 QCD: The Canonical Example

In QCD, asymptotic freedom was discovered by Gross, Wilczek, and Politzer (1973), earning the Nobel Prize:

$$\beta_{\alpha_s} = -\frac{\alpha_s^2}{2\pi}\left(\frac{11N_c - 2N_f}{3}\right)$$

**Contributions:**
- $+11N_c/3$: Gluon self-interaction (anti-screening, dominant)
- $-2N_f/3$: Quark loops (screening, subdominant for $N_f < 16.5$)

**Net effect:** Anti-screening dominates → asymptotic freedom.

### 3.3 Why CG Also Exhibits Asymptotic Freedom

The phase-gradient coupling in CG has a **structurally similar** β-function:

$$\beta_{g_\chi} = \frac{g_\chi^3}{16\pi^2}\left(2 - \frac{N_c N_f}{2}\right)$$

**Contributions (Proposition 3.1.1b):**
- $+2$: Vertex + fermion self-energy corrections
- $-N_c N_f/2$: Fermion loop contribution to χ wavefunction renormalization

For $N_f > 4/3$, the fermion loop term dominates → $\beta_{g_\chi} < 0$ → asymptotic freedom.

---

## 4. Connection to Confinement

### 4.1 The Asymptotic Freedom → Confinement Link

Asymptotic freedom in the UV implies **strong coupling** in the IR. This is the foundation for confinement:

```
UV (high energy)        IR (low energy)
──────────────────────────────────────────
α_s small               α_s ~ O(1)
g_χ small               g_χ ~ O(1)
     ↓                       ↓
Perturbative            Non-perturbative
Quarks quasi-free       Quarks confined
χ ≈ 0                   χ = v_χ
```

### 4.2 Connection to Theorem 2.5.2 (Dynamical Confinement)

Theorem 2.5.2 derives the Wilson loop area law from the chiral pressure mechanism. The present theorem provides the **UV completion** of that picture:

| Aspect | Theorem 2.5.2 | This Theorem (7.3.2) |
|--------|---------------|----------------------|
| Energy regime | IR ($\mu \lesssim \Lambda_{QCD}$) | UV ($\mu \gtrsim \Lambda_{QCD}$) |
| Coupling | Strong ($\alpha_s \sim 1$) | Weak ($\alpha_s \ll 1$) |
| Physics | Confinement, area law | Perturbative QCD |
| Role | Why confinement occurs | Why UV is well-defined |

**Together:** Asymptotic freedom (UV) and confinement (IR) form a **complete dynamical picture**.

### 4.2.1 Unified Geometric Origin (NEW)

**Proposition 7.3.2a** establishes that confinement and asymptotic freedom are **two manifestations of the same geometric effect**: pressure balance in stella octangula geometry.

The key equation from Theorem 3.0.1:

$$v_\chi^2(x) = \frac{a_0^2}{2}\left[(P_R - P_G)^2 + (P_G - P_B)^2 + (P_B - P_R)^2\right]$$

gives rise to **both phenomena**:

| Phenomenon | Domain | Pressure State | Consequence |
|------------|--------|----------------|-------------|
| **Confinement** | Spatial (large r) | Balanced: $P_R \approx P_G \approx P_B$ | $v_\chi \to 0$ → flux tubes |
| **Asymptotic freedom** | Momentum (high k) | Form factor $\mathcal{F}(k) \to 0$ | Coupling suppressed |

**Physical interpretation:** High-momentum probes sample regions where single-color pressure dominates (near vertices), experiencing screening. Low-momentum probes average over pressure-balanced regions (far field), experiencing the full coupling strength.

**See:** [Proposition 7.3.2a](./Proposition-7.3.2a-Pressure-Balance-Asymptotic-Freedom.md) for the complete derivation.

### 4.3 The Chiral Transition

At intermediate scales $\mu \sim \Lambda_{QCD}$:

- **Above transition:** $\langle\chi\rangle \approx 0$ (chiral symmetry approximately restored)
- **Below transition:** $\langle\chi\rangle = v_\chi$ (chiral symmetry spontaneously broken)

The RG flow of $g_\chi$ governs this transition:
- $g_\chi \ll 1$ at high scales → χ dynamics perturbative
- $g_\chi \sim O(1)$ at $\Lambda_{QCD}$ → χ develops VEV → mass generation (Theorem 3.1.1)

---

## 5. Connection to E₆ → E₈ Cascade

### 5.1 Pre-Geometric Running

From Proposition 2.4.2, the framework extends above $M_{GUT}$ through E₆ → E₈ cascade unification:

| Scale Range | Gauge Group | β₀ | Running |
|-------------|-------------|-----|---------|
| $M_Z \to M_{GUT}$ | SM | 7 (QCD) | Standard |
| $M_{GUT} \to M_{E8}$ | E₆ | 30 | Enhanced |
| $M_{E8} \to M_P$ | E₈ (pure) | 110 | Strongly enhanced |

### 5.2 UV Coupling Matching

From Proposition 0.0.17s:

$$\frac{1}{\alpha_s^{geom}(M_P)} = (N_c^2 - 1)^2 = 64$$

**Edge-mode decomposition ([Prop 0.0.17ac](../foundations/Proposition-0.0.17ac-Edge-Mode-Decomposition-UV-Coupling.md)):** This total exponent 64 decomposes as 52 local running face modes + 12 non-local non-running holonomy modes. The running coupling 1/α_s^{running} = 52 matches standard QCD running to ~1% at one loop.

With E₆ → E₈ cascade running and scheme conversion:

> **RETRACTED (corrected 2026-02-08: NNLO running bug fix):** The value ~~1/α_s^{MS-bar}(M_P) = 99.34~~ was based on a factor-of-2 bug in `theorem_5_2_6_nnlo_running.py`. The correct NNLO running gives 1/α_s(M_P) ~ 52-55, not ~96-99. The "scheme conversion factor" θ_O/θ_T = 1.55215 was reverse-engineered to match the buggy output. The CG geometric prediction remains 1/α_s^{geom}(M_P) = 64; comparison with correct SM running is an open question under active investigation.

### 5.3 Complete UV Picture

```
M_P ──────── E₈ (pure gauge) ──────── M_{E8}
                    ↓
              1/α = 64 (geometric; MS-bar value under revision)

M_{E8} ────── E₆ (with matter) ────── M_{GUT}
                    ↓
              Cascade unification

M_{GUT} ────────── SM ────────────── M_Z
                    ↓
              α_s(M_Z) = 0.1180
```

---

## 6. Summary of Main Claims

### Claim 1: QCD Asymptotic Freedom (✅ ESTABLISHED)

Standard QCD result: $\beta_{\alpha_s} < 0$ for $N_f < 16.5$.

**See:** [Derivation §1](Theorem-7.3.2-Asymptotic-Freedom-Derivation.md#1-qcd-beta-function)

### Claim 2: Phase-Gradient Asymptotic Freedom (🔶 NOVEL)

The chiral coupling exhibits asymptotic freedom: $\beta_{g_\chi} < 0$ for $N_f > 4/3$.

**See:** [Derivation §2](Theorem-7.3.2-Asymptotic-Freedom-Derivation.md#2-phase-gradient-beta-function)

### Claim 3: Natural O(1) Coupling (🔶 NOVEL)

RG flow naturally produces $g_\chi(\Lambda_{QCD}) \sim O(1)$ from perturbative UV values.

**See:** [Derivation §3](Theorem-7.3.2-Asymptotic-Freedom-Derivation.md#3-uv-to-ir-running)

### Claim 4: UV-IR Connection (🔶 NOVEL)

Asymptotic freedom provides the UV completion for dynamical confinement (Theorem 2.5.2).

**See:** [Derivation §4](Theorem-7.3.2-Asymptotic-Freedom-Derivation.md#4-connection-to-confinement)

---

## 7. References

### 7.1 Framework Documents

1. **Proposition 3.1.1b** — RG Fixed Point Analysis for g_χ (β-function derivation)
2. **Proposition 3.1.1c** — Geometric Coupling Formula (g_χ = 4π/9 derivation)
3. **Proposition 2.4.2** — Pre-Geometric β-Function from Unified Gauge Groups
4. **Proposition 0.0.17s** — Strong Coupling From Gauge Unification
5. **Theorem 2.1.1** — Bag Model Derivation
6. **Theorem 2.5.2** — Dynamical Confinement from Pressure Mechanism
7. **Theorem 3.1.1** — Chiral Drag Mass Formula
8. **[Two-Loop-Calculation.md](./Theorem-7.3.2-Two-Loop-Calculation.md)** — Two-loop β-function coefficient (NEW)
9. **[Proposition 0.0.17ac](../foundations/Proposition-0.0.17ac-Edge-Mode-Decomposition-UV-Coupling.md)** — Edge-mode decomposition: 64 = 52 (running) + 12 (holonomy)

### 7.2 External Literature

7. **Gross, D.J. & Wilczek, F.** (1973): "Ultraviolet Behavior of Non-Abelian Gauge Theories," *Phys. Rev. Lett.* 30, 1343 — Discovery of asymptotic freedom

8. **Politzer, H.D.** (1973): "Reliable Perturbative Results for Strong Interactions?" *Phys. Rev. Lett.* 30, 1346 — Independent discovery

9. **Gross, D.J. & Wilczek, F.** (1973): "Asymptotically Free Gauge Theories. I," *Phys. Rev. D* 8, 3633 — Detailed derivation and renormalization group analysis

10. **Gross, D.J.** (2005): "The Discovery of Asymptotic Freedom and the Emergence of QCD," *Rev. Mod. Phys.* 77, 837 — Nobel lecture

11. **Caswell, W.E.** (1974): "Asymptotic Behavior of Non-Abelian Gauge Theories to Two-Loop Order," *Phys. Rev. Lett.* 33, 244 — Two-loop β-function

12. **Jones, D.R.T.** (1974): "Two-Loop Diagrams in Yang-Mills Theory," *Nucl. Phys. B* 75, 531 — Two-loop β-function (independent derivation)

13. **Peskin, M. & Schroeder, D.** (1995): *An Introduction to Quantum Field Theory*, Westview Press — Chapter 16: β-functions

14. **Weinberg, S.** (1996): *The Quantum Theory of Fields*, Vol. II, Cambridge — Asymptotic freedom derivation

15. **Particle Data Group** (2024): "Review of Particle Physics," *Phys. Rev. D* — $\alpha_s(M_Z) = 0.1180 \pm 0.0009$, $m_t = 172.57 \pm 0.29$ GeV (direct measurements)

16. **FLAG Collaboration** (2024): "FLAG Review 2024," *arXiv:2411.04268* — Lattice QCD averages (note: LEC section omitted in 2024 edition)

---

**End of Statement File**

For complete derivations, see [Theorem-7.3.2-Asymptotic-Freedom-Derivation.md](./Theorem-7.3.2-Asymptotic-Freedom-Derivation.md)

For applications and verification, see [Theorem-7.3.2-Asymptotic-Freedom-Applications.md](./Theorem-7.3.2-Asymptotic-Freedom-Applications.md)
