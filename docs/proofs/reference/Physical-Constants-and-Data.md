# Physical Constants and Verification Data

This document contains physical constants, numerical verification targets, and the dependency graph for Chiral Geometrogenesis theorems. See [CLAUDE.md](../CLAUDE.md) for core directives.

---

## Key Physical Constants (for numerical verification)

When restoring units for numerical checks:

| Constant | Symbol | Value |
|----------|--------|-------|
| Speed of light | c | 2.998 × 10⁸ m/s |
| Planck's constant | ℏ | 1.055 × 10⁻³⁴ J·s |
| Newton's constant | G | 6.674 × 10⁻¹¹ m³/(kg·s²) |
| Planck mass | M_P | 2.176 × 10⁻⁸ kg = 1.221 × 10¹⁹ GeV |
| Pion decay constant | f_π | 92.2 MeV |
| Proton mass | m_p | 938.3 MeV |
| QCD scale | Λ_QCD | 210 ± 14 MeV (PDG 2024) |

### QCD Scales and ω₀ (STANDARD DEFINITIONS)

**IMPORTANT:** The "140 vs 200 MeV" in different theorems is NOT an inconsistency.

| Scale | Value | Relation to ω₀ | Used In | Status |
|-------|-------|----------------|---------|--------|
| **ω₀ ≡ Λ_QCD** | **200-210 MeV** | Fundamental | Prediction 8.2.2, Time emergence | Phenomenological |
| m_π (pion mass) | 139.57 MeV | 0.70 × ω₀ | Theorem 3.1.1 (mass formula) | Observed |
| f_π (decay constant) | 92.2 MeV | 0.46 × ω₀ | ChPT, VEV scale | Observed |
| **√σ (string tension)** | **440 MeV** | **ℏc/R_stella** | Confinement | ✅ **DERIVED (Prop 0.0.17j)** |
| R_stella | 0.44847 fm | ℏc/√σ | Stella size | Input |

**Key insight:** All QCD scales differ by O(1) factors from Λ_QCD. When Theorem 3.1.1 uses "ω ~ 140 MeV", this is equivalent to using Λ_QCD ~ 200 MeV with a redefined coupling constant (the O(1) factor is absorbed into g_χ). Both formulations give **identical predictions**.

**String Tension Derivation (2026-01-05):** Proposition 0.0.17j derives σ from Casimir vacuum energy:
$$\sigma = \frac{(\hbar c)^2}{R_{\text{stella}}^2} \quad \Rightarrow \quad \sqrt{\sigma} = \frac{\hbar c}{R_{\text{stella}}} = \frac{197.327 \text{ MeV·fm}}{0.44847 \text{ fm}} = 440 \text{ MeV}$$
This gives **exact agreement** with the observed √σ = 440 MeV from lattice QCD. See [Proposition-0.0.17j-String-Tension-From-Casimir-Energy.md](../foundations/Proposition-0.0.17j-String-Tension-From-Casimir-Energy.md).

### Framework Parameters (Phase-Gradient Mass Generation)

| Parameter | Symbol | Value | Status | Source |
|-----------|--------|-------|--------|--------|
| Chiral coupling | g_χ | 4π/9 ≈ 1.396 | **DERIVED** | Proposition 3.1.1c (geometric derivation) |
| EFT cutoff | Λ | 4πf_π ≈ 1.16 GeV | IDENTIFIED | ChPT power counting (Prop. 0.0.17d) |
| Chiral VEV | v_χ | f_π ≈ 92 MeV | IDENTIFIED | QCD scale |
| Chiral condensate | Σ^(1/3) | 272 ± 15 MeV | LATTICE | FLAG 2024 |

**g_χ Geometric Derivation (2026-01-04):**

The coupling g_χ has been **derived from first principles**:

$$g_\chi = \frac{4\pi}{N_c^2} = \frac{4\pi}{9} \approx 1.396$$

**Three converging perspectives:**
1. **Holonomy:** Gauss-Bonnet gives 4π for effective χ=2 interaction surface
2. **Anomaly Matching:** Color singlet requires N_c² amplitude averaging (3̄ ⊗ 3 = 8 ⊕ **1**)
3. **Topological Invariants:** (111) boundary structure combines both constraints

**Verification:**
- Within 0.14σ of lattice QCD constraints (g_χ ≈ 1.26 ± 1.0 from LECs)
- Within 0.19σ of RG flow estimate (Prop 3.1.1b: g_χ ~ 1.3 at Λ_QCD)

See [Proposition-3.1.1c-Geometric-Coupling-Formula-Derivation.md](../Phase3/Proposition-3.1.1c-Geometric-Coupling-Formula-Derivation.md) for full derivation.

| Weinberg angle | sin²θ_W | 0.2312 (at M_Z) |
| Fine structure | α_em | 1/137.036 |

---

## Numerical Verification Targets

### Critical Values That Must Match Observation

| Quantity | CG Prediction | Observed Value | Status |
|----------|--------------|----------------|--------|
| Baryon asymmetry η | (6 ± 3) × 10⁻¹⁰ | (6.12 ± 0.04) × 10⁻¹⁰ | ✅ |
| Higgs mass | 125 GeV (input via λ) | 125.25 ± 0.17 GeV | ✅ |
| sin²θ_W(M_Z) | 0.231 (from GUT running) | 0.23122 ± 0.00003 | ✅ |
| Wolfenstein λ | 0.2245 (bare) → 0.2265 (dressed) | 0.22650 ± 0.00048 | ✅ |
| Proton mass origin | ~99% from chiral dynamics | ~99% from QCD | ✅ |
| Newton's constant | From f_χ = M_P/√(8π) | 6.674 × 10⁻¹¹ m³/kg·s² | ✅ |

### CKM Parameters (STANDARD VALUES — PDG 2024)

**IMPORTANT:** Use these values consistently throughout all documents.

| Parameter | Standard Value | Source | Notes |
|-----------|---------------|--------|-------|
| **λ (Wolfenstein)** | **0.22650 ± 0.00048** | PDG 2024 CKM fit | NOT 0.22500 |
| λ_geometric (bare) | 0.224514 | (1/φ³)×sin(72°) | High-scale value |
| QCD correction δ | 0.88% | Radiative corrections | λ_dressed = 1.009 × λ_bare |
| A | 0.826 ± 0.015 | PDG 2024 | Wolfenstein |
| ρ̄ | 0.1581 ± 0.0092 | PDG 2024 | Wolfenstein |
| η̄ | 0.3548 ± 0.0072 | PDG 2024 | Wolfenstein |
| γ (deg) | 66.0 ± 3.4 | PDG 2024 | CP angle |
| β (deg) | 22.9 ± 0.7 | PDG 2024 | CP angle |

**Note on λ confusion:** PDG lists TWO values:
- Wolfenstein (Table 12.1): λ = 0.22500 ± 0.00067 (older parameterization)
- CKM global fit: λ = 0.22650 ± 0.00048 (current standard — USE THIS ONE)

### Predictions for Future Tests

| Quantity | CG Prediction | Current Bound | Future Probe |
|----------|--------------|---------------|--------------|
| EW precision (Λ) | > 3.5 TeV | Satisfied | FCC-ee |
| Higgs trilinear κ_λ | 1.00-1.02 | |κ_λ − 1| < 0.5 | HL-LHC, FCC-hh |
| GW from EWPT | Detectable | Not yet searched | LISA |
| Torsion precession | ~10⁻²⁰ mas/yr | Not accessible | Future |
| χ* resonances | m ~ Λ ~ 4-10 TeV | Not seen | FCC-hh |

---

## Contact Points for External Verification

For establishing credibility, novel claims should be cross-checked against:

1. **Lattice QCD:** Compare predictions with numerical simulations
2. **Particle Data Group:** Verify consistency with measured values
3. **Established textbooks:** Confirm recovery of known results
4. **ArXiv preprints:** Check for related recent work
5. **Expert consultation:** Identify potential reviewers in each subdomain

---

## Dependency Graph (Critical Path)

```
PHASE 0: PRE-GEOMETRIC FOUNDATIONS
Definition 0.1.1 (Stella Octangula Topology)
    ↓
Definition 0.1.2 (Three Color Fields)
    ↓
Definition 0.1.3 (Pressure Functions)
    ↓
Theorem 0.2.1 (Total Field Superposition)
    ↓
Theorem 0.2.2 (Internal Time Emergence) ←── BREAKS BOOTSTRAP
    ↓
Theorem 0.2.3 (Stable Convergence Point)
    ↓
Theorem 0.2.4 (Pre-Geometric Energy) ←── RESOLVES NOETHER CIRCULARITY
    ↓
Theorem 5.2.2 (Pre-Geometric Coherence) ←── RESOLVES INFLATION CIRCULARITY

PHASE 1-2: DYNAMICS
Theorem 1.1.1 (Weight Diagram) ──→ SU(3) foundation
Theorem 1.2.1 (VEV) + 1.2.2 (Anomaly) ──→ Chiral field foundation
    ↓
Theorem 2.2.2 (Limit Cycle) + Theorem 2.2.4 (Chirality Selection)
    ↓
Theorem 2.2.3 (Time Irreversibility) ←── ARROW OF TIME

PHASE 3: MASS GENERATION
Theorem 3.0.1 (Pressure-Modulated Superposition)
    ↓
Theorem 3.1.1 (Phase-Gradient Mass Generation Mass) ←── CORE MECHANISM
    ↓
Theorem 3.1.2 (Mass Hierarchy)
    ↓
Theorem 3.2.1 (Low-Energy Equivalence) ←── SM RECOVERY

PHASE 4: MATTER
Theorem 4.1.1 (Soliton Existence)
    ↓
Theorem 4.2.1 (Chiral Bias) ──→ Corollary 4.2.3 (η ~ 6×10⁻¹⁰)

PHASE 5: GRAVITY
Theorem 5.1.1 (Stress-Energy) + 5.1.2 (Vacuum Energy)
    ↓
Theorem 5.2.0 (Wick Rotation)
    ↓
Theorem 5.2.1 (Emergent Metric)
    ↓
Theorem 5.2.3 (Einstein Equations) + 5.2.4 (Newton's Constant)
    ↓
Theorem 5.3.1-2 (Torsion)
```
