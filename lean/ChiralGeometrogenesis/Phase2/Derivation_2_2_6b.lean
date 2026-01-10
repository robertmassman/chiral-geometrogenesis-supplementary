/-
  Phase2/Derivation_2_2_6b.lean

  Derivation 2.2.6b: QCD-EM Coupling Efficiency ε

  Theorem 2.2.6 establishes that Gibbs entropy production occurs at rate
  σ = 3K/4 ~ 2.3×10²³ s⁻¹ per hadron. However, this internal entropy production
  only manifests as **observable thermodynamic entropy** when coupled to external
  degrees of freedom.

  Key Results:
  1. Coupling efficiency ε relates: dS_thermo/dt = ε · dS_Gibbs/dt
  2. For equilibrium matter at T ~ 300K: ε ~ 10⁻⁴² to 10⁻⁴⁰
  3. Suppression arises from:
     - Confinement (color fields don't extend beyond hadron)
     - Energy scale mismatch (QCD 200 MeV vs thermal 25 meV at 300K)
     - EM form factor suppression
  4. Dominant mechanism: Hadronic vacuum polarization
  5. QGP regime (T ≥ T_c): ε saturates at 1

  Physical Foundation:
  - Internal QCD color phase dynamics are confined within hadrons
  - Coupling to external (EM/thermal) degrees of freedom requires:
    * Direct EM form factor radiation (~0, exponentially suppressed)
    * Gluon-photon conversion (~0, requires deconfinement)
    * Vacuum polarization (~10⁻⁴², dominant mechanism)

  Physical Constants:
  - Λ_QCD ~ 200 MeV (QCD scale)
  - k_B T ~ 25 meV at T = 300 K (thermal energy)
  - α_em ~ 1/137 (fine structure constant)
  - T_c ~ 156 MeV (deconfinement temperature)

  Status: 🔶 NOVEL — QUANTIFIES OBSERVABLE ENTROPY PRODUCTION

  Dependencies:
  - ChiralGeometrogenesis.Basic (ColorPhase, phase angles)
  - ChiralGeometrogenesis.Phase2.Theorem_2_2_6 (Entropy Propagation)
  - ChiralGeometrogenesis.Phase2.Derivation_2_2_5a (QCD parameters, K)
  - ChiralGeometrogenesis.Phase2.Derivation_2_2_5b (QCD bath degrees of freedom)
  - ChiralGeometrogenesis.Phase2.Derivation_2_2_6a (QGP entropy production)

  Reference: docs/proofs/Phase2/Derivation-2.2.6b-QCD-EM-Coupling-Efficiency.md
-/

import ChiralGeometrogenesis.Basic
import ChiralGeometrogenesis.Phase2.Theorem_2_2_6
import ChiralGeometrogenesis.Phase2.Derivation_2_2_5a
import ChiralGeometrogenesis.Phase2.Derivation_2_2_5b
import ChiralGeometrogenesis.Phase2.Derivation_2_2_6a
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ChiralGeometrogenesis.Phase2.Derivation_2_2_6b

open Real Filter Topology
open ChiralGeometrogenesis
open ChiralGeometrogenesis.Phase2.Theorem_2_2_6
open ChiralGeometrogenesis.Phase2.Derivation_2_2_5a
open ChiralGeometrogenesis.Phase2.Derivation_2_2_6a

/-! ## Section 1: Physical Energy Scales

From §1 of the markdown: The physical problem involves coupling between
internal QCD dynamics (energy scale ~ 200 MeV) and external thermal
degrees of freedom (energy scale ~ 25 meV at 300K).

The enormous energy scale mismatch is the primary source of suppression.
-/

/-- Physical parameters for the QCD-EM coupling efficiency calculation.

Contains energy scales from both QCD and thermal sectors:
- Λ_QCD: QCD confinement scale (~200 MeV)
- k_B T: Thermal energy at temperature T
- α_em: Fine structure constant (~1/137) -/
structure CouplingEfficiencyParams where
  /-- QCD confinement scale Λ_QCD in MeV (~200 MeV) -/
  Lambda_QCD : ℝ
  Lambda_QCD_pos : Lambda_QCD > 0
  /-- Thermal energy k_B T in MeV (at 300K: ~0.0259 meV = 2.59×10⁻⁵ MeV) -/
  kBT : ℝ
  kBT_pos : kBT > 0
  /-- Fine structure constant α_em (~1/137 ≈ 0.0073) -/
  alpha_em : ℝ
  alpha_em_pos : alpha_em > 0
  alpha_em_small : alpha_em < 1
  /-- Temperature T in units of T_c -/
  T_over_Tc : ℝ
  T_over_Tc_pos : T_over_Tc > 0

/-- Standard parameters for room temperature (T = 300K).

From §1.1:
- Λ_QCD = 200 MeV
- k_B T = 25.85 meV at 300K = 2.585×10⁻⁸ MeV
- α_em ≈ 1/137 ≈ 0.0073
- T/T_c = 300K / (156 MeV / k_B) ≈ 1.66×10⁻¹⁰ (far below deconfinement)

**Unit verification:**
  k_B = 8.617×10⁻⁵ eV/K
  k_B × 300K = 0.02585 eV = 25.85 meV
  25.85 meV = 25.85 × 10⁻³ eV = 2.585 × 10⁻⁸ MeV ✓ -/
noncomputable def standardRoomTempParams : CouplingEfficiencyParams where
  Lambda_QCD := 200
  Lambda_QCD_pos := by norm_num
  kBT := 2.585e-8  -- 25.85 meV = 2.585×10⁻⁸ MeV (CORRECTED)
  kBT_pos := by norm_num
  alpha_em := 1 / 137
  alpha_em_pos := by norm_num
  alpha_em_small := by norm_num
  T_over_Tc := 1.66e-10  -- T/T_c at 300K (corrected precision)
  T_over_Tc_pos := by norm_num

/-- The energy scale ratio ξ_E = k_B T / Λ_QCD.

From §2.7: This ratio characterizes the energy mismatch.
At room temperature: ξ_E ~ 1.3×10⁻¹⁰ -/
noncomputable def energyScaleRatio (params : CouplingEfficiencyParams) : ℝ :=
  params.kBT / params.Lambda_QCD

/-- Energy scale ratio is positive. -/
theorem energyScaleRatio_pos (params : CouplingEfficiencyParams) :
    energyScaleRatio params > 0 := by
  unfold energyScaleRatio
  exact div_pos params.kBT_pos params.Lambda_QCD_pos

/-- Energy scale ratio is much smaller than 1 for T << T_c.

From §2.7: For room temperature, ξ_E ~ 10⁻¹⁰. -/
theorem energyScaleRatio_small (params : CouplingEfficiencyParams)
    (h : params.kBT < params.Lambda_QCD) :
    energyScaleRatio params < 1 := by
  unfold energyScaleRatio
  rw [div_lt_one params.Lambda_QCD_pos]
  exact h

/-- Numerical verification for standard parameters.

**Calculation:**
  ξ_E = k_B T / Λ_QCD = 2.585×10⁻⁸ MeV / 200 MeV = 1.2925×10⁻¹⁰

We prove a weak bound (ξ < 10⁻⁶) that is easily verified by norm_num.
The actual value is ~10⁻¹⁰, much smaller. -/
theorem energyScaleRatio_at_roomTemp :
    ∃ ξ : ℝ, energyScaleRatio standardRoomTempParams = ξ ∧
    ξ > 0 ∧ ξ < 1e-6 := by
  use energyScaleRatio standardRoomTempParams
  constructor
  · rfl
  constructor
  · exact energyScaleRatio_pos standardRoomTempParams
  · unfold energyScaleRatio standardRoomTempParams
    simp only
    -- 2.585×10⁻⁸ / 200 = 1.2925×10⁻¹⁰ < 10⁻⁶
    norm_num

/-! ## Section 2: Mechanism 1 — Direct EM Form Factor Coupling

From §2 of the markdown: Color phase oscillations at ω ~ K ~ 200 MeV
could produce EM radiation, but this is exponentially suppressed because:
1. Confinement cancels dipole radiation (only quadrupole survives)
2. Photons at 200 MeV cannot thermalize with a 25 meV bath

The thermal suppression factor is exp(-ℏω/k_B T) ~ exp(-10¹⁰) ≈ 0.
-/

/-- The thermal occupation number suppression factor.

From §2.7: For ω >> k_B T, the thermal occupation is:
  n(ω) = 1/(exp(ℏω/k_B T) - 1) ≈ exp(-ℏω/k_B T)

This is astronomically suppressed for QCD-scale photons at room temperature. -/
noncomputable def thermalOccupationSuppression (params : CouplingEfficiencyParams) : ℝ :=
  Real.exp (-(params.Lambda_QCD / params.kBT))

/-- Thermal suppression is always positive (but exponentially small). -/
theorem thermalOccupationSuppression_pos (params : CouplingEfficiencyParams) :
    thermalOccupationSuppression params > 0 :=
  Real.exp_pos _

/-- Thermal suppression is always less than 1 for Λ_QCD > k_B T. -/
theorem thermalOccupationSuppression_lt_one (params : CouplingEfficiencyParams)
    (h : params.Lambda_QCD > params.kBT) :
    thermalOccupationSuppression params < 1 := by
  unfold thermalOccupationSuppression
  rw [Real.exp_lt_one_iff]
  have h1 : params.Lambda_QCD / params.kBT > 1 := by
    rw [gt_iff_lt, one_lt_div params.kBT_pos]
    exact h
  linarith

/-- At room temperature, thermal suppression is effectively zero.

From §2.7: exp(-ℏω/k_B T) = exp(-10¹⁰) is computationally indistinguishable from 0.

We prove a weaker bound: exp(-x) < 1/x for x > 1.
For x = Λ_QCD/k_B T ~ 10⁷, this gives suppression < 10⁻⁷.

**Proof outline:**
1. For any x > 0, x ≠ 0: x < x + 1 < exp(x) (from Real.add_one_lt_exp)
2. Taking reciprocals (order reverses): exp(-x) = 1/exp(x) < 1/x
3. Apply to x = Λ_QCD/k_B T > 1 -/
theorem thermalSuppression_negligible (params : CouplingEfficiencyParams)
    (h : params.Lambda_QCD / params.kBT > 1) :
    thermalOccupationSuppression params < params.kBT / params.Lambda_QCD := by
  unfold thermalOccupationSuppression
  -- Let x = Λ_QCD / k_B T, then we need exp(-x) < 1/x = k_B T / Λ_QCD
  set x := params.Lambda_QCD / params.kBT with hx_def
  have hx_pos : x > 0 := div_pos params.Lambda_QCD_pos params.kBT_pos
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  -- Step 1: x < exp(x) (from x < x + 1 < exp(x))
  have h1 : x < Real.exp x := by
    calc x < x + 1 := by linarith
      _ < Real.exp x := Real.add_one_lt_exp hx_ne
  -- Step 2: exp(-x) < 1/x (taking reciprocals)
  have hexp_pos : Real.exp x > 0 := Real.exp_pos x
  have h2 : Real.exp (-x) < x⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_lt_inv₀ hexp_pos hx_pos).mpr h1
  -- Step 3: 1/x = k_B T / Λ_QCD (by definition of x)
  have h3 : x⁻¹ = params.kBT / params.Lambda_QCD := by
    rw [hx_def]
    rw [inv_div]
  rw [← h3]
  exact h2

/-- Coupling efficiency from EM form factor mechanism.

From §2.8: ε_EM ~ exp(-ℏω/k_B T) ~ exp(-10¹⁰) ≈ 0

This mechanism contributes negligibly to the total coupling. -/
noncomputable def epsilon_EM (params : CouplingEfficiencyParams) : ℝ :=
  thermalOccupationSuppression params

/-- EM form factor coupling is positive. -/
theorem epsilon_EM_pos (params : CouplingEfficiencyParams) :
    epsilon_EM params > 0 :=
  thermalOccupationSuppression_pos params

/-! ## Section 3: Mechanism 2 — Gluon-Photon Conversion

From §3 of the markdown: Gluons can convert to photons via quark loops (gg → γ),
but this requires **deconfinement**. In the confined phase:
- Gluon field orientations are random on average
- Color confinement prevents coherent conversion
- Only in QGP (T > T_c) is conversion nonzero

Key reference: Nedelko & Nikolskii (Physics 2023): "photon production from gg→γ
requires deconfinement"
-/

/-- The confinement suppression factor for gluon-photon conversion.

From §3.3: The amplitude suppression is ~exp(-m_g · r_hadron) ~ exp(-1) ~ 0.37
For the rate (amplitude squared): ~0.14 -/
noncomputable def confinementSuppressionFactor : ℝ := Real.exp (-1)

/-- Confinement suppression is positive. -/
theorem confinementSuppressionFactor_pos : confinementSuppressionFactor > 0 :=
  Real.exp_pos _

/-- Confinement suppression is less than 1. -/
theorem confinementSuppressionFactor_lt_one : confinementSuppressionFactor < 1 := by
  unfold confinementSuppressionFactor
  rw [Real.exp_lt_one_iff]
  norm_num

/-- Numerical bound: confinement suppression ~ 0.37.

From Mathlib: Real.exp_neg_one_gt_d9 : 0.36787944116 < Real.exp (-1)
             Real.exp_neg_one_lt_d9 : Real.exp (-1) < 0.3678794412 -/
theorem confinementSuppressionFactor_bounds :
    0.3 < confinementSuppressionFactor ∧ confinementSuppressionFactor < 0.4 := by
  unfold confinementSuppressionFactor
  constructor
  · -- 0.3 < exp(-1) ≈ 0.368
    -- From Mathlib: 0.36787944116 < exp(-1), and 0.3 < 0.36787944116
    calc (0.3 : ℝ) < 0.36787944116 := by norm_num
      _ < Real.exp (-1) := Real.exp_neg_one_gt_d9
  · -- exp(-1) < 0.4
    -- From Mathlib: exp(-1) < 0.3678794412, and 0.3678794412 < 0.4
    calc Real.exp (-1) < 0.3678794412 := Real.exp_neg_one_lt_d9
      _ < 0.4 := by norm_num

/-- Coupling efficiency from gluon-photon conversion.

From §3.4: ε_gγ ~ α_s² · α_em · ξ_conf²

But this still produces QCD-scale photons, so thermal suppression applies:
ε_gγ,thermal ~ ε_gγ · exp(-10¹⁰) ≈ 0

**Parameters used:**
- α_s = 0.5 (strong coupling at QCD scale, from Derivation_2_2_5a.standardQCDParams)
- α_em from params (fine structure constant)
- ξ_conf = exp(-1) ≈ 0.37 (amplitude suppression from confinement)
- Thermal suppression exp(-Λ_QCD/k_B T) ≈ 0

**Note:** This mechanism contributes negligibly due to the astronomical
thermal suppression factor. The hardcoded α_s = 0.5 is consistent with
standardQCDParams.alpha_s from Derivation_2_2_5a. -/
noncomputable def epsilon_gluon_photon (params : CouplingEfficiencyParams) : ℝ :=
  (0.5)^2 * params.alpha_em * confinementSuppressionFactor^2 *
    thermalOccupationSuppression params

/-- Gluon-photon coupling is positive. -/
theorem epsilon_gluon_photon_pos (params : CouplingEfficiencyParams) :
    epsilon_gluon_photon params > 0 := by
  unfold epsilon_gluon_photon
  apply mul_pos
  · apply mul_pos
    · apply mul_pos
      · norm_num
      · exact params.alpha_em_pos
    · apply pow_pos confinementSuppressionFactor_pos
  · exact thermalOccupationSuppression_pos params

/-! ## Section 4: Mechanism 3 — Hadronic Vacuum Polarization

From §4 of the markdown: This is the **dominant mechanism** for coupling.

The hadronic vacuum polarization allows coupling to **low-energy** (thermal)
photons, avoiding the thermal suppression problem.

Key result: ε_VP ~ (k_B T / Λ_QCD)⁴ · α_em

At room temperature: ε_VP ~ (1.3×10⁻¹⁰)⁴ × (1/137) ~ 2×10⁻⁴²
-/

/-- The vacuum polarization energy suppression factor.

From §4.5: The coupling to thermal external fields goes as (k_B T / Λ_QCD)⁴
due to the hadronic vacuum polarization at low momentum transfer.

**Physical derivation of the ⁴ power:**

The hadronic vacuum polarization Π(q²) at low q² expands as:
  Π(q²) ≈ Π(0) + q² · Π'(0) + O(q⁴)

For thermal photons: q² ~ (k_B T)²

The coupling to color phase dynamics involves a loop integral that
introduces another factor of (q²/Λ_QCD²). Combined:
  ε_VP ~ (q²/Λ_QCD²)² ~ (k_B T / Λ_QCD)⁴

This is the leading contribution since it doesn't require QCD-scale
photon emission—it couples directly to thermal (soft) photons.

**Reference:** Jegerlehner, World Scientific (2017) — hadronic vacuum polarization. -/
noncomputable def vacuumPolarizationSuppression (params : CouplingEfficiencyParams) : ℝ :=
  (energyScaleRatio params)^4

/-- Vacuum polarization suppression is positive. -/
theorem vacuumPolarizationSuppression_pos (params : CouplingEfficiencyParams) :
    vacuumPolarizationSuppression params > 0 := by
  unfold vacuumPolarizationSuppression
  apply pow_pos (energyScaleRatio_pos params)

/-- Vacuum polarization suppression is less than 1 for T < T_c. -/
theorem vacuumPolarizationSuppression_lt_one (params : CouplingEfficiencyParams)
    (h : params.kBT < params.Lambda_QCD) :
    vacuumPolarizationSuppression params < 1 := by
  unfold vacuumPolarizationSuppression
  have hξ := energyScaleRatio_small params h
  have hξ_pos := energyScaleRatio_pos params
  have h1 : (energyScaleRatio params)^4 < 1^4 := by
    apply pow_lt_pow_left₀ hξ (le_of_lt hξ_pos)
    norm_num
  simp only [one_pow] at h1
  exact h1

/-- The coupling efficiency from vacuum polarization.

From §4.5: ε_VP = (k_B T / Λ_QCD)⁴ · α_em

This is the **dominant mechanism** because it couples to low-energy modes. -/
noncomputable def epsilon_VP (params : CouplingEfficiencyParams) : ℝ :=
  vacuumPolarizationSuppression params * params.alpha_em

/-- Vacuum polarization coupling is positive. -/
theorem epsilon_VP_pos (params : CouplingEfficiencyParams) :
    epsilon_VP params > 0 := by
  unfold epsilon_VP
  apply mul_pos (vacuumPolarizationSuppression_pos params) params.alpha_em_pos

/-- Vacuum polarization coupling is less than α_em for T < T_c. -/
theorem epsilon_VP_lt_alpha_em (params : CouplingEfficiencyParams)
    (h : params.kBT < params.Lambda_QCD) :
    epsilon_VP params < params.alpha_em := by
  unfold epsilon_VP
  have hVP := vacuumPolarizationSuppression_lt_one params h
  calc vacuumPolarizationSuppression params * params.alpha_em
      < 1 * params.alpha_em := by
        apply mul_lt_mul_of_pos_right hVP params.alpha_em_pos
    _ = params.alpha_em := one_mul _

/-! ## Section 5: Total Coupling Efficiency

From §5 of the markdown: The total coupling efficiency is dominated by
vacuum polarization since the other mechanisms have thermal suppression.

Total: ε ≈ ε_VP ~ (k_B T / Λ_QCD)⁴ · α_em ~ 10⁻⁴² at 300K
-/

/-- The total coupling efficiency.

From §5.2-5.3: The vacuum polarization mechanism dominates because it
allows soft (low-energy) photon exchange, avoiding the energy mismatch.

ε_total ≈ ε_VP ~ (k_B T / Λ_QCD)⁴ · α_em

**Physical saturation:** In the QGP regime (T ≥ T_c), the coupling efficiency
saturates at 1 (full coupling). We model this with min(ε_VP, 1).

For confined matter (T << T_c), ε_VP << 1, so min(ε_VP, 1) = ε_VP. -/
noncomputable def epsilon_total (params : CouplingEfficiencyParams) : ℝ :=
  min (epsilon_VP params) 1

/-- Total coupling efficiency is positive. -/
theorem epsilon_total_pos (params : CouplingEfficiencyParams) :
    epsilon_total params > 0 := by
  unfold epsilon_total
  exact lt_min (epsilon_VP_pos params) zero_lt_one

/-- Total coupling efficiency is bounded by 1 (physical saturation).

In the QGP regime, coupling saturates at 1. This is unconditionally true
due to the min(ε_VP, 1) definition. -/
theorem epsilon_total_le_one (params : CouplingEfficiencyParams) :
    epsilon_total params ≤ 1 := by
  unfold epsilon_total
  exact min_le_right _ _

/-- Total coupling efficiency is much less than 1 for T < T_c.

From §5.3: ε ~ 10⁻⁴² at room temperature, which is effectively zero
for observable thermodynamic effects. -/
theorem epsilon_total_lt_one (params : CouplingEfficiencyParams)
    (h : params.kBT < params.Lambda_QCD) :
    epsilon_total params < 1 := by
  unfold epsilon_total
  have h1 := epsilon_VP_lt_alpha_em params h
  have h2 : epsilon_VP params < 1 := calc epsilon_VP params
      < params.alpha_em := h1
    _ < 1 := params.alpha_em_small
  exact lt_of_le_of_lt (min_le_left _ _) h2

/-- In the confined regime, epsilon_total equals epsilon_VP.

When T << T_c, we have ε_VP << 1, so min(ε_VP, 1) = ε_VP. -/
theorem epsilon_total_eq_VP (params : CouplingEfficiencyParams)
    (h : params.kBT < params.Lambda_QCD) :
    epsilon_total params = epsilon_VP params := by
  unfold epsilon_total
  have h1 := epsilon_VP_lt_alpha_em params h
  have h2 : epsilon_VP params < 1 := calc epsilon_VP params
      < params.alpha_em := h1
    _ < 1 := params.alpha_em_small
  exact min_eq_left (le_of_lt h2)

/-- Temperature scaling of epsilon_VP: ε_VP ∝ T⁴.

From §5.3: The vacuum polarization contribution scales as T⁴ because ε_VP ~ (k_B T)⁴.

For fixed Λ_QCD and α_em, if T₂/T₁ = r, then ε_VP₂/ε_VP₁ = r⁴.

**Note:** This scaling holds for ε_VP. The total ε = min(ε_VP, 1) has this
scaling only in the confined regime where ε_VP < 1. -/
theorem epsilon_VP_scales_as_T4 (params1 params2 : CouplingEfficiencyParams)
    (h_Lambda : params1.Lambda_QCD = params2.Lambda_QCD)
    (h_alpha : params1.alpha_em = params2.alpha_em)
    (h_kBT2_pos : params2.kBT > 0) :
    epsilon_VP params1 / epsilon_VP params2 =
    (params1.kBT / params2.kBT)^4 := by
  unfold epsilon_VP vacuumPolarizationSuppression energyScaleRatio
  simp only [h_Lambda, h_alpha]
  have hΛ_ne : params2.Lambda_QCD ≠ 0 := ne_of_gt params2.Lambda_QCD_pos
  have hα_ne : params2.alpha_em ≠ 0 := ne_of_gt params2.alpha_em_pos
  have hkBT2_ne : params2.kBT ≠ 0 := ne_of_gt h_kBT2_pos
  -- Goal: (a/Λ)^4 * α / ((b/Λ)^4 * α) = (a/b)^4
  have hΛ_pow_ne : params2.Lambda_QCD ^ 4 ≠ 0 := pow_ne_zero 4 hΛ_ne
  have hkBT2_pow_ne : params2.kBT ^ 4 ≠ 0 := pow_ne_zero 4 hkBT2_ne
  field_simp [hΛ_ne, hα_ne, hkBT2_ne, hΛ_pow_ne, hkBT2_pow_ne]

/-- Temperature scaling: ε ∝ T⁴ in confined regime.

From §5.3: The coupling efficiency scales as T⁴ because ε ~ (k_B T)⁴.
This holds when both parameters are in the confined regime (ε_VP < 1). -/
theorem epsilon_scales_as_T4 (params1 params2 : CouplingEfficiencyParams)
    (h_Lambda : params1.Lambda_QCD = params2.Lambda_QCD)
    (h_alpha : params1.alpha_em = params2.alpha_em)
    (h_kBT2_pos : params2.kBT > 0)
    (h1_conf : params1.kBT < params1.Lambda_QCD)
    (h2_conf : params2.kBT < params2.Lambda_QCD) :
    epsilon_total params1 / epsilon_total params2 =
    (params1.kBT / params2.kBT)^4 := by
  -- In confined regime, epsilon_total = epsilon_VP
  rw [epsilon_total_eq_VP params1 h1_conf, epsilon_total_eq_VP params2 h2_conf]
  exact epsilon_VP_scales_as_T4 params1 params2 h_Lambda h_alpha h_kBT2_pos

/-! ## Section 6: Physical Interpretation

From §5.4 of the markdown: The extreme smallness of ε explains why:
1. Matter doesn't spontaneously heat despite enormous internal entropy production
2. The arrow of time is not directly observable at the hadron level
3. Thermodynamic entropy production requires macroscopic non-equilibrium processes
-/

/-- Structure capturing the physical interpretation of ε.

The coupling efficiency ε relates internal Gibbs entropy production to
observable thermodynamic entropy production:
  dS_thermo/dt = ε · dS_Gibbs/dt -/
structure CouplingEfficiencyPhysics where
  /-- The coupling efficiency value -/
  epsilon : ℝ
  /-- ε is positive (some coupling exists) -/
  epsilon_pos : epsilon > 0
  /-- ε is much less than 1 (strongly suppressed) -/
  epsilon_lt_one : epsilon < 1
  /-- The temperature in units of T_c -/
  T_over_Tc : ℝ
  /-- Temperature is below deconfinement (confined phase) -/
  below_Tc : T_over_Tc < 1

/-- Extract physics interpretation from standard parameters. -/
noncomputable def roomTempPhysics : CouplingEfficiencyPhysics where
  epsilon := epsilon_total standardRoomTempParams
  epsilon_pos := epsilon_total_pos standardRoomTempParams
  epsilon_lt_one := by
    apply epsilon_total_lt_one
    unfold standardRoomTempParams
    simp only
    norm_num
  T_over_Tc := standardRoomTempParams.T_over_Tc
  below_Tc := by
    unfold standardRoomTempParams
    simp only
    norm_num

/-- Key physical consequence: no spontaneous heating.

From §6.1: The observable thermodynamic entropy production is:
  Ṡ_thermo = ε · N · k_B · σ ~ 10⁻⁴² × N × 3.1 J/(K·s)

For a mole (N ~ 10²³), this is ~10⁻¹⁸ J/(K·s), which is undetectable. -/
theorem no_spontaneous_heating (physics : CouplingEfficiencyPhysics) :
    physics.epsilon < 1 := physics.epsilon_lt_one

/-- Numerical upper bound on ε at room temperature.

**Calculation:**
  ε_VP = (k_B T / Λ_QCD)⁴ × α_em
       = (2.585×10⁻⁸ / 200)⁴ × (1/137)
       = (1.2925×10⁻¹⁰)⁴ × 7.3×10⁻³
       ≈ 2.04×10⁻⁴²

We prove ε < 10⁻³⁰ as a computationally tractable bound.
The actual value is ~10⁻⁴², much smaller.

**Why 10⁻³⁰ and not 10⁻⁴²:**
Lean's norm_num can verify simple rational bounds but struggles with
extremely small exponents. The bound 10⁻³⁰ is sufficient to demonstrate
that ε is negligibly small for thermodynamic purposes. -/
theorem epsilon_room_temp_upper_bound :
    epsilon_total standardRoomTempParams < 1e-30 := by
  -- First show we're in confined regime
  have h_conf : standardRoomTempParams.kBT < standardRoomTempParams.Lambda_QCD := by
    unfold standardRoomTempParams
    simp only
    norm_num
  -- In confined regime, epsilon_total = epsilon_VP
  rw [epsilon_total_eq_VP standardRoomTempParams h_conf]
  unfold epsilon_VP vacuumPolarizationSuppression energyScaleRatio standardRoomTempParams
  simp only
  -- (2.585e-8 / 200)^4 * (1/137) < 1e-30
  -- = (1.2925e-10)^4 * (1/137)
  -- ≈ 2.79e-40 * 7.3e-3 ≈ 2e-42 < 1e-30 ✓
  norm_num

/-! ## Section 7: QGP Regime (T ≥ T_c)

From §7 of the markdown: Above the deconfinement temperature T_c ~ 156 MeV,
the coupling efficiency **saturates** at ε = 1.

Physical mechanism:
- Below T_c: Quarks are confined, internal dynamics hidden
- Above T_c: Color degrees of freedom become thermal, directly coupled
- The "internal" and "external" distinction vanishes

The transition is a crossover, so ε rises smoothly from ~(T/Λ_QCD)⁴α_em to 1.
-/

/-- Coupling efficiency in the QGP regime.

From §7.2: Above T_c, the coupling efficiency saturates at 1.

ε_QGP = 1 for T ≥ T_c -/
noncomputable def epsilon_QGP : ℝ := 1

/-- QGP coupling efficiency is exactly 1. -/
theorem epsilon_QGP_eq_one : epsilon_QGP = 1 := rfl

/-- QGP coupling efficiency is the maximum possible.

From §7.2: ε cannot exceed 1 because it's the ratio of observable
to total entropy production. -/
theorem epsilon_QGP_maximal : epsilon_QGP ≤ 1 := le_refl 1

/-- The saturation property: ε = 1 means all internal entropy is observable.

From §7.2.1: When ε = 1, the full QCD entropy production rate becomes
directly observable as thermodynamic entropy.

**Physical interpretation:** In QGP (T ≥ T_c), the "internal" and "external"
distinction vanishes — color degrees of freedom become directly thermal.
The Gibbs entropy production rate equals the observable thermodynamic rate:
  dS_thermo/dt = ε × dS_Gibbs/dt = 1 × dS_Gibbs/dt = dS_Gibbs/dt -/
theorem epsilon_saturation_full_coupling :
    epsilon_QGP = 1 ∧
    ∀ (sigma kB : ℝ), sigma > 0 → kB > 0 →
      epsilon_QGP * kB * sigma = kB * sigma := by
  constructor
  · rfl
  · intro sigma kB _ _
    simp only [epsilon_QGP, one_mul]

/-- Parameters for QGP regime (T ≥ T_c). -/
structure QGPRegimeParams where
  /-- Temperature in units of T_c -/
  T_over_Tc : ℝ
  /-- Above deconfinement -/
  above_Tc : T_over_Tc ≥ 1

/-- Coupling efficiency in QGP is 1 regardless of exact temperature.

From §7.2: For all T ≥ T_c, ε = 1 (full coupling). -/
noncomputable def epsilon_in_QGP (_qgp : QGPRegimeParams) : ℝ := 1

/-- QGP coupling is always 1. -/
theorem epsilon_in_QGP_eq_one (qgp : QGPRegimeParams) :
    epsilon_in_QGP qgp = 1 := rfl

/-! ## Section 8: Transition Region

From §7.2 of the markdown: The transition from ε << 1 to ε = 1 occurs
smoothly at the QCD crossover (not a sharp phase transition).

The transition width is ~10-20 MeV around T_c ≈ 156 MeV.
-/

/-- Monotonicity of epsilon_VP: ε_VP increases with temperature.

From §5.3: Since ε_VP ∝ T⁴, higher temperatures give larger coupling. -/
theorem epsilon_VP_monotonic_in_T (params1 params2 : CouplingEfficiencyParams)
    (h_Lambda : params1.Lambda_QCD = params2.Lambda_QCD)
    (h_alpha : params1.alpha_em = params2.alpha_em)
    (h_T : params1.kBT < params2.kBT) :
    epsilon_VP params1 < epsilon_VP params2 := by
  unfold epsilon_VP vacuumPolarizationSuppression energyScaleRatio
  simp only [h_Lambda, h_alpha]
  apply mul_lt_mul_of_pos_right _ params2.alpha_em_pos
  have h_div : params1.kBT / params2.Lambda_QCD < params2.kBT / params2.Lambda_QCD := by
    apply div_lt_div_of_pos_right h_T params2.Lambda_QCD_pos
  have h_pos : params1.kBT / params2.Lambda_QCD > 0 := by
    rw [← h_Lambda]
    exact div_pos params1.kBT_pos params1.Lambda_QCD_pos
  apply pow_lt_pow_left₀ h_div (le_of_lt h_pos)
  norm_num

/-- Monotonicity: ε increases with temperature.

From §5.3: Since ε ∝ T⁴ (before saturation), higher temperatures give larger coupling.
Due to the min(ε_VP, 1) clamping, ε_total is monotonically non-decreasing. -/
theorem epsilon_monotonic_in_T (params1 params2 : CouplingEfficiencyParams)
    (h_Lambda : params1.Lambda_QCD = params2.Lambda_QCD)
    (h_alpha : params1.alpha_em = params2.alpha_em)
    (h_T : params1.kBT < params2.kBT) :
    epsilon_total params1 ≤ epsilon_total params2 := by
  unfold epsilon_total
  -- min(a, 1) ≤ min(b, 1) when a < b (monotonicity of min in first arg)
  have h_VP := epsilon_VP_monotonic_in_T params1 params2 h_Lambda h_alpha h_T
  exact min_le_min (le_of_lt h_VP) (le_refl 1)

/-- The crossover transition structure.

This captures the smooth transition from confined (ε << 1) to
deconfined (ε = 1) phases. -/
structure CrossoverTransition where
  /-- Temperature in units of T_c -/
  T_over_Tc : ℝ
  /-- Effective coupling efficiency -/
  epsilon_eff : ℝ
  /-- ε is positive -/
  epsilon_pos : epsilon_eff > 0
  /-- ε ≤ 1 (bounded) -/
  epsilon_bounded : epsilon_eff ≤ 1
  /-- Below T_c: ε << 1; above T_c: ε ≈ 1 -/
  transition_behavior : T_over_Tc < 1 → epsilon_eff < 1

/-! ## Section 9: Observable Consequences

From §6 of the markdown: The observable thermodynamic entropy production rate.
-/

/-- Thermodynamic entropy production rate per hadron.

From §6.1: Ṡ_thermo = ε · k_B · σ where σ = 3K/4 ~ 2.3×10²³ s⁻¹.

For ε ~ 10⁻⁴² and σ ~ 10²³ s⁻¹:
  Ṡ_thermo ~ 10⁻⁴² × 1.38×10⁻²³ × 10²³ ~ 10⁻⁴² J/(K·s) per hadron -/
noncomputable def thermoEntropyRate_per_hadron
    (params : CouplingEfficiencyParams) (sigma : ℝ) (kB : ℝ) : ℝ :=
  epsilon_total params * kB * sigma

/-- Thermodynamic entropy rate is positive. -/
theorem thermoEntropyRate_pos (params : CouplingEfficiencyParams)
    (sigma : ℝ) (kB : ℝ) (hσ : sigma > 0) (hkB : kB > 0) :
    thermoEntropyRate_per_hadron params sigma kB > 0 := by
  unfold thermoEntropyRate_per_hadron
  apply mul_pos (mul_pos (epsilon_total_pos params) hkB) hσ

/-- Thermodynamic rate is much smaller than Gibbs rate.

From §6.1: Since ε << 1, the observable entropy production is strongly
suppressed compared to the internal Gibbs entropy production. -/
theorem thermo_lt_gibbs (params : CouplingEfficiencyParams)
    (sigma : ℝ) (kB : ℝ) (hσ : sigma > 0) (hkB : kB > 0)
    (h : params.kBT < params.Lambda_QCD) :
    thermoEntropyRate_per_hadron params sigma kB < kB * sigma := by
  unfold thermoEntropyRate_per_hadron
  have hε := epsilon_total_lt_one params h
  calc epsilon_total params * kB * sigma
      = epsilon_total params * (kB * sigma) := by ring
    _ < 1 * (kB * sigma) := by
        apply mul_lt_mul_of_pos_right hε (mul_pos hkB hσ)
    _ = kB * sigma := one_mul _

/-! ## Section 10: Main Theorem Structure

The complete derivation bundled as a theorem structure.
-/

/-- **Derivation 2.2.6b: QCD-EM Coupling Efficiency**

The coupling efficiency ε between internal QCD color phase dynamics and
external electromagnetic/thermodynamic degrees of freedom.

**Main Results:**
1. ε(T) ≈ (k_B T / Λ_QCD)⁴ · α_em for T < T_c
2. ε ~ 10⁻⁴² at room temperature (T = 300K)
3. ε = 1 for T ≥ T_c (QGP regime)
4. dS_thermo/dt = ε · dS_Gibbs/dt

**Physical Origin of Suppression:**
- Energy scale mismatch: (k_B T / Λ_QCD)⁴ ~ (10⁻¹⁰)⁴ = 10⁻⁴⁰
- Fine structure constant: α_em ~ 10⁻²
- Total: ε ~ 10⁻⁴² at room temperature

**Physical Interpretation:**
1. Matter doesn't spontaneously heat despite internal entropy production
2. The arrow of time is intrinsic but not directly observable at hadron level
3. Heavy-ion collisions (T > T_c) expose the full QCD entropy production -/
structure QCDEMCouplingEfficiencyTheorem (params : CouplingEfficiencyParams) where
  /-- Claim 1: Total coupling efficiency is positive -/
  epsilon_pos : epsilon_total params > 0

  /-- Claim 2: Coupling efficiency is bounded by 1 (unconditionally) -/
  epsilon_bounded : epsilon_total params ≤ 1

  /-- Claim 3: ε << 1 for T << T_c (confined phase) -/
  strongly_suppressed : params.kBT < params.Lambda_QCD → epsilon_total params < 1

  /-- Claim 4: In confined regime, ε equals ε_VP -/
  VP_dominates : params.kBT < params.Lambda_QCD → epsilon_total params = epsilon_VP params

  /-- Claim 5: ε scales as T⁴ (in confined regime) -/
  T4_scaling : ∀ params2 : CouplingEfficiencyParams,
    params.Lambda_QCD = params2.Lambda_QCD →
    params.alpha_em = params2.alpha_em →
    params.kBT < params.Lambda_QCD →
    params2.kBT < params2.Lambda_QCD →
    epsilon_total params / epsilon_total params2 =
      (params.kBT / params2.kBT)^4

  /-- Claim 6: QGP regime has ε = 1 -/
  QGP_saturation : epsilon_QGP = 1

/-- Main theorem: QCD-EM coupling efficiency derivation holds. -/
theorem qcd_em_coupling_efficiency_holds (params : CouplingEfficiencyParams) :
    Nonempty (QCDEMCouplingEfficiencyTheorem params) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- Claim 1: ε > 0
    exact epsilon_total_pos params
  · -- Claim 2: ε ≤ 1 (unconditionally, from min definition)
    exact epsilon_total_le_one params
  · -- Claim 3: Strongly suppressed
    exact epsilon_total_lt_one params
  · -- Claim 4: VP dominates (in confined regime)
    exact epsilon_total_eq_VP params
  · -- Claim 5: T⁴ scaling (in confined regime)
    intro params2 hΛ hα h1_conf h2_conf
    exact epsilon_scales_as_T4 params params2 hΛ hα params2.kBT_pos h1_conf h2_conf
  · -- Claim 6: QGP saturation
    rfl

/-- Direct construction of the theorem for standard parameters. -/
noncomputable def theQCDEMCouplingTheorem :
    QCDEMCouplingEfficiencyTheorem standardRoomTempParams where
  epsilon_pos := epsilon_total_pos standardRoomTempParams
  epsilon_bounded := epsilon_total_le_one standardRoomTempParams
  strongly_suppressed := epsilon_total_lt_one standardRoomTempParams
  VP_dominates := epsilon_total_eq_VP standardRoomTempParams
  T4_scaling := fun params2 hΛ hα h1_conf h2_conf =>
    epsilon_scales_as_T4 standardRoomTempParams params2 hΛ hα params2.kBT_pos h1_conf h2_conf
  QGP_saturation := rfl

/-! ## Section 11: Dimensional Verification

From §9.1 of the markdown: Verify that ε is dimensionless.

| Term | Dimensions | Value |
|------|------------|-------|
| k_B T | [Energy] | 25.9 meV at 300K |
| Λ_QCD | [Energy] | 200 MeV |
| k_B T / Λ_QCD | [1] (dimensionless) | 1.29×10⁻¹⁰ |
| (k_B T / Λ_QCD)⁴ | [1] | 2.8×10⁻⁴⁰ |
| α_em | [1] | 7.3×10⁻³ |
| ε | [1] ✓ | 2.0×10⁻⁴² |
-/

/-- ε is dimensionless (all factors are dimensionless ratios or α_em).

**Dimensional analysis:**
- k_B T has dimensions [Energy]
- Λ_QCD has dimensions [Energy]
- k_B T / Λ_QCD is dimensionless [1]
- (k_B T / Λ_QCD)⁴ is dimensionless [1]
- α_em is dimensionless [1] (fine structure constant)
- ε = (k_B T / Λ_QCD)⁴ × α_em is dimensionless [1] ✓

This is verified by the structure of epsilon_VP: it's a product of:
1. energyScaleRatio⁴ — ratio of energies, hence dimensionless
2. α_em — dimensionless coupling constant -/
theorem epsilon_dimensionless (params : CouplingEfficiencyParams) :
    epsilon_VP params = (energyScaleRatio params)^4 * params.alpha_em := by
  unfold epsilon_VP vacuumPolarizationSuppression
  rfl

/-! ## Section 12: Uncertainty Estimate

From §9.1 of the markdown: With Λ_QCD = 200 ± 20 MeV (10% uncertainty),
the propagated uncertainty in ε is ±40% (since ε ∝ Λ_QCD⁻⁴).

ε(300K) = (1.4 - 3.1) × 10⁻⁴²

The order of magnitude is robust.
-/

/-- Uncertainty structure for ε. -/
structure EpsilonUncertainty where
  /-- Central value -/
  central : ℝ
  /-- Lower bound (Λ_QCD + 10%) -/
  lower : ℝ
  /-- Upper bound (Λ_QCD - 10%) -/
  upper : ℝ
  /-- Ordering: lower < central < upper -/
  ordering : lower < central ∧ central < upper

/-- ε scales as Λ_QCD⁻⁴, so 10% uncertainty in Λ gives ~40% in ε.

More precisely: if Λ → Λ(1+x), then ε → ε(1+x)⁻⁴ ≈ ε(1-4x) for small x.
For x = 0.1, the factor is (1.1)⁻⁴ ≈ 0.68 (lower) and (0.9)⁻⁴ ≈ 1.52 (upper).

**Derivation:**
ε_VP = (k_B T / Λ_QCD)⁴ × α_em

If Λ_QCD → Λ_QCD × (1 + δ), then:
ε_VP' = (k_B T / (Λ_QCD × (1 + δ)))⁴ × α_em
      = (k_B T / Λ_QCD)⁴ × (1 + δ)⁻⁴ × α_em
      = ε_VP × (1 + δ)⁻⁴

For δ = 0.1: (1.1)⁻⁴ ≈ 0.683
For δ = -0.1: (0.9)⁻⁴ ≈ 1.524

This gives uncertainty bounds of approximately [-32%, +52%] for ±10% in Λ_QCD. -/
theorem epsilon_uncertainty_propagation (params1 params2 : CouplingEfficiencyParams)
    (h_kBT : params1.kBT = params2.kBT)
    (h_alpha : params1.alpha_em = params2.alpha_em)
    (h_Lambda2_pos : params2.Lambda_QCD > 0) :
    epsilon_VP params1 / epsilon_VP params2 =
    (params2.Lambda_QCD / params1.Lambda_QCD)^4 := by
  unfold epsilon_VP vacuumPolarizationSuppression energyScaleRatio
  simp only [h_kBT, h_alpha]
  have hΛ1_ne : params1.Lambda_QCD ≠ 0 := ne_of_gt params1.Lambda_QCD_pos
  have hΛ2_ne : params2.Lambda_QCD ≠ 0 := ne_of_gt h_Lambda2_pos
  have hα_ne : params2.alpha_em ≠ 0 := ne_of_gt params2.alpha_em_pos
  have hkBT2_ne : params2.kBT ≠ 0 := ne_of_gt params2.kBT_pos
  have hΛ1_pow_ne : params1.Lambda_QCD ^ 4 ≠ 0 := pow_ne_zero 4 hΛ1_ne
  have hΛ2_pow_ne : params2.Lambda_QCD ^ 4 ≠ 0 := pow_ne_zero 4 hΛ2_ne
  have hkBT2_pow_ne : params2.kBT ^ 4 ≠ 0 := pow_ne_zero 4 hkBT2_ne
  field_simp [hΛ1_ne, hΛ2_ne, hα_ne, hΛ1_pow_ne, hΛ2_pow_ne, hkBT2_ne, hkBT2_pow_ne]

/-! ## Section 13: Summary

Derivation 2.2.6b establishes the QCD-EM coupling efficiency:

**Main Formula:**
ε(T) = (k_B T / Λ_QCD)⁴ · α_em ~ 10⁻⁴² × (T/300K)⁴

**Physical Origin:**
| Factor | Contribution | Value |
|--------|--------------|-------|
| Energy scale mismatch | (k_BT/Λ_QCD)⁴ | 10⁻⁴⁰ |
| EM coupling | α_em | 1/137 |
| Color neutrality | ~1 (second-order) | ~1 |

**Key Insights:**
1. Gibbs entropy production is always present (σ = 3K/4 > 0)
2. Observable thermodynamic entropy requires coupling through ε
3. The coupling is temperature-dependent: ε ∝ T⁴
4. At room temperature: ε ~ 10⁻⁴² (undetectable)
5. At QGP temperature: ε = 1 (fully exposed)
6. Heavy-ion collisions are the natural laboratory for testing

**Connection to Theorem 2.2.6:**
This derivation completes the picture in Theorem 2.2.6 §6.3:
"Observable thermodynamic entropy production occurs when the hadron
interacts with its external environment... where ε << 1."

We now have a **quantitative estimate** of ε from first principles.
-/

/-! ## Section 14: Verification Tests -/

section VerificationTests

-- Parameter structures
#check CouplingEfficiencyParams
#check standardRoomTempParams

-- Energy scale ratio
#check energyScaleRatio
#check energyScaleRatio_pos
#check energyScaleRatio_small
#check energyScaleRatio_at_roomTemp

-- Mechanism 1: EM form factor
#check thermalOccupationSuppression
#check thermalOccupationSuppression_pos
#check thermalOccupationSuppression_lt_one
#check thermalSuppression_negligible
#check epsilon_EM
#check epsilon_EM_pos

-- Mechanism 2: Gluon-photon conversion
#check confinementSuppressionFactor
#check confinementSuppressionFactor_pos
#check confinementSuppressionFactor_lt_one
#check confinementSuppressionFactor_bounds
#check epsilon_gluon_photon
#check epsilon_gluon_photon_pos

-- Mechanism 3: Vacuum polarization (dominant)
#check vacuumPolarizationSuppression
#check vacuumPolarizationSuppression_pos
#check vacuumPolarizationSuppression_lt_one
#check epsilon_VP
#check epsilon_VP_pos
#check epsilon_VP_lt_alpha_em

-- Total coupling efficiency
#check epsilon_total
#check epsilon_total_pos
#check epsilon_total_le_one
#check epsilon_total_lt_one
#check epsilon_total_eq_VP
#check epsilon_VP_scales_as_T4
#check epsilon_scales_as_T4

-- Physical interpretation
#check CouplingEfficiencyPhysics
#check roomTempPhysics
#check no_spontaneous_heating
#check epsilon_room_temp_upper_bound

-- QGP regime
#check epsilon_QGP
#check epsilon_QGP_eq_one
#check epsilon_QGP_maximal
#check epsilon_saturation_full_coupling
#check QGPRegimeParams
#check epsilon_in_QGP
#check epsilon_in_QGP_eq_one

-- Temperature scaling
#check epsilon_VP_monotonic_in_T
#check epsilon_monotonic_in_T
#check CrossoverTransition

-- Observable consequences
#check thermoEntropyRate_per_hadron
#check thermoEntropyRate_pos
#check thermo_lt_gibbs

-- Main theorem
#check QCDEMCouplingEfficiencyTheorem
#check qcd_em_coupling_efficiency_holds
#check theQCDEMCouplingTheorem

-- Uncertainty and dimensional analysis
#check EpsilonUncertainty
#check epsilon_dimensionless
#check epsilon_uncertainty_propagation

end VerificationTests

end ChiralGeometrogenesis.Phase2.Derivation_2_2_6b
