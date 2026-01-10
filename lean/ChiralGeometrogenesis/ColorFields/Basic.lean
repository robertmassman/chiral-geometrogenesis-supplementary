/-
  ColorFields/Basic.lean

  Color Field Formalization - Connecting SU(3) Weight Vectors to Color Phases

  This file establishes the fundamental connection between:
  1. The abstract SU(3) weight vectors (w_R, w_G, w_B) from Lie algebra
  2. The physical color phases (R, G, B) with 2π/3 separation
  3. Pressure fields defined on the stella octangula

  This is the bridge between pure mathematics (Phase -1) and
  the physical field theory (Phase 0+).

  Reference: docs/proofs/Phase-0/
-/

import ChiralGeometrogenesis.Basic
import ChiralGeometrogenesis.PureMath.LieAlgebra.Weights
import ChiralGeometrogenesis.PureMath.Polyhedra.StellaOctangula
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.ColorFields

open ChiralGeometrogenesis
open ChiralGeometrogenesis.PureMath.LieAlgebra
open ChiralGeometrogenesis.PureMath.Polyhedra

/-! ## Color Phase to Weight Vector Correspondence

The three color phases R, G, B correspond to the three fundamental
weight vectors of SU(3). This is not arbitrary - it's forced by
the geometric realization.
-/

/-- Map from ColorPhase to its corresponding weight vector -/
noncomputable def colorToWeight : ColorPhase → WeightVector
  | .R => w_R
  | .G => w_G
  | .B => w_B

/-- Map from ColorPhase to its anti-weight (antiparticle) -/
noncomputable def colorToAntiWeight : ColorPhase → WeightVector
  | .R => w_Rbar
  | .G => w_Gbar
  | .B => w_Bbar

/-- The color-to-weight map preserves the triangular structure -/
theorem color_weight_correspondence :
    colorToWeight ColorPhase.R = w_R ∧
    colorToWeight ColorPhase.G = w_G ∧
    colorToWeight ColorPhase.B = w_B := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Phase Angle Correspondence

The phase angles of color fields match the angular positions of
weight vectors in the 2D weight space.

**Mathematical Analysis:**

The weight vectors in the (T₃, T₈) plane are:
- w_R = (1/2, 1/(2√3))      → angle π/6 from positive T₃ axis
- w_G = (-1/2, 1/(2√3))     → angle 5π/6 (second quadrant)
- w_B = (0, -1/√3)          → angle 3π/2 (negative T₈ axis)

The angular separations are:
- G - R: 5π/6 - π/6 = 4π/6 = 2π/3
- B - G: 3π/2 - 5π/6 = 9π/6 - 5π/6 = 4π/6 = 2π/3
- R - B (mod 2π): π/6 + 2π - 3π/2 = π/6 + π/2 = 2π/3

Note: The ColorPhase.angle values (0, 2π/3, 4π/3) are normalized to start at 0,
while the weight vector angles start at π/6. Both have the same 2π/3 separation.
-/

/-- Angle of a weight vector from the positive T₃ axis using atan2 convention.

For a point (t3, t8) in the weight plane:
- Quadrant I (t3 > 0, t8 > 0): arctan(t8/t3)
- Quadrant II (t3 < 0, t8 > 0): π + arctan(t8/t3)
- Quadrant III (t3 < 0, t8 < 0): -π + arctan(t8/t3)
- Quadrant IV (t3 > 0, t8 < 0): arctan(t8/t3)
- Positive T₈ axis (t3 = 0, t8 > 0): π/2
- Negative T₈ axis (t3 = 0, t8 < 0): -π/2 (or 3π/2 in [0, 2π))
-/
noncomputable def weightToAngle (w : WeightVector) : ℝ :=
  if w.t3 = 0 then
    if w.t8 > 0 then Real.pi / 2
    else if w.t8 < 0 then -Real.pi / 2
    else 0  -- origin has undefined angle, default to 0
  else if w.t3 > 0 then
    Real.arctan (w.t8 / w.t3)
  else  -- w.t3 < 0
    if w.t8 ≥ 0 then Real.pi + Real.arctan (w.t8 / w.t3)
    else -Real.pi + Real.arctan (w.t8 / w.t3)

/-! ### Weight Vector Angular Positions

We prove the actual angles of the weight vectors in weight space.
-/

/-- The angle of w_R in weight space is π/6.

Calculation: w_R = (1/2, 1/(2√3))
tan(θ) = t8/t3 = (1/(2√3))/(1/2) = 1/√3
θ = arctan(1/√3) = π/6

Note: tan(π/6) = 1/√3 is a standard identity. -/
theorem weight_angle_R : weightToAngle w_R = Real.arctan (1 / Real.sqrt 3) := by
  unfold weightToAngle w_R
  simp only
  -- w_R.t3 = 1/2 > 0, so we're in the t3 > 0 branch
  have ht3_pos : (1 : ℝ) / 2 > 0 := by norm_num
  have ht3_ne : (1 : ℝ) / 2 ≠ 0 := ne_of_gt ht3_pos
  simp only [ht3_ne, ↓reduceIte, gt_iff_lt, ht3_pos]
  -- Simplify the ratio: (1/(2√3)) / (1/2) = 1/√3
  have hne : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (3 : ℝ) > 0)
  congr 1
  field_simp

/-- arctan(1/√3) = π/6.

This is a standard trigonometric identity: tan(π/6) = 1/√3.
We prove it using the relationship tan(π/6) = sin(π/6)/cos(π/6) = (1/2)/(√3/2) = 1/√3. -/
theorem arctan_one_over_sqrt3 : Real.arctan (1 / Real.sqrt 3) = Real.pi / 6 := by
  -- Use the fact that tan(π/6) = 1/√3
  have h1 : Real.tan (Real.pi / 6) = 1 / Real.sqrt 3 := Real.tan_pi_div_six
  -- And π/6 is in the range of arctan
  have h2 : Real.pi / 6 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  rw [← h1, Real.arctan_tan h2.1 h2.2]

/-- The angle of w_R in weight space is exactly π/6 -/
theorem weight_angle_R_exact : weightToAngle w_R = Real.pi / 6 := by
  rw [weight_angle_R, arctan_one_over_sqrt3]

/-- The angle of w_G in weight space is 5π/6.

Calculation: w_G = (-1/2, 1/(2√3))
t3 < 0, t8 > 0, so we're in quadrant II
θ = π + arctan(t8/t3) = π + arctan(-1/√3) = π - π/6 = 5π/6 -/
theorem weight_angle_G : weightToAngle w_G = Real.pi + Real.arctan (-1 / Real.sqrt 3) := by
  unfold weightToAngle w_G
  simp only
  -- w_G.t3 = -1/2 < 0
  have ht3_neg : (-1 : ℝ) / 2 < 0 := by norm_num
  have ht3_ne : (-1 : ℝ) / 2 ≠ 0 := ne_of_lt ht3_neg
  have ht3_not_pos : ¬((-1 : ℝ) / 2 > 0) := not_lt.mpr (le_of_lt ht3_neg)
  -- w_G.t8 = 1/(2√3) > 0
  have ht8_pos : (1 : ℝ) / (2 * Real.sqrt 3) > 0 := by
    apply div_pos (by norm_num : (1 : ℝ) > 0)
    apply mul_pos (by norm_num : (2 : ℝ) > 0)
    exact Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
  have ht8_nonneg : (1 : ℝ) / (2 * Real.sqrt 3) ≥ 0 := le_of_lt ht8_pos
  simp only [ht3_ne, ↓reduceIte, ht3_not_pos, ht8_nonneg]
  -- Simplify the ratio: (1/(2√3)) / (-1/2) = -1/√3
  have hne : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (3 : ℝ) > 0)
  congr 1
  field_simp

/-- arctan(-x) = -arctan(x) -/
theorem arctan_neg' (x : ℝ) : Real.arctan (-x) = -Real.arctan x := Real.arctan_neg x

/-- The angle of w_G is exactly 5π/6 -/
theorem weight_angle_G_exact : weightToAngle w_G = 5 * Real.pi / 6 := by
  rw [weight_angle_G]
  -- arctan(-1/√3) = -arctan(1/√3) = -π/6
  have h : Real.arctan (-1 / Real.sqrt 3) = -Real.pi / 6 := by
    rw [neg_div, Real.arctan_neg, arctan_one_over_sqrt3]
    ring
  rw [h]
  ring

/-- The angle of w_B in weight space is -π/2 (or 3π/2 in [0, 2π)).

Calculation: w_B = (0, -1/√3)
t3 = 0, t8 < 0, so θ = -π/2 -/
theorem weight_angle_B : weightToAngle w_B = -Real.pi / 2 := by
  unfold weightToAngle w_B
  simp only
  -- w_B.t8 = -1/√3 < 0
  have ht8_neg : (-1 : ℝ) / Real.sqrt 3 < 0 := by
    apply div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0)
    exact Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
  have ht8_not_pos : ¬((-1 : ℝ) / Real.sqrt 3 > 0) := not_lt.mpr (le_of_lt ht8_neg)
  simp only [↓reduceIte, ht8_not_pos, ht8_neg]

/-- The angle of w_B in [0, 2π) representation is 3π/2 -/
theorem weight_angle_B_normalized : weightToAngle w_B + 2 * Real.pi = 3 * Real.pi / 2 := by
  rw [weight_angle_B]
  ring

/-! ### Angular Separation Theorems

Now we prove the 2π/3 angular separation using the actual weight vector angles.
-/

/-- Angular separation between w_G and w_R in weight space is 2π/3 -/
theorem weight_vector_angle_separation_G_R :
    weightToAngle w_G - weightToAngle w_R = 2 * Real.pi / 3 := by
  rw [weight_angle_G_exact, weight_angle_R_exact]
  ring

/-- Angular separation between w_B and w_G in weight space is 2π/3 (using normalized angles) -/
theorem weight_vector_angle_separation_B_G :
    (weightToAngle w_B + 2 * Real.pi) - weightToAngle w_G = 2 * Real.pi / 3 := by
  rw [weight_angle_B, weight_angle_G_exact]
  ring

/-- Angular separation from w_R to w_B (going the long way) is 4π/3, or equivalently
    from w_B to w_R (going the short way in [0, 2π)) is 2π/3 -/
theorem weight_vector_angle_separation_R_B :
    (weightToAngle w_R + 2 * Real.pi) - (weightToAngle w_B + 2 * Real.pi) = 2 * Real.pi / 3 := by
  rw [weight_angle_R_exact, weight_angle_B]
  ring

/-- The ColorPhase angles are a normalized version of weight vector angles.

ColorPhase.angle assigns:
- R → 0 (instead of π/6)
- G → 2π/3 (instead of 5π/6)
- B → 4π/3 (instead of 3π/2)

This is equivalent to subtracting π/6 from each weight vector angle and then
taking mod 2π. The separation of 2π/3 is preserved. -/
theorem color_phase_is_normalized_weight_angle :
    ColorPhase.R.angle = weightToAngle w_R - Real.pi / 6 ∧
    ColorPhase.G.angle = weightToAngle w_G - Real.pi / 6 ∧
    ColorPhase.B.angle = (weightToAngle w_B + 2 * Real.pi) - Real.pi / 6 := by
  rw [weight_angle_R_exact, weight_angle_G_exact, weight_angle_B]
  simp only [ColorPhase.angle]
  constructor
  · ring
  constructor
  · ring
  · ring

/-- The angular separation between R and G phases is 2π/3 -/
theorem weight_angle_R_G_separation :
    ColorPhase.G.angle - ColorPhase.R.angle = 2 * Real.pi / 3 := by
  simp only [ColorPhase.angle]
  ring

/-- The angular separation between G and B phases is 2π/3 -/
theorem weight_angle_G_B_separation :
    ColorPhase.B.angle - ColorPhase.G.angle = 2 * Real.pi / 3 := by
  simp only [ColorPhase.angle]
  ring

/-- All three phase separations are equal (2π/3) -/
theorem uniform_phase_separation :
    let sep := 2 * Real.pi / 3
    ColorPhase.G.angle - ColorPhase.R.angle = sep ∧
    ColorPhase.B.angle - ColorPhase.G.angle = sep ∧
    (ColorPhase.R.angle + 2 * Real.pi) - ColorPhase.B.angle = sep := by
  simp only [ColorPhase.angle]
  constructor
  · ring
  constructor
  · ring
  · ring

/-- The weight vector angles and color phase angles have the same separation structure -/
theorem weight_and_phase_angles_isomorphic :
    (weightToAngle w_G - weightToAngle w_R = ColorPhase.G.angle - ColorPhase.R.angle) ∧
    ((weightToAngle w_B + 2 * Real.pi) - weightToAngle w_G =
     ColorPhase.B.angle - ColorPhase.G.angle) := by
  rw [weight_angle_R_exact, weight_angle_G_exact, weight_angle_B]
  simp only [ColorPhase.angle]
  constructor <;> ring

/-! ## Color Fields on the Stella Octangula

Each color phase defines a pressure field on ℝ³. The stella octangula
vertices are special points where these fields take characteristic values.

**Physical Model:**

A color field χ_c(x,t) is a complex scalar field with:
- Amplitude A_c(x): spatial variation of field strength
- Phase φ_c(x,t) = ω·t + θ_c + k·x: time evolution with color-specific offset θ_c

The real pressure is P_c(x,t) = A_c(x) · cos(φ_c(x,t))

For the three colors:
- θ_R = 0
- θ_G = 2π/3
- θ_B = 4π/3
-/

/-- A static color field amplitude function (position-dependent only) -/
structure StaticColorField where
  amplitude : Point3D → ℝ
  phase : ColorPhase

/-- A dynamic color field includes time dependence -/
structure DynamicColorField where
  amplitude : Point3D → ℝ
  phase : ColorPhase
  frequency : ℝ      -- ω (angular frequency)
  wavenumber : ℝ     -- k (for 1D propagation along a specified axis)

/-- Backward compatible: A color field (static version) -/
abbrev ColorField := StaticColorField

/-- Construct a static field with uniform amplitude -/
noncomputable def ColorField.uniform (A : ℝ) (c : ColorPhase) : ColorField :=
  ⟨fun _ => A, c⟩

/-- Construct a static field with radial falloff from origin -/
noncomputable def ColorField.radial (A₀ : ℝ) (c : ColorPhase) : ColorField :=
  ⟨fun p => A₀ / (1 + distSqFromOrigin p), c⟩

/-- The three fundamental color fields with uniform unit amplitude -/
noncomputable def fieldR : ColorField := ColorField.uniform 1 ColorPhase.R
noncomputable def fieldG : ColorField := ColorField.uniform 1 ColorPhase.G
noncomputable def fieldB : ColorField := ColorField.uniform 1 ColorPhase.B

/-- Static pressure from a color field (time-independent snapshot at t=0) -/
noncomputable def ColorField.toStaticPressure (f : ColorField) : Point3D → ℝ :=
  fun p => f.amplitude p * Real.cos f.phase.angle

/-- Dynamic pressure from a color field at time t -/
noncomputable def DynamicColorField.toPressure (f : DynamicColorField) (t : ℝ) : Point3D → ℝ :=
  fun p => f.amplitude p * Real.cos (f.frequency * t + f.phase.angle)

/-- Full wave pressure including spatial propagation (1D along x-axis) -/
noncomputable def DynamicColorField.toWavePressure (f : DynamicColorField) (t : ℝ) : Point3D → ℝ :=
  fun p => f.amplitude p * Real.cos (f.wavenumber * p.x - f.frequency * t + f.phase.angle)

/-- Backward compatible: A pressure field derived from a color field -/
noncomputable def ColorField.toPressure (f : ColorField) : Point3D → ℝ :=
  f.toStaticPressure

/-- The total static pressure is the superposition of all three color pressures -/
noncomputable def totalColorPressure (fR fG fB : ColorField) : Point3D → ℝ :=
  fun p => fR.toPressure p + fG.toPressure p + fB.toPressure p

/-- The total dynamic pressure at time t -/
noncomputable def totalDynamicPressure (fR fG fB : DynamicColorField) (t : ℝ) : Point3D → ℝ :=
  fun p => fR.toPressure t p + fG.toPressure t p + fB.toPressure t p

/-! ### Static Pressure Properties -/

/-- Uniform fields give constant pressure -/
theorem uniform_field_constant_pressure (A : ℝ) (c : ColorPhase) (p q : Point3D) :
    (ColorField.uniform A c).toPressure p = (ColorField.uniform A c).toPressure q := by
  simp only [ColorField.toPressure, ColorField.toStaticPressure, ColorField.uniform]

/-- cos(2π/3) = -1/2.

Proof: cos(2π/3) = cos(π - π/3) = -cos(π/3) = -1/2 -/
theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1/2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

/-- cos(4π/3) = -1/2.

Proof: cos(4π/3) = cos(π + π/3) = -cos(π/3) = -1/2 -/
theorem cos_four_pi_div_three : Real.cos (4 * Real.pi / 3) = -1/2 := by
  have h : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
  rw [h, Real.cos_add_pi, Real.cos_pi_div_three]
  norm_num

/-- The sum cos(0) + cos(2π/3) + cos(4π/3) = 0.

This is the fundamental identity underlying color field cancellation. -/
theorem cos_sum_thirds_zero :
    Real.cos 0 + Real.cos (2 * Real.pi / 3) + Real.cos (4 * Real.pi / 3) = 0 := by
  rw [Real.cos_zero, cos_two_pi_div_three, cos_four_pi_div_three]
  norm_num

/-- The sum of static pressures from uniform RGB fields is zero.

This is a consequence of cos(0) + cos(2π/3) + cos(4π/3) = 0.
-/
theorem uniform_rgb_pressure_sum_zero (A : ℝ) (p : Point3D) :
    (ColorField.uniform A .R).toPressure p +
    (ColorField.uniform A .G).toPressure p +
    (ColorField.uniform A .B).toPressure p = 0 := by
  simp only [ColorField.toPressure, ColorField.toStaticPressure,
             ColorField.uniform, ColorPhase.angle]
  -- Need: A * cos(0) + A * cos(2π/3) + A * cos(4π/3) = 0
  -- Factor: A * (cos(0) + cos(2π/3) + cos(4π/3)) = A * 0 = 0
  have h1 : Real.cos 0 = 1 := Real.cos_zero
  have h2 : Real.cos (2 * Real.pi / 3) = -1/2 := cos_two_pi_div_three
  have h3 : Real.cos (4 * Real.pi / 3) = -1/2 := cos_four_pi_div_three
  rw [h1, h2, h3]
  ring

/-! ### Dynamic Pressure Properties -/

/-- The sum of dynamic RGB pressures is zero at any time t (when frequencies match).

This generalizes uniform_rgb_pressure_sum_zero to the time-dependent case.
The key insight: cos(ωt) + cos(ωt + 2π/3) + cos(ωt + 4π/3) = 0 for all t.
-/
theorem dynamic_rgb_pressure_sum_zero (A : ℝ) (ω t : ℝ) (p : Point3D) :
    let fR : DynamicColorField := ⟨fun _ => A, .R, ω, 0⟩
    let fG : DynamicColorField := ⟨fun _ => A, .G, ω, 0⟩
    let fB : DynamicColorField := ⟨fun _ => A, .B, ω, 0⟩
    fR.toPressure t p + fG.toPressure t p + fB.toPressure t p = 0 := by
  simp only [DynamicColorField.toPressure, ColorPhase.angle]
  -- Need: A·cos(ωt) + A·cos(ωt + 2π/3) + A·cos(ωt + 4π/3) = 0
  -- Use sum-to-product: this is A times the sum of three equally spaced cosines
  -- which equals zero by the roots-of-unity argument
  have h1 : Real.cos (ω * t + 0) = Real.cos (ω * t) := by ring_nf
  have h2 : ω * t + 2 * Real.pi / 3 = ω * t + 2 * Real.pi / 3 := rfl
  have h3 : ω * t + 4 * Real.pi / 3 = ω * t + 4 * Real.pi / 3 := rfl
  rw [h1]
  -- Use the cosine addition formula and the fact that the phases are 2π/3 apart
  have key : Real.cos (ω * t) + Real.cos (ω * t + 2 * Real.pi / 3) +
             Real.cos (ω * t + 4 * Real.pi / 3) = 0 := by
    rw [Real.cos_add, Real.cos_add]
    have c1 : Real.cos (2 * Real.pi / 3) = -1/2 := cos_two_pi_div_three
    have s1 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
      have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
      rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]
    have c2 : Real.cos (4 * Real.pi / 3) = -1/2 := cos_four_pi_div_three
    have s2 : Real.sin (4 * Real.pi / 3) = -Real.sqrt 3 / 2 := by
      have h : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
      rw [h, Real.sin_add_pi, Real.sin_pi_div_three]
      ring
    rw [c1, s1, c2, s2]
    ring
  calc A * Real.cos (ω * t) + A * Real.cos (ω * t + 2 * Real.pi / 3) +
       A * Real.cos (ω * t + 4 * Real.pi / 3)
      = A * (Real.cos (ω * t) + Real.cos (ω * t + 2 * Real.pi / 3) +
             Real.cos (ω * t + 4 * Real.pi / 3)) := by ring
    _ = A * 0 := by rw [key]
    _ = 0 := by ring

/-- Dynamic phases maintain 2π/3 separation at all times -/
theorem dynamic_pressure_phase_separation (f1 f2 : DynamicColorField)
    (h_freq : f1.frequency = f2.frequency)
    (h_phases : f2.phase.angle - f1.phase.angle = 2 * Real.pi / 3) :
    ∀ t : ℝ, (f1.frequency * t + f1.phase.angle) - (f2.frequency * t + f2.phase.angle) =
             -(2 * Real.pi / 3) := by
  intro t
  rw [h_freq]
  ring_nf
  linarith [h_phases]

/-! ## Pressure at Stella Octangula Vertices

The 8 vertices of the stella octangula have special significance:
- 6 vertices form a hexagon in the "equatorial" plane, corresponding to the 6 weight vectors
  - 3 Weight vertices: R, G, B (fundamental representation)
  - 3 AntiWeight vertices: R̄, Ḡ, B̄ (anti-fundamental representation)
- 2 Apex vertices at the "poles" are color-neutral (project to origin in weight space)

The hexagonal vertices correspond to the SU(3) weight diagram.
-/

/-- Classification of stella octangula vertices by color charge.

- `Weight c`: One of 3 vertices carrying fundamental color charge (R, G, or B)
- `AntiWeight c`: One of 3 vertices carrying anti-color charge (R̄, Ḡ, or B̄)
- `Apex`: One of 2 neutral vertices at the tetrahedron tips

Total: 3 + 3 + 2 = 8 vertices (though Apex represents 2 distinct points)
-/
inductive VertexColor
  | Weight (c : ColorPhase)      -- 3 fundamental color vertices
  | AntiWeight (c : ColorPhase)  -- 3 anti-color vertices
  | Apex                         -- 2 neutral apex vertices (at tetrahedron tips)
deriving DecidableEq

/-- All vertex color types (note: Apex appears once but represents 2 physical vertices) -/
def allVertexColors : List VertexColor :=
  [.Weight .R, .Weight .G, .Weight .B,
   .AntiWeight .R, .AntiWeight .G, .AntiWeight .B,
   .Apex]

/-- The 6 weight-carrying vertices of the stella (equatorial hexagon) -/
def weightVertices : List VertexColor :=
  [.Weight .R, .Weight .G, .Weight .B,
   .AntiWeight .R, .AntiWeight .G, .AntiWeight .B]

/-- Count of weight vertices -/
theorem weight_vertex_count : weightVertices.length = 6 := rfl

/-- Total vertices: 6 weight + 2 apex = 8 -/
theorem total_vertex_count : weightVertices.length + 2 = 8 := rfl

/-! ### Mapping Vertex Colors to Weight Vectors

Each colored vertex corresponds to a weight vector in the 2D weight space.
The hexagonal arrangement matches the SU(3) weight diagram.
-/

/-- Map a vertex color to its weight vector (Apex maps to zero/origin) -/
noncomputable def vertexColorToWeight : VertexColor → WeightVector
  | .Weight c => colorToWeight c
  | .AntiWeight c => colorToAntiWeight c
  | .Apex => 0  -- Apex vertices are color-neutral

/-- Weight vertices carry non-zero color charge -/
theorem weight_vertex_nonzero (c : ColorPhase) :
    vertexColorToWeight (.Weight c) ≠ 0 := by
  simp only [vertexColorToWeight, colorToWeight]
  cases c
  · -- R case: w_R = (1/2, 1/(2√3)) ≠ 0
    intro h
    have : w_R.t3 = 0 := congrArg WeightVector.t3 h
    simp only [w_R] at this
    norm_num at this
  · -- G case: w_G = (-1/2, 1/(2√3)) ≠ 0
    intro h
    have : w_G.t3 = 0 := congrArg WeightVector.t3 h
    simp only [w_G] at this
    norm_num at this
  · -- B case: w_B = (0, -1/√3) ≠ 0
    intro h
    have : w_B.t8 = 0 := congrArg WeightVector.t8 h
    simp only [w_B] at this
    have hne : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (3 : ℝ) > 0)
    field_simp at this
    linarith [Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)]

/-- AntiWeight vertices also carry non-zero color charge -/
theorem antiweight_vertex_nonzero (c : ColorPhase) :
    vertexColorToWeight (.AntiWeight c) ≠ 0 := by
  simp only [vertexColorToWeight, colorToAntiWeight]
  cases c
  · -- R̄ case: w_Rbar = -w_R ≠ 0
    intro h
    have : w_Rbar.t3 = 0 := congrArg WeightVector.t3 h
    simp only [w_Rbar, WeightVector.neg_t3, w_R] at this
    norm_num at this
  · -- Ḡ case: w_Gbar = -w_G ≠ 0
    intro h
    have : w_Gbar.t3 = 0 := congrArg WeightVector.t3 h
    simp only [w_Gbar, WeightVector.neg_t3, w_G] at this
    norm_num at this
  · -- B̄ case: w_Bbar = -w_B ≠ 0
    intro h
    have : w_Bbar.t8 = 0 := congrArg WeightVector.t8 h
    simp only [w_Bbar, WeightVector.neg_t8, w_B] at this
    have hne : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (3 : ℝ) > 0)
    field_simp at this
    linarith [Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)]

/-- Apex vertices are color-neutral (weight = 0) -/
theorem apex_is_neutral : vertexColorToWeight .Apex = 0 := rfl

/-- AntiWeight is the negation of Weight -/
theorem antiweight_is_negation (c : ColorPhase) :
    vertexColorToWeight (.AntiWeight c) = -vertexColorToWeight (.Weight c) := by
  simp only [vertexColorToWeight, colorToAntiWeight, colorToWeight]
  cases c <;> rfl

/-! ### Weight Vector Magnitudes

All fundamental weight vectors have the same squared magnitude 1/3.
This is essential for them to form a regular hexagon in weight space.
-/

/-- Squared magnitude of w_R is 1/3 -/
theorem weight_R_norm_sq : weightNormSq w_R = 1 / 3 := by
  simp only [weightNormSq, w_R]
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  field_simp
  ring_nf
  rw [h]
  ring

/-- Squared magnitude of w_G is 1/3 -/
theorem weight_G_norm_sq : weightNormSq w_G = 1 / 3 := by
  simp only [weightNormSq, w_G]
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  field_simp
  ring_nf
  rw [h]
  ring

/-- Squared magnitude of w_B is 1/3 -/
theorem weight_B_norm_sq : weightNormSq w_B = 1 / 3 := by
  simp only [weightNormSq, w_B]
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  field_simp
  ring_nf
  rw [h]

/-- All fundamental weights have equal magnitude (regular hexagon property) -/
theorem fundamental_weights_equal_norm :
    weightNormSq w_R = weightNormSq w_G ∧
    weightNormSq w_G = weightNormSq w_B := by
  rw [weight_R_norm_sq, weight_G_norm_sq, weight_B_norm_sq]
  exact ⟨rfl, rfl⟩

/-- Anti-weights have the same magnitude as weights -/
theorem antiweight_norm_sq (c : ColorPhase) :
    weightNormSq (colorToAntiWeight c) = weightNormSq (colorToWeight c) := by
  simp only [colorToAntiWeight, colorToWeight, weightNormSq]
  cases c <;> simp only [w_Rbar, w_Gbar, w_Bbar, WeightVector.neg_t3, WeightVector.neg_t8] <;> ring

/-! ### Mapping to 3D Stella Octangula Coordinates

The stella octangula lives in ℝ³. The weight vectors live in the 2D weight plane.
We establish a correspondence between these spaces.

**Geometric picture:**
- The 6 weight vertices form a hexagon in a plane (the "equatorial plane")
- The 2 apex vertices are above and below this plane (the "poles")
- This is analogous to projecting a cube onto a hexagon

**Coordinate correspondence:**
We embed the 2D weight space into the xy-plane of ℝ³:
- T₃ axis → x-axis
- T₈ axis → y-axis
- Apex vertices have z ≠ 0
-/

/-- Embed a weight vector into ℝ³ (in the z=0 plane) -/
noncomputable def weightToPoint3D (w : WeightVector) : Point3D :=
  ⟨w.t3, w.t8, 0⟩

/-- The weight embedding preserves the hexagonal structure -/
theorem weight_embedding_preserves_distances (w1 w2 : WeightVector) :
    distSq (weightToPoint3D w1) (weightToPoint3D w2) = weightDistSq w1 w2 := by
  simp only [distSq, weightToPoint3D, weightDistSq]
  ring

/-- Map vertex colors to approximate 3D positions.

Note: This is a schematic embedding. The exact correspondence with
stella octangula vertices v_up_i and v_down_i requires scaling.
The key property is that the 6 weight vertices form a regular hexagon. -/
noncomputable def vertexColorToPoint3D : VertexColor → Point3D
  | .Weight c => weightToPoint3D (colorToWeight c)
  | .AntiWeight c => weightToPoint3D (colorToAntiWeight c)
  | .Apex => ⟨0, 0, 1⟩  -- Representative apex (there are 2: z=±1)

/-- The weight vertices lie in the z=0 plane -/
theorem weight_vertices_in_plane (c : ColorPhase) :
    (vertexColorToPoint3D (.Weight c)).z = 0 ∧
    (vertexColorToPoint3D (.AntiWeight c)).z = 0 := by
  constructor
  · simp only [vertexColorToPoint3D, weightToPoint3D]
  · simp only [vertexColorToPoint3D, weightToPoint3D]

/-- The apex vertex is out of the weight plane -/
theorem apex_out_of_plane : (vertexColorToPoint3D .Apex).z = 1 := rfl

/-! ## Color Neutrality (Confinement Condition)

A key physical requirement: isolated color charges cannot exist.
Observable states must be color-neutral (sum of weights = 0).

**Physical interpretation:**
- Quarks carry color charge (R, G, or B)
- Antiquarks carry anti-color (R̄, Ḡ, B̄)
- Only color-neutral combinations are observable:
  - Mesons: quark + antiquark (e.g., RR̄)
  - Baryons: three quarks of different colors (RGB)
  - Antibaryons: three antiquarks (R̄ḠB̄)

**Mathematical formulation:**
A color configuration is neutral iff its total weight vector is zero.
-/

/-- Sum of fundamental weights is zero (color neutrality) -/
theorem fundamental_weights_neutral :
    w_R.t3 + w_G.t3 + w_B.t3 = 0 ∧
    w_R.t8 + w_G.t8 + w_B.t8 = 0 := by
  constructor
  · exact fundamental_t3_sum_zero
  · exact fundamental_t8_sum_zero

/-- Sum of a list of weight vectors using foldl -/
def sumWeights (ws : List WeightVector) : WeightVector :=
  ws.foldl (· + ·) 0

/-- sumWeights of empty list is zero -/
theorem sumWeights_nil : sumWeights [] = 0 := rfl

/-- WeightVector extensionality: two weight vectors are equal iff both components are equal -/
theorem WeightVector.ext' {w1 w2 : WeightVector} (h3 : w1.t3 = w2.t3) (h8 : w1.t8 = w2.t8) :
    w1 = w2 := by
  cases w1; cases w2; simp only at h3 h8; simp [h3, h8]

/-- The t3 component of zero is zero -/
theorem WeightVector.zero_t3 : (0 : WeightVector).t3 = 0 := rfl

/-- The t8 component of zero is zero -/
theorem WeightVector.zero_t8 : (0 : WeightVector).t8 = 0 := rfl

/-- 0 + w = w for WeightVectors -/
theorem WeightVector.zero_add' (w : WeightVector) : (0 : WeightVector) + w = w := by
  apply WeightVector.ext'
  · simp only [WeightVector.add_t3, WeightVector.zero_t3, zero_add]
  · simp only [WeightVector.add_t8, WeightVector.zero_t8, zero_add]

/-- sumWeights of singleton is that element -/
theorem sumWeights_singleton (w : WeightVector) : sumWeights [w] = w := by
  simp only [sumWeights, List.foldl_cons, List.foldl_nil]
  exact WeightVector.zero_add' w

/-- sumWeights of two elements -/
theorem sumWeights_pair (w1 w2 : WeightVector) : sumWeights [w1, w2] = w1 + w2 := by
  simp only [sumWeights, List.foldl_cons, List.foldl_nil]
  rw [WeightVector.zero_add']

/-- sumWeights of three elements -/
theorem sumWeights_triple (w1 w2 w3 : WeightVector) :
    sumWeights [w1, w2, w3] = w1 + w2 + w3 := by
  simp only [sumWeights, List.foldl_cons, List.foldl_nil]
  rw [WeightVector.zero_add']

/-- A color configuration is neutral if the sum of its weights is zero -/
def IsColorNeutral (colors : List ColorPhase) : Prop :=
  let weights := colors.map colorToWeight
  (sumWeights weights).t3 = 0 ∧ (sumWeights weights).t8 = 0

/-- Alternative: check if weight vector equals zero -/
def IsColorNeutral' (colors : List ColorPhase) : Prop :=
  sumWeights (colors.map colorToWeight) = 0

/-- The two definitions are equivalent (when 0 means both components zero) -/
theorem isColorNeutral_iff_zero (colors : List ColorPhase) :
    IsColorNeutral colors ↔
    (sumWeights (colors.map colorToWeight)).t3 = 0 ∧
    (sumWeights (colors.map colorToWeight)).t8 = 0 := by
  rfl

/-- IsColorNeutral and IsColorNeutral' are equivalent -/
theorem isColorNeutral_iff_neutral' (colors : List ColorPhase) :
    IsColorNeutral colors ↔ IsColorNeutral' colors := by
  unfold IsColorNeutral IsColorNeutral'
  constructor
  · intro ⟨h3, h8⟩
    apply WeightVector.ext'
    · simp only [WeightVector.zero_t3]; exact h3
    · simp only [WeightVector.zero_t8]; exact h8
  · intro h
    constructor
    · rw [h]; rfl
    · rw [h]; rfl

/-- RGB triplet is color neutral (baryon configuration) -/
theorem rgb_is_neutral : IsColorNeutral [.R, .G, .B] := by
  unfold IsColorNeutral sumWeights colorToWeight
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  constructor
  · have h : (0 : WeightVector).t3 = 0 := rfl
    have h2 : ∀ a b : WeightVector, (a + b).t3 = a.t3 + b.t3 := fun _ _ => rfl
    simp only [h2, h, zero_add]
    exact fundamental_t3_sum_zero
  · have h : (0 : WeightVector).t8 = 0 := rfl
    have h2 : ∀ a b : WeightVector, (a + b).t8 = a.t8 + b.t8 := fun _ _ => rfl
    simp only [h2, h, zero_add]
    exact fundamental_t8_sum_zero

/-- Anti-RGB triplet (R̄ḠB̄) sums to zero in weight space (antibaryon configuration).

Note: This uses the same ColorPhase list but the physical interpretation is
that these represent antiquarks carrying anti-colors. The anti-weights
w_Rbar + w_Gbar + w_Bbar = (-w_R) + (-w_G) + (-w_B) = -(w_R + w_G + w_B) = 0.
-/
theorem antiweight_sum_neutral :
    (colorToAntiWeight .R + colorToAntiWeight .G + colorToAntiWeight .B).t3 = 0 ∧
    (colorToAntiWeight .R + colorToAntiWeight .G + colorToAntiWeight .B).t8 = 0 := by
  simp only [colorToAntiWeight, w_Rbar, w_Gbar, w_Bbar]
  constructor
  · simp only [WeightVector.add_t3, WeightVector.neg_t3]
    have h := fundamental_t3_sum_zero
    linarith
  · simp only [WeightVector.add_t8, WeightVector.neg_t8]
    have h := fundamental_t8_sum_zero
    linarith

/-- A quark-antiquark pair of the same color is neutral (meson configuration) -/
theorem meson_is_neutral (c : ColorPhase) :
    (colorToWeight c + colorToAntiWeight c).t3 = 0 ∧
    (colorToWeight c + colorToAntiWeight c).t8 = 0 := by
  simp only [colorToAntiWeight]
  cases c <;> simp only [colorToWeight, w_Rbar, w_Gbar, w_Bbar] <;> constructor
  all_goals simp only [WeightVector.add_t3, WeightVector.add_t8,
                       WeightVector.neg_t3, WeightVector.neg_t8]
  all_goals ring

/-- Empty configuration is trivially neutral -/
theorem empty_is_neutral : IsColorNeutral [] := by
  unfold IsColorNeutral sumWeights colorToWeight
  simp only [List.map_nil, List.foldl_nil]
  exact ⟨rfl, rfl⟩

/-- Single color is NOT neutral -/
theorem single_color_not_neutral (c : ColorPhase) : ¬IsColorNeutral [c] := by
  unfold IsColorNeutral sumWeights colorToWeight
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  -- Helper lemmas for component access
  have h3_zero : (0 : WeightVector).t3 = 0 := rfl
  have h8_zero : (0 : WeightVector).t8 = 0 := rfl
  have h3_add : ∀ a b : WeightVector, (a + b).t3 = a.t3 + b.t3 := fun _ _ => rfl
  have h8_add : ∀ a b : WeightVector, (a + b).t8 = a.t8 + b.t8 := fun _ _ => rfl
  simp only [h3_add, h8_add, h3_zero, h8_zero, zero_add]
  cases c
  · -- R case: w_R.t3 = 1/2 ≠ 0
    intro ⟨ht3, _⟩
    simp only [w_R] at ht3
    norm_num at ht3
  · -- G case: w_G.t3 = -1/2 ≠ 0
    intro ⟨ht3, _⟩
    simp only [w_G] at ht3
    norm_num at ht3
  · -- B case: w_B.t8 = -1/√3 ≠ 0 (but w_B.t3 = 0)
    intro ⟨_, ht8⟩
    simp only [w_B] at ht8
    -- ht8 : -1/√3 = 0, which contradicts √3 ≠ 0
    have hsqrt_pos : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
    have hsqrt_ne : Real.sqrt 3 ≠ 0 := ne_of_gt hsqrt_pos
    have h_neg : (-1 : ℝ) / Real.sqrt 3 ≠ 0 := by
      rw [neg_div, ne_eq, neg_eq_zero, div_eq_zero_iff]
      push_neg
      exact ⟨one_ne_zero, hsqrt_ne⟩
    exact h_neg ht8

/-! ## Phase Dynamics Setup

The time evolution of color fields involves oscillation at frequency ω
with the characteristic 2π/3 phase offsets.
-/

/-- Time-dependent phase for a color field -/
noncomputable def dynamicPhase (c : ColorPhase) (ω t : ℝ) : ℝ :=
  ω * t + c.angle

/-- The three dynamic phases maintain their 2π/3 separation at all times -/
theorem dynamic_phase_separation (ω t : ℝ) :
    dynamicPhase .G ω t - dynamicPhase .R ω t = 2 * Real.pi / 3 ∧
    dynamicPhase .B ω t - dynamicPhase .G ω t = 2 * Real.pi / 3 := by
  unfold dynamicPhase
  simp only [ColorPhase.angle]
  constructor <;> ring

/-- A propagating color wave -/
structure ColorWave where
  color : ColorPhase
  frequency : ℝ      -- ω
  wavenumber : ℝ     -- k
  amplitude : ℝ      -- A

/-- Wave at position x and time t -/
noncomputable def ColorWave.evaluate (w : ColorWave) (x t : ℝ) : ℝ :=
  w.amplitude * Real.cos (w.wavenumber * x - w.frequency * t + w.color.angle)

/-! ## Connection to Chirality

The "chiral" in Chiral Geometrogenesis refers to the handedness of
the field oscillations. Right-handed rotation through R → G → B → R
corresponds to positive frequency; left-handed is negative.

**Mathematical formulation:**

For a rotating phase φ(t) = ω·t + φ₀:
- If ω > 0: phase increases with time (counterclockwise in phase space)
- If ω < 0: phase decreases with time (clockwise in phase space)

The phase angles are: R=0, G=2π/3, B=4π/3

For right-handed (ω > 0):
- At t=0: dominant color is R (phase 0)
- At t=π/(3ω): all phases shift by π/3, dominant moves toward G
- At t=2π/(3ω): dominant is G (phase crossed 2π/3)
- At t=4π/(3ω): dominant is B
- At t=2π/ω: cycle completes back to R

For left-handed (ω < 0):
- Phases decrease, so dominance goes R → B → G → R
-/

/-- Chirality: the direction of phase rotation -/
inductive Chirality
  | Right  -- R → G → B → R (positive ω, counterclockwise)
  | Left   -- R → B → G → R (negative ω, clockwise)
deriving DecidableEq, Repr

/-- Right-handed phase sequence (increasing angle order) -/
def rightHandedSequence : List ColorPhase := [.R, .G, .B]

/-- Left-handed phase sequence (decreasing angle order) -/
def leftHandedSequence : List ColorPhase := [.R, .B, .G]

/-- The framework focuses on right-handed oscillations -/
theorem framework_chirality : rightHandedSequence = [.R, .G, .B] := rfl

/-- The frequency sign corresponding to each chirality -/
def Chirality.frequencySign : Chirality → ℤ
  | .Right => 1
  | .Left => -1

/-- Right-handed means positive frequency -/
theorem right_is_positive_freq : Chirality.Right.frequencySign = 1 := rfl

/-- Left-handed means negative frequency -/
theorem left_is_negative_freq : Chirality.Left.frequencySign = -1 := rfl

/-- Next color in right-handed sequence -/
def nextColorRight : ColorPhase → ColorPhase
  | .R => .G
  | .G => .B
  | .B => .R

/-- Next color in left-handed sequence -/
def nextColorLeft : ColorPhase → ColorPhase
  | .R => .B
  | .G => .R
  | .B => .G

/-- Right-handed next increases angle by 2π/3 (or wraps by -4π/3) -/
theorem next_right_angle (c : ColorPhase) :
    (nextColorRight c).angle - c.angle = 2 * Real.pi / 3 ∨
    (nextColorRight c).angle - c.angle = -4 * Real.pi / 3 := by
  cases c
  · -- R → G: 2π/3 - 0 = 2π/3
    left
    simp only [nextColorRight, ColorPhase.angle]
    ring
  · -- G → B: 4π/3 - 2π/3 = 2π/3
    left
    simp only [nextColorRight, ColorPhase.angle]
    ring
  · -- B → R: 0 - 4π/3 = -4π/3
    right
    simp only [nextColorRight, ColorPhase.angle]
    ring

/-- Left-handed next decreases angle by 2π/3 (or wraps by +4π/3) -/
theorem next_left_angle (c : ColorPhase) :
    c.angle - (nextColorLeft c).angle = 2 * Real.pi / 3 ∨
    c.angle - (nextColorLeft c).angle = -4 * Real.pi / 3 := by
  cases c
  · -- R → B: 0 - 4π/3 = -4π/3
    right
    simp only [nextColorLeft, ColorPhase.angle]
    ring
  · -- G → R: 2π/3 - 0 = 2π/3
    left
    simp only [nextColorLeft, ColorPhase.angle]
    ring
  · -- B → G: 4π/3 - 2π/3 = 2π/3
    left
    simp only [nextColorLeft, ColorPhase.angle]
    ring

/-- Right-handed sequence returns to start after 3 steps -/
theorem right_cycle : ∀ c : ColorPhase,
    nextColorRight (nextColorRight (nextColorRight c)) = c := by
  intro c; cases c <;> rfl

/-- Left-handed sequence returns to start after 3 steps -/
theorem left_cycle : ∀ c : ColorPhase,
    nextColorLeft (nextColorLeft (nextColorLeft c)) = c := by
  intro c; cases c <;> rfl

/-- Left is the inverse of right -/
theorem left_right_inverse : ∀ c : ColorPhase, nextColorLeft (nextColorRight c) = c := by
  intro c; cases c <;> rfl

/-- Right is the inverse of left -/
theorem right_left_inverse : ∀ c : ColorPhase, nextColorRight (nextColorLeft c) = c := by
  intro c; cases c <;> rfl

/-! ### Chiral Wave Dynamics

For a chiral wave, the phase evolution determines which color
is "dominant" (has maximum amplitude) at any given time.
-/

/-- A chiral color wave with explicit handedness -/
structure ChiralWave where
  chirality : Chirality
  frequency : ℝ            -- |ω| (always positive)
  wavenumber : ℝ           -- k
  amplitude : ℝ            -- A
  referenceColor : ColorPhase  -- Color that peaks at t=0, x=0

/-- Effective frequency including chirality sign -/
noncomputable def ChiralWave.effectiveFrequency (w : ChiralWave) : ℝ :=
  w.frequency * (w.chirality.frequencySign : ℝ)

/-- Right-handed wave has positive effective frequency -/
theorem right_wave_positive_freq (w : ChiralWave)
    (h : w.chirality = .Right) (hf : w.frequency > 0) :
    w.effectiveFrequency > 0 := by
  simp only [ChiralWave.effectiveFrequency, h, Chirality.frequencySign]
  simp only [Int.cast_one, mul_one]
  exact hf

/-- Left-handed wave has negative effective frequency -/
theorem left_wave_negative_freq (w : ChiralWave)
    (h : w.chirality = .Left) (hf : w.frequency > 0) :
    w.effectiveFrequency < 0 := by
  simp only [ChiralWave.effectiveFrequency, h, Chirality.frequencySign]
  simp only [Int.cast_neg, Int.cast_one, mul_neg_one]
  linarith

/-- Time to transition to next color in sequence (period/3) -/
noncomputable def ChiralWave.colorTransitionTime (w : ChiralWave) : ℝ :=
  2 * Real.pi / (3 * w.frequency)

/-- After one transition time, the phase advances by 2π/3 (for right-handed, when ω > 0) -/
theorem right_wave_color_advance (w : ChiralWave)
    (h : w.chirality = .Right) (hf : w.frequency > 0) :
    w.effectiveFrequency * w.colorTransitionTime = 2 * Real.pi / 3 := by
  simp only [ChiralWave.colorTransitionTime, ChiralWave.effectiveFrequency,
             h, Chirality.frequencySign, Int.cast_one, mul_one]
  have hne : w.frequency ≠ 0 := ne_of_gt hf
  field_simp

/-! ## Summary: The Color-Geometry Bridge

This module establishes:
1. ColorPhase ↔ WeightVector correspondence (colorToWeight)
2. Phase angles match weight vector positions (2π/3 separation)
3. Color fields on stella octangula vertices
4. Color neutrality (RGB sums to zero)
5. Dynamic phases maintain separation
6. Chirality (right-handed = R→G→B)

This connects the abstract SU(3) mathematics to physical field dynamics.
-/

end ChiralGeometrogenesis.ColorFields
