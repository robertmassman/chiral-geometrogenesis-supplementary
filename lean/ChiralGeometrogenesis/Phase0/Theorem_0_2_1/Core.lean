/-
  Phase0/Theorem_0_2_1/Core.lean

  Core definitions for Theorem 0.2.1: Total Field from Superposition

  This module contains the fundamental structures:
  - ChiralField, AmplitudeFunction
  - Phase exponentials (phaseR, phaseG, phaseB)
  - ColorAmplitudes configuration
  - Total chiral field definition
  - Pressure modulated configurations

  Reference: docs/proofs/Phase0/Theorem-0.2.1-Total-Field-Superposition.md
-/

import ChiralGeometrogenesis.Basic
import ChiralGeometrogenesis.ColorFields.Basic
import ChiralGeometrogenesis.PureMath.LieAlgebra.Weights
import ChiralGeometrogenesis.PureMath.Polyhedra.StellaOctangula
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

set_option linter.style.docString false
set_option linter.unusedVariables false

namespace ChiralGeometrogenesis.Phase0.Theorem_0_2_1

open ChiralGeometrogenesis
open ChiralGeometrogenesis.ColorFields
open ChiralGeometrogenesis.PureMath.LieAlgebra
open ChiralGeometrogenesis.PureMath.Polyhedra
open Complex Real

/-! ## The Chiral Field

The chiral field χ is a complex-valued field on the stella octangula boundary.
Each color contributes with its characteristic phase.
-/

/-- A complex chiral field value -/
structure ChiralField where
  value : Point3D → ℂ

/-- Amplitude function for a single color field -/
structure AmplitudeFunction where
  amplitude : Point3D → ℝ
  nonneg : ∀ x, 0 ≤ amplitude x

/-- Phase value as complex exponential e^{iφ} -/
noncomputable def phaseExp (c : ColorPhase) : ℂ :=
  Complex.exp (Complex.I * c.angle)

/-- The three phase exponentials -/
noncomputable def phaseR : ℂ := phaseExp ColorPhase.R  -- e^{i·0} = 1
noncomputable def phaseG : ℂ := phaseExp ColorPhase.G  -- e^{i·2π/3}
noncomputable def phaseB : ℂ := phaseExp ColorPhase.B  -- e^{i·4π/3}

/-! ## Theorem 0.2.1: Total Field Superposition

The total chiral field is the sum of contributions from each color.
-/

/-- Single color field contribution: a_c(x) · e^{iφ_c} -/
noncomputable def colorContribution (a : AmplitudeFunction) (c : ColorPhase) (x : Point3D) : ℂ :=
  (a.amplitude x : ℂ) * phaseExp c

/-- Configuration of three amplitude functions (one per color) -/
structure ColorAmplitudes where
  aR : AmplitudeFunction
  aG : AmplitudeFunction
  aB : AmplitudeFunction

/-- Total chiral field from superposition (Theorem 0.2.1 main statement) -/
noncomputable def totalChiralField (cfg : ColorAmplitudes) (x : Point3D) : ℂ :=
  colorContribution cfg.aR ColorPhase.R x +
  colorContribution cfg.aG ColorPhase.G x +
  colorContribution cfg.aB ColorPhase.B x

/-- Symmetric configuration: all amplitudes equal -/
noncomputable def symmetricConfig (a₀ : ℝ) (ha : 0 ≤ a₀) : ColorAmplitudes :=
  { aR := ⟨fun _ => a₀, fun _ => ha⟩
    aG := ⟨fun _ => a₀, fun _ => ha⟩
    aB := ⟨fun _ => a₀, fun _ => ha⟩ }

/-! ## Pressure Modulated Configuration

For non-uniform pressure distributions, the gradient of the total field
is non-zero. This is essential for the phase-gradient mass generation mechanism.
-/

/-- A pressure-modulated amplitude configuration -/
structure PressureModulatedConfig where
  /-- Base amplitude -/
  a₀ : ℝ
  /-- Base amplitude is positive -/
  a₀_pos : 0 < a₀
  /-- Pressure function for each color -/
  pressure : ColorPhase → Point3D → ℝ
  /-- Pressures are positive -/
  pressure_pos : ∀ c x, 0 < pressure c x

/-- Convert pressure config to amplitude config -/
noncomputable def PressureModulatedConfig.toAmplitudes (cfg : PressureModulatedConfig) :
    ColorAmplitudes :=
  { aR := ⟨fun x => cfg.a₀ * cfg.pressure ColorPhase.R x,
          fun x => mul_nonneg (le_of_lt cfg.a₀_pos) (le_of_lt (cfg.pressure_pos _ _))⟩
    aG := ⟨fun x => cfg.a₀ * cfg.pressure ColorPhase.G x,
          fun x => mul_nonneg (le_of_lt cfg.a₀_pos) (le_of_lt (cfg.pressure_pos _ _))⟩
    aB := ⟨fun x => cfg.a₀ * cfg.pressure ColorPhase.B x,
          fun x => mul_nonneg (le_of_lt cfg.a₀_pos) (le_of_lt (cfg.pressure_pos _ _))⟩ }

/-- Total field with pressure modulation -/
noncomputable def pressureModulatedField (cfg : PressureModulatedConfig) (x : Point3D) : ℂ :=
  totalChiralField cfg.toAmplitudes x

/-- The center point of the stella octangula -/
noncomputable def stellaCenter : Point3D := ⟨0, 0, 0⟩

/-! ## Canonical Vertex Positions

The four vertices of the "up" tetrahedron T₊ are positioned at alternating
vertices of a cube inscribed in the unit sphere. Each vertex is at distance 1
from the center (since (1/√3)² + (1/√3)² + (1/√3)² = 1/3 + 1/3 + 1/3 = 1).

The three COLOR vertices (R, G, B) correspond to the three color charges.
The fourth vertex W ("white") completes the tetrahedron.

These are the **canonical definitions** used throughout Theorem 0.2.1.
All other files should import these rather than redefining them.

**Geometric Note:**
The vertices satisfy the tetrahedron constraint: any two vertices are
equidistant (edge length = 2√(2/3) in our normalization).

**Citation:**
For regular tetrahedron inscribed in unit sphere, see:
Coxeter, "Regular Polytopes" (Dover, 1973), §2.4.
-/

/-- Vertex R position: (1/√3, 1/√3, 1/√3)
    This is a vertex of the "up" tetrahedron T₊ -/
noncomputable def vertexR : Point3D := ⟨1/Real.sqrt 3, 1/Real.sqrt 3, 1/Real.sqrt 3⟩

/-- Vertex G position: (1/√3, -1/√3, -1/√3)
    This is a vertex of the "up" tetrahedron T₊ -/
noncomputable def vertexG : Point3D := ⟨1/Real.sqrt 3, -1/Real.sqrt 3, -1/Real.sqrt 3⟩

/-- Vertex B position: (-1/√3, 1/√3, -1/√3)
    This is a vertex of the "up" tetrahedron T₊ -/
noncomputable def vertexB : Point3D := ⟨-1/Real.sqrt 3, 1/Real.sqrt 3, -1/Real.sqrt 3⟩

/-- Vertex W position: (-1/√3, -1/√3, 1/√3)
    This is the fourth vertex of T₊, completing the tetrahedron.
    The "white" vertex has no color charge in the physics interpretation. -/
noncomputable def vertexW : Point3D := ⟨-1/Real.sqrt 3, -1/Real.sqrt 3, 1/Real.sqrt 3⟩

/-- Map from color phase to vertex position.
    Note: Only the three color vertices are mapped; the fourth vertex W
    is defined separately as it has no associated color phase. -/
noncomputable def colorVertex : ColorPhase → Point3D
  | .R => vertexR
  | .G => vertexG
  | .B => vertexB

/-- Verification: All four T₊ vertices are at unit distance from center.
    This follows from (±1/√3)² + (±1/√3)² + (±1/√3)² = 3 × (1/3) = 1. -/
theorem vertexR_unit_dist : vertexR.x^2 + vertexR.y^2 + vertexR.z^2 = 1 := by
  unfold vertexR
  have h : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
    rw [div_pow, one_pow]
    have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)
    rw [hsqrt]
  simp only [h]; ring

theorem vertexG_unit_dist : vertexG.x^2 + vertexG.y^2 + vertexG.z^2 = 1 := by
  unfold vertexG
  have h : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
    rw [div_pow, one_pow]
    have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)
    rw [hsqrt]
  have hn : (-1 / Real.sqrt 3) ^ 2 = 1 / 3 := by rw [neg_div, neg_sq, h]
  simp only [h, hn]; ring

theorem vertexB_unit_dist : vertexB.x^2 + vertexB.y^2 + vertexB.z^2 = 1 := by
  unfold vertexB
  have h : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
    rw [div_pow, one_pow]
    have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)
    rw [hsqrt]
  have hn : (-1 / Real.sqrt 3) ^ 2 = 1 / 3 := by rw [neg_div, neg_sq, h]
  simp only [h, hn]; ring

theorem vertexW_unit_dist : vertexW.x^2 + vertexW.y^2 + vertexW.z^2 = 1 := by
  unfold vertexW
  have h : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
    rw [div_pow, one_pow]
    have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)
    rw [hsqrt]
  have hn : (-1 / Real.sqrt 3) ^ 2 = 1 / 3 := by rw [neg_div, neg_sq, h]
  simp only [h, hn]; ring

end ChiralGeometrogenesis.Phase0.Theorem_0_2_1
