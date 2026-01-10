/-
  ChiralGeometrogenesis/Prelude.lean

  Unified Prelude for Chiral Geometrogenesis

  This file provides a single import point for the most commonly used
  definitions and theorems from the pure math modules. It re-exports
  key types and lemmas so that downstream files can simply write:

    import ChiralGeometrogenesis.Prelude

  instead of importing multiple separate modules.

  ## Exported Modules

  1. **StellaOctangula** - 3D geometry of the stella octangula
     - `Point3D`, `distSq`, `dot`, vertex definitions
     - Regularity, antipodal, and symmetry theorems

  2. **Weights** - SU(3) weight vectors
     - `WeightVector`, `w_R`, `w_G`, `w_B` and their anti-colors
     - Weight neutrality and hexagonal arrangement

  3. **SU3** - SU(3) Lie algebra
     - `SU3`, `sl3ℂ`, Gell-Mann matrices
     - Dimension and rank formulas

  4. **Basic** - Core ColorPhase and pressure definitions
     - `ColorPhase`, phase angles
     - `PressureField` type

  5. **DynamicsFoundation** - Field dynamics infrastructure
     - `ChiralFieldValue`, `ChiralField`, `ColorFieldTriplet`
     - `EvolutionConfig`, `PhaseEvolution` (internal time)
     - `PreGeometricEnergyConfig` (algebraic energy)
     - Bootstrap and Noether circularity resolution theorems

  ## Usage

  ```lean
  import ChiralGeometrogenesis.Prelude

  -- Now available without namespace qualification:
  #check Point3D
  #check WeightVector
  #check ColorPhase
  #check w_R
  ```
-/

-- Import all foundational modules
import ChiralGeometrogenesis.Constants
import ChiralGeometrogenesis.Basic
import ChiralGeometrogenesis.PureMath.Polyhedra.StellaOctangula
import ChiralGeometrogenesis.PureMath.LieAlgebra.SU3
import ChiralGeometrogenesis.PureMath.LieAlgebra.Weights
import ChiralGeometrogenesis.Foundations.DynamicsFoundation

namespace ChiralGeometrogenesis.Prelude

/-! ## Re-exports from StellaOctangula

These are the most commonly used geometric definitions and theorems.
-/

-- Core types
export PureMath.Polyhedra (Point3D)
export PureMath.Polyhedra (Edge Face)
export PureMath.Polyhedra (StellaVertex S4xZ2)

-- Distance and dot product functions
export PureMath.Polyhedra (distSq distSqFromOrigin dot)

-- Vertex definitions (up-tetrahedron)
export PureMath.Polyhedra (v_up_0 v_up_1 v_up_2 v_up_3)
export PureMath.Polyhedra (upVertex)

-- Vertex definitions (down-tetrahedron)
export PureMath.Polyhedra (v_down_0 v_down_1 v_down_2 v_down_3)
export PureMath.Polyhedra (downVertex)

-- Vertex and edge lists
export PureMath.Polyhedra (stellaOctangulaVertices stellaOctangulaEdges stellaOctangulaFaces)
export PureMath.Polyhedra (upTetrahedronEdges downTetrahedronEdges)
export PureMath.Polyhedra (upTetrahedronFaces downTetrahedronFaces)

-- Key theorems: counts
export PureMath.Polyhedra (stella_vertex_count stella_edge_count stella_face_count)
export PureMath.Polyhedra (tetrahedron_edge_count tetrahedron_face_count)

-- Key theorems: regularity
export PureMath.Polyhedra (up_tetrahedron_regular down_tetrahedron_regular both_tetrahedra_regular)

-- Key theorems: vertex properties
export PureMath.Polyhedra (up_vertices_on_sphere down_vertices_on_sphere)
export PureMath.Polyhedra (up_vertices_distinct down_vertices_distinct up_down_disjoint)
export PureMath.Polyhedra (stella_vertices_pairwise_distinct)

-- Key theorems: antipodal and symmetry
export PureMath.Polyhedra (antipodal_property swap_negates_vertices)
export PureMath.Polyhedra (stella_symmetry_order tetrahedron_symmetry_count)

-- Key theorems: angles and Euler characteristic
export PureMath.Polyhedra (tetrahedral_angle_cos_squared euler_characteristic_explicit)

-- Simp lemmas (for automation)
export PureMath.Polyhedra (distSq_self distSq_comm dot_comm)

-- Summary theorem
export PureMath.Polyhedra (stella_octangula_complete)

/-! ## Re-exports from Weights

SU(3) weight vectors for color charge representation.
-/

-- Core type
export PureMath.LieAlgebra (WeightVector)

-- Fundamental representation weights (quarks)
export PureMath.LieAlgebra (w_R w_G w_B)
export PureMath.LieAlgebra (fundamentalWeights)

-- Anti-fundamental representation weights (antiquarks)
export PureMath.LieAlgebra (w_Rbar w_Gbar w_Bbar)
export PureMath.LieAlgebra (antiFundamentalWeights allWeightVertices)

-- Distance and norm functions
export PureMath.LieAlgebra (weightDistSq weightNormSq weightDot)

-- Key theorems: neutrality
export PureMath.LieAlgebra (fundamental_t3_sum_zero fundamental_t8_sum_zero)

-- Key theorems: equilateral triangle (diagonals of hexagon)
export PureMath.LieAlgebra (fundamental_weights_equilateral)
export PureMath.LieAlgebra (dist_sq_R_G dist_sq_G_B dist_sq_B_R)

-- Key theorems: norm properties
export PureMath.LieAlgebra (fundamental_weight_norm_sq neg_weight_norm_sq)

-- Key theorems: hexagonal arrangement
export PureMath.LieAlgebra (dist_sq_R_Bbar dist_sq_Bbar_G)

-- Root vectors (A₂ root system)
export PureMath.LieAlgebra (root_alpha1 root_alpha2 root_alpha3 su3_roots)

-- Key theorems: root properties
export PureMath.LieAlgebra (root_alpha1_norm_sq root_alpha2_norm_sq root_alpha3_norm_sq)
export PureMath.LieAlgebra (root_alpha3_eq_sum root_sum_closure)
export PureMath.LieAlgebra (root_dot_alpha1_alpha2 cartan_matrix_entry_12 cartan_matrix_entry_21)
export PureMath.LieAlgebra (all_roots_equal_norm roots_form_hexagon)

-- Sqrt(3) properties
export PureMath.LieAlgebra (sqrt_three_pos sqrt_three_sq sqrt_three_ne_zero two_sqrt_three_ne_zero)

/-! ## Re-exports from SU3

SU(3) Lie algebra structure.
-/

-- Core types
export PureMath.LieAlgebra (SU3 sl3ℂ)

-- Gell-Mann matrices
export PureMath.LieAlgebra (gellMannMatrix)

-- Dimension formulas
export PureMath.LieAlgebra (gellMann_count su3_dimension_formula)
export PureMath.LieAlgebra (cartan_generators_count su3_rank_formula)

-- Tracelessness
export PureMath.LieAlgebra (gellMann_traceless)

/-! ## Re-exports from Basic

Core framework definitions.
-/

-- Color phases
export ChiralGeometrogenesis (ColorPhase)

-- Phase angle and properties
export ChiralGeometrogenesis (color_phases_equally_spaced color_phases_sum)

-- Pressure field type
export ChiralGeometrogenesis (PressureField totalPressureField)

-- Generic Tetrahedron and StellaOctangula structures
export ChiralGeometrogenesis (Tetrahedron StellaOctangula)

-- Sqrt(3) properties (from Basic, also available from Weights)
export ChiralGeometrogenesis (sqrt_three_pos sqrt_three_sq sqrt_three_ne_zero)

/-! ## Re-exports from DynamicsFoundation

Complex chiral field structure, internal time parameter, and pre-geometric energy.
-/

-- Phase configuration (canonical definition for R/G/B phases)
export Foundations (PhaseConfig)

-- Chiral field value (amplitude × phase)
export Foundations (ChiralFieldValue)

-- Spatially-dependent chiral field
export Foundations (ChiralField)

-- Color field triplet (R, G, B)
export Foundations (ColorFieldTriplet)

-- Internal evolution parameter (breaks bootstrap circularity)
export Foundations (EvolutionConfig PhaseEvolution)

-- Pre-geometric energy functional (resolves Noether circularity)
export Foundations (PreGeometricEnergyConfig)

-- Combined dynamics configuration
export Foundations (DynamicsConfig)

-- Key theorems
export Foundations (bootstrap_resolution phaseLock_stability noether_circularity_resolution)

/-! ## Convenience Aliases

These provide shorter names for commonly used theorems.
-/

-- Alias for the complete stella characterization
abbrev stellaComplete := PureMath.Polyhedra.stella_octangula_complete

-- Alias for weight neutrality (both components)
theorem weight_neutrality :
    w_R.t3 + w_G.t3 + w_B.t3 = 0 ∧ w_R.t8 + w_G.t8 + w_B.t8 = 0 :=
  ⟨PureMath.LieAlgebra.fundamental_t3_sum_zero, PureMath.LieAlgebra.fundamental_t8_sum_zero⟩

-- Combined antipodal statement using negation
theorem antipodal_symmetry :
    v_down_0 = -v_up_0 ∧ v_down_1 = -v_up_1 ∧ v_down_2 = -v_up_2 ∧ v_down_3 = -v_up_3 :=
  PureMath.Polyhedra.antipodal_property

-- All vertices equidistant from origin (circumsphere)
theorem all_vertices_equidistant :
    distSqFromOrigin v_up_0 = 3 ∧ distSqFromOrigin v_up_1 = 3 ∧
    distSqFromOrigin v_up_2 = 3 ∧ distSqFromOrigin v_up_3 = 3 ∧
    distSqFromOrigin v_down_0 = 3 ∧ distSqFromOrigin v_down_1 = 3 ∧
    distSqFromOrigin v_down_2 = 3 ∧ distSqFromOrigin v_down_3 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PureMath.Polyhedra.up_vertices_on_sphere.1
  · exact PureMath.Polyhedra.up_vertices_on_sphere.2.1
  · exact PureMath.Polyhedra.up_vertices_on_sphere.2.2.1
  · exact PureMath.Polyhedra.up_vertices_on_sphere.2.2.2
  · exact PureMath.Polyhedra.down_vertices_on_sphere.1
  · exact PureMath.Polyhedra.down_vertices_on_sphere.2.1
  · exact PureMath.Polyhedra.down_vertices_on_sphere.2.2.1
  · exact PureMath.Polyhedra.down_vertices_on_sphere.2.2.2

/-! ## Re-exports from Constants

Physical and mathematical constants for the framework.
-/

-- Fundamental particle physics
export Constants (N_c N_f N_f_chiral hbar_c_MeV_fm numberOfGenerations baryonNumberChange)

-- QCD and beta function
export Constants (lambdaQCD beta0 beta0_formula beta0_pure_YM)

-- SU(3) Lie algebra structure
export Constants (su_rank adjoint_dim num_roots num_zero_weights)
export Constants (killingCoefficient dualCoxeterNumber gellMannTraceNorm)

-- Color/phase geometry
export Constants (colorPhaseOffset phi_R phi_G phi_B omegaSquared omegaCharacteristic)

-- Stella octangula geometry
export Constants (WF4_order stella_symmetry_order cell24_vertices)
export Constants (intrinsicEdgeLength intrinsicCenterToVertex intrinsicDiagonalDistance)

-- Gravitational/Planck constants
export Constants (GravitationalConstants)

-- Experimental values
export Constants (experimentalPionDecayRate_eV experimentalPionDecayUncertainty_eV)
export Constants (observationRadius_physical sqrt_sigma_observed_MeV avogadro)

-- Derived constants
export Constants (anomalyCoefficient WZW_coefficient tHooft_fermion_legs)
export Constants (confinementRadius dimensionlessIntegralJ total_mode_count)

-- Key theorems
export Constants (N_c_pos N_f_pos hbar_c_pos lambdaQCD_pos beta0_positive)
export Constants (phase_separations phase_sum omega_sq_relation)
export Constants (confinementRadius_pos dimensionlessIntegralJ_pos)

end ChiralGeometrogenesis.Prelude
