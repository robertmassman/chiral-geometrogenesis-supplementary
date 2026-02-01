-- Core modules (existing)
import ChiralGeometrogenesis.Basic
import ChiralGeometrogenesis.Definition_0_0_0

-- Pure Math foundations
import ChiralGeometrogenesis.PureMath.LieAlgebra.SU3
import ChiralGeometrogenesis.PureMath.LieAlgebra.Weights
import ChiralGeometrogenesis.PureMath.Polyhedra.StellaOctangula

-- D=4 Derivation (definitive, from physical axioms)
import ChiralGeometrogenesis.Foundations.PhysicalAxioms
import ChiralGeometrogenesis.Foundations.StabilityTheorems
import ChiralGeometrogenesis.Foundations.Theorem_0_0_1
import ChiralGeometrogenesis.Foundations.Theorem_0_0_2

-- Theorem 0.0.3: Stella Octangula Uniqueness (modular structure)
import ChiralGeometrogenesis.Foundations.Lemma_0_0_3a  -- Definitions, GR/MIN criteria
import ChiralGeometrogenesis.Foundations.Lemma_0_0_3b  -- Candidate elimination
import ChiralGeometrogenesis.Foundations.Lemma_0_0_3c  -- A₂ root system
import ChiralGeometrogenesis.Foundations.Lemma_0_0_3d  -- Regularity from Weyl
import ChiralGeometrogenesis.Foundations.Lemma_0_0_3e  -- QCD physics structures
import ChiralGeometrogenesis.Foundations.Lemma_0_0_3f  -- Explicit isomorphism
import ChiralGeometrogenesis.Foundations.Theorem_0_0_3_Main  -- Main uniqueness theorem
import ChiralGeometrogenesis.Foundations.Theorem_0_0_3_Supplements  -- Additional results
import ChiralGeometrogenesis.Foundations.Theorem_0_0_4  -- GUT Structure from Stella Octangula
import ChiralGeometrogenesis.Foundations.Theorem_0_0_5  -- Chirality Selection from Geometry

-- Color Fields (Phase 0 - Physics Connection)
import ChiralGeometrogenesis.ColorFields.Basic

-- Phase 0: Boundary Topology and Time Emergence
import ChiralGeometrogenesis.Phase0.Definition_0_1_1  -- Stella Octangula Boundary Topology
import ChiralGeometrogenesis.Phase0.Definition_0_1_2  -- Three Color Fields with Relative Phases
-- Theorem 0.2.1 is now split into modular subfiles
import ChiralGeometrogenesis.Phase0.Theorem_0_2_1.Main
import ChiralGeometrogenesis.Phase0.Theorem_0_2_2
import ChiralGeometrogenesis.Phase0.Theorem_0_3_1  -- W-Direction Correspondence (4D → 3D)

-- Phase 4: Topological Solitons and Matter
import ChiralGeometrogenesis.Phase4.Theorem_4_1_1  -- Existence of Solitons
import ChiralGeometrogenesis.Phase4.Theorem_4_1_2  -- Soliton Mass Spectrum
import ChiralGeometrogenesis.Phase4.Theorem_4_1_3  -- Fermion Number from Topology
import ChiralGeometrogenesis.Phase4.Theorem_4_1_4  -- Dynamic Suspension Equilibrium
import ChiralGeometrogenesis.Phase4.Theorem_4_2_1  -- Chiral Bias in Soliton Formation
import ChiralGeometrogenesis.Phase4.Theorem_4_2_2  -- Baryon Asymmetry from Chiral Bias
import ChiralGeometrogenesis.Phase4.Theorem_4_2_3  -- First-Order Electroweak Phase Transition

-- Phase 5: Emergent Spacetime and Gravity
import ChiralGeometrogenesis.Phase5.Theorem_5_1_1  -- Stress-Energy Tensor from L_CG
import ChiralGeometrogenesis.Phase5.Proposition_5_2_4c  -- Tensor Rank from Derivative Structure

-- Phase 6: Scattering Theory
import ChiralGeometrogenesis.Phase6.Theorem_6_1_1  -- Complete Feynman Rules
import ChiralGeometrogenesis.Phase6.Theorem_6_2_1  -- Tree-Level Scattering Amplitudes

-- Phase 8: Predictions and Tests
import ChiralGeometrogenesis.Phase8.Proposition_8_4_4  -- Atmospheric Angle θ₂₃ Correction
import ChiralGeometrogenesis.Phase8.Proposition_8_5_1  -- Lattice QCD and Heavy-Ion Predictions
import ChiralGeometrogenesis.Phase8.Prediction_8_3_1  -- W Condensate Dark Matter

/-!
# Chiral Geometrogenesis - Lean Formalization

A formal verification of the mathematical framework proposing that
spacetime and matter emerge from right-handed pressure-driven field
oscillations on the stella octangula.

## Module Structure

### Core Definitions (`Basic.lean`)
- ColorPhase: R, G, B color fields with 2π/3 phase separation
- Tetrahedron, StellaOctangula: geometric structures
- PressureField: field definitions
- Sqrt(3) properties for symbolic handling

### Pure Mathematics (`PureMath/`)
- `LieAlgebra/SU3.lean`: Gell-Mann matrices, Cartan subalgebra, Killing form
- `LieAlgebra/Weights.lean`: Weight vectors, hexagonal arrangement
- `Polyhedra/StellaOctangula.lean`: 8 vertices, tetrahedral angle cos θ = -1/3

### Physical Foundations (`Foundations/`)
- `PhysicalAxioms.lean`: Four physical axioms (gravity, EM, QM, waves)
- `StabilityTheorems.lean`: Derived constraints (orbital, atomic, Huygens, knots)
- `Theorem_0_0_1.lean`: D = 4 derived definitively from observer existence

### Geometric Realization (`Definition_0_0_0.lean`)
- GR1-GR3, MIN1-MIN3 criteria
- Stella octangula satisfies these for SU(3)

### Euclidean Metric (`Theorem_0_0_2.lean`)
- Killing form of SU(3)
- Induced Euclidean metric on ℝ³

## Proof Structure

- **Phase -1**: Pre-geometric foundations (D=4, SU(3), ℝ³)
- **Phase 0**: Stella octangula topology, color fields, pressure functions
- **Phase 1**: SU(3) geometry and chiral field definitions
- **Phase 2**: Pressure-depression mechanism and phase dynamics
- **Phase 3**: Mass generation via phase-gradient mass generation
- **Phase 4**: Topological solitons and matter
- **Phase 5**: Emergent spacetime and gravity

## Key Results

1. **D = 4 is DERIVED** (not axiomatized) from physical constraints
2. **Stella octangula uniqueness** for SU(3) geometric realization
3. **Tetrahedral angle** cos θ = -1/3 proven exactly
4. **Weight hexagon** from SU(3) fundamental + anti-fundamental representations
-/
