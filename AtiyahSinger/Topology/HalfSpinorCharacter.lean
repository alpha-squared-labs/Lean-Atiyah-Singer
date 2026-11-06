/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactHalfSpinorCharacter
public import AtiyahSinger.Topology.CompactHausdorffHomologyTestSources
public import AtiyahSinger.Topology.HalfSpinorCharacterBasic
public import AtiyahSinger.Topology.HalfSpinorPullback
public import AtiyahSinger.Topology.PontryaginPullback
public import AtiyahSinger.Topology.SpinEulerPullback

/-!
# The Chern character of the actual half-spinor difference

Public module ID: M1875.

The original difference uses the two actual associated half-spin bundles
and their genuine degreewise rational Chern characters. For the specified
positive-even-rank topological spin structure its character is the normalized
Euler class of the same original real bundle times the actual inverse A-hat
class, with the sign (-1)^m fixed by the original exterior parity convention.

Sources: Lawson--Michelsohn, Spin Geometry, III.11, Construction 11.23 and
Proposition 11.24, p.238; Gilkey, Invariance Theory, the Heat Equation, and
the Atiyah--Singer Index Theorem, 3.2.5, p.164, and 3.3.6(b), p.174.
The torus character is the product of exp(-x_j/2)-exp(x_j/2), so the
rank-two leading coefficient is minus the original normalized Euler class.
This is the positive-minus-negative convention, not its reversal.

The base is an arbitrary topological space. The three auxiliary metrics
are supplied explicitly; no compactness, connectedness or paracompactness
is imposed. The original spin structure supplies the geometrically normalized
Euler class; an unrelated cohomological orientation is not an input.
Only positive even rank is covered by the existing spin-structure interface.
The statements are separated into lower-degree vanishing and a shifted
formula, avoiding truncated subtraction of natural cohomological degrees.
The definition and below-rank theorem are re-exported from `HalfSpinorCharacterBasic`.
That theorem uses the actual Clifford isomorphism off the zero section and the
low-degree Thom restriction theorem on arbitrary bases.

The shifted formula follows from the proved compact-base K-character formula,
its comparison with the ordinary character, and naturality under the native
spin pullback. Every singular homology class comes from a compact Hausdorff
finite realization; the field Kronecker pairing therefore detects cohomology
equality on those test sources. The proof applies the compact formula on each
such source with its actual pulled spin structure, Euler class and inverse
A-hat class. No compactness assumption on the original base or additional
restriction-injectivity premise is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle
open scoped TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

universe u v

variable {m : ℕ} {B : Type u} {P : Type v} {E : B → Type u}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  {o : ∀ x, Orientation ℝ (E x) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- SG Proposition 11.24: the half-spinor difference is signed Euler times inverse A-hat. -/
theorem TopologicalSpinStructure.halfSpinorCharacterComponent_add
    (S : TopologicalSpinStructure m E o hm hP)
    (hPlus : ComplexBundle.ContinuousHermitianMetric (HalfSpinorBundle m hP 0))
    (hMinus : ComplexBundle.ContinuousHermitianMetric (HalfSpinorBundle m hP 1))
    (hV : letI := (ComplexBundle.complexificationTopology
        (EuclideanSpace ℝ (Fin (2 * m))) E)
      ComplexBundle.ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x))
    (j : ℕ) :
    letI := RealBundle.isFiniteRank_of_vectorBundle
      (EuclideanSpace ℝ (Fin (2 * m))) E
    halfSpinorCharacterComponent m hP hPlus hMinus (m + j) =
      (-1 : ℚ) ^ m • singularCohomologyEvenCup ℚ B m j S.rationalEulerClass
        (RealBundle.inverseAHatEvenComponent
          (EuclideanSpace ℝ (Fin (2 * m))) E hV j) := by
  /- Detect the equality on compact Hausdorff test sources. On each source,
  pull back the same spin structure and choose metrics on its actual bundles.
  The compact formula and the three naturality theorems then give the pullback
  of the required equality. The original base acquires no extra hypothesis. -/
  classical
  let V := EuclideanSpace ℝ (Fin (2 * m))
  let hnorm : ∀ b, NormedAddCommGroup (E b) := inferInstance
  let hinner : ∀ b, InnerProductSpace ℝ (E b) := inferInstance
  let := hP
  let := RealBundle.isFiniteRank_of_vectorBundle V E
  apply singularCohomology_eq_of_compactHausdorff_pullback ℚ (2 * (m + j))
  intro Y _ _ f
  -- Keep the pulled real fibers with their original norm and inner product.
  let E' : Y → Type u := (f : Y → B) *ᵖ E
  let : ∀ y, NormedAddCommGroup (E' y) := fun y ↦ hnorm (f y)
  let : ∀ y, InnerProductSpace ℝ (E' y) := fun y ↦ hinner (f y)
  let : ∀ y, TopologicalSpace (E' y) :=
    fun y ↦ (hnorm (f y)).toUniformSpace.toTopologicalSpace
  let : FiberBundle V E' := FiberBundle.pullback (F := V) (E := E) f
  let : ∀ y, AddCommMonoid (E' y) := fun y ↦ (hnorm (f y)).toAddCommMonoid
  let : ∀ y, Module ℝ (E' y) := fun y ↦ (hinner (f y)).toModule
  let : VectorBundle ℝ V E' := VectorBundle.pullback ℝ (F := V) (E := E) f
  let := isContinuousRiemannianBundle_pullback V E f
  let hQ := isPrincipalBundle_pullback (G := spinGroup (realSpinorQuadraticForm m))
    (projection := projection) f
  let S' : TopologicalSpinStructure m E' (fun y ↦ o (f y)) hm hQ := S.pullback f
  -- Compactness supplies metrics only on these actual pulled bundles and complexification.
  let := isFiniteRank_associatedVector hQ (complexSpinParityContRepresentation m 0)
    (continuous_complexSpinParityRepresentation m 0)
  let := isFiniteRank_associatedVector hQ (complexSpinParityContRepresentation m 1)
    (continuous_complexSpinParityRepresentation m 1)
  let kPlus := (nonempty_continuousHermitianMetric (HalfSpinorBundle m hQ 0)).some
  let kMinus := (nonempty_continuousHermitianMetric (HalfSpinorBundle m hQ 1)).some
  let := RealBundle.isFiniteRank_of_vectorBundle V E'
  let kV : letI := ComplexBundle.complexificationTopology V E'
      ContinuousHermitianMetric (fun y ↦ ℂ ⊗[ℝ] E' y) := by
    letI := ComplexBundle.complexificationTopology V E'
    letI := RealBundle.isFiniteRank_complexification V E'
    exact (nonempty_continuousHermitianMetric (fun y ↦ ℂ ⊗[ℝ] E' y)).some
  -- Naturality retains the specified source metrics, orientation, parity and inverse series.
  have hcharacter := halfSpinorCharacterComponent_pullback m (hP := hP)
    f hPlus hMinus kPlus kMinus (m + j)
  have hEuler : singularCohomologyPullback ℚ f (2 * m) S.rationalEulerClass =
      S'.rationalEulerClass := S.rationalEulerClass_pullback f
  have hAHat : singularCohomologyPullback ℚ f (2 * j)
      (RealBundle.inverseAHatEvenComponent V E hV j) =
        RealBundle.inverseAHatEvenComponent V E' kV j :=
    RealBundle.inverseAHatEvenComponent_pullback V E hV f kV j
  have hcompact := S'.halfSpinorCharacterComponent_add_of_compactSpace kPlus kMinus kV j
  -- The even-cup naturality theorem preserves the original degree transport and Euler-first order.
  rw [← hcharacter, map_smul, singularCohomologyPullback_evenCup, hEuler, hAHat]
  exact hcompact

end AtiyahSinger
