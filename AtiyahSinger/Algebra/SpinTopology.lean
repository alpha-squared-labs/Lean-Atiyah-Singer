/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorTopology
public import AtiyahSinger.Algebra.RealSpinor
public import Mathlib.RepresentationTheory.Continuous.Basic

/-!
# The native spin group's finite-dimensional topology and continuous actions

Public module ID: M0060.

The real Clifford algebra has its actual finite-dimensional vector-space
topology. We realize it by transporting the coordinate norm through mathlib's
Clifford-to-exterior linear equivalence and a finite real exterior basis. The
original spinGroup inherits the subspace topology from this same algebra.
In particular the topology does not come from its vector action, which would
lose the distinction between the two central lifts in positive rank.

The full and parity spinor spaces retain the original exterior coordinate
norm and subspace norms from ExteriorTopology. All actions below are exactly
the previously defined real vector and complex spinor representations. Their
ContRepresentation wrappers only add continuity of each original operator;
joint continuity in the group and vector is stated separately and supplies
the hypothesis needed by the associated-vector-bundle construction.

Source: Lawson--Michelsohn, Spin Geometry, I.2, I.5 and II.5. The coordinate
norms and wrappers are implementation adapters for these standard topological
representations. No topology on a new group carrier, spin structure, covering
map or associated bundle is introduced here. The zero-dimensional algebra,
its native spin group and both parity spaces are included.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- Real exterior coordinates on the original real Clifford algebra. -/
def realSpinorCliffordCoordinates (m : ℕ) :
    CliffordAlgebra (realSpinorQuadraticForm m) ≃ₗ[ℝ]
      (Finset (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin m)))) → ℝ) :=
  (CliffordAlgebra.equivExterior (realSpinorQuadraticForm m)).trans
    (Module.finBasis ℝ (EuclideanSpace ℂ (Fin m))).ExteriorAlgebra.equivFun

/-- A real coordinate norm on the original Clifford algebra, without changing its carrier. -/
@[instance_reducible]
def realSpinorCliffordNormedAddCommGroup (m : ℕ) :
    NormedAddCommGroup (CliffordAlgebra (realSpinorQuadraticForm m)) :=
  NormedAddCommGroup.induced _ _ (realSpinorCliffordCoordinates m)
    (realSpinorCliffordCoordinates m).injective

attribute [local instance] realSpinorCliffordNormedAddCommGroup

/-- Real scalar multiplication for the same pulled-back Clifford coordinate norm. -/
@[instance_reducible]
def realSpinorCliffordNormedSpace (m : ℕ) :
    NormedSpace ℝ (CliffordAlgebra (realSpinorQuadraticForm m)) :=
  NormedSpace.induced ℝ _ _ (realSpinorCliffordCoordinates m)

attribute [local instance] realSpinorCliffordNormedSpace

/-- The native spin group has the subspace topology of the original real Clifford algebra. -/
@[instance_reducible]
def spinGroupTopology (m : ℕ) : TopologicalSpace (spinGroup (realSpinorQuadraticForm m)) :=
  TopologicalSpace.induced
    (Subtype.val : spinGroup (realSpinorQuadraticForm m) →
      CliffordAlgebra (realSpinorQuadraticForm m)) inferInstance

attribute [local instance] spinGroupTopology

/-- The native spin group is a topological group for this Clifford subspace topology. -/
theorem spinGroup_isTopologicalGroup (m : ℕ) :
    IsTopologicalGroup (spinGroup (realSpinorQuadraticForm m)) := by
  /- Stage 1: in the finite real exterior coordinates the Clifford product is
  a bilinear map between finite-dimensional real vector spaces. Its structure
  coefficients are fixed real numbers, so multiplication is jointly continuous.
  Stage 2: native spin inversion is Clifford conjugation. This is a real-linear
  map of the same finite-dimensional algebra and is continuous. Both product
  and inverse restrict to the native subgroup, whose topology is exactly the
  induced subspace topology. These restrictions give the topological-group
  axioms, without quotienting by the kernel of the vector representation. -/
  let : FiniteDimensional ℝ (CliffordAlgebra (realSpinorQuadraticForm m)) :=
    FiniteDimensional.of_injective (realSpinorCliffordCoordinates m).toLinearMap
      (realSpinorCliffordCoordinates m).injective
  -- The original Clifford product is jointly continuous by finite-dimensional bilinearity.
  let product : CliffordAlgebra (realSpinorQuadraticForm m) →ₗ[ℝ]
      CliffordAlgebra (realSpinorQuadraticForm m) →L[ℝ]
        CliffordAlgebra (realSpinorQuadraticForm m) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      (LinearMap.mul ℝ (CliffordAlgebra (realSpinorQuadraticForm m)))
  have hproduct : Continuous (fun p : CliffordAlgebra (realSpinorQuadraticForm m) ×
      CliffordAlgebra (realSpinorQuadraticForm m) ↦ p.1 * p.2) :=
    (product.continuous_of_finiteDimensional.comp continuous_fst).clm_apply continuous_snd
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply Continuous.subtype_mk
    exact hproduct.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  · -- Native inversion is the same real-linear Clifford conjugation restricted to the group.
    apply Continuous.subtype_mk
    change Continuous (fun g : spinGroup (realSpinorQuadraticForm m) ↦
      CliffordAlgebra.reverse (CliffordAlgebra.involute (g :
        CliffordAlgebra (realSpinorQuadraticForm m))))
    exact CliffordAlgebra.reverse.continuous_of_finiteDimensional.comp
      (CliffordAlgebra.involute.toLinearMap.continuous_of_finiteDimensional.comp
        continuous_subtype_val)

attribute [local instance] spinGroup_isTopologicalGroup

/-- Joint continuity of the original vector action for the native spin-group topology. -/
theorem continuous_realSpinVectorRepresentation (m : ℕ) :
    Continuous (fun p : spinGroup (realSpinorQuadraticForm m) ×
      EuclideanSpace ℂ (Fin m) ↦ realSpinVectorRepresentation m p.1 p.2) := by
  /- Stage 1: Clifford multiplication, conjugation and the canonical vector
  embedding are continuous in their finite-dimensional real topologies.
  Hence (g,v) -> g*iota(v)*g^{-1} is jointly continuous in the original algebra.
  Stage 2: the native spin condition keeps this value in the original vector
  image. The injective real-linear embedding identifies that image with the
  Euclidean real vector space by a continuous linear equivalence. Transport
  through precisely realSpinorVectorEmbeddingEquiv gives the previously
  defined vector representation. No new action or topology is chosen. -/
  let : FiniteDimensional ℝ (CliffordAlgebra (realSpinorQuadraticForm m)) :=
    FiniteDimensional.of_injective (realSpinorCliffordCoordinates m).toLinearMap
      (realSpinorCliffordCoordinates m).injective
  -- Use the original Clifford product and the native continuous group inverse.
  let product : CliffordAlgebra (realSpinorQuadraticForm m) →ₗ[ℝ]
      CliffordAlgebra (realSpinorQuadraticForm m) →L[ℝ]
        CliffordAlgebra (realSpinorQuadraticForm m) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      (LinearMap.mul ℝ (CliffordAlgebra (realSpinorQuadraticForm m)))
  have hproduct : Continuous (fun p : CliffordAlgebra (realSpinorQuadraticForm m) ×
      CliffordAlgebra (realSpinorQuadraticForm m) ↦ p.1 * p.2) :=
    (product.continuous_of_finiteDimensional.comp continuous_fst).clm_apply continuous_snd
  have hg : Continuous (fun p : spinGroup (realSpinorQuadraticForm m) ×
      EuclideanSpace ℂ (Fin m) ↦ (p.1 : CliffordAlgebra (realSpinorQuadraticForm m))) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun p : spinGroup (realSpinorQuadraticForm m) ×
      EuclideanSpace ℂ (Fin m) ↦ CliffordAlgebra.ι (realSpinorQuadraticForm m) p.2) :=
    (CliffordAlgebra.ι (realSpinorQuadraticForm m)).continuous_of_finiteDimensional.comp
      continuous_snd
  have hinv : Continuous (fun p : spinGroup (realSpinorQuadraticForm m) ×
      EuclideanSpace ℂ (Fin m) ↦ ((p.1⁻¹ : spinGroup (realSpinorQuadraticForm m)) :
        CliffordAlgebra (realSpinorQuadraticForm m))) :=
    continuous_subtype_val.comp (continuous_inv.comp continuous_fst)
  -- The specified injective linear vector map is an embedding for these exact topologies.
  have hinjective : Function.Injective (CliffordAlgebra.ι (realSpinorQuadraticForm m)) := by
    intro v w hvw
    apply (realSpinorVectorEmbeddingEquiv m).injective
    exact Subtype.ext hvw
  have hembedding := LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr hinjective)
  apply hembedding.isEmbedding.continuous_iff.mpr
  change Continuous (fun p : spinGroup (realSpinorQuadraticForm m) ×
    EuclideanSpace ℂ (Fin m) ↦ CliffordAlgebra.ι (realSpinorQuadraticForm m)
      (realSpinVectorRepresentation m p.1 p.2))
  simp_rw [(realSpinVectorRepresentation_properties m _ _).1]
  exact hproduct.comp ((hproduct.comp (hg.prodMk hv)).prodMk hinv)

attribute [local instance] exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace

/-- Joint continuity of the same complex spin action on the original exterior spinor space. -/
theorem continuous_complexSpinRepresentation (m : ℕ) :
    Continuous (fun p : spinGroup (realSpinorQuadraticForm m) × ComplexSpinor m ↦
      complexSpinRepresentation m p.1 p.2) := by
  /- Stage 1: realSpinorRepresentation is a real-linear map from the original
  finite-dimensional Clifford algebra to the complex endomorphisms of the
  original finite-dimensional exterior algebra, considered as a real space.
  In the fixed finite coordinates this map and endomorphism evaluation are
  continuous, so their composite is jointly continuous.
  Stage 2: restricting its first input to the spin subgroup gives exactly
  complexSpinRepresentation, since the units-map construction retains the
  same underlying endomorphism. This checks joint continuity, which the
  type ContRepresentation by itself does not require. -/
  let : FiniteDimensional ℝ (CliffordAlgebra (realSpinorQuadraticForm m)) :=
    FiniteDimensional.of_injective (realSpinorCliffordCoordinates m).toLinearMap
      (realSpinorCliffordCoordinates m).injective
  -- Attach continuity to the original endomorphism-valued real representation.
  let action : CliffordAlgebra (realSpinorQuadraticForm m) →ₗ[ℝ]
      ComplexSpinor m →L[ℂ] ComplexSpinor m :=
    (LinearMap.toContinuousLinearMap.toLinearMap.restrictScalars ℝ).comp
      (realSpinorRepresentation m).toLinearMap
  have haction : Continuous (fun p : spinGroup (realSpinorQuadraticForm m) × ComplexSpinor m ↦
      action p.1.val p.2) :=
    (action.continuous_of_finiteDimensional.comp
      (continuous_subtype_val.comp continuous_fst)).clm_apply continuous_snd
  -- The units wrapper evaluates by this same endomorphism on every original spinor.
  exact haction

/-- Joint continuity of the original restricted action on either exterior parity subspace. -/
theorem continuous_complexSpinParityRepresentation (m : ℕ) (i : ZMod 2) :
    Continuous (fun p : spinGroup (realSpinorQuadraticForm m) ×
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i ↦
        complexSpinParityRepresentation m i p.1 p.2) := by
  /- Stage 1: include the original parity subspace into the exterior algebra
  and apply the joint continuity of the full spin action. The inclusion is
  continuous for the same induced subspace norm used by ExteriorTopology.
  Stage 2: complexSpinRepresentation_evenOdd keeps the value in that parity
  subspace. The original restricted equivalence is precisely the full action
  with this membership certificate. Continuity into the induced subspace
  proves the claim, including the zero odd space in dimension zero. -/
  -- Include the same parity subspace, apply the full action, and retain its original certificate.
  apply Continuous.subtype_mk
  change Continuous (fun p : spinGroup (realSpinorQuadraticForm m) ×
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i ↦
    complexSpinRepresentation m p.1 p.2.val)
  exact (continuous_complexSpinRepresentation m).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- The original full spin action, with continuity of each operator explicitly attached. -/
def complexSpinContRepresentation (m : ℕ) :
    ContRepresentation ℂ (spinGroup (realSpinorQuadraticForm m)) (ComplexSpinor m) :=
  .ofMonoidHom {
    toFun := fun g ↦ (complexSpinRepresentation m g).toLinearMap.toContinuousLinearMap
    map_one' := by
      -- The continuous wrapper leaves every original linear value unchanged.
      ext s
      change complexSpinRepresentation m 1 s = s
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      ext s
      change complexSpinRepresentation m (g * h) s =
        complexSpinRepresentation m g (complexSpinRepresentation m h s)
      rw [map_mul]
      rfl }

/-- The original half-spin parity action as a representation by continuous linear operators. -/
def complexSpinParityContRepresentation (m : ℕ) (i : ZMod 2) :
    ContRepresentation ℂ (spinGroup (realSpinorQuadraticForm m))
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :=
  .ofMonoidHom {
    toFun := fun g ↦ (complexSpinParityRepresentation m i g).toLinearMap.toContinuousLinearMap
    map_one' := by
      -- The subtype operator still acts on the identical original parity vector.
      apply ContinuousLinearMap.ext
      intro s
      change complexSpinParityRepresentation m i 1 s = s
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply ContinuousLinearMap.ext
      intro s
      change complexSpinParityRepresentation m i (g * h) s =
        complexSpinParityRepresentation m i g (complexSpinParityRepresentation m i h s)
      rw [map_mul]
      rfl }

end AtiyahSinger
