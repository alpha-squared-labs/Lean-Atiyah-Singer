/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalOperator

/-!
# A Green identity for associated vertical lifts

Public module ID: M0204.

Given equivariant sphere operators satisfying RQ = I - K, their smooth
vertical lifts satisfy the same composition identity. The proof compares full
restrictions at each principal representative and uses the canonical
tensor-section equivalence on the finite base fiber. All three supplied
sphere maps and their complete section actions are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology tensorTopology continuousSMul_orthogonalSphere
  lieGroup_orthogonalGroup

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  {F' : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F' y)]
  [∀ y, Module ℂ (F' y)] [TopologicalSpace (TotalSpace Unit F')] [IsFiniteRank F']
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')
  (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z


local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "T'" => fun z : Z ↦ E (q z) ⊗[ℂ] D' z

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 600000 in

/-- The actual vertical lifts preserve the same complete Green composition identity. -/
theorem associatedSphereTensorVerticalOperator_comp_eq_id_sub {m l t : ℝ}
    (Q : AtlasPseudodifferentialOperator A A' m)
    (R : AtlasPseudodifferentialOperator A' A l)
    (K : AtlasPseudodifferentialOperator A A t)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (hR : R.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ' σ hσ' hσ)
    (hK : K.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ hσ hσ)
    (hidentity : R.toLinearMap.comp Q.toLinearMap = LinearMap.id - K.toLinearMap) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let VQ := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
    let VR := associatedSphereTensorVerticalOperator (a := a) S E A' σ' hσ' A σ hσ R hR
    let VK := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A σ hσ K hK
    VR.comp VQ = LinearMap.id - VK := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  intro VQ VR VK
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
  let restr := associatedSphereTensorFiberRestriction (a := a) S E A σ hσ
  let restr' := associatedSphereTensorFiberRestriction (a := a) S E A' σ' hσ'
  -- First recover the full sphere output in the same principal representative.
  have hrestrict (p : P) (w : AT.smoothSections) :
      restr' p (VQ w) = tensorSectionOperator (E (projection p))
        A.smoothSections A'.smoothSections Q.toLinearMap (restr p w) := by
    apply Subtype.ext
    funext y
    apply (associatedSphereTensorFiberEquiv S E σ' p y).injective
    rw [associatedSphereTensorFiberRestriction_apply,
      associatedSphereTensorVerticalOperator_apply]
    rfl
  -- Tensoring a finite unchanged coefficient preserves the original full map identity.
  have htensor (p : P) (w : dualTensorSections (E (projection p)) A.smoothSections) :
      tensorSectionOperator (E (projection p)) A'.smoothSections A.smoothSections R.toLinearMap
          (tensorSectionOperator (E (projection p)) A.smoothSections A'.smoothSections
            Q.toLinearMap w) =
        w - tensorSectionOperator (E (projection p)) A.smoothSections A.smoothSections
          K.toLinearMap w := by
    obtain ⟨z, rfl⟩ := (tensorSectionEquiv (E (projection p)) A.smoothSections).surjective w
    simp only [tensorSectionOperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rw [← LinearMap.lTensor_comp_apply, hidentity, LinearMap.lTensor_sub,
      LinearMap.sub_apply, LinearMap.lTensor_id_apply, map_sub]
  -- Values at all actual quotient representatives determine the same upstairs smooth section.
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext z
  induction z using Quotient.inductionOn with
  | h z =>
    change (VR (VQ w)).val (associatedBundleMk G P (OrthogonalSphere r) z.1 z.2) =
      w.val (associatedBundleMk G P (OrthogonalSphere r) z.1 z.2) -
        (VK w).val (associatedBundleMk G P (OrthogonalSphere r) z.1 z.2)
    rw [associatedSphereTensorVerticalOperator_apply (a := a) S E A' σ' hσ' A σ hσ R hR,
      associatedSphereTensorVerticalOperator_apply (a := a) S E A σ hσ A σ hσ K hK]
    change associatedSphereTensorFiberEquiv S E σ z.1 z.2
      ((tensorSectionOperator (E (projection z.1)) A'.smoothSections A.smoothSections
        R.toLinearMap (restr' z.1 (VQ w))).val z.2) = _
    rw [hrestrict, htensor]
    change associatedSphereTensorFiberEquiv S E σ z.1 z.2
      ((restr z.1 w).val z.2 - (tensorSectionOperator (E (projection z.1))
        A.smoothSections A.smoothSections K.toLinearMap (restr z.1 w)).val z.2) = _
    rw [map_sub, associatedSphereTensorFiberRestriction_apply]
    rfl

end AtiyahSinger
