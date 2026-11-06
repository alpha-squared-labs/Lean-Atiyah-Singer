/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalOperator

/-!
# Exact whole-sphere coordinates of the associated vertical operator

Public module ID: M0196.

In the original principal trivialization, each base-frame contraction of the
actual vertical output equals the same complete sphere operator applied to the
input contraction. Arbitrary base multipliers commute with that action. This
coordinate formula is used for vertical Sobolev bounds and local parametrices;
there is no sphere localization or discarded smoothing term.
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

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual vertical operator acts on the exact original whole-sphere coordinates. -/
theorem associatedSphereTensorVerticalOperator_localFiberCoordinates {m : ℝ}
    (Q : AtlasPseudodifferentialOperator A A' m)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (b : B) (e : Trivialization (EuclideanSpace ℂ (Fin a))
      (π (EuclideanSpace ℂ (Fin a)) E)) (he : MemTrivializationAtlas e)
    (i : Fin a) (ρ : B → ℂ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections) (x : B),
      ρ x • associatedSphereTensorLocalFiberCoordinates S E A' b e he i
        (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A' σ' hσ' p
          (associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ w)) x =
      Q.toLinearMap (ρ x • associatedSphereTensorLocalFiberCoordinates S E A b e he i
        (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w) x) := by
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
  let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
  let R := associatedSphereTensorFiberRestriction (a := a) S E A σ hσ
  let R' := associatedSphereTensorFiberRestriction (a := a) S E A' σ' hσ'
  intro w x
  -- Every principal representative sees the same complete tensorized sphere map.
  have hR (p : P) : R' p (V w) =
      tensorSectionOperator (E (projection p)) A.smoothSections A'.smoothSections
        Q.toLinearMap (R p w) := by
    apply Subtype.ext
    funext y
    apply (associatedSphereTensorFiberEquiv S E σ' p y).injective
    rw [associatedSphereTensorFiberRestriction_apply, associatedSphereTensorVerticalOperator_apply]
    rfl
  rw [map_smul]
  apply congrArg (fun v ↦ ρ x • v)
  by_cases hx : x ∈ (S.trivialization b).baseSet ∩ e.baseSet
  · let := he
    let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
    let φ : E (projection p) →ₗ[ℂ] ℂ := (LinearMap.proj i).comp
      ((EuclideanSpace.equiv (Fin a) ℂ).toLinearMap.comp
        ((e.linearEquivAt ℂ x hx.2).toLinearMap.comp
          (LinearEquiv.cast (R := ℂ) (M := E)
            ((S.trivialization b).proj_symm_apply' hx.1)).toLinearMap))
    apply Subtype.ext
    have hc := tensorSectionOperator_contract (E (projection p)) A.smoothSections
      A'.smoothSections Q.toLinearMap (R p w) φ
    simp only [associatedSphereTensorLocalFiberCoordinates, dite_eq_left hx]
    change (fun y ↦ TensorProduct.lid ℂ (F' y)
      (TensorProduct.map φ LinearMap.id ((R' p (V w)).val y))) = _
    rw [hR]
    exact hc
  · -- The original coordinate convention sets both whole-sphere sections to zero here.
    simp only [associatedSphereTensorLocalFiberCoordinates, dite_eq_right hx, map_zero]

end AtiyahSinger
