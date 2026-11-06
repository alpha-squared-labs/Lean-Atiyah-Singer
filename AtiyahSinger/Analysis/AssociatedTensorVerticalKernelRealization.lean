/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalOperator

/-!
# The full kernel of the actual smooth vertical operator

Public module ID: M0206.

The actual upstairs smooth vertical operator has exactly the kernel of its
original whole-fiber family. Consequently the previously constructed full
associated representation-kernel equivalence identifies this actual kernel,
with the same evaluation map and original finite representation coordinates.
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
set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual smooth vertical kernel is exactly the existing whole-fiber kernel. -/
theorem ker_associatedSphereTensorVerticalOperator {m : ℝ}
    (Q : AtlasPseudodifferentialOperator A A' m)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ') :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ).ker =
      (associatedSphereTensorVerticalFamilyOperator (a := a) S E A σ hσ A'
        Q.toLinearMap).ker := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
  let F := associatedSphereTensorVerticalFamilyOperator (a := a) S E A σ hσ A' Q.toLinearMap
  apply Submodule.ext
  intro w
  change V w = 0 ↔ F w = 0
  constructor
  · intro hw
    funext p
    apply Subtype.ext
    funext y
    apply (associatedSphereTensorFiberEquiv S E σ' p y).injective
    change associatedSphereTensorFiberEquiv S E σ' p y ((F w p).val y) =
      associatedSphereTensorFiberEquiv S E σ' p y 0
    rw [← associatedSphereTensorVerticalOperator_apply, map_zero]
    change (V w).val (associatedBundleMk G P (OrthogonalSphere r) p y) = 0
    rw [hw]
    rfl
  · intro hw
    apply Subtype.ext
    funext z
    induction z using Quotient.inductionOn with
    | h z =>
      change (V w).val (associatedBundleMk G P (OrthogonalSphere r) z.1 z.2) = 0
      rw [associatedSphereTensorVerticalOperator_apply]
      change associatedSphereTensorFiberEquiv S E σ' z.1 z.2 ((F w z.1).val z.2) = 0
      rw [hw]
      exact map_zero _

variable (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))

local notation "C" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original full kernel representation identifies the actual smooth vertical kernel. -/
theorem exists_associatedSphereTensorVerticalKernelRealization {m : ℝ}
    (Q : AtlasPseudodifferentialOperator A A' m)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] Q.toLinearMap.ker)
    (he : ∀ (g : G) (y : OrthogonalSphere r) (v : Fin ρ.dimension → ℂ),
      (e (ρ.representation g v)).val.val (g • y) =
        σ.linearMap g y ((e v).val.val y)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∃ ev : Hom ((q : Z → B) *ᵖ C) D,
      (∀ (p : P) (y : OrthogonalSphere r) (v : Fin ρ.dimension → ℂ),
        ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
            (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((e v).val.val y)) ∧
      ∃ Φ : (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
          (associatedOrthogonalRepresentationAtlas S ρ)).smoothSections ≃ₗ[ℂ]
          (associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ).ker,
        ∀ u z, (Φ u).val.val z =
          TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (q z)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  obtain ⟨ev, hev, Φ, hΦ⟩ := exists_associatedSphereTensorVerticalKernelEquiv (a := a)
    S E A σ hσ A' ρ Q.toLinearMap e he
  have hker := ker_associatedSphereTensorVerticalOperator (a := a)
    S E A σ hσ A' σ' hσ' Q hQ
  refine ⟨ev, hev, Φ.trans (LinearEquiv.ofEq _ _ hker.symm), ?_⟩
  exact hΦ

end AtiyahSinger
