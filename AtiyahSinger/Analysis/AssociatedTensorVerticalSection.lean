/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorSectionDescent
public import AtiyahSinger.Analysis.AssociatedTensorVerticalCovariance

/-!
# The actual associated vertical section operator

Public module ID: M0213.

The specified equivariant sphere operator on every whole fiber descends to
one linear map into sections of the original associated tensor bundle. Its
value is exactly the existing vertical family at every principal point.
This module constructs the actual section and its linearity; joint PDO
regularity supplies its separate smooth-section realization.
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
set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full original vertical family descends to an actual linear section operator. -/
theorem exists_associatedSphereTensorVerticalSectionOperator
    (L : A.smoothSections →ₗ[ℂ] A'.smoothSections)
    (hL : ∀ g : G,
      L.comp (σ.atlasSmoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) A hσ g) =
        (σ'.atlasSmoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) A' hσ' g).comp L) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∃ V : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections →ₗ[ℂ]
        (∀ z : Z, T' z),
      ∀ (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections)
        (p : P) (y : OrthogonalSphere r),
        V w (associatedBundleMk G P (OrthogonalSphere r) p y) =
          associatedSphereTensorFiberEquiv S E σ' p y
            ((associatedSphereTensorVerticalFamilyOperator (a := a) S E A σ hσ A' L w p).val
              y) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let F := associatedSphereTensorVerticalFamilyOperator (a := a) S E A σ hσ A' L
  have hexists (w : AT.smoothSections) : ∃! s : ∀ z : Z, T' z,
      ∀ (p : P) (y : OrthogonalSphere r),
        s (associatedBundleMk G P (OrthogonalSphere r) p y) =
          associatedSphereTensorFiberEquiv S E σ' p y ((F w p).val y) :=
    existsUnique_associatedSphereTensorSection_of_covariant S E σ'
      (fun p y ↦ (F w p).val y)
      (fun p g y ↦ associatedSphereTensorVerticalFamilyOperator_smul (a := a)
        S E A σ hσ A' σ' hσ' L hL p g y w)
  let v (w : AT.smoothSections) : ∀ z : Z, T' z := (hexists w).choose
  have hv (w : AT.smoothSections) (p : P) (y : OrthogonalSphere r) :
      v w (associatedBundleMk G P (OrthogonalSphere r) p y) =
        associatedSphereTensorFiberEquiv S E σ' p y ((F w p).val y) :=
    (hexists w).choose_spec.1 p y
  -- Equality at every original representative proves the algebraic laws upstairs.
  let V : AT.smoothSections →ₗ[ℂ] (∀ z : Z, T' z) :=
    { toFun := v
      map_add' w z := by
        funext x
        induction x using Quotient.inductionOn with
        | h x =>
          change v (w + z) (associatedBundleMk G P (OrthogonalSphere r) x.1 x.2) = _
          rw [hv]
          change _ = v w (associatedBundleMk G P (OrthogonalSphere r) x.1 x.2) +
            v z (associatedBundleMk G P (OrthogonalSphere r) x.1 x.2)
          rw [hv, hv, map_add]
          exact map_add _ _ _
      map_smul' c w := by
        funext x
        induction x using Quotient.inductionOn with
        | h x =>
          change v (c • w) (associatedBundleMk G P (OrthogonalSphere r) x.1 x.2) = _
          rw [hv]
          change _ = c • v w (associatedBundleMk G P (OrthogonalSphere r) x.1 x.2)
          rw [hv, map_smul]
          exact (associatedSphereTensorFiberEquiv S E σ' x.1 x.2).map_smul
            c ((F w x.1).val x.2) }
  exact ⟨V, hv⟩

end AtiyahSinger
