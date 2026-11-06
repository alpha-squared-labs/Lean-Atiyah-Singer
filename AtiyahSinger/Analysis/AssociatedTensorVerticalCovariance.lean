/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorFiberCovariance
public import AtiyahSinger.Analysis.AssociatedTensorVerticalKernel

/-!
# Covariance of the actual whole vertical family

Public module ID: M0197.

The original equivariant sphere operator commutes with changing the principal
representative of each whole-fiber restriction. Finite tensor evaluation
preserves the exact sphere action and projection transport. Thus its output
has the same quotient covariance as an actual upstairs tensor section.
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
  [∀ y, Module ℂ (F' y)] [TopologicalSpace (TotalSpace Unit F')]
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')
  (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z


set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified equivariant sphere operator preserves whole-fiber quotient covariance. -/
theorem associatedSphereTensorVerticalFamilyOperator_smul
    (L : A.smoothSections →ₗ[ℂ] A'.smoothSections)
    (hL : ∀ g : G,
      L.comp (σ.atlasSmoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) A hσ g) =
        (σ'.atlasSmoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) A' hσ' g).comp L)
    (p : P) (g : G) (y : OrthogonalSphere r) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections,
      TensorProduct.map
          (LinearEquiv.cast (R := ℂ) (M := E) (S.projection_smul g p)).toLinearMap
          (σ'.linearMap g y)
          ((associatedSphereTensorVerticalFamilyOperator (a := a) S E A σ hσ A' L w
            (MulOpposite.op g • p)).val y) =
        (associatedSphereTensorVerticalFamilyOperator (a := a) S E A σ hσ A' L w p).val
          (g • y) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  intro w
  let U := E (projection (MulOpposite.op g • p))
  let V := E (projection p)
  let e : U →ₗ[ℂ] V :=
    (LinearEquiv.cast (R := ℂ) (M := E) (S.projection_smul g p)).toLinearMap
  let R := σ.atlasSmoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) A hσ g
  let R' := σ'.atlasSmoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) A' hσ' g
  have hR (s : A.smoothSections) (z : OrthogonalSphere r) :
      (R s).val (g • z) = σ.linearMap g z (s.val z) := by
    let transport : ∀ {x z : OrthogonalSphere r}, x = z → F x →ₗ[ℂ] F z :=
      fun {x z} h ↦ by
        subst z
        exact LinearMap.id
    have htransport {x z : OrthogonalSphere r} (h : x = z) (v : F x) :
        (⟨z, transport h v⟩ : TotalSpace Unit F) = ⟨x, v⟩ := by
      subst z
      rfl
    apply TotalSpace.mk_injective (F := Unit) (g • z)
    change (⟨g • z, transport (smul_inv_smul g (g • z))
      (σ.linearMap g (g⁻¹ • (g • z)) (s.val (g⁻¹ • (g • z))))⟩ : TotalSpace Unit F) = _
    exact (htransport _ _).trans (congrArg
      (fun x ↦ (⟨g • x, σ.linearMap g x (s.val x)⟩ : TotalSpace Unit F))
      (inv_smul_smul g z))
  have hR' (s : A'.smoothSections) (z : OrthogonalSphere r) :
      (R' s).val (g • z) = σ'.linearMap g z (s.val z) := by
    let transport : ∀ {x z : OrthogonalSphere r}, x = z → F' x →ₗ[ℂ] F' z :=
      fun {x z} h ↦ by
        subst z
        exact LinearMap.id
    have htransport {x z : OrthogonalSphere r} (h : x = z) (v : F' x) :
        (⟨z, transport h v⟩ : TotalSpace Unit F') = ⟨x, v⟩ := by
      subst z
      rfl
    apply TotalSpace.mk_injective (F := Unit) (g • z)
    change (⟨g • z, transport (smul_inv_smul g (g • z))
      (σ'.linearMap g (g⁻¹ • (g • z)) (s.val (g⁻¹ • (g • z))))⟩ : TotalSpace Unit F') = _
    exact (htransport _ _).trans (congrArg
      (fun x ↦ (⟨g • x, σ'.linearMap g x (s.val x)⟩ : TotalSpace Unit F'))
      (inv_smul_smul g z))
  let v := associatedSphereTensorFiberRestriction (a := a) S E A σ hσ
    (MulOpposite.op g • p) w
  let z := associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w
  obtain ⟨t, ht⟩ := (tensorSectionEquiv U A.smoothSections).surjective v
  -- The original input covariance identifies one actual algebraic tensor, including its action.
  have heval (t : U ⊗[ℂ] A.smoothSections) (x : OrthogonalSphere r) :
      (tensorSectionEquiv V A.smoothSections (TensorProduct.map e R t)).val (g • x) =
        TensorProduct.map e (σ.linearMap g x)
          ((tensorSectionEquiv U A.smoothSections t).val x) := by
    induction t using TensorProduct.inductionOn with
    | tmul u s =>
      change e u ⊗ₜ[ℂ] (R s).val (g • x) = e u ⊗ₜ[ℂ] σ.linearMap g x (s.val x)
      rw [hR]
    | add t t' ht ht' =>
      simpa only [map_add, Submodule.coe_add, Pi.add_apply] using congrArg₂ (· + ·) ht ht'
  have hz : z = tensorSectionEquiv V A.smoothSections (TensorProduct.map e R t) := by
    apply Subtype.ext
    funext x
    obtain ⟨x, rfl⟩ := (MulAction.bijective g).surjective x
    rw [heval, ht]
    exact (associatedSphereTensorFiberRestriction_smul (a := a)
      S E A σ hσ p g x w).symm
  have heval' (t : U ⊗[ℂ] A'.smoothSections) (x : OrthogonalSphere r) :
      (tensorSectionEquiv V A'.smoothSections (TensorProduct.map e R' t)).val (g • x) =
        TensorProduct.map e (σ'.linearMap g x)
          ((tensorSectionEquiv U A'.smoothSections t).val x) := by
    induction t using TensorProduct.inductionOn with
    | tmul u s =>
      change e u ⊗ₜ[ℂ] (R' s).val (g • x) = e u ⊗ₜ[ℂ] σ'.linearMap g x (s.val x)
      rw [hR']
    | add t t' ht ht' =>
      simpa only [map_add, Submodule.coe_add, Pi.add_apply] using congrArg₂ (· + ·) ht ht'
  -- Apply exactly the supplied equivariance relation before evaluating the output tensor.
  have hcomm (t : U ⊗[ℂ] A.smoothSections) :
      (L.lTensor V) (TensorProduct.map e R t) =
      TensorProduct.map e R' ((L.lTensor U) t) := by
    induction t using TensorProduct.inductionOn with
    | tmul u s =>
      change e u ⊗ₜ[ℂ] L (R s) = e u ⊗ₜ[ℂ] R' (L s)
      exact congrArg (fun v ↦ e u ⊗ₜ[ℂ] v) (congrArg (fun M ↦ M s) (hL g))
    | add t t' ht ht' =>
      simpa only [map_add] using congrArg₂ (· + ·) ht ht'
  change TensorProduct.map e (σ'.linearMap g y)
      ((tensorSectionOperator U A.smoothSections A'.smoothSections L v).val y) =
    (tensorSectionOperator V A.smoothSections A'.smoothSections L z).val (g • y)
  rw [← ht, hz]
  simp only [tensorSectionOperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rw [hcomm, heval']

end AtiyahSinger
