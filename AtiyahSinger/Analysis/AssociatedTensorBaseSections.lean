/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorBaseSmoothness

/-!
# Original base slices as smooth tensor sections

Public module ID: M0137.

Every dual contraction of the actual principal-chart base family is a smooth
section of the original base bundle. The finite original sphere frame proves
this for arbitrary duals, while its joint smoothness is retained separately.
The resulting map is the unchanged raw family with its smoothness certificate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

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

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same normalized base family, certified in the original smooth section space. -/
def associatedSphereTensorCutoffBaseRestriction
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ y : OrthogonalSphere r,
      (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections →ₗ[ℂ]
        dualTensorSections (F y) (smoothSections (n := n) (r := a) E) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let R := associatedSphereTensorCutoffBaseFamily (a := a) S E A σ hσ b χ
  intro y
  refine (R y).codRestrict (dualTensorSections (F y) (smoothSections E)) ?_
  intro w φ
  obtain ⟨j, hy⟩ := A.covers y
  let e := A.frameLinearEquiv j y hy
  let v (k : Fin (A.rank j)) : F y := e.symm (Pi.single k 1)
  let l (k : Fin (A.rank j)) (z : OrthogonalSphere r) : F z →ₗ[ℂ] ℂ :=
    if hz : z ∈ (A.chart j).baseSet then
      (LinearMap.proj k).comp (A.frameLinearEquiv j z hz).toLinearMap
    else 0
  have hl (k : Fin (A.rank j)) (z : OrthogonalSphere r)
      (hz : z ∈ (A.chart j).baseSet) :
      l k z = (LinearMap.proj k).comp (A.frameLinearEquiv j z hz).toLinearMap :=
    dite_eq_left hz
  have hly (k : Fin (A.rank j)) (u : F y) : l k y u = e u k := by
    rw [hl k y hy]
    rfl
  -- The original finite frame spans the entire dual, including rank zero.
  have hφ : φ = ∑ k, φ (v k) • l k y := by
    apply LinearMap.ext
    intro u
    have hu : (∑ k, e u k • v k) = u := by
      apply e.injective
      simp only [map_sum, map_smul, v, LinearEquiv.apply_symm_apply]
      funext k
      simp [Pi.single_apply]
    have h := congrArg φ hu
    change φ u = (∑ k, φ (v k) • l k y) u
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hly, smul_eq_mul]
    simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using h.symm
  let C : (F y →ₗ[ℂ] ℂ) →ₗ[ℂ] (∀ x : B, E x) :=
    { toFun ψ := fun x ↦ TensorProduct.lid ℂ (E x)
        (TensorProduct.map ψ LinearMap.id (R y w x))
      map_add' ψ θ := by
        funext x
        simp only [TensorProduct.map_add_left, LinearMap.add_apply, map_add, Pi.add_apply]
      map_smul' c ψ := by
        funext x
        simp only [TensorProduct.map_smul_left, LinearMap.smul_apply, map_smul, Pi.smul_apply,
          RingHom.id_apply] }
  have hs (k : Fin (A.rank j)) : C (l k y) ∈ smoothSections (n := n) (r := a) E := by
    intro c hc
    have h := contMDiffOn_associatedSphereTensorCutoffBaseFamily (a := a)
      S E A σ hσ b χ hχ hχsupport j k (l k) (hl k) c hc w
    have hpair : ContMDiffOn (𝓡 n) ((𝓡 r).prod (𝓡 n)) ∞
        (fun x : B ↦ (y, x)) c.baseSet := contMDiffOn_const.prodMk contMDiffOn_id
    exact h.comp hpair (fun x hx ↦ ⟨hy, hx⟩)
  -- Linearity of dual contraction preserves this finite combination of smooth sections.
  change C φ ∈ smoothSections (n := n) (r := a) E
  rw [hφ, map_sum]
  apply Submodule.sum_mem
  intro k _
  rw [map_smul]
  exact (smoothSections (n := n) (r := a) E).smul_mem (φ (v k)) (hs k)

set_option maxSynthPendingDepth 30 in
/-- Certification changes no value of the original base family. -/
theorem associatedSphereTensorCutoffBaseRestriction_apply
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ (y : OrthogonalSphere r)
      (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections),
      (associatedSphereTensorCutoffBaseRestriction (a := a) S E A σ hσ
        b χ hχ hχsupport y w).val =
          associatedSphereTensorCutoffBaseFamily (a := a) S E A σ hσ b χ y w := by
  intros
  rfl

end AtiyahSinger
