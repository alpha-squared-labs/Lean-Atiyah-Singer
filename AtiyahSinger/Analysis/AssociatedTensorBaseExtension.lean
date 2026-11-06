/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereTensorBundle

/-!
# Returning a base tensor family through its original principal chart

Public module ID: M0133.

The normalized principal representative places a whole sphere/base tensor
family back into the original associated fibers. The return map is linear
and is zero outside the original principal chart. This raw construction
keeps the original base factor and actual quotient vector; smoothness of a
supported family is supplied separately.
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
/-- Return the whole normalized tensor family through the original principal chart. -/
def associatedSphereTensorBaseExtension (b : B) :
    (∀ y : OrthogonalSphere r, ∀ x : B, F y ⊗[ℂ] E x) →ₗ[ℂ] ∀ z : Z, T z := by
  classical
  let principal := S.trivialization b
  let t := associatedSphereTrivialization S b
  have hbase : t.baseSet = principal.baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      principal (S.equivariant b)).choose_spec.1
  exact LinearMap.pi fun z ↦
    if hz : z ∈ t.source then by
      let p := principal.toOpenPartialHomeomorph.symm (q z, 1)
      let y := (t z).2
      have hx : q z ∈ principal.baseSet := hbase ▸ t.mem_source.mp hz
      have hinverse : t.toOpenPartialHomeomorph.symm (q z, y) =
          associatedBundleMk G P (OrthogonalSphere r) p y :=
        (exists_associatedBundleTrivialization S.toIsPrincipalBundle
          principal (S.equivariant b)).choose_spec.2.2 (q z) y hx
      have hpair : (q z, y) = t z := Prod.ext (t.proj_toFun z hz).symm rfl
      have hpoint : associatedBundleMk G P (OrthogonalSphere r) p y = z :=
        hinverse.symm.trans ((congrArg t.toOpenPartialHomeomorph.symm hpair).trans
          (t.toOpenPartialHomeomorph.left_inv hz))
      let c : F y →ₗ[ℂ] D z :=
        (associatedEquivariantFiberMk_isLinear S.toIsPrincipalBundle σ p y hpoint).mk'
      let evalY : (∀ y : OrthogonalSphere r, ∀ x : B, F y ⊗[ℂ] E x) →ₗ[ℂ]
          ∀ x : B, F y ⊗[ℂ] E x := LinearMap.proj y
      let evalX : (∀ x : B, F y ⊗[ℂ] E x) →ₗ[ℂ] F y ⊗[ℂ] E (q z) := LinearMap.proj (q z)
      exact (TensorProduct.map LinearMap.id c).comp
        ((TensorProduct.comm ℂ (F y) (E (q z))).toLinearMap.comp (evalX.comp evalY))
    else 0

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Returning through the same principal chart preserves every original tensor coordinate. -/
theorem associatedSphereTensorBaseExtension_coordinate
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (e : Trivialization (EuclideanSpace ℂ (Fin a))
      (π (EuclideanSpace ℂ (Fin a)) E)) (he : MemTrivializationAtlas e)
    (j : A.Index) (z : Z) (hz : z ∈ (associatedSphereTrivialization S b).source)
    (hx : q z ∈ e.baseSet)
    (hy : (associatedSphereTrivialization S b z).2 ∈ (A.chart j).baseSet)
    (i : Fin a) (k : Fin (A.rank j))
    (u : ∀ y : OrthogonalSphere r, ∀ x : B, F y ⊗[ℂ] E x) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let y := (associatedSphereTrivialization S b z).2
    let l := (LinearMap.proj k).comp (A.frameLinearEquiv j y hy).toLinearMap
    ((associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).chart (⟨e, he⟩, (b, j))
      ⟨z, associatedSphereTensorBaseExtension S E σ b u z⟩).2 (finProdFinEquiv (i, k)) =
      (e ⟨q z, TensorProduct.lid ℂ (E (q z))
        (TensorProduct.map l LinearMap.id (u y (q z)))⟩).2 i := by
  as_aux_lemma =>
    classical
    let := he
    let := modelTopology (EuclideanSpace ℂ (Fin a)) E
    let : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    let := associatedSphereChartedSpace S
    let lm := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
    let d := linearModelDiffeomorph lm Z
    let := linearModelChartedSpace lm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AD := associatedSphereSmoothBundleAtlas S A σ hσ
    let AE := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
    have hq : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ q :=
      (smoothAssociatedSphereProjection S).contMDiff.comp d.symm.contMDiff
    let AC := AE.pullback q hq
    let principal := S.trivialization b
    let t := associatedSphereTrivialization S b
    let p := principal.toOpenPartialHomeomorph.symm (q z, 1)
    let y := (t z).2
    let l := (LinearMap.proj k).comp (A.frameLinearEquiv j y hy).toLinearMap
    have hb : t.baseSet = principal.baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        principal (S.equivariant b)).choose_spec.1
    have hxb : q z ∈ principal.baseSet := hb ▸ t.mem_source.mp hz
    have hpx : projection p = q z := principal.proj_symm_apply' hxb
    have hp : projection p ∈ principal.baseSet := hpx.symm ▸ hxb
    have hg : (principal p).2 = 1 := congrArg Prod.snd (principal.apply_symm_apply' hxb)
    have hinverse : t.toOpenPartialHomeomorph.symm (q z, y) =
        associatedBundleMk G P (OrthogonalSphere r) p y :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        principal (S.equivariant b)).choose_spec.2.2 (q z) y hxb
    have hpair : (q z, y) = t z := Prod.ext (t.proj_toFun z hz).symm rfl
    have hpoint : associatedBundleMk G P (OrthogonalSphere r) p y = z :=
      hinverse.symm.trans ((congrArg t.toOpenPartialHomeomorph.symm hpair).trans
        (t.toOpenPartialHomeomorph.left_inv hz))
    let c : F y →ₗ[ℂ] D z :=
      (associatedEquivariantFiberMk_isLinear S.toIsPrincipalBundle σ p y hpoint).mk'
    have hDbase : z ∈ (AD.chart (b, j)).baseSet := by
      have hbase : (AD.chart (b, j)).baseSet =
          t.source ∩ t ⁻¹' (Set.univ ×ˢ (A.chart j).baseSet) :=
        (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
          principal (S.equivariant b) (A.chart j) (A.linear j)).choose_spec.1
      exact hbase.symm ▸ ⟨hz, Set.mem_univ _, hy⟩
    have hEbase : z ∈ (AC.chart ⟨e, he⟩).baseSet := by
      have hbase : (AC.chart ⟨e, he⟩).baseSet = q ⁻¹' e.baseSet :=
        (AE.exists_pullbackChart q ⟨e, he⟩).choose_spec.1
      exact hbase.symm ▸ hx
    have hTbase : z ∈ (AT.chart (⟨e, he⟩, (b, j))).baseSet :=
      (exists_tensor_trivialization (AC.chart ⟨e, he⟩) (AD.chart (b, j))
        (AC.linear ⟨e, he⟩) (AD.linear (b, j))).choose_spec.1.symm ▸ ⟨hEbase, hDbase⟩
    let lT : T z →ₗ[ℂ] ℂ := (LinearMap.proj (finProdFinEquiv (i, k))).comp
      (AT.linear (⟨e, he⟩, (b, j)) z hTbase).mk'
    let lE : E (q z) →ₗ[ℂ] ℂ := (LinearMap.proj i).comp
      ((EuclideanSpace.equiv (Fin a) ℂ).toLinearMap.comp (e.linearEquivAt ℂ (q z) hx).toLinearMap)
    let forward : F y ⊗[ℂ] E (q z) →ₗ[ℂ] T z :=
      (TensorProduct.map LinearMap.id c).comp (TensorProduct.comm ℂ (F y) (E (q z))).toLinearMap
    have hlinear : lT.comp forward = lE.comp
        ((TensorProduct.lid ℂ (E (q z))).toLinearMap.comp (TensorProduct.map l LinearMap.id)) := by
      -- Equality on pure tensors proves the full coordinate identity by linearity.
      apply TensorProduct.ext'
      intro v w
      change (AT.chart (⟨e, he⟩, (b, j)) ⟨z, w ⊗ₜ[ℂ] c v⟩).2
        (finProdFinEquiv (i, k)) = (e ⟨q z, l v • w⟩).2 i
      have h := (exists_tensor_trivialization (AC.chart ⟨e, he⟩) (AD.chart (b, j))
        (AC.linear ⟨e, he⟩) (AD.linear (b, j))).choose_spec.2.2
          z ⟨hEbase, hDbase⟩ w (c v) i k
      change (AT.chart (⟨e, he⟩, (b, j)) ⟨z, w ⊗ₜ[ℂ] c v⟩).2 _ = _ at h
      have hEc := congrFun ((AE.exists_pullbackChart q ⟨e, he⟩).choose_spec.2
        (⟨z, w⟩ : TotalSpace Unit ((q : Z → B) *ᵖ E))) i
      change (AC.chart ⟨e, he⟩ ⟨z, w⟩).2 i = (e ⟨q z, w⟩).2 i at hEc
      have hDc : (AD.chart (b, j) ⟨z, c v⟩).2 k = (A.chart j ⟨y, v⟩).2 k := by
        have h : (AD.chart (b, j) ⟨z, c v⟩).2 =
            (A.chart j ⟨(principal p).2 • y, σ.linearMap (principal p).2 y v⟩).2 :=
          (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
            principal (S.equivariant b) (A.chart j) (A.linear j)).choose_spec.2.2
              p y z hpoint v hp
        rw [hg] at h
        exact congrFun (h.trans (congrArg (fun v : TotalSpace Unit F ↦ (A.chart j v).2)
          (σ.one_map y v))) k
      have hE := congrArg (fun v : EuclideanSpace ℂ (Fin a) ↦ v i)
        ((e.linearEquivAt ℂ (q z) hx).map_smul (l v) w)
      change (e ⟨q z, l v • w⟩).2 i = l v * (e ⟨q z, w⟩).2 i at hE
      rw [h, hEc, hDc, hE]
      exact mul_comm _ _
    have hraw : associatedSphereTensorBaseExtension S E σ b u z = forward (u y (q z)) := by
      simp only [associatedSphereTensorBaseExtension, LinearMap.pi_apply, dite_eq_left hz,
        LinearMap.comp_apply, LinearMap.proj_apply]
      rfl
    rw [hraw]
    exact LinearMap.congr_fun hlinear (u y (q z))

end AtiyahSinger
