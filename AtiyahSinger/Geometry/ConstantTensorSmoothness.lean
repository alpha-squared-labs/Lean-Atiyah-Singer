/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FiniteTensorSections
public import AtiyahSinger.Geometry.SmoothTensorAtlas

/-!
# Smoothness of tensor sections with a constant finite coefficient

In an actual constant bundle with a specified global constant frame, a tensor
section is smooth exactly when every dual contraction is a smooth section of
the other factor. The tensor atlas, its topology and all original fibers are
retained. Other charts of the constant bundle may vary with the base point.

The global frame is used only for finite reconstruction. This is the local
coefficient test for the actual horizontal lift and the vertical kernel in
SG III.13.6, not an assertion about infinite-dimensional weak smoothness.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

variable {n : ℕ} {M U : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [AddCommGroup U] [Module ℂ U]
  [TopologicalSpace (TotalSpace Unit (fun _ : M ↦ U))]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

attribute [local instance] ComplexBundle.tensorTopology

set_option maxSynthPendingDepth 20 in
/-- In the original tensor atlas, all finite dual contractions detect smooth sections. -/
theorem isSmoothSection_tensor_iff_of_constant_frame
    (C : SmoothComplexBundleAtlas (n := n) (fun _ : M ↦ U))
    (A : SmoothComplexBundleAtlas (n := n) E)
    (i₀ : C.Index) (hbase : (C.chart i₀).baseSet = Set.univ)
    (e : U ≃ₗ[ℂ] (Fin (C.rank i₀) → ℂ))
    (hcoord : ∀ (x : M) (v : U), (C.chart i₀ ⟨x, v⟩).2 = e v)
    (w : ∀ x, U ⊗[ℂ] E x) :
    (tensorSmoothAtlas C A).IsSmoothSection w ↔
      ∀ l : U →ₗ[ℂ] ℂ, A.IsSmoothSection
        (fun x ↦ TensorProduct.lid ℂ (E x) (TensorProduct.map l LinearMap.id (w x))) := by
  classical
  let b (i : Fin (C.rank i₀)) : U := e.symm (Pi.single i 1)
  let l (i : Fin (C.rank i₀)) : U →ₗ[ℂ] ℂ :=
    (LinearMap.proj i).comp e.toLinearMap
  let c (φ : U →ₗ[ℂ] ℂ) (x : M) (v : U ⊗[ℂ] E x) : E x :=
    TensorProduct.lid ℂ (E x) (TensorProduct.map φ LinearMap.id v)
  have hsum (v : U) : (∑ i, e v i • b i) = v := by
    apply e.injective
    simp only [map_sum, map_smul, b, LinearEquiv.apply_symm_apply]
    funext k
    simp [Pi.single_apply]
  have hdecomp (x : M) (v : U ⊗[ℂ] E x) :
      (∑ i, b i ⊗ₜ[ℂ] c (l i) x v) = v := by
    induction v using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [c, l, TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.proj_apply,
        LinearEquiv.coe_coe, LinearMap.id_apply, TensorProduct.lid_tmul,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, hsum]
    | add u v hu hv =>
      simp only [c, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib] at *
      exact congrArg₂ (· + ·) hu hv
  let T := tensorSmoothAtlas C A
  have hspec (i : C.Index) (j : A.Index) :=
    (ComplexBundle.exists_tensor_trivialization (C.chart i) (A.chart j)
      (C.linear i) (A.linear j)).choose_spec
  constructor
  · intro hw φ j
    have hdomain : (T.chart (i₀, j)).baseSet = (A.chart j).baseSet := by
      exact (hspec i₀ j).1.trans (by rw [hbase, Set.univ_inter])
    have hformula (x : M) (hx : x ∈ (A.chart j).baseSet) (v : U ⊗[ℂ] E x)
        (k : Fin (A.rank j)) :
        (A.chart j ⟨x, c φ x v⟩).2 k =
          ∑ i, φ (b i) * (T.chart (i₀, j) ⟨x, v⟩).2 (finProdFinEquiv (i, k)) := by
      have hx₀ : x ∈ (C.chart i₀).baseSet := hbase.symm ▸ Set.mem_univ x
      induction v using TensorProduct.inductionOn with
      | tmul u v =>
        have hφ : φ u = ∑ i, e u i * φ (b i) := by
          have h := congrArg φ (hsum u)
          simpa only [map_sum, map_smul, smul_eq_mul] using h.symm
        simp only [c, TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul]
        change ((A.frameLinearEquiv j x hx) (φ u • v)) k = _
        rw [map_smul]
        change φ u * (A.chart j ⟨x, v⟩).2 k = _
        rw [hφ, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        have h := (hspec i₀ j).2.2 x ⟨hx₀, hx⟩ u v i k
        change (T.chart (i₀, j) ⟨x, u ⊗ₜ[ℂ] v⟩).2 _ = _ at h
        rw [h, hcoord]
        ring
      | add u v hu hv =>
        have hA := (A.linear j x hx).map_add (c φ x u) (c φ x v)
        have hT := (T.linear (i₀, j) x (hdomain.symm ▸ hx)).map_add u v
        simp only [c, map_add] at hA ⊢
        rw [hA, hT]
        change (A.chart j ⟨x, c φ x u⟩).2 k + (A.chart j ⟨x, c φ x v⟩).2 k =
          ∑ i, φ (b i) * ((T.chart (i₀, j) ⟨x, u⟩).2 (finProdFinEquiv (i, k)) +
            (T.chart (i₀, j) ⟨x, v⟩).2 (finProdFinEquiv (i, k)))
        rw [hu, hv]
        simp only [mul_add, Finset.sum_add_distrib]
    apply contMDiffOn_pi_space.mpr
    intro k
    have hsmooth : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
        (fun x ↦ ∑ i, φ (b i) * (T.chart (i₀, j) ⟨x, w x⟩).2
          (finProdFinEquiv (i, k))) (A.chart j).baseSet := by
      apply contMDiffOn_finsetSum
      intro i _
      have h := (contMDiffOn_pi_space.mp (hw (i₀, j))) (finProdFinEquiv (i, k))
      rw [hdomain] at h
      exact (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
        (contMDiffOn_const.prodMk_space h)
    exact hsmooth.congr (fun x hx ↦ hformula x hx (w x) k)
  · intro hw
    -- The same global frame vectors are smooth in every chart of the constant bundle.
    have hb (i : Fin (C.rank i₀)) : C.IsSmoothSection (fun _ ↦ b i) := by
      intro j
      have h := C.contMDiffOn_coordChange i₀ j i
      rw [hbase, Set.univ_inter] at h
      apply h.congr
      intro x _
      have hx : x ∈ (C.chart i₀).baseSet := hbase.symm ▸ Set.mem_univ x
      have heq : C.chart i₀ ⟨x, b i⟩ = (x, Pi.single i 1) := by
        apply Prod.ext
        · exact (C.chart i₀).proj_toFun _ ((C.chart i₀).mem_source.mpr hx)
        · rw [hcoord]
          exact e.apply_symm_apply _
      rw [← heq]
      have hpoint := (C.chart i₀).toPartialEquiv.left_inv
        (x := (⟨x, b i⟩ : TotalSpace Unit (fun _ : M ↦ U)))
        ((C.chart i₀).mem_source.mpr hx)
      exact (congrArg (fun z : TotalSpace Unit (fun _ : M ↦ U) ↦
        (C.chart j z).2) hpoint).symm
    have hterms (i : Fin (C.rank i₀)) :
        T.IsSmoothSection (fun x ↦ b i ⊗ₜ[ℂ] c (l i) x (w x)) :=
      isSmoothSection_tensor C A ⟨fun _ ↦ b i, hb i⟩ ⟨_, hw (l i)⟩
    have htotal : (fun x ↦ ∑ i, b i ⊗ₜ[ℂ] c (l i) x (w x)) ∈ T.smoothSections := by
      have h := T.smoothSections.sum_mem (fun i (_ : i ∈ Finset.univ) ↦ hterms i)
      have hsumFun : (∑ i, fun x ↦ b i ⊗ₜ[ℂ] c (l i) x (w x)) =
          (fun x ↦ ∑ i, b i ⊗ₜ[ℂ] c (l i) x (w x)) := by
        funext x
        exact map_sum (LinearMap.proj x : (∀ x, U ⊗[ℂ] E x) →ₗ[ℂ] U ⊗[ℂ] E x)
          (fun i x ↦ b i ⊗ₜ[ℂ] c (l i) x (w x)) Finset.univ
      rwa [hsumFun] at h
    have heq : (fun x ↦ ∑ i, b i ⊗ₜ[ℂ] c (l i) x (w x)) = w :=
      funext (fun x ↦ hdecomp x (w x))
    rwa [heq] at htotal

end AtiyahSinger
