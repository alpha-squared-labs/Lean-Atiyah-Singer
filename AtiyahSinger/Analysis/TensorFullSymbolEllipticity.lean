/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasFullSymbolEllipticity
public import AtiyahSinger.Analysis.TensorAtlasSymbol
public import AtiyahSinger.Geometry.AtlasFrameTransition

import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Full-symbol ellipticity with the actual coefficient bundle

Public module ID: M1034.

Tensoring with the identity of a smooth finite-rank bundle preserves the
compact-local high-frequency inverse estimate. The two coefficient frames may
be different and have locally varying rank. Their actual reverse transition
is bounded on each compact overlap. No homogeneous representative or positive
coefficient rank is assumed. Source: the coefficient construction in SG III.13.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {E F W : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
  [TopologicalSpace (TotalSpace Unit W)]

attribute [local instance] ComplexBundle.tensorTopology

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4096 in
set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 800000 in

/-- The same tensor symbol retains quantitative full ellipticity, including rank-zero fibers. -/
theorem IsEllipticFullAtlasSymbol.tensorAtlasSymbol
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F)
    (C : SmoothComplexBundleAtlas (n := n) W) {m : ℝ}
    {a : AtlasSymbolFunction (n := n) E F}
    (ha : IsEllipticFullAtlasSymbol A B m a) :
    IsEllipticFullAtlasSymbol (tensorSmoothAtlas A C) (tensorSmoothAtlas B C) m
      (AtiyahSinger.tensorAtlasSymbol a) := by
  classical
  let V (r : ℕ) := EuclideanSpace ℂ (Fin r)
  let model (r s : ℕ) : (V r ⊗[ℂ] V s) ≃L[ℂ] V (r * s) :=
    (((EuclideanSpace.basisFun (Fin r) ℂ).tensorProduct
      (EuclideanSpace.basisFun (Fin s) ℂ)).reindex finProdFinEquiv).repr.toContinuousLinearEquiv
  have hmodel (r s : ℕ) (u : V r) (v : V s) (k : Fin (r * s)) :
      model r s (u ⊗ₜ[ℂ] v) k =
        u (finProdFinEquiv.symm k).1 * v (finProdFinEquiv.symm k).2 := by
    change (((EuclideanSpace.basisFun (Fin r) ℂ).tensorProduct
      (EuclideanSpace.basisFun (Fin s) ℂ)).reindex finProdFinEquiv).repr (u ⊗ₜ[ℂ] v) k = _
    rw [OrthonormalBasis.repr_reindex, OrthonormalBasis.tensorProduct_repr_tmul_apply']
    simp only [EuclideanSpace.basisFun_repr]
    exact mul_comm _ _
  let AT := tensorSmoothAtlas A C
  let BT := tensorSmoothAtlas B C
  intro c hc i j K hKU hK
  change A.Index × C.Index at i
  change B.Index × C.Index at j
  have hbaseA : (AT.chart i).baseSet =
      (A.chart i.1).baseSet ∩ (C.chart i.2).baseSet :=
    (ComplexBundle.exists_tensor_trivialization (A.chart i.1) (C.chart i.2)
      (A.linear i.1) (C.linear i.2)).choose_spec.1
  have hbaseB : (BT.chart j).baseSet =
      (B.chart j.1).baseSet ∩ (C.chart j.2).baseSet :=
    (ComplexBundle.exists_tensor_trivialization (B.chart j.1) (C.chart j.2)
      (B.linear j.1) (C.linear j.2)).choose_spec.1
  have hKA (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ K) :
      c.symm z ∈ (A.chart i.1).baseSet ∩ (C.chart i.2).baseSet :=
    hbaseA ▸ (hKU hz).1.2
  have hKB (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ K) :
      c.symm z ∈ (B.chart j.1).baseSet ∩ (C.chart j.2).baseSet :=
    hbaseB ▸ (hKU hz).2
  -- Keep the original frequency radius; only the inverse constant changes under tensor frames.
  obtain ⟨R, D, hR, hD, hbound⟩ := ha c hc i.1 j.1 K
    (fun z hz ↦ ⟨⟨(hKU hz).1.1, (hKA z hz).1⟩, (hKB z hz).1⟩) hK
  have hback : ContinuousOn (fun z ↦ C.coordChangeL j.2 i.2 (c.symm z)) K :=
    (C.contDiffOn_coordChangeL_comp j.2 i.2 K c.symm
      ((contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hc)).mono
          (fun _ hz ↦ (hKU hz).1.1))
      (fun z hz ↦ ⟨(hKB z hz).2, (hKA z hz).2⟩)).continuousOn
  obtain ⟨D₀, hD₀⟩ := hK.exists_bound_of_continuousOn hback
  let e := model (A.rank i.1) (C.rank i.2)
  let f := model (B.rank j.1) (C.rank j.2)
  let L := ‖e.toContinuousLinearMap‖ *
    (D * max D₀ 0) * ‖f.symm.toContinuousLinearMap‖
  refine ⟨R, L, hR, by dsimp [L]; positivity, ?_⟩
  intro z hz ξ hξ
  obtain ⟨hinv, hnorm⟩ := hbound z hz ξ hξ
  let p := atlasGlobalSymbolInChart A B a c i.1 j.1 z ξ
  let t := C.coordChangeL i.2 j.2 (c.symm z)
  let t' := C.coordChangeL j.2 i.2 (c.symm z)
  let q := atlasGlobalSymbolInChart AT BT (AtiyahSinger.tensorAtlasSymbol a) c i j z ξ
  let q' := e.toContinuousLinearMap.comp
    ((TensorProduct.mapL p.inverse t').comp f.symm.toContinuousLinearMap)
  let a₀ := (A.frameLinearEquiv i.1 (c.symm z) (hKA z hz).1).trans
    (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
  let b₀ := (B.frameLinearEquiv j.1 (c.symm z) (hKB z hz).1).trans
    (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
  let c₀ := (C.frameLinearEquiv i.2 (c.symm z) (hKA z hz).2).trans
    (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
  let c₁ := (C.frameLinearEquiv j.2 (c.symm z) (hKB z hz).2).trans
    (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
  let a₁ := (AT.frameLinearEquiv i (c.symm z) (hKU hz).1.2).trans
    (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
  let b₁ := (BT.frameLinearEquiv j (c.symm z) (hKU hz).2).trans
    (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
  have hta (w : W (c.symm z)) : t (c₀ w) = c₁ w :=
    (C.coordChangeL_apply i.2 j.2 (c.symm z) ⟨(hKA z hz).2, (hKB z hz).2⟩ w).symm
  have htb (w : W (c.symm z)) : t' (c₁ w) = c₀ w :=
    (C.coordChangeL_apply j.2 i.2 (c.symm z) ⟨(hKB z hz).2, (hKA z hz).2⟩ w).symm
  have hleft : t.comp t' = ContinuousLinearMap.id ℂ _ := by
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := c₁.surjective v
    change t (t' (c₁ w)) = c₁ w
    rw [htb, hta]
  have hright : t'.comp t = ContinuousLinearMap.id ℂ _ := by
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := c₀.surjective v
    change t' (t (c₀ w)) = c₀ w
    rw [hta, htb]
  -- The tensor-coordinate identity is checked on genuine tensors in the given fibers.
  have hinput (u : E (c.symm z)) (w : W (c.symm z)) :
      a₁ (u ⊗ₜ[ℂ] w) = e (a₀ u ⊗ₜ[ℂ] c₀ w) := by
    apply PiLp.ext
    intro k
    change a₁ (u ⊗ₜ[ℂ] w) k = model _ _ (a₀ u ⊗ₜ[ℂ] c₀ w) k
    rw [hmodel]
    change ((tensorSmoothAtlas A C).chart i ⟨c.symm z, u ⊗ₜ[ℂ] w⟩).2 k =
      (A.chart i.1 ⟨c.symm z, u⟩).2 (finProdFinEquiv.symm k).1 *
        (C.chart i.2 ⟨c.symm z, w⟩).2 (finProdFinEquiv.symm k).2
    have h := (ComplexBundle.exists_tensor_trivialization (A.chart i.1) (C.chart i.2)
      (A.linear i.1) (C.linear i.2)).choose_spec.2.2 (c.symm z)
        (hKA z hz) u w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    simpa only [tensorSmoothAtlas, tensorBundleChart, Prod.mk.eta,
      Equiv.apply_symm_apply] using h
  have houtput (u : F (c.symm z)) (w : W (c.symm z)) :
      b₁ (u ⊗ₜ[ℂ] w) = f (b₀ u ⊗ₜ[ℂ] c₁ w) := by
    apply PiLp.ext
    intro k
    change b₁ (u ⊗ₜ[ℂ] w) k = model _ _ (b₀ u ⊗ₜ[ℂ] c₁ w) k
    rw [hmodel]
    change ((tensorSmoothAtlas B C).chart j ⟨c.symm z, u ⊗ₜ[ℂ] w⟩).2 k =
      (B.chart j.1 ⟨c.symm z, u⟩).2 (finProdFinEquiv.symm k).1 *
        (C.chart j.2 ⟨c.symm z, w⟩).2 (finProdFinEquiv.symm k).2
    have h := (ComplexBundle.exists_tensor_trivialization (B.chart j.1) (C.chart j.2)
      (B.linear j.1) (C.linear j.2)).choose_spec.2.2 (c.symm z)
        (hKB z hz) u w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    simpa only [tensorSmoothAtlas, tensorBundleChart, Prod.mk.eta,
      Equiv.apply_symm_apply] using h
  have hp (u : E (c.symm z)) : p (a₀ u) =
      b₀ (a (c.symm z) (covectorFromChart c (c.symm z) ξ) u) := by
    dsimp only [p, atlasGlobalSymbolInChart]
    rw [dite_eq_left ⟨(hKA z hz).1, (hKB z hz).1⟩]
    change b₀ (a _ _ (a₀.symm (a₀ u))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hq : q = f.toContinuousLinearMap.comp
      ((TensorProduct.mapL p t).comp e.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := a₁.surjective v
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simpa only [map_add] using congrArg₂ HAdd.hAdd hv hw
    | tmul u w =>
      have hqa : q (a₁ (u ⊗ₜ[ℂ] w)) =
          b₁ (a (c.symm z) (covectorFromChart c (c.symm z) ξ) u ⊗ₜ[ℂ] w) := by
        dsimp only [q, atlasGlobalSymbolInChart]
        rw [dite_eq_left ⟨(hKU hz).1.2, (hKU hz).2⟩]
        change b₁ (AtiyahSinger.tensorAtlasSymbol a _ _ (a₁.symm (a₁ (u ⊗ₜ[ℂ] w)))) = _
        rw [LinearEquiv.symm_apply_apply]
        rfl
      rw [hqa, houtput, hinput]
      change _ = f (TensorProduct.mapL p t (e.symm (e (a₀ u ⊗ₜ[ℂ] c₀ w))))
      rw [ContinuousLinearEquiv.symm_apply_apply, TensorProduct.mapL_tmul, hp, hta]
  -- The inverse uses exactly the inverse original symbol and the reverse frame transition.
  have hqleft : q.comp q' = ContinuousLinearMap.id ℂ _ := by
    rw [hq]
    apply ContinuousLinearMap.ext
    intro v
    change f (TensorProduct.mapL p t
      (e.symm (e (TensorProduct.mapL p.inverse t' (f.symm v))))) = v
    rw [ContinuousLinearEquiv.symm_apply_apply,
      ← ContinuousLinearMap.comp_apply, ← TensorProduct.mapL_comp,
      hinv.self_comp_inverse, hleft, TensorProduct.mapL_id_id,
      ContinuousLinearMap.id_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hqright : q'.comp q = ContinuousLinearMap.id ℂ _ := by
    rw [hq]
    apply ContinuousLinearMap.ext
    intro v
    change e (TensorProduct.mapL p.inverse t'
      (f.symm (f (TensorProduct.mapL p t (e.symm v))))) = v
    rw [ContinuousLinearEquiv.symm_apply_apply,
      ← ContinuousLinearMap.comp_apply, ← TensorProduct.mapL_comp,
      hinv.inverse_comp_self, hright, TensorProduct.mapL_id_id,
      ContinuousLinearMap.id_apply, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨ContinuousLinearMap.IsInvertible.of_inverse hqleft hqright, ?_⟩
  change ‖q.inverse‖ ≤ L * (1 + ‖ξ‖) ^ (-m)
  rw [ContinuousLinearMap.inverse_eq hqleft hqright]
  have htbound : ‖t'‖ ≤ max D₀ 0 := (hD₀ z hz).trans (le_max_left _ _)
  have hnonneg : 0 ≤ (1 + ‖ξ‖) ^ (-m) := Real.rpow_nonneg (by positivity) _
  calc
    ‖q'‖ ≤ ‖e.toContinuousLinearMap‖ *
        (‖TensorProduct.mapL p.inverse t'‖ * ‖f.symm.toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖e.toContinuousLinearMap‖ *
        ((‖p.inverse‖ * ‖t'‖) * ‖f.symm.toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (TensorProduct.norm_mapL_le _ _) (norm_nonneg _))
        (norm_nonneg _)
    _ ≤ ‖e.toContinuousLinearMap‖ *
        (((D * (1 + ‖ξ‖) ^ (-m)) * max D₀ 0) * ‖f.symm.toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul hnorm htbound (norm_nonneg _) (by positivity))
          (norm_nonneg _)) (norm_nonneg _)
    _ = L * (1 + ‖ξ‖) ^ (-m) := by dsimp [L]; ring

end AtiyahSinger
