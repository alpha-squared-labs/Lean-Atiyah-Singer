/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.TensorAtlasSymbolSmooth

import all AtiyahSinger.Analysis.TensorAtlasSymbolSmooth

/-!
# Tensoring an arbitrary smooth punctured symbol

Public module ID: M0315.

The coefficient frame transitions and tensor coordinate maps preserve
smoothness of a general symbol. Covector linearity is unnecessary, so the
result applies to the homogeneous PDO coefficient symbols used in the
associated-sphere index argument.

Source: smooth tensor frames, SG III.13.6. The coordinate argument uses the
specified chart comparisons of TensorAtlasSymbolSmooth.
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

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxSynthPendingDepth 30 in
/-- Tensoring with the given bundle identity preserves smoothness of any punctured symbol. -/
theorem IsSmoothOffZeroAtlasSymbol.tensorAtlasSymbol
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F)
    (C : SmoothComplexBundleAtlas (n := n) W)
    (c : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B c) :
    IsSmoothOffZeroAtlasSymbol (tensorSmoothAtlas A C) (tensorSmoothAtlas B C)
      (tensorAtlasSymbol (W := W) c) := by
  classical
  -- Work in the same tensor frames and retain the actual coefficient transition factor.
  let V (r : ℕ) := EuclideanSpace ℂ (Fin r)
  let AT := tensorSmoothAtlas A C
  let BT := tensorSmoothAtlas B C
  have hbaseA (i : AT.Index) :
      (AT.chart i).baseSet = (A.chart i.1).baseSet ∩ (C.chart i.2).baseSet :=
    (ComplexBundle.exists_tensor_trivialization (A.chart i.1) (C.chart i.2)
      (A.linear i.1) (C.linear i.2)).choose_spec.1
  have hbaseB (j : BT.Index) :
      (BT.chart j).baseSet = (B.chart j.1).baseSet ∩ (C.chart j.2).baseSet :=
    (ComplexBundle.exists_tensor_trivialization (B.chart j.1) (C.chart j.2)
      (B.linear j.1) (C.linear j.2)).choose_spec.1
  intro d hd i j
  change A.Index × C.Index at i
  change B.Index × C.Index at j
  let U := atlasSymbolChartDomain AT BT d i j
  have hUA (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ U) :
      d.symm z ∈ (A.chart i.1).baseSet ∩ (C.chart i.2).baseSet := hbaseA i ▸ hz.1.2
  have hUB (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ U) :
      d.symm z ∈ (B.chart j.1).baseSet ∩ (C.chart j.2).baseSet := hbaseB j ▸ hz.2
  -- Smooth compatibility of the base charts is used precisely in the transition factor.
  have htrans : ContDiffOn ℝ ∞ (fun z ↦ C.coordChangeL i.2 j.2 (d.symm z)) U := by
    apply C.contDiffOn_coordChangeL_comp i.2 j.2 U d.symm
    · exact (contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hd)).mono
        (fun _ hz ↦ hz.1.1)
    · intro z hz
      exact ⟨(hUA z hz).2, (hUB z hz).2⟩
  have hsymbol : ContDiffOn ℝ ∞
      (Function.uncurry (atlasGlobalSymbolInChart A B c d i.1 j.1))
      (U ×ˢ {ξ | ξ ≠ 0}) := (hs d hd i.1 j.1).mono (by
    intro z hz
    exact ⟨⟨⟨hz.1.1.1, (hUA z.1 hz.1).1⟩, (hUB z.1 hz.1).1⟩, hz.2⟩)
  let μ := LinearMap.mk₂ ℂ
    (fun (L : V (A.rank i.1) →L[ℂ] V (B.rank j.1))
      (K : V (C.rank i.2) →L[ℂ] V (C.rank j.2)) ↦ TensorProduct.mapL L K)
    (fun _ _ _ ↦ TensorProduct.mapL_add_left _ _ _)
    (fun _ _ _ ↦ TensorProduct.mapL_smul_left _ _ _)
    (fun _ _ _ ↦ TensorProduct.mapL_add_right _ _ _)
    (fun _ _ _ ↦ TensorProduct.mapL_smul_right _ _ _)
  let μc := (μ.mkContinuous₂ 1 (by
    intro L K
    change ‖TensorProduct.mapL L K‖ ≤ 1 * ‖L‖ * ‖K‖
    simpa only [one_mul] using TensorProduct.norm_mapL_le L K)).bilinearRestrictScalars ℝ
  have hK : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) ↦ C.coordChangeL i.2 j.2 (d.symm z.1))
      (U ×ˢ {ξ | ξ ≠ 0}) := htrans.comp contDiffOn_fst (fun _ hz ↦ hz.1)
  have hproduct := μc.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hsymbol hK
  change ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) ×
    EuclideanSpace ℝ (Fin n) ↦ TensorProduct.mapL
      (atlasGlobalSymbolInChart A B c d i.1 j.1 z.1 z.2)
      (C.coordChangeL i.2 j.2 (d.symm z.1))) (U ×ˢ {ξ | ξ ≠ 0}) at hproduct
  have hfull : ContDiffOn ℝ ∞ (fun z ↦
      (tensorSymbolModel (B.rank j.1) (C.rank j.2)).toContinuousLinearMap.comp
        ((TensorProduct.mapL (atlasGlobalSymbolInChart A B c d i.1 j.1 z.1 z.2)
          (C.coordChangeL i.2 j.2 (d.symm z.1))).comp
            (tensorSymbolModel (A.rank i.1) (C.rank i.2)).symm.toContinuousLinearMap))
      (U ×ˢ {ξ | ξ ≠ 0}) := by
    let T₁ := V (A.rank i.1) ⊗[ℂ] V (C.rank i.2)
    let T₂ := V (B.rank j.1) ⊗[ℂ] V (C.rank j.2)
    let pre := (ContinuousLinearMap.compL ℂ (V (A.rank i.1 * C.rank i.2)) T₁ T₂).flip
      (tensorSymbolModel (A.rank i.1) (C.rank i.2)).symm.toContinuousLinearMap
    have hpre := (pre.restrictScalars ℝ).contDiff.comp_contDiffOn hproduct
    let post := ContinuousLinearMap.compL ℂ (V (A.rank i.1 * C.rank i.2)) T₂
      (V (B.rank j.1 * C.rank j.2))
      (tensorSymbolModel (B.rank j.1) (C.rank j.2)).toContinuousLinearMap
    exact (post.restrictScalars ℝ).contDiff.comp_contDiffOn hpre
  apply hfull.congr
  intro z hz
  have hA := (hUA z.1 hz.1).1
  have hCi := (hUA z.1 hz.1).2
  have hB := (hUB z.1 hz.1).1
  have hCj := (hUB z.1 hz.1).2
  have hAT : d.symm z.1 ∈ (AT.chart i).baseSet := hz.1.1.2
  have hBT : d.symm z.1 ∈ (BT.chart j).baseSet := hz.1.2
  -- Both coordinate maps agree on pure tensors in the original fibers.
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨t, rfl⟩ := (tensorSymbolCoord AT i (d.symm z.1) hAT).surjective v
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simpa only [map_add] using congrArg₂ HAdd.hAdd ht ht'
  | tmul u w =>
    have hinput := tensorSymbolFrame_tmul A C i.1 i.2 (d.symm z.1) hAT hA hCi u w
    erw [hinput]
    change _ = tensorSymbolModel (B.rank j.1) (C.rank j.2)
      (TensorProduct.mapL (atlasGlobalSymbolInChart A B c d i.1 j.1 z.1 z.2)
        (C.coordChangeL i.2 j.2 (d.symm z.1))
        ((tensorSymbolModel (A.rank i.1) (C.rank i.2)).symm
          (tensorSymbolModel (A.rank i.1) (C.rank i.2)
            (tensorSymbolCoord A i.1 (d.symm z.1) hA u ⊗ₜ[ℂ]
              tensorSymbolCoord C i.2 (d.symm z.1) hCi w))))
    rw [ContinuousLinearEquiv.symm_apply_apply, TensorProduct.mapL_tmul]
    have hcinput : atlasGlobalSymbolInChart A B c d i.1 j.1 z.1 z.2
        (tensorSymbolCoord A i.1 (d.symm z.1) hA u) =
          tensorSymbolCoord B j.1 (d.symm z.1) hB (c (d.symm z.1)
            (covectorFromChart d (d.symm z.1) z.2) u) := by
      dsimp only [atlasGlobalSymbolInChart]
      rw [dite_eq_left ⟨hA, hB⟩]
      change tensorSymbolCoord B j.1 (d.symm z.1) hB
        (c (d.symm z.1) (covectorFromChart d (d.symm z.1) z.2)
          ((tensorSymbolCoord A i.1 (d.symm z.1) hA).symm
            (tensorSymbolCoord A i.1 (d.symm z.1) hA u))) = _
      rw [LinearEquiv.symm_apply_apply]
    have htwist : C.coordChangeL i.2 j.2 (d.symm z.1)
        (tensorSymbolCoord C i.2 (d.symm z.1) hCi w) =
          tensorSymbolCoord C j.2 (d.symm z.1) hCj w :=
      (C.coordChangeL_apply i.2 j.2 (d.symm z.1) ⟨hCi, hCj⟩ w).symm
    rw [hcinput, htwist]
    erw [← tensorSymbolFrame_tmul B C j.1 j.2 (d.symm z.1) hBT hB hCj]
    rw [← hinput]
    dsimp only [Function.uncurry, atlasGlobalSymbolInChart]
    rw [dite_eq_left ⟨hAT, hBT⟩]
    change tensorSymbolCoord BT j (d.symm z.1) hBT
      (AtiyahSinger.tensorAtlasSymbol c (d.symm z.1) (covectorFromChart d (d.symm z.1) z.2)
        ((tensorSymbolCoord AT i (d.symm z.1) hAT).symm
          (tensorSymbolCoord AT i (d.symm z.1) hAT (u ⊗ₜ[ℂ] w)))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl

end AtiyahSinger
