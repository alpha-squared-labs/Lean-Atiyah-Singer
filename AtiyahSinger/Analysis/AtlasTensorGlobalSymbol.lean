/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasQuantization
public import AtiyahSinger.Analysis.AtlasTensorCoefficientSymbol

/-!
# Tensoring the full symbol filtration on a compact base

Public module ID: M0313.

Use a common quantization presentation in the actual tensor atlases. Its
projected base patches retain all coefficient support conditions. Tensoring
their actual symbols and summing the same partition recovers the original
full symbol tensored with the coefficient identity, at every real order.
This supplies the lower-order comparison for coefficient principal classes.

Source: SG III.3 and III.13.6. The proof uses the existing local tensor-piece
construction; it requires neither covector linearity nor homogeneous data.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

attribute [local instance] ComplexBundle.tensorTopology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E F W : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
  [TopologicalSpace (TotalSpace Unit W)]

set_option maxSynthPendingDepth 30 in
/-- The actual coefficient identity preserves every full symbol order on the compact base. -/
theorem IsAtlasGlobalSymbol.tensorAtlasSymbol
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F)
    (C : SmoothComplexBundleAtlas (n := n) W)
    {m : ℝ} (p : AtlasSymbolFunction (n := n) E F)
    (hp : IsAtlasGlobalSymbol A B m p) :
    IsAtlasGlobalSymbol (tensorSmoothAtlas A C) (tensorSmoothAtlas B C) m
      (tensorAtlasSymbol (W := W) p) := by
  classical
  let AT := tensorSmoothAtlas A C
  let BT := tensorSmoothAtlas B C
  let R := (nonempty_atlasQuantizationPresentation AT BT).some
  have hbaseA (i : AT.Index) :
      (AT.chart i).baseSet = (A.chart i.1).baseSet ∩ (C.chart i.2).baseSet :=
    (ComplexBundle.exists_tensor_trivialization (A.chart i.1) (C.chart i.2)
      (A.linear i.1) (C.linear i.2)).choose_spec.1
  have hbaseB (i : BT.Index) :
      (BT.chart i).baseSet = (B.chart i.1).baseSet ∩ (C.chart i.2).baseSet :=
    (ComplexBundle.exists_tensor_trivialization (B.chart i.1) (C.chart i.2)
      (B.linear i.1) (C.linear i.2)).choose_spec.1
  -- Project only the frames: the original chart, partition and plateau remain fixed.
  let L (j : Fin R.size) : AtlasQuantizationPatch A B := {
    chart := (R.patch j).chart
    chart_mem_atlas := (R.patch j).chart_mem_atlas
    input := {
      frameIndex := (R.patch j).input.frameIndex.1
      cutoff := (R.patch j).input.cutoff
      smooth_cutoff := (R.patch j).input.smooth_cutoff
      compact_support := (R.patch j).input.compact_support
      support_subset := fun x hx ↦ ⟨((R.patch j).input.support_subset hx).1,
        (hbaseA _ ▸ ((R.patch j).input.support_subset hx).2).1⟩ }
    output := {
      frameIndex := (R.patch j).output.frameIndex.1
      cutoff := (R.patch j).output.cutoff
      smooth_cutoff := (R.patch j).output.smooth_cutoff
      compact_support := (R.patch j).output.compact_support
      support_subset := fun x hx ↦ ⟨((R.patch j).output.support_subset hx).1,
        (hbaseB _ ▸ ((R.patch j).output.support_subset hx).2).1⟩ }
    output_nonneg := (R.patch j).output_nonneg
    input_support_in_output_frame := fun x hx ↦
      (hbaseB _ ▸ (R.patch j).input_support_in_output_frame hx).1
    output_support_in_input_frame := fun x hx ↦
      (hbaseA _ ▸ (R.patch j).output_support_in_input_frame hx).1
    input_eq_one := (R.patch j).input_eq_one }
  let P : atlasGlobalSymbolSpace A B m := ⟨p, hp⟩
  have hin (j : Fin R.size) : tsupport (L j).input.cutoff ⊆
      (L j).chart.symm ⁻¹' (C.chart (R.patch j).input.frameIndex.2).baseSet := by
    intro x hx
    exact (hbaseA _ ▸ ((R.patch j).input.support_subset hx).2).2
  have hout (j : Fin R.size) : tsupport (L j).output.cutoff ⊆
      (L j).chart.symm ⁻¹' (C.chart (R.patch j).input.frameIndex.2).baseSet := by
    intro x hx
    exact (hbaseA _ ▸ (R.patch j).output_support_in_input_frame hx).2
  let T (j : Fin R.size) := ((L j).toPiece P).tensorCoefficient C
    (R.patch j).input.frameIndex.2 (hin j) (hout j)
  -- Each tensor piece has the exact weighted original symbol, before taking any quotient.
  have hT (j : Fin R.size) : (T j).globalSymbolFunction =
      AtiyahSinger.tensorAtlasSymbol (W := W) (fun x ξ ↦ ((L j).weight x : ℂ) • p x ξ) :=
    (((L j).toPiece P).globalSymbolFunction_tensorCoefficient C
      (R.patch j).input.frameIndex.2 (hin j) (hout j)).trans
        (congrArg (AtiyahSinger.tensorAtlasSymbol (W := W))
          ((L j).globalSymbolFunction_toPiece P))
  have hsum : (∑ j, (T j).globalSymbol).val = AtiyahSinger.tensorAtlasSymbol (W := W) p := by
    funext x ξ
    apply TensorProduct.ext'
    intro u w
    simp only [Submodule.coe_sum, Finset.sum_apply, LinearMap.sum_apply]
    change (∑ j, (T j).globalSymbolFunction x ξ (u ⊗ₜ[ℂ] w)) = _
    simp only [hT, AtiyahSinger.tensorAtlasSymbol,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.smul_apply]
    rw [← TensorProduct.sum_tmul, ← Finset.sum_smul]
    have hweight : (∑ j, ((L j).weight x : ℂ)) = 1 := by
      change (∑ j, ((R.patch j).weight x : ℂ)) = 1
      exact_mod_cast R.sum_weight x
    rw [hweight, one_smul]
  -- Membership of this finite sum gives all mixed derivative bounds for the same tensor map.
  exact hsum ▸ (∑ j, (T j).globalSymbol).property

end AtiyahSinger
