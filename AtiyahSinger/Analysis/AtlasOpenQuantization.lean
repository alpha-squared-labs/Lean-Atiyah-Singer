/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasOpenLocalization
public import AtiyahSinger.Analysis.AtlasQuantization

/-!
# Extending the original quantization patches from clopen pieces

Public module ID: M0269.

The ambient patch retains the restricted patch's Euclidean operator, cutoff
and original frame indices. Consequently its action is actual restriction,
the original local quantization and zero extension, in that order. This
identity permits finite component assembly with exactly the same witnesses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff BigOperators

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A patch on a clopen piece extends with its original weight and exact section action. -/
theorem AtlasQuantizationPatch.exists_openExtension
    (U : Opens M) (hclosed : IsClosed (U : Set M))
    (R : AtlasQuantizationPatch (A.restrictOpen U) (B.restrictOpen U)) :
    ∃ S : AtlasQuantizationPatch A B,
      (∀ x, S.weight x = if hx : x ∈ U then R.weight ⟨x, hx⟩ else 0) ∧
      (∀ (m : ℝ) (p : atlasGlobalSymbolSpace A B m),
        (S.toPiece p).toLinearMap =
          (atlasSmoothSectionZeroExtension B U hclosed).comp
            (((R.toPiece ⟨fun x ξ ↦ p.val x.val ξ, p.property.restrictOpen A B U⟩).toLinearMap).comp
              (atlasSmoothSectionRestriction A U))) := by
  classical
  have hU : Nonempty U := by
    rcases R.chart_mem_atlas with ⟨_, ⟨x, _⟩, _⟩
    exact ⟨x⟩
  obtain ⟨x₀, hc⟩ := Opens.chart_eq hU R.chart_mem_atlas
  rcases R with ⟨d, hd, L, K, hnonneg, hLK, hKL, hone⟩
  dsimp only at hc
  subst d
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x₀.val
  have hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M := _root_.chart_mem_atlas _ _
  have hAbase : ((A.restrictOpen U).chart L.frameIndex).baseSet =
      Subtype.val ⁻¹' (A.chart L.frameIndex).baseSet :=
    (A.exists_restrictOpenChart U L.frameIndex).choose_spec.1
  have hBbase : ((B.restrictOpen U).chart K.frameIndex).baseSet =
      Subtype.val ⁻¹' (B.chart K.frameIndex).baseSet :=
    (B.exists_restrictOpenChart U K.frameIndex).choose_spec.1
  -- Compact support inside the restricted chart also lies inside both ambient frames.
  have hLK' : tsupport L.cutoff ⊆ c.symm ⁻¹' (B.chart K.frameIndex).baseSet := by
    intro z hz
    have h := hLK hz
    change (c.subtypeRestr hU).symm z ∈ ((B.restrictOpen U).chart K.frameIndex).baseSet at h
    rw [hBbase] at h
    change c.symm z ∈ (B.chart K.frameIndex).baseSet
    rw [← c.subtypeRestr_symm_apply hU (L.support_subset hz).1]
    exact h
  have hKL' : tsupport K.cutoff ⊆ c.symm ⁻¹' (A.chart L.frameIndex).baseSet := by
    intro z hz
    have h := hKL hz
    change (c.subtypeRestr hU).symm z ∈ ((A.restrictOpen U).chart L.frameIndex).baseSet at h
    rw [hAbase] at h
    change c.symm z ∈ (A.chart L.frameIndex).baseSet
    rw [← c.subtypeRestr_symm_apply hU (K.support_subset hz).1]
    exact h
  let R : AtlasQuantizationPatch (A.restrictOpen U) (B.restrictOpen U) :=
    ⟨c.subtypeRestr hU, hd, L, K, hnonneg, hLK, hKL, hone⟩
  let S : AtlasQuantizationPatch A B :=
    ⟨c, hc, L.openExtension, K.openExtension, hnonneg, hLK', hKL', hone⟩
  refine ⟨S, ?_, ?_⟩
  · intro x
    change S.weight x = if hx : x ∈ U then R.weight ⟨x, hx⟩ else 0
    by_cases hxU : x ∈ U
    · simp only [S, R, AtlasQuantizationPatch.weight, dite_eq_left hxU,
        OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
      rfl
    · rw [dite_eq_right hxU]
      by_cases hx : x ∈ c.source
      · have hzero : K.cutoff (c x) = 0 := by
          by_contra hn
          have hz := (K.support_subset (subset_tsupport _ hn)).1
          have hr := c.subtypeRestr_symm_apply hU hz
          have hu : c.symm (c x) ∈ U :=
            hr ▸ ((c.subtypeRestr hU).symm (c x)).property
          exact hxU ((c.left_inv hx) ▸ hu)
        simp [S, AtlasQuantizationPatch.weight, hx, AtlasChartCutoff.openExtension, hzero]
      · simp [S, AtlasQuantizationPatch.weight, hx]
  · intro m p
    let q : atlasGlobalSymbolSpace (A.restrictOpen U) (B.restrictOpen U) m :=
      ⟨fun x ξ ↦ p.val x.val ξ, p.property.restrictOpen A B U⟩
    -- The cutoff makes both local full symbols zero off its support. On its support
    -- the inherited cotangent coordinate calculation identifies the two exact symbols.
    have hsymbol : S.localSymbol p.val = R.localSymbol q.val := by
      funext z η
      by_cases hz : z ∈ tsupport L.cutoff
      · have hD : z ∈ atlasSymbolChartDomain (A.restrictOpen U) (B.restrictOpen U)
            (c.subtypeRestr hU) L.frameIndex K.frameIndex := ⟨L.support_subset hz, hLK hz⟩
        have hD' := atlasSymbolChartDomain_restrictOpen_subset A B U hU c
          L.frameIndex K.frameIndex hD
        simp only [AtlasQuantizationPatch.localSymbol, S, R, zeroExtendedSymbol,
          AtlasChartCutoff.openExtension, hD, hD', ite_true]
        congr 1
        exact (atlasGlobalSymbolInChart_restrictOpen A B U hU c hc p.val
          L.frameIndex K.frameIndex z hD η).symm
      · have hzero := image_eq_zero_of_notMem_tsupport hz
        simp [AtlasQuantizationPatch.localSymbol, S, R, zeroExtendedSymbol,
          AtlasChartCutoff.openExtension, hzero]
    have hop : quantizeSchwartz m (S.localSymbol p.val)
        (S.localSymbol_properties p).2 (S.localSymbol_properties p).1 =
        quantizeSchwartz m (R.localSymbol q.val)
          (R.localSymbol_properties q).2 (R.localSymbol_properties q).1 := by
      apply ContinuousLinearMap.ext
      intro v
      apply SchwartzMap.ext
      intro z
      simp only [quantizeSchwartz_apply, hsymbol]
      exact (quantizeSchwartz_apply m (R.localSymbol q.val)
        (R.localSymbol_properties q).2 (R.localSymbol_properties q).1 v z).symm
    apply LinearMap.ext
    intro u
    change S.output.extend S.chart_mem_atlas
      (quantizeSchwartz m (S.localSymbol p.val)
        (S.localSymbol_properties p).2 (S.localSymbol_properties p).1
        (S.input.localize S.chart_mem_atlas u)) =
      atlasSmoothSectionZeroExtension B U hclosed
        (R.output.extend R.chart_mem_atlas
          (quantizeSchwartz m (R.localSymbol q.val)
            (R.localSymbol_properties q).2 (R.localSymbol_properties q).1
            (R.input.localize R.chart_mem_atlas (atlasSmoothSectionRestriction A U u))))
    rw [hop]
    change K.openExtension.extend hc
      (quantizeSchwartz m (R.localSymbol q.val)
        (R.localSymbol_properties q).2 (R.localSymbol_properties q).1
        (L.openExtension.localize hc u)) = _
    rw [L.localize_openExtension hc hd,
      K.extend_openExtension hclosed hc hd]

end AtiyahSinger
