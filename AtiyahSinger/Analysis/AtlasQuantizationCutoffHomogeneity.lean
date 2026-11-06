/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasQuantization
public import AtiyahSinger.Analysis.CotangentChartNormBounds
public import AtiyahSinger.Analysis.ProductCutoffHomogeneousTail

/-!
# Homogeneous tails of the original atlas quantization symbols

Public module ID: M0298.

The original input cutoff puts the actual local symbol in one compact chart
window. The specified cotangent metric converts its global homogeneous tail
to a uniform local frequency tail. The same product cutoff consequently has
an exact homogeneous tail, with the original frames and zero extension retained.
This applies to the vertical pieces of the specified native sphere quantizer.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E} {B : SmoothComplexBundleAtlas (n := n) F}
  {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in

/-- The original input-cutoff local symbol retains its tail under the same product cutoff. -/
theorem AtlasQuantizationPatch.exists_productCutoff_localSymbol_homogeneous_of_tail
    (D : AtlasQuantizationPatch A B) (p : atlasGlobalSymbolSpace A B 1)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R₀ : ℝ)
    (hp : ∀ x ξ (t : ℝ), 0 < t → R₀ ≤ g.length x ξ →
      R₀ ≤ g.length x (t • ξ) → p.val x (t • ξ) = (t : ℂ) • p.val x ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (z ξ : EuclideanSpace ℝ (Fin n)) (η : Y) (t : ℝ),
      0 < t → R ≤ ‖ξ‖ + ‖η‖ → R ≤ ‖t • ξ‖ + ‖t • η‖ →
      (productFrequencyCutoff ε ‖t • ξ‖ ‖t • η‖ : ℂ) •
          D.localSymbol p.val z (t • ξ) =
        (t : ℂ) • ((productFrequencyCutoff ε ‖ξ‖ ‖η‖ : ℂ) • D.localSymbol p.val z ξ) := by
  classical
  -- The original compact input support controls the retained cotangent frequency.
  obtain ⟨b, _, hb, _, hbound⟩ := g.exists_length_bounds_on
    D.chart D.chart_mem_atlas (tsupport D.input.cutoff) D.input.compact_support
      (fun _ hx ↦ (D.input.support_subset hx).1)
  let R₁ := max R₀ 1 / b
  have hscale : ∀ (z ξ : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t →
      R₁ ≤ ‖ξ‖ → R₁ ≤ ‖t • ξ‖ →
      D.localSymbol p.val z (t • ξ) = (t : ℂ) • D.localSymbol p.val z ξ := by
    intro z ξ t ht hξ htξ
    by_cases hz : z ∈ tsupport D.input.cutoff
    · have hdomain : z ∈
          atlasSymbolChartDomain A B D.chart D.input.frameIndex D.output.frameIndex :=
        ⟨D.input.support_subset hz, D.input_support_in_output_frame hz⟩
      have hframes : D.chart.symm z ∈ (A.chart D.input.frameIndex).baseSet ∧
          D.chart.symm z ∈ (B.chart D.output.frameIndex).baseSet :=
        ⟨hdomain.1.2, hdomain.2⟩
      have hlarge (ν : EuclideanSpace ℝ (Fin n)) (hν : R₁ ≤ ‖ν‖) :
          R₀ ≤ g.length (D.chart.symm z) (covectorFromChart D.chart (D.chart.symm z) ν) := by
        have h := (hbound z hz ν).1
        have h' : max R₀ 1 ≤ ‖ν‖ * b := (div_le_iff₀ hb).mp hν
        exact (le_max_left _ _).trans (by nlinarith)
      have hcov : covectorFromChart D.chart (D.chart.symm z) (t • ξ) =
          t • covectorFromChart D.chart (D.chart.symm z) ξ := by
        ext v
        exact real_inner_smul_left ξ _ t
      have htail := hp (D.chart.symm z) (covectorFromChart D.chart (D.chart.symm z) ξ)
        t ht (hlarge ξ hξ) (hcov ▸ hlarge (t • ξ) htξ)
      -- Both original complex-linear frames preserve the specified scalar dilation.
      have hcoordinate :
          atlasGlobalSymbolInChart A B p.val D.chart D.input.frameIndex D.output.frameIndex
              z (t • ξ) =
            (t : ℂ) • atlasGlobalSymbolInChart A B p.val D.chart D.input.frameIndex
              D.output.frameIndex z ξ := by
        simp only [atlasGlobalSymbolInChart, dite_eq_left hframes, hcov, htail]
        apply ContinuousLinearMap.ext
        intro v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
          LinearMap.smul_apply, smul_apply, map_smul]
      dsimp only [AtlasQuantizationPatch.localSymbol, zeroExtendedSymbol]
      rw [ite_eq_left hdomain, ite_eq_left hdomain, hcoordinate]
      exact smul_comm _ _ _
    · have hzero : D.input.cutoff z = 0 := by
        by_contra h
        exact hz (subset_tsupport _ h)
      simp [AtlasQuantizationPatch.localSymbol, zeroExtendedSymbol, hzero]
  exact exists_productFrequencyCutoff_homogeneous_of_tail ε R₁ hε
    (fun z ξ ↦ D.localSymbol p.val z ξ) hscale

end AtiyahSinger
