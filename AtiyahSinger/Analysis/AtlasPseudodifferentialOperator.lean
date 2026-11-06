/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSmoothingOperator
public import AtiyahSinger.Analysis.TwoSidedCutoff
public import AtiyahSinger.Geometry.AtlasChartLocalization

/-!
# Pseudodifferential operators on the original locally finite-rank bundles

Public module ID: M0291.

D05: SG III.3.15, p.186, defines an operator by finitely many local Fourier
pieces and a smoothing remainder. Each piece retains a common base chart,
the original input and output frames, and both compact cutoffs. Their local
ranks are independent. The composite acts on the original smooth sections;
the smoothing remainder may also couple disconnected components.

The remainder uses SG's all-real-order bounded-extension condition on the
actual AtlasSobolev completions. No diagonal decomposition of the whole
operator is imposed. Compactness is explicit in the global finite-presentation
definition; local cutoff pieces make sense without it. A principal symbol,
homogeneous expansion, parametrix or whole-PDO bound is not an input field.
Homogeneous principal representatives used in SG III.13 are imposed separately.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- One actual local Fourier operator, with the two original cutoff frame maps. -/
structure AtlasPseudodifferentialPiece (m : ℝ) where
  /-- The common manifold chart for input and output. -/
  chart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  /-- The chart belongs to the given smooth manifold atlas. -/
  chart_mem_atlas : chart ∈ atlas (EuclideanSpace ℝ (Fin n)) M
  /-- Input coordinates and the compact input cutoff. -/
  input : AtlasChartCutoff A chart
  /-- Output coordinates and the compact output cutoff. -/
  output : AtlasChartCutoff B chart
  /-- The output frame is valid near the entire input support. -/
  input_support_in_output_frame :
    tsupport input.cutoff ⊆ chart.symm ⁻¹' (B.chart output.frameIndex).baseSet
  /-- The input frame is valid near the entire output support. -/
  output_support_in_input_frame :
    tsupport output.cutoff ⊆ chart.symm ⁻¹' (A.chart input.frameIndex).baseSet
  /-- The actual continuous coordinate Schwartz operator. -/
  operator : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank input.frameIndex)))
    →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank output.frameIndex)))
  /-- Its specified full left symbol, before the two outer cutoffs. -/
  symbol : SymbolFunction n (A.rank input.frameIndex) (B.rank output.frameIndex)
  /-- The local symbol obeys the usual order bound. -/
  isSymbol : IsSymbol Set.univ m symbol
  /-- Exact quantization action, using the existing Fourier convention. -/
  operator_apply : ∀ u x, operator u x = quantize symbol u x

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

namespace AtlasPseudodifferentialPiece

variable {A B} {m : ℝ} (L : AtlasPseudodifferentialPiece A B m)

/-- The actual restriction, coordinate action and inverse-frame extension on sections. -/
def toLinearMap : A.smoothSections →ₗ[ℂ] B.smoothSections :=
  (L.output.extendLinearMap L.chart_mem_atlas).comp
    (L.operator.toLinearMap.comp (L.input.localizeLinearMap L.chart_mem_atlas))

/-- The two support controls of the actual transported local operator.
This is one joint support statement, not additional structure on the operator. -/
theorem toLinearMap_support_properties :
    (∀ (u : A.smoothSections) (x : M),
      x ∉ L.chart.symm '' tsupport L.output.cutoff → (L.toLinearMap u).val x = 0) ∧
    (∀ u v : A.smoothSections,
      (∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, u.val x = v.val x) →
        L.toLinearMap u = L.toLinearMap v) := by
  /- Stage 1: the actual output is the cutoff extension of L.operator's
  Schwartz value. Outside the inverse image of the output cutoff support
  that section is zero, including at the chart boundary.
  Stage 2: equality on the input support identifies the actual localized
  Schwartz functions; outside that support both are zero. Apply the same
  continuous operator and the same output extension to obtain equality.
  This uses neither compactness of M nor equality of the two local ranks. -/
  classical
  constructor
  · intro u x hx
    -- The specified output extension vanishes outside its own cutoff image.
    exact (L.output.extendedFunction_properties L.chart_mem_atlas
      (L.operator (L.input.localize L.chart_mem_atlas u))).2 x hx
  · intro u v huv
    -- The same input cutoff identifies the actual localized Schwartz functions.
    have hlocal : L.input.localize L.chart_mem_atlas u =
        L.input.localize L.chart_mem_atlas v := by
      apply DFunLike.ext
      intro z
      change L.input.localizedFunction u z = L.input.localizedFunction v z
      by_cases hz : z ∈ tsupport L.input.cutoff
      · have hvalue : u.val (L.chart.symm z) = v.val (L.chart.symm z) :=
          huv (L.chart.symm z) ⟨z, hz, rfl⟩
        simp only [AtlasChartCutoff.localizedFunction, atlasSectionInChart, hvalue]
      · -- Off that closed support, the original inner multiplier is zero.
        have hzero := image_eq_zero_of_notMem_tsupport hz
        simp [AtlasChartCutoff.localizedFunction, hzero]
    -- Apply the same coordinate operator and the same output extension to that equality.
    change L.output.extend L.chart_mem_atlas (L.operator (L.input.localize L.chart_mem_atlas u)) =
      L.output.extend L.chart_mem_atlas (L.operator (L.input.localize L.chart_mem_atlas v))
    rw [hlocal]

end AtlasPseudodifferentialPiece

variable [SecondCountableTopology M] [CompactSpace M]

/-- SG's finite local representation modulo all-order smoothing, on original sections. -/
def IsAtlasPseudodifferentialOperator (m : ℝ)
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections) : Prop :=
  ∃ (N : ℕ) (L : Fin N → AtlasPseudodifferentialPiece A B m),
    IsAtlasSmoothingOperator A B (P - ∑ j, (L j).toLinearMap)

/-- The standard PDO consists of its original section action and local representation. -/
structure AtlasPseudodifferentialOperator (m : ℝ) where
  /-- Complex-linear action on the original smooth sections. -/
  toLinearMap : A.smoothSections →ₗ[ℂ] B.smoothSections
  /-- Finitely many local Fourier pieces modulo the actual all-order remainder. -/
  isPseudodifferentialOperator : IsAtlasPseudodifferentialOperator A B m toLinearMap

end AtiyahSinger
