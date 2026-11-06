/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSmoothChartSobolevLocalization
public import AtiyahSinger.Analysis.AtlasSmoothingOperator
public import AtiyahSinger.Analysis.Pseudolocal

/-!
# Smoothing symbols in compatible manifold charts

Public module ID: M0374.

An actual compactly supported Schwartz quantizer whose full symbol has every
real order gives an all-order smoothing operator on the unchanged atlas
Sobolev spaces. Both cutoff maps are specified by their original pointwise
formulas. In particular the conclusion does not require the compatible chart
to belong to the original, potentially smaller, raw atlas.

This is the smoothing-remainder step in the coordinate invariance of PDOs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- An all-order full symbol in a compatible chart gives an actual atlas smoothing map. -/
theorem isAtlasSmoothingOperator_of_compatible_chart_symbol
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (Din : AtlasChartCutoff A c) (Dout : AtlasChartCutoff B c)
    (T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))
      →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))))
    (a : SymbolFunction n (A.rank Din.frameIndex) (B.rank Dout.frameIndex))
    (ha : ∀ m : ℝ, IsSymbol univ m a) (hca : HasCompactSupport a)
    (hT : ∀ u x, T u x = quantize a u x)
    (I : A.smoothSections →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank Din.frameIndex))))
    (O : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)))
      →ₗ[ℂ] B.smoothSections)
    (hI : ∀ u z, I u z = Din.localizedFunction u z)
    (hO : ∀ v x, (O v).val x = Dout.extendedFunction v x) :
    IsAtlasSmoothingOperator A B (O.comp (T.toLinearMap.comp I)) := by
  intro L K s t
  -- Compatible-chart bounds are measured in these same two original presentations.
  obtain ⟨I₀, hI₀, Ci, hCi, hi⟩ := Din.exists_localize_sobolev_of_mem_maximalAtlas hc L s
  obtain ⟨O₀, hO₀, Co, hCo, ho⟩ := Dout.exists_extend_sobolev_of_mem_maximalAtlas hc K t
  have hII : I = I₀ := by
    apply LinearMap.ext
    intro u
    apply SchwartzMap.ext
    intro z
    exact (hI u z).trans (hI₀ u z).symm
  have hOO : O = O₀ := by
    ext v x
    exact (hO v x).trans (hO₀ v x).symm
  let Q := quantizeSobolev (s - t) s a (ha (s - t)) hca
  have hQ (v) : Q (schwartzSobolevCoordinate s v) = schwartzSobolevCoordinate t (T v) := by
    have hst : s - (s - t) = t := by ring
    apply besselRealization_injective n (B.rank Dout.frameIndex) t
    ext1 φ
    conv_lhs => rw [← hst]
    rw [besselRealization_quantizeSobolev, besselRealization_schwartzSobolevCoordinate,
      SchwartzMap.coe_apply]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ congrArg (φ x • ·) (hT v x).symm)
  let f := (K.smoothToSobolev t).comp (O.comp (T.toLinearMap.comp I))
  have hb (u : A.smoothSections) :
      ‖f u‖ ≤ (Co * ‖Q‖ * Ci) * ‖L.smoothToSobolev s u‖ := by
    calc
      ‖f u‖ ≤ Co * ‖schwartzSobolevCoordinate t (T (I u))‖ := by
        simpa only [f, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hOO] using ho (T (I u))
      _ = Co * ‖Q (schwartzSobolevCoordinate s (I u))‖ := by rw [hQ]
      _ ≤ Co * (‖Q‖ * ‖schwartzSobolevCoordinate s (I u)‖) :=
        mul_le_mul_of_nonneg_left (Q.le_opNorm _) hCo
      _ ≤ Co * (‖Q‖ * (Ci * ‖L.smoothToSobolev s u‖)) := by
        apply mul_le_mul_of_nonneg_left _ hCo
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg Q)
        simpa only [hII] using hi u
      _ = _ := by ring
  refine ⟨f.extendOfNorm (L.smoothToSobolev s), ?_⟩
  exact LinearMap.extendOfNorm_eq (L.denseRange_smoothToSobolev s) ⟨_, hb⟩

end AtiyahSinger
