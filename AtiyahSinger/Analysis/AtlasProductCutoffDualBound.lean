/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSmoothChartSobolevLocalization
public import AtiyahSinger.Analysis.ProductCutoffDualApproximation
public import AtiyahSinger.Analysis.ProductCutoffRealization

import all AtiyahSinger.Analysis.ProductSymbolCutoff

/-!
# Actual chart cutoff errors in the negative Sobolev norm

Public module ID: M0279.

The original compatible input and output maps transport the H⁰-to-H⁻¹
Fourier estimate to the given finite-atlas presentations. The bound applies
to the literal difference of the supplied uncut and cut Schwartz outputs,
with a single constant chosen before the positive parameter and the section.
This is the coordinate estimate needed before actual metric adjunction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n + m) E)
  (B : SmoothComplexBundleAtlas (n := n + m) F)

set_option maxSynthPendingDepth 20 in
/-- The actual localized cutoff error is small in the original negative Sobolev norm. -/
theorem norm_productCutoff_error_sobolev_neg_one_le
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + m))))
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ M)
    (Din : AtlasChartCutoff A c) (Dout : AtlasChartCutoff B c)
    (I : A.smoothSections →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (A.rank Din.frameIndex))))
    (O : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)))
      →ₗ[ℂ] B.smoothSections)
    (hI : ∀ u z, I u z = Din.localizedFunction u z)
    (hO : ∀ v x, (O v).val x = Dout.extendedFunction v x)
    (α : SymbolFunction n (A.rank Din.frameIndex) (B.rank Dout.frameIndex))
    (hα : IsSymbol Set.univ 1 α) (hαK : HasCompactSupport α)
    (ρ : EuclideanSpace ℝ (Fin m) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρK : HasCompactSupport ρ)
    (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (u : A.smoothSections)
        (v vε : 𝓢(EuclideanSpace ℝ (Fin (n + m)),
          EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)))),
        (∀ z, quantize (liftedProductSymbol α ρ) (I u) z = v z) →
        (∀ z, quantize (productCutoffSymbol α ρ ε) (I u) z = vε z) →
        ‖K.smoothToSobolev (-1) (O (v - vε))‖ ≤ C * ε * ‖L.smoothToSobolev 0 u‖ := by
  -- The original compatible chart maps are bounded at these two specified orders.
  obtain ⟨I₀, hI₀, Ci, hCi, hi⟩ := Din.exists_localize_sobolev_of_mem_maximalAtlas hc L 0
  obtain ⟨O₀, hO₀, Co, hCo, ho⟩ := Dout.exists_extend_sobolev_of_mem_maximalAtlas hc K (-1)
  have hII : I = I₀ := by
    apply LinearMap.ext
    intro u
    apply SchwartzMap.ext
    intro z
    exact (hI u z).trans (hI₀ u z).symm
  have hOO : O = O₀ := by
    ext v x
    exact (hO v x).trans (hO₀ v x).symm
  -- The Fourier constant and exact scalar frequency bound both precede epsilon.
  obtain ⟨C₀, hC₀, hbound⟩ := exists_productCutoffErrorOperator_zero_neg_one_bound
    α hα hαK ρ hρ hρK
  obtain ⟨B₀, hB₀, _, hfreq⟩ := productCutoffError_frequency_bounds n m
  refine ⟨Co * C₀ * B₀ * Ci, by positivity, ?_⟩
  intro ε hε _hεone u v vε hv hvε
  obtain ⟨T, hTnorm, hT⟩ := hbound ε (B₀ * ε) (mul_nonneg hB₀ hε.le) (hfreq ε hε)
  -- The weak Fourier formula identifies the actual Schwartz difference in H minus one.
  have hvalue : T (schwartzSobolevCoordinate 0 (I u)) =
      schwartzSobolevCoordinate (-1) (v - vε) := by
    apply besselRealization_injective (n + m) (B.rank Dout.frameIndex) (-1)
    ext1 φ
    rw [hT, besselRealization_schwartzSobolevCoordinate]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [quantize_productCutoffErrorSymbol α hα ρ hρ ε hε, hv, hvε]
    rfl
  have hin : ‖schwartzSobolevCoordinate 0 (I u)‖ ≤ Ci * ‖L.smoothToSobolev 0 u‖ := by
    rw [hII]
    exact hi u
  calc
    ‖K.smoothToSobolev (-1) (O (v - vε))‖ ≤
        Co * ‖schwartzSobolevCoordinate (-1) (v - vε)‖ := by
      rw [hOO]
      exact ho (v - vε)
    _ = Co * ‖T (schwartzSobolevCoordinate 0 (I u))‖ := by rw [hvalue]
    _ ≤ Co * (‖T‖ * ‖schwartzSobolevCoordinate 0 (I u)‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) hCo
    _ ≤ Co * ((C₀ * (B₀ * ε)) * (Ci * ‖L.smoothToSobolev 0 u‖)) := by gcongr
    _ = (Co * C₀ * B₀ * Ci) * ε * ‖L.smoothToSobolev 0 u‖ := by ring

end AtiyahSinger
