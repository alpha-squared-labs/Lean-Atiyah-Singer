/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasProductCutoffDualBound
public import AtiyahSinger.Analysis.IsometricSymbolTransport

import all AtiyahSinger.Analysis.ProductSymbolCutoff

/-!
# Negative-order errors under the specified coordinate isometries

Public module ID: M0255.

The original base and fiber isometries transport the full product cutoff
error from H⁰ to H⁻¹. The same compatible chart maps, original Schwartz
outputs and Sobolev presentations are retained. In particular this applies
to the right-factor cutoff used by the vertical regularization, before
taking its actual metric formal adjoint.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

variable {n m k r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin k)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := k) E)
  (B : SmoothComplexBundleAtlas (n := k) F)

set_option maxSynthPendingDepth 20 in
/-- The same orthogonally transported cutoff error has a uniform negative-order bound. -/
theorem norm_isometricProductCutoff_error_sobolev_neg_one_le
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin k)))
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ M)
    (Din : AtlasChartCutoff A c) (Dout : AtlasChartCutoff B c)
    (I : A.smoothSections →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin k), EuclideanSpace ℂ (Fin (A.rank Din.frameIndex))))
    (O : 𝓢(EuclideanSpace ℝ (Fin k), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)))
      →ₗ[ℂ] B.smoothSections)
    (hI : ∀ u z, I u z = Din.localizedFunction u z)
    (hO : ∀ v x, (O v).val x = Dout.extendedFunction v x)
    (e : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + m)))
    (i : EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin r))
    (o : EuclideanSpace ℂ (Fin q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)))
    (α : SymbolFunction n r q) (hα : IsSymbol Set.univ 1 α) (hαK : HasCompactSupport α)
    (ρ : EuclideanSpace ℝ (Fin m) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρK : HasCompactSupport ρ)
    (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (u : A.smoothSections)
        (v vε : 𝓢(EuclideanSpace ℝ (Fin k),
          EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)))),
        (∀ z, quantize (isometricSymbolTransport e i o (liftedProductSymbol α ρ))
          (I u) z = v z) →
        (∀ z, quantize (isometricSymbolTransport e i o (productCutoffSymbol α ρ ε))
          (I u) z = vε z) →
        ‖K.smoothToSobolev (-1) (O (v - vε))‖ ≤ C * ε * ‖L.smoothToSobolev 0 u‖ := by
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
  obtain ⟨C₀, hC₀, hbound⟩ := exists_productCutoffErrorOperator_zero_neg_one_bound
    α hα hαK ρ hρ hρK
  obtain ⟨B₀, hB₀, _, hfreq⟩ := productCutoffError_frequency_bounds n m
  refine ⟨Co * C₀ * B₀ * Ci, by positivity, ?_⟩
  intro ε hε _hεone u v vε hv hvε
  let w := schwartzCoordinateEquiv e.symm i (I u)
  let z := schwartzCoordinateEquiv e.symm o.symm v
  let zε := schwartzCoordinateEquiv e.symm o.symm vε
  -- Undo exactly the supplied isometries in both Fourier formulas.
  have hw : schwartzCoordinateEquiv e i.symm w = I u := by
    apply SchwartzMap.ext
    intro x
    change i.symm (i (I u (e.symm (e x)))) = I u x
    rw [e.symm_apply_apply, i.symm_apply_apply]
  have htransport (p : SymbolFunction (n + m) r q)
      (v' : 𝓢(EuclideanSpace ℝ (Fin k), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))))
      (hp : ∀ x, quantize (isometricSymbolTransport e i o p) (I u) x = v' x)
      (x : EuclideanSpace ℝ (Fin (n + m))) :
      quantize p w x = schwartzCoordinateEquiv e.symm o.symm v' x := by
    apply o.injective
    have h := quantize_isometricSymbolTransport e i o p w (e.symm x)
    rw [hw, e.apply_symm_apply, hp] at h
    change _ = o (o.symm (v' (e.symm x)))
    rw [o.apply_symm_apply]
    exact h.symm
  obtain ⟨T, hTnorm, hT⟩ := hbound ε (B₀ * ε) (mul_nonneg hB₀ hε.le) (hfreq ε hε)
  have hvalue : T (schwartzSobolevCoordinate 0 w) =
      schwartzSobolevCoordinate (-1) (z - zε) := by
    apply besselRealization_injective (n + m) q (-1)
    ext1 φ
    rw [hT, besselRealization_schwartzSobolevCoordinate]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [quantize_productCutoffErrorSymbol α hα ρ hρ ε hε,
      htransport _ v hv, htransport _ vε hvε]
    rfl
  -- Bessel coordinates are isometric at each order, including the negative output order.
  have hin : ‖schwartzSobolevCoordinate 0 w‖ ≤ Ci * ‖L.smoothToSobolev 0 u‖ := by
    rw [← sobolevCoordinateIsometry_apply, LinearIsometryEquiv.norm_map, hII]
    exact hi u
  have hout : ‖schwartzSobolevCoordinate (-1) (v - vε)‖ =
      ‖schwartzSobolevCoordinate (-1) (z - zε)‖ := by
    have hmap := (sobolevCoordinateIsometry e.symm o.symm (-1)).norm_map
      (schwartzSobolevCoordinate (-1) (v - vε))
    rw [sobolevCoordinateIsometry_apply, map_sub] at hmap
    exact hmap.symm
  calc
    ‖K.smoothToSobolev (-1) (O (v - vε))‖ ≤
        Co * ‖schwartzSobolevCoordinate (-1) (v - vε)‖ := by
      rw [hOO]
      exact ho (v - vε)
    _ = Co * ‖T (schwartzSobolevCoordinate 0 w)‖ := by rw [hout, hvalue]
    _ ≤ Co * (‖T‖ * ‖schwartzSobolevCoordinate 0 w‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) hCo
    _ ≤ Co * ((C₀ * (B₀ * ε)) * (Ci * ‖L.smoothToSobolev 0 u‖)) := by gcongr
    _ = (Co * C₀ * B₀ * Ci) * ε * ‖L.smoothToSobolev 0 u‖ := by ring

end AtiyahSinger
