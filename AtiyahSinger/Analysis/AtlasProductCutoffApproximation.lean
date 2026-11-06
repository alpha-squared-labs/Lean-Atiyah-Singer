/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSmoothChartSobolevLocalization
public import AtiyahSinger.Analysis.ProductCompactSchwartz
public import AtiyahSinger.Analysis.ProductSchwartzCutoffRealization

/-!
# Product-frequency approximation in the original atlas Sobolev spaces

Public module ID: M0278.

The exact compatible-chart input and output maps transport the full Fourier
cutoff estimate to any two specified original finite-atlas Sobolev norms.
The unregularized limit has its actual Fourier action on every original smooth
section. Every positive regularization is compared using these same maps.

This is the analytic assembly step of SG III.13.5--13.6. Its application to
the geometric horizontal operator still requires the original output identity;
PDO membership and the prescribed principal symbol are separate conclusions.
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
set_option maxHeartbeats 800000 in

/-- One full Fourier limit and all its actual positive cutoffs use the same original norms. -/
theorem exists_atlas_productCutoff_sobolev_approximation
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
    ∃ R : L.SobolevSpace 1 →L[ℂ] K.SobolevSpace 0,
      (∀ u : A.smoothSections,
        ∃ v : 𝓢(EuclideanSpace ℝ (Fin (n + m)),
            EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))),
          (∀ z, quantize (liftedProductSymbol α ρ) (I u) z = v z) ∧
            R (L.smoothToSobolev 1 u) = K.smoothToSobolev 0 (O v)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ _hε : 0 < ε, ε ≤ 1 →
        ∀ T : 𝓢(EuclideanSpace ℝ (Fin (n + m)),
            EuclideanSpace ℂ (Fin (A.rank Din.frameIndex))) →L[ℂ]
          𝓢(EuclideanSpace ℝ (Fin (n + m)),
            EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))),
          (∀ u z, quantize (productCutoffSymbol α ρ ε) u z = T u z) →
          ∃ Rε : L.SobolevSpace 1 →L[ℂ] K.SobolevSpace 0,
            (∀ u, Rε (L.smoothToSobolev 1 u) = K.smoothToSobolev 0 (O (T (I u)))) ∧
              ‖Rε - R‖ ≤ C * ε := by
  classical
  let X := EuclideanSpace ℝ (Fin (n + m))
  let W := EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))
  -- Both coordinate maps are bounded in the specified original presentations.
  obtain ⟨I₀, hI₀, Ci, _, hi⟩ := Din.exists_localize_sobolev_of_mem_maximalAtlas hc L 1
  obtain ⟨O₀, hO₀, Co, _, ho⟩ := Dout.exists_extend_sobolev_of_mem_maximalAtlas hc K 0
  have hII : I = I₀ := by
    apply LinearMap.ext
    intro u
    apply SchwartzMap.ext
    intro z
    exact (hI u z).trans (hI₀ u z).symm
  have hOO : O = O₀ := by
    ext v x
    exact (hO v x).trans (hO₀ v x).symm
  let li := (schwartzSobolevCoordinateLinearMap (n + m) (A.rank Din.frameIndex) 1).comp I
  have hli (u : A.smoothSections) : ‖li u‖ ≤ Ci * ‖L.smoothToSobolev 1 u‖ := by
    change ‖schwartzSobolevCoordinate 1 (I u)‖ ≤ _
    rw [hII]
    exact hi u
  let J := li.extendOfNorm (L.smoothToSobolev 1)
  have hJ (u : A.smoothSections) :
      J (L.smoothToSobolev 1 u) = schwartzSobolevCoordinate 1 (I u) :=
    li.extendOfNorm_eq (L.denseRange_smoothToSobolev 1) ⟨Ci, hli⟩ u
  let lo := (K.smoothToSobolev 0).comp O
  have hlo (v : 𝓢(X, W)) : ‖lo v‖ ≤ Co * ‖schwartzSobolevCoordinate 0 v‖ := by
    simpa only [lo, LinearMap.comp_apply, hOO] using ho v
  let H := lo.extendOfNorm (schwartzSobolevCoordinateLinearMap (n + m)
    (B.rank Dout.frameIndex) 0)
  have hH (v : 𝓢(X, W)) : H (schwartzSobolevCoordinate 0 v) = K.smoothToSobolev 0 (O v) :=
    lo.extendOfNorm_eq
      (denseRange_schwartzSobolevCoordinate (n + m) (B.rank Dout.frameIndex) 0) ⟨Co, hlo⟩ v
  obtain ⟨S, hS, C, hC, hbound⟩ :=
    exists_liftedProductSobolev_approximation_schwartz α hα hαK ρ hρ hρK
  let R := H.comp (S.comp J)
  refine ⟨R, ?_, ‖H‖ * C * ‖J‖,
    mul_nonneg (mul_nonneg (norm_nonneg _) hC) (norm_nonneg _), ?_⟩
  · intro u
    -- The actual compact chart input has a full Schwartz Fourier output.
    have hcompact : HasCompactSupport (I u) := by
      apply Din.compact_support.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ (isClosed_tsupport Din.cutoff)
      intro z hz
      by_contra hout
      apply hz
      rw [hI]
      simp [AtlasChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hout]
    obtain ⟨v, hv, _⟩ := exists_schwartz_quantize_liftedProductSymbol_of_hasCompactSupport
      α hα hαK ρ hρ hρK (I u) hcompact
    refine ⟨v, hv, ?_⟩
    change H (S (J (L.smoothToSobolev 1 u))) = _
    rw [hJ, hS (I u) v hv, hH]
  · intro ε hε hε1 T hT
    -- The same bounded coordinate maps transport the common epsilon error.
    let Sε := productCutoffSobolevOperator α hα hαK ρ hρ hρK ε hε
    let Rε := H.comp (Sε.comp J)
    refine ⟨Rε, ?_, ?_⟩
    · intro u
      change H (Sε (J (L.smoothToSobolev 1 u))) = _
      rw [hJ, productCutoffSobolevOperator_apply α hα hαK ρ hρ hρK ε hε
        (I u) (T (I u)) (hT (I u)), hH]
    · have hdiff : Rε - R = H.comp ((Sε - S).comp J) := by
        apply ContinuousLinearMap.ext
        intro u
        simp only [Rε, R, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
      rw [hdiff]
      calc
        ‖H.comp ((Sε - S).comp J)‖ ≤ ‖H‖ * (‖Sε - S‖ * ‖J‖) :=
          (H.opNorm_comp_le _).trans
            (mul_le_mul_of_nonneg_left ((Sε - S).opNorm_comp_le J) (norm_nonneg _))
        _ ≤ ‖H‖ * ((C * ε) * ‖J‖) := by gcongr; exact hbound ε hε hε1
        _ = (‖H‖ * C * ‖J‖) * ε := by ring

end AtiyahSinger
