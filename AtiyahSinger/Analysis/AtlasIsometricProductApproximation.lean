/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSmoothChartSobolevLocalization
public import AtiyahSinger.Analysis.ProductCompactSchwartz
public import AtiyahSinger.Analysis.ProductSchwartzCutoffRealization
public import AtiyahSinger.Analysis.IsometricSymbolTransport

/-!
# Orthogonal product cutoffs in the original atlas Sobolev spaces

Public module ID: M0254.

Fixed base and fiber isometries transport the complete product-frequency
approximation, including every original Schwartz input and the actual limit.
The original chart localization, inverse-frame extension and both supplied
Sobolev presentations stay fixed. This permits the sphere and base coordinate
blocks to be exchanged for vertical regularization without changing the
associated manifold atlas or replacing its tensor frames.

Source: SG III.13.5--13.6 and orthogonal invariance of Bessel coordinates.
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
set_option maxHeartbeats 800000 in

/-- Fixed isometries transport product cutoff approximations in the specified Sobolev norms. -/
theorem exists_atlas_isometricProductCutoff_sobolev_approximation
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
    ∃ R : L.SobolevSpace 1 →L[ℂ] K.SobolevSpace 0,
      (∀ u : A.smoothSections,
        ∃ v : 𝓢(EuclideanSpace ℝ (Fin k),
            EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))),
          (∀ z, quantize (isometricSymbolTransport e i o (liftedProductSymbol α ρ)) (I u) z = v z) ∧
            R (L.smoothToSobolev 1 u) = K.smoothToSobolev 0 (O v)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ _hε : 0 < ε, ε ≤ 1 →
        ∀ T : 𝓢(EuclideanSpace ℝ (Fin k),
            EuclideanSpace ℂ (Fin (A.rank Din.frameIndex))) →L[ℂ]
          𝓢(EuclideanSpace ℝ (Fin k),
            EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))),
          (∀ u z,
            quantize (isometricSymbolTransport e i o (productCutoffSymbol α ρ ε)) u z = T u z) →
          ∃ Rε : L.SobolevSpace 1 →L[ℂ] K.SobolevSpace 0,
            (∀ u, Rε (L.smoothToSobolev 1 u) = K.smoothToSobolev 0 (O (T (I u)))) ∧
              ‖Rε - R‖ ≤ C * ε := by
  classical
  let X := EuclideanSpace ℝ (Fin k)
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
  let li := (schwartzSobolevCoordinateLinearMap k (A.rank Din.frameIndex) 1).comp I
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
  let H := lo.extendOfNorm (schwartzSobolevCoordinateLinearMap k
    (B.rank Dout.frameIndex) 0)
  have hH (v : 𝓢(X, W)) : H (schwartzSobolevCoordinate 0 v) = K.smoothToSobolev 0 (O v) :=
    lo.extendOfNorm_eq
      (denseRange_schwartzSobolevCoordinate k (B.rank Dout.frameIndex) 0) ⟨Co, hlo⟩ v
  let Ii := sobolevCoordinateIsometry e.symm i 1
  let Oo := sobolevCoordinateIsometry e o 0
  let J' := Ii.toContinuousLinearEquiv.toContinuousLinearMap.comp J
  let H' := H.comp Oo.toContinuousLinearEquiv.toContinuousLinearMap
  have hJ' (u : A.smoothSections) :
      J' (L.smoothToSobolev 1 u) =
        schwartzSobolevCoordinate 1 (schwartzCoordinateEquiv e.symm i (I u)) := by
    change Ii (J (L.smoothToSobolev 1 u)) = _
    rw [hJ, sobolevCoordinateIsometry_apply]
  have hH' (v : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin q))) :
      H' (schwartzSobolevCoordinate 0 v) =
        K.smoothToSobolev 0 (O (schwartzCoordinateEquiv e o v)) := by
    change H (Oo (schwartzSobolevCoordinate 0 v)) = _
    rw [sobolevCoordinateIsometry_apply, hH]
  -- The actual orthogonal maps transport the full Fourier expression, without a symbol assumption.
  have htransport (p : SymbolFunction (n + m) r q)
      (w : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))) (x : X) :
      quantize (isometricSymbolTransport e i o p) w x =
        o (quantize p (schwartzCoordinateEquiv e.symm i w) (e x)) := by
    have hw : schwartzCoordinateEquiv e i.symm (schwartzCoordinateEquiv e.symm i w) = w := by
      apply SchwartzMap.ext
      intro y
      change i.symm (i (w (e.symm (e y)))) = w y
      rw [e.symm_apply_apply, i.symm_apply_apply]
    simpa only [hw] using
      quantize_isometricSymbolTransport e i o p (schwartzCoordinateEquiv e.symm i w) x
  have hreturn (v : 𝓢(X, EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)))) :
      schwartzCoordinateEquiv e o (schwartzCoordinateEquiv e.symm o.symm v) = v := by
    apply SchwartzMap.ext
    intro x
    change o (o.symm (v (e.symm (e x)))) = v x
    rw [e.symm_apply_apply, o.apply_symm_apply]
  obtain ⟨S, hS, C, hC, hbound⟩ :=
    exists_liftedProductSobolev_approximation_schwartz α hα hαK ρ hρ hρK
  let R := H'.comp (S.comp J')
  refine ⟨R, ?_, ‖H'‖ * C * ‖J'‖,
    mul_nonneg (mul_nonneg (norm_nonneg _) hC) (norm_nonneg _), ?_⟩
  · intro u
    -- Orthogonal transport preserves the compact support of the actual original input.
    have hcompact : HasCompactSupport (I u) := by
      apply Din.compact_support.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ (isClosed_tsupport Din.cutoff)
      intro z hz
      by_contra hout
      apply hz
      rw [hI]
      simp [AtlasChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hout]
    let w := schwartzCoordinateEquiv e.symm i (I u)
    have hwcompact : HasCompactSupport w := by
      apply (hcompact.image e.continuous).of_isClosed_subset (isClosed_tsupport w)
      apply closure_minimal _ (hcompact.image e.continuous).isClosed
      intro x hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      apply subset_tsupport
      intro hzero
      apply hx
      change i (I u (e.symm x)) = 0
      rw [hzero, map_zero]
    obtain ⟨v, hv, _⟩ := exists_schwartz_quantize_liftedProductSymbol_of_hasCompactSupport
      α hα hαK ρ hρ hρK w hwcompact
    refine ⟨schwartzCoordinateEquiv e o v, ?_, ?_⟩
    · intro x
      rw [htransport, hv]
      rfl
    · change H' (S (J' (L.smoothToSobolev 1 u))) = _
      rw [hJ', hS w v hv, hH']
  · intro ε hε hε1 T hT
    -- The same isometries and fixed chart maps transport the common epsilon bound.
    let Sε := productCutoffSobolevOperator α hα hαK ρ hρ hρK ε hε
    let Rε := H'.comp (Sε.comp J')
    refine ⟨Rε, ?_, ?_⟩
    · intro u
      let w := schwartzCoordinateEquiv e.symm i (I u)
      let v := schwartzCoordinateEquiv e.symm o.symm (T (I u))
      have hv (x : EuclideanSpace ℝ (Fin (n + m))) :
          quantize (productCutoffSymbol α ρ ε) w x = v x := by
        apply o.injective
        have h := (htransport (productCutoffSymbol α ρ ε) (I u) (e.symm x)).symm
        rw [e.apply_symm_apply, hT] at h
        change _ = o (o.symm (T (I u) (e.symm x)))
        rw [o.apply_symm_apply]
        exact h
      change H' (Sε (J' (L.smoothToSobolev 1 u))) = _
      rw [hJ', productCutoffSobolevOperator_apply α hα hαK ρ hρ hρK ε hε w v hv,
        hH', hreturn]
    · have hdiff : Rε - R = H'.comp ((Sε - S).comp J') := by
        apply ContinuousLinearMap.ext
        intro u
        simp only [Rε, R, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
      rw [hdiff]
      calc
        ‖H'.comp ((Sε - S).comp J')‖ ≤ ‖H'‖ * (‖Sε - S‖ * ‖J'‖) :=
          (H'.opNorm_comp_le _).trans
            (mul_le_mul_of_nonneg_left ((Sε - S).opNorm_comp_le J') (norm_nonneg _))
        _ ≤ ‖H'‖ * ((C * ε) * ‖J'‖) := by gcongr; exact hbound ε hε hε1
        _ = (‖H'‖ * C * ‖J'‖) * ε := by ring

end AtiyahSinger
