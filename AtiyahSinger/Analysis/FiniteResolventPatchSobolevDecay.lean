/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FiniteResolventPatchSobolev
public import AtiyahSinger.Analysis.JointFrequencyQuantizationDecay
public import AtiyahSinger.Analysis.ScalarResolventNormalization

/-!
# Resolvent decay and integrability of the original fixed patch families

Public module ID: M0632.

The actual Sobolev patch action inherits the local quantizer's resolvent decay.
Density identifies the same global family, with its original frame and cutoffs.
Finite sums preserve that estimate, so their fractional resolvent weights are
Bochner integrable at every fixed real Sobolev level for exponents between zero and one.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped ContDiff Manifold SchwartzMap Topology

set_option maxSynthPendingDepth 30

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

namespace FiniteResolventPatch

variable {L : DifferentialOperator (n := n) (r := r) (q := r) E E 2}

/-- Joint order at most minus two gives resolvent decay for the original Sobolev patch. -/
theorem exists_continuous_decay_sobolev_piece (P : FiniteResolventPatch L)
    (A B : SmoothBundlePresentation (n := n) (r := r) E)
    (m s : ℝ) (hm : m ≤ -2) (a : SymbolFunction (n + 1) r r)
    (ha : IsSymbol
      ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹'
          (P.chart '' P.domain)) m a) :
    ∃ T : ℝ → (A.SobolevSpace s →L[ℂ] B.SobolevSpace s),
      Continuous T ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ‖T τ‖ ≤ C / (1 + τ)) ∧
      ∀ (τ : ℝ) (hτ : 0 < τ) (u : smoothSections (n := n) (r := r) E),
        T τ (A.smoothToSobolev s u) =
          B.smoothToSobolev s ((P.piece m (by linarith) a ha τ hτ).toLinearMap u) := by
  classical
  have hfamily : ∃ T : ℝ → (A.SobolevSpace s →L[ℂ] B.SobolevSpace s),
      Continuous T ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ‖T τ‖ ≤ C) ∧
      ∀ (τ : ℝ) (hτ : 0 < τ) (u : smoothSections (n := n) (r := r) E),
        T τ (A.smoothToSobolev s u) =
          B.smoothToSobolev s ((P.piece m (by linarith) a ha τ hτ).toLinearMap u) := by
    -- Transport the whole dependent family, including the Sobolev normed structures.
    let H (t : ℝ) : Prop :=
      ∃ T : ℝ → (A.SobolevSpace s →L[ℂ] B.SobolevSpace t),
        Continuous T ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ‖T τ‖ ≤ C) ∧
        ∀ (τ : ℝ) (hτ : 0 < τ) (u : smoothSections (n := n) (r := r) E),
          T τ (A.smoothToSobolev s u) =
            B.smoothToSobolev t ((P.piece m (by linarith) a ha τ hτ).toLinearMap u)
    have hfamily₀ : H (s - 0) :=
      P.exists_continuous_uniform_sobolev_piece A B m 0 s
        (by linarith) le_rfl (by linarith) a ha
    exact (congrArg H (sub_zero s)).mp hfamily₀
  obtain ⟨T, hTcontinuous, _, hTaction⟩ := hfamily
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin (n + 1))
  let D := P.chart '' P.domain
  let W := (fun z : Y ↦
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹' D
  have hD : IsOpen D := P.chart.isOpen_image_of_subset_source P.isOpen_domain
    (fun x hx ↦ (P.hasCoordinateExpression.1 hx).1.1)
  have hW : IsOpen W :=
    hD.preimage (continuous_fst.comp EuclideanSpace.finAddEquivProd.continuous)
  have hDW : ∀ x ∈ D, EuclideanSpace.finAddEquivProd.symm
      (x, (0 : EuclideanSpace ℝ (Fin 1))) ∈ W := by
    intro x hx
    simpa only [W, Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hx
  -- The local decay estimate is for the same symbol, with only its order certificate weakened.
  obtain ⟨hslice, C, hC, hbound⟩ := exists_decay_quantizeSobolev_jointFrequencySymbolSlice
    W hW a (ha.mono hm) D hD hDW P.cutoff.cutoff P.cutoff.smooth_cutoff
    P.cutoff.compact_support P.support_cutoff s
  let p (τ : ℝ) := zeroExtendedSymbol D P.cutoff.cutoff (jointFrequencySymbolSlice a τ)
  have hp (τ : ℝ) (hτ : 0 < τ) : IsSymbol univ 0 (p τ) :=
    isSymbol_zeroExtendedSymbol D hD 0 P.cutoff.cutoff P.cutoff.smooth_cutoff
      P.cutoff.compact_support P.support_cutoff _ (hslice τ hτ)
  have hcp (τ : ℝ) : HasCompactSupport (p τ) :=
    hasCompactSupport_zeroExtendedSymbol D P.cutoff.cutoff _ P.cutoff.compact_support
  let Q (τ : ℝ) (hτ : 0 < τ) := quantizeSobolev 0 s (p τ) (hp τ hτ) (hcp τ)
  have hQbound (τ : ℝ) (hτ : 0 < τ) : ‖Q τ hτ‖ ≤ C / (1 + τ) := hbound τ hτ
  obtain ⟨I, hI⟩ := P.cutoff.exists_sobolev_localization P.chart_mem_atlas A s
  obtain ⟨O, hO⟩ := P.cutoff.exists_sobolev_extension P.chart_mem_atlas B s
  have hfactor (τ : ℝ) (hτ : 0 < τ) : T τ = O.comp ((Q τ hτ).comp I) := by
    have hsymbol : (P.piece m (by linarith) a ha τ hτ).symbol = p τ := by
      rfl
    -- The two bounded maps agree on the same original dense smooth section image.
    have hQ (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
        Q τ hτ (schwartzSobolevCoordinate s v) = schwartzSobolevCoordinate (s - 0)
          ((P.piece m (by linarith) a ha τ hτ).operator v) := by
      apply besselRealization_injective n r (s - 0)
      ext1 φ
      rw [besselRealization_quantizeSobolev, besselRealization_schwartzSobolevCoordinate,
        SchwartzMap.coe_apply]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [(P.piece m (by linarith) a ha τ hτ).operator_apply, hsymbol]
    simp only [sub_zero] at hQ
    apply DFunLike.ext'
    apply (A.denseRange_smoothToSobolev s).equalizer
      (T τ).continuous (O.comp ((Q τ hτ).comp I)).continuous
    funext u
    change T τ (A.smoothToSobolev s u) = O (Q τ hτ (I (A.smoothToSobolev s u)))
    rw [hTaction, hI, hQ, hO]
    rfl
  refine ⟨T, hTcontinuous, ⟨‖O‖ * C * ‖I‖, by positivity, ?_⟩, hTaction⟩
  intro τ hτ
  rw [hfactor τ hτ]
  calc
    ‖O.comp ((Q τ hτ).comp I)‖ ≤ ‖O‖ * ‖(Q τ hτ).comp I‖ := O.opNorm_comp_le _
    _ ≤ ‖O‖ * (‖Q τ hτ‖ * ‖I‖) :=
      mul_le_mul_of_nonneg_left ((Q τ hτ).opNorm_comp_le I) (norm_nonneg _)
    _ ≤ ‖O‖ * ((C / (1 + τ)) * ‖I‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hQbound τ hτ) (norm_nonneg _)) (norm_nonneg _)
    _ = (‖O‖ * C * ‖I‖) / (1 + τ) := by ring

/-- Each original recursive term has resolvent decay on every fixed real Sobolev level. -/
theorem exists_continuous_decay_sobolev_term (P : FiniteResolventPatch L)
    (A : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ) (j : ℕ) :
    ∃ T : ℝ → (A.SobolevSpace s →L[ℂ] A.SobolevSpace s),
      Continuous T ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ‖T τ‖ ≤ C / (1 + τ)) ∧
      ∀ (τ : ℝ) (hτ : 0 < τ) (u : smoothSections (n := n) (r := r) E),
        T τ (A.smoothToSobolev s u) = A.smoothToSobolev s (P.term j τ hτ u) := by
  exact P.exists_continuous_decay_sobolev_piece A A (-2 - (j : ℝ)) s
    (by have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j; linarith)
    (P.symbol j) (P.isSymbol_symbol j)

/-- The fixed finite sum has a continuous Sobolev family and integrable fractional weights. -/
theorem exists_integrable_sobolev_sum_terms {k : ℕ} (P : Fin k → FiniteResolventPatch L)
    (A : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ) (N : ℕ) :
    ∃ T : ℝ → (A.SobolevSpace s →L[ℂ] A.SobolevSpace s),
      Continuous T ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ‖T τ‖ ≤ C / (1 + τ)) ∧
      (∀ p : ℝ, 0 < p → p < 1 →
        IntegrableOn (fun τ : ℝ ↦ ((τ ^ (-p) : ℝ) : ℂ) • T τ) (Ioi 0)) ∧
      ∀ (τ : ℝ) (hτ : 0 < τ) (u : smoothSections (n := n) (r := r) E),
        T τ (A.smoothToSobolev s u) =
          A.smoothToSobolev s (∑ i, ∑ j ∈ Finset.range N, (P i).term j τ hτ u) := by
  classical
  let : NormedSpace ℝ (A.SobolevSpace s) := NormedSpace.restrictScalars ℝ ℂ _
  let : NormedSpace ℝ (A.SobolevSpace s →L[ℂ] A.SobolevSpace s) :=
    NormedSpace.restrictScalars ℝ ℂ _
  let : SecondCountableTopologyEither ℝ
      (A.SobolevSpace s →L[ℂ] A.SobolevSpace s) := ⟨Or.inl inferInstance⟩
  choose T hcontinuous hbounded haction using
    (fun (i : Fin k) (j : ℕ) ↦ (P i).exists_continuous_decay_sobolev_term A s j)
  choose C hC hbound using hbounded
  let R (τ : ℝ) := ∑ i : Fin k, ∑ j ∈ Finset.range N, T i j τ
  let D : ℝ := ∑ i : Fin k, ∑ j ∈ Finset.range N, C i j
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hC i j
  have hRcontinuous : Continuous R :=
    continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦ hcontinuous i j
  have hRbound (τ : ℝ) (hτ : 0 < τ) : ‖R τ‖ ≤ D / (1 + τ) := by
    calc
      ‖R τ‖ ≤ ∑ i : Fin k, ‖∑ j ∈ Finset.range N, T i j τ‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin k, ∑ j ∈ Finset.range N, ‖T i j τ‖ :=
        Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _
      _ ≤ ∑ i : Fin k, ∑ j ∈ Finset.range N, C i j / (1 + τ) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hbound i j τ hτ
      _ = D / (1 + τ) := by simp only [D, Finset.sum_div]
  refine ⟨R, hRcontinuous, ⟨D, hD, hRbound⟩, ?_, ?_⟩
  · intro p hp hp1
    -- The scalar resolvent profile controls the Bochner norm on the whole positive half-line.
    have hweight : IntegrableOn (fun τ : ℝ ↦ τ ^ (-p) / (1 + τ)) (Ioi 0) :=
      (scalar_resolvent_integral_normalization p hp hp1 1 zero_lt_one).2.1
    have hw : ContinuousOn (fun τ : ℝ ↦ τ ^ (-p)) (Ioi 0) :=
      continuousOn_id.rpow_const (fun τ hτ ↦ Or.inl (ne_of_gt hτ))
    have hweighted : ContinuousOn (fun τ : ℝ ↦ ((τ ^ (-p) : ℝ) : ℂ) • R τ) (Ioi 0) :=
      (Complex.continuous_ofReal.comp_continuousOn hw).smul hRcontinuous.continuousOn
    apply (hweight.const_mul D).mono' (hweighted.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hτ.le _)]
    calc
      τ ^ (-p) * ‖R τ‖ ≤ τ ^ (-p) * (D / (1 + τ)) :=
        mul_le_mul_of_nonneg_left (hRbound τ hτ) (Real.rpow_nonneg hτ.le _)
      _ = D * (τ ^ (-p) / (1 + τ)) := by ring
  · intro τ hτ u
    dsimp only [R]
    simp only [sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact haction i j τ hτ u

end FiniteResolventPatch

end AtiyahSinger
