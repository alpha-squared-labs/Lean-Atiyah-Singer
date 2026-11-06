/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianFiniteResolvent
public import AtiyahSinger.Analysis.JointFrequencyQuantizationContinuous
public import AtiyahSinger.Analysis.SobolevCutoffMaps

/-!
# Sobolev families for the original fixed resolvent patches

Public module ID: M0631.

A fixed patch retains its chart, frame, cutoff and joint symbol. Its actual
section action is realized by the original Sobolev quantizer between the same
bounded localization and extension maps. A one-order gap gives continuity in
operator norm, and the joint estimate gives one bound for all positive parameters.
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

/-- The same fixed patch has continuous, uniformly bounded Sobolev realizations.
The one-order gap is explicit; the smooth action is the original piece at order m. -/
theorem exists_continuous_uniform_sobolev_piece (P : FiniteResolventPatch L)
    (A B : SmoothBundlePresentation (n := n) (r := r) E)
    (m l s : ℝ) (hm : m ≤ 0) (hl : l ≤ 0) (hml : m + 1 ≤ l)
    (a : SymbolFunction (n + 1) r r)
    (ha : IsSymbol
      ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹'
          (P.chart '' P.domain)) m a) :
    ∃ T : ℝ → (A.SobolevSpace s →L[ℂ] B.SobolevSpace (s - l)),
      Continuous T ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ‖T τ‖ ≤ C) ∧
      ∀ (τ : ℝ) (hτ : 0 < τ) (u : smoothSections (n := n) (r := r) E),
        T τ (A.smoothToSobolev s u) =
          B.smoothToSobolev (s - l) ((P.piece m hm a ha τ hτ).toLinearMap u) := by
  classical
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
  -- Continuity uses a weaker joint order but retains the original symbol itself.
  have ha' : IsSymbol W (l - 1) a := ha.mono (by linarith)
  obtain ⟨hslice, hcontinuous⟩ := continuous_quantizeSobolev_jointFrequencySymbolSlice
    W hW (l - 1) s (by linarith) a ha' D hD hDW P.cutoff.cutoff
    P.cutoff.smooth_cutoff P.cutoff.compact_support P.support_cutoff
  have hlorder : l - 1 + 1 = l := by ring
  let p (τ : ℝ) := zeroExtendedSymbol D P.cutoff.cutoff (jointFrequencySymbolSlice a τ)
  have hp (τ : ℝ) : IsSymbol univ l (p τ) :=
    isSymbol_zeroExtendedSymbol D hD l P.cutoff.cutoff P.cutoff.smooth_cutoff
      P.cutoff.compact_support P.support_cutoff _ ((hslice τ).mono (by linarith))
  have hcp (τ : ℝ) : HasCompactSupport (p τ) :=
    hasCompactSupport_zeroExtendedSymbol D P.cutoff.cutoff _ P.cutoff.compact_support
  let Q (τ : ℝ) := quantizeSobolev l s (p τ) (hp τ) (hcp τ)
  have hQcontinuous : Continuous Q := by
    simpa only [hlorder] using hcontinuous
  -- The all-parameter bound is for this same named quantizer and the same cutoff.
  obtain ⟨_, C, hC, hbound⟩ := exists_uniform_quantizeSobolev_jointFrequencySymbolSlice
    W hW l s hl a (ha.mono (by linarith)) D hD hDW P.cutoff.cutoff
    P.cutoff.smooth_cutoff P.cutoff.compact_support P.support_cutoff
  have hQbound (τ : ℝ) (hτ : 0 < τ) : ‖Q τ‖ ≤ C := hbound τ hτ
  -- The patch's input and output maps are fixed before the parameter is selected.
  obtain ⟨I, hI⟩ := P.cutoff.exists_sobolev_localization P.chart_mem_atlas A s
  obtain ⟨O, hO⟩ := P.cutoff.exists_sobolev_extension P.chart_mem_atlas B (s - l)
  let T (τ : ℝ) : A.SobolevSpace s →L[ℂ] B.SobolevSpace (s - l) :=
    O.comp ((Q τ).comp I)
  have hTcontinuous : Continuous T :=
    continuous_const.clm_comp (hQcontinuous.clm_comp continuous_const)
  refine ⟨T, hTcontinuous, ⟨‖O‖ * (C * ‖I‖), by positivity, ?_⟩, ?_⟩
  · intro τ hτ
    calc
      ‖T τ‖ ≤ ‖O‖ * ‖(Q τ).comp I‖ := O.opNorm_comp_le _
      _ ≤ ‖O‖ * (‖Q τ‖ * ‖I‖) :=
        mul_le_mul_of_nonneg_left ((Q τ).opNorm_comp_le I) (norm_nonneg _)
      _ ≤ ‖O‖ * (C * ‖I‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hQbound τ hτ) (norm_nonneg _)) (norm_nonneg _)
  · intro τ hτ u
    -- The piece retains exactly the same zero-extended symbol, with a different order certificate.
    have hsymbol : (P.piece m hm a ha τ hτ).symbol = p τ := by
      rfl
    -- Identify the original Schwartz output, independently of the symbol-order certificate.
    have hQ (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
        Q τ (schwartzSobolevCoordinate s v) = schwartzSobolevCoordinate (s - l)
          ((P.piece m hm a ha τ hτ).operator v) := by
      apply besselRealization_injective n r (s - l)
      ext1 φ
      rw [besselRealization_quantizeSobolev, besselRealization_schwartzSobolevCoordinate,
        SchwartzMap.coe_apply]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [(P.piece m hm a ha τ hτ).operator_apply, hsymbol]
    change O (Q τ (I (A.smoothToSobolev s u))) = _
    rw [hI, hQ, hO]
    rfl

/-- Each original recursive term has a continuous Sobolev family on the fixed patch. -/
theorem exists_continuous_uniform_sobolev_term (P : FiniteResolventPatch L)
    (A B : SmoothBundlePresentation (n := n) (r := r) E)
    (j : ℕ) (l s : ℝ) (hl : l ≤ 0) (hjl : -1 - (j : ℝ) ≤ l) :
    ∃ T : ℝ → (A.SobolevSpace s →L[ℂ] B.SobolevSpace (s - l)),
      Continuous T ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ‖T τ‖ ≤ C) ∧
      ∀ (τ : ℝ) (hτ : 0 < τ) (u : smoothSections (n := n) (r := r) E),
        T τ (A.smoothToSobolev s u) =
          B.smoothToSobolev (s - l) (P.term j τ hτ u) := by
  exact P.exists_continuous_uniform_sobolev_piece A B (-2 - (j : ℝ)) l s
    (by have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j; linarith) hl (by linarith)
    (P.symbol j) (P.isSymbol_symbol j)

/-- The explicit finite remainder has a continuous Sobolev family at every allowed lower order. -/
theorem exists_continuous_uniform_sobolev_remainder (P : FiniteResolventPatch L)
    (A B : SmoothBundlePresentation (n := n) (r := r) E)
    (N : ℕ) (l s : ℝ) (hl : l ≤ 0) (hNl : 1 - (N : ℝ) ≤ l) :
    ∃ T : ℝ → (A.SobolevSpace s →L[ℂ] B.SobolevSpace (s - l)),
      Continuous T ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ‖T τ‖ ≤ C) ∧
      ∀ (τ : ℝ) (hτ : 0 < τ) (u : smoothSections (n := n) (r := r) E),
        T τ (A.smoothToSobolev s u) =
          B.smoothToSobolev (s - l) (P.remainder N τ hτ u) := by
  exact P.exists_continuous_uniform_sobolev_piece A B (-(N : ℝ)) l s
    (neg_nonpos.mpr (Nat.cast_nonneg N)) hl (by linarith)
    (P.remainderSymbol N) (P.isSymbol_remainder N)

end FiniteResolventPatch

end AtiyahSinger
