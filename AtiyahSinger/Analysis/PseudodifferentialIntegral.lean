/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactAmplitudePrincipalSymbol
public import AtiyahSinger.Analysis.CompactSymbolIntegral
public import AtiyahSinger.Analysis.GlobalPseudodifferentialOperator

/-!
# Compact integration in fixed local PDO coordinates

Public module ID: M0894.

A uniformly controlled continuous family of local symbols, quantized between
one fixed pair of the original chart cutoffs, integrates to an actual original
PDO piece. A separate compact plateau supplies the Schwartz realization of the
integrated symbol without changing either original cutoff or squaring its weight.

The uniform jet hypotheses concern the actual local symbols. They are not
inferred from an arbitrary pointwise choice of a PDO representation. Applying
this result to moving-coordinate families requires proving those hypotheses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory Set
open scoped ContDiff Manifold SchwartzMap

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]

set_option maxSynthPendingDepth 20 in
/-- A uniform symbol family in fixed original cutoffs integrates to an actual PDO piece. -/
theorem PseudodifferentialPiece.exists_integral_of_uniform_symbols {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (a : Y → SymbolFunction n r q) (ha : ∀ y, IsSymbol univ m (a y))
    (T : Y → (𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))))
    (hT : ∀ y u z, T y u z = quantize (a y) u z)
    (hmixed : ∀ i j : ℕ, Continuous
      (fun p : Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        symbolDerivative (a p.1) i j p.2.1 p.2.2))
    (hjoint : ∀ k : ℕ, Continuous
      (fun p : Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ k (Function.uncurry (a p.1)) p.2))
    (hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ z ∈ K, ∀ ξ,
        ‖symbolDerivative (a y) i j z ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - (j : ℝ))) :
    ∃ Q : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m,
      ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
        (Q.toLinearMap u).val x =
          ∫ y, (L.output.extendLinearMap L.chart_mem_atlas
            (T y (L.input.localize L.chart_mem_atlas u))).val x ∂μ := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let abar : SymbolFunction n r q := fun z ξ ↦ ∫ y, a y z ξ ∂μ
  have habar : IsSymbol univ m abar :=
    isSymbol_integral_of_continuous_jets μ isOpen_univ a ha
      (fun i j ↦ (hmixed i j).continuousOn) (fun k ↦ (hjoint k).continuousOn)
      (fun K _ hK ↦ hbound K hK)
  -- A plateau, equal to one on the existing output support, makes the symbol compact.
  obtain ⟨O, hO, hKO, _, hOc⟩ := exists_open_between_and_isCompact_closure
    L.output.compact_support isOpen_univ (subset_univ (tsupport L.output.cutoff))
  obtain ⟨γ, hγ, _, hsγ, honeγ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO (isClosed_tsupport L.output.cutoff) hKO
  have hcγ : HasCompactSupport γ := by
    change IsCompact (tsupport γ)
    rw [show tsupport γ = closure O from congrArg closure hsγ]
    exact hOc
  let b := zeroExtendedSymbol univ γ abar
  have hb : IsSymbol univ m b :=
    isSymbol_zeroExtendedSymbol univ isOpen_univ m γ hγ hcγ (subset_univ _) abar habar
  have hbc : HasCompactSupport b := hasCompactSupport_zeroExtendedSymbol univ γ abar hcγ
  let Q : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
    { L with
      symbol := b
      isSymbol := hb
      operator := quantizeSchwartz m b hb hbc
      operator_apply := quantizeSchwartz_apply m b hb hbc }
  have hquantize (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) :
      quantize b u z = (γ z : ℂ) • quantize abar u z := by
    simp only [quantize, b, zeroExtendedSymbol, mem_univ, ite_true,
      smul_apply, smul_comm (Complex.exp _), integral_smul]
    exact smul_comm _ _ _
  have haverage (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) :
      quantize abar u z = ∫ y, T y u z ∂μ := by
    simp_rw [hT]
    apply quantize_integral_of_uniform_bound μ (m := m) a u z
    · have hc := (continuousMultilinearCurryFin0 ℝ (X × X)
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))).continuous.comp
          (hjoint 0)
      change Continuous (fun p : Y × (X × X) ↦
        (iteratedFDeriv ℝ 0 (Function.uncurry (a p.1)) p.2).curry0) at hc
      have hc' : Continuous (fun p : Y × (X × X) ↦ a p.1 p.2.1 p.2.2) := by
        simpa only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.curry0_apply,
          Function.comp_def, Function.uncurry, id_eq] using hc
      exact hc'.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
    · obtain ⟨C, hC, hCbound⟩ := hbound {z} isCompact_singleton 0 0
      refine ⟨C, hC, fun y ξ ↦ ?_⟩
      simpa only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero]
        using hCbound y z (mem_singleton z) ξ
  -- Return to the same original output fiber; the original cutoffs stay unchanged.
  refine ⟨Q, fun u x ↦ ?_⟩
  change L.output.extendedFunction
    (quantizeSchwartz m b hb hbc (L.input.localize L.chart_mem_atlas u)) x =
      ∫ y, L.output.extendedFunction (T y (L.input.localize L.chart_mem_atlas u)) x ∂μ
  by_cases hx : x ∈ L.chart.source
  · simp only [BundleChartCutoff.extendedFunction, ite_eq_left hx]
    rw [quantizeSchwartz_apply, hquantize]
    by_cases hcut : L.output.cutoff (L.chart x) = 0
    · simp only [hcut, Complex.ofReal_zero, zero_smul, integral_zero]
    · have hz : L.chart x ∈ tsupport L.output.cutoff := subset_tsupport _ hcut
      have hf : x ∈ L.output.frame.baseSet := by
        have hf := (L.output.support_subset hz).2
        change L.chart.symm (L.chart x) ∈ L.output.frame.baseSet at hf
        rwa [L.chart.left_inv hx] at hf
      rw [(honeγ _).mp hz, Complex.ofReal_one, one_smul, haverage]
      let := L.output.frame_mem_atlas
      let C := (L.output.frame.linearEquivAt ℂ x hf).symm.toContinuousLinearEquiv
      have hmap (v : EuclideanSpace ℂ (Fin q)) : L.output.frame.symmL ℂ x v = C v :=
        L.output.frame.symmL_apply hf v
      simp only [hmap, integral_smul]
      rw [C.integral_comp_comm]
  · simp only [BundleChartCutoff.extendedFunction, ite_eq_right hx, integral_zero]

set_option maxSynthPendingDepth 25 in
/-- A uniform compact amplitude family in fixed original cutoffs integrates to a PDO piece. -/
theorem PseudodifferentialPiece.exists_integral_of_uniform_amplitudes {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (a : Y → AmplitudeFunction n r q) (ha : ∀ t, IsAmplitude m (a t))
    (T : Y → (𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))))
    (hT : ∀ t u z, T t u z = amplitudeApply (a t) u z)
    (K : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hsupp : ∀ t, tsupport (Function.uncurry (a t)) ⊆ K)
    (hmixed : ∀ i j k : ℕ, Continuous
      (fun p : Y × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n)) ↦ amplitudeDerivative (a p.1) i j k
          p.2.1.1 p.2.1.2 p.2.2))
    (hjoint : ∀ l : ℕ, Continuous
      (fun p : Y × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n)) ↦ iteratedFDeriv ℝ l
          (fun z : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
            EuclideanSpace ℝ (Fin n) ↦ a p.1 z.1.1 z.1.2 z.2) p.2))
    (hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      IsCompact K → ∀ i j k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t x y, (x, y) ∈ K → ∀ ξ,
        ‖amplitudeDerivative (a t) i j k x y ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - (k : ℝ))) :
    ∃ Q : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m,
      ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
        (Q.toLinearMap u).val x =
          ∫ t, (L.output.extendLinearMap L.chart_mem_atlas
            (T t (L.input.localize L.chart_mem_atlas u))).val x ∂μ := by
  obtain ⟨Q, hQ, _⟩ := L.exists_integral_of_uniform_amplitudes_with_principalSymbol
    μ a ha T hT K hK hsupp hmixed hjoint hbound
  exact ⟨Q, hQ⟩

end AtiyahSinger
