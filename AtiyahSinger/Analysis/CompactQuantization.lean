/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Pseudolocal

import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Compact spatial cutoffs and continuous Schwartz quantization

Public module ID: M0357.

D05/A02/A03: local prerequisites for partition-of-unity quantization, following
SG III.3.2 and the assembly discussion preceding III.3.18. Spatial compactness is
explicit: an arbitrary symbol with only local spatial estimates need not preserve
Schwartz space. The operator below is uniquely specified by the actual integral.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff SchwartzMap

variable {n r q : ℕ}

/-- Multiply a symbol on an open spatial domain by a cutoff and extend it by zero. -/
def zeroExtendedSymbol (U : Set (EuclideanSpace ℝ (Fin n)))
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (p : SymbolFunction n r q) :
    SymbolFunction n r q := by
  classical
  exact fun x ξ ↦ if x ∈ U then (χ x : ℂ) • p x ξ else 0

/-- The extension uses the specified cutoff formula at every point in the domain. -/
theorem zeroExtendedSymbol_apply_of_mem (U : Set (EuclideanSpace ℝ (Fin n)))
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (p : SymbolFunction n r q)
    (x ξ : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) :
    zeroExtendedSymbol U χ p x ξ = (χ x : ℂ) • p x ξ := by
  /- The membership hypothesis selects the first branch of the zero extension.
  No regularity or support property is required for this pointwise identity. -/
  simp only [zeroExtendedSymbol, ite_eq_left hx]

/-- Spatial support of the extended symbol lies in the cutoff's closed support. -/
theorem tsupport_zeroExtendedSymbol_subset (U : Set (EuclideanSpace ℝ (Fin n)))
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (p : SymbolFunction n r q) :
    tsupport (zeroExtendedSymbol U χ p) ⊆ tsupport χ := by
  /- If χ vanishes on a neighborhood, the symbol is identically zero in the
  frequency variable throughout that neighborhood, regardless of its branch.
  Equivalently take closures of the inclusion between the nonzero spatial sets. -/
  -- The support concerns the entire frequency-valued function at each spatial point.
  apply closure_minimal ?_ (isClosed_tsupport χ)
  intro x hx
  by_contra hxχ
  have hzero : χ x = 0 := image_eq_zero_of_notMem_tsupport hxχ
  apply hx
  funext ξ
  simp [zeroExtendedSymbol, hzero]

/-- Compact cutoff support gives compact spatial support of the whole symbol. -/
theorem hasCompactSupport_zeroExtendedSymbol (U : Set (EuclideanSpace ℝ (Fin n)))
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (p : SymbolFunction n r q)
    (hc : HasCompactSupport χ) : HasCompactSupport (zeroExtendedSymbol U χ p) := by
  /- The symbol's topological support is closed and lies in the compact support
  of χ by the preceding inclusion. A closed subset of a compact set is compact. -/
  exact hc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_zeroExtendedSymbol_subset U χ p)

/-- Compact support strictly inside the open domain makes zero extension a global symbol. -/
theorem isSymbol_zeroExtendedSymbol (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (m : ℝ) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U)
    (p : SymbolFunction n r q) (hp : IsSymbol U m p) :
    IsSymbol Set.univ m (zeroExtendedSymbol U χ p) := by
  /- Near the cutoff support use the smooth product formula. Outside that closed
  support the extension is locally zero, including at the boundary of U, giving
  joint smoothness on the full space. On the fixed compact cutoff support inside U,
  Leibniz's rule combines finitely many cutoff and symbol derivative bounds. Outside
  it, every mixed derivative vanishes. No smoothness of the totalized p outside U
  is required. -/
  classical
  let P := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  have hχc : ContDiff ℝ ∞ (fun x ↦ (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  -- Outside the closed cutoff support the full frequency-valued symbol vanishes locally.
  have hzero (x : P) (hx : x ∉ tsupport χ) :
      zeroExtendedSymbol U χ p =ᶠ[nhds x] (fun _ ↦ 0) := by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    funext ξ
    simp [zeroExtendedSymbol, image_eq_zero_of_notMem_tsupport hy]
  refine ⟨?_, ?_⟩
  · intro z _
    apply ContDiffAt.contDiffWithinAt
    by_cases hz : z.1 ∈ tsupport χ
    · have hpz := hp.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds
        ⟨hs hz, Set.mem_univ z.2⟩)
      apply ((hχc.contDiffAt.comp z contDiffAt_fst).smul hpz).congr_of_eventuallyEq
      filter_upwards [continuous_fst.continuousAt (hU.mem_nhds (hs hz))] with y hy
      change y.1 ∈ U at hy
      simp only [Function.uncurry, zeroExtendedSymbol, ite_eq_left hy]
      rfl
    · apply (contDiffAt_const (c := (0 : H))).congr_of_eventuallyEq
      filter_upwards [continuous_fst.continuousAt (hzero z.1 hz)] with y hy
      exact congrFun hy y.2
  · intro K _ _ i j
    -- Parameter differentiation retains smoothness before applying the spatial product rule.
    have parametric {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
        (f : P → P → V) (x ξ : P)
        (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, ξ)) (k : ℕ) :
        ContDiffAt ℝ ∞ (fun z : P × P ↦ iteratedFDeriv ℝ k (f z.1) z.2) (x, ξ) := by
      induction k with
      | zero =>
        exact hf.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ P V).symm : _ →L[ℝ] P [×0]→L[ℝ] V)
      | succ k ih =>
        have h : ContDiffAt ℝ ∞
            (Function.uncurry (fun z : P × P ↦ fun η : P ↦ iteratedFDeriv ℝ k (f z.1) η))
            ((x, ξ), ξ) := ih.comp ((x, ξ), ξ) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
        have hd : ContDiffAt ℝ ∞
            (fun z : P × P ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) (x, ξ) :=
          h.fderiv contDiffAt_snd (by simp)
        exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ P) V).symm :
            _ →L[ℝ] P [×(k + 1)]→L[ℝ] V)
    have hfreq (ξ : P) : ContDiffOn ℝ ∞ (fun x ↦ iteratedFDeriv ℝ j (p x) ξ) U := by
      intro x hx
      exact ((parametric p x ξ
        (hp.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, Set.mem_univ ξ⟩)) j).comp x
          (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
    -- The fixed support itself is compact in U, and controls every cutoff and symbol derivative.
    have hbounded (k : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ tsupport χ,
        ‖iteratedFDeriv ℝ k (fun y ↦ (χ y : ℂ)) x‖ ≤ B := by
      obtain ⟨B, hB⟩ := (hc.image (hχc.continuous_iteratedFDeriv (by simp)).norm).bddAbove
      exact ⟨max B 0, le_max_right _ _, fun x hx ↦
        (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
    choose B hB hb using hbounded
    choose C hC hcBound using fun k ↦ hp.2 (tsupport χ) hs hc k j
    refine ⟨∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * B k * C (i - k),
      Finset.sum_nonneg (fun k _ ↦ mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hB k)) (hC (i - k))), ?_⟩
    intro x _ ξ
    by_cases hx : x ∈ tsupport χ
    · have hxU := hs hx
      have heq : (fun y ↦ iteratedFDeriv ℝ j (zeroExtendedSymbol U χ p y) ξ) =ᶠ[nhds x]
          (fun y ↦ (χ y : ℂ) • iteratedFDeriv ℝ j (p y) ξ) := by
        filter_upwards [hU.mem_nhds hxU] with y hy
        have hpy := (hp.1.contDiffAt
          ((hU.prod isOpen_univ).mem_nhds ⟨hy, Set.mem_univ ξ⟩)).comp ξ
            (contDiffAt_const.prodMk contDiffAt_id)
        have hformula : zeroExtendedSymbol U χ p y =
            fun η ↦ (χ y : ℂ) • p y η :=
          funext (fun η ↦ zeroExtendedSymbol_apply_of_mem U χ p y η hy)
        rw [hformula]
        exact iteratedFDeriv_const_smul_apply' (hpy.of_le (by simp))
      rw [symbolDerivative, (heq.iteratedFDeriv ℝ i).eq_of_nhds]
      have hbound := norm_iteratedFDerivWithin_smul_le hχc.contDiffOn (hfreq ξ)
        hU.uniqueDiffOn hxU (n := i) (by simp)
      simp only [iteratedFDerivWithin_of_isOpen _ hU hxU] at hbound
      apply hbound.trans
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro k hk
      have hpk := hcBound (i - k) x hx ξ
      change ‖iteratedFDeriv ℝ (i - k) (fun y ↦ iteratedFDeriv ℝ j (p y) ξ) x‖ ≤ _ at hpk
      calc
        (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k (fun y ↦ (χ y : ℂ)) x‖ *
            ‖iteratedFDeriv ℝ (i - k) (fun y ↦ iteratedFDeriv ℝ j (p y) ξ) x‖ ≤
            (i.choose k : ℝ) * B k * (C (i - k) * (1 + ‖ξ‖) ^ (m - (j : ℝ))) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hb k x hx) (Nat.cast_nonneg _)) hpk
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB k))
        _ = _ := by ring
    · -- Off that support every mixed derivative is the derivative of a local zero family.
      have heq : (fun y ↦ iteratedFDeriv ℝ j (zeroExtendedSymbol U χ p y) ξ) =ᶠ[nhds x]
          (fun _ ↦ 0) := by
        filter_upwards [hzero x hx] with y hy
        rw [hy]
        exact congrFun (iteratedFDeriv_zero (𝕜 := ℝ) (n := j)) ξ
      rw [symbolDerivative, (heq.iteratedFDeriv ℝ i).eq_of_nhds]
      simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (Finset.sum_nonneg (fun k _ ↦ mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hB k)) (hC (i - k))))
        (Real.rpow_nonneg (by positivity) _)

set_option maxSynthPendingDepth 20 in
/-- SG 3.2 with compact spatial support: the integral specifies one continuous Schwartz map. -/
theorem existsUnique_quantizeSchwartz (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hc : HasCompactSupport p) :
    ∃! T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
      ∀ u x, T u x = quantize p u x := by
  /- Integral additivity and complex homogeneity give linearity of the exact
  pointwise quantization formula. The established finite seminorm estimates supply
  smooth outputs and continuity for each output seminorm, using compact spatial
  support and rapid Fourier decay. SchwartzMap.mkCLM packages these data as one
  continuous operator. Pointwise equality then determines that operator uniquely. -/
  have hInt (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
      (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (x : EuclideanSpace ℝ (Fin n)) :
      MeasureTheory.Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        p x ξ (fourierSG u ξ)) := by
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let F := EuclideanSpace ℂ (Fin q)
    -- At each fixed spatial point, the symbol is a temperate frequency multiplier.
    have hg : (p x).HasTemperateGrowth := by
      refine ⟨?_, ?_⟩
      · have hs : ContDiff ℝ ∞ (Function.uncurry p) := by
          simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
        exact hs.comp (contDiff_const.prodMk contDiff_id)
      · intro j
        obtain ⟨C, hC, hbound⟩ := hp.2 {x} (Set.subset_univ _) isCompact_singleton 0 j
        refine ⟨⌈m - (j : ℝ)⌉₊, C, fun ξ ↦ ?_⟩
        have h := hbound x (Set.mem_singleton x) ξ
        simp only [symbolDerivative, norm_iteratedFDeriv_zero] at h
        apply h.trans
        apply mul_le_mul_of_nonneg_left _ hC
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil _)
    have hphase : (fun ξ : V ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))).HasTemperateGrowth := by
      simpa [Function.comp_def, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ x).hasTemperateGrowth
    -- The Fourier convention differs by an invertible real dilation, preserving Schwartz space.
    have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let e : V ≃L[ℝ] V :=
      (LinearEquiv.smulOfNeZero ℝ V ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
    let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (FourierTransform.fourier u)
    exact (SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.id ℂ (E →L[ℂ] F)).flip (hphase.smul hg) w).integrable
  -- Integral linearity and the finite seminorm bounds define the continuous operator.
  have hadd (u v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (x : EuclideanSpace ℝ (Fin n)) :
      quantize p (u + v) x = quantize p u x + quantize p v x := by
    simp only [quantize, fourierSG, FourierTransform.fourier_add,
      add_apply, map_add, smul_add]
    have hu := hInt p hp u x
    have hv := hInt p hp v x
    dsimp only [fourierSG] at hu hv
    rw [MeasureTheory.integral_add hu hv, smul_add]
  have hsmul (a : ℂ)
      (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (x : EuclideanSpace ℝ (Fin n)) :
      quantize p (a • u) x = a • quantize p u x := by
    simp only [quantize, fourierSG, FourierTransform.fourier_smul,
      smul_apply, map_smul, smul_comm (Complex.exp _),
      MeasureTheory.integral_smul]
    exact smul_comm _ _ _
  obtain ⟨hsmooth, hbound⟩ := quantize_schwartz_seminorm_bounds m p hp hc
  let T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) :=
    SchwartzMap.mkCLM (quantize p) hadd hsmul hsmooth (fun ki ↦ hbound ki.1 ki.2)
  refine ⟨T, fun _ _ ↦ rfl, ?_⟩
  -- The exact pointwise integral determines both the Schwartz output and the operator.
  intro S hS
  apply ContinuousLinearMap.ext
  intro u
  exact SchwartzMap.ext (hS u)

/-- The continuous Schwartz realization chosen by its unique exact integral specification. -/
def quantizeSchwartz (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hc : HasCompactSupport p) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) :=
  (existsUnique_quantizeSchwartz m p hp hc).exists.choose

/-- The selected Schwartz map retains the actual Fourier quantization formula. -/
theorem quantizeSchwartz_apply (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hc : HasCompactSupport p)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) : quantizeSchwartz m p hp hc u x = quantize p u x := by
  /- Apply the specification of the unique chosen continuous operator. This
  identifies its exact values, including all lower-order and smoothing terms. -/
  exact (existsUnique_quantizeSchwartz m p hp hc).exists.choose_spec u x

set_option maxSynthPendingDepth 20 in
/-- Quantization is additive in compact spatial symbols of a fixed order. -/
theorem quantizeSchwartz_add (m : ℝ) (p p' : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hp' : IsSymbol Set.univ m p')
    (hc : HasCompactSupport p) (hc' : HasCompactSupport p')
    (hadd : IsSymbol Set.univ m (p + p')) (hcadd : HasCompactSupport (p + p')) :
    quantizeSchwartz m (p + p') hadd hcadd =
      quantizeSchwartz m p hp hc + quantizeSchwartz m p' hp' hc' := by
  /- Both integrands are integrable on each Schwartz input. Integral additivity
  gives equality at every point; extensionality gives equality of the continuous
  maps. The explicit certificates may be any proofs of the stated properties. -/
  have hInt (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
      (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (x : EuclideanSpace ℝ (Fin n)) :
      MeasureTheory.Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        p x ξ (fourierSG u ξ)) := by
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let F := EuclideanSpace ℂ (Fin q)
    -- At each fixed spatial point, the symbol is a temperate frequency multiplier.
    have hg : (p x).HasTemperateGrowth := by
      refine ⟨?_, ?_⟩
      · have hs : ContDiff ℝ ∞ (Function.uncurry p) := by
          simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
        exact hs.comp (contDiff_const.prodMk contDiff_id)
      · intro j
        obtain ⟨C, hC, hbound⟩ := hp.2 {x} (Set.subset_univ _) isCompact_singleton 0 j
        refine ⟨⌈m - (j : ℝ)⌉₊, C, fun ξ ↦ ?_⟩
        have h := hbound x (Set.mem_singleton x) ξ
        simp only [symbolDerivative, norm_iteratedFDeriv_zero] at h
        apply h.trans
        apply mul_le_mul_of_nonneg_left _ hC
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil _)
    have hphase : (fun ξ : V ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))).HasTemperateGrowth := by
      simpa [Function.comp_def, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ x).hasTemperateGrowth
    -- The Fourier convention differs by an invertible real dilation, preserving Schwartz space.
    have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let e : V ≃L[ℝ] V :=
      (LinearEquiv.smulOfNeZero ℝ V ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
    let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (FourierTransform.fourier u)
    exact (SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.id ℂ (E →L[ℂ] F)).flip (hphase.smul hg) w).integrable
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  simp only [add_apply, quantizeSchwartz_apply]
  simp only [quantize, Pi.add_apply, _root_.add_apply, smul_add]
  rw [MeasureTheory.integral_add (hInt p hp u x) (hInt p' hp' u x), smul_add]

set_option maxSynthPendingDepth 20 in
/-- Quantization is complex-linear in the symbol, with no conjugation of the scalar. -/
theorem quantizeSchwartz_smul (m : ℝ) (a : ℂ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hc : HasCompactSupport p)
    (hsmul : IsSymbol Set.univ m (a • p)) (hcsmul : HasCompactSupport (a • p)) :
    quantizeSchwartz m (a • p) hsmul hcsmul = a • quantizeSchwartz m p hp hc := by
  /- Move the fixed complex scalar through the Fourier integral on each input.
  The exact action specification and extensionality identify the operators.
  There is no transpose or Hermitian pairing in this computation. -/
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  simp only [smul_apply, quantizeSchwartz_apply]
  simp only [quantize, Pi.smul_apply, _root_.smul_apply,
    smul_comm (Complex.exp _), MeasureTheory.integral_smul]
  exact smul_comm _ _ _

end AtiyahSinger
