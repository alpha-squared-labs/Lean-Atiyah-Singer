/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactQuantization
public import AtiyahSinger.Analysis.LocalComposition

import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact raw quantization with a fixed input cutoff

Public module ID: M2304.

Sources: SG III.3.10–3.11 and the original Fourier convention of LocalAdjoint.
SG means H. Blaine Lawson, Jr. and Marie-Louise Michelsohn, *Spin Geometry*
(Princeton University Press, 1989). These are supplementary exact interfaces for
that calculus, using the original quantize, adjointAmplitude and compositionSymbol.

A raw symbol with compact spatial support has compact output support. The
adjoint amplitude with the specified χ corresponds to that same raw operator
with multiplication by χ on its input. Its full pairing and exact composition
are retained below. An internally chosen scalar plateau proves an auxiliary
integrability fact; the supplied χ has no normalization at the coordinate origin.

The statements cover arbitrary real orders, independent rectangular fiber ranks,
zero dimension and empty supports. Their exact input cutoff must be accounted
for before applying an operator estimate to a raw composition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

variable {n r q s t : ℕ}

set_option maxSynthPendingDepth 20 in
set_option maxHeartbeats 1000000 in
-- Use the original two integrable Fourier pairings at the same real-order symbol.
/-- The actual adjoint amplitude is the formal adjoint of the raw operator with input χ. -/
theorem isSchwartzFormalAdjoint_quantize_mulCutoff (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hpSupp : HasCompactSupport p)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) :
    IsSchwartzFormalAdjoint
      ((quantizeSchwartz m p hp hpSupp).comp
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (χ x : ℂ))))
      (amplitudeOperator m (adjointAmplitude χ p)
        (isAmplitude_adjointAmplitude m p hp χ hχ)
        (hasCompactSupport_adjointAmplitude p hpSupp χ hcχ)) := by
  /- First derive the original raw quantization pairing by its two genuine L¹ bounds.
  Then insert the supplied χ into the input and match the original adjoint amplitude.
  The second pairing uses a separate auxiliary plateau only to establish integrability
  of its cutoff-independent Fourier expression, and imposes no extra condition on χ. -/
  let V := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  have pairing (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))) :
      (∫ y, inner ℂ (quantize p u y) (v y)) = ((2 * Real.pi) ^ n)⁻¹ •
        ∫ ξ, inner ℂ (fourierSG u ξ)
          (∫ y, Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • (p y ξ).adjoint (v y)) := by
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let phase (y ξ : V) := Complex.exp (Complex.I * (inner ℝ y ξ : ℂ))
    have hphase (y ξ : V) : ‖phase y ξ‖ = 1 := by
      simp [phase, Complex.norm_exp, Complex.mul_re]
    have hpCont : Continuous (Function.uncurry p) := by
      simpa only [Set.univ_prod_univ, continuousOn_univ] using hp.1.continuousOn
    obtain ⟨C, hC, hbound⟩ := hp.2 (tsupport p) (Set.subset_univ _) hpSupp 0 0
    have hpnorm (y ξ : V) : ‖p y ξ‖ ≤ C * (1 + ‖ξ‖) ^ m := by
      by_cases hy : y ∈ tsupport p
      · simpa only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero]
          using hbound y hy ξ
      · have hz : p y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp only [hz, Pi.zero_apply, norm_zero]
        positivity
    -- A smooth polynomial weight bounds the order-m growth against this same Fourier input.
    obtain ⟨d, hd⟩ := exists_nat_ge m
    have hpi : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let e : V ≃L[ℝ] V :=
      (LinearEquiv.smulOfNeZero ℝ V ((2 * Real.pi)⁻¹) hpi).toContinuousLinearEquiv
    let fu : 𝓢(V, E) :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (FourierTransform.fourier u)
    have hfu (ξ : V) : fu ξ = fourierSG u ξ := rfl
    let weight (ξ : V) : ℂ := ((1 + ‖ξ‖ ^ 2) ^ d : ℝ)
    have hw : weight.HasTemperateGrowth := by dsimp [weight]; fun_prop
    let wu : 𝓢(V, E) := SchwartzMap.smulLeftCLM E weight fu
    have hwu (ξ : V) : ‖wu ξ‖ = (1 + ‖ξ‖ ^ 2) ^ d * ‖fourierSG u ξ‖ := by
      rw [show wu ξ = weight ξ • fu ξ from SchwartzMap.smulLeftCLM_apply_apply hw _ _,
        norm_smul, hfu]
      dsimp [weight]
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hweight (ξ : V) : (1 + ‖ξ‖) ^ m ≤ (2 : ℝ) ^ d * (1 + ‖ξ‖ ^ 2) ^ d := by
      have hbase : 1 + ‖ξ‖ ≤ 2 * (1 + ‖ξ‖ ^ 2) := by
        nlinarith [sq_nonneg (‖ξ‖ - 1)]
      calc
        _ ≤ (1 + ‖ξ‖) ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) hd
        _ = (1 + ‖ξ‖) ^ d := Real.rpow_natCast _ _
        _ ≤ (2 * (1 + ‖ξ‖ ^ 2)) ^ d := pow_le_pow_left₀ (by positivity) hbase d
        _ = _ := mul_pow _ _ _
    let D : ℝ := C * (2 : ℝ) ^ d
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hprod (y ξ : V) : ‖p y ξ‖ * ‖fourierSG u ξ‖ ≤ D * ‖wu ξ‖ := by
      calc
        _ ≤ (C * (1 + ‖ξ‖) ^ m) * ‖fourierSG u ξ‖ :=
          mul_le_mul_of_nonneg_right (hpnorm y ξ) (norm_nonneg _)
        _ ≤ (C * ((2 : ℝ) ^ d * (1 + ‖ξ‖ ^ 2) ^ d)) * ‖fourierSG u ξ‖ := by
          gcongr
          exact hweight ξ
        _ = _ := by rw [hwu]; dsimp [D]; ring
    let g (y ξ : V) := phase y ξ • p y ξ (fourierSG u ξ)
    have hg (y ξ : V) : ‖g y ξ‖ ≤ D * ‖wu ξ‖ := by
      dsimp only [g]
      rw [norm_smul, hphase, one_mul]
      exact ((p y ξ).le_opNorm _).trans (hprod y ξ)
    have hgcont : Continuous (Function.uncurry g) := by
      have hph : Continuous (Function.uncurry phase) := by dsimp [phase]; fun_prop
      exact hph.smul (hpCont.clm_apply (fu.continuous.comp continuous_snd))
    have hgint (y : V) : Integrable (g y) :=
      (wu.integrable.norm.const_mul D).mono'
        ((hgcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
        (Filter.Eventually.of_forall (hg y))
    -- The double pairing is bounded by the product of two genuine L1 functions.
    let H (y ξ : V) := inner ℂ (g y ξ) (v y)
    have hHcont : Continuous (Function.uncurry H) :=
      hgcont.inner (v.continuous.comp continuous_fst)
    have hHint : Integrable (Function.uncurry H) := by
      apply ((v.integrable.norm.mul_prod wu.integrable.norm).const_mul D).mono'
        hHcont.aestronglyMeasurable
      filter_upwards with z
      calc
        ‖H z.1 z.2‖ ≤ ‖g z.1 z.2‖ * ‖v z.1‖ := norm_inner_le_norm _ _
        _ ≤ (D * ‖wu z.2‖) * ‖v z.1‖ :=
          mul_le_mul_of_nonneg_right (hg z.1 z.2) (norm_nonneg _)
        _ = D * (‖v z.1‖ * ‖wu z.2‖) := by ring
    have hIntegral {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
        [CompleteSpace F] (f : V → F) (hf : Integrable f) (z : F) :
        inner ℂ (∫ x, f x) z = ∫ x, inner ℂ (f x) z := by
      simpa only [← integral_conj, inner_conj_symm] using
        (congrArg (starRingEnd ℂ) (integral_inner (𝕜 := ℂ) hf z)).symm
    have hpoint (ξ : V) : (∫ y, H y ξ) = inner ℂ (fourierSG u ξ)
        (∫ y, Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • (p y ξ).adjoint (v y)) := by
      let f (y : V) := Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) •
        (p y ξ).adjoint (v y)
      have hfcont : Continuous f := by
        have hpc : Continuous (fun y ↦ p y ξ) :=
          hpCont.comp (continuous_id.prodMk continuous_const)
        have hph : Continuous (fun y ↦ Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ))) := by
          fun_prop
        exact hph.smul ((ContinuousLinearMap.adjoint.continuous.comp hpc).clm_apply v.continuous)
      have hfint : Integrable f := by
        apply hfcont.integrable_of_hasCompactSupport
        apply hpSupp.of_isClosed_subset (isClosed_tsupport _)
        apply closure_minimal ?_ (isClosed_tsupport p)
        intro y hy
        by_contra h
        have hz : p y = 0 := image_eq_zero_of_notMem_tsupport h
        exact hy (by simp [f, hz])
      rw [← integral_inner hfint]
      apply integral_congr_ae
      filter_upwards with y
      change inner ℂ (phase y ξ • p y ξ (fourierSG u ξ)) (v y) =
        inner ℂ (fourierSG u ξ) (Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) •
          (p y ξ).adjoint (v y))
      rw [inner_smul_left, inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
      congr 1
      dsimp [phase]
      rw [← Complex.exp_conj]
      congr 1
      simp
    calc
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ y, ∫ ξ, H y ξ := by
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards with y
        change inner ℂ (((2 * Real.pi) ^ n)⁻¹ • ∫ ξ, g y ξ) (v y) = _
        rw [inner_smul_left_eq_smul, hIntegral (g y) (hgint y)]
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ ξ, ∫ y, H y ξ := by
        rw [integral_integral_swap hHint]
      _ = _ := by
        simp_rw [hpoint]
        rfl
  have ampPairing (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
      (hcχ : HasCompactSupport χ)
      (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))) :
      (∫ y, inner ℂ (quantize p
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (χ x : ℂ)) u) y) (v y)) =
        ∫ x, inner ℂ (u x) (amplitudeApply (adjointAmplitude χ p) v x) := by
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let phase (x ξ : V) := Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))
    let R (ξ : V) := ∫ y,
      Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • (p y ξ).adjoint (v y)
    let w := SchwartzMap.smulLeftCLM E (fun x ↦ (χ x : ℂ)) u
    have hχgrowth : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
      (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hχ)
    have hw (x : V) : w x = χ x • u x := by
      simpa only [Complex.coe_smul] using
        SchwartzMap.smulLeftCLM_apply_apply hχgrowth u x
    -- The dependence on x is exactly a fixed scalar phase and the selected real cutoff.
    have hfactor (φ : V → ℝ) (x ξ : V) :
        (∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
          adjointAmplitude φ p x y ξ (v y)) = φ x • (phase x ξ • R ξ) := by
      dsimp only [R]
      rw [← integral_smul, ← integral_smul]
      apply integral_congr_ae
      filter_upwards with y
      have hphase : Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) =
          phase x ξ * Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) := by
        dsimp [phase]
        rw [← Complex.exp_add, inner_sub_left]
        congr 1
        push_cast
        ring
      simp only [adjointAmplitude, smul_apply, hphase, ← Complex.coe_smul, smul_smul]
      congr 1
      ring
    have hRint : Integrable R := by
      -- A separate plateau at zero proves integrability without restricting the supplied χ.
      let ψ : ContDiffBump (0 : V) :=
        { rIn := 1
          rOut := 2
          rIn_pos := zero_lt_one
          rIn_lt_rOut := by norm_num }
      have hψ0 : ψ 0 = 1 := by
        apply ψ.one_of_mem_closedBall
        simp only [Metric.mem_closedBall, dist_self]
        exact ψ.rIn_pos.le
      have h := integrable_amplitudeApply_outer m (adjointAmplitude ψ p)
        (isAmplitude_adjointAmplitude m p hp ψ ψ.contDiff)
        (hasCompactSupport_adjointAmplitude p hpSupp ψ ψ.hasCompactSupport) v 0
      change Integrable (fun ξ : V ↦ ∫ y : V,
        Complex.exp (Complex.I * (inner ℝ (0 - y) ξ : ℂ)) •
          adjointAmplitude ψ p 0 y ξ (v y)) at h
      simpa only [hfactor ψ, hψ0, phase, inner_zero_left, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, one_smul] using h
    have hamp (x : V) : amplitudeApply (adjointAmplitude χ p) v x =
        ((2 * Real.pi) ^ n)⁻¹ • (χ x • ∫ ξ, phase x ξ • R ξ) := by
      change ((2 * Real.pi) ^ n)⁻¹ • (∫ ξ : V, ∫ y : V,
        Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
          adjointAmplitude χ p x y ξ (v y)) = _
      simp_rw [hfactor χ]
      rw [integral_smul]
    -- Products of the two L1 norms justify the actual spatial-frequency swap.
    let G (x ξ : V) := inner ℂ (w x) (phase x ξ • R ξ)
    have hphaseCont : Continuous (Function.uncurry phase) := by dsimp [phase]; fun_prop
    have hphaseNorm (x ξ : V) : ‖phase x ξ‖ = 1 := by
      simp [phase, Complex.norm_exp, Complex.mul_re]
    have hGmeas : AEStronglyMeasurable (Function.uncurry G) :=
      w.continuous.aestronglyMeasurable.comp_fst.inner
        (hphaseCont.aestronglyMeasurable.smul hRint.aestronglyMeasurable.comp_snd)
    have hGint : Integrable (Function.uncurry G) := by
      apply (w.integrable.norm.mul_prod hRint.norm).mono' hGmeas
      filter_upwards with z
      exact (norm_inner_le_norm _ _).trans_eq
        (by rw [norm_smul, hphaseNorm, one_mul])
    have hphaseInt (x : V) : Integrable (fun ξ ↦ phase x ξ • R ξ) := by
      apply hRint.norm.mono'
        ((hphaseCont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.smul
          hRint.aestronglyMeasurable)
      filter_upwards with ξ
      change ‖phase x ξ • R ξ‖ ≤ ‖R ξ‖
      rw [norm_smul, hphaseNorm, one_mul]
    have hfourier (ξ : V) : fourierSG w ξ =
        ∫ x, Complex.exp (-Complex.I * (inner ℝ x ξ : ℂ)) • w x := by
      unfold fourierSG
      rw [SchwartzMap.fourier_coe, Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with x
      congr 2
      rw [inner_smul_right]
      push_cast
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
    have hpoint (ξ : V) : (∫ x, G x ξ) = inner ℂ (fourierSG w ξ) (R ξ) := by
      have hfint : Integrable (fun x ↦
          Complex.exp (-Complex.I * (inner ℝ x ξ : ℂ)) • w x) := by
        have hcont : Continuous (fun x : V ↦
            Complex.exp (-Complex.I * (inner ℝ x ξ : ℂ)) • w x) := by fun_prop
        apply w.integrable.norm.mono' hcont.aestronglyMeasurable
        filter_upwards with x
        simp [norm_smul, Complex.norm_exp, Complex.mul_re]
      have hi := congrArg (starRingEnd ℂ) (integral_inner (𝕜 := ℂ) hfint (R ξ))
      simp only [← integral_conj, inner_conj_symm] at hi
      rw [hfourier, ← hi]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [G]
      rw [inner_smul_left, inner_smul_right]
      congr 1
      dsimp [phase]
      rw [← Complex.exp_conj]
      congr 1
      simp
    calc
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ ξ, inner ℂ (fourierSG w ξ) (R ξ) :=
        pairing w v
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ ξ, ∫ x, G x ξ := by
        simp_rw [hpoint]
        rfl
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ x, ∫ ξ, G x ξ := by
        rw [integral_integral_swap hGint]
      _ = _ := by
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards with x
        rw [hamp, inner_smul_right_eq_smul]
        congr 1
        rw [inner_smul_right_eq_smul, ← integral_inner (hphaseInt x), ← integral_smul]
        apply integral_congr_ae
        filter_upwards with ξ
        dsimp only [G]
        rw [hw, inner_smul_left_eq_smul]
  -- Apply the exact integrated pairing to the same actual two Schwartz operators.
  intro u v
  simp only [ContinuousLinearMap.comp_apply, quantizeSchwartz_apply, amplitudeOperator_apply]
  exact ampPairing χ hχ hcχ u v

/-- The original reduced composition is the raw composition with its specified input cutoff. -/
theorem quantize_compositionSymbol_mulCutoff (l m : ℝ)
    (p : SymbolFunction n s t) (q : SymbolFunction n r s)
    (hp : IsSymbol Set.univ l p) (hq : IsSymbol Set.univ m q)
    (hpSupp : HasCompactSupport p) (hqSupp : HasCompactSupport q)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize (compositionSymbol χ p q) u x =
      quantize p ((quantizeSchwartz m q hq hqSupp)
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun y ↦ (χ y : ℂ)) u)) x := by
  /- The actual cutoff right operator Q has the actual adjoint amplitude A. Its full
  pairing identifies FourierSG(Q u) with the original right-symbol Fourier expression.
  The same two ordered integrals then give the exact left-right amplitude reduction.
  No compact input support is inferred for either raw symbol operator. -/
  let Q := (quantizeSchwartz m q hq hqSupp).comp
    (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun y ↦ (χ y : ℂ)))
  let a := adjointSymbol χ q
  let A := amplitudeOperator m (adjointAmplitude χ q)
    (isAmplitude_adjointAmplitude m q hq χ hχ)
    (hasCompactSupport_adjointAmplitude q hqSupp χ hcχ)
  have ha : IsSymbol Set.univ m a := isSymbol_adjointSymbol m q hq hqSupp χ hχ hcχ
  have haSupp : HasCompactSupport a :=
    hcχ.of_isClosed_subset (isClosed_tsupport _) (tsupport_adjointSymbol_subset χ q)
  have hb : IsSymbol Set.univ m (symbolAdjoint a) := ha.symbolAdjoint isOpen_univ
  have hbSupp : HasCompactSupport (symbolAdjoint a) := by
    simpa only [HasCompactSupport, tsupport_symbolAdjoint] using haSupp
  have hA (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
      (z : EuclideanSpace ℝ (Fin n)) : A v z = quantize a v z := by
    rw [amplitudeOperator_apply]
    exact (congrFun (quantize_amplitudeSymbol m (adjointAmplitude χ q)
      (isAmplitude_adjointAmplitude m q hq χ hχ)
      (hasCompactSupport_adjointAmplitude q hqSupp χ hcχ) v) z).symm
  have hQA : IsSchwartzFormalAdjoint Q A :=
    isSchwartzFormalAdjoint_quantize_mulCutoff m q hq hqSupp χ hχ hcχ
  -- Identify the Fourier transform of this same Q u through the full actual adjoint pairing.
  have hfourier (ξ : EuclideanSpace ℝ (Fin n)) :
      fourierSG (Q u) ξ = rightSymbolFourierApply (symbolAdjoint a) u ξ :=
    fourierSG_eq_rightSymbolFourierApply m a ha haSupp Q A hA hQA u ξ
  have hreduce := quantize_amplitudeSymbol (l + m) (leftRightAmplitude p (symbolAdjoint a))
    (isAmplitude_leftRightAmplitude l m p _ hp hb)
    (hasCompactSupport_leftRightAmplitude p _ hpSupp hbSupp) u
  calc
    _ = amplitudeApply (leftRightAmplitude p (symbolAdjoint a)) u x := congrFun hreduce x
    _ = quantize p (Q u) x := by
      unfold amplitudeApply quantize
      congr 1
      apply integral_congr_ae
      filter_upwards with ξ
      rw [hfourier]
      unfold rightSymbolFourierApply
      -- The actual right-symbol integrand is integrable at every fixed frequency.
      rw [← (p x ξ).integral_comp_comm
        (integrable_rightSymbolFourierApply m _ hb hbSupp u ξ), ← integral_smul]
      apply integral_congr_ae
      filter_upwards with y
      have hphase : Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) =
          Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
            Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) := by
        rw [← Complex.exp_add, inner_sub_left]
        congr 1
        push_cast
        ring
      simp only [leftRightAmplitude, ContinuousLinearMap.comp_apply, hphase, mul_smul, map_smul]

end AtiyahSinger
