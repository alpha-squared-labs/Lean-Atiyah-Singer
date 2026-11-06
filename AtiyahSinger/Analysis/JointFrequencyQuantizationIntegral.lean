/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.JointFrequencySymbolIntegral
public import AtiyahSinger.Analysis.Quantization

/-!
# Quantization of the actual fractional joint-symbol integral

Public module ID: M0770.

For 0 < p < 1, the parameter and Fourier integrals commute for the original joint symbol on
Schwartz inputs. Absolute product integrability follows from the actual joint
estimate and the scalar resolvent weight. No parameter measurability or operator
identity is taken as input.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set
open scoped ContDiff SchwartzMap Topology

set_option maxSynthPendingDepth 25

set_option maxHeartbeats 1000000 in

private theorem integrableOn_and_quantize_integral_jointFrequencySymbolSlice
    {n r q : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (a : SymbolFunction (n + 1) r q) (j : ℕ)
    (ha : IsSymbol ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd z).1) ⁻¹' U) (-2 - (j : ℝ)) a)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) :
    IntegrableOn (fun t : ℝ ↦ t ^ (-p) • quantize (jointFrequencySymbolSlice a t) u x)
        (Ioi 0) ∧
      quantize (fun y ξ ↦ ∫ t in Ioi (0 : ℝ),
      t ^ (-p) • jointFrequencySymbolSlice a t y ξ) u x =
        ∫ t in Ioi (0 : ℝ), t ^ (-p) • quantize (jointFrequencySymbolSlice a t) u x := by
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin (n + 1))
  let V := EuclideanSpace ℂ (Fin q)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] V
  let e : Y ≃L[ℝ] X × EuclideanSpace ℝ (Fin 1) := EuclideanSpace.finAddEquivProd
  let W : Set Y := (fun z ↦ (e z).1) ⁻¹' U
  have hW : IsOpen W := hU.preimage (continuous_fst.comp e.continuous)
  have hxW : e.symm (x, 0) ∈ W := by
    change (e (e.symm (x, 0))).1 ∈ U
    simpa only [e.apply_symm_apply] using hx
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let c : ℝ := ((2 * Real.pi) ^ n)⁻¹
  have hπ : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  let rescale : X ≃L[ℝ] X :=
    (LinearEquiv.smulOfNeZero ℝ X ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
  let v := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ rescale (FourierTransform.fourier u)
  let b (t : ℝ) : SymbolFunction n r q := t ^ (-p) • jointFrequencySymbolSlice a t
  -- The actual raw frequency restriction is continuous before multiplying the singular weight.
  have haf : Continuous (a (e.symm (x, 0))) := by
    have hs : ContDiffOn ℝ ∞ (a (e.symm (x, 0))) univ :=
      ha.1.comp (contDiffOn_const.prodMk contDiffOn_id)
        (fun _ _ ↦ ⟨hxW, mem_univ _⟩)
    exact (contDiffOn_univ.mp hs).continuous
  have hsqrt : Continuous (fun z : ℝ × X ↦
      WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt z.1)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℝ)).comp
      (continuous_pi (fun _ ↦ Real.continuous_sqrt.comp continuous_fst))
  have hraw : Continuous (fun z : ℝ × X ↦ jointFrequencySymbolSlice a z.1 x z.2) :=
    haf.comp (e.symm.continuous.comp (continuous_snd.prodMk hsqrt))
  have hw : AEStronglyMeasurable (fun t : ℝ ↦ t ^ (-p)) μ := by
    have hc : ContinuousOn (fun t : ℝ ↦ t ^ (-p)) (Ioi 0) :=
      continuousOn_id.rpow_const (fun t ht ↦ Or.inl (ne_of_gt ht))
    exact hc.aestronglyMeasurable measurableSet_Ioi
  -- The zeroth mixed estimate supplies a single integrable parameter profile, uniform in ξ.
  obtain ⟨C, hC, hbound⟩ := exists_bound_jointFrequencySymbolSlice W hW
    (-2 - (j : ℝ)) a ha {x} isCompact_singleton (by
      rintro _ ⟨y, hy, rfl⟩
      have hyx : y = x := mem_singleton_iff.mp hy
      simpa only [hyx] using hxW) 0 0
  let base (t : ℝ) : ℝ := t ^ (-p) * (1 + t) ^ (-1 : ℝ)
  have hbaseInt : Integrable base μ := by
    have h := ((resolvent_weight_integral p hp hp1 0).2 1 zero_lt_one).1
    change IntegrableOn base (Ioi 0)
    exact IntegrableOn.congr_fun h (fun t _ ↦ by
      dsimp only [base]
      norm_num) measurableSet_Ioi
  have hbnd (t : ℝ) (ht : 0 < t) (ξ : X) : ‖b t x ξ‖ ≤ C * base t := by
    have hb := hbound t ht x (mem_singleton x) ξ
    simp only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero] at hb
    have hexp : (-2 - (j : ℝ)) / 2 ≤ (-1 : ℝ) := by
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have hweight : (1 + ‖ξ‖ ^ 2 + t) ^ ((-2 - (j : ℝ)) / 2) ≤
        (1 + t) ^ (-1 : ℝ) := by
      calc
        _ ≤ (1 + t) ^ ((-2 - (j : ℝ)) / 2) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) (by nlinarith [sq_nonneg ‖ξ‖])
            (hexp.trans (by norm_num))
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    change ‖t ^ (-p) • jointFrequencySymbolSlice a t x ξ‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
    calc
      _ ≤ t ^ (-p) * (C * (1 + ‖ξ‖ ^ 2 + t) ^ ((-2 - (j : ℝ)) / 2)) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.le _)
      _ ≤ t ^ (-p) * (C * (1 + t) ^ (-1 : ℝ)) := by
        gcongr
      _ = C * base t := by dsimp only [base]; ring
  have hbInt (ξ : X) : Integrable (fun t ↦ b t x ξ) μ := by
    apply (hbaseInt.const_mul C).mono'
    · exact hw.smul ((hraw.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbnd t ht ξ
  let phase (η : X) : ℂ := Complex.exp (Complex.I * (inner ℝ x η : ℂ))
  have hphase (η : X) : ‖phase η‖ = 1 := by
    exact Complex.norm_exp_I_mul_ofReal _
  let F (t : ℝ) (η : X) : V := phase η • b t x η (v η)
  have hFmeas : AEStronglyMeasurable (Function.uncurry F) (μ.prod volume) := by
    -- Keep the original Fourier variable; the rescaling is already inside its Schwartz input.
    have hwprod : AEStronglyMeasurable (fun z : ℝ × X ↦ z.1 ^ (-p))
        (μ.prod (volume : Measure X)) :=
      hw.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have hbmeas : AEStronglyMeasurable (fun z : ℝ × X ↦ b z.1 x z.2)
        (μ.prod (volume : Measure X)) := hwprod.smul hraw.aestronglyMeasurable
    have hpmeas : AEStronglyMeasurable (fun z : ℝ × X ↦ phase z.2) (μ.prod volume) := by
      have hc : Continuous (fun z : ℝ × X ↦ phase z.2) := by dsimp only [phase]; fun_prop
      exact hc.aestronglyMeasurable
    have heval : Continuous (fun z : H × EuclideanSpace ℂ (Fin r) ↦ z.1 z.2) :=
      continuous_fst.clm_apply continuous_snd
    exact hpmeas.smul (heval.comp_aestronglyMeasurable
      (hbmeas.prodMk (v.continuous.comp continuous_snd).aestronglyMeasurable))
  have hFi : Integrable (Function.uncurry F) (μ.prod volume) := by
    apply ((hbaseInt.const_mul C).mul_prod v.integrable.norm).mono' hFmeas
    have hpos : ∀ᵐ z : ℝ × X ∂μ.prod volume, 0 < z.1 := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Filter.Eventually.of_forall (fun _ ↦ ht)
    filter_upwards [hpos] with z hz
    change ‖phase z.2 • b z.1 x z.2 (v z.2)‖ ≤ C * base z.1 * ‖v z.2‖
    rw [norm_smul, hphase, one_mul]
    exact ((b z.1 x z.2).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbnd z.1 hz z.2) (norm_nonneg _))
  have hq (a' : SymbolFunction n r q) : quantize a' u x =
      c • ∫ ξ : X, phase ξ • a' x ξ (v ξ) := rfl
  have hkernel (t : ℝ) (ξ : X) : F t ξ =
      t ^ (-p) • (phase ξ • jointFrequencySymbolSlice a t x ξ (v ξ)) := by
    change phase ξ • (t ^ (-p) • jointFrequencySymbolSlice a t x ξ (v ξ)) = _
    exact smul_comm _ _ _
  have houtput (t : ℝ) : c • (∫ η, F t η) =
      t ^ (-p) • quantize (jointFrequencySymbolSlice a t) u x := by
    simp only [hkernel, hq, integral_smul]
    exact smul_comm _ _ _
  refine ⟨?_, ?_⟩
  · -- Product integrability also certifies the actual parameter integral of the output.
    have hi := hFi.integral_prod_left.fun_smul c
    change Integrable (fun t : ℝ ↦
      t ^ (-p) • quantize (jointFrequencySymbolSlice a t) u x) μ
    exact hi.congr (Filter.Eventually.of_forall houtput)
  -- Fubini now exchanges the actual parameter and Fourier integrals of the same symbol.
  calc
    _ = c • ∫ η, ∫ t, F t η ∂μ := by
      rw [hq]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with η
      let T : H →L[ℂ] V := phase η • ContinuousLinearMap.apply ℂ V (v η)
      change T (∫ t, b t x η ∂μ) = ∫ t, T (b t x η) ∂μ
      exact (T.integral_comp_comm (hbInt η)).symm
    _ = c • ∫ t, (∫ η, F t η) ∂μ :=
      congrArg (fun z : V ↦ c • z) (integral_integral_swap hFi).symm
    _ = ∫ t, c • (∫ η, F t η) ∂μ := (integral_smul c _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact houtput t

/-- The fractional family of actual quantizer outputs is absolutely parameter integrable. -/
theorem integrableOn_smul_quantize_jointFrequencySymbolSlice
    {n r q : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (a : SymbolFunction (n + 1) r q) (j : ℕ)
    (ha : IsSymbol ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd z).1) ⁻¹' U) (-2 - (j : ℝ)) a)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) :
    IntegrableOn (fun t : ℝ ↦ t ^ (-p) • quantize (jointFrequencySymbolSlice a t) u x)
      (Ioi 0) :=
  (integrableOn_and_quantize_integral_jointFrequencySymbolSlice hU a j ha p hp hp1 u x hx).1

/-- Fractional integration of a specified joint symbol commutes with its actual quantizer. -/
theorem quantize_integral_jointFrequencySymbolSlice
    {n r q : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (a : SymbolFunction (n + 1) r q) (j : ℕ)
    (ha : IsSymbol ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd z).1) ⁻¹' U) (-2 - (j : ℝ)) a)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) :
    quantize (fun y ξ ↦ ∫ t in Ioi (0 : ℝ),
      t ^ (-p) • jointFrequencySymbolSlice a t y ξ) u x =
        ∫ t in Ioi (0 : ℝ), t ^ (-p) • quantize (jointFrequencySymbolSlice a t) u x :=
  (integrableOn_and_quantize_integral_jointFrequencySymbolSlice hU a j ha p hp hp1 u x hx).2

end AtiyahSinger
