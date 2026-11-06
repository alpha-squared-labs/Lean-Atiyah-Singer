/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# L² operators with a translation invariant Schur majorant

Public module ID: M0938.

A strongly measurable matrix kernel dominated by an even integrable function of the
frequency difference defines a bounded operator on the original L² spaces.
The proof applies weighted Cauchy–Schwarz on the product measure, then uses
Schwartz density and Riesz representation. This standard Schur test supplies
the analytic estimate needed for spatially compact pseudodifferential symbols.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped SchwartzMap

set_option maxSynthPendingDepth 20

private theorem norm_toLp_sq_eq_integral_norm_sq {X V : Type*}
    [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (f : X → V) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

private theorem real_norm_toLp_sq_eq_integral_sq {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (f : X → ℝ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx, pow_two]

/-- The Schur bound for a measurable kernel dominated by one integrable even majorant.
This is used for weighted spatial Fourier kernels of compactly supported symbols. -/
private theorem schur_pairing_estimate {n r q : ℕ}
    (K : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (hK : StronglyMeasurable (Function.uncurry K))
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hwi : Integrable w)
    (hwe : ∀ x, w (-x) = w x) (hbound : ∀ x y, ‖K x y‖ ≤ w (x - y))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
      inner ℂ (K z.1 z.2 (u z.2)) (v z.1)) ∧
    ‖∫ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      inner ℂ (K z.1 z.2 (u z.2)) (v z.1)‖ ≤
        (∫ x, w x) * ‖u.toLp 2 volume‖ * ‖v.toLp 2 volume‖ := by
  let X := EuclideanSpace ℝ (Fin n)
  let A : X × X → ℝ := fun z ↦ Real.sqrt (w (z.1 - z.2)) * ‖u z.2‖
  let B : X × X → ℝ := fun z ↦ Real.sqrt (w (z.1 - z.2)) * ‖v z.1‖
  have hAcont : Continuous A := (hw.comp (continuous_fst.sub continuous_snd)).sqrt.mul
    (u.continuous.comp continuous_snd).norm
  have hBcont : Continuous B := (hw.comp (continuous_fst.sub continuous_snd)).sqrt.mul
    (v.continuous.comp continuous_fst).norm
  have hAsq (z : X × X) : A z ^ 2 = ‖u z.2‖ ^ 2 * w (z.1 - z.2) := by
    dsimp [A]
    rw [mul_pow, Real.sq_sqrt (hw0 _)]
    ring
  have hBsq (z : X × X) : B z ^ 2 = ‖v z.1‖ ^ 2 * w (z.2 - z.1) := by
    dsimp [B]
    rw [mul_pow, Real.sq_sqrt (hw0 _)]
    rw [show z.2 - z.1 = -(z.1 - z.2) by abel, hwe]
    ring
  -- Weighted squares are integrable by translation invariance and Fubini.
  have hu2 := (u.memLp (p := 2) (μ := volume)).norm.integrable_sq
  have hv2 := (v.memLp (p := 2) (μ := volume)).norm.integrable_sq
  have hAint : Integrable (fun z : X × X ↦ A z ^ 2) := by
    simp_rw [hAsq]
    exact hu2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hwi
  have hBint : Integrable (fun z : X × X ↦ B z ^ 2) := by
    simp_rw [hBsq]
    exact (hv2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hwi).swap
  have hA : MemLp A 2 :=
    (memLp_two_iff_integrable_sq hAcont.aestronglyMeasurable).mpr hAint
  have hB : MemLp B 2 :=
    (memLp_two_iff_integrable_sq hBcont.aestronglyMeasurable).mpr hBint
  have huNorm : ‖u.toLp 2 volume‖ ^ 2 = ∫ x : X, ‖u x‖ ^ 2 := by
    exact norm_toLp_sq_eq_integral_norm_sq (μ := (volume : Measure X))
      (u : X → EuclideanSpace ℂ (Fin r)) (u.memLp 2 volume)
  have hvNorm : ‖v.toLp 2 volume‖ ^ 2 = ∫ x : X, ‖v x‖ ^ 2 := by
    exact norm_toLp_sq_eq_integral_norm_sq (μ := (volume : Measure X))
      (v : X → EuclideanSpace ℂ (Fin q)) (v.memLp 2 volume)
  have hnormA : ‖hA.toLp A‖ ^ 2 = (∫ x, w x) * ‖u.toLp 2 volume‖ ^ 2 := by
    rw [real_norm_toLp_sq_eq_integral_sq A hA]
    change (∫ z : X × X, A z ^ 2 ∂volume.prod volume) = _
    rw [integral_prod_symm _ hAint]
    simp_rw [hAsq, integral_const_mul, integral_sub_right_eq_self]
    rw [integral_mul_const]
    rw [← huNorm, mul_comm]
  have hnormB : ‖hB.toLp B‖ ^ 2 = (∫ x, w x) * ‖v.toLp 2 volume‖ ^ 2 := by
    rw [real_norm_toLp_sq_eq_integral_sq B hB]
    change (∫ z : X × X, B z ^ 2 ∂volume.prod volume) = _
    rw [integral_prod _ hBint]
    simp_rw [hBsq, integral_const_mul, integral_sub_right_eq_self]
    rw [integral_mul_const]
    rw [← hvNorm, mul_comm]
  -- The kernel pairing is bounded by the product of these two L² functions.
  have hAB (z : X × X) : A z * B z =
      w (z.1 - z.2) * ‖u z.2‖ * ‖v z.1‖ := by
    dsimp [A, B]
    calc
      _ = Real.sqrt (w (z.1 - z.2)) ^ 2 * ‖u z.2‖ * ‖v z.1‖ := by ring
      _ = _ := by rw [Real.sq_sqrt (hw0 _)]
  have hnorm : ∀ z : X × X,
      ‖inner ℂ (K z.1 z.2 (u z.2)) (v z.1)‖ ≤ A z * B z := by
    intro z
    rw [hAB, norm_inner_symm]
    calc
      _ ≤ ‖v z.1‖ * ‖K z.1 z.2 (u z.2)‖ := norm_inner_le_norm _ _
      _ ≤ ‖v z.1‖ * (‖K z.1 z.2‖ * ‖u z.2‖) := by
        gcongr
        exact (K z.1 z.2).le_opNorm _
      _ ≤ ‖v z.1‖ * (w (z.1 - z.2) * ‖u z.2‖) := by gcongr; exact hbound _ _
      _ = _ := by ring
  have habint : Integrable (fun z ↦ A z * B z) := hA.integrable_mul hB
  have hpair : (∫ z, A z * B z) = inner ℝ (hA.toLp A) (hB.toLp B) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hA.coeFn_toLp, hB.coeFn_toLp] with z hAz hBz
    simp [hAz, hBz, mul_comm]
  have hmass : 0 ≤ ∫ x, w x := integral_nonneg hw0
  have hkm : StronglyMeasurable (fun z : X × X ↦ K z.1 z.2 (u z.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (hK.prodMk (u.continuous.comp continuous_snd).stronglyMeasurable)
  have hpairm : StronglyMeasurable (fun z : X × X ↦
      inner ℂ (K z.1 z.2 (u z.2)) (v z.1)) :=
    hkm.inner (v.continuous.comp continuous_fst).stronglyMeasurable
  refine ⟨habint.mono' hpairm.aestronglyMeasurable (Filter.Eventually.of_forall hnorm), ?_⟩
  calc
    _ ≤ ∫ z, A z * B z := norm_integral_le_of_norm_le habint (Filter.Eventually.of_forall hnorm)
    _ = inner ℝ (hA.toLp A) (hB.toLp B) := hpair
    _ ≤ ‖hA.toLp A‖ * ‖hB.toLp B‖ := real_inner_le_norm _ _
    _ ≤ (∫ x, w x) * ‖u.toLp 2 volume‖ * ‖v.toLp 2 volume‖ := by
      have hsq : (‖hA.toLp A‖ * ‖hB.toLp B‖) ^ 2 =
          ((∫ x, w x) * ‖u.toLp 2 volume‖ * ‖v.toLp 2 volume‖) ^ 2 := by
        rw [mul_pow, hnormA, hnormB]
        ring
      exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq.le

/-- A measurable kernel with an even integrable Schur majorant defines a bounded L² operator.
Its weak action uses the original kernel and the ordinary Lebesgue measure. -/
theorem exists_schur_kernel_operator {n r q : ℕ}
    (K : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (hK : StronglyMeasurable (Function.uncurry K))
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hwi : Integrable w)
    (hwe : ∀ x, w (-x) = w x) (hbound : ∀ x y, ‖K x y‖ ≤ w (x - y)) :
    ∃ T : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ‖T‖ ≤ ∫ x, w x ∧ ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
        (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))),
        inner ℂ (T (u.toLp 2 volume)) (v.toLp 2 volume) =
          ∫ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
            inner ℂ (K z.1 z.2 (u z.2)) (v z.1) := by
  let X := EuclideanSpace ℝ (Fin n)
  let U := EuclideanSpace ℂ (Fin r)
  let V := EuclideanSpace ℂ (Fin q)
  let HU := Lp U 2 (volume : Measure X)
  let HV := Lp V 2 (volume : Measure X)
  let eU : 𝓢(X, U) →ₗ[ℂ] HU := (SchwartzMap.toLpCLM ℂ U 2 volume).toLinearMap
  let eV : 𝓢(X, V) →ₗ[ℂ] HV := (SchwartzMap.toLpCLM ℂ V 2 volume).toLinearMap
  have hdU : DenseRange eU := SchwartzMap.denseRange_toLpCLM (by simp)
  have hdV : DenseRange eV := SchwartzMap.denseRange_toLpCLM (by simp)
  let c : ℝ := ∫ x, w x
  have hc : 0 ≤ c := integral_nonneg hw0
  have hest := schur_pairing_estimate K hK w hw hw0 hwi hwe hbound
  let Q (u : 𝓢(X, U)) : 𝓢(X, V) →ₗ[ℂ] ℂ :=
    { toFun := fun v ↦ ∫ z : X × X, inner ℂ (K z.1 z.2 (u z.2)) (v z.1)
      map_add' := by
        intro v₁ v₂
        simp only [add_apply, inner_add_right]
        exact integral_add (hest u v₁).1 (hest u v₂).1
      map_smul' := by
        intro a v
        simp only [smul_apply, inner_smul_right, integral_const_mul,
          RingHom.id_apply, smul_eq_mul] }
  have hQ (u : 𝓢(X, U)) (v : 𝓢(X, V)) :
      ‖Q u v‖ ≤ (c * ‖eU u‖) * ‖eV v‖ := (hest u v).2
  let B : 𝓢(X, U) →ₗ⋆[ℂ] StrongDual ℂ HV :=
    { toFun := fun u ↦ (Q u).extendOfNorm eV
      map_add' := by
        intro u₁ u₂
        apply DFunLike.coe_injective
        apply hdV.equalizer ((Q (u₁ + u₂)).extendOfNorm eV).continuous
          (((Q u₁).extendOfNorm eV) + ((Q u₂).extendOfNorm eV)).continuous
        funext v
        change (Q (u₁ + u₂)).extendOfNorm eV (eV v) =
          (Q u₁).extendOfNorm eV (eV v) + (Q u₂).extendOfNorm eV (eV v)
        rw [LinearMap.extendOfNorm_eq hdV ⟨_, hQ (u₁ + u₂)⟩,
          LinearMap.extendOfNorm_eq hdV ⟨_, hQ u₁⟩,
          LinearMap.extendOfNorm_eq hdV ⟨_, hQ u₂⟩]
        change (∫ z : X × X, inner ℂ (K z.1 z.2 ((u₁ + u₂) z.2)) (v z.1)) = _
        simp only [add_apply, map_add, inner_add_left]
        exact integral_add (hest u₁ v).1 (hest u₂ v).1
      map_smul' := by
        intro a u
        apply DFunLike.coe_injective
        apply hdV.equalizer ((Q (a • u)).extendOfNorm eV).continuous
          ((starRingEnd ℂ a) • (Q u).extendOfNorm eV).continuous
        funext v
        change (Q (a • u)).extendOfNorm eV (eV v) =
          starRingEnd ℂ a • (Q u).extendOfNorm eV (eV v)
        rw [LinearMap.extendOfNorm_eq hdV ⟨_, hQ (a • u)⟩,
          LinearMap.extendOfNorm_eq hdV ⟨_, hQ u⟩]
        change (∫ z : X × X, inner ℂ (K z.1 z.2 ((a • u) z.2)) (v z.1)) = _
        simp only [smul_apply, map_smul, inner_smul_left, integral_const_mul,
          starRingEnd_apply, smul_eq_mul]
        rfl }
  -- Riesz represents the extended test functional by its unique vector in the target L² space.
  let R : 𝓢(X, U) →ₗ[ℂ] HV :=
    (InnerProductSpace.toDual ℂ HV).symm.toLinearEquiv.toLinearMap.comp B
  have hR (u : 𝓢(X, U)) : ‖R u‖ ≤ c * ‖eU u‖ := by
    change ‖(InnerProductSpace.toDual ℂ HV).symm ((Q u).extendOfNorm eV)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.opNorm_extendOfNorm_le hdV (mul_nonneg hc (norm_nonneg _)) (hQ u)
  let T : HU →L[ℂ] HV := R.extendOfNorm eU
  refine ⟨T, LinearMap.opNorm_extendOfNorm_le hdU hc hR, ?_⟩
  intro u v
  change inner ℂ (R.extendOfNorm eU (eU u)) (eV v) = _
  rw [LinearMap.extendOfNorm_eq hdU ⟨c, hR⟩]
  change inner ℂ ((InnerProductSpace.toDual ℂ HV).symm ((Q u).extendOfNorm eV)) (eV v) = _
  rw [InnerProductSpace.toDual_symm_apply, LinearMap.extendOfNorm_eq hdV ⟨_, hQ u⟩]
  rfl

end AtiyahSinger
