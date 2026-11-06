/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DistributionSupport
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Real-order Sobolev spaces in Bessel coordinates

Public module ID: M0604.

An element of H^s is represented uniquely as J^(-s) f with f in L², and its
norm is ‖f‖₂. `besselRealization` is this actual map into tempered distributions;
no arbitrary family of Hilbert spaces is postulated. The inclusion between
different orders must intertwine these maps, so it cannot be silently
interpreted as the identity on the L² coordinate spaces.

mathlib uses exp(-2πi x·ξ), so J^s = (1-(2π)^(-2)Δ)^(s/2). This changes equivalent
Sobolev norms, not the space. Global bundle localization is a separate construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory TemperedDistribution
open scoped SchwartzMap Topology FourierTransform

variable {n r : ℕ}

/-- The Bessel realization of H^s, with the norm transported from L². -/
def besselRealization (n r : ℕ) (s : ℝ) :
    Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
  (besselPotential _ _ (-s)).comp (Lp.toTemperedDistributionCLM _ volume 2)

open Filter in
open scoped ContDiff in
/-- Compactly supported scalar tests are dense for the full Schwartz topology.
This permits compact-test support identities to extend to tempered distributions. -/
theorem dense_hasCompactSupport_schwartz (n : ℕ) :
    Dense {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) | HasCompactSupport φ} := by
  -- Expanding a fixed bump bounds every cutoff derivative uniformly for radii at least one.
  have uniform_cutoff_derivative {n : ℕ} (b : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) (R : ℝ) (hR : 1 ≤ R)
      (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      ‖iteratedFDeriv ℝ j (fun y ↦ (1 : ℝ) - b (R⁻¹ • y)) x‖ ≤
        1 + SchwartzMap.seminorm ℝ 0 j b := by
    let V := EuclideanSpace ℝ (Fin n)
    let L : V →L[ℝ] V := R⁻¹ • ContinuousLinearMap.id ℝ V
    have hL : ‖L‖ ≤ 1 := by
      calc
        ‖L‖ ≤ ‖R⁻¹‖ * ‖ContinuousLinearMap.id ℝ V‖ := norm_smul_le _ _
        _ ≤ 1 * 1 := mul_le_mul
          (by rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hR)
          ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
    have hcomp : ‖iteratedFDeriv ℝ j (fun y ↦ b (R⁻¹ • y)) x‖ ≤
        SchwartzMap.seminorm ℝ 0 j b := by
      change ‖iteratedFDeriv ℝ j (b ∘ L) x‖ ≤ _
      rw [L.iteratedFDeriv_comp_right (b.smooth ⊤) x (by simp)]
      calc
        _ ≤ ‖iteratedFDeriv ℝ j b (L x)‖ * ∏ _ : Fin j, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ SchwartzMap.seminorm ℝ 0 j b * 1 := mul_le_mul
          (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ b j (L x))
          (by simpa using pow_le_one₀ (norm_nonneg L) hL (n := j))
          (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _)) (apply_nonneg _ _)
        _ = _ := mul_one _
    have hs : ContDiff ℝ (j : ℕ∞ω) (fun y : V ↦ b (R⁻¹ • y)) := by
      exact (b.smooth j).comp L.contDiff
    change ‖iteratedFDeriv ℝ j ((fun _ : V ↦ (1 : ℝ)) -
      (fun y : V ↦ b (R⁻¹ • y))) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply (contDiffAt_const (c := (1 : ℝ))) hs.contDiffAt]
    apply (norm_sub_le _ _).trans
    apply add_le_add _ hcomp
    by_cases hj : j = 0
    · subst j
      simp
    · rw [iteratedFDeriv_const_of_ne hj]
      simp
  -- The error vanishes on the expanding ball; one extra spatial weight bounds its tail.
  have cutoff_tail {n : ℕ} (b : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) (hb : HasCompactSupport b)
      (hone : ∀ x, ‖x‖ ≤ 1 → b x = 1) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (k m : ℕ) (R : ℝ) (hR : 1 ≤ R) :
      let a := fun x ↦ (1 : ℝ) - b (R⁻¹ • x)
      SchwartzMap.seminorm ℂ k m (SchwartzMap.smulLeftCLM ℂ a φ) ≤
        (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          (1 + SchwartzMap.seminorm ℝ 0 i b) *
          SchwartzMap.seminorm ℂ (k + 1) (m - i) φ) / R := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    intro a
    have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hbs : ContDiff ℝ ∞ (fun x : V ↦ b (R⁻¹ • x)) := by fun_prop
    have hbc : HasCompactSupport (fun x : V ↦ b (R⁻¹ • x)) :=
      hb.comp_smul (inv_ne_zero hRp.ne')
    have hag : a.HasTemperateGrowth := Function.HasTemperateGrowth.sub
      (by fun_prop) (hbc.hasTemperateGrowth hbs)
    let e := SchwartzMap.smulLeftCLM ℂ a φ
    have he : ⇑e = fun x ↦ a x • φ x := SchwartzMap.smulLeftCLM_apply hag φ
    have ha : ContDiff ℝ ∞ a := contDiff_const.sub hbs
    let C : ℝ := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      (1 + SchwartzMap.seminorm ℝ 0 i b) * SchwartzMap.seminorm ℂ (k + 1) (m - i) φ
    have hC : 0 ≤ C := by positivity
    apply SchwartzMap.seminorm_le_bound ℂ k m e (div_nonneg hC hRp.le)
    intro x
    rw [le_div_iff₀ hRp]
    by_cases hx : ‖x‖ < R
    · have hzero : (e : V → ℂ) =ᶠ[𝓝 x] 0 := by
        filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with y hy
        rw [he]
        have hby : b (R⁻¹ • y) = 1 := by
          apply hone
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hRp.le), ← div_eq_inv_mul]
          exact (div_le_one hRp).mpr hy.le
        simp only [a, hby, sub_self, zero_smul, Pi.zero_apply]
      rw [(hzero.iteratedFDeriv ℝ m).eq_of_nhds]
      simpa using hC
    · have hRx : R ≤ ‖x‖ := le_of_not_gt hx
      have hprod := norm_iteratedFDeriv_smul_le ha (φ.smooth ⊤) x (n := m) (by simp)
      rw [he]
      calc
        (‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x ↦ a x • φ x) x‖) * R ≤
            (‖x‖ ^ k * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i a x‖ * ‖iteratedFDeriv ℝ (m - i) φ x‖) * R := by
          gcongr
        _ = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i a x‖ *
            (R * ‖x‖ ^ k * ‖iteratedFDeriv ℝ (m - i) φ x‖) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ C := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (uniform_cutoff_derivative b R hR i x)
              (Nat.cast_nonneg _)
          · calc
              R * ‖x‖ ^ k * ‖iteratedFDeriv ℝ (m - i) φ x‖ ≤
                  ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (m - i) φ x‖ := by
                rw [pow_succ]
                nlinarith [mul_nonneg (pow_nonneg (norm_nonneg x) k)
                  (norm_nonneg (iteratedFDeriv ℝ (m - i) φ x))]
              _ ≤ _ := SchwartzMap.le_seminorm ℂ (k + 1) (m - i) φ x
          · positivity
          · positivity
  -- Every Schwartz seminorm of the cutoff error tends to zero.
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let b : ContDiffBump (0 : V) :=
    { rIn := 1
      rOut := 2
      rIn_pos := zero_lt_one
      rIn_lt_rOut := one_lt_two }
  let β : 𝓢(V, ℝ) := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hβ : HasCompactSupport β := b.hasCompactSupport
  have hβone (x : V) (hx : ‖x‖ ≤ 1) : β x = 1 := by
    apply b.one_of_mem_closedBall
    simpa [Metric.mem_closedBall, dist_zero_right, b] using hx
  let R (a : ℕ) : ℝ := a + 1
  have hR (a : ℕ) : 1 ≤ R a := by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) a]
  let χ (a : ℕ) (x : V) : ℝ := β ((R a)⁻¹ • x)
  have hcχ (a : ℕ) : HasCompactSupport (χ a) :=
    hβ.comp_smul (inv_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one (hR a))))
  have hχ (a : ℕ) : ContDiff ℝ ∞ (χ a) := by dsimp [χ]; fun_prop
  have hg (a : ℕ) : (χ a).HasTemperateGrowth := (hcχ a).hasTemperateGrowth (hχ a)
  intro φ
  let ψ (a : ℕ) := SchwartzMap.smulLeftCLM ℂ (χ a) φ
  have hcψ (a : ℕ) : HasCompactSupport (ψ a) := by
    change HasCompactSupport (SchwartzMap.smulLeftCLM ℂ (χ a) φ)
    rw [SchwartzMap.smulLeftCLM_apply (hg a)]
    exact (hcχ a).smul_right
  have ht : Tendsto ψ atTop (𝓝 φ) := by
    apply ((schwartz_withSeminorms ℂ V ℂ).tendsto_nhds_atTop ψ φ).mpr
    rintro ⟨k, m⟩ ε hε
    let C : ℝ := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      (1 + SchwartzMap.seminorm ℝ 0 i β) *
      SchwartzMap.seminorm ℂ (k + 1) (m - i) φ
    obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
    refine ⟨N, ?_⟩
    intro a ha
    have hRa : 0 < R a := lt_of_lt_of_le zero_lt_one (hR a)
    have hag : (fun x ↦ (1 : ℝ) - χ a x).HasTemperateGrowth :=
      Function.HasTemperateGrowth.sub (by fun_prop) (hg a)
    have he : ψ a - φ = -(SchwartzMap.smulLeftCLM ℂ (fun x ↦ (1 : ℝ) - χ a x) φ) := by
      ext x
      simp only [ψ, sub_apply, neg_apply,
        SchwartzMap.smulLeftCLM_apply_apply (hg a),
        SchwartzMap.smulLeftCLM_apply_apply hag, sub_smul, one_smul, neg_sub]
    change SchwartzMap.seminorm ℂ k m (ψ a - φ) < ε
    rw [he, map_neg_eq_map]
    apply lt_of_le_of_lt (cutoff_tail β hβ hβone φ k m (R a) (hR a))
    change C / R a < ε
    rw [div_lt_iff₀ hRa]
    have hNa : (N : ℝ) ≤ a := by exact_mod_cast ha
    have hC := (div_lt_iff₀ hε).mp hN
    dsimp [R]
    nlinarith
  exact mem_closure_of_tendsto ht (Filter.Eventually.of_forall hcψ)

/-- The Bessel realization is injective, so the transported norm is nondegenerate. -/
theorem besselRealization_injective (n r : ℕ) (s : ℝ) :
    Function.Injective (besselRealization n r s) := by
  /- Apply J^s to cancel J^(-s). The embedding of L² into tempered distributions
  is injective, as established by mathlib's zero-kernel lemma for that embedding. -/
  intro f g h
  -- Applying the opposite Bessel weight recovers the original L² distributions.
  have hdist := congrArg (besselPotential _ _ s) h
  simp only [besselRealization, ContinuousLinearMap.comp_apply,
    besselPotential_besselPotential_apply, neg_add_cancel, besselPotential_zero,
    ContinuousLinearMap.id_apply] at hdist
  -- The canonical L² distribution embedding has zero kernel.
  exact (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot) hdist

/-- Bessel coordinates give exactly the existing Fourier Sobolev predicate. -/
theorem memSobolev_iff_exists_besselRealization (s : ℝ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    u.MemSobolev s 2 ↔ ∃ f, besselRealization n r s f = u := by
  /- MemSobolev says precisely that J^s u is represented by an L² function f.
  Apply J^(-s) in one direction and J^s in the other. -/
  change (∃ f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))), besselPotential _ _ s u = f) ↔ _
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (besselPotential_neg_apply_eq_iff s _ u).mpr hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, (besselPotential_neg_apply_eq_iff s _ u).mp hf⟩

/-- The natural inclusion H^s → H^t is bounded when t ≤ s. -/
theorem exists_sobolev_inclusion (n r : ℕ) (s t : ℝ) (hst : t ≤ s) :
    ∃ J : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin r)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ‖J‖ ≤ 1 ∧ ∀ f, besselRealization n r t (J f) = besselRealization n r s f := by
  /- In Bessel coordinates the inclusion is the Fourier multiplier
  (1+|ξ|²)^((t-s)/2). Its absolute value is at most one. Plancherel gives the
  norm bound and the product rule for Bessel multipliers gives the intertwining identity. -/
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let g : X → ℂ := fun ξ ↦ ((1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2) : ℝ)
  -- The nonpositive Bessel exponent gives an everywhere bounded smooth multiplier.
  have hg : g.HasTemperateGrowth := by
    dsimp [g]
    fun_prop
  have hg_le (ξ : X) : ‖g ξ‖ ≤ 1 := by
    dsimp [g]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)
  let g' : BoundedContinuousFunction X ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup g hg.1.continuous 1 hg_le
  have hgLp : MemLp g ⊤ (volume : Measure X) := g'.memLp_top
  let a : Lp ℂ ⊤ (volume : Measure X) := hgLp.toLp g
  have ha : ‖a‖ ≤ 1 := by
    rw [Lp.norm_toLp, eLpNorm_exponent_top hgLp.aestronglyMeasurable]
    have hess : eLpNormEssSup g volume ≤ 1 := by
      simpa using eLpNormEssSup_le_of_ae_bound (μ := volume)
        (Filter.Eventually.of_forall hg_le)
    simpa using ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) hess
  -- Fourier conjugation preserves complex linearity and the L2 contraction bound.
  let T : Lp V 2 (volume : Measure X) →ₗ[ℂ] Lp V 2 (volume : Measure X) :=
    { toFun := fun f ↦ 𝓕⁻ (a • 𝓕 f)
      map_add' := by
        intro f₁ f₂
        rw [FourierTransform.fourier_add, Lp.add_smul, FourierTransform.fourierInv_add]
      map_smul' := by
        intro c f
        rw [FourierTransform.fourier_smul, ← Lp.smul_comm,
          FourierTransform.fourierInv_smul]
        rfl }
  have hT (f : Lp V 2 (volume : Measure X)) : ‖T f‖ ≤ 1 * ‖f‖ := by
    change ‖(Lp.fourierTransformₗᵢ X V).symm (a • 𝓕 f)‖ ≤ _
    rw [(Lp.fourierTransformₗᵢ X V).symm.norm_map]
    calc
      ‖a • 𝓕 f‖ ≤ ‖a‖ * ‖𝓕 f‖ := Lp.norm_smul_le a (𝓕 f)
      _ ≤ 1 * ‖f‖ := by
        rw [Lp.norm_fourier_eq]
        exact mul_le_mul_of_nonneg_right ha (norm_nonneg f)
  let J : Lp V 2 (volume : Measure X) →L[ℂ] Lp V 2 (volume : Measure X) :=
    T.mkContinuous 1 hT
  -- The L2 multiplier and its distributional Bessel operator are the same map.
  have hdist (f : Lp V 2 (volume : Measure X)) :
      (J f : 𝓢'(X, V)) = besselPotential X V (t - s) (f : 𝓢'(X, V)) := by
    change ((𝓕⁻ (a • 𝓕 f) : Lp V 2 (volume : Measure X)) : 𝓢'(X, V)) = _
    rw [← Lp.fourierInv_toTemperedDistribution_eq,
      Lp.toTemperedDistribution_smul_eq hg hgLp,
      ← Lp.fourier_toTemperedDistribution_eq]
    rfl
  refine ⟨J, T.mkContinuous_norm_le (by norm_num) hT, ?_⟩
  intro f
  change besselPotential X V (-t) (J f : 𝓢'(X, V)) =
    besselPotential X V (-s) (f : 𝓢'(X, V))
  rw [hdist, besselPotential_besselPotential_apply]
  rw [show t - s + -t = -s by ring]

set_option maxHeartbeats 4000000 in
-- The extended limit accommodates the Fourier cutoff estimates and compactness argument.

open Filter Set in
open scoped BoundedContinuousFunction in
/-- The natural inclusion is compact on distributions supported in a fixed compact set.
This covers all real orders s > t and includes vector-valued distributions. -/
theorem rellich_compact_inclusion (n r : ℕ) (s t : ℝ) (hst : t < s)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (J : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hJ : ∀ f, besselRealization n r t (J f) = besselRealization n r s f) :
    IsCompact (closure (J '' {f | ‖f‖ ≤ 1 ∧
      IsSupportedIn (besselRealization n r s f) K})) := by
  /- First construct continuous Fourier representatives for the fixed compact support.
  Weighted Schwartz kernels give uniform bounds and Lipschitz estimates on every ball.
  Compact-test support identities extend by Schwartz density; the resulting representatives
  agree almost everywhere with the original Bessel coordinates. Arzela-Ascoli and the
  strictly lower-order Fourier tail give a compact L2 closure. Fourier inversion then
  returns exactly the specified inclusion J. All auxiliary steps remain proof-local. -/
  -- Schwartz decay absorbs the polynomial Bessel weight uniformly on each frequency ball.
  have translated_weighted_derivative_bound {n : ℕ}
      (b : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (a : EuclideanSpace ℝ (Fin n) → ℂ)
      (ha : a.HasTemperateGrowth) (R : ℝ) (hR : 0 ≤ R) (d j : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R →
        ‖a y‖ * ‖iteratedFDeriv ℝ j b (x - y)‖ ≤
          C * (1 + ‖y‖) ^ (-(d : ℝ)) := by
    obtain ⟨k, A, hA, haA⟩ := ha.norm_iteratedFDeriv_le_uniform 0
    have hpoly (y : EuclideanSpace ℝ (Fin n)) : ‖a y‖ ≤ A * (1 + ‖y‖) ^ k := by
      simpa using haA 0 le_rfl y
    let B := 2 ^ (k + d) *
      (Finset.Iic (k + d, j)).sup (fun q ↦ SchwartzMap.seminorm ℂ q.1 q.2) b
    have hB : 0 ≤ B := by positivity
    refine ⟨A * (1 + R) ^ (k + d) * B, by positivity, ?_⟩
    intro x y hx
    have hscale : 1 + ‖y‖ ≤ (1 + R) * (1 + ‖x - y‖) := by
      have hy : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
        calc
          ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_self]
          _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
      nlinarith [norm_nonneg (x - y), mul_nonneg hR (norm_nonneg (x - y))]
    have hdecay : (1 + ‖y‖) ^ (k + d) * ‖iteratedFDeriv ℝ j b (x - y)‖ ≤
        (1 + R) ^ (k + d) * B := by
      calc
        _ ≤ ((1 + R) * (1 + ‖x - y‖)) ^ (k + d) *
            ‖iteratedFDeriv ℝ j b (x - y)‖ := by gcongr
        _ = (1 + R) ^ (k + d) *
            ((1 + ‖x - y‖) ^ (k + d) * ‖iteratedFDeriv ℝ j b (x - y)‖) := by
          rw [mul_pow, mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (SchwartzMap.one_add_le_sup_seminorm_apply
            (𝕜 := ℂ) (m := (k + d, j)) le_rfl le_rfl b (x - y)) (by positivity)
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < (1 + ‖y‖) ^ d)).mpr
    calc
      _ ≤ (A * (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ j b (x - y)‖) *
          (1 + ‖y‖) ^ d := by gcongr; exact hpoly y
      _ = A * ((1 + ‖y‖) ^ (k + d) * ‖iteratedFDeriv ℝ j b (x - y)‖) := by
        rw [pow_add]
        ring
      _ ≤ A * ((1 + R) ^ (k + d) * B) := mul_le_mul_of_nonneg_left hdecay hA
      _ = _ := by ring
  -- The mean-value estimate gives the same weighted decay for frequency differences.
  have translated_weighted_difference_bound {n : ℕ}
      (b : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (a : EuclideanSpace ℝ (Fin n) → ℂ)
      (ha : a.HasTemperateGrowth) (R : ℝ) (hR : 0 ≤ R) (d : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x z y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R → ‖z‖ ≤ R →
        ‖a y * (b (x - y) - b (z - y))‖ ≤
          C * ‖x - z‖ * (1 + ‖y‖) ^ (-(d : ℝ)) := by
    obtain ⟨C, hC, hbound⟩ := translated_weighted_derivative_bound b a ha R hR d 1
    refine ⟨C, hC, ?_⟩
    intro x z y hx hz
    let f := fun v : EuclideanSpace ℝ (Fin n) ↦ a y * b (v - y)
    have hdiff (v : EuclideanSpace ℝ (Fin n)) : DifferentiableAt ℝ f v := by
      have hb : Differentiable ℝ b := (b.smooth ⊤).differentiable (by simp)
      exact ((hb.differentiableAt).comp v (differentiableAt_id.sub_const y)).const_mul (a y)
    have hderiv (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ Metric.closedBall 0 R) :
        ‖fderiv ℝ f v‖ ≤ C * (1 + ‖y‖) ^ (-(d : ℝ)) := by
      have hv' : ‖v‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hv
      have hf : HasFDerivAt f
          (a y • fderiv ℝ b (v - y)) v := by
        have hb := (((b.smooth ⊤).differentiable (by simp)).differentiableAt
          (x := v - y)).hasFDerivAt
        convert (hb.comp v ((hasFDerivAt_id v).sub_const y)).const_smul (a y) using 1
        · rfl
        · simp
      rw [hf.fderiv, norm_smul]
      simpa only [norm_iteratedFDeriv_one] using hbound v y hv'
    have hm := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun v _ ↦ hdiff v) hderiv (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
    simpa only [f, ← mul_sub, mul_right_comm] using hm
  -- A fixed square-integrable majorant turns those pointwise estimates into L2 bounds.
  have kernel_local_l2_bounds {n : ℕ}
      (b : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (a : EuclideanSpace ℝ (Fin n) → ℂ)
      (ha : a.HasTemperateGrowth)
      (κ : EuclideanSpace ℝ (Fin n) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (hκ : ∀ x y, κ x y = a y * b (x - y)) (R : ℝ) (hR : 0 ≤ R) :
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ x, ‖x‖ ≤ R → ‖(κ x).toLp 2 volume‖ ≤ C) ∧
        (∀ x z, ‖x‖ ≤ R → ‖z‖ ≤ R →
          ‖(κ x).toLp 2 volume - (κ z).toLp 2 volume‖ ≤ C * ‖x - z‖) := by
    let V := EuclideanSpace ℝ (Fin n)
    let d : ℕ := n + 1
    let q : V → ℝ := fun y ↦ (1 + ‖y‖) ^ (-(d : ℝ))
    have hqc : Continuous q := by
      have hc : Continuous (fun y : V ↦ (1 : ℝ) + ‖y‖) := continuous_const.add continuous_norm
      exact hc.rpow_const (fun y ↦ Or.inl (by positivity))
    have hqm : MemLp q 2 volume := by
      apply (memLp_two_iff_integrable_sq hqc.aestronglyMeasurable).mpr
      have hi : Integrable (fun y : V ↦ (1 + ‖y‖) ^ (-(2 * d : ℝ))) :=
        integrable_one_add_norm (by simp [V, d]; linarith [Nat.cast_nonneg (α := ℝ) n])
      convert hi using 1
      funext y
      dsimp [q]
      rw [← Real.rpow_mul_natCast (by positivity)]
      congr 1
      ring
    let Q : Lp ℝ 2 (volume : Measure V) := hqm.toLp q
    obtain ⟨C₀, hC₀, hb₀⟩ := translated_weighted_derivative_bound b a ha R hR d 0
    obtain ⟨C₁, hC₁, hb₁⟩ := translated_weighted_difference_bound b a ha R hR d
    refine ⟨max C₀ C₁ * ‖Q‖, by positivity, ?_, ?_⟩
    · intro x hx
      have hbound : ‖(κ x).toLp 2 volume‖ ≤ C₀ * ‖Q‖ := by
        apply Lp.norm_le_mul_norm_of_ae_le_mul
        filter_upwards [(κ x).coeFn_toLp 2 volume, hqm.coeFn_toLp] with y hy hQy
        rw [hy, hQy, Real.norm_of_nonneg (by dsimp [q]; positivity), hκ, norm_mul]
        simpa only [norm_iteratedFDeriv_zero] using hb₀ x y hx
      exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · intro x z hx hz
      have hbound : ‖(κ x).toLp 2 volume - (κ z).toLp 2 volume‖ ≤ (C₁ * ‖x - z‖) * ‖Q‖ := by
        apply Lp.norm_le_mul_norm_of_ae_le_mul
        filter_upwards [Lp.coeFn_sub ((κ x).toLp 2 volume) ((κ z).toLp 2 volume),
          (κ x).coeFn_toLp 2 volume, (κ z).coeFn_toLp 2 volume,
          hqm.coeFn_toLp] with y hsub hyx hyz hQy
        rw [hsub, Pi.sub_apply, hyx, hyz, hQy, hκ, hκ, ← mul_sub,
          Real.norm_of_nonneg (by dsimp [q]; positivity)]
        exact hb₁ x z y hx hz
      calc
        _ ≤ (C₁ * ‖x - z‖) * ‖Q‖ := hbound
        _ ≤ (max C₀ C₁ * ‖x - z‖) * ‖Q‖ := by gcongr; exact le_max_right _ _
        _ = _ := by ring
  -- The local Lipschitz estimates give continuity of the L2-valued kernel.
  have continuous_kernel_toLp {n : ℕ}
      (b : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (a : EuclideanSpace ℝ (Fin n) → ℂ)
      (ha : a.HasTemperateGrowth)
      (κ : EuclideanSpace ℝ (Fin n) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (hκ : ∀ x y, κ x y = a y * b (x - y)) :
      Continuous (fun x ↦ (κ x).toLp 2 volume) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    obtain ⟨C, hC, _, hL⟩ := kernel_local_l2_bounds b a ha κ hκ (‖x‖ + 1) (by positivity)
    have hLip : LipschitzOnWith C.toNNReal (fun x ↦ (κ x).toLp 2 volume)
        (Metric.closedBall 0 (‖x‖ + 1)) := by
      apply LipschitzOnWith.of_dist_le'
      intro y hy z hz
      simpa only [dist_eq_norm] using hL y z
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
    apply hLip.continuousOn.continuousAt
    apply Metric.closedBall_mem_nhds_of_mem
    simp only [Metric.mem_ball, dist_zero_right, lt_add_iff_pos_right, zero_lt_one]
  -- Holder pairing transfers the kernel bounds to all vector-valued L2 inputs.
  have weighted_convolution_local_bounds {n : ℕ}
      (r : ℕ) (b : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (a : EuclideanSpace ℝ (Fin n) → ℂ) (ha : a.HasTemperateGrowth)
      (κ : EuclideanSpace ℝ (Fin n) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (hκ : ∀ x y, κ x y = a y * b (x - y))
      (R : ℝ) (hR : 0 ≤ R) :
      let B := (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ]
        EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)).lpPairing volume 2 2
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ f : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
          ∀ x, ‖x‖ ≤ R → ‖B ((κ x).toLp 2 volume) f‖ ≤ C * ‖f‖) ∧
        (∀ f : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
          ∀ x z, ‖x‖ ≤ R → ‖z‖ ≤ R →
            ‖B ((κ x).toLp 2 volume) f - B ((κ z).toLp 2 volume) f‖ ≤
              C * ‖f‖ * ‖x - z‖) := by
    intro B
    obtain ⟨C, hC, hbound, hLip⟩ := kernel_local_l2_bounds b a ha κ hκ R hR
    refine ⟨‖B‖ * C, by positivity, ?_, ?_⟩
    · intro f x hx
      exact (B.le_opNorm₂ _ _).trans (by gcongr; exact hbound x hx)
    · intro f x z hx hz
      rw [← sub_apply, ← map_sub]
      calc
        _ ≤ ‖B‖ * ‖(κ x).toLp 2 volume - (κ z).toLp 2 volume‖ * ‖f‖ := B.le_opNorm₂ _ _
        _ ≤ ‖B‖ * (C * ‖x - z‖) * ‖f‖ := by gcongr; exact hLip x z hx hz
        _ = _ := by ring
  -- On Schwartz inputs, multiplication and convolution use the original Fourier normalization.
  have product_fourier {n : ℕ} {r : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (g : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
      𝓕 (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) f g) =
        SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) (𝓕 f) (𝓕 g) := by
    open FourierTransform in
    apply (fourierEquiv ℂ 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))).symm.injective
    rw [FourierTransform.fourierEquiv_symm_apply, FourierTransform.fourierEquiv_symm_apply,
      FourierTransform.fourierInv_fourier_eq]
    apply SchwartzMap.ext
    intro x
    change f x • g x =
      (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) (𝓕 f) (𝓕 g))) (-x)
    rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
    change f x • g x = (𝓕⁻ (𝓕 f)) x • (𝓕⁻ (𝓕 g)) x
    rw [FourierTransform.fourierInv_fourier_eq, FourierTransform.fourierInv_fourier_eq]
  /- Extend the Fourier formula from dense Schwartz inputs using a compactly supported
  operator-valued integral. -/
  have exists_cutoff_fourier_representative {n : ℕ} (r : ℕ)
      (χ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (a : EuclideanSpace ℝ (Fin n) → ℂ) (ha : a.HasTemperateGrowth) :
      ∃ T : EuclideanSpace ℝ (Fin n) →
        (Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
          EuclideanSpace ℂ (Fin r)), Continuous T ∧
        (∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
          (∀ f x, ‖x‖ ≤ R → ‖T x f‖ ≤ C * ‖f‖) ∧
          (∀ f x z, ‖x‖ ≤ R → ‖z‖ ≤ R → ‖T x f - T z f‖ ≤ C * ‖f‖ * ‖x - z‖)) ∧
        ∀ (f : Lp (EuclideanSpace ℂ (Fin r)) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n))))
          (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)), HasCompactSupport φ →
            (𝓕 (TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin r)) χ
              (TemperedDistribution.fourierMultiplierCLM (EuclideanSpace ℂ (Fin r)) a
                (f : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))))) φ =
              ∫ x, φ x • T x f := by
    let V := EuclideanSpace ℝ (Fin n)
    let H := EuclideanSpace ℂ (Fin r)
    let κ (x : V) : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ a
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)
        (𝓕 χ)).compSubConstCLM ℂ x)
    have hκ (x y : V) : κ x y = a y * (𝓕 χ) (x - y) := by
      simp only [κ, SchwartzMap.smulLeftCLM_apply_apply ha, smul_eq_mul,
        SchwartzMap.compSubConstCLM_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp_apply, ContinuousLinearEquiv.neg_apply, neg_sub]
    let B := (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).lpPairing
      (volume : Measure V) 2 2
    let T (x : V) : Lp H 2 (volume : Measure V) →L[ℂ] H :=
      (B ((κ x).toLp 2 volume)).comp (FourierTransform.fourierCLM ℂ _)
    have hT : Continuous T :=
      (B.continuous.comp (continuous_kernel_toLp (𝓕 χ) a ha κ hκ)).clm_comp continuous_const
    refine ⟨T, hT, ?_, ?_⟩
    · intro R hR
      obtain ⟨C, hC, hnorm, hLip⟩ :=
        weighted_convolution_local_bounds r (𝓕 χ) a ha κ hκ R hR
      refine ⟨C, hC, ?_, ?_⟩
      · intro f x hx
        change ‖B ((κ x).toLp 2 volume) (𝓕 f)‖ ≤ C * ‖f‖
        simpa only [Lp.norm_fourier_eq] using hnorm (𝓕 f) x hx
      · intro f x z hx hz
        change ‖B ((κ x).toLp 2 volume) (𝓕 f) - B ((κ z).toLp 2 volume) (𝓕 f)‖ ≤ _
        simpa only [Lp.norm_fourier_eq] using hLip (𝓕 f) x z hx hz
    · intro f φ hφ
      -- The compactly supported operator-valued integral is a bounded linear map of f.
      have hint : Integrable (fun x ↦ φ x • T x) :=
        (φ.continuous.smul hT).integrable_of_hasCompactSupport hφ.smul_right
      let I : Lp H 2 (volume : Measure V) →L[ℂ] H := ∫ x, φ x • T x
      have hI (f : Lp H 2 (volume : Measure V)) : I f = ∫ x, φ x • T x f := by
        exact ContinuousLinearMap.integral_apply hint f
      let D : Lp H 2 (volume : Measure V) → 𝓢'(V, H) := fun f ↦
        𝓕 (TemperedDistribution.smulLeftCLM H χ
          (TemperedDistribution.fourierMultiplierCLM H a (f : 𝓢'(V, H))))
      have hD : Continuous D := FourierTransform.continuous_fourier.comp
        ((TemperedDistribution.smulLeftCLM H χ).continuous.comp
          ((TemperedDistribution.fourierMultiplierCLM H a).continuous.comp
            (Lp.toTemperedDistributionCLM H volume 2).continuous))
      have heq : (fun f ↦ D f φ) = I := by
        apply (SchwartzMap.denseRange_toLpCLM (F := H) (by simp : (2 : ENNReal) ≠ ⊤)).equalizer
          ((continuous_eval_const φ).comp hD) I.continuous
        funext g
        -- On Schwartz inputs Fourier multiplication is the usual convolution identity.
        let v : 𝓢(V, H) := SchwartzMap.fourierMultiplierCLM H a g
        let w : 𝓢(V, H) := SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) χ v
        have hdist : D (g.toLp 2 volume) = (𝓕 w : 𝓢(V, H)) := by
          dsimp [D]
          rw [Lp.toTemperedDistribution_toLp_eq,
            TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq ha]
          have hmul : TemperedDistribution.smulLeftCLM H χ (v : 𝓢'(V, H)) =
              (w : 𝓢'(V, H)) := by
            apply DFunLike.ext
            intro ψ
            rw [TemperedDistribution.smulLeftCLM_apply_apply, SchwartzMap.coe_apply,
              SchwartzMap.coe_apply]
            apply integral_congr_ae
            filter_upwards with x
            simp only [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,
              w, SchwartzMap.pairing_apply_apply, ContinuousLinearMap.lsmul_apply,
              smul_smul, smul_eq_mul, mul_comm]
          rw [hmul]
          exact TemperedDistribution.fourier_toTemperedDistributionCLM_eq w
        have hpoint (x : V) : T x (g.toLp 2 volume) = (𝓕 w) x := by
          dsimp [T]
          rw [SchwartzMap.toLp_fourier_eq]
          change B ((κ x).toLp 2 volume) ((𝓕 g).toLp 2 volume) = _
          rw [ContinuousLinearMap.lpPairing_eq_integral]
          have hconv : (𝓕 w) x = ∫ y, (𝓕 χ) (x - y) • (𝓕 v) y := by
            rw [show w = SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) χ v from rfl,
              product_fourier, SchwartzMap.convolution_apply]
            exact (congrFun (convolution_flip (ContinuousLinearMap.lsmul ℂ ℂ)
              (f := ⇑(𝓕 χ : 𝓢(V, ℂ))) (g := ⇑(𝓕 v : 𝓢(V, H))) (μ := volume)) x).symm
          rw [hconv]
          apply integral_congr_ae
          filter_upwards [(κ x).coeFn_toLp 2 volume, (𝓕 g).coeFn_toLp 2 volume] with y hyκ hyg
          rw [hyκ, hyg, hκ]
          have hv : 𝓕 v = SchwartzMap.smulLeftCLM H a (𝓕 g) := by
            exact FourierTransform.fourier_fourierInv_eq _
          rw [hv, SchwartzMap.smulLeftCLM_apply_apply ha]
          change (a y * (𝓕 χ) (x - y)) • (𝓕 g) y = _
          rw [smul_smul, mul_comm]
        change D (g.toLp 2 volume) φ = I (g.toLp 2 volume)
        rw [hdist, SchwartzMap.coe_apply, hI]
        exact integral_congr_ae (ae_of_all _ (fun x ↦ congrArg (φ x • ·) (hpoint x).symm))
      exact (congrFun heq f).trans (hI f)
  -- A plateau cutoff fixes supported distributions, first on compact tests and then by density.
  have exists_schwartz_cutoff_identity {n : ℕ} (r : ℕ)
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) :
      ∃ χ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        ∀ u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
          AtiyahSinger.IsSupportedIn u K →
            TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin r)) χ u = u := by
    let V := EuclideanSpace ℝ (Fin n)
    obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : V)
    let b : ContDiffBump (0 : V) :=
      { rIn := R
        rOut := R + 1
        rIn_pos := hR
        rIn_lt_rOut := lt_add_one R }
    have hbc : HasCompactSupport (Complex.ofRealCLM ∘ b) :=
      b.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl
    let χ : 𝓢(V, ℂ) := hbc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
    have hone (x : V) (hx : x ∈ K) : ∀ᶠ y in 𝓝 x, χ y = 1 := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (hKR hx)] with y hy
      change (b y : ℂ) = 1
      rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), Complex.ofReal_one]
    refine ⟨χ, ?_⟩
    intro u hu
    let T := TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin r)) χ u
    have htest (φ : 𝓢(V, ℂ)) (hφ : HasCompactSupport φ) : T φ = u φ := by
      let ψ := SchwartzMap.smulLeftCLM ℂ χ φ
      have hcψ : HasCompactSupport ψ := by
        rw [show ⇑ψ = fun x ↦ χ x • φ x from
          SchwartzMap.smulLeftCLM_apply χ.hasTemperateGrowth φ]
        exact hφ.smul_left (f := fun x ↦ χ x)
      have hd : Disjoint (tsupport (φ - ψ)) K := by
        apply Set.disjoint_left.mpr
        intro x hx hxK
        apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
        filter_upwards [hone x hxK] with y hy
        change φ y - ψ y = 0
        rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, hy]
        simp
      have hpair := hu.apply_eq_zero (φ - ψ) (hφ.sub hcψ) hd
      rw [map_sub] at hpair
      exact (sub_eq_zero.mp hpair).symm
    apply DFunLike.ext
    intro φ
    have hc : IsClosed {φ | T φ = u φ} := isClosed_eq T.continuous u.continuous
    exact closure_minimal htest hc (AtiyahSinger.dense_hasCompactSupport_schwartz n φ)
  -- Compact test uniqueness identifies the continuous representative almost everywhere.
  have exists_supported_fourier_representative {n : ℕ} (r : ℕ) (s : ℝ)
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) :
      ∃ T : EuclideanSpace ℝ (Fin n) →
        (Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
          EuclideanSpace ℂ (Fin r)), Continuous T ∧
        (∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
          (∀ f x, ‖x‖ ≤ R → ‖T x f‖ ≤ C * ‖f‖) ∧
          (∀ f x z, ‖x‖ ≤ R → ‖z‖ ≤ R → ‖T x f - T z f‖ ≤ C * ‖f‖ * ‖x - z‖)) ∧
        ∀ f : Lp (EuclideanSpace ℂ (Fin r)) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n))),
          AtiyahSinger.IsSupportedIn (AtiyahSinger.besselRealization n r s f) K →
            (fun x ↦ T x f) =ᵐ[volume]
              (fun x ↦ ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) • (𝓕 f) x) := by
    let V := EuclideanSpace ℝ (Fin n)
    let H := EuclideanSpace ℂ (Fin r)
    let a : V → ℂ := fun x ↦ ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)
    have ha : a.HasTemperateGrowth := by dsimp [a]; fun_prop
    obtain ⟨χ, hχ⟩ := exists_schwartz_cutoff_identity r K hK
    obtain ⟨T, hT, hbound, hrepr⟩ := exists_cutoff_fourier_representative r χ a ha
    refine ⟨T, hT, hbound, ?_⟩
    intro f hf
    have hFc : Continuous (fun x ↦ T x f) := hT.clm_apply continuous_const
    have hflocal : LocallyIntegrable (fun x ↦ a x • (𝓕 f) x) volume :=
      ((Lp.memLp (𝓕 f)).locallyIntegrable (by norm_num)).continuous_smul ha.1.continuous
    have hae : (fun x ↦ T x f) =ᵐ[volume] (fun x ↦ a x • (𝓕 f) x) := by
      apply ae_eq_of_integral_contDiff_smul_eq hFc.locallyIntegrable hflocal
      intro φ hφ hcφ
      have hcφC : HasCompactSupport (Complex.ofRealCLM ∘ φ) :=
        hcφ.comp_left (g := Complex.ofRealCLM) rfl
      let ψ : 𝓢(V, ℂ) := hcφC.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφ)
      have hcψ : HasCompactSupport ψ := hcφ.comp_left (g := Complex.ofRealCLM) rfl
      have hid := hrepr f ψ hcψ
      change (𝓕 (TemperedDistribution.smulLeftCLM H χ
        (AtiyahSinger.besselRealization n r s f))) ψ = ∫ x, ψ x • T x f at hid
      rw [hχ _ hf] at hid
      have heval : (𝓕 (AtiyahSinger.besselRealization n r s f)) ψ =
          ∫ x, ψ x • (a x • (𝓕 f) x) := by
        change (𝓕 (TemperedDistribution.besselPotential V H (-s)
          (f : 𝓢'(V, H)))) ψ = _
        rw [TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
          Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.smulLeftCLM_apply_apply,
          Lp.toTemperedDistribution_apply]
        apply integral_congr_ae
        filter_upwards with x
        rw [SchwartzMap.smulLeftCLM_apply_apply ha]
        change (a x • ψ x) • (𝓕 f) x = ψ x • (a x • (𝓕 f) x)
        simp only [smul_smul, smul_eq_mul, mul_comm]
      rw [heval] at hid
      change (∫ x, (φ x : ℂ) • (a x • (𝓕 f) x)) =
        ∫ x, (φ x : ℂ) • T x f at hid
      simpa only [Complex.coe_smul] using hid.symm
    filter_upwards [hae] with x hx
    simpa only [a, Complex.coe_smul] using hx
  -- Multiplication by the target Bessel weight preserves all local uniform estimates.
  have temperate_smul_local_bounds {n : ℕ} {r : ℕ}
      (a : EuclideanSpace ℝ (Fin n) → ℂ) (ha : a.HasTemperateGrowth)
      (T : EuclideanSpace ℝ (Fin n) →
        (Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
          EuclideanSpace ℂ (Fin r)))
      (hT : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
        (∀ f x, ‖x‖ ≤ R → ‖T x f‖ ≤ C * ‖f‖) ∧
        (∀ f x z, ‖x‖ ≤ R → ‖z‖ ≤ R → ‖T x f - T z f‖ ≤ C * ‖f‖ * ‖x - z‖))
      (R : ℝ) (hR : 0 ≤ R) :
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ f x, ‖f‖ ≤ 1 → ‖x‖ ≤ R → ‖a x • T x f‖ ≤ C) ∧
        (∀ f x z, ‖f‖ ≤ 1 → ‖x‖ ≤ R → ‖z‖ ≤ R →
          ‖a x • T x f - a z • T z f‖ ≤ C * ‖x - z‖) := by
    obtain ⟨C, hC, hnorm, hLip⟩ := hT R hR
    obtain ⟨k, D, hD, hderiv⟩ := ha.norm_iteratedFDeriv_le_uniform 1
    let A := D * (1 + R) ^ k
    have hA : 0 ≤ A := by positivity
    have haA (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ R) : ‖a x‖ ≤ A := by
      have hd := hderiv 0 (by simp) x
      simp only [norm_iteratedFDeriv_zero] at hd
      exact hd.trans (by dsimp [A]; gcongr)
    have hdaA (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.closedBall 0 R) :
        ‖fderiv ℝ a x‖ ≤ A := by
      have hx' : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
      have hd := hderiv 1 le_rfl x
      simp only [norm_iteratedFDeriv_one] at hd
      exact hd.trans (by dsimp [A]; gcongr)
    have haLip (x z : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
        ‖a x - a z‖ ≤ A * ‖x - z‖ := by
      exact Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun v _ ↦ (ha.1.differentiable (by simp)).differentiableAt) hdaA
        (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
    refine ⟨2 * A * C, by positivity, ?_, ?_⟩
    · intro f x hf hx
      rw [norm_smul]
      calc
        _ ≤ A * (C * ‖f‖) := mul_le_mul (haA x hx) (hnorm f x hx) (norm_nonneg _) hA
        _ ≤ A * (C * 1) := by gcongr
        _ ≤ 2 * A * C := by nlinarith [mul_nonneg hA hC]
    · intro f x z hf hx hz
      have hdecomp : a x • T x f - a z • T z f =
          a x • (T x f - T z f) + (a x - a z) • T z f := by
        rw [smul_sub, sub_smul]
        exact (sub_add_sub_cancel _ _ _).symm
      rw [hdecomp]
      calc
        _ ≤ ‖a x • (T x f - T z f)‖ + ‖(a x - a z) • T z f‖ := norm_add_le _ _
        _ = ‖a x‖ * ‖T x f - T z f‖ + ‖a x - a z‖ * ‖T z f‖ := by
          rw [norm_smul, norm_smul]
        _ ≤ A * (C * ‖f‖ * ‖x - z‖) + (A * ‖x - z‖) * (C * ‖f‖) := by
          gcongr
          · exact haA x hx
          · exact hLip f x z hx hz
          · exact haLip x z hx hz
          · exact hnorm f z hz
        _ ≤ A * (C * 1 * ‖x - z‖) + (A * ‖x - z‖) * (C * 1) := by gcongr
        _ = _ := by ring
  -- Arzela-Ascoli controls bounded frequencies; uniform L2 tails give total boundedness globally.
  have l2_criterion {n r : ℕ} {ι : Type}
      (F : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
      (hF : ∀ i, Continuous (F i))
      (hLp : ∀ i, MemLp (F i) 2 volume)
      (hlocal : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 ≤ C ∧
        (∀ i x, x ∈ Metric.closedBall 0 R → ‖F i x‖ ≤ C) ∧
        (∀ i x y, x ∈ Metric.closedBall 0 R → y ∈ Metric.closedBall 0 R →
          ‖F i x - F i y‖ ≤ C * ‖x - y‖))
      (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
        ∀ i, ∫ x in (Metric.closedBall 0 R)ᶜ, ‖F i x‖ ^ 2 ≤ ε) :
      IsCompact (closure (range (fun i ↦ (hLp i).toLp (F i)))) := by
    classical
    let X := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r)
    let G (i : ι) : Lp V 2 (volume : Measure X) := (hLp i).toLp (F i)
    have hnorm (i j : ι) : ‖G i - G j‖ ^ 2 = ∫ x, ‖F i x - F j x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp_rw [real_inner_self_eq_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (G i) (G j), (hLp i).coeFn_toLp,
        (hLp j).coeFn_toLp] with x hx hi hj
      change (G i) x = F i x at hi
      change (G j) x = F j x at hj
      rw [hx, Pi.sub_apply, hi, hj]
    have hlow (R : ℝ) (i j : ι) (δ : ℝ) (hδ : 0 ≤ δ)
        (hclose : ∀ x ∈ Metric.closedBall (0 : X) R, ‖F i x - F j x‖ ≤ δ) :
        ∫ x in Metric.closedBall (0 : X) R, ‖F i x - F j x‖ ^ 2 ≤
          δ ^ 2 * (volume (Metric.closedBall (0 : X) R)).toReal := by
      have hfin : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : X) R)) :=
        ⟨by simpa using (isCompact_closedBall (0 : X) R).measure_lt_top⟩
      have hint := ((hLp i).sub (hLp j)).norm.integrable_sq
      calc
        _ ≤ ∫ _x in Metric.closedBall (0 : X) R, δ ^ 2 :=
          setIntegral_mono_on hint.integrableOn (integrable_const _) measurableSet_closedBall
            (fun x hx ↦ pow_le_pow_left₀ (norm_nonneg _) (hclose x hx) 2)
        _ = _ := by simp [mul_comm, measureReal_def]
    have hhigh (R : ℝ) (i j : ι) :
        ∫ x in (Metric.closedBall (0 : X) R)ᶜ, ‖F i x - F j x‖ ^ 2 ≤
          2 * (∫ x in (Metric.closedBall (0 : X) R)ᶜ, ‖F i x‖ ^ 2) +
          2 * (∫ x in (Metric.closedBall (0 : X) R)ᶜ, ‖F j x‖ ^ 2) := by
      have hi := (hLp i).norm.integrable_sq.integrableOn (s := (Metric.closedBall (0 : X) R)ᶜ)
      have hj := (hLp j).norm.integrable_sq.integrableOn (s := (Metric.closedBall (0 : X) R)ᶜ)
      calc
        _ ≤ ∫ x in (Metric.closedBall (0 : X) R)ᶜ, 2 * ‖F i x‖ ^ 2 + 2 * ‖F j x‖ ^ 2 := by
          apply integral_mono (((hLp i).sub (hLp j)).norm.integrable_sq.integrableOn)
            ((hi.const_mul 2).add (hj.const_mul 2))
          intro x
          change ‖F i x - F j x‖ ^ 2 ≤ 2 * ‖F i x‖ ^ 2 + 2 * ‖F j x‖ ^ 2
          have h := norm_sub_le (F i x) (F j x)
          have hs := pow_le_pow_left₀ (norm_nonneg (F i x - F j x)) h 2
          nlinarith [sq_nonneg (‖F i x‖ - ‖F j x‖), norm_nonneg (F i x - F j x)]
        _ = _ := by rw [integral_add (hi.const_mul 2) (hj.const_mul 2),
          integral_const_mul, integral_const_mul]
    apply TotallyBounded.isCompact_of_isClosed _ isClosed_closure
    apply TotallyBounded.closure
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨R, hR, htailR⟩ := htail (ε ^ 2 / 16) (by positivity)
    let K := Metric.closedBall (0 : X) R
    let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : X) R)
    obtain ⟨C, hC, hbound, hlip⟩ := hlocal R hR
    let f (i : ι) : K →ᵇ V := BoundedContinuousFunction.mkOfCompact
      ⟨fun x ↦ F i x, (hF i).comp continuous_subtype_val⟩
    have hcompact : IsCompact (closure (range f)) := by
      apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : V) C)
        (isCompact_closedBall (0 : V) C)
      · rintro _ x ⟨i, rfl⟩
        simpa [Metric.mem_closedBall, dist_zero_right, f] using hbound i x x.property
      · intro x
        apply Metric.equicontinuousAt_iff.mpr
        intro ε hε
        refine ⟨ε / (C + 1), by positivity, ?_⟩
        intro y hy z
        obtain ⟨i, hi⟩ := z.property
        have h := hlip i x y x.property y.property
        have hxy : ‖(x : X) - y‖ < ε / (C + 1) := by
          change dist (y : X) (x : X) < ε / (C + 1) at hy
          rw [dist_eq_norm] at hy
          simpa only [norm_sub_rev] using hy
        have hz : (z : K →ᵇ V) = f i := hi.symm
        rw [hz]
        change dist (F i x) (F i y) < ε
        rw [dist_eq_norm]
        have hpos : 0 < C + 1 := by linarith
        have hmul := (lt_div_iff₀ hpos).mp hxy
        nlinarith [norm_nonneg ((x : X) - y)]
    let B := (volume K).toReal
    have hB : 0 ≤ B := ENNReal.toReal_nonneg
    let δ := ε / (2 * (B + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨t, ht, htfin, hcover⟩ :=
      exists_finite_cover_balls_of_isCompact_closure hcompact hδ
    have hex (z : t) : ∃ i, f i = z.val := ht z.property
    choose idx hidx using hex
    let : Finite t := htfin.to_subtype
    let centers := (fun z : t ↦ G (idx z)) '' (univ : Set t)
    refine ⟨centers, (Set.toFinite (univ : Set t)).image _, ?_⟩
    rintro _ ⟨i, rfl⟩
    obtain ⟨z, hz, hdist⟩ := mem_iUnion₂.mp (hcover (mem_range_self i))
    let j := idx ⟨z, hz⟩
    have hfj : f j = z := hidx ⟨z, hz⟩
    have hclose (x : X) (hx : x ∈ K) : ‖F i x - F j x‖ ≤ δ := by
      have h := BoundedContinuousFunction.dist_coe_le_dist (f := f i) (g := f j) (⟨x, hx⟩ : K)
      have hd : dist (f i) (f j) < δ := by simpa [hfj] using hdist
      have heval : ‖F i x - F j x‖ ≤ dist (f i) (f j) := by
        change dist (F i x) (F j x) ≤ dist (f i) (f j) at h
        simpa only [dist_eq_norm] using h
      exact heval.trans hd.le
    have hδbound : δ ^ 2 * B ≤ ε ^ 2 / 4 := by
      have heq : δ * (2 * (B + 1)) = ε := div_mul_cancel₀ ε (by positivity)
      have hsq := sq_nonneg B
      have heq2 := congrArg (fun x : ℝ ↦ x ^ 2) heq
      nlinarith [sq_nonneg δ, mul_nonneg (sq_nonneg δ) (by nlinarith : 0 ≤ B * B + B + 1)]
    have hnormbound : ‖G i - G j‖ ^ 2 ≤ ε ^ 2 / 2 := by
      rw [hnorm]
      have hint : Integrable (fun x ↦ ‖F i x - F j x‖ ^ 2) volume :=
        ((hLp i).sub (hLp j)).norm.integrable_sq
      rw [← integral_add_compl (s := Metric.closedBall (0 : X) R) measurableSet_closedBall hint]
      have hlo := hlow R i j δ hδ.le hclose
      have hhi := hhigh R i j
      have hti := htailR i
      have htj := htailR j
      dsimp [B, K] at hδbound
      linarith
    have hd : dist (G i) (G j) < ε := by
      rw [dist_eq_norm]
      nlinarith [sq_pos_of_pos hε, norm_nonneg (G i - G j)]
    apply mem_iUnion₂.mpr
    refine ⟨G j, ?_, hd⟩
    exact ⟨⟨z, hz⟩, mem_univ _, rfl⟩
  -- The specified intertwining identity fixes J and gives its uniform high-frequency tail.
  have inclusion_fourier_tail (n r : ℕ) (s t : ℝ) (hst : t < s)
      (J : Lp (EuclideanSpace ℂ (Fin r)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin r)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (hJ : ∀ f, besselRealization n r t (J f) = besselRealization n r s f) :
      (∀ f, (fun ξ : EuclideanSpace ℝ (Fin n) ↦ (𝓕 (J f)) ξ) =ᵐ[volume]
        fun ξ ↦ ((1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2) : ℝ) • (𝓕 f) ξ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ f, ‖f‖ ≤ 1 →
        ∫ ξ in (Metric.closedBall 0 R)ᶜ, ‖(𝓕 (J f)) ξ‖ ^ 2 ≤ ε) := by
    let X := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r)
    let g : X → ℂ := fun ξ ↦ ((1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2) : ℝ)
    have hg : g.HasTemperateGrowth := by
      dsimp [g]
      fun_prop
    have hg_le (ξ : X) : ‖g ξ‖ ≤ 1 := by
      dsimp [g]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg ‖ξ‖))
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hst.le) zero_le_two)
    let g' : BoundedContinuousFunction X ℂ :=
      BoundedContinuousFunction.ofNormedAddCommGroup g hg.1.continuous 1 hg_le
    have hgLp : MemLp g ⊤ (volume : Measure X) := g'.memLp_top
    let a : Lp ℂ ⊤ (volume : Measure X) := hgLp.toLp g
    -- The specified intertwining identity determines exactly the original Bessel multiplier.
    have hdist (f : Lp V 2 (volume : Measure X)) :
        (J f : 𝓢'(X, V)) = besselPotential X V (t - s) (f : 𝓢'(X, V)) := by
      have h := (besselPotential_neg_apply_eq_iff t (J f : 𝓢'(X, V))
        (besselRealization n r s f)).mp (hJ f)
      simpa only [besselRealization, ContinuousLinearMap.comp_apply,
        Lp.toTemperedDistributionCLM_apply, besselPotential_besselPotential_apply,
        neg_add_eq_sub] using h.symm
    have hfour (f : Lp V 2 (volume : Measure X)) : 𝓕 (J f) = a • 𝓕 f := by
      apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
      change ((𝓕 (J f) : Lp V 2 (volume : Measure X)) : 𝓢'(X, V)) =
        (a • 𝓕 f : Lp V 2 (volume : Measure X))
      rw [← Lp.fourier_toTemperedDistribution_eq, hdist, besselPotential,
        TemperedDistribution.fourierMultiplierCLM_apply,
        FourierTransform.fourier_fourierInv_eq, Lp.toTemperedDistribution_smul_eq hg hgLp,
        ← Lp.fourier_toTemperedDistribution_eq]
    have hae (f : Lp V 2 (volume : Measure X)) :
        (fun ξ : X ↦ (𝓕 (J f)) ξ) =ᵐ[volume]
          fun ξ ↦ ((1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2) : ℝ) • (𝓕 f) ξ := by
      rw [hfour]
      filter_upwards [Lp.coeFn_lpSMul (r := 2) a (𝓕 f), hgLp.coeFn_toLp] with ξ hξ ha
      change a ξ = g ξ at ha
      rw [hξ, Pi.smul_apply', ha]
      exact Complex.coe_smul _ _
    refine ⟨hae, ?_⟩
    intro ε hε
    have hdecay : Tendsto (fun q : ℝ ↦ q ^ ((t - s) / 2)) atTop (𝓝 0) := by
      simpa only [neg_neg] using
        (tendsto_rpow_neg_atTop (show 0 < -((t - s) / 2) by linarith))
    obtain ⟨A, hA⟩ := eventually_atTop.mp (hdecay (gt_mem_nhds (Real.sqrt_pos.mpr hε)))
    let R := max 1 A
    have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨R, hR, ?_⟩
    intro f hf
    -- The negative order difference forces uniformly small Fourier mass outside a large ball.
    have hbound : ∀ᵐ ξ ∂volume.restrict (Metric.closedBall (0 : X) R)ᶜ,
        ‖(𝓕 (J f) : Lp V 2 (volume : Measure X)) ξ‖ ^ 2 ≤
          ε * ‖(𝓕 f : Lp V 2 (volume : Measure X)) ξ‖ ^ 2 := by
      filter_upwards [ae_restrict_of_ae (hae f),
        ae_restrict_mem measurableSet_closedBall.compl] with ξ hξ hout
      have hnorm : R < ‖ξ‖ := by
        simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hout
      have hbase : A ≤ 1 + ‖ξ‖ ^ 2 := by
        have h1 : 1 ≤ R := le_max_left _ _
        have h2 : A ≤ R := le_max_right _ _
        nlinarith
      have hw : (1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2) < Real.sqrt ε :=
        hA (1 + ‖ξ‖ ^ 2) hbase
      have hw0 : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2) := Real.rpow_nonneg (by positivity) _
      have hwsq : ((1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2)) ^ 2 ≤ ε := by
        nlinarith [Real.sq_sqrt hε.le, Real.sqrt_nonneg ε]
      rw [hξ, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0, mul_pow]
      exact mul_le_mul_of_nonneg_right hwsq (sq_nonneg _)
    have hint := (Lp.memLp (𝓕 f : Lp V 2 (volume : Measure X))).norm.integrable_sq
    have hnormsq : ∫ ξ, ‖(𝓕 f : Lp V 2 (volume : Measure X)) ξ‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [← Lp.norm_fourier_eq (f := f), ← real_inner_self_eq_norm_sq, L2.inner_def]
      simp_rw [real_inner_self_eq_norm_sq]
      rfl
    calc
      _ ≤ ∫ ξ : X in (Metric.closedBall (0 : X) R)ᶜ,
          ε * ‖(𝓕 f : Lp V 2 (volume : Measure X)) ξ‖ ^ 2 :=
        integral_mono_ae
          (f := fun ξ : X ↦ ‖(𝓕 (J f) : Lp V 2 (volume : Measure X)) ξ‖ ^ 2)
          (g := fun ξ : X ↦ ε * ‖(𝓕 f : Lp V 2 (volume : Measure X)) ξ‖ ^ 2)
          (Lp.memLp (𝓕 (J f) : Lp V 2 (volume : Measure X))).norm.integrable_sq.integrableOn
          (hint.const_mul ε).integrableOn hbound
      _ = ε * ∫ ξ in (Metric.closedBall (0 : X) R)ᶜ, ‖(𝓕 f : Lp V 2 (volume : Measure X)) ξ‖ ^ 2 :=
        integral_const_mul _ _
      _ ≤ ε * ∫ ξ, ‖(𝓕 f : Lp V 2 (volume : Measure X)) ξ‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hε.le
        exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun ξ ↦ sq_nonneg _)
      _ = ε * ‖f‖ ^ 2 := by rw [hnormsq]
      _ ≤ ε := by
        have hs : ‖f‖ ^ 2 ≤ 1 := (sq_le_one_iff₀ (norm_nonneg f)).mpr hf
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hs hε.le
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r)
  let S : Set (Lp H 2 (volume : Measure V)) :=
    {f | ‖f‖ ≤ 1 ∧ IsSupportedIn (besselRealization n r s f) K}
  obtain ⟨T, hTc, hTlocal, hTae⟩ := exists_supported_fourier_representative r s K hK
  obtain ⟨hJae, htail⟩ := inclusion_fourier_tail n r s t hst J hJ
  let a : V → ℂ := fun x ↦ ((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ)
  have ha : a.HasTemperateGrowth := by dsimp [a]; fun_prop
  let F (f : S) (x : V) : H := a x • T x f.val
  have hFc (f : S) : Continuous (F f) :=
    ha.1.continuous.smul (hTc.clm_apply continuous_const)
  -- The same supported Fourier representative is the Fourier transform of the specified J.
  have hFae (f : S) : F f =ᵐ[volume]
      (fun x ↦ (𝓕 (J f.val) : Lp H 2 (volume : Measure V)) x) := by
    filter_upwards [hTae f.val f.property.2, hJae f.val] with x hx hJx
    change a x • T x f.val = (𝓕 (J f.val)) x
    rw [hx, hJx]
    dsimp [a]
    rw [smul_smul, ← Real.rpow_add (by positivity)]
    congr 2
    ring
  have hLp (f : S) : MemLp (F f) 2 volume :=
    (memLp_congr_ae (hFae f)).mpr (Lp.memLp (𝓕 (J f.val)))
  have hlocal : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 ≤ C ∧
      (∀ f : S, ∀ x ∈ Metric.closedBall 0 R, ‖F f x‖ ≤ C) ∧
      (∀ f : S, ∀ x y, x ∈ Metric.closedBall 0 R → y ∈ Metric.closedBall 0 R →
        ‖F f x - F f y‖ ≤ C * ‖x - y‖) := by
    intro R hR
    obtain ⟨C, hC, hnorm, hLip⟩ := temperate_smul_local_bounds a ha T hTlocal R hR.le
    refine ⟨C, hC, ?_, ?_⟩
    · intro f x hx
      exact hnorm f.val x f.property.1
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
    · intro f x y hx hy
      exact hLip f.val x y f.property.1
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)
  have hFtail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ f : S, ∫ x in (Metric.closedBall 0 R)ᶜ, ‖F f x‖ ^ 2 ≤ ε := by
    intro ε hε
    obtain ⟨R, hR, hbound⟩ := htail ε hε
    refine ⟨R, hR, ?_⟩
    intro f
    calc
      _ = ∫ x : V in (Metric.closedBall 0 R)ᶜ,
          ‖(𝓕 (J f.val) : Lp H 2 (volume : Measure V)) x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (hFae f)] with x hx
        rw [hx]
      _ ≤ ε := hbound f.val f.property.1
  have hcompact := l2_criterion (n := n) (r := r) (ι := S) F hFc hLp hlocal hFtail
  -- Fourier inversion transports the compact closure back to the original L2 coordinates.
  have hinverse := hcompact.image
    (FourierTransform.continuous_fourierInv : Continuous
      (fun g : Lp H 2 (volume : Measure V) ↦ 𝓕⁻ g))
  apply hinverse.of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ hinverse.isClosed
  rintro _ ⟨f, hf, rfl⟩
  let i : S := ⟨f, hf⟩
  have hcoord : (hLp i).toLp (F i) = 𝓕 (J f) := by
    apply Lp.ext
    exact (hLp i).coeFn_toLp.trans (hFae i)
  refine ⟨(hLp i).toLp (F i), subset_closure (mem_range_self i), ?_⟩
  rw [hcoord]
  exact FourierTransform.fourierInv_fourier_eq _

/-- Sobolev embedding, including the strict exponent and uniform derivative bounds. -/
theorem sobolev_embedding (n r k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r),
        ContDiff ℝ k u ∧
        (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          besselRealization n r s f φ = ∫ x, φ x • u x) ∧
        ∀ j : ℕ, j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ C * ‖f‖ := by
  /- Split the Fourier integrand into its weighted L² factor and the reciprocal weight.
  The stated strict inequality makes that weight square integrable, so Cauchy-Schwarz
  gives integrable Fourier moments through order k. Fourier inversion yields bounded
  continuous derivatives with the displayed estimate. Dominated differentiation proves
  ContDiff and the test identity. The critical endpoint is not covered by this estimate. -/
  -- The reciprocal Bessel weight is square integrable above half the dimension.
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let weight (a : ℝ) (ξ : X) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (-a / 2)
  have weight_pos (a : ℝ) (ξ : X) : 0 < weight a ξ := by
    exact Real.rpow_pos_of_pos (by positivity) _
  have weight_cont (a : ℝ) : Continuous (weight a) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const
      (fun ξ ↦ Or.inl (ne_of_gt (by positivity : 0 < (1 : ℝ) + ‖ξ‖ ^ 2)))
  have weight_mem (a : ℝ) (ha : (n : ℝ) < 2 * a) :
      MemLp (weight a) 2 (volume : Measure X) := by
    have hmeas : AEStronglyMeasurable (weight a) := by
      exact (weight_cont a).aestronglyMeasurable
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by simp) (by simp) hmeas]
    have h : ∫⁻ ξ : X, ENNReal.ofReal ‖(1 + ‖ξ‖ ^ 2) ^ (-a)‖ < ⊤ := by
      apply ((integrable_rpow_neg_one_add_norm_sq (by simpa [X] using ha)).congr _).lintegral_lt_top
      filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
      congr 1
      ring
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← enorm_pow]
    convert h using 1
    congr 2
    ext ξ
    dsimp [weight]
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 2
    ring
  -- Hölder and Plancherel give one bound for all required Fourier moments.
  have hW := weight_mem (s - k) (by linarith)
  let W : Lp ℝ 2 (volume : Measure X) := hW.toLp (weight (s - k))
  let c := 2 * Real.pi * ‖(innerSL ℝ : X →L[ℝ] X →L[ℝ] ℝ)‖
  refine ⟨(max c 1) ^ k * ‖W‖, by positivity, ?_⟩
  intro f
  let F : Lp V 2 (volume : Measure X) := 𝓕 f
  have hdom : Integrable (fun ξ : X ↦ weight (s - k) ξ * ‖F ξ‖) := by
    exact hW.integrable_mul (Lp.memLp F).norm
  have hdom_bound : (∫ ξ : X, weight (s - k) ξ * ‖F ξ‖) ≤ ‖W‖ * ‖f‖ := by
    let B : Lp ℝ 2 (volume : Measure X) := (Lp.memLp F).norm.toLp (fun ξ ↦ ‖F ξ‖)
    let H : Lp ℝ 1 (volume : Measure X) := W • B
    have heq : H =ᵐ[volume] fun ξ ↦ weight (s - k) ξ * ‖F ξ‖ := by
      filter_upwards [Lp.coeFn_lpSMul (r := 1) W B, hW.coeFn_toLp,
        (Lp.memLp F).norm.coeFn_toLp] with ξ hξ hWξ hFξ
      change H ξ = W ξ * B ξ at hξ
      rw [hWξ, hFξ] at hξ
      exact hξ
    calc
      _ = ‖H‖ := by
        rw [L1.norm_eq_integral_norm]
        apply integral_congr_ae
        filter_upwards [heq] with ξ hξ
        rw [hξ, Real.norm_of_nonneg (by positivity)]
      _ ≤ ‖W‖ * ‖B‖ := Lp.norm_smul_le W B
      _ = ‖W‖ * ‖f‖ := by
        have hB : ‖B‖ = ‖F‖ := by
          rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable F), ← Lp.norm_def]
        rw [hB, Lp.norm_fourier_eq]
  -- The loss of k derivatives is absorbed into the same integrable weight.
  have hmoment (j : ℕ) (hj : j ≤ k) (ξ : X) :
      ‖ξ‖ ^ j * weight s ξ ≤ weight (s - k) ξ := by
    have hbase : 1 ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
    have hnorm : ‖ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖ξ‖])
    calc
      _ ≤ ((1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ)) ^ j * weight s ξ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm j)
          (weight_pos _ _).le
      _ = (1 + ‖ξ‖ ^ 2) ^ (((j : ℝ) - s) / 2) := by
        dsimp [weight]
        rw [← Real.rpow_mul_natCast (by positivity), ← Real.rpow_add (by positivity)]
        congr 1
        ring
      _ ≤ weight (s - k) ξ := by
        apply Real.rpow_le_rpow_of_exponent_le hbase
        have hjreal : (j : ℝ) ≤ k := by exact_mod_cast hj
        linarith
  -- Differentiate the actual inverse Fourier integral through order k.
  let g : X → V := fun ξ ↦ weight s ξ • F ξ
  have hg_meas : AEStronglyMeasurable g :=
    (weight_cont s).aestronglyMeasurable.smul (Lp.aestronglyMeasurable F)
  have hg_mom (j : ℕ) (hj : j ≤ k) : Integrable (fun ξ : X ↦ ‖ξ‖ ^ j * ‖g ξ‖) := by
    apply hdom.mono'
    · exact (continuous_norm.pow j).aestronglyMeasurable.mul hg_meas.norm
    · filter_upwards with ξ
      dsimp [g]
      rw [norm_smul, Real.norm_of_nonneg (weight_pos _ _).le]
      rw [← mul_assoc, abs_of_nonneg (by
        exact mul_nonneg (mul_nonneg (pow_nonneg (norm_nonneg ξ) j)
          (weight_pos _ _).le) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hmoment j hj ξ) (norm_nonneg _)
  have hg_int : Integrable g := (integrable_norm_iff hg_meas).mp
    (by simpa only [pow_zero, one_mul] using hg_mom 0 (Nat.zero_le k))
  let L : X →L[ℝ] X →L[ℝ] ℝ := -(innerSL ℝ)
  let u : X → V := VectorFourier.fourierIntegral Real.fourierChar volume L.toLinearMap₁₂ g
  have hu : ContDiff ℝ k u := by
    exact VectorFourier.contDiff_fourierIntegral L
      (fun j hj ↦ hg_mom j (by exact_mod_cast hj))
  refine ⟨u, hu, ?_, ?_⟩
  · intro φ
    -- Identify this function with the original Bessel distribution, using Fubini.
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hws := weight_mem s (by linarith)
    have hwsC : MemLp (fun ξ : X ↦ (weight s ξ : ℂ)) 2 volume := hws.ofReal
    have htemp : (fun ξ : X ↦ (weight s ξ : ℂ)).HasTemperateGrowth := by
      dsimp [weight]
      fun_prop
    let G : Lp V 1 (volume : Measure X) := hwsC.toLp (fun ξ ↦ (weight s ξ : ℂ)) • F
    have hG : G =ᵐ[volume] g := by
      filter_upwards [Lp.coeFn_lpSMul (r := 1) (hwsC.toLp _) F,
        hwsC.coeFn_toLp] with ξ hξ hwsξ
      change G ξ = (hwsC.toLp _ : Lp ℂ 2 volume) ξ • F ξ at hξ
      rw [hwsξ] at hξ
      simpa only [g, Complex.coe_smul] using hξ
    have hdist : (G : 𝓢'(X, V)) =
        smulLeftCLM V (fun ξ : X ↦ (weight s ξ : ℂ)) (𝓕 (f : 𝓢'(X, V))) := by
      rw [Lp.fourier_toTemperedDistribution_eq]
      exact Lp.toTemperedDistribution_smul_eq htemp hwsC F
    have hrepr : besselRealization n r s f = 𝓕⁻ (G : 𝓢'(X, V)) := by
      rw [hdist]
      rfl
    have hLflip : L.toLinearMap₁₂.flip = L.toLinearMap₁₂ := by
      ext x y
      change -inner ℝ y x = -inner ℝ x y
      exact congrArg Neg.neg (real_inner_comm x y)
    rw [hrepr, TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
    change (∫ ξ : X, (𝓕⁻ φ) ξ • G ξ) = ∫ x : X, φ x • u x
    calc
      _ = ∫ ξ : X, (𝓕⁻ φ) ξ • g ξ := by
        apply integral_congr_ae
        filter_upwards [hG] with ξ hξ
        rw [hξ]
      _ = ∫ x : X, φ x • u x := by
        convert VectorFourier.integral_fourierIntegral_smul_eq_flip
          (e := Real.fourierChar) (L := L.toLinearMap₁₂)
          (f := (φ : X → ℂ)) (g := g) (μ := volume) (ν := volume)
          Real.continuous_fourierChar
          (by change Continuous (fun p : X × X ↦ L p.1 p.2); fun_prop)
          φ.integrable hg_int using 1
        · rw [SchwartzMap.fourierInv_coe]
          rfl
        · rw [hLflip]
  · intro j hj x
    -- Every derivative has the same Hölder bound, up to the fixed Fourier constants.
    have hderiv := VectorFourier.iteratedFDeriv_fourierIntegral L
      (N := (k : ℕ∞)) (fun i hi ↦ hg_mom i (by exact_mod_cast hi)) hg_meas
      (n := j) (by exact_mod_cast hj)
    rw [congrFun hderiv x]
    calc
      _ ≤ ∫ ξ : X, ‖VectorFourier.fourierPowSMulRight L g ξ j‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      _ ≤ (max c 1) ^ k * ∫ ξ : X, weight (s - k) ξ * ‖F ξ‖ := by
        rw [← integral_const_mul]
        apply integral_mono_of_nonneg
        · filter_upwards with ξ
          exact norm_nonneg _
        · exact hdom.const_mul _
        · filter_upwards with ξ
          calc
            _ ≤ (2 * Real.pi * ‖L‖) ^ j * ‖ξ‖ ^ j * ‖g ξ‖ :=
              VectorFourier.norm_fourierPowSMulRight_le L g ξ j
            _ ≤ (max c 1) ^ k * (weight (s - k) ξ * ‖F ξ‖) := by
              dsimp [g]
              rw [norm_smul, Real.norm_of_nonneg (weight_pos _ _).le]
              have hc : (2 * Real.pi * ‖L‖) ^ j ≤ (max c 1) ^ k := by
                have hcc : 2 * Real.pi * ‖L‖ = c := by
                  dsimp [L, c]
                  rw [ContinuousLinearMap.opNorm_neg]
                rw [hcc]
                exact (pow_le_pow_left₀ (by positivity) (le_max_left c 1) j).trans
                  (pow_le_pow_right₀ (le_max_right c 1) hj)
              calc
                _ = ((2 * Real.pi * ‖L‖) ^ j * (‖ξ‖ ^ j * weight s ξ)) * ‖F ξ‖ := by ring
                _ ≤ ((max c 1) ^ k * weight (s - k) ξ) * ‖F ξ‖ := by
                  gcongr
                  exact hmoment j hj ξ
                _ = _ := by ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hdom_bound
          (pow_nonneg (le_trans zero_le_one (le_max_right c 1)) k)
        simpa only [mul_assoc] using h


end AtiyahSinger
