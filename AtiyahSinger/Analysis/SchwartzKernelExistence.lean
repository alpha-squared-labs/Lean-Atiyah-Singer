/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzTensorDensity

import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Quantitative estimates for continuous Schwartz kernel extension

Public module ID: M0946.

Joint continuity of an original bilinear test pairing supplies finite Schwartz
seminorm bounds. These bounds are the input to a controlled windowed Fourier
extension; tensor density alone supplies uniqueness and is not used as an
existence assertion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option backward.isDefEq.respectTransparency false

attribute [local instance 2000] NormedField.toNormedCommRing Real.normedCommRing

open Filter Set Topology
open scoped ContDiff SchwartzMap

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

/-- Jointly continuous Schwartz bilinear forms are bounded by a product of two
finite collections of the original Schwartz seminorms. The collections can be
chosen to contain the zeroth seminorm, so their common kernels are trivial. -/
theorem exists_schwartz_bilinear_seminorm_bound
    (b : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) →ₗ[ℂ] ℂ)
    (hb : Continuous (fun z : 𝓢(V, ℂ) × 𝓢(V, ℂ) ↦ b z.1 z.2)) :
    ∃ s t : Finset (ℕ × ℕ), (0, 0) ∈ s ∧ (0, 0) ∈ t ∧
      ∃ C : ℝ, 0 < C ∧ ∀ φ ψ : 𝓢(V, ℂ),
        ‖b φ ψ‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ V ℂ)) φ *
          (t.sup (schwartzSeminormFamily ℂ V ℂ)) ψ := by
  classical
  let p := schwartzSeminormFamily ℂ V ℂ
  -- The inverse image of the unit ball contains two finite-seminorm balls.
  have hnear : {z : 𝓢(V, ℂ) × 𝓢(V, ℂ) | ‖b z.1 z.2‖ < 1} ∈ 𝓝 (0, 0) :=
    (isOpen_lt hb.norm continuous_const).mem_nhds (by simp)
  rw [nhds_prod_eq] at hnear
  obtain ⟨U, hU, W, hW, hUW⟩ := Filter.mem_prod_iff.mp hnear
  obtain ⟨s, ε, hε, hs⟩ := (schwartz_withSeminorms ℂ V ℂ).mem_nhds_iff 0 U |>.mp hU
  obtain ⟨t, δ, hδ, ht⟩ := (schwartz_withSeminorms ℂ V ℂ).mem_nhds_iff 0 W |>.mp hW
  let S := insert (0, 0) s
  let T := insert (0, 0) t
  let q := S.sup p
  let r := T.sup p
  have hlocal (φ ψ : 𝓢(V, ℂ)) (hφ : q φ < ε) (hψ : r ψ < δ) : ‖b φ ψ‖ < 1 := by
    change (φ, ψ) ∈ {z : 𝓢(V, ℂ) × 𝓢(V, ℂ) | ‖b z.1 z.2‖ < 1}
    apply hUW
    constructor
    · apply hs
      apply (s.sup p).mem_ball_zero.mpr
      exact lt_of_le_of_lt
        ((Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert (0, 0) s))) φ) hφ
    · apply ht
      apply (t.sup p).mem_ball_zero.mpr
      exact lt_of_le_of_lt
        ((Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert (0, 0) t))) ψ) hψ
  -- The zeroth seminorm makes normalization legitimate for every nonzero test.
  have hpos (v : Finset (ℕ × ℕ)) (hv : (0, 0) ∈ v) (φ : 𝓢(V, ℂ)) (hφ : φ ≠ 0) :
      0 < (v.sup p) φ := by
    by_contra h
    have hzero : (v.sup p) φ = 0 := le_antisymm (le_of_not_gt h) (apply_nonneg _ _)
    apply hφ
    apply SchwartzMap.ext
    intro x
    have hbound : ‖φ x‖ ≤ (v.sup p) φ := by
      calc
        _ ≤ SchwartzMap.seminorm ℂ 0 0 φ := by
          simpa only [norm_iteratedFDeriv_zero] using
            SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ 0 x
        _ ≤ _ := by
          change p (0, 0) φ ≤ (v.sup p) φ
          exact Seminorm.le_finset_sup_apply hv
    rw [hzero] at hbound
    exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
  refine ⟨S, T, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _,
    4 / (ε * δ), by positivity, ?_⟩
  intro φ ψ
  by_cases hφ : φ = 0
  · simp [hφ]
  by_cases hψ : ψ = 0
  · simp [hψ]
  have hq : 0 < q φ := hpos S (Finset.mem_insert_self _ _) φ hφ
  have hr : 0 < r ψ := hpos T (Finset.mem_insert_self _ _) ψ hψ
  let a : ℂ := (ε / (2 * q φ) : ℝ)
  let c : ℂ := (δ / (2 * r ψ) : ℝ)
  have ha : ‖a‖ = ε / (2 * q φ) := by
    change ‖(↑(ε / (2 * q φ)) : ℂ)‖ = ε / (2 * q φ)
    rw [Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  have hc : ‖c‖ = δ / (2 * r ψ) := by
    change ‖(↑(δ / (2 * r ψ)) : ℂ)‖ = δ / (2 * r ψ)
    rw [Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  have haq : q (a • φ) < ε := by
    rw [map_smul_eq_mul, ha]
    have heq : ε / (2 * q φ) * q φ = ε / 2 := by field_simp
    rw [heq]
    exact half_lt_self hε
  have hcr : r (c • ψ) < δ := by
    rw [map_smul_eq_mul, hc]
    have heq : δ / (2 * r ψ) * r ψ = δ / 2 := by field_simp
    rw [heq]
    exact half_lt_self hδ
  have hsmall := hlocal (a • φ) (c • ψ) haq hcr
  -- Undo both scalar normalizations using the original bilinearity.
  have hscale : ‖b (a • φ) (c • ψ)‖ =
      (ε / (2 * q φ)) * (δ / (2 * r ψ)) * ‖b φ ψ‖ := by
    rw [b.map_smul a φ, LinearMap.smul_apply, (b φ).map_smul c ψ,
      norm_smul, norm_smul, ha, hc, mul_assoc]
  have hrecover : ‖b φ ψ‖ =
      (4 / (ε * δ) * q φ * r ψ) * ‖b (a • φ) (c • ψ)‖ := by
    rw [hscale]
    field_simp
    ring
  change ‖b φ ψ‖ ≤ 4 / (ε * δ) * q φ * r ψ
  rw [hrecover]
  exact mul_le_of_le_one_right (by positivity) hsmall.le

/-- Translation has polynomial growth in each original Schwartz seminorm.
Only the spatial weight changes; all derivative orders are retained exactly. -/
theorem seminorm_compSubConstCLM_le (φ : 𝓢(V, ℂ)) (a : V) (k j : ℕ) :
    SchwartzMap.seminorm ℂ k j (SchwartzMap.compSubConstCLM ℂ a φ) ≤
      2 ^ k * (SchwartzMap.seminorm ℂ k j φ + SchwartzMap.seminorm ℂ 0 j φ) *
        (1 + ‖a‖) ^ k := by
  apply SchwartzMap.seminorm_le_bound ℂ k j _ (by positivity)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (fun y ↦ φ (y - a)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub]
  -- Split the old spatial weight between the translated variable and the shift.
  have hweight : ‖x‖ ^ k ≤ 2 ^ k * (‖x - a‖ ^ k + ‖a‖ ^ k) := by
    calc
      _ ≤ (‖x - a‖ + ‖a‖) ^ k := by
        gcongr
        simpa only [sub_add_cancel] using norm_add_le (x - a) a
      _ ≤ 2 ^ (k - 1) * (‖x - a‖ ^ k + ‖a‖ ^ k) :=
        add_pow_le (norm_nonneg _) (norm_nonneg _) k
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (Nat.sub_le k 1)) (by positivity)
  have hlarge : 1 ≤ (1 + ‖a‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg a])
  have ha : ‖a‖ ^ k ≤ (1 + ‖a‖) ^ k := by gcongr; linarith
  calc
    _ ≤ (2 ^ k * (‖x - a‖ ^ k + ‖a‖ ^ k)) *
        ‖iteratedFDeriv ℝ j φ (x - a)‖ := by gcongr
    _ = 2 ^ k * (‖x - a‖ ^ k * ‖iteratedFDeriv ℝ j φ (x - a)‖ +
        ‖a‖ ^ k * ‖iteratedFDeriv ℝ j φ (x - a)‖) := by ring
    _ ≤ 2 ^ k * (SchwartzMap.seminorm ℂ k j φ +
        ‖a‖ ^ k * SchwartzMap.seminorm ℂ 0 j φ) := by
      gcongr
      · exact SchwartzMap.le_seminorm ℂ k j φ (x - a)
      · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ j (x - a)
    _ ≤ 2 ^ k * ((1 + ‖a‖) ^ k * SchwartzMap.seminorm ℂ k j φ +
        (1 + ‖a‖) ^ k * SchwartzMap.seminorm ℂ 0 j φ) := by
      gcongr
      exact le_mul_of_one_le_left (apply_nonneg _ _) hlarge
    _ = _ := by ring

/-- Every continuous Schwartz seminorm grows at most polynomially along a translation orbit.
This permits later Fourier changes of variables without discarding weighted derivatives. -/
theorem exists_schwartz_translation_seminorm_bound
    (p : Seminorm ℂ 𝓢(V, ℂ)) (hp : Continuous p) (φ : 𝓢(V, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ a : V,
      p (SchwartzMap.compSubConstCLM ℂ a φ) ≤ C * (1 + ‖a‖) ^ N := by
  classical
  obtain ⟨s, C, _, hbound⟩ :=
    Seminorm.bound_sum_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  let c (i : ℕ × ℕ) := 2 ^ i.1 *
    (SchwartzMap.seminorm ℂ i.1 i.2 φ + SchwartzMap.seminorm ℂ 0 i.2 φ)
  let N := s.sup Prod.fst
  refine ⟨(C : ℝ) * ∑ i ∈ s, c i, by positivity, N, ?_⟩
  intro a
  have hsum : p (SchwartzMap.compSubConstCLM ℂ a φ) ≤
      (C : ℝ) * ∑ i ∈ s,
        SchwartzMap.seminorm ℂ i.1 i.2 (SchwartzMap.compSubConstCLM ℂ a φ) := by
    simpa only [smul_apply, sum_apply, NNReal.smul_def, smul_eq_mul,
      schwartzSeminormFamily] using
        Seminorm.le_def.mp hbound (SchwartzMap.compSubConstCLM ℂ a φ)
  calc
    _ ≤ (C : ℝ) * ∑ i ∈ s, c i * (1 + ‖a‖) ^ N := by
      apply hsum.trans
      gcongr with i hi
      apply (seminorm_compSubConstCLM_le φ a i.1 i.2).trans
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact pow_le_pow_right₀ (by linarith [norm_nonneg a]) (Finset.le_sup hi)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- A translated and modulated Schwartz window has polynomial growth in every
continuous Schwartz seminorm. Fourier translation provides the modulation,
while all continuity bounds retain the original spatial weights and derivatives. -/
theorem exists_schwartz_modulation_translation_seminorm_bound
    (p : Seminorm ℂ 𝓢(V, ℂ)) (hp : Continuous p) (φ : 𝓢(V, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ a ξ : V,
      p (FourierTransform.fourierInv
        (SchwartzMap.compSubConstCLM ℂ ξ
          (FourierTransform.fourier (SchwartzMap.compSubConstCLM ℂ a φ)))) ≤
        C * (1 + ‖a‖ + ‖ξ‖) ^ N := by
  classical
  let L : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := FourierTransform.fourierCLM ℂ 𝓢(V, ℂ)
  let R : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := FourierTransform.fourierInvCLM ℂ 𝓢(V, ℂ)
  let q := p.comp R.toLinearMap
  have hq : Continuous q := hp.comp R.continuous
  obtain ⟨s, C, _, hbound⟩ :=
    Seminorm.bound_sum_of_continuous (schwartz_withSeminorms ℂ V ℂ) q hq
  let qj (i : ℕ × ℕ) : Seminorm ℂ 𝓢(V, ℂ) :=
    (SchwartzMap.seminorm ℂ i.1 i.2 + SchwartzMap.seminorm ℂ 0 i.2).comp L.toLinearMap
  have hqj (i : ℕ × ℕ) : Continuous (qj i) :=
    (((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i).add
      ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (0, i.2))).comp L.continuous
  choose c hc N hN using fun i : ℕ × ℕ ↦
    exists_schwartz_translation_seminorm_bound (qj i) (hqj i) φ
  let D := s.sup (fun i ↦ N i + i.1)
  refine ⟨(C : ℝ) * ∑ i ∈ s, 2 ^ i.1 * c i, ?_, D, ?_⟩
  · exact mul_nonneg C.coe_nonneg
      (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (by positivity) (hc i)))
  intro a ξ
  let f := L (SchwartzMap.compSubConstCLM ℂ a φ)
  have hsum : p (R (SchwartzMap.compSubConstCLM ℂ ξ f)) ≤
      (C : ℝ) * ∑ i ∈ s,
        SchwartzMap.seminorm ℂ i.1 i.2 (SchwartzMap.compSubConstCLM ℂ ξ f) := by
    change p (R.toLinearMap (SchwartzMap.compSubConstCLM ℂ ξ f)) ≤ _
    simpa only [q, Seminorm.comp_apply, smul_apply, sum_apply, NNReal.smul_def,
      smul_eq_mul, schwartzSeminormFamily] using
        Seminorm.le_def.mp hbound (SchwartzMap.compSubConstCLM ℂ ξ f)
  change p (R (SchwartzMap.compSubConstCLM ℂ ξ f)) ≤ _
  calc
    _ ≤ (C : ℝ) * ∑ i ∈ s, (2 ^ i.1 * c i) * (1 + ‖a‖ + ‖ξ‖) ^ D := by
      apply hsum.trans
      apply mul_le_mul_of_nonneg_left ?_ C.coe_nonneg
      apply Finset.sum_le_sum
      intro i hi
      have hci := hc i
      have hdegree : N i + i.1 ≤ D := Finset.le_sup (f := fun i ↦ N i + i.1) hi
      calc
        _ ≤ 2 ^ i.1 * (SchwartzMap.seminorm ℂ i.1 i.2 f +
            SchwartzMap.seminorm ℂ 0 i.2 f) * (1 + ‖ξ‖) ^ i.1 :=
          seminorm_compSubConstCLM_le f ξ i.1 i.2
        _ ≤ 2 ^ i.1 * (c i * (1 + ‖a‖) ^ N i) * (1 + ‖ξ‖) ^ i.1 := by
          gcongr
          exact hN i a
        _ ≤ 2 ^ i.1 * (c i * (1 + ‖a‖ + ‖ξ‖) ^ N i) *
            (1 + ‖a‖ + ‖ξ‖) ^ i.1 := by
          have haP : (1 + ‖a‖) ^ N i ≤ (1 + ‖a‖ + ‖ξ‖) ^ N i :=
            pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg ξ]) _
          have hξP : (1 + ‖ξ‖) ^ i.1 ≤ (1 + ‖a‖ + ‖ξ‖) ^ i.1 :=
            pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg a]) _
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left haP hci) (by positivity))
            hξP (by positivity) (by positivity)
        _ = (2 ^ i.1 * c i) * (1 + ‖a‖ + ‖ξ‖) ^ (N i + i.1) := by
          rw [pow_add]
          ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_right₀ (by linarith [norm_nonneg a, norm_nonneg ξ]) hdegree
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Windowing by a translated Schwartz test decays rapidly in the translation parameter.
The estimate simultaneously retains any prescribed spatial weight and derivative
order, and controls the result by finitely many original seminorms of both factors. -/
theorem seminorm_pairing_compSubConstCLM_decay (f g : 𝓢(V, ℂ)) (a : V) (k j M : ℕ) :
    (1 + ‖a‖) ^ M * SchwartzMap.seminorm ℂ k j
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f
        (SchwartzMap.compSubConstCLM ℂ a g)) ≤
      2 ^ (M + M) * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ((SchwartzMap.seminorm ℂ k i f + SchwartzMap.seminorm ℂ (k + M) i f) *
          (SchwartzMap.seminorm ℂ 0 (j - i) g + SchwartzMap.seminorm ℂ M (j - i) g)) := by
  let A := (1 + ‖a‖) ^ M
  let C := 2 ^ (M + M) * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
    ((SchwartzMap.seminorm ℂ k i f + SchwartzMap.seminorm ℂ (k + M) i f) *
      (SchwartzMap.seminorm ℂ 0 (j - i) g + SchwartzMap.seminorm ℂ M (j - i) g))
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpower (r : ℝ) (hr : 0 ≤ r) : (1 + r) ^ M ≤ 2 ^ M * (1 + r ^ M) := by
    calc
      _ ≤ 2 ^ (M - 1) * (1 ^ M + r ^ M) := add_pow_le zero_le_one hr M
      _ ≤ _ := by
        rw [one_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (Nat.sub_le M 1)) (by positivity)
  have hweight (x : V) : A ≤
      2 ^ (M + M) * (1 + ‖x‖ ^ M) * (1 + ‖x - a‖ ^ M) := by
    have hnorm : ‖a‖ ≤ ‖x‖ + ‖x - a‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le x (x - a)
    have hbase : 1 + ‖a‖ ≤ (1 + ‖x‖) * (1 + ‖x - a‖) := by
      nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg (x - a))]
    calc
      _ ≤ ((1 + ‖x‖) * (1 + ‖x - a‖)) ^ M := by dsimp [A]; gcongr
      _ = (1 + ‖x‖) ^ M * (1 + ‖x - a‖) ^ M := mul_pow _ _ _
      _ ≤ (2 ^ M * (1 + ‖x‖ ^ M)) * (2 ^ M * (1 + ‖x - a‖ ^ M)) := by
        exact mul_le_mul (hpower _ (norm_nonneg _)) (hpower _ (norm_nonneg _))
          (by positivity) (by positivity)
      _ = _ := by rw [pow_add]; ring
  let u := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f
    (SchwartzMap.compSubConstCLM ℂ a g)
  have hbound : SchwartzMap.seminorm ℂ k j u ≤ C / A := by
    apply SchwartzMap.seminorm_le_bound ℂ k j u (div_nonneg hC hA.le)
    intro x
    apply (le_div_iff₀ hA).mpr
    have hderiv : ‖iteratedFDeriv ℝ j u x‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g (x - a)‖ := by
      have h := norm_iteratedFDeriv_mul_le (f.smooth ⊤)
        ((SchwartzMap.compSubConstCLM ℂ a g).smooth ⊤) x (show (j : ℕ∞ω) ≤ ∞ by simp)
      change ‖iteratedFDeriv ℝ j (fun y ↦ f y * g (y - a)) x‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (j - i) (fun y ↦ g (y - a)) x‖ at h
      simp_rw [iteratedFDeriv_comp_sub] at h
      exact h
    have hterm (i : ℕ) :
        A * ‖x‖ ^ k * ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (j - i) g (x - a)‖ ≤
          2 ^ (M + M) *
            ((SchwartzMap.seminorm ℂ k i f + SchwartzMap.seminorm ℂ (k + M) i f) *
              (SchwartzMap.seminorm ℂ 0 (j - i) g +
                SchwartzMap.seminorm ℂ M (j - i) g)) := by
      calc
        _ ≤ (2 ^ (M + M) * (1 + ‖x‖ ^ M) * (1 + ‖x - a‖ ^ M)) *
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ i f x‖ *
              ‖iteratedFDeriv ℝ (j - i) g (x - a)‖ := by gcongr; exact hweight x
        _ = 2 ^ (M + M) *
            ((‖x‖ ^ k * ‖iteratedFDeriv ℝ i f x‖ +
              ‖x‖ ^ (k + M) * ‖iteratedFDeriv ℝ i f x‖) *
              (‖iteratedFDeriv ℝ (j - i) g (x - a)‖ +
                ‖x - a‖ ^ M * ‖iteratedFDeriv ℝ (j - i) g (x - a)‖)) := by
          rw [pow_add]
          ring
        _ ≤ _ := by
          gcongr
          · exact SchwartzMap.le_seminorm ℂ k i f x
          · exact SchwartzMap.le_seminorm ℂ (k + M) i f x
          · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ g (j - i) (x - a)
          · exact SchwartzMap.le_seminorm ℂ M (j - i) g (x - a)
    calc
      _ = (A * ‖x‖ ^ k) * ‖iteratedFDeriv ℝ j u x‖ := by ring
      _ ≤ (A * ‖x‖ ^ k) * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g (x - a)‖ := by gcongr
      _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (A * ‖x‖ ^ k * ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (j - i) g (x - a)‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (2 ^ (M + M) *
            ((SchwartzMap.seminorm ℂ k i f + SchwartzMap.seminorm ℂ (k + M) i f) *
              (SchwartzMap.seminorm ℂ 0 (j - i) g +
                SchwartzMap.seminorm ℂ M (j - i) g))) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hterm i) (Nat.cast_nonneg _)
      _ = C := by
        dsimp [C]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  change A * SchwartzMap.seminorm ℂ k j u ≤ C
  rw [mul_comm]
  exact (le_div_iff₀ hA).mp hbound

/-- Rapid decay of windowed tests is uniform for every continuous Schwartz seminorm,
with a single continuous seminorm of the original input controlling the whole family. -/
theorem exists_schwartz_window_decay_seminorm
    (p : Seminorm ℂ 𝓢(V, ℂ)) (hp : Continuous p) (g : 𝓢(V, ℂ)) (M : ℕ) :
    ∃ q : Seminorm ℂ 𝓢(V, ℂ), Continuous q ∧ ∀ f : 𝓢(V, ℂ), ∀ a : V,
      (1 + ‖a‖) ^ M * p
        (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f
          (SchwartzMap.compSubConstCLM ℂ a g)) ≤ q f := by
  classical
  have hcont (k j : ℕ) : Continuous (SchwartzMap.seminorm ℂ k j : 𝓢(V, ℂ) → ℝ) :=
    (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, j)
  apply Seminorm.induction_add_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    (motive := fun p ↦ ∃ q : Seminorm ℂ 𝓢(V, ℂ), Continuous q ∧
      ∀ f : 𝓢(V, ℂ), ∀ a : V, (1 + ‖a‖) ^ M * p
        (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f
          (SchwartzMap.compSubConstCLM ℂ a g)) ≤ q f) ?_ ?_ ?_ ?_ ?_ hp
  · rintro ⟨k, j⟩
    let c (i : ℕ) : NNReal := ⟨2 ^ (M + M) * (j.choose i : ℝ) *
      (SchwartzMap.seminorm ℂ 0 (j - i) g + SchwartzMap.seminorm ℂ M (j - i) g),
      by positivity⟩
    let q : Seminorm ℂ 𝓢(V, ℂ) := ∑ i ∈ Finset.range (j + 1),
      c i • (SchwartzMap.seminorm ℂ k i + SchwartzMap.seminorm ℂ (k + M) i)
    refine ⟨q, ?_, ?_⟩
    · change Continuous (fun f : 𝓢(V, ℂ) ↦ q f)
      simp only [q, sum_apply, smul_apply, add_apply, NNReal.smul_def, smul_eq_mul]
      exact continuous_finsetSum _ (fun i _ ↦
        continuous_const.mul ((hcont k i).add (hcont (k + M) i)))
    · intro f a
      have hq : q f = 2 ^ (M + M) *
          ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            ((SchwartzMap.seminorm ℂ k i f + SchwartzMap.seminorm ℂ (k + M) i f) *
              (SchwartzMap.seminorm ℂ 0 (j - i) g +
                SchwartzMap.seminorm ℂ M (j - i) g)) := by
        simp only [q, sum_apply, smul_apply, add_apply, NNReal.smul_def, smul_eq_mul,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        change (2 ^ (M + M) * (j.choose i : ℝ) *
          (SchwartzMap.seminorm ℂ 0 (j - i) g + SchwartzMap.seminorm ℂ M (j - i) g)) *
            (SchwartzMap.seminorm ℂ k i f + SchwartzMap.seminorm ℂ (k + M) i f) = _
        ring
      rw [hq]
      exact seminorm_pairing_compSubConstCLM_decay f g a k j M
  · refine ⟨0, continuous_const, ?_⟩
    intro f a
    simp
  · rintro r s ⟨q, hq, hr⟩ ⟨v, hv, hs⟩
    refine ⟨q + v, hq.add hv, ?_⟩
    intro f a
    simp only [add_apply, mul_add]
    exact add_le_add (hr f a) (hs f a)
  · rintro r s hrs ⟨q, hq, hs⟩
    refine ⟨q, hq, ?_⟩
    intro f a
    exact (mul_le_mul_of_nonneg_left (Seminorm.le_def.mp hrs _) (by positivity)).trans (hs f a)
  · rintro r C ⟨q, hq, hr⟩
    refine ⟨C • q, hq.const_smul C, ?_⟩
    intro f a
    simp only [smul_apply, NNReal.smul_def, smul_eq_mul]
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hr f a) C.coe_nonneg

/-- Inverse Fourier translation gives the literal scalar plane-wave modulation. -/
theorem fourierInv_compSubConstCLM_fourier_apply (f : 𝓢(V, ℂ)) (ξ x : V) :
    FourierTransform.fourierInv
        (SchwartzMap.compSubConstCLM ℂ ξ (FourierTransform.fourier f)) x =
      (Real.fourierChar (inner ℝ ξ x) : ℂ) * f x := by
  open FourierTransform in
  have hshift := congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar MeasureTheory.volume
      (-innerₗ V) ((𝓕 f : 𝓢(V, ℂ)) : V → ℂ) (-ξ)) x
  have hinverse : (FourierTransform.fourierInv
      (FourierTransform.fourier f) : 𝓢(V, ℂ)) = f :=
    FourierTransform.fourierInv_fourier_eq f
  rw [SchwartzMap.fourierInv_coe]
  change VectorFourier.fourierIntegral Real.fourierChar MeasureTheory.volume
    (-innerₗ V) (fun y ↦ (FourierTransform.fourier f : 𝓢(V, ℂ)) (y - ξ)) x = _
  rw [show (fun y : V ↦ (FourierTransform.fourier f : 𝓢(V, ℂ)) (y - ξ)) =
      ((FourierTransform.fourier f : 𝓢(V, ℂ)) : V → ℂ) ∘ (fun y ↦ y + -ξ) by rfl, hshift]
  have hInvx : VectorFourier.fourierIntegral Real.fourierChar MeasureTheory.volume
      (-innerₗ V) ((FourierTransform.fourier f : 𝓢(V, ℂ)) : V → ℂ) x = f x := by
    have h := congrArg (fun u : 𝓢(V, ℂ) ↦ u x) hinverse
    rw [SchwartzMap.fourierInv_coe] at h
    exact h
  rw [hInvx]
  change Real.fourierChar (-inner ℝ (-ξ) x) • f x = _
  rw [inner_neg_left, neg_neg]
  rfl

/-- Joint continuity of all spatial jets on a common compact support gives
continuity in the full Schwartz topology, for an arbitrary parameter space. -/
theorem continuous_schwartzMap_of_common_compact_support
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {Y : Type*} [TopologicalSpace Y] (F : Y → 𝓢(D, ℂ))
    (K : Set D) (hK : IsCompact K) (hF : ∀ y, tsupport (F y) ⊆ K)
    (hjets : ∀ j : ℕ, Continuous (fun p : Y × D ↦ iteratedFDeriv ℝ j (F p.1) p.2)) :
    Continuous F := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply continuous_iff_continuousAt.mpr
  intro y₀
  apply (schwartz_withSeminorms ℂ D ℂ).tendsto_nhds F (F y₀) |>.mpr
  intro i ε hε
  let J := schwartzWeightedJetOn K i.1 i.2
  have hJ : Continuous (fun y ↦ J (F y)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : Y × K ↦
      ‖(p.2 : D)‖ ^ i.1 • iteratedFDeriv ℝ i.2 (F p.1) p.2)
    exact ((continuous_subtype_val.comp continuous_snd).norm.pow _).smul
      ((hjets i.2).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hnear : {y | ‖J (F y) - J (F y₀)‖ < ε} ∈ 𝓝 y₀ :=
    (isOpen_lt ((hJ.sub continuous_const).norm) continuous_const).mem_nhds
      (by
        change ‖J (F y₀) - J (F y₀)‖ < ε
        simpa only [sub_self, norm_zero] using hε)
  filter_upwards [hnear] with y hy
  have hsupport : tsupport (F y - F y₀) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra hxK
    have hyx : F y x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hxK (hF y h))
    have hy₀x : F y₀ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hxK (hF y₀ h))
    exact hx (by simp only [sub_apply, hyx, hy₀x, sub_self])
  change SchwartzMap.seminorm ℂ i.1 i.2 (F y - F y₀) < ε
  rw [← norm_schwartzWeightedJetOn K i.1 i.2 (F y - F y₀) hsupport]
  simpa only [map_sub] using hy

/-- Windowed Fourier coefficients decay jointly in position and frequency, with
one continuous Schwartz seminorm controlling the original input. This is the
absolute-integrability estimate used by the kernel extension. -/
theorem exists_schwartz_window_fourier_bound (g : 𝓢(V, ℂ)) (M N : ℕ) :
    ∃ q : Seminorm ℂ 𝓢(V, ℂ), Continuous q ∧ ∀ f : 𝓢(V, ℂ), ∀ a ξ : V,
      (1 + ‖a‖) ^ M * (1 + ‖ξ‖) ^ N *
        ‖(FourierTransform.fourier
          (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f
            (SchwartzMap.compSubConstCLM ℂ a g)) : 𝓢(V, ℂ)) ξ‖ ≤ q f := by
  let L : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := FourierTransform.fourierCLM ℂ 𝓢(V, ℂ)
  let p := (SchwartzMap.seminorm ℂ 0 0 + SchwartzMap.seminorm ℂ N 0).comp L.toLinearMap
  have hp : Continuous p :=
    (((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (0, 0)).add
      ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (N, 0))).comp L.continuous
  obtain ⟨q, hq, hbound⟩ := exists_schwartz_window_decay_seminorm p hp g M
  refine ⟨(2 ^ N : NNReal) • q, hq.const_smul (2 ^ N : NNReal), ?_⟩
  intro f a ξ
  let u := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f
    (SchwartzMap.compSubConstCLM ℂ a g)
  let w : 𝓢(V, ℂ) := L u
  have hpower : (1 + ‖ξ‖) ^ N ≤ 2 ^ N * (1 + ‖ξ‖ ^ N) := by
    apply (add_pow_le zero_le_one (norm_nonneg ξ) N).trans
    rw [one_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (Nat.sub_le N 1)) (by positivity)
  have hξ : (1 + ‖ξ‖) ^ N * ‖w ξ‖ ≤ 2 ^ N * p u := by
    calc
      _ ≤ (2 ^ N * (1 + ‖ξ‖ ^ N)) * ‖w ξ‖ := by gcongr
      _ = 2 ^ N * (‖w ξ‖ + ‖ξ‖ ^ N * ‖w ξ‖) := by ring
      _ ≤ 2 ^ N * (SchwartzMap.seminorm ℂ 0 0 w + SchwartzMap.seminorm ℂ N 0 w) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply add_le_add
        · simpa only [norm_iteratedFDeriv_zero] using
            SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ w 0 ξ
        · simpa only [norm_iteratedFDeriv_zero] using SchwartzMap.le_seminorm ℂ N 0 w ξ
      _ = _ := rfl
  change (1 + ‖a‖) ^ M * (1 + ‖ξ‖) ^ N * ‖w ξ‖ ≤ ((2 ^ N : NNReal) • q) f
  simp only [smul_apply, NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, NNReal.coe_ofNat]
  calc
    _ = (1 + ‖a‖) ^ M * ((1 + ‖ξ‖) ^ N * ‖w ξ‖) := mul_assoc _ _ _
    _ ≤ (1 + ‖a‖) ^ M * (2 ^ N * p u) := by gcongr
    _ = 2 ^ N * ((1 + ‖a‖) ^ M * p u) := by ring
    _ ≤ 2 ^ N * q f := mul_le_mul_of_nonneg_left (hbound f a) (by positivity)

/-- A compactly supported Schwartz window depends continuously on position and
frequency in the original Schwartz topology after translation and modulation. -/
theorem continuous_schwartz_modulation_translation (g : 𝓢(V, ℂ))
    (hg : HasCompactSupport g) :
    Continuous (fun p : V × V ↦ FourierTransform.fourierInv
      (SchwartzMap.compSubConstCLM ℂ p.2
        (FourierTransform.fourier (SchwartzMap.compSubConstCLM ℂ p.1 g)))) := by
  classical
  let F : V × V → 𝓢(V, ℂ) := fun p ↦ FourierTransform.fourierInv
    (SchwartzMap.compSubConstCLM ℂ p.2
      (FourierTransform.fourier (SchwartzMap.compSubConstCLM ℂ p.1 g)))
  let W : (V × V) × V → ℂ := fun p ↦
    (Real.fourierChar (inner ℝ p.1.2 p.2) : ℂ) * g (p.2 - p.1.1)
  have hF (p : V × V) (x : V) : F p x = W (p, x) :=
    fourierInv_compSubConstCLM_fourier_apply (SchwartzMap.compSubConstCLM ℂ p.1 g) p.2 x
  have hcast : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hinner : ContDiff ℝ ∞ (fun p : (V × V) × V ↦ inner ℝ p.1.2 p.2) :=
    ((innerSL ℝ).contDiff.comp contDiff_fst.snd).clm_apply contDiff_snd
  have hW : ContDiff ℝ ∞ W := by
    simp only [W, Real.fourierChar_apply]
    fun_prop
  -- Differentiation in the spatial variable retains smooth dependence on both parameters.
  have hjets (j : ℕ) : ContDiff ℝ ∞ (fun p : (V × V) × V ↦
      iteratedFDeriv ℝ j (fun x ↦ W (p.1, x)) p.2) := by
    induction j with
    | zero =>
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact (continuousMultilinearCurryFin0 ℝ V ℂ).symm.contDiff.comp hW
    | succ j ih =>
      simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      have hp : ContDiff ℝ ∞ (fun p : ((V × V) × V) × V ↦
          iteratedFDeriv ℝ j (fun x ↦ W (p.1.1, x)) p.2) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd := hp.fderiv
        (f := fun p : (V × V) × V ↦ fun x : V ↦
          iteratedFDeriv ℝ j (fun z ↦ W (p.1, z)) x)
        (g := fun p : (V × V) × V ↦ p.2) contDiff_snd
        (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (j + 1) ↦ V) ℂ).symm.contDiff.comp hd
  have hjetF (j : ℕ) : Continuous (fun p : (V × V) × V ↦
      iteratedFDeriv ℝ j (F p.1) p.2) := by
    convert (hjets j).continuous using 1
    funext p
    rw [show (F p.1 : V → ℂ) = (fun x ↦ W (p.1, x)) from funext (hF p.1)]
  obtain ⟨R, hR, hGR⟩ := hg.isBounded.subset_closedBall_lt 0 (0 : V)
  apply continuous_iff_continuousAt.mpr
  intro p₀
  let S := Metric.ball p₀ 1
  let K := Metric.closedBall (0 : V) (R + ‖p₀.1‖ + 1)
  have hsupport (p : S) : tsupport (F p) ⊆ K := by
    apply closure_minimal ?_ Metric.isClosed_closedBall
    intro x hx
    have htest : g (x - p.val.1) ≠ 0 := by
      intro hzero
      apply hx
      rw [hF]
      simp [W, hzero]
    have hxR : ‖x - p.val.1‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hGR (subset_tsupport g htest)
    have hpdist : dist p.val.1 p₀.1 < 1 :=
      lt_of_le_of_lt (show dist p.val.1 p₀.1 ≤ dist p.val p₀ from le_max_left _ _) p.property
    have hpR : ‖p.val.1‖ ≤ ‖p₀.1‖ + 1 := by
      have h := norm_add_le (p.val.1 - p₀.1) p₀.1
      rw [sub_add_cancel, ← dist_eq_norm] at h
      linarith
    change dist x 0 ≤ R + ‖p₀.1‖ + 1
    rw [dist_zero_right]
    have h := norm_add_le (x - p.val.1) p.val.1
    rw [sub_add_cancel] at h
    linarith
  have hcontinuous : Continuous (fun p : S ↦ F p) := by
    apply continuous_schwartzMap_of_common_compact_support (D := V) (Y := S)
      (fun p : S ↦ F p.val) K (isCompact_closedBall _ _) hsupport
    intro j
    have hproj : Continuous (fun p : S × V ↦ ((p.1 : V × V), p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hcomposed := (hjetF j).comp hproj
    exact hcomposed
  have hOn : ContinuousOn F S := continuousOn_iff_continuous_domRestrict.mpr hcontinuous
  exact hOn.continuousAt (Metric.ball_mem_nhds p₀ zero_lt_one)

end AtiyahSinger
