/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EuclideanSobolev
public import AtiyahSinger.Analysis.Symbol
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Spatial Fourier estimates for symbols

Public module ID: M1021.

Compact spatial support controls all Schwartz seminorms uniformly in the original
real symbol order. Fourier continuity gives decay in the spatial dual variable.
Peetre's inequality then supplies an integrable majorant for Bessel-conjugated
kernels, with the exact frequency rescaling used by Kohn–Nirenberg quantization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open FourierTransform MeasureTheory
open scoped SchwartzMap ContDiff

set_option maxSynthPendingDepth 20

/-- Compact spatial support gives uniform Fourier decay at the original real symbol order. -/
theorem spatial_fourier_decay {n r q : ℕ} (m : ℝ)
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (ha : IsSymbol Set.univ m a)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hsupp : ∀ x, x ∉ K → ∀ ξ, a x ξ = 0) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η ζ,
      ‖𝓕 (fun x ↦ a x η) ζ‖ ≤
        C * (1 + ‖η‖) ^ m * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  have hsmooth : ContDiff ℝ ∞ (Function.uncurry a) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
  have hs (η : X) : HasCompactSupport (fun x ↦ a x η) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (hsupp x hxK η)
  have hsub (η : X) : tsupport (fun x ↦ a x η) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (hsupp x hxK η)
  let S (η : X) : 𝓢(X, V) :=
    (hs η).toSchwartzMap (hsmooth.comp (contDiff_id.prodMk contDiff_const))
  have hderiv (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ η x, x ∈ K →
      ‖iteratedFDeriv ℝ i (fun x ↦ a x η) x‖ ≤ C * (1 + ‖η‖) ^ m := by
    obtain ⟨C, hC, hbound⟩ := ha.2 K (Set.subset_univ _) hK i 0
    refine ⟨C, hC, ?_⟩
    intro η x hx
    have heq : (fun y ↦ iteratedFDeriv ℝ 0 (a y) η) =
        (continuousMultilinearCurryFin0 ℝ X V).symm ∘ (fun y ↦ a y η) := by
      funext y
      exact congrFun iteratedFDeriv_zero_eq_comp η
    simpa only [symbolDerivative, heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      Nat.cast_zero, sub_zero] using hbound x hx η
  have hseminorm (j i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ η,
      SchwartzMap.seminorm ℂ j i (S η) ≤ C * (1 + ‖η‖) ^ m := by
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    obtain ⟨C, hC, hb⟩ := hderiv i
    refine ⟨(max R 0) ^ j * C, by positivity, ?_⟩
    intro η
    apply SchwartzMap.seminorm_le_bound ℂ j i (S η) (by positivity)
    intro x
    change ‖x‖ ^ j * ‖iteratedFDeriv ℝ i (fun x ↦ a x η) x‖ ≤ _
    by_cases hx : x ∈ K
    · calc
        _ ≤ (max R 0) ^ j * (C * (1 + ‖η‖) ^ m) := by
          gcongr
          · exact (hR x hx).trans (le_max_left R 0)
          · exact hb η x hx
        _ = _ := by ring
    · have hz : iteratedFDeriv ℝ i (fun x ↦ a x η) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h ↦ hx (hsub η (tsupport_iteratedFDeriv_subset i h)))
      rw [hz, norm_zero, mul_zero]
      positivity
  let T : 𝓢(X, V) →L[ℂ] 𝓢(X, V) := FourierTransform.fourierCLM ℂ _
  let p : Seminorm ℂ 𝓢(X, V) :=
    (Finset.Iic (N, 0)).sup (fun i ↦ SchwartzMap.seminorm ℂ i.1 i.2)
  have hp : Continuous p :=
    Seminorm.continuous_finsetSup (fun i _ ↦
      (schwartz_withSeminorms ℂ X V).continuous_seminorm i)
  obtain ⟨s, A, hA0, hA⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ X V) (p.comp T.toLinearMap) (hp.comp T.continuous)
  choose C hC hb using hseminorm
  let D := ∑ i ∈ s, C i.1 i.2
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ ↦ hC i.1 i.2)
  refine ⟨2 ^ N * A * D, by positivity, ?_⟩
  intro η ζ
  have hsum : s.sup (schwartzSeminormFamily ℂ X V) (S η) ≤ D * (1 + ‖η‖) ^ m := by
    apply Seminorm.finset_sup_apply_le
    · positivity
    · intro i hi
      exact (hb i.1 i.2 η).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ ↦ hC j.1 j.2) hi) (by positivity))
  have hweight : (1 + ‖ζ‖) ^ N * ‖T (S η) ζ‖ ≤
      (2 ^ N * A * D) * (1 + ‖η‖) ^ m := by
    calc
      _ ≤ 2 ^ N * p (T (S η)) := by
        simpa only [p, schwartzSeminormFamily, iteratedFDeriv_zero_eq_comp,
          Function.comp_apply, LinearIsometryEquiv.norm_map] using
          SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
            (m := (N, 0)) (le_refl _) (le_refl _) (T (S η)) ζ
      _ ≤ 2 ^ N * (A * (s.sup (schwartzSeminormFamily ℂ X V) (S η))) :=
        mul_le_mul_of_nonneg_left (hA (S η)) (by positivity)
      _ ≤ 2 ^ N * (A * (D * (1 + ‖η‖) ^ m)) := by gcongr
      _ = _ := by ring
  have hFourier : T (S η) ζ = 𝓕 (fun x ↦ a x η) ζ := rfl
  rw [hFourier] at hweight
  have hpos : 0 < 1 + ‖ζ‖ := by positivity
  calc
    _ ≤ ((2 ^ N * A * D) * (1 + ‖η‖) ^ m) / (1 + ‖ζ‖) ^ N :=
      (le_div_iff₀ (pow_pos hpos N)).mpr (by simpa only [mul_comm] using hweight)
    _ = _ := by rw [Real.rpow_neg hpos.le, Real.rpow_natCast]; rfl

private theorem bessel_weight_shift {X : Type*} [NormedAddCommGroup X]
    (t : ℝ) (x y : X) :
    (1 + ‖x + y‖ ^ 2) ^ t ≤
      (2 : ℝ) ^ |t| * (1 + ‖x‖ ^ 2) ^ t * (1 + ‖y‖ ^ 2) ^ |t| := by
  have htriangle (x y : X) :
      1 + ‖x + y‖ ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2) := by
    have hsq := (sq_le_sq₀ (norm_nonneg (x + y))
      (add_nonneg (norm_nonneg x) (norm_nonneg y))).mpr (norm_add_le x y)
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖)]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, ← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (htriangle x y) ht
  · have ht0 : t ≤ 0 := le_of_not_ge ht
    have hreverse : 1 + ‖x‖ ^ 2 ≤ 2 * (1 + ‖x + y‖ ^ 2) * (1 + ‖y‖ ^ 2) := by
      simpa only [add_neg_cancel_right, norm_neg] using htriangle (x + y) (-y)
    have h := Real.rpow_le_rpow_of_nonpos (by positivity) hreverse ht0
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)] at h
    calc
      _ ≤ (1 + ‖x‖ ^ 2) ^ t / ((2 : ℝ) ^ t * (1 + ‖y‖ ^ 2) ^ t) :=
        (le_div_iff₀ (by positivity)).mpr (by nlinarith [h])
      _ = _ := by
        rw [abs_of_nonpos ht0, Real.rpow_neg (by positivity),
          Real.rpow_neg (by positivity)]
        field_simp

private theorem spatial_weight_le_bessel {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (m : ℝ) (x : X) :
    (1 + ‖(2 * Real.pi) • x‖) ^ m ≤
      max ((2 * (2 * Real.pi) ^ 2) ^ (m / 2)) 1 * (1 + ‖x‖ ^ 2) ^ (m / 2) := by
  let c : ℝ := 2 * Real.pi
  have hc : 1 ≤ c := by dsimp [c]; linarith [Real.one_le_pi_div_two]
  have hnorm : ‖(2 * Real.pi) • x‖ = c * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hlow : 1 + ‖x‖ ^ 2 ≤ (1 + c * ‖x‖) ^ 2 := by
    have hx : ‖x‖ ≤ c * ‖x‖ := by nlinarith [norm_nonneg x]
    have hs := (sq_le_sq₀ (norm_nonneg x) (by positivity)).mpr hx
    nlinarith [norm_nonneg x]
  have hhigh : (1 + c * ‖x‖) ^ 2 ≤ (2 * c ^ 2) * (1 + ‖x‖ ^ 2) := by
    have hc2 : 1 ≤ c ^ 2 := by nlinarith
    nlinarith [sq_nonneg (1 - c * ‖x‖)]
  rw [hnorm]
  have hpow : (1 + c * ‖x‖) ^ m = ((1 + c * ‖x‖) ^ 2) ^ (m / 2) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  rw [hpow]
  by_cases hm : 0 ≤ m / 2
  · calc
      _ ≤ ((2 * c ^ 2) * (1 + ‖x‖ ^ 2)) ^ (m / 2) :=
        Real.rpow_le_rpow (by positivity) hhigh hm
      _ = (2 * c ^ 2) ^ (m / 2) * (1 + ‖x‖ ^ 2) ^ (m / 2) :=
        Real.mul_rpow (by positivity) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · calc
      _ ≤ (1 + ‖x‖ ^ 2) ^ (m / 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hlow (le_of_not_ge hm)
      _ ≤ _ := by
        calc
          _ = 1 * (1 + ‖x‖ ^ 2) ^ (m / 2) := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The conjugated Fourier kernel is dominated by an even integrable frequency majorant. -/
theorem weighted_spatial_fourier_kernel_bound {n r q : ℕ} (m s : ℝ)
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (ha : IsSymbol Set.univ m a)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hsupp : ∀ x, x ∉ K → ∀ ξ, a x ξ = 0) :
    ∃ w : EuclideanSpace ℝ (Fin n) → ℝ,
      Continuous w ∧ (∀ x, 0 ≤ w x) ∧ Integrable w ∧ (∀ x, w (-x) = w x) ∧
      ∀ ξ η,
        ‖((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2)) •
          𝓕 (fun x ↦ a x ((2 * Real.pi) • η)) (ξ - η)‖ ≤ w (ξ - η) := by
  let X := EuclideanSpace ℝ (Fin n)
  let t : ℝ := (s - m) / 2
  let d : ℕ := ⌈2 * |t|⌉₊ + n + 1
  obtain ⟨C, hC, hdecay⟩ := spatial_fourier_decay m a ha K hK hsupp d
  let D : ℝ := max ((2 * (2 * Real.pi) ^ 2) ^ (m / 2)) 1
  have hD : 0 ≤ D := (zero_le_one.trans (le_max_right _ _))
  let E : ℝ := C * D * (2 : ℝ) ^ |t|
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let w : X → ℝ := fun z ↦ E * (1 + ‖z‖) ^ (-(n : ℝ) - 1)
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · apply Continuous.const_mul
    apply Continuous.rpow_const (continuous_const.add continuous_norm)
    intro x
    left
    exact ne_of_gt (show 0 < 1 + ‖x‖ from by positivity)
  · intro x
    dsimp [w]
    positivity
  · apply Integrable.const_mul
    have hd : (Module.finrank ℝ X : ℝ) < (n : ℝ) + 1 := by simp [X]
    simpa only [neg_add, sub_eq_add_neg] using
      (integrable_one_add_norm (E := X) (μ := volume) hd)
  · intro x
    simp only [w, norm_neg]
  · intro ξ η
    have hshift := bessel_weight_shift t η (ξ - η)
    rw [add_sub_cancel] at hshift
    have hspatial := spatial_weight_le_bessel m η
    have hη : (1 + ‖η‖ ^ 2) ^ t * (1 + ‖η‖ ^ 2) ^ (m / 2) *
        (1 + ‖η‖ ^ 2) ^ (-s / 2) = 1 := by
      rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
      have he : t + m / 2 + -s / 2 = 0 := by dsimp [t]; ring
      rw [he, Real.rpow_zero]
    have hpower : (1 + ‖ξ - η‖ ^ 2) ^ |t| * (1 + ‖ξ - η‖) ^ (-(d : ℝ)) ≤
        (1 + ‖ξ - η‖) ^ (-(n : ℝ) - 1) := by
      calc
        _ ≤ ((1 + ‖ξ - η‖) ^ 2) ^ |t| * (1 + ‖ξ - η‖) ^ (-(d : ℝ)) := by
          gcongr
          nlinarith [norm_nonneg (ξ - η)]
        _ = (1 + ‖ξ - η‖) ^ (2 * |t| - (d : ℝ)) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity),
            ← Real.rpow_add (by positivity)]
          rfl
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by have := norm_nonneg (ξ - η); linarith)
          (by dsimp [d]; push_cast; linarith [Nat.le_ceil (2 * |t|)])
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ ((1 + ‖ξ‖ ^ 2) ^ t * (1 + ‖η‖ ^ 2) ^ (-s / 2)) *
          (C * (1 + ‖(2 * Real.pi) • η‖) ^ m * (1 + ‖ξ - η‖) ^ (-(d : ℝ))) := by
        gcongr
        exact hdecay _ _
      _ ≤ ((2 ^ |t| * (1 + ‖η‖ ^ 2) ^ t * (1 + ‖ξ - η‖ ^ 2) ^ |t|) *
          (1 + ‖η‖ ^ 2) ^ (-s / 2)) *
          (C * (D * (1 + ‖η‖ ^ 2) ^ (m / 2)) * (1 + ‖ξ - η‖) ^ (-(d : ℝ))) := by
        gcongr
      _ = E * ((1 + ‖ξ - η‖ ^ 2) ^ |t| * (1 + ‖ξ - η‖) ^ (-(d : ℝ))) := by
        dsimp [E]
        calc
          _ = (C * D * 2 ^ |t|) *
              ((1 + ‖ξ - η‖ ^ 2) ^ |t| * (1 + ‖ξ - η‖) ^ (-(d : ℝ))) *
              ((1 + ‖η‖ ^ 2) ^ t * (1 + ‖η‖ ^ 2) ^ (m / 2) *
                (1 + ‖η‖ ^ 2) ^ (-s / 2)) := by ring
          _ = _ := by rw [hη, mul_one]
      _ ≤ w (ξ - η) := mul_le_mul_of_nonneg_left hpower hE

end AtiyahSinger
