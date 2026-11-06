/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SymbolCoordinateEstimates

import all AtiyahSinger.Analysis.SymbolCoordinateEstimates

/-!
# Estimates for conic symbol cutoffs

Public module ID: M0379.

A globally smooth function that agrees with degree-zero homogeneous data outside
a ball has the derivative estimates of an order-zero symbol. Only the smooth
regularization is differentiated; the homogeneous data need not be defined
smoothly at the origin. The estimates support product-frequency regularization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter
open scoped ContDiff Topology

set_option maxSynthPendingDepth 20

/-- A smooth regularization of degree-zero homogeneous data has order-zero derivative bounds. -/
theorem exists_iteratedFDeriv_bound_of_eventually_homogeneous_zero
    {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f g : X → V) (hf : ContDiff ℝ ∞ f)
    (hg : ∀ (x : X) (t : ℝ), 0 < t → g (t • x) = g x)
    (R : ℝ) (hfg : ∀ x, R ≤ ‖x‖ → f x = g x) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖iteratedFDeriv ℝ j f x‖ ≤ C * (1 + ‖x‖) ^ (-(j : ℝ)) := by
  let M : ℝ := max R 1 + 1
  have hM : 0 < M := by dsimp [M]; linarith [le_max_right R 1]
  have hRM : R < M := by dsimp [M]; linarith [le_max_left R 1]
  have hM1 : 1 ≤ M := by dsimp [M]; linarith [le_max_right R 1]
  have hcompact : IsCompact (Metric.closedBall (0 : X) M) := isCompact_closedBall _ _
  obtain ⟨D, hD⟩ := (hcompact.image (hf.continuous_iteratedFDeriv (by simp)).norm).bddAbove
  let A : ℝ := max D 0
  have hA : 0 ≤ A := le_max_right _ _
  have hbound (x : X) (hx : ‖x‖ ≤ M) : ‖iteratedFDeriv ℝ j f x‖ ≤ A :=
    (hD ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, rfl⟩).trans
      (le_max_left _ _)
  let C : ℝ := (1 + M) ^ j * A + 2 ^ j * M ^ j * A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x
  have hweighted : (1 + ‖x‖) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    by_cases hx : ‖x‖ ≤ M
    · have h : (1 + ‖x‖) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ (1 + M) ^ j * A :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) j)
          (hbound x hx) (norm_nonneg _) (by positivity)
      exact h.trans (le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hM.le j)) hA))
    · -- At high frequency both dilates agree with the same homogeneous data locally.
      let t : ℝ := ‖x‖
      have htM : M < t := lt_of_not_ge hx
      have ht : 0 < t := hM.trans htM
      let η : X := t⁻¹ • x
      have hη : ‖η‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
        exact inv_mul_cancel₀ ht.ne'
      have htx : t • η = x := smul_inv_smul₀ ht.ne' x
      have hnorm (s : ℝ) (hs : 0 < s) : ‖s • η‖ = s := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, hη, mul_one]
      have heq : (fun ζ ↦ f (t • ζ)) =ᶠ[𝓝 η] (fun ζ ↦ f (M • ζ)) := by
        have h₁ : R < ‖t • η‖ := by rw [hnorm t ht]; exact hRM.trans htM
        have h₂ : R < ‖M • η‖ := by rw [hnorm M hM]; exact hRM
        filter_upwards [((continuous_const.smul continuous_id).norm.continuousAt.eventually
          (lt_mem_nhds h₁)), ((continuous_const.smul continuous_id).norm.continuousAt.eventually
          (lt_mem_nhds h₂))] with ζ hζ₁ hζ₂
        change R < ‖t • ζ‖ at hζ₁
        change R < ‖M • ζ‖ at hζ₂
        rw [hfg _ hζ₁.le, hfg _ hζ₂.le, hg ζ t ht, hg ζ M hM]
      have hd := (heq.iteratedFDeriv ℝ j).eq_of_nhds
      rw [congrFun (iteratedFDeriv_comp_const_smul t (hf.of_le (by simp))) η,
        congrFun (iteratedFDeriv_comp_const_smul M (hf.of_le (by simp))) η, htx] at hd
      have hn := congrArg norm hd
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos ht j),
        abs_of_pos (pow_pos hM j)] at hn
      have hscaled : t ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ M ^ j * A := by
        rw [hn]
        exact mul_le_mul_of_nonneg_left (hbound (M • η) (by rw [hnorm M hM]))
          (pow_nonneg hM.le _)
      have ht1 : 1 ≤ t := hM1.trans htM.le
      calc
        _ ≤ (2 * t) ^ j * ‖iteratedFDeriv ℝ j f x‖ := by
          gcongr
          change 1 + t ≤ 2 * t
          linarith
        _ = 2 ^ j * (t ^ j * ‖iteratedFDeriv ℝ j f x‖) := by rw [mul_pow]; ring
        _ ≤ 2 ^ j * (M ^ j * A) := mul_le_mul_of_nonneg_left hscaled (by positivity)
        _ = 2 ^ j * M ^ j * A := by ring
        _ ≤ C := le_add_of_nonneg_left (mul_nonneg (pow_nonneg (by positivity) j) hA)
  have hxpos : 0 < 1 + ‖x‖ := by positivity
  calc
    _ ≤ C / (1 + ‖x‖) ^ j :=
      (le_div_iff₀ (pow_pos hxpos j)).mpr (by simpa only [mul_comm] using hweighted)
    _ = _ := by rw [Real.rpow_neg hxpos.le, Real.rpow_natCast]; rfl

set_option maxHeartbeats 1000000 in
-- Rescaling combines mixed symbol estimates, two fixed pullbacks, and Leibniz bounds.
/-- An order-zero frequency cutoff supported on a controlled cone regularizes a linear lift. -/
theorem isSymbol_linearPullback_of_conicCutoff {n N r q : ℕ}
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (ha : IsSymbol Set.univ 1 a)
    (p : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (χ τ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hτ : ContDiff ℝ ∞ τ)
    (hτb : ∀ j : ℕ, ∃ T : ℝ, 0 ≤ T ∧ ∀ ξ,
      ‖iteratedFDeriv ℝ j τ ξ‖ ≤ T * (1 + ‖ξ‖) ^ (-(j : ℝ)))
    (B : ℝ) (hzero : ∀ ξ, B * (1 + ‖p ξ‖) < 1 + ‖ξ‖ → τ ξ = 0) :
    IsSymbol Set.univ 1 (fun x ξ ↦ (χ x * τ ξ) • a (p x) (p ξ)) := by
  let X := EuclideanSpace ℝ (Fin N)
  let Y := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let b : X → X → V := fun x ξ ↦ (χ x * τ ξ) • a (p x) (p ξ)
  have hs : ContDiff ℝ ∞ (Function.uncurry a) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
  have hb : ContDiff ℝ ∞ (Function.uncurry b) :=
    ((hχ.comp contDiff_fst).mul (hτ.comp contDiff_snd)).smul
      (hs.comp ((p.contDiff.comp contDiff_fst).prodMk (p.contDiff.comp contDiff_snd)))
  refine ⟨hb.contDiffOn, ?_⟩
  intro K _ hK i j
  let k := i + j
  let K₁ := p '' K
  have hK₁ : IsCompact K₁ := hK.image p.continuous
  choose A hA hAb using ha.2 K₁ (Set.subset_univ _) hK₁
  let D : ℝ := max B (1 + ‖p‖)
  have hD : 0 < D := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  let A' : ℝ := ∑ u ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (k + 1),
    A u v * D ^ |(1 : ℝ) - (v : ℝ)|
  have hA' : 0 ≤ A' := Finset.sum_nonneg (fun u _ ↦ Finset.sum_nonneg (fun v _ ↦
    mul_nonneg (hA u v) (Real.rpow_nonneg hD.le _)))
  have hAA' (u v : ℕ) (hu : u ≤ k) (hv : v ≤ k) :
      A u v * D ^ |(1 : ℝ) - (v : ℝ)| ≤ A' := by
    apply (Finset.single_le_sum (fun w _ ↦
      mul_nonneg (hA u w) (Real.rpow_nonneg hD.le _))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hv))).trans
    change (∑ v ∈ Finset.range (k + 1), A u v * D ^ |(1 : ℝ) - (v : ℝ)|) ≤
      ∑ w ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (k + 1),
        A w v * D ^ |(1 : ℝ) - (v : ℝ)|
    have hnonneg (w : ℕ) :
        0 ≤ ∑ v ∈ Finset.range (k + 1), A w v * D ^ |(1 : ℝ) - (v : ℝ)| :=
      Finset.sum_nonneg (fun v _ ↦ mul_nonneg (hA w v) (Real.rpow_nonneg hD.le _))
    exact Finset.single_le_sum (fun w _ ↦ hnonneg w)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hu))
  have hχbound (u : ℕ) : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ x ∈ K,
      ‖iteratedFDeriv ℝ u χ x‖ ≤ Q := by
    obtain ⟨Q, hQ⟩ := (hK.image (hχ.continuous_iteratedFDeriv (by simp)).norm).bddAbove
    exact ⟨max Q 0, le_max_right _ _, fun x hx ↦
      (hQ ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
  choose Q hQ hQb using hχbound
  choose T hT hTb using hτb
  let F : X × X →L[ℝ] X := ContinuousLinearMap.fst ℝ X X
  let S : X × X →L[ℝ] X := ContinuousLinearMap.snd ℝ X X
  let P : X × X →L[ℝ] Y × Y := p.prodMap p
  let Q' (u : ℕ) : ℝ := Q u * ‖F‖ ^ u
  let T' (u : ℕ) : ℝ := T u * ‖S‖ ^ u
  have hQ' (u : ℕ) : 0 ≤ Q' u := mul_nonneg (hQ u) (pow_nonneg (norm_nonneg _) _)
  have hT' (u : ℕ) : 0 ≤ T' u := mul_nonneg (hT u) (pow_nonneg (norm_nonneg _) _)
  let G (u : ℕ) : ℝ := ∑ v ∈ Finset.range (u + 1), (u.choose v : ℝ) * Q' v * T' (u - v)
  let H (u : ℕ) : ℝ := ‖P‖ ^ u * (2 ^ u * A')
  have hG (u : ℕ) : 0 ≤ G u := Finset.sum_nonneg (fun v _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hQ' v)) (hT' (u - v)))
  have hH (u : ℕ) : 0 ≤ H u := by dsimp [H]; positivity
  let C : ℝ := ∑ u ∈ Finset.range (k + 1), (k.choose u : ℝ) * G u * H (k - u)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun u _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hG u)) (hH (k - u)))
  refine ⟨C, hC, ?_⟩
  intro x hx ξ
  by_cases hz : B * (1 + ‖p ξ‖) < 1 + ‖ξ‖
  · -- Outside the closed cone the cutoff symbol vanishes on a frequency neighborhood.
    have hder (y : X) : iteratedFDeriv ℝ j (b y) ξ = 0 := by
      have heq : b y =ᶠ[𝓝 ξ] (fun _ ↦ 0) := by
        filter_upwards [(isOpen_lt (continuous_const.mul (continuous_const.add p.continuous.norm))
          (continuous_const.add continuous_norm)).mem_nhds hz] with ζ hζ
        simp only [b, hzero ζ hζ, mul_zero, zero_smul]
      simpa using (heq.iteratedFDeriv ℝ j).eq_of_nhds
    change ‖iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (b y) ξ) x‖ ≤ _
    simp only [hder]
    have hz' : iteratedFDeriv ℝ i (fun _ : X ↦
        (0 : X [×j]→L[ℝ] V)) x = 0 := by
      cases i <;> simp
    rw [hz', norm_zero]
    positivity
  · let t : ℝ := 1 + ‖ξ‖
    have ht : 0 < t := by dsimp [t]; positivity
    let η : X := t⁻¹ • ξ
    have htη : t • η = ξ := smul_inv_smul₀ ht.ne' ξ
    have hpt : t • p η = p ξ := (p.map_smul t η).symm.trans (congrArg p htη)
    have hsmall : 1 + ‖p ξ‖ ≤ D * t := by
      have h := p.le_opNorm ξ
      calc
        _ ≤ (1 + ‖p‖) * t := by dsimp [t]; nlinarith [norm_nonneg p, norm_nonneg ξ]
        _ ≤ D * t := mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le
    have hlarge : t ≤ D * (1 + ‖p ξ‖) :=
      (le_of_not_gt hz).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hpower (v : ℕ) : (1 + ‖p ξ‖) ^ ((1 : ℝ) - (v : ℝ)) ≤
        D ^ |(1 : ℝ) - (v : ℝ)| * t ^ ((1 : ℝ) - (v : ℝ)) :=
      rpow_le_mul_rpow_of_comparable _ _ D _ (by positivity) ht hD hsmall hlarge
    let a' : Y → Y → V := fun y ζ ↦ a y (t • ζ)
    have ha' : ContDiff ℝ ∞ (Function.uncurry a') :=
      hs.comp (contDiff_fst.prodMk ((contDiff_const (c := t)).smul contDiff_snd))
    have hscaled (u v : ℕ) (hu : u ≤ k) (hv : v ≤ k) :
        ‖iteratedFDeriv ℝ u (fun y ↦ iteratedFDeriv ℝ v (a' y) (p η)) (p x)‖ ≤ A' * t := by
      rw [mixed_iteratedFDeriv_frequency_smul a t ht.ne' u v, hpt,
        norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos ht v)]
      calc
        _ ≤ t ^ v * (A u v * (1 + ‖p ξ‖) ^ ((1 : ℝ) - (v : ℝ))) :=
          mul_le_mul_of_nonneg_left (hAb u v (p x) ⟨x, hx, rfl⟩ (p ξ)) (by positivity)
        _ ≤ t ^ v * (A u v *
            (D ^ |(1 : ℝ) - (v : ℝ)| * t ^ ((1 : ℝ) - (v : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpower v) (hA u v))
            (pow_nonneg ht.le _)
        _ = (A u v * D ^ |(1 : ℝ) - (v : ℝ)|) *
            (t ^ v * t ^ ((1 : ℝ) - (v : ℝ))) := by ring
        _ = (A u v * D ^ |(1 : ℝ) - (v : ℝ)|) * t := by
          rw [← Real.rpow_natCast, ← Real.rpow_add ht]
          rw [show (v : ℝ) + (1 - (v : ℝ)) = 1 by ring, Real.rpow_one]
        _ ≤ A' * t := mul_le_mul_of_nonneg_right (hAA' u v hu hv) ht.le
    have hfull (u : ℕ) (hu : u ≤ k) :
        ‖iteratedFDeriv ℝ u (Function.uncurry a') (p x, p η)‖ ≤ (2 ^ u * A') * t := by
      have h := norm_iteratedFDeriv_uncurry_le_of_mixed a' ha' u (p x) (p η) (A' * t)
        (mul_nonneg hA' ht.le) (fun v hv w hw ↦ hscaled v w (hv.trans hu) (hw.trans hu))
      exact h.trans_eq (by ring)
    have hpull (u : ℕ) (hu : u ≤ k) :
        ‖iteratedFDeriv ℝ u (fun z : X × X ↦ a' (p z.1) (p z.2)) (x, η)‖ ≤ H u * t := by
      change ‖iteratedFDeriv ℝ u (Function.uncurry a' ∘ P) (x, η)‖ ≤ _
      rw [P.iteratedFDeriv_comp_right ha' (x, η) (by simp)]
      apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc
        _ ≤ ((2 ^ u * A') * t) * ‖P‖ ^ u :=
          mul_le_mul_of_nonneg_right (hfull u hu) (by positivity)
        _ = _ := by dsimp [H]; ring
    have hχpull (u : ℕ) :
        ‖iteratedFDeriv ℝ u (fun z : X × X ↦ χ z.1) (x, η)‖ ≤ Q' u := by
      change ‖iteratedFDeriv ℝ u (χ ∘ F) (x, η)‖ ≤ _
      rw [F.iteratedFDeriv_comp_right hχ (x, η) (by simp)]
      apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul_of_nonneg_right (hQb u x hx) (by positivity)
    let L : X × X →L[ℝ] X := t • S
    have hτpull (u : ℕ) : ‖iteratedFDeriv ℝ u (τ ∘ L) (x, η)‖ ≤ T' u := by
      rw [L.iteratedFDeriv_comp_right hτ (x, η) (by simp)]
      apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hLξ : L (x, η) = ξ := htη
      rw [hLξ]
      calc
        _ ≤ (T u * t ^ (-(u : ℝ))) * ‖L‖ ^ u :=
          mul_le_mul_of_nonneg_right (hTb u ξ) (by positivity)
        _ = (T u * ‖S‖ ^ u) * (t ^ (-(u : ℝ)) * t ^ u) := by
          simp only [L, norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow]
          ring
        _ = T' u := by
          rw [Real.rpow_neg ht.le, Real.rpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ ht.ne'),
            mul_one]
    have hcut (u : ℕ) :
        ‖iteratedFDeriv ℝ u (fun z : X × X ↦ χ z.1 * τ (L z)) (x, η)‖ ≤ G u := by
      have h := norm_iteratedFDeriv_smul_le (hχ.comp contDiff_fst) (hτ.comp L.contDiff)
        (x, η) (n := u) (by simp)
      apply h.trans
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hχpull v) (Nat.cast_nonneg _))
        (hτpull (u - v)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hQ' v))
    have hprod := norm_iteratedFDeriv_smul_le
      ((hχ.comp contDiff_fst).mul (hτ.comp L.contDiff))
      (ha'.comp P.contDiff) (x, η) (n := k) (by simp)
    have hprodBound : ‖iteratedFDeriv ℝ k (fun z : X × X ↦
        (χ z.1 * τ (L z)) • a' (p z.1) (p z.2)) (x, η)‖ ≤ C * t := by
      apply hprod.trans
      dsimp only [C]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro u hu
      calc
        _ ≤ (k.choose u : ℝ) * G u * (H (k - u) * t) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hcut u) (Nat.cast_nonneg _))
            (hpull (k - u) (Nat.sub_le _ _)) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (hG u))
        _ = _ := by ring
    have hsame : (fun z : X × X ↦ (χ z.1 * τ (L z)) • a' (p z.1) (p z.2)) =
        Function.uncurry (fun y ζ ↦ b y (t • ζ)) := by
      funext z
      simp only [Function.uncurry, b, a', p.map_smul]
      rfl
    rw [hsame] at hprodBound
    have hbScaled : ContDiff ℝ ∞ (Function.uncurry (fun y ζ ↦ b y (t • ζ))) :=
      hb.comp (contDiff_fst.prodMk ((contDiff_const (c := t)).smul contDiff_snd))
    have hmixed := norm_mixed_iteratedFDeriv_le (fun y ζ ↦ b y (t • ζ)) hbScaled i j x η
    have hnorm := hmixed.trans hprodBound
    rw [mixed_iteratedFDeriv_frequency_smul b t ht.ne' i j, htη,
      norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos ht j)] at hnorm
    have hdivide := (le_div_iff₀ (pow_pos ht j)).mpr
      (show ‖symbolDerivative b i j x ξ‖ * t ^ j ≤ C * t by
        simpa only [mul_comm, symbolDerivative] using hnorm)
    have hweight : C * t / t ^ j = C * t ^ ((1 : ℝ) - (j : ℝ)) := by
      rw [Real.rpow_sub ht, Real.rpow_one, Real.rpow_natCast]
      ring
    exact hdivide.trans_eq hweight

end AtiyahSinger
