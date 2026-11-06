/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SymbolQuotient

import all AtiyahSinger.Analysis.SymbolCoordinateEstimates

import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Derivative bounds for a high-frequency inverse symbol

Public module ID: M0763.

The inverse estimate of SG III.4.4 is proved for the original mixed symbol
seminorms, with independent source and target ranks. Uniform bounds for a symbol
and its inverse become a compact normalized matrix range. A smooth extension of
inversion on that range and the higher chain rule give the exact inverse order.
Spatial localization permits applying this estimate to symbols on open domains.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter Set
open scoped ContDiff Topology

set_option maxSynthPendingDepth 25

set_option maxHeartbeats 800000 in

/-- A uniform high-frequency inverse bound gives all mixed inverse-symbol estimates.
Each frequency derivative lowers the inverse order by one. -/
theorem exists_symbolDerivative_inverse_bound {n r q : ℕ} (m : ℝ) (a : SymbolFunction n r q)
    (ha : IsSymbol univ m a) (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (R B : ℝ) (_hB : 0 ≤ B)
    (hinv : ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ → (a x ξ).IsInvertible)
    (hbound : ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ → ‖(a x ξ).inverse‖ ≤
      B * (1 + ‖ξ‖) ^ (-m)) (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
      ‖symbolDerivative (fun y η ↦ (a y η).inverse) i j x ξ‖ ≤
        C * (1 + ‖ξ‖) ^ (-m - (j : ℝ)) := by
  classical
  -- Compactly cut off matrix inversion on the normalized invertible range.
  have hExtension {r q : ℕ} (A B : ℝ) :
      ∃ g : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) →
          (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)),
        ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
          ∀ L, L.IsInvertible → ‖L‖ ≤ A → ‖L.inverse‖ ≤ B →
            g =ᶠ[𝓝 L] ContinuousLinearMap.inverse := by
    classical
    let E := EuclideanSpace ℂ (Fin r)
    let F := EuclideanSpace ℂ (Fin q)
    let : FiniteDimensional ℂ (E →L[ℂ] F) :=
      FiniteDimensional.of_injective (ContinuousLinearMap.coeLM ℂ)
        (fun _ _ h ↦ DFunLike.ext _ _ (LinearMap.congr_fun h))
    let : FiniteDimensional ℂ (F →L[ℂ] E) :=
      FiniteDimensional.of_injective (ContinuousLinearMap.coeLM ℂ)
        (fun _ _ h ↦ DFunLike.ext _ _ (LinearMap.congr_fun h))
    let : FiniteDimensional ℝ (E →L[ℂ] F) := Module.Finite.trans ℂ _
    let : FiniteDimensional ℝ (F →L[ℂ] E) := Module.Finite.trans ℂ _
    let : ProperSpace (E →L[ℂ] F) := FiniteDimensional.proper ℝ (E →L[ℂ] F)
    let : ProperSpace (F →L[ℂ] E) := FiniteDimensional.proper ℝ (F →L[ℂ] E)
    let S : Set ((E →L[ℂ] F) × (F →L[ℂ] E)) :=
      (Metric.closedBall 0 A ×ˢ Metric.closedBall 0 B) ∩
        {z | z.1.comp z.2 = ContinuousLinearMap.id ℂ F ∧
          z.2.comp z.1 = ContinuousLinearMap.id ℂ E}
    have hS : IsCompact S := by
      apply ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right
      exact (isClosed_eq (continuous_fst.clm_comp continuous_snd) continuous_const).inter
        (isClosed_eq (continuous_snd.clm_comp continuous_fst) continuous_const)
    let K := Prod.fst '' S
    have hK : IsCompact K := hS.image continuous_fst
    have hInv (L : E →L[ℂ] F) (hL : L ∈ K) : L.IsInvertible := by
      obtain ⟨⟨L', R⟩, h, rfl⟩ := hL
      exact ContinuousLinearMap.IsInvertible.of_inverse h.2.1 h.2.2
    let U : Set (E →L[ℂ] F) := {L | L.IsInvertible}
    have hU : IsOpen U := ContinuousLinearMap.isOpen_setOfPred_isInvertible
    obtain ⟨O, hO, hKO, hOU, hOc⟩ :=
      exists_open_between_and_isCompact_closure hK hU hInv
    obtain ⟨W, hW, hOW, hWU, hWc⟩ :=
      exists_open_between_and_isCompact_closure hOc hU hOU
    obtain ⟨χ, hχ, _, hχs, hχone⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hW isClosed_closure hOW
    have hχsupp : tsupport χ = closure W := congrArg closure hχs
    have hχc : HasCompactSupport χ := by rwa [HasCompactSupport, hχsupp]
    have hχU : tsupport χ ⊆ U := by rwa [hχsupp]
    let g : (E →L[ℂ] F) → (F →L[ℂ] E) := fun L ↦ χ L • L.inverse
    have hg : ContDiff ℝ ∞ g := by
      apply contDiff_iff_contDiffAt.mpr
      intro L
      by_cases hL : L ∈ tsupport χ
      · exact hχ.contDiffAt.smul
          (((hχU hL).contDiffAt_map_inverse (n := ∞)).restrict_scalars ℝ)
      · apply (contDiffAt_const (c := (0 : F →L[ℂ] E))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hL] with T hT
        simp [g, image_eq_zero_of_notMem_tsupport hT]
    refine ⟨g, hg, ?_, ?_⟩
    · exact hχc.of_isClosed_subset isClosed_closure
        (tsupport_smul_subset_left χ ContinuousLinearMap.inverse)
    · intro L hL hA hB
      have hLK : L ∈ K := by
        refine ⟨(L, L.inverse), ⟨?_, hL.self_comp_inverse, hL.inverse_comp_self⟩, rfl⟩
        simpa only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right] using And.intro hA hB
      filter_upwards [hO.mem_nhds (hKO hLK)] with T hT
      have hone : χ T = 1 := (hχone T).mp (subset_closure hT)
      simp only [g, hone, one_smul]
  -- Local equality transfers both groups of mixed derivatives.
  have hMixedEq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → V)
      (x y : EuclideanSpace ℝ (Fin n))
      (h : Function.uncurry f =ᶠ[𝓝 (x, y)] Function.uncurry g) (i j : ℕ) :
      iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f z) y) x =
        iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (g z) y) x := by
    obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.mp h
    have heq : (fun z ↦ iteratedFDeriv ℝ j (f z) y) =ᶠ[𝓝 x]
        (fun z ↦ iteratedFDeriv ℝ j (g z) y) := by
      filter_upwards [hU] with z hz
      have hfg : f z =ᶠ[𝓝 y] g z := by
        filter_upwards [hW] with v hv
        exact @hUW (z, v) ⟨hz, hv⟩
      exact (hfg.iteratedFDeriv ℝ j).eq_of_nhds
    exact (heq.iteratedFDeriv ℝ i).eq_of_nhds
  -- Constant rescaling is an exact continuous-linear equivalence.
  have hMixedSmul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → V) (c : ℝ) (hc : c ≠ 0)
      (i j : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
      iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ c • f z w) y) x =
        c • iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f z) y) x := by
    let e : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
    have h (z : EuclideanSpace ℝ (Fin n)) : iteratedFDeriv ℝ j (fun w ↦ c • f z w) y =
        c • iteratedFDeriv ℝ j (f z) y := e.iteratedFDeriv_comp_left
    simp_rw [h]
    let e' : (EuclideanSpace ℝ (Fin n) [×j]→L[ℝ] V) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) [×j]→L[ℝ] V) :=
      ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
    exact e'.iteratedFDeriv_comp_left
  -- Normalize frequency and symbol size, then apply the bounded higher chain rule.
  let X := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  let F := EuclideanSpace ℂ (Fin q)
  let k := i + j
  have hs : ContDiff ℝ ∞ (Function.uncurry a) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using ha.1
  choose A hA haA using ha.2 K (subset_univ _) hK
  obtain ⟨g, hg, hgc, hgeq⟩ := hExtension (r := r) (q := q) (A 0 0) B
  have hgBound (b : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ L : E →L[ℂ] F,
      ‖iteratedFDeriv ℝ b g L‖ ≤ D := by
    obtain ⟨D, hD⟩ := (hgc.iteratedFDeriv b).exists_bound_of_continuous
      (hg.continuous_iteratedFDeriv (by simp))
    exact ⟨max D 0, le_max_right _ _, fun L ↦ (hD L).trans (le_max_left _ _)⟩
  choose D hD hgD using hgBound
  let A' := ∑ u ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (k + 1), A u v
  have hA' : 0 ≤ A' := Finset.sum_nonneg (fun u _ ↦ Finset.sum_nonneg (fun v _ ↦ hA u v))
  have hAA' (u v : ℕ) (hu : u ≤ k) (hv : v ≤ k) : A u v ≤ A' := by
    have h₁ : A u v ≤ ∑ w ∈ Finset.range (k + 1), A u w :=
      Finset.single_le_sum (fun w _ ↦ hA u w) (Finset.mem_range.mpr (by omega))
    have h₂ : (∑ w ∈ Finset.range (k + 1), A u w) ≤ A' :=
      Finset.single_le_sum (fun w _ ↦ Finset.sum_nonneg (fun v _ ↦ hA w v))
        (Finset.mem_range.mpr (by omega))
    exact h₁.trans h₂
  let D' := 1 + 2 ^ k * A'
  have hD' : 1 ≤ D' := le_add_of_nonneg_right (mul_nonneg (by positivity) hA')
  let C' := ∑ b ∈ Finset.range (k + 1), D b
  have hC' : 0 ≤ C' := Finset.sum_nonneg (fun b _ ↦ hD b)
  have hDC' (b : ℕ) (hb : b ≤ k) : D b ≤ C' :=
    Finset.single_le_sum (fun c _ ↦ hD c) (Finset.mem_range.mpr (by omega))
  let C := k.factorial * C' * D' ^ k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x hx ξ hξ
  let t : ℝ := 1 + ‖ξ‖
  have ht : 0 < t := by dsimp [t]; positivity
  let c : ℝ := t ^ (-m)
  have hc : 0 < c := Real.rpow_pos_of_pos ht _
  let η : X := t⁻¹ • ξ
  have htη : t • η = ξ := smul_inv_smul₀ ht.ne' ξ
  let a' : X → X → (E →L[ℂ] F) := fun y ζ ↦ c • a y (t • ζ)
  have ha' : ContDiff ℝ ∞ (Function.uncurry a') := by
    change ContDiff ℝ ∞ (fun z : X × X ↦ c • a z.1 (t • z.2))
    exact (contDiff_const (c := c)).smul
      (hs.comp (contDiff_fst.prodMk ((contDiff_const (c := t)).smul contDiff_snd)))
  have hscaleInv (L : E →L[ℂ] F) : (c • L).inverse = c⁻¹ • L.inverse := by
    let e : F ≃L[ℂ] F := (Units.mk0 (c : ℂ) (by exact_mod_cast hc.ne')) •
      ContinuousLinearEquiv.refl ℂ F
    have he : c • L = (e : F →L[ℂ] F).comp L := by ext v; rfl
    rw [he, ContinuousLinearMap.inverse_equiv_comp]
    apply ContinuousLinearMap.ext
    intro v
    simp [e, ← Complex.ofReal_inv, Complex.coe_smul]
  have hnormA : ‖a' x η‖ ≤ A 0 0 := by
    have h := haA 0 0 x hx ξ
    simp only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero] at h
    change ‖c • a x (t • η)‖ ≤ _
    rw [htη, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    calc
      _ ≤ c * (A 0 0 * t ^ m) := mul_le_mul_of_nonneg_left h hc.le
      _ = A 0 0 := by
        dsimp [c]
        rw [mul_left_comm, ← Real.rpow_add ht]
        simp
  have hnormInv : ‖(a' x η).inverse‖ ≤ B := by
    change ‖(c • a x (t • η)).inverse‖ ≤ _
    rw [htη, hscaleInv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    calc
      _ ≤ c⁻¹ * (B * c) := mul_le_mul_of_nonneg_left (hbound x hx ξ hξ) (inv_nonneg.mpr hc.le)
      _ = B := by field_simp
  have haInv : (a' x η).IsInvertible := by
    obtain ⟨e, he⟩ := hinv x hx ξ hξ
    refine ⟨(Units.mk0 (c : ℂ) (by exact_mod_cast hc.ne')) • e, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    change (c : ℂ) • e v = c • a x (t • η) v
    rw [htη]
    exact congrArg (c • ·) (DFunLike.congr_fun he v)
  have hscaled (u v : ℕ) (hu : u ≤ k) (hv : v ≤ k) :
      ‖iteratedFDeriv ℝ u (fun y ↦ iteratedFDeriv ℝ v (a' y) η) x‖ ≤ A' := by
    rw [hMixedSmul _ c hc.ne',
      mixed_iteratedFDeriv_frequency_smul a t ht.ne' u v, htη,
      norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos ht v)]
    calc
      _ ≤ c * (t ^ v * (A u v * t ^ (m - (v : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (haA u v x hx ξ) (pow_nonneg ht.le _)) hc.le
      _ = A u v := by
        have hpow : t ^ v * t ^ (m - (v : ℝ)) = t ^ m := by
          rw [← Real.rpow_natCast, ← Real.rpow_add ht]
          congr 1
          ring
        calc
          _ = A u v * (c * (t ^ v * t ^ (m - (v : ℝ)))) := by ring
          _ = A u v := by
            rw [hpow]
            dsimp [c]
            rw [← Real.rpow_add ht]
            simp
      _ ≤ A' := hAA' u v hu hv
  have hinner (b : ℕ) (hb : 1 ≤ b) (hbk : b ≤ k) :
      ‖iteratedFDeriv ℝ b (Function.uncurry a') (x, η)‖ ≤ D' ^ b := by
    have h := norm_iteratedFDeriv_uncurry_le_of_mixed a' ha' b x η A' hA'
      (fun u hu v hv ↦ hscaled u v (hu.trans hbk) (hv.trans hbk))
    exact h.trans ((mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hbk) hA').trans
        ((le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ hD' (by omega))))
  have houter (b : ℕ) (hb : b ≤ k) :
      ‖iteratedFDeriv ℝ b g (Function.uncurry a' (x, η))‖ ≤ C' :=
    (hgD b _).trans (hDC' b hb)
  have hchain := norm_iteratedFDeriv_comp_le hg ha' (n := k) (by simp) (x, η) houter hinner
  let f : X → X → (F →L[ℂ] E) := fun y ζ ↦ g (a' y ζ)
  have hf : ContDiff ℝ ∞ (Function.uncurry f) := hg.comp ha'
  have hmixed := (norm_mixed_iteratedFDeriv_le f hf i j x η).trans hchain
  let q' : X → X → (F →L[ℂ] E) := fun y ζ ↦ c • f y ζ
  have hnear : Function.uncurry q' =ᶠ[𝓝 (x, η)]
      Function.uncurry (fun y ζ ↦ (a y (t • ζ)).inverse) := by
    have h := (hgeq (a' x η) haInv hnormA hnormInv).comp_tendsto
      (show Tendsto (Function.uncurry a') (𝓝 (x, η)) (𝓝 (a' x η)) from
        ha'.continuous.continuousAt)
    filter_upwards [h] with z hz
    change g (a' z.1 z.2) = (a' z.1 z.2).inverse at hz
    change c • g (a' z.1 z.2) = _
    rw [hz]
    change c • (c • a z.1 (t • z.2)).inverse = _
    rw [hscaleInv, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    rfl
  have hmixeq := hMixedEq q' (fun y ζ ↦ (a y (t • ζ)).inverse) x η hnear i j
  rw [hMixedSmul f c hc.ne',
    mixed_iteratedFDeriv_frequency_smul (fun y ζ ↦ (a y ζ).inverse) t ht.ne' i j, htη] at hmixeq
  have hn := congrArg norm hmixeq
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc,
    norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos ht j)] at hn
  have hfinal : t ^ j * ‖symbolDerivative (fun y ζ ↦ (a y ζ).inverse) i j x ξ‖ ≤ c * C := by
    unfold symbolDerivative
    rw [← hn]
    exact mul_le_mul_of_nonneg_left hmixed hc.le
  have hdivide : ‖symbolDerivative (fun y ζ ↦ (a y ζ).inverse) i j x ξ‖ ≤
      c * C / t ^ j := (le_div_iff₀ (pow_pos ht j)).mpr (by
        simpa only [mul_comm] using hfinal)
  have hpow : c * C / t ^ j = C * t ^ (-m - (j : ℝ)) := by
    rw [Real.rpow_sub ht, Real.rpow_natCast]
    dsimp [c]
    ring
  exact hdivide.trans_eq hpow

end AtiyahSinger
