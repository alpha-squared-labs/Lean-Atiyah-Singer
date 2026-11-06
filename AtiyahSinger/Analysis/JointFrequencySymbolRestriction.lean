/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SymbolCoordinateEstimates
public import AtiyahSinger.Analysis.SymbolQuotient

/-!
# Restricting a symbol along an additional frequency parameter

Public module ID: M0772.

The actual symbol on one more Euclidean coordinate is evaluated at base point `(x, 0)`
and frequency `(ξ, √τ)`. Its mixed derivatives retain the precise loss in frequency order,
uniformly for every positive parameter. The input is an ordinary higher-dimensional symbol;
the parameter-dependent estimate is proved by restriction of its derivatives.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff Manifold Topology

set_option maxSynthPendingDepth 20

/-- The original symbol restricted to base `(x, 0)` and frequency `(ξ, √τ)`. -/
def jointFrequencySymbolSlice {n r q : ℕ} (a : SymbolFunction (n + 1) r q)
    (τ : ℝ) : SymbolFunction n r q :=
  fun x ξ ↦ a (EuclideanSpace.finAddEquivProd.symm (x, 0))
    (EuclideanSpace.finAddEquivProd.symm
      (ξ, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt τ)))

/-- The Euclidean splitting has the square-sum norm of its two coordinate blocks. -/
private theorem norm_finAddEquivProd_symm_sq {n k : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin k)) :
    ‖EuclideanSpace.finAddEquivProd.symm (x, y)‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  let e : EuclideanSpace ℝ (Fin (n + k)) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
      (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin k ↦ ℝ))
  change ‖e.symm (WithLp.toLp 2 (x, y))‖ ^ 2 = _
  rw [e.symm.norm_map, WithLp.prod_norm_sq_eq_of_L2]
  rfl

/-- Fixed affine restrictions contract both levels of the original mixed derivative. -/
private theorem norm_mixed_iteratedFDeriv_comp_affine_le
    {X Y V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Y → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (L : X →L[ℝ] Y) (hL : ‖L‖ ≤ 1) (c : Y) (i j : ℕ) (x ξ : X) :
    ‖iteratedFDeriv ℝ i
      (fun z ↦ iteratedFDeriv ℝ j (fun η ↦ f (L z) (c + L η)) ξ) x‖ ≤
      ‖iteratedFDeriv ℝ i
        (fun z ↦ iteratedFDeriv ℝ j (f z) (c + L ξ)) (L x)‖ := by
  -- Smooth dependence of the frequency jet on both original variables.
  have hpartial (k : ℕ) : ContDiff ℝ ∞
      (fun z : Y × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
    induction k with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Y V).symm : _ →L[ℝ] Y [×0]→L[ℝ] V)
    | succ k ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : Y × Y ↦ fun η : Y ↦
            iteratedFDeriv ℝ k (f z.1) η)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : Y × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) V).symm :
          _ →L[ℝ] Y [×(k + 1)]→L[ℝ] V)
  let T : (Y [×j]→L[ℝ] V) →L[ℝ] (X [×j]→L[ℝ] V) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j ↦ L)
  have hT : ‖T‖ ≤ 1 :=
    (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le V _).trans
      (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hL))
  -- Restrict the frequency derivative before differentiating in the base variable.
  have hfrequency (z : Y) :
      iteratedFDeriv ℝ j (fun η ↦ f z (c + L η)) ξ =
        T (iteratedFDeriv ℝ j (f z) (c + L ξ)) := by
    let g : Y → V := fun η ↦ f z (c + η)
    have hg : ContDiff ℝ ∞ g :=
      hf.comp (contDiff_const.prodMk (contDiff_const.add contDiff_id))
    change iteratedFDeriv ℝ j (g ∘ L) ξ = _
    rw [L.iteratedFDeriv_comp_right hg ξ (by simp)]
    change (iteratedFDeriv ℝ j (fun η ↦ f z (c + η)) (L ξ)).compContinuousLinearMap _ = _
    rw [iteratedFDeriv_comp_add_left]
    rfl
  let G : Y → Y [×j]→L[ℝ] V := fun z ↦ iteratedFDeriv ℝ j (f z) (c + L ξ)
  have hG : ContDiff ℝ ∞ G :=
    (hpartial j).comp (contDiff_id.prodMk contDiff_const)
  have hbase : ‖iteratedFDeriv ℝ i (G ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ i G (L x)‖ := by
    rw [L.iteratedFDeriv_comp_right hG x (by simp)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    have hprod : (∏ _ : Fin i, ‖L‖) ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hL)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod
      (norm_nonneg (iteratedFDeriv ℝ i G (L x)))
  simp_rw [hfrequency]
  change ‖iteratedFDeriv ℝ i (T ∘ (G ∘ L)) x‖ ≤ ‖iteratedFDeriv ℝ i G (L x)‖
  exact (T.norm_iteratedFDeriv_comp_left (hG.comp L.contDiff).contDiffAt (by simp)).trans
    ((mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans (by simpa using hbase))

/-- Replacing the linear Japanese bracket by its quadratic version works for every real order. -/
private theorem one_add_rpow_le_two_rpow_mul_quadratic
    (R s : ℝ) (hR : 0 ≤ R) :
    (1 + R) ^ s ≤ 2 ^ |s| * (1 + R ^ 2) ^ (s / 2) := by
  let b := Real.sqrt (1 + R ^ 2)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hbsq : b ^ 2 = 1 + R ^ 2 := Real.sq_sqrt (by positivity)
  have hb1 : 1 ≤ b := by nlinarith
  have hbR : R ≤ b := by nlinarith
  have hab : 1 + R ≤ 2 * b := by linarith
  have hba : b ≤ 2 * (1 + R) := by nlinarith
  have hb : 0 < b := zero_lt_one.trans_le hb1
  have ha : 0 < 1 + R := by positivity
  rw [Real.rpow_div_two_eq_sqrt s (by positivity)]
  change (1 + R) ^ s ≤ 2 ^ |s| * b ^ s
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hb.le]
    exact Real.rpow_le_rpow ha.le hab hs
  · have hs' : s ≤ 0 := (lt_of_not_ge hs).le
    have hcomp : (2 * (1 + R)) ^ s ≤ b ^ s :=
      Real.rpow_le_rpow_of_nonpos hb hba hs'
    calc
      (1 + R) ^ s = 2 ^ |s| * (2 * (1 + R)) ^ s := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha.le, abs_of_nonpos hs',
          ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel,
          Real.rpow_zero, one_mul]
      _ ≤ 2 ^ |s| * b ^ s := mul_le_mul_of_nonneg_left hcomp (by positivity)

/-- An ordinary symbol in one more dimension gives parameter-uniform mixed derivative estimates.
The constant is independent of the positive parameter, base point, and frequency. -/
theorem exists_bound_jointFrequencySymbolSlice
    {n r q : ℕ} (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hW : IsOpen W)
    (m : ℝ) (a : SymbolFunction (n + 1) r q) (ha : IsSymbol W m a)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKW : (fun x : EuclideanSpace ℝ (Fin n) ↦
      EuclideanSpace.finAddEquivProd.symm (x, (0 : EuclideanSpace ℝ (Fin 1)))) '' K ⊆ W)
    (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ x ∈ K, ∀ ξ,
      ‖symbolDerivative (jointFrequencySymbolSlice a τ) i j x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2 + τ) ^ ((m - (j : ℝ)) / 2) := by
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin (n + 1))
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let split : Y ≃L[ℝ] X × EuclideanSpace ℝ (Fin 1) := EuclideanSpace.finAddEquivProd
  let L : X →L[ℝ] Y :=
    split.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ X _)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro x
    have hs : ‖L x‖ ^ 2 = ‖x‖ ^ 2 := by
      change ‖split.symm (x, 0)‖ ^ 2 = ‖x‖ ^ 2
      simpa only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] using
        norm_finAddEquivProd_symm_sq x (0 : EuclideanSpace ℝ (Fin 1))
    have hn : ‖L x‖ = ‖x‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
    simp only [hn, one_mul, le_refl]
  have hLK : IsCompact (L '' K) := hK.image L.continuous
  have hLKW : L '' K ⊆ W := hKW
  -- Extend smoothly without changing any base germ above the specified compact set.
  obtain ⟨χ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (n := (⊤ : ℕ∞)) 𝓘(ℝ, Y) hW.isClosed_compl hLK.isClosed
      (Set.disjoint_compl_left_iff_subset.mpr hLKW)
  have hχ : ContDiff ℝ ∞ χ := contMDiff_iff_contDiff.mp χ.contMDiff
  let a' : Y → Y → V := fun z η ↦ χ z • a z η
  have ha' : ContDiff ℝ ∞ (Function.uncurry a') := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z.1 ∈ W
    · exact (hχ.comp contDiff_fst).contDiffAt.smul
        (ha.1.contDiffAt ((hW.prod isOpen_univ).mem_nhds ⟨hz, Set.mem_univ _⟩))
    · apply (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
      have hzeroAt : χ =ᶠ[nhds z.1] (fun _ ↦ 0) :=
        hzero.filter_mono (nhds_le_nhdsSet hz)
      have heq := hzeroAt.comp_tendsto continuous_fst.continuousAt
      filter_upwards [heq] with w hw
      change χ w.1 = 0 at hw
      simp only [a', Function.uncurry, hw, zero_smul]
  have hae (x : X) (hx : x ∈ K) : a' =ᶠ[nhds (L x)] a := by
    have heq := hone.filter_mono (nhds_le_nhdsSet (show L x ∈ L '' K from ⟨x, hx, rfl⟩))
    filter_upwards [heq] with z hz
    funext η
    simp only [a', hz, one_smul]
  obtain ⟨C₀, hC₀, hbound⟩ := ha.2 (L '' K) hLKW hLK i j
  refine ⟨C₀ * 2 ^ |m - (j : ℝ)|, mul_nonneg hC₀ (by positivity), ?_⟩
  intro τ hτ x hx ξ
  let t : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt τ)
  let c : Y := split.symm (0, t)
  have hfreq (η : X) : c + L η = split.symm (η, t) := by
    change split.symm (0, t) + split.symm (η, 0) = _
    rw [← map_add]
    simp
  -- The same ambient derivative controls the restricted derivative, with no order loss.
  have hder : ‖symbolDerivative (jointFrequencySymbolSlice a τ) i j x ξ‖ ≤
      ‖symbolDerivative a i j (L x) (split.symm (ξ, t))‖ := by
    have hs := norm_mixed_iteratedFDeriv_comp_affine_le a' ha' L hL c i j x ξ
    have hebase : (fun z ↦ iteratedFDeriv ℝ j (a' z) (c + L ξ)) =ᶠ[nhds (L x)]
        (fun z ↦ iteratedFDeriv ℝ j (a z) (c + L ξ)) := by
      filter_upwards [hae x hx] with z hz
      rw [hz]
    rw [(hebase.iteratedFDeriv ℝ i).eq_of_nhds] at hs
    have helocal : (fun z η ↦ a' (L z) (c + L η)) =ᶠ[nhds x]
        jointFrequencySymbolSlice a τ := by
      filter_upwards [(hae x hx).comp_tendsto L.continuous.continuousAt] with z hz
      change a' (L z) = a (L z) at hz
      funext η
      rw [hz, hfreq]
      rfl
    have hemixed : (fun z ↦ iteratedFDeriv ℝ j (fun η ↦ a' (L z) (c + L η)) ξ)
        =ᶠ[nhds x] (fun z ↦ iteratedFDeriv ℝ j (jointFrequencySymbolSlice a τ z) ξ) := by
      filter_upwards [helocal] with z hz
      rw [hz]
    rw [(hemixed.iteratedFDeriv ℝ i).eq_of_nhds, hfreq] at hs
    exact hs
  -- The parameter enters the actual Euclidean norm as the last squared coordinate.
  have ht : ‖t‖ ^ 2 = τ := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [t, Fin.sum_univ_one]
    exact Real.sq_sqrt hτ.le
  have hnorm : ‖split.symm (ξ, t)‖ ^ 2 = ‖ξ‖ ^ 2 + τ := by
    rw [norm_finAddEquivProd_symm_sq, ht]
  have hweight := one_add_rpow_le_two_rpow_mul_quadratic
    ‖split.symm (ξ, t)‖ (m - (j : ℝ)) (norm_nonneg _)
  rw [hnorm, ← add_assoc] at hweight
  calc
    ‖symbolDerivative (jointFrequencySymbolSlice a τ) i j x ξ‖ ≤
        ‖symbolDerivative a i j (L x) (split.symm (ξ, t))‖ := hder
    _ ≤ C₀ * (1 + ‖split.symm (ξ, t)‖) ^ (m - (j : ℝ)) :=
      hbound (L x) ⟨x, hx, rfl⟩ (split.symm (ξ, t))
    _ ≤ C₀ * (2 ^ |m - (j : ℝ)| *
        (1 + ‖ξ‖ ^ 2 + τ) ^ ((m - (j : ℝ)) / 2)) :=
      mul_le_mul_of_nonneg_left hweight hC₀
    _ = _ := by ring

end AtiyahSinger
