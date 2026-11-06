/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.JointFrequencySymbolRestriction
public import AtiyahSinger.Analysis.NoncompactSymbolIntegral
public import AtiyahSinger.Analysis.ResolventWeightIntegral
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Fractional integration of a joint frequency symbol

Public module ID: M0771.

For 0 < p < 1, an actual symbol of order `-2-j` in one additional frequency coordinate produces
a symbol of order `-2p-j` after restriction to that coordinate's square root and
integration against `t⁻ᵖ dt`. Smoothness, parameter measurability, and local
integrable domination of all actual derivatives are derived from that same symbol.
The final frequency order uses the exact scalar resolvent-weight integral.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter MeasureTheory Set Topology
open scoped ContDiff Manifold

set_option maxSynthPendingDepth 25

private theorem contDiffAt_parameter_iteratedFDeriv
    {P X V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : P → X → V) (x : P) (y : X)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, y)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun z : P × X ↦ iteratedFDeriv ℝ k (f z.1) z.2) (x, y) := by
  induction k with
  | zero =>
    exact hf.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ X V).symm : _ →L[ℝ] X [×0]→L[ℝ] V)
  | succ k ih =>
    have h : ContDiffAt ℝ ∞
        (Function.uncurry (fun z : P × X ↦ fun η : X ↦
          iteratedFDeriv ℝ k (f z.1) η)) ((x, y), y) :=
      ih.comp ((x, y), y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞
        (fun z : P × X ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) (x, y) :=
      h.fderiv contDiffAt_snd (by simp)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) V).symm :
        _ →L[ℝ] X [×(k + 1)]→L[ℝ] V)

private theorem norm_iteratedFDeriv_uncurry_le_of_mixed_on
    {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : Set X} (hU : IsOpen U) (f : X → X → V)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    (k : ℕ) (x y : X) (hx : x ∈ U) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ i ≤ k, ∀ j ≤ k,
      ‖iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f z) y) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ k (Function.uncurry f) (x, y)‖ ≤ 2 ^ k * A := by
  -- A base cutoff preserves every frequency germ near x while giving global smoothness.
  obtain ⟨χ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (n := (⊤ : ℕ∞)) 𝓘(ℝ, X) hU.isClosed_compl (isClosed_singleton (x := x))
      (Set.disjoint_compl_left_iff_subset.mpr (singleton_subset_iff.mpr hx))
  have hχ : ContDiff ℝ ∞ χ := contMDiff_iff_contDiff.mp χ.contMDiff
  let f' : X → X → V := fun z η ↦ χ z • f z η
  have hf' : ContDiff ℝ ∞ (Function.uncurry f') := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z.1 ∈ U
    · exact (hχ.comp contDiff_fst).contDiffAt.smul
        (hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩))
    · apply (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
      have hzeroAt : χ =ᶠ[𝓝 z.1] (fun _ ↦ 0) :=
        hzero.filter_mono (nhds_le_nhdsSet hz)
      filter_upwards [hzeroAt.comp_tendsto continuous_fst.continuousAt] with w hw
      change χ w.1 = 0 at hw
      simp only [f', Function.uncurry, hw, zero_smul]
  have hnear : f' =ᶠ[𝓝 x] f := by
    have heq := hone.filter_mono (nhds_le_nhdsSet (mem_singleton x))
    filter_upwards [heq] with z hz
    funext η
    simp only [f', hz, one_smul]
  have hmixed (i j : ℕ) :
      iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f' z) y) x =
        iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f z) y) x := by
    have heq : (fun z ↦ iteratedFDeriv ℝ j (f' z) y) =ᶠ[𝓝 x]
        (fun z ↦ iteratedFDeriv ℝ j (f z) y) := by
      filter_upwards [hnear] with z hz
      rw [hz]
    exact (heq.iteratedFDeriv ℝ i).eq_of_nhds
  have hfull : Function.uncurry f' =ᶠ[𝓝 (x, y)] Function.uncurry f := by
    filter_upwards [hnear.comp_tendsto continuous_fst.continuousAt] with z hz
    exact congrFun hz z.2
  have h := norm_iteratedFDeriv_uncurry_le_of_mixed f' hf' k x y A hA
    (fun i hi j hj ↦ by rw [hmixed i j]; exact hbound i hi j hj)
  rwa [(hfull.iteratedFDeriv ℝ k).eq_of_nhds] at h

set_option maxHeartbeats 2000000 in

/-- Integrating the actual additional-frequency symbol gives the fractional symbol order. -/
theorem isSymbol_integral_jointFrequencySymbolSlice
    {n r q : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (a : SymbolFunction (n + 1) r q) (j : ℕ)
    (ha : IsSymbol ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd z).1) ⁻¹' U) (-2 - (j : ℝ)) a)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    IsSymbol U (-2 * p - (j : ℝ)) (fun x ξ ↦
      ∫ t in Ioi (0 : ℝ), t ^ (-p) • jointFrequencySymbolSlice a t x ξ) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin (n + 1))
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let e : Y ≃L[ℝ] X × EuclideanSpace ℝ (Fin 1) := EuclideanSpace.finAddEquivProd
  let W : Set Y := (fun z ↦ (e z).1) ⁻¹' U
  have hW : IsOpen W := hU.preimage (continuous_fst.comp e.continuous)
  let f : ℝ → SymbolFunction n r q := fun t x ξ ↦
    t ^ (-p) • jointFrequencySymbolSlice a t x ξ
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  -- Each spatial slice is smooth, including the parameter values outside the integration set.
  have hslice (t : ℝ) :
      ContDiffOn ℝ ∞ (Function.uncurry (jointFrequencySymbolSlice a t)) (U ×ˢ univ) := by
    change ContDiffOn ℝ ∞ (Function.uncurry a ∘ (fun z : X × X ↦
      (e.symm (z.1, 0), e.symm (z.2, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt t)))))
      (U ×ˢ univ)
    apply ha.1.comp
    · exact ((e.symm.contDiff.comp (contDiff_fst.prodMk contDiff_const)).prodMk
        (e.symm.contDiff.comp (contDiff_snd.prodMk contDiff_const))).contDiffOn
    · intro z hz
      refine ⟨?_, mem_univ _⟩
      change (e (e.symm (z.1, 0))).1 ∈ U
      simpa only [e.apply_symm_apply] using hz.1
  have hf (t : ℝ) : ContDiffOn ℝ ∞ (Function.uncurry (f t)) (U ×ˢ univ) :=
    (hslice t).const_smul (t ^ (-p))
  have hsmul (t : ℝ) (i b : ℕ) (x : X) (hx : x ∈ U) (ξ : X) :
      symbolDerivative (f t) i b x ξ =
        t ^ (-p) • symbolDerivative (jointFrequencySymbolSlice a t) i b x ξ := by
    have hs (y : X) (hy : y ∈ U) (η : X) :
        ContDiffAt ℝ ∞ (Function.uncurry (jointFrequencySymbolSlice a t)) (y, η) :=
      (hslice t).contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy, mem_univ _⟩)
    have hnear : (fun y ↦ iteratedFDeriv ℝ b (f t y) ξ) =ᶠ[𝓝 x]
        (fun y ↦ t ^ (-p) • iteratedFDeriv ℝ b (jointFrequencySymbolSlice a t y) ξ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact iteratedFDeriv_const_smul_apply (a := t ^ (-p))
        (((hs y hy ξ).comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
    have hparam := (contDiffAt_parameter_iteratedFDeriv
      (jointFrequencySymbolSlice a t) x ξ (hs x hx ξ) b).comp x
        (contDiffAt_id.prodMk contDiffAt_const)
    exact ((hnear.iteratedFDeriv ℝ i).eq_of_nhds).trans
      (iteratedFDeriv_const_smul_apply (a := t ^ (-p)) (hparam.of_le (by simp)))
  -- The original higher-dimensional estimates give precise mixed bounds for every positive t.
  have hbound (K : Set X) (hKU : K ⊆ U) (hK : IsCompact K) (i b : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ x ∈ K, ∀ ξ,
        ‖symbolDerivative (f t) i b x ξ‖ ≤
          C * (t ^ (-p) * (1 + ‖ξ‖ ^ 2 + t) ^ (-1 - ((j + b : ℕ) : ℝ) / 2)) := by
    obtain ⟨C, hC, hCb⟩ := exists_bound_jointFrequencySymbolSlice W hW
      (-2 - (j : ℝ)) a ha K hK (by
        rintro z ⟨x, hx, rfl⟩
        change (e (e.symm (x, 0))).1 ∈ U
        simpa only [e.apply_symm_apply] using hKU hx) i b
    refine ⟨C, hC, ?_⟩
    intro t ht x hx ξ
    rw [hsmul t i b x (hKU hx) ξ, norm_smul,
      Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
    have he : ((-2 - (j : ℝ)) - (b : ℝ)) / 2 =
        -1 - ((j + b : ℕ) : ℝ) / 2 := by push_cast; ring
    calc
      _ ≤ t ^ (-p) * (C *
          (1 + ‖ξ‖ ^ 2 + t) ^ (((-2 - (j : ℝ)) - (b : ℝ)) / 2)) :=
        mul_le_mul_of_nonneg_left (hCb t ht x hx ξ) (Real.rpow_nonneg ht.le _)
      _ = _ := by rw [he]; ring
  -- Joint parameter smoothness implies measurability of the actual parameterized derivatives.
  have hparam (t : ℝ) (ht : 0 < t) (z : X × X) (hz : z ∈ U ×ˢ univ) :
      ContDiffAt ℝ ∞ (fun w : ℝ × (X × X) ↦ f w.1 w.2.1 w.2.2) (t, z) := by
    have hbase : ContDiffAt ℝ ∞
        (fun w : ℝ × (X × X) ↦ e.symm (w.2.1, 0)) (t, z) :=
      e.symm.contDiff.contDiffAt.comp (t, z)
        (contDiffAt_snd.fst.prodMk contDiffAt_const)
    have hlast : ContDiffAt ℝ ∞ (fun w : ℝ × (X × X) ↦
        WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt w.1)) (t, z) :=
      (contDiffAt_piLp 2).2 (fun _ ↦ contDiffAt_fst.sqrt ht.ne')
    have hfreq : ContDiffAt ℝ ∞ (fun w : ℝ × (X × X) ↦
        e.symm (w.2.2, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt w.1))) (t, z) :=
      e.symm.contDiff.contDiffAt.comp (t, z) (contDiffAt_snd.snd.prodMk hlast)
    have haAt : ContDiffAt ℝ ∞ (Function.uncurry a)
        (e.symm (z.1, 0), e.symm (z.2, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt t))) :=
      ha.1.contDiffAt ((hW.prod isOpen_univ).mem_nhds ⟨by
        change (e (e.symm (z.1, 0))).1 ∈ U
        simpa only [e.apply_symm_apply] using hz.1, mem_univ _⟩)
    have hraw : ContDiffAt ℝ ∞ (Function.uncurry a ∘
        (fun w : ℝ × (X × X) ↦ (e.symm (w.2.1, 0),
          e.symm (w.2.2, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt w.1))))) (t, z) :=
      haAt.comp (t, z) (hbase.prodMk hfreq)
    change ContDiffAt ℝ ∞ (fun w : ℝ × (X × X) ↦ w.1 ^ (-p) •
      a (e.symm (w.2.1, 0))
        (e.symm (w.2.2, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt w.1)))) (t, z)
    exact (contDiffAt_fst.rpow_const_of_ne ht.ne').smul hraw
  have hmeasJoint (k : ℕ) (z : X × X) (hz : z ∈ U ×ˢ univ) :
      AEStronglyMeasurable
        (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (f t)) z) μ := by
    let _ : SecondCountableTopologyEither ℝ ((X × X) [×k]→L[ℝ] V) :=
      secondCountableTopologyEither_of_left _ _
    have hc : ContinuousOn
        (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (f t)) z) (Ioi 0) := by
      intro t ht
      have hd := contDiffAt_parameter_iteratedFDeriv
        (fun (t : ℝ) (z : X × X) ↦ f t z.1 z.2) t z (hparam t ht z hz) k
      exact (hd.comp t (contDiffAt_id.prodMk contDiffAt_const)).continuousAt.continuousWithinAt
    exact hc.aestronglyMeasurable measurableSet_Ioi
  have hmeasMixed (i b : ℕ) (z : X × X) (hz : z ∈ U ×ˢ univ) :
      AEStronglyMeasurable (fun t ↦ symbolDerivative (f t) i b z.1 z.2) μ := by
    let _ : SecondCountableTopologyEither ℝ (X [×i]→L[ℝ] X [×b]→L[ℝ] V) :=
      secondCountableTopologyEither_of_left _ _
    have hc : ContinuousOn (fun t ↦ symbolDerivative (f t) i b z.1 z.2) (Ioi 0) := by
      intro t ht
      have hfreq := contDiffAt_parameter_iteratedFDeriv
        (fun w : ℝ × X ↦ fun η : X ↦ f w.1 w.2 η) (t, z.1) z.2
        ((hparam t ht z hz).comp ((t, z.1), z.2)
          (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))) b
      have hbase := contDiffAt_parameter_iteratedFDeriv
        (fun w : ℝ × X ↦ fun x : X ↦ iteratedFDeriv ℝ b (f w.1 x) w.2) (t, z.2) z.1
        (hfreq.comp ((t, z.2), z.1)
          ((contDiffAt_fst.fst.prodMk contDiffAt_snd).prodMk contDiffAt_fst.snd)) i
      exact (hbase.comp t ((contDiffAt_id.prodMk contDiffAt_const).prodMk
        contDiffAt_const)).continuousAt.continuousWithinAt
    exact hc.aestronglyMeasurable measurableSet_Ioi
  -- A single integrable profile controls every derivative locally in the base, uniformly in ξ.
  let base : ℝ → ℝ := fun t ↦ t ^ (-p) * (1 + t) ^ (-1 : ℝ)
  have hbaseInt : Integrable base μ := by
    have h := ((resolvent_weight_integral p hp hp1 0).2 1 zero_lt_one).1
    change IntegrableOn base (Ioi 0)
    exact IntegrableOn.congr_fun h (fun t _ ↦ by
      dsimp only [base]
      norm_num) measurableSet_Ioi
  have hbaseNonneg (t : ℝ) (ht : 0 < t) : 0 ≤ base t :=
    mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (by linarith) _)
  have hweightLocal (t : ℝ) (ht : 0 < t) (ξ : X) (k : ℕ) :
      t ^ (-p) * (1 + ‖ξ‖ ^ 2 + t) ^ (-1 - (k : ℝ) / 2) ≤ base t := by
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
    calc
      _ ≤ (1 + t) ^ (-1 - (k : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by nlinarith [sq_nonneg ‖ξ‖])
          (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith)
      _ ≤ (1 + t) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith)
          (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hlocal (K : Set X) (hKU : K ⊆ U) (hK : IsCompact K) (i b : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ x ∈ K, ∀ ξ,
        ‖symbolDerivative (f t) i b x ξ‖ ≤ C * base t := by
    obtain ⟨C, hC, hCb⟩ := hbound K hKU hK i b
    exact ⟨C, hC, fun t ht x hx ξ ↦ (hCb t ht x hx ξ).trans
      (mul_le_mul_of_nonneg_left (hweightLocal t ht ξ (j + b)) hC)⟩
  have hdomMixed (i b : ℕ) (z : X × X) (hz : z ∈ U ×ˢ univ) :
      ∃ S : Set (X × X), S ∈ 𝓝 z ∧ S ⊆ U ×ˢ univ ∧
        ∃ B : ℝ → ℝ, Integrable B μ ∧
          ∀ᵐ t ∂μ, ∀ w ∈ S, ‖symbolDerivative (f t) i b w.1 w.2‖ ≤ B t := by
    obtain ⟨K, hK, hzK, hKU⟩ := exists_compact_subset hU hz.1
    obtain ⟨C, _, hC⟩ := hlocal K hKU hK i b
    refine ⟨interior K ×ˢ univ,
      (isOpen_interior.prod isOpen_univ).mem_nhds ⟨hzK, mem_univ _⟩,
      prod_mono (interior_subset.trans hKU) subset_rfl,
      fun t ↦ C * base t, hbaseInt.const_mul C, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    exact hC t ht w.1 (interior_subset hw.1) w.2
  have hdomJoint (k : ℕ) (z : X × X) (hz : z ∈ U ×ˢ univ) :
      ∃ S : Set (X × X), S ∈ 𝓝 z ∧ S ⊆ U ×ˢ univ ∧
        ∃ B : ℝ → ℝ, Integrable B μ ∧
          ∀ᵐ t ∂μ, ∀ w ∈ S, ‖iteratedFDeriv ℝ k (Function.uncurry (f t)) w‖ ≤ B t := by
    obtain ⟨K, hK, hzK, hKU⟩ := exists_compact_subset hU hz.1
    choose C hC hCb using hlocal K hKU hK
    let D : ℝ := ∑ i ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1), C i b
    have hD : 0 ≤ D := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun b _ ↦ hC i b
    have hCD (i : ℕ) (hi : i ≤ k) (b : ℕ) (hb : b ≤ k) : C i b ≤ D := by
      exact (Finset.single_le_sum (fun c _ ↦ hC i c)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hb))).trans
        (Finset.single_le_sum
          (fun c _ ↦ Finset.sum_nonneg fun d _ ↦ hC c d)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
    refine ⟨interior K ×ˢ univ,
      (isOpen_interior.prod isOpen_univ).mem_nhds ⟨hzK, mem_univ _⟩,
      prod_mono (interior_subset.trans hKU) subset_rfl,
      fun t ↦ (2 ^ k * D) * base t, hbaseInt.const_mul _, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    have hb := norm_iteratedFDeriv_uncurry_le_of_mixed_on hU (f t) (hf t)
      k w.1 w.2 (hKU (interior_subset hw.1)) (D * base t)
      (mul_nonneg hD (hbaseNonneg t ht)) (fun i hi b hb ↦
        (hCb i b t ht w.1 (interior_subset hw.1) w.2).trans
          (mul_le_mul_of_nonneg_right (hCD i hi b hb) (hbaseNonneg t ht)))
    simpa only [mul_assoc] using hb
  apply isSymbol_integral_of_locally_dominated_jets μ hU f hf
    hmeasMixed hdomMixed hmeasJoint hdomJoint
  -- Integrate the precise frequency majorant before forming the final symbol seminorm.
  intro K hKU hK i b
  obtain ⟨C, hC, hCb⟩ := hbound K hKU hK i b
  let d : ℝ := -1 - ((j + b : ℕ) : ℝ) / 2
  let D : ℝ := ∫ u in Ioi (0 : ℝ), u ^ (-p) * (1 + u) ^ d
  obtain ⟨hD, hDall⟩ := resolvent_weight_integral p hp hp1 (j + b)
  have hd : d ≤ 0 := by dsimp [d]; have hk := Nat.cast_nonneg (α := ℝ) (j + b); linarith
  refine ⟨C * 2 ^ (-d) * D, mul_nonneg (mul_nonneg hC (by positivity)) hD, ?_⟩
  intro ξ
  let ρ : ℝ := 1 + ‖ξ‖
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨hI, hIe⟩ := hDall ρ hρ
  let J : ℝ → ℝ := fun t ↦ t ^ (-p) * (ρ ^ 2 + t) ^ d
  refine ⟨fun t ↦ (C * 2 ^ (-d)) * J t, hI.const_mul _, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro x hx
    have ht0 : 0 < t := ht
    have hE : 0 < ρ ^ 2 + t := add_pos (pow_pos hρ 2) ht
    have hhalf : (ρ ^ 2 + t) / 2 ≤ 1 + ‖ξ‖ ^ 2 + t := by
      dsimp [ρ]
      nlinarith only [ht0, sq_nonneg (‖ξ‖ - 1)]
    have hbracket : (1 + ‖ξ‖ ^ 2 + t) ^ d ≤ 2 ^ (-d) * (ρ ^ 2 + t) ^ d := by
      calc
        _ ≤ ((ρ ^ 2 + t) / 2) ^ d :=
          Real.rpow_le_rpow_of_nonpos (half_pos hE) hhalf hd
        _ = 2 ^ (-d) * (ρ ^ 2 + t) ^ d := by
          rw [div_eq_mul_inv, Real.mul_rpow hE.le (by norm_num),
            ← Real.rpow_neg_eq_inv_rpow (2 : ℝ) d]
          ring
    calc
      _ ≤ C * (t ^ (-p) * (1 + ‖ξ‖ ^ 2 + t) ^ d) := hCb t ht x hx ξ
      _ ≤ C * (t ^ (-p) * (2 ^ (-d) * (ρ ^ 2 + t) ^ d)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbracket (Real.rpow_nonneg ht.le _)) hC
      _ = (C * 2 ^ (-d)) * J t := by dsimp [J]; ring
  · change (∫ t in Ioi (0 : ℝ), (C * 2 ^ (-d)) * J t) ≤
      C * 2 ^ (-d) * D * (1 + ‖ξ‖) ^ ((-2 * p - (j : ℝ)) - (b : ℝ))
    rw [integral_const_mul]
    change C * 2 ^ (-d) * (∫ t in Ioi (0 : ℝ),
      t ^ (-p) * (ρ ^ 2 + t) ^ (-1 - ((j + b : ℕ) : ℝ) / 2)) ≤ _
    rw [hIe]
    have he : -2 * p - ((j + b : ℕ) : ℝ) = (-2 * p - (j : ℝ)) - (b : ℝ) := by
      push_cast
      ring
    rw [he]
    change C * 2 ^ (-d) * (D * ρ ^ ((-2 * p - (j : ℝ)) - (b : ℝ))) ≤
      C * 2 ^ (-d) * D * ρ ^ ((-2 * p - (j : ℝ)) - (b : ℝ))
    exact le_of_eq (mul_assoc _ _ _).symm

end AtiyahSinger
