/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSobolev
public import AtiyahSinger.Analysis.JointFrequencyQuantizationBound
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Operator-norm continuity of the real joint-frequency quantizer

Public module ID: M0768.

The real last-frequency parameter is retained before composition with its square
root. A uniform lower-order symbol bound gives continuity in the symbol topology
with one order of slack, using a compact frequency window and a uniform tail.
The quantizer uses the same spatial cutoff and the original Sobolev coordinates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter MeasureTheory Set Topology
open scoped ContDiff Manifold NNReal SchwartzMap

attribute [local instance] symbolTopology

set_option maxSynthPendingDepth 25

/-- Restrict the original symbol at the specified real last-frequency coordinate. -/
def realFrequencySymbolSlice {n r q : ℕ} (a : SymbolFunction (n + 1) r q)
    (τ : ℝ) : SymbolFunction n r q :=
  fun x ξ ↦ a (EuclideanSpace.finAddEquivProd.symm (x, 0))
    (EuclideanSpace.finAddEquivProd.symm (ξ, WithLp.toLp 2 (fun _ : Fin 1 ↦ τ)))

/-- Restricting the same symbol at a real frequency gives uniform mixed bounds.
The constant is independent of the real parameter, base point, and frequency. -/
private theorem exists_bound_realFrequencySymbolSlice
    {n r q : ℕ} (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hW : IsOpen W)
    (m : ℝ) (hm : m ≤ 0) (a : SymbolFunction (n + 1) r q) (ha : IsSymbol W m a)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKW : (fun x : EuclideanSpace ℝ (Fin n) ↦
      EuclideanSpace.finAddEquivProd.symm (x, (0 : EuclideanSpace ℝ (Fin 1)))) '' K ⊆ W)
    (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ∀ x ∈ K, ∀ ξ,
      ‖symbolDerivative (realFrequencySymbolSlice a τ) i j x ξ‖ ≤
        C * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
  -- These restrictions are local tools for the same fixed-slice estimate.
  have hnormSplit {n k : ℕ}
      (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin k)) :
      ‖EuclideanSpace.finAddEquivProd.symm (x, y)‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    let e : EuclideanSpace ℝ (Fin (n + k)) ≃ₗᵢ[ℝ]
        WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) :=
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
        (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin k ↦ ℝ))
    change ‖e.symm (WithLp.toLp 2 (x, y))‖ ^ 2 = _
    rw [e.symm.norm_map, WithLp.prod_norm_sq_eq_of_L2]
    rfl
  have hmixedRestrict
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
        hnormSplit x (0 : EuclideanSpace ℝ (Fin 1))
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
  refine ⟨C₀, hC₀, ?_⟩
  intro τ x hx ξ
  let t : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ : Fin 1 ↦ τ)
  let c : Y := split.symm (0, t)
  have hfreq (η : X) : c + L η = split.symm (η, t) := by
    change split.symm (0, t) + split.symm (η, 0) = _
    rw [← map_add]
    simp
  -- The same ambient derivative controls the restricted derivative, with no order loss.
  have hder : ‖symbolDerivative (realFrequencySymbolSlice a τ) i j x ξ‖ ≤
      ‖symbolDerivative a i j (L x) (split.symm (ξ, t))‖ := by
    have hs := hmixedRestrict a' ha' L hL c i j x ξ
    have hebase : (fun z ↦ iteratedFDeriv ℝ j (a' z) (c + L ξ)) =ᶠ[nhds (L x)]
        (fun z ↦ iteratedFDeriv ℝ j (a z) (c + L ξ)) := by
      filter_upwards [hae x hx] with z hz
      rw [hz]
    rw [(hebase.iteratedFDeriv ℝ i).eq_of_nhds] at hs
    have helocal : (fun z η ↦ a' (L z) (c + L η)) =ᶠ[nhds x]
        realFrequencySymbolSlice a τ := by
      filter_upwards [(hae x hx).comp_tendsto L.continuous.continuousAt] with z hz
      change a' (L z) = a (L z) at hz
      funext η
      rw [hz, hfreq]
      rfl
    have hemixed : (fun z ↦ iteratedFDeriv ℝ j (fun η ↦ a' (L z) (c + L η)) ξ)
        =ᶠ[nhds x] (fun z ↦ iteratedFDeriv ℝ j (realFrequencySymbolSlice a τ z) ξ) := by
      filter_upwards [helocal] with z hz
      rw [hz]
    rw [(hemixed.iteratedFDeriv ℝ i).eq_of_nhds, hfreq] at hs
    exact hs
  -- The horizontal frequency norm never exceeds the full Euclidean frequency norm.
  have hnorm : ‖ξ‖ ≤ ‖split.symm (ξ, t)‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hnormSplit]
    nlinarith [sq_nonneg ‖t‖]
  have hexp : m - (j : ℝ) ≤ 0 := sub_nonpos.mpr (hm.trans (Nat.cast_nonneg _))
  calc
    ‖symbolDerivative (realFrequencySymbolSlice a τ) i j x ξ‖ ≤
        ‖symbolDerivative a i j (L x) (split.symm (ξ, t))‖ := hder
    _ ≤ C₀ * (1 + ‖split.symm (ξ, t)‖) ^ (m - (j : ℝ)) :=
      hbound (L x) ⟨x, hx, rfl⟩ (split.symm (ξ, t))
    _ ≤ C₀ * (1 + ‖ξ‖) ^ (m - (j : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hexp) hC₀

/-- Mixed derivatives remain smooth in the parameter and both original variables. -/
private theorem raw_contDiffAt_parameter_mixed_iteratedFDeriv
    {P X V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : P → X → X → V) (p : P) (x ξ : X)
    (hf : ContDiffAt ℝ ∞ (fun w : P × (X × X) ↦ f w.1 w.2.1 w.2.2) (p, (x, ξ)))
    (i j : ℕ) :
    ContDiffAt ℝ ∞ (fun w : P × (X × X) ↦
      iteratedFDeriv ℝ i (fun y : X ↦ iteratedFDeriv ℝ j (f w.1 y) w.2.2) w.2.1)
      (p, (x, ξ)) := by
  -- The local derivative induction keeps the multilinear target abstract.
  have hparameter
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
  -- Keep the higher derivative target abstract while changing the parameter grouping twice.
  have hfreq : ContDiffAt ℝ ∞ (fun v : (P × X) × X ↦
      iteratedFDeriv ℝ j (f v.1.1 v.1.2) v.2) ((p, x), ξ) :=
    hparameter
      (fun v : P × X ↦ fun η : X ↦ f v.1 v.2 η) (p, x) ξ
      (hf.comp ((p, x), ξ)
        (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))) j
  have hbase : ContDiffAt ℝ ∞ (fun v : (P × X) × X ↦
      iteratedFDeriv ℝ i (fun y : X ↦ iteratedFDeriv ℝ j (f v.1.1 y) v.1.2) v.2)
      ((p, ξ), x) :=
    hparameter
      (fun v : P × X ↦ fun y : X ↦ iteratedFDeriv ℝ j (f v.1 y) v.2)
      (p, ξ) x (hfreq.comp ((p, ξ), x)
        ((contDiffAt_fst.fst.prodMk contDiffAt_snd).prodMk contDiffAt_fst.snd)) i
  exact hbase.comp (p, (x, ξ))
    ((contDiffAt_fst.prodMk contDiffAt_snd.snd).prodMk contDiffAt_snd.fst)

private theorem raw_symbolDerivative_sub {n r q : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (f g : SymbolFunction n r q)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ))
    (i j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    symbolDerivative (f - g) i j x ξ =
      symbolDerivative f i j x ξ - symbolDerivative g i j x ξ := by
  -- Smoothness of the frequency jet is a local input to this subtraction identity.
  have hparameter
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
  have hs (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U) :
      ContDiffAt ℝ ∞ (Function.uncurry f) (y, ξ) ∧
        ContDiffAt ℝ ∞ (Function.uncurry g) (y, ξ) :=
    ⟨hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy, mem_univ _⟩),
      hg.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy, mem_univ _⟩)⟩
  have hnear : (fun y ↦ iteratedFDeriv ℝ j ((f - g) y) ξ) =ᶠ[𝓝 x]
      (fun y ↦ iteratedFDeriv ℝ j (f y) ξ - iteratedFDeriv ℝ j (g y) ξ) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact iteratedFDeriv_sub_apply
      (((hs y hy).1.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
      (((hs y hy).2.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
  have hfj := (hparameter f x ξ (hs x hx).1 j).comp x
    (contDiffAt_id.prodMk contDiffAt_const)
  have hgj := (hparameter g x ξ (hs x hx).2 j).comp x
    (contDiffAt_id.prodMk contDiffAt_const)
  exact ((hnear.iteratedFDeriv ℝ i).eq_of_nhds).trans
    (iteratedFDeriv_sub_apply (hfj.of_le (by simp)) (hgj.of_le (by simp)))

/-- A compact window and one uniform vanishing tail give uniform convergence in the parameter. -/
private theorem eventually_uniform_norm_sub_le_of_uniform_tail
    {X V : Type} [NormedAddCommGroup X] [ProperSpace X] [NormedAddCommGroup V]
    (K : Set X) (hK : IsCompact K) (G : ℝ → X × X → V)
    (hG : ContinuousOn (fun w : ℝ × (X × X) ↦ G w.1 w.2)
      (univ ×ˢ (K ×ˢ univ))) (C : ℝ) (t₀ : ℝ)
    (htail : ∀ t : ℝ, ∀ x ∈ K, ∀ ξ : X,
      ‖G t (x, ξ) - G t₀ (x, ξ)‖ ≤ C / (1 + ‖ξ‖))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ x ∈ K, ∀ ξ : X, ‖G t (x, ξ) - G t₀ (x, ξ)‖ ≤ ε := by
  -- The target is abstract here, so compact-map continuity uses only its normed-group structure.
  let R : ℝ := C / ε + 1
  have hlarge (ξ : X) (hξ : R < ‖ξ‖) : C / (1 + ‖ξ‖) < ε := by
    have hlt : C / ε < ‖ξ‖ := by dsimp [R] at hξ; linarith
    have hmul := (div_lt_iff₀ hε).mp hlt
    apply (div_lt_iff₀ (by positivity : 0 < 1 + ‖ξ‖)).mpr
    nlinarith
  let S : Set (X × X) := K ×ˢ Metric.closedBall 0 R
  have hS : IsCompact S := hK.prod (isCompact_closedBall 0 R)
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hGS : Continuous (fun w : ℝ × S ↦ G w.1 w.2.val) :=
    hG.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun w ↦ ⟨mem_univ _, w.2.property.1, mem_univ _⟩)
  let family : ℝ → C(S, V) := fun t ↦
    ⟨fun z ↦ G t z.val, hGS.comp (continuous_const.prodMk continuous_id)⟩
  have hfamily : Continuous family :=
    ContinuousMap.continuous_of_continuous_uncurry family hGS
  have hnear : ∀ᶠ t in 𝓝 t₀, ‖family t - family t₀‖ < ε :=
    (isOpen_lt (hfamily.sub continuous_const).norm continuous_const).mem_nhds
      (by
        change ‖family t₀ - family t₀‖ < ε
        simpa only [sub_self, norm_zero] using hε)
  filter_upwards [hnear] with t ht
  intro x hx ξ
  by_cases hξ : ‖ξ‖ ≤ R
  · have hz : (x, ξ) ∈ S := ⟨hx, mem_closedBall_zero_iff.mpr hξ⟩
    exact ((family t - family t₀).norm_coe_le_norm ⟨(x, ξ), hz⟩).trans ht.le
  · exact ((htail t x hx ξ).trans_lt (hlarge ξ (lt_of_not_ge hξ))).le

set_option maxHeartbeats 4000000 in

private theorem continuous_symbolFamily_with_order_slack {n r q : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (m : ℝ)
    (f : ℝ → SymbolFunction n r q) (hf : ∀ t, IsSymbol U m (f t))
    (hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n)), K ⊆ U → IsCompact K →
      ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ∀ x ∈ K, ∀ ξ,
        ‖symbolDerivative (f t) i j x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - (j : ℝ)))
    (hjets : ∀ i j : ℕ, ContinuousOn (fun w : ℝ ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        symbolDerivative (f w.1) i j w.2.1 w.2.2) (univ ×ˢ (U ×ˢ univ))) :
    Continuous (fun t ↦ (⟨f t, (hf t).mono (by linarith)⟩ :
      symbolSpace U hU (m + 1) r q)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let p (t : ℝ) : symbolSpace U hU (m + 1) r q :=
    ⟨f t, (hf t).mono (by linarith)⟩
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply (tendsto_symbolTopology_iff hU (m + 1) (𝓝 t₀) p (p t₀)).mpr
  intro J ε hε
  obtain ⟨C, _, hCb⟩ := hbound J.compactSet J.subset_domain J.isCompact
    J.spatialOrder J.frequencyOrder
  let d : ℝ := (m + 1) - (J.frequencyOrder : ℝ)
  let G (t : ℝ) (z : X × X) :
      X [×J.spatialOrder]→L[ℝ] X [×J.frequencyOrder]→L[ℝ] V := (1 + ‖z.2‖) ^ (-d) •
    symbolDerivative (f t) J.spatialOrder J.frequencyOrder z.1 z.2
  have hnorm (t : ℝ) (z : X × X) :
      ‖G t z - G t₀ z‖ =
        ‖symbolDerivative (f t) J.spatialOrder J.frequencyOrder z.1 z.2 -
          symbolDerivative (f t₀) J.spatialOrder J.frequencyOrder z.1 z.2‖ /
          (1 + ‖z.2‖) ^ d := by
    dsimp only [G]
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Real.rpow_neg (by positivity), div_eq_mul_inv, mul_comm]
  -- The one-order gap makes the frequency tail uniformly small for every parameter.
  have htail (t : ℝ) (x : X) (hx : x ∈ J.compactSet) (ξ : X) :
      ‖G t (x, ξ) - G t₀ (x, ξ)‖ ≤ (2 * C) / (1 + ‖ξ‖) := by
    rw [hnorm]
    have hnum :
        ‖symbolDerivative (f t) J.spatialOrder J.frequencyOrder x ξ -
          symbolDerivative (f t₀) J.spatialOrder J.frequencyOrder x ξ‖ ≤
          (2 * C) * (1 + ‖ξ‖) ^ (m - (J.frequencyOrder : ℝ)) := by
      calc
        _ ≤ ‖symbolDerivative (f t) J.spatialOrder J.frequencyOrder x ξ‖ +
            ‖symbolDerivative (f t₀) J.spatialOrder J.frequencyOrder x ξ‖ := norm_sub_le _ _
        _ ≤ C * (1 + ‖ξ‖) ^ (m - (J.frequencyOrder : ℝ)) +
            C * (1 + ‖ξ‖) ^ (m - (J.frequencyOrder : ℝ)) :=
          add_le_add (hCb t x hx ξ) (hCb t₀ x hx ξ)
        _ = _ := by ring
    calc
      _ ≤ ((2 * C) * (1 + ‖ξ‖) ^ (m - (J.frequencyOrder : ℝ))) /
          (1 + ‖ξ‖) ^ d := div_le_div_of_nonneg_right hnum (by positivity)
      _ = (2 * C) / (1 + ‖ξ‖) := by
        have hd : d = (m - (J.frequencyOrder : ℝ)) + 1 := by dsimp [d]; ring
        rw [hd, Real.rpow_add (by positivity), Real.rpow_one,
          mul_comm (2 * C) ((1 + ‖ξ‖) ^ (m - (J.frequencyOrder : ℝ))),
          mul_div_mul_left _ _ (Real.rpow_pos_of_pos (by positivity) _).ne']
  -- Apply the abstract compact-window lemma to the actual weighted mixed jets.
  have hG : ContinuousOn (fun w : ℝ × (X × X) ↦ G w.1 w.2)
      (univ ×ˢ (J.compactSet ×ˢ univ)) := by
    have hw : Continuous (fun w : ℝ × (X × X) ↦ (1 + ‖w.2.2‖) ^ (-d)) :=
      (continuous_const.add continuous_snd.snd.norm).rpow_const
        (fun w ↦ Or.inl (show 1 + ‖w.2.2‖ ≠ 0 from
          (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)).ne'))
    exact hw.continuousOn.smul ((hjets J.spatialOrder J.frequencyOrder).mono
      (fun w hw ↦ ⟨hw.1, J.subset_domain hw.2.1, hw.2.2⟩))
  have hnear : ∀ᶠ t in 𝓝 t₀, ∀ x ∈ J.compactSet, ∀ ξ : X,
      ‖G t (x, ξ) - G t₀ (x, ξ)‖ ≤ ε / 2 :=
    eventually_uniform_norm_sub_le_of_uniform_tail J.compactSet J.isCompact G hG
      (2 * C) t₀ htail (ε / 2) (half_pos hε)
  filter_upwards [hnear] with t ht
  apply lt_of_le_of_lt (b := ε / 2) _ (half_lt_self hε)
  change symbolSeminormValue hU (m + 1) J (p t - p t₀) ≤ ε / 2
  by_cases hK : J.compactSet.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hK
    unfold symbolSeminormValue
    refine csSup_le ?_ ?_
    · exact ⟨_, x₀, hx₀, (0 : X), rfl⟩
    · rintro v ⟨x, hx, ξ, rfl⟩
      change ‖symbolDerivative (f t - f t₀) J.spatialOrder J.frequencyOrder x ξ‖ /
        (1 + ‖ξ‖) ^ d ≤ ε / 2
      rw [raw_symbolDerivative_sub hU (f t) (f t₀) (hf t).1 (hf t₀).1
        J.spatialOrder J.frequencyOrder x (J.subset_domain hx) ξ, ← hnorm t (x, ξ)]
      exact ht x hx ξ
  · have hempty : J.compactSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hK
    simp only [symbolSeminormValue, hempty, mem_empty_iff_false, false_and,
      exists_false, Set.ofPred_false]
    simpa using (half_pos hε).le

private theorem continuous_fixed_quantizeSobolev {n r q : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (m s : ℝ)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ U) :
    Continuous (fun p : symbolSpace U hU m r q ↦
      quantizeSobolev m s (zeroExtendedSymbol U χ p.val)
        (isSymbol_zeroExtendedSymbol U hU m χ hχ hcχ hsχ p.val p.property)
        (hasCompactSupport_zeroExtendedSymbol U χ p.val hcχ)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let H₁ := Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure X)
  let H₂ := Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure X)
  let E (p : symbolSpace U hU m r q) := zeroExtendedSymbol U χ p.val
  have hE (p : symbolSpace U hU m r q) : IsSymbol univ m (E p) :=
    isSymbol_zeroExtendedSymbol U hU m χ hχ hcχ hsχ p.val p.property
  have hcE (p : symbolSpace U hU m r q) : HasCompactSupport (E p) :=
    hasCompactSupport_zeroExtendedSymbol U χ p.val hcχ
  let T (p : symbolSpace U hU m r q) := quantizeSchwartz m (E p) (hE p) (hcE p)
  let Q (p : symbolSpace U hU m r q) : H₁ →L[ℂ] H₂ :=
    quantizeSobolev m s (E p) (hE p) (hcE p)
  have hEadd (p q : symbolSpace U hU m r q) : E (p + q) = E p + E q := by
    funext x ξ
    by_cases hx : x ∈ U
    · simp [E, zeroExtendedSymbol, hx, smul_add]
    · simp [E, zeroExtendedSymbol, hx]
  have hEsmul (c : ℂ) (p : symbolSpace U hU m r q) : E (c • p) = c • E p := by
    funext x ξ
    by_cases hx : x ∈ U
    · simpa only [E, zeroExtendedSymbol, ite_eq_left hx, Submodule.coe_smul, Pi.smul_apply] using
        smul_comm (χ x : ℂ) c (p.val x ξ)
    · simp [E, zeroExtendedSymbol, hx]
  have hTadd (p q : symbolSpace U hU m r q) : T (p + q) = T p + T q := by
    have hadd := (hE p).add isOpen_univ (hE q)
    have hcadd := (hcE p).add (hcE q)
    have h := quantizeSchwartz_add m (E p) (E q) (hE p) (hE q) (hcE p) (hcE q)
      hadd hcadd
    simpa only [← hEadd] using h
  have hTsmul (c : ℂ) (p : symbolSpace U hU m r q) : T (c • p) = c • T p := by
    have hsmul := (hE p).smul isOpen_univ c
    have hcsmul : HasCompactSupport (c • E p) :=
      HasCompactSupport.smul_left (f := fun _ : X ↦ c) (hcE p)
    have h := quantizeSchwartz_smul m c (E p) (hE p) (hcE p) hsmul hcsmul
    simpa only [← hEsmul] using h
  -- Identify the exact Schwartz output of the same named Sobolev quantizer.
  have hcoordinate (p : symbolSpace U hU m r q)
      (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
      Q p (schwartzSobolevCoordinate s u) =
        schwartzSobolevCoordinate (s - m) (T p u) := by
    apply besselRealization_injective n q (s - m)
    ext1 φ
    rw [besselRealization_quantizeSobolev, besselRealization_schwartzSobolevCoordinate,
      SchwartzMap.coe_apply]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [quantizeSchwartz_apply]
  -- Linearity first holds on those same Schwartz coordinates, then passes by density.
  have hQadd (p q : symbolSpace U hU m r q) : Q (p + q) = Q p + Q q := by
    apply DFunLike.ext'
    apply (denseRange_schwartzSobolevCoordinate n r s).equalizer
      (Q (p + q)).continuous (Q p + Q q).continuous
    funext u
    simp only [Function.comp_apply, _root_.add_apply, hcoordinate,
      hTadd, schwartzSobolevCoordinate_add]
  have hQsmul (c : ℂ) (p : symbolSpace U hU m r q) : Q (c • p) = c • Q p := by
    apply DFunLike.ext'
    apply (denseRange_schwartzSobolevCoordinate n r s).equalizer
      (Q (c • p)).continuous (c • Q p).continuous
    funext u
    simp only [Function.comp_apply, _root_.smul_apply, hcoordinate,
      hTsmul, schwartzSobolevCoordinate_smul]
  let L : symbolSpace U hU m r q →ₗ[ℂ] (H₁ →L[ℂ] H₂) :=
    { toFun := Q
      map_add' := hQadd
      map_smul' := hQsmul }
  -- A finite set of original symbol seminorms controls the operator norm.
  obtain ⟨J, c, hquant⟩ := exists_quantizeSchwartz_zeroExtendedSymbol_seminorm_bound
    (r := r) (q := q) U hU m s χ hχ hcχ hsχ
  have hnorm (p : symbolSpace U hU m r q) :
      ‖L p‖ ≤ (c : ℝ) * (J.sup (symbolSeminorm hU m)) p := by
    let B : ℝ := (c : ℝ) * (J.sup (symbolSeminorm hU m)) p
    have hB : 0 ≤ B := mul_nonneg c.coe_nonneg (apply_nonneg _ p)
    apply (Q p).opNorm_le_bound hB
    intro z
    change ‖Q p z‖ ≤ B * ‖z‖
    refine (denseRange_schwartzSobolevCoordinate n r s).induction_on z
      (isClosed_le (Q p).continuous.norm (continuous_const.mul continuous_norm)) ?_
    intro u
    rw [hcoordinate]
    exact hquant p u
  exact WithSeminorms.continuous_normedSpace_rng (H₁ →L[ℂ] H₂)
    (withSeminorms_symbolTopology (r := r) (q := q) hU m) L
    ⟨J, c, by
      intro p
      change ‖L p‖ ≤ (c : ℝ) * (J.sup (symbolSeminorm hU m)) p
      exact hnorm p⟩

set_option maxHeartbeats 1000000 in

/-- The same compactly localized quantizer varies continuously with the real last frequency.
The Sobolev target uses one order of slack in the original symbol estimate. -/
theorem continuous_quantizeSobolev_realFrequencySymbolSlice
    {n r q : ℕ} (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hW : IsOpen W)
    (m s : ℝ) (hm : m ≤ 0) (a : SymbolFunction (n + 1) r q) (ha : IsSymbol W m a)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hUW : ∀ x ∈ U, EuclideanSpace.finAddEquivProd.symm
      (x, (0 : EuclideanSpace ℝ (Fin 1))) ∈ W)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ U) :
    ∃ hslice : ∀ τ : ℝ, IsSymbol U m (realFrequencySymbolSlice a τ),
      Continuous (fun τ : ℝ ↦ quantizeSobolev (m + 1) s
        (zeroExtendedSymbol U χ (realFrequencySymbolSlice a τ))
        (isSymbol_zeroExtendedSymbol U hU (m + 1) χ hχ hcχ hsχ
          (realFrequencySymbolSlice a τ) ((hslice τ).mono (by linarith)))
        (hasCompactSupport_zeroExtendedSymbol U χ (realFrequencySymbolSlice a τ) hcχ)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin (n + 1))
  let e : Y ≃L[ℝ] X × EuclideanSpace ℝ (Fin 1) := EuclideanSpace.finAddEquivProd
  let f : ℝ → SymbolFunction n r q := realFrequencySymbolSlice a
  have hbound (K : Set X) (hKU : K ⊆ U) (hK : IsCompact K) (i j : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ τ, ∀ x ∈ K, ∀ ξ,
        ‖symbolDerivative (f τ) i j x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
    apply exists_bound_realFrequencySymbolSlice W hW m hm a ha K hK
    rintro z ⟨x, hx, rfl⟩
    exact hUW x (hKU hx)
  have hslice (τ : ℝ) : IsSymbol U m (f τ) := by
    constructor
    · change ContDiffOn ℝ ∞ (Function.uncurry a ∘ (fun z : X × X ↦
        (e.symm (z.1, 0), e.symm (z.2, WithLp.toLp 2 (fun _ : Fin 1 ↦ τ)))))
        (U ×ˢ univ)
      apply ha.1.comp
      · exact ((e.symm.contDiff.comp (contDiff_fst.prodMk contDiff_const)).prodMk
          (e.symm.contDiff.comp (contDiff_snd.prodMk contDiff_const))).contDiffOn
      · intro z hz
        exact ⟨hUW z.1 hz.1, mem_univ _⟩
    · intro K hKU hK i j
      obtain ⟨C, hC, hCb⟩ := hbound K hKU hK i j
      exact ⟨C, hC, hCb τ⟩
  -- The real parameter, base variable and frequency enter the same smooth symbol.
  have hparam (τ : ℝ) (z : X × X) (hz : z ∈ U ×ˢ univ) :
      ContDiffAt ℝ ∞ (fun w : ℝ × (X × X) ↦ f w.1 w.2.1 w.2.2) (τ, z) := by
    have hbase : ContDiffAt ℝ ∞
        (fun w : ℝ × (X × X) ↦ e.symm (w.2.1, 0)) (τ, z) :=
      e.symm.contDiff.contDiffAt.comp (τ, z)
        (contDiffAt_snd.fst.prodMk contDiffAt_const)
    have hlast : ContDiffAt ℝ ∞ (fun w : ℝ × (X × X) ↦
        WithLp.toLp 2 (fun _ : Fin 1 ↦ w.1)) (τ, z) :=
      (contDiffAt_piLp 2).2 (fun _ ↦ contDiffAt_fst)
    have hfreq : ContDiffAt ℝ ∞ (fun w : ℝ × (X × X) ↦
        e.symm (w.2.2, WithLp.toLp 2 (fun _ : Fin 1 ↦ w.1))) (τ, z) :=
      e.symm.contDiff.contDiffAt.comp (τ, z) (contDiffAt_snd.snd.prodMk hlast)
    have haAt : ContDiffAt ℝ ∞ (Function.uncurry a)
        (e.symm (z.1, 0), e.symm (z.2, WithLp.toLp 2 (fun _ : Fin 1 ↦ τ))) :=
      ha.1.contDiffAt ((hW.prod isOpen_univ).mem_nhds ⟨hUW z.1 hz.1, mem_univ _⟩)
    change ContDiffAt ℝ ∞ (Function.uncurry a ∘
      (fun w : ℝ × (X × X) ↦ (e.symm (w.2.1, 0),
        e.symm (w.2.2, WithLp.toLp 2 (fun _ : Fin 1 ↦ w.1))))) (τ, z)
    exact haAt.comp (τ, z) (hbase.prodMk hfreq)
  have hjets (i j : ℕ) : ContinuousOn (fun w : ℝ × (X × X) ↦
      symbolDerivative (f w.1) i j w.2.1 w.2.2) (univ ×ˢ (U ×ˢ univ)) := by
    intro w hw
    change ContinuousWithinAt (fun v : ℝ × (X × X) ↦
      iteratedFDeriv ℝ i (fun x : X ↦ iteratedFDeriv ℝ j (f v.1 x) v.2.2) v.2.1)
      (univ ×ˢ (U ×ˢ univ)) w
    have hjet : ContDiffAt ℝ ∞ (fun v : ℝ × (X × X) ↦
        iteratedFDeriv ℝ i (fun x : X ↦ iteratedFDeriv ℝ j (f v.1 x) v.2.2) v.2.1) w :=
      raw_contDiffAt_parameter_mixed_iteratedFDeriv f w.1 w.2.1 w.2.2
        (hparam w.1 w.2 hw.2) i j
    exact hjet.continuousAt.continuousWithinAt
  let localSymbols (τ : ℝ) : symbolSpace U hU (m + 1) r q :=
    ⟨f τ, (hslice τ).mono (by linarith)⟩
  have hcontinuous : Continuous localSymbols :=
    continuous_symbolFamily_with_order_slack (n := n) (r := r) (q := q)
      hU m f hslice hbound hjets
  -- Compose the continuous symbol family with the continuous Sobolev quantizer.
  let quantizer (p : symbolSpace U hU (m + 1) r q) :
      Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure X) →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure X) :=
    quantizeSobolev (m + 1) s (zeroExtendedSymbol U χ p.val)
      (isSymbol_zeroExtendedSymbol U hU (m + 1) χ hχ hcχ hsχ p.val p.property)
      (hasCompactSupport_zeroExtendedSymbol U χ p.val hcχ)
  have hquantizer : Continuous quantizer :=
    continuous_fixed_quantizeSobolev (n := n) (r := r) (q := q)
      U hU (m + 1) s χ hχ hcχ hsχ
  refine ⟨hslice, ?_⟩
  change Continuous (fun τ : ℝ ↦ quantizer (localSymbols τ))
  exact hquantizer.comp hcontinuous

/-- Composition with the continuous square root gives continuity of the original named slice. -/
theorem continuous_quantizeSobolev_jointFrequencySymbolSlice
    {n r q : ℕ} (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hW : IsOpen W)
    (m s : ℝ) (hm : m ≤ 0) (a : SymbolFunction (n + 1) r q) (ha : IsSymbol W m a)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hUW : ∀ x ∈ U, EuclideanSpace.finAddEquivProd.symm
      (x, (0 : EuclideanSpace ℝ (Fin 1))) ∈ W)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ U) :
    ∃ hslice : ∀ t : ℝ, IsSymbol U m (jointFrequencySymbolSlice a t),
      Continuous (fun t : ℝ ↦ quantizeSobolev (m + 1) s
        (zeroExtendedSymbol U χ (jointFrequencySymbolSlice a t))
        (isSymbol_zeroExtendedSymbol U hU (m + 1) χ hχ hcχ hsχ
          (jointFrequencySymbolSlice a t) ((hslice t).mono (by linarith)))
        (hasCompactSupport_zeroExtendedSymbol U χ (jointFrequencySymbolSlice a t) hcχ)) := by
  obtain ⟨hslice, hcontinuous⟩ := continuous_quantizeSobolev_realFrequencySymbolSlice
    W hW m s hm a ha U hU hUW χ hχ hcχ hsχ
  refine ⟨fun t ↦ hslice (Real.sqrt t), ?_⟩
  exact hcontinuous.comp Real.continuous_sqrt

end AtiyahSinger

