/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Pseudolocal

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Sobolev bounds for compact smooth Euclidean kernels

Public module ID: M0359.

A05: the standard smooth-kernel estimate between arbitrary real Sobolev orders.
Opposite Bessel weights bound the original kernel rows, and finite Schwartz
seminorm bounds control the output. The integral uses the original Lebesgue
measure and matrix action. No geometric Sobolev duality or chart comparison is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 20

private theorem sobolev_coordinate_seminorm_bound {n r : ℕ} (s : ℝ) :
    ∃ (J : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ‖schwartzSobolevCoordinate s u‖ ≤
          C * J.sup (schwartzSeminormFamily ℂ _ _) u := by
  let X := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  let T := (SchwartzMap.toLpCLM ℂ E 2 (volume : Measure X)).comp
    (SchwartzMap.fourierMultiplierCLM E (fun ξ : X ↦ ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ)))
  let q : Seminorm ℂ 𝓢(X, E) := (normSeminorm ℂ _).comp T.toLinearMap
  obtain ⟨J, C, _, hC⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ X E) q T.continuous.norm
  refine ⟨J, C, C.coe_nonneg, ?_⟩
  intro u
  have hT : T u = schwartzSobolevCoordinate s u := by
    change (SchwartzMap.fourierMultiplierCLM E
      (fun ξ : X ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u).toLp 2 = _
    exact congrArg (fun v : 𝓢(X, E) ↦ v.toLp 2)
      (SchwartzMap.fourierMultiplierCLM_ofReal (F := E) ℂ
        (g := fun ξ : X ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2))
        (Function.hasTemperateGrowth_one_add_norm_sq_rpow X (s / 2)) u)
  have hb := hC u
  change ‖T u‖ ≤ (C : ℝ) * _ at hb
  simpa only [hT] using hb

private theorem compact_partial_derivatives {n : ℕ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → W)
    (hg : ContDiff ℝ ∞ g) (j : ℕ) :
    ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
      iteratedFDeriv ℝ j (fun x ↦ g (x, z.2)) z.1) ∧
      tsupport (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
      iteratedFDeriv ℝ j (fun x ↦ g (x, z.2)) z.1) ⊆ tsupport g := by
  let X := EuclideanSpace ℝ (Fin n)
  have hs (j : ℕ) :
      ContDiff ℝ ∞ (fun z : X × X ↦ iteratedFDeriv ℝ j (fun x ↦ g (x, z.2)) z.1) := by
    induction j with
    | zero =>
      exact hg.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ X W).symm : _ →L[ℝ] X [×0]→L[ℝ] W)
    | succ j ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : X × X ↦ fun x : X ↦
            iteratedFDeriv ℝ j (fun y ↦ g (y, z.2)) x)) :=
        ih.comp (contDiff_snd.prodMk contDiff_fst.snd)
      have hd : ContDiff ℝ ∞ (fun z : X × X ↦
          fderiv ℝ (iteratedFDeriv ℝ j (fun y ↦ g (y, z.2))) z.1) :=
        h.fderiv contDiff_fst (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ X) W).symm :
          _ →L[ℝ] X [×(j + 1)]→L[ℝ] W)
  refine ⟨hs j, closure_minimal ?_ (isClosed_tsupport g)⟩
  intro z hz
  by_contra hzg
  have heq : g =ᶠ[nhds z] (fun _ ↦ 0) := by
    filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hzg] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hslice : (fun x : X ↦ g (x, z.2)) =ᶠ[nhds z.1] (fun _ ↦ 0) :=
    heq.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hzero : iteratedFDeriv ℝ j (fun x : X ↦ g (x, z.2)) z.1 = 0 := by
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
      (hslice.iteratedFDeriv ℝ j).eq_of_nhds
  exact hz hzero

private theorem compact_rows_seminorm_bound {n r : ℕ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → W)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : EuclideanSpace ℝ (Fin n))
      (L : W →L[ℝ] EuclideanSpace ℂ (Fin r))
      (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))),
      (∀ y, v y = L (g (x, y))) → SchwartzMap.seminorm ℂ a b v ≤ C * ‖L‖ := by
  let X := EuclideanSpace ℝ (Fin n)
  let K := Prod.snd '' tsupport g
  have hK : IsCompact K := hc.image continuous_snd
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨D, hDnonneg, hD⟩ := hc.exists_bound_iteratedFDeriv hg b
  refine ⟨(max R 0) ^ a * max D 0, by positivity, ?_⟩
  intro x L v hv
  have hsupport : tsupport v ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hyK
    have hzero : g (x, y) = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hyK ⟨(x, y), h, rfl⟩)
    exact hy (by rw [hv, hzero, map_zero])
  apply SchwartzMap.seminorm_le_bound ℂ a b v (by positivity)
  intro y
  by_cases hy : y ∈ K
  · let I : X →L[ℝ] X × X := ContinuousLinearMap.inr ℝ X X
    let f : X × X → W := fun z ↦ g ((x, 0) + z)
    have hf : ContDiff ℝ ∞ f := hg.comp (contDiff_const.add contDiff_id)
    have heq : (v : X → EuclideanSpace ℂ (Fin r)) = L ∘ (f ∘ I) := by
      funext y
      simpa [f, I] using hv y
    have hI : ‖I‖ ≤ 1 := by
      apply I.opNorm_le_bound zero_le_one
      intro y
      simp [I]
    have hder : ‖iteratedFDeriv ℝ b (f ∘ I) y‖ ≤ max D 0 := by
      rw [I.iteratedFDeriv_comp_right hf y (by simp)]
      apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      apply (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hI) (norm_nonneg _)).trans
      rw [mul_one]
      have htranslate : iteratedFDeriv ℝ b f (I y) = iteratedFDeriv ℝ b g (x, y) := by
        simpa [f, I] using iteratedFDeriv_comp_add_left b (x, 0) (I y) (f := g)
      rw [htranslate]
      exact (hD b le_rfl (x, y)).trans (le_max_left _ _)
    have hvder : ‖iteratedFDeriv ℝ b v y‖ ≤ ‖L‖ * max D 0 := by
      rw [heq]
      exact (L.norm_iteratedFDeriv_comp_left
        ((hf.comp I.contDiff).contDiffAt) (by simp)).trans
          (mul_le_mul_of_nonneg_left hder (norm_nonneg _))
    calc
      _ ≤ (max R 0) ^ a * (‖L‖ * max D 0) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ((hR y hy).trans (le_max_left _ _)) a)
          hvder (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hzero : iteratedFDeriv ℝ b v y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hy (hsupport (tsupport_iteratedFDeriv_subset b h)))
    rw [hzero, norm_zero, mul_zero]
    positivity

private theorem compact_rows_sobolev_bound {n r : ℕ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → W)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : EuclideanSpace ℝ (Fin n))
      (L : W →L[ℝ] EuclideanSpace ℂ (Fin r))
      (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))),
      (∀ y, v y = L (g (x, y))) →
        ‖schwartzSobolevCoordinate s v‖ ≤ C * ‖L‖ := by
  classical
  obtain ⟨J, C, hC, hbound⟩ := sobolev_coordinate_seminorm_bound (n := n) (r := r) s
  choose D hD hrows using fun p : ℕ × ℕ ↦ compact_rows_seminorm_bound g hg hc p.1 p.2
  refine ⟨C * ∑ p ∈ J, D p, mul_nonneg hC (Finset.sum_nonneg fun p _ ↦ hD p), ?_⟩
  intro x L v hv
  have hb : J.sup (schwartzSeminormFamily ℂ _ _) v ≤ (∑ p ∈ J, D p) * ‖L‖ := by
    apply Seminorm.finset_sup_apply_le
      (mul_nonneg (Finset.sum_nonneg fun p _ ↦ hD p) (norm_nonneg _))
    intro p hp
    exact (hrows p x L v hv).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun q _ ↦ hD q) hp) (norm_nonneg _))
  exact (hbound v).trans ((mul_le_mul_of_nonneg_left hb hC).trans_eq (mul_assoc _ _ _).symm)

private theorem compact_kernel_rows_integral_bound {n r q j : ℕ}
    (g : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ]
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : EuclideanSpace ℝ (Fin n))
      (m : Fin j → EuclideanSpace ℝ (Fin n))
      (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))),
      ‖∫ y, g (x, y) m (u y)‖ ≤ C * (∏ i, ‖m i‖) * ‖schwartzSobolevCoordinate s u‖ := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  let F := EuclideanSpace ℂ (Fin q)
  let W := X [×j]→L[ℝ] (E →L[ℂ] F)
  let J : (E →L[ℂ] F) ≃ₗᵢ[ℝ] (F →L[ℂ] E) := {
    toEquiv := (ContinuousLinearMap.adjoint : (E →L[ℂ] F) ≃ₗᵢ⋆[ℂ] (F →L[ℂ] E)).toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by
      intro t A
      change (t • A).adjoint = t • A.adjoint
      rw [← Complex.coe_smul t A, map_smulₛₗ]
      simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  obtain ⟨C, hC, hrows⟩ := compact_rows_sobolev_bound (r := r) g hg hc (-s)
  refine ⟨C, hC, ?_⟩
  intro x m u
  have hs : ContDiff ℝ ∞ (fun y : X ↦ g (x, y)) :=
    hg.comp (contDiff_const.prodMk contDiff_id)
  have hcSlice : HasCompactSupport (fun y : X ↦ g (x, y)) := by
    apply (hc.image continuous_snd).of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_
      (hc.image continuous_snd).isClosed)
    intro y hy
    exact ⟨(x, y), subset_tsupport _ hy, rfl⟩
  have hi : Integrable (fun y : X ↦ g (x, y) m (u y)) := by
    have hcompact : HasCompactSupport (fun y : X ↦ g (x, y) m (u y)) := by
      apply hcSlice.of_isClosed_subset (isClosed_tsupport _) (closure_mono ?_)
      intro y hy
      contrapose! hy
      simp only [Function.mem_support, ne_eq, not_not] at hy ⊢
      simp [hy]
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hcompact
  let z : F := ∫ y, g (x, y) m (u y)
  have hinner (w : F) : ‖inner ℂ w z‖ ≤
      C * (∏ i, ‖m i‖) * ‖w‖ * ‖schwartzSobolevCoordinate s u‖ := by
    let ev : W →L[ℝ] (E →L[ℂ] F) :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ X) (E →L[ℂ] F) m
    let L : W →L[ℝ] E := ((ContinuousLinearMap.apply ℂ E w).restrictScalars ℝ).comp
      (J.toContinuousLinearEquiv.toContinuousLinearMap.comp ev)
    have hL : ‖L‖ ≤ (∏ i, ‖m i‖) * ‖w‖ := by
      apply L.opNorm_le_bound (by positivity)
      intro A
      calc
        ‖L A‖ = ‖(A m).adjoint w‖ := rfl
        _ ≤ ‖(A m).adjoint‖ * ‖w‖ := (A m).adjoint.le_opNorm w
        _ = ‖A m‖ * ‖w‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
        _ ≤ (‖A‖ * ∏ i, ‖m i‖) * ‖w‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm m) (norm_nonneg _)
        _ = _ := by ring
    let v : 𝓢(X, E) := (hcSlice.comp_left L.map_zero).toSchwartzMap
      (L.contDiff.comp hs)
    have hv (y : X) : v y = (g (x, y) m).adjoint w := rfl
    have hb : ‖schwartzSobolevCoordinate (-s) v‖ ≤ C * ((∏ i, ‖m i‖) * ‖w‖) :=
      (hrows x L v (fun _ ↦ rfl)).trans (mul_le_mul_of_nonneg_left hL hC)
    have heq : inner ℂ w z = inner ℂ (schwartzSobolevCoordinate (-s) v)
        (schwartzSobolevCoordinate s u) := by
      rw [show inner ℂ (schwartzSobolevCoordinate (-s) v)
        (schwartzSobolevCoordinate s u) = ∫ y, inner ℂ (v y) (u y) from
          by simpa only [neg_neg] using sobolev_pairing_schwartz (-s) v u]
      rw [← integral_inner hi w]
      apply integral_congr_ae
      filter_upwards with y
      rw [hv, ContinuousLinearMap.adjoint_inner_left]
    rw [heq]
    exact (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_right hb
      (norm_nonneg _)).trans_eq (by ring))
  have hz := hinner z
  rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq] at hz
  by_cases hzero : ‖z‖ = 0
  · change ‖z‖ ≤ _
    rw [hzero]
    positivity
  · have hpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hzero)
    change ‖z‖ ≤ _
    nlinarith

private theorem compact_kernel_integral_derivatives {n r q : ℕ}
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (hk : ContDiff ℝ ∞ (Function.uncurry k))
    (hc : HasCompactSupport (Function.uncurry k))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    ContDiff ℝ ∞ (fun x ↦ ∫ y, k x y (u y)) ∧
      ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n))
        (m : Fin j → EuclideanSpace ℝ (Fin n)),
        Integrable (fun y ↦ (iteratedFDeriv ℝ j (fun x ↦ k x y) x m) (u y)) ∧
          iteratedFDeriv ℝ j (fun x ↦ ∫ y, k x y (u y)) x m =
            ∫ y, (iteratedFDeriv ℝ j (fun x ↦ k x y) x m) (u y) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  let F := EuclideanSpace ℂ (Fin q)
  -- A dominated Taylor series records all derivatives of the actual Bochner integral.
  have integrate {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
      [CompleteSpace W] [SecondCountableTopology W]
      (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → W)
      (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (hbound : ∀ k : ℕ, ∃ b : EuclideanSpace ℝ (Fin n) → ℝ,
        Integrable b ∧ ∀ x ξ, ‖iteratedFDeriv ℝ k (fun x ↦ f x ξ) x‖ ≤ b ξ) :
      ContDiff ℝ ∞ (fun x ↦ ∫ ξ, f x ξ) ∧
        ∀ k x, Integrable (fun ξ ↦ iteratedFDeriv ℝ k (fun x ↦ f x ξ) x) ∧
          iteratedFDeriv ℝ k (fun x ↦ ∫ ξ, f x ξ) x =
            ∫ ξ, iteratedFDeriv ℝ k (fun x ↦ f x ξ) x := by
    let V := EuclideanSpace ℝ (Fin n)
    have parametric {X Y Z : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup Z] [NormedSpace ℝ Z]
        (g : X → Y → Z) (hg : ContDiff ℝ ∞ (Function.uncurry g)) (k : ℕ) :
        ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (g z.1) z.2) := by
      induction k with
      | zero =>
        exact hg.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ Y Z).symm : _ →L[ℝ] Y [×0]→L[ℝ] Z)
      | succ k ih =>
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun z : X × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ k (g z.1) η)) :=
          ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
        have hd : ContDiff ℝ ∞
            (fun z : X × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (g z.1)) z.2) :=
          h.fderiv contDiff_snd (by simp)
        exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) Z).symm :
            _ →L[ℝ] Y [×(k + 1)]→L[ℝ] Z)
    let D (k : ℕ) (x ξ : V) := iteratedFDeriv ℝ k (fun x ↦ f x ξ) x
    have hs (k : ℕ) : ContDiff ℝ ∞ (Function.uncurry (D k)) := by
      exact (parametric (fun ξ x ↦ f x ξ)
        (hf.comp (contDiff_snd.prodMk contDiff_fst)) k).comp
          (contDiff_snd.prodMk contDiff_fst)
    have hi (k : ℕ) (x : V) : Integrable (D k x) := by
      obtain ⟨b, hb, hbk⟩ := hbound k
      exact hb.mono' ((hs k).continuous.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
          (Filter.Eventually.of_forall (hbk x))
    have hd (k : ℕ) (x : V) :
        HasFDerivAt (fun x ↦ ∫ ξ, D k x ξ)
          ((∫ ξ, D (k + 1) x ξ).curryLeft) x := by
      obtain ⟨b, hb, hbk⟩ := hbound (k + 1)
      let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ V) W
      have heq (z ξ : V) : fderiv ℝ (fun z ↦ D k z ξ) z = L (D (k + 1) z ξ) := by
        dsimp only [D]
        rw [iteratedFDeriv_succ_eq_comp_left]
        exact (L.apply_symm_apply _).symm
      have hdiff (ξ z : V) : HasFDerivAt (fun z ↦ D k z ξ) (L (D (k + 1) z ξ)) z := by
        rw [← heq]
        exact (((hs k).comp (contDiff_id.prodMk contDiff_const)).differentiable
          (by simp) z).hasFDerivAt
      have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := D k) (F' := fun z ξ ↦ L (D (k + 1) z ξ)) (s := Set.univ)
        (bound := b) (x₀ := x) (by simp)
        (Filter.Eventually.of_forall (fun z ↦ (hi k z).1)) (hi k x)
        ((L.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (hi (k + 1) x)).1)
        (Filter.Eventually.of_forall (fun ξ z _ ↦ by simpa using hbk z ξ))
        hb (Filter.Eventually.of_forall (fun ξ z _ ↦ hdiff ξ z))
      have hL : (∫ ξ, L (D (k + 1) x ξ)) = L (∫ ξ, D (k + 1) x ξ) :=
        L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm (hi (k + 1) x)
      rw [hL] at h
      exact h
    have hTaylor : HasFTaylorSeriesUpTo (∞ : ℕ∞ω) (fun x ↦ ∫ ξ, f x ξ)
        (fun x k ↦ ∫ ξ, D k x ξ) := by
      constructor
      · intro x
        let L := continuousMultilinearCurryFin0 ℝ V W
        calc
          _ = ∫ ξ, L (D 0 x ξ) :=
            (L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm (hi 0 x)).symm
          _ = _ := by
            apply integral_congr_ae
            filter_upwards with ξ
            simp [D, L]
      · intro k _ x
        exact hd k x
      · intro k _
        exact (show Differentiable ℝ (fun x ↦ ∫ ξ, D k x ξ) from
          fun x ↦ (hd k x).differentiableAt).continuous
    exact ⟨hTaylor.contDiff, fun k x ↦
      ⟨hi k x, (hTaylor.eq_iteratedFDeriv (by simp) x).symm⟩⟩
  let f (x y : X) : F := k x y (u y)
  have hf : ContDiff ℝ ∞ (Function.uncurry f) := by
    have hreal : ContDiff ℝ ∞ (fun z : X × X ↦ (k z.1 z.2).restrictScalars ℝ) :=
      (ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).contDiff.comp hk
    exact hreal.clm_apply (u.smooth'.comp contDiff_snd)
  have hslice (y : X) : ContDiff ℝ ∞ (fun x ↦ k x y) :=
    hk.comp (contDiff_id.prodMk contDiff_const)
  let L (y : X) : (E →L[ℂ] F) →L[ℝ] F :=
    (ContinuousLinearMap.apply ℂ F (u y)).restrictScalars ℝ
  have hder (j : ℕ) (x y : X) : iteratedFDeriv ℝ j (fun x ↦ f x y) x =
      (L y).compContinuousMultilinearMap (iteratedFDeriv ℝ j (fun x ↦ k x y) x) := by
    exact (L y).iteratedFDeriv_comp_left (hslice y).contDiffAt (by simp)
  -- Compact support bounds joint derivatives; restriction to x has operator norm at most one.
  have hbound (j : ℕ) : ∃ b : X → ℝ, Integrable b ∧
      ∀ x y, ‖iteratedFDeriv ℝ j (fun x ↦ f x y) x‖ ≤ b y := by
    obtain ⟨D, hDnonneg, hD⟩ := hc.exists_bound_iteratedFDeriv hk j
    refine ⟨fun y ↦ D * ‖u y‖, u.integrable.norm.const_mul D, ?_⟩
    intro x y
    let I : X →L[ℝ] X × X := ContinuousLinearMap.inl ℝ X X
    let g : X × X → (E →L[ℂ] F) := fun z ↦ Function.uncurry k ((0, y) + z)
    have hg : ContDiff ℝ ∞ g := hk.comp (contDiff_const.add contDiff_id)
    have heq : (fun x ↦ k x y) = g ∘ I := by
      funext x
      simp [g, I]
    have hI : ‖I‖ ≤ 1 := by
      apply I.opNorm_le_bound zero_le_one
      intro x
      simp [I]
    have hkder : ‖iteratedFDeriv ℝ j (fun x ↦ k x y) x‖ ≤ D := by
      rw [heq, I.iteratedFDeriv_comp_right hg x (by simp)]
      apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      apply (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hI)
        (norm_nonneg _)).trans
      rw [mul_one]
      have htranslate : iteratedFDeriv ℝ j g (I x) =
          iteratedFDeriv ℝ j (Function.uncurry k) (x, y) := by
        simpa [g, I] using iteratedFDeriv_comp_add_left (𝕜 := ℝ) j (0, y) (I x)
            (f := Function.uncurry k)
      rw [htranslate]
      exact hD j le_rfl (x, y)
    have hL : ‖L y‖ ≤ ‖u y‖ := by
      apply (L y).opNorm_le_bound (norm_nonneg _)
      intro T
      simpa [L, mul_comm] using T.le_opNorm (u y)
    rw [hder]
    exact ((L y).norm_compContinuousMultilinearMap_le _).trans
      ((mul_le_mul hL hkder (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _))
  obtain ⟨hsmooth, hfull⟩ := integrate f hf hbound
  refine ⟨hsmooth, ?_⟩
  intro j x m
  obtain ⟨hi, hid⟩ := hfull j x
  let ev : (X [×j]→L[ℝ] F) →L[ℝ] F :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ X) F m
  have heval (y : X) : iteratedFDeriv ℝ j (fun x ↦ f x y) x m =
      (iteratedFDeriv ℝ j (fun x ↦ k x y) x m) (u y) := by
    rw [hder]
    rfl
  refine ⟨?_, ?_⟩
  · exact (ev.integrable_comp hi).congr (Filter.Eventually.of_forall heval)
  · change iteratedFDeriv ℝ j (fun x ↦ ∫ y, f x y) x m = _
    rw [hid, ContinuousMultilinearMap.integral_apply hi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall heval


/-- Compact smooth kernels improve every real Sobolev order. -/
theorem compact_smooth_kernel_sobolev_bound {n r q : ℕ}
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (hk : ContDiff ℝ ∞ (Function.uncurry k))
    (hc : HasCompactSupport (Function.uncurry k))
    (s t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
        (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))),
        (∀ x, v x = ∫ y, k x y (u y)) →
        ‖schwartzSobolevCoordinate t v‖ ≤ C * ‖schwartzSobolevCoordinate s u‖ := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℂ (Fin q)
  -- Differentiate only the output variable; each derivative is still a compact smooth kernel.
  let D (j : ℕ) (z : X × X) := iteratedFDeriv ℝ j (fun x ↦ k x z.2) z.1
  have hD (j : ℕ) : ContDiff ℝ ∞ (D j) := (compact_partial_derivatives _ hk j).1
  have hcD (j : ℕ) : HasCompactSupport (D j) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (compact_partial_derivatives _ hk j).2
  choose C hC hrows using fun j ↦ compact_kernel_rows_integral_bound (D j) (hD j) (hcD j) s
  let K := Prod.fst '' tsupport (Function.uncurry k)
  have hK : IsCompact K := hc.image continuous_fst
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨J, B, hB, htarget⟩ := sobolev_coordinate_seminorm_bound (n := n) (r := q) t
  let Q (p : ℕ × ℕ) := (max R 0) ^ p.1 * C p.2
  have hQ (p : ℕ × ℕ) : 0 ≤ Q p := mul_nonneg (by positivity) (hC p.2)
  refine ⟨B * ∑ p ∈ J, Q p, mul_nonneg hB (Finset.sum_nonneg fun p _ ↦ hQ p), ?_⟩
  intro u v hv
  -- The original output vanishes outside the first projection of the kernel support.
  have hsupport : tsupport v ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra hxK
    have hz (y : X) : k x y = 0 := image_eq_zero_of_notMem_tsupport
      (f := Function.uncurry k)
      (fun h ↦ hxK ⟨(x, y), h, rfl⟩)
    exact hx (by simp [hv, hz])
  have hd (j : ℕ) (x : X) :
      ‖iteratedFDeriv ℝ j v x‖ ≤ C j * ‖schwartzSobolevCoordinate s u‖ := by
    apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (hC j) (norm_nonneg _))
    intro m
    rw [show (v : X → F) = (fun x ↦ ∫ y, k x y (u y)) from funext hv,
      ((compact_kernel_integral_derivatives k hk hc u).2 j x m).2]
    exact (hrows j x m u).trans_eq (by ring)
  -- A single compact output support bounds all spatial weights in the finite target family.
  have hsemi (p : ℕ × ℕ) :
      schwartzSeminormFamily ℂ X F p v ≤ Q p * ‖schwartzSobolevCoordinate s u‖ := by
    apply SchwartzMap.seminorm_le_bound ℂ p.1 p.2 v
      (mul_nonneg (hQ p) (norm_nonneg _))
    intro x
    by_cases hx : x ∈ K
    · calc
        _ ≤ (max R 0) ^ p.1 * (C p.2 * ‖schwartzSobolevCoordinate s u‖) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
            ((hR x hx).trans (le_max_left _ _)) _) (hd p.2 x) (norm_nonneg _) (by positivity)
        _ = _ := by dsimp [Q]; ring
    · have hz : iteratedFDeriv ℝ p.2 v x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hx (hsupport (tsupport_iteratedFDeriv_subset p.2 h)))
      rw [hz, norm_zero, mul_zero]
      exact mul_nonneg (hQ p) (norm_nonneg _)
  have hsup : J.sup (schwartzSeminormFamily ℂ X F) v ≤
      (∑ p ∈ J, Q p) * ‖schwartzSobolevCoordinate s u‖ := by
    apply Seminorm.finset_sup_apply_le
      (mul_nonneg (Finset.sum_nonneg fun p _ ↦ hQ p) (norm_nonneg _))
    intro p hp
    exact (hsemi p).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun p _ ↦ hQ p) hp) (norm_nonneg _))
  exact (htarget v).trans ((mul_le_mul_of_nonneg_left hsup hB).trans_eq (mul_assoc _ _ _).symm)

end AtiyahSinger
