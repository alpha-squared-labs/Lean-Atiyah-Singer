/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzFiniteParameter
public import AtiyahSinger.Analysis.SchwartzKernelExistence

import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Smooth compactly supported families under a Schwartz operator

Public module ID: M0939.

Joint smoothness and a common compact spatial support supply the actual
coordinate derivative tower. Applying a continuous Schwartz operator to this
family gives a smooth Banach-valued function of the finite-dimensional parameter.
All derivatives are formed from the same original function, and the support
is retained under differentiation before passing to Schwartz space.

This is the local parameter argument needed for operator lifts in SG III.13.6.
It does not assert compatibility with bundle transition functions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff SchwartzMap

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Joint smoothness constructs the actual Schwartz coordinate derivative tower,
with the same compact spatial support at every order. -/
theorem exists_schwartz_derivative_tower_of_common_compact_support
    (F : (Fin n → ℝ) → 𝓢(E, ℂ))
    (hF : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × E ↦ F p.1 p.2))
    (K : Set E) (hK : IsCompact K) (hsupport : ∀ x, tsupport (F x) ⊆ K) :
    ∃ G : List (Fin n) → (Fin n → ℝ) → 𝓢(E, ℂ),
      G [] = F ∧ (∀ a x, tsupport (G a x) ⊆ K) ∧ (∀ a, Continuous (G a)) ∧
      ∀ (a : List (Fin n)) (x v : Fin n → ℝ) (t : ℝ) (y : E),
        HasDerivAt (fun u ↦ G a (x + u • v) y)
          (∑ i : Fin n, v i • G (i :: a) (x + t • v) y) t := by
  classical
  -- Form each parameter derivative from the preceding original joint function.
  let D : List (Fin n) → ((Fin n → ℝ) × E) → ℂ :=
    List.rec (fun p ↦ F p.1 p.2)
      (fun i _ g p ↦ fderiv ℝ g p (Pi.single i 1, 0))
  have hD (a : List (Fin n)) : ContDiff ℝ ∞ (D a) := by
    induction a with
    | nil => exact hF
    | cons i a ih =>
      exact (ih.fderiv_right (by simp)).clm_apply contDiff_const
  have hDsupp (a : List (Fin n)) : tsupport (D a) ⊆ Prod.snd ⁻¹' K := by
    induction a with
    | nil =>
      apply closure_minimal ?_ (hK.isClosed.preimage continuous_snd)
      intro p hp
      exact hsupport p.1 (subset_tsupport (F p.1) hp)
    | cons i a ih =>
      exact (tsupport_fderiv_apply_subset ℝ (Pi.single i 1, 0)).trans ih
  have hspatial (a : List (Fin n)) (x : Fin n → ℝ) :
      ContDiff ℝ ∞ (fun y : E ↦ D a (x, y)) :=
    (hD a).comp (contDiff_const.prodMk contDiff_id)
  have hspatialSupp (a : List (Fin n)) (x : Fin n → ℝ) :
      tsupport (fun y : E ↦ D a (x, y)) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro y hy
    exact hDsupp a (subset_tsupport (D a) hy)
  let G (a : List (Fin n)) (x : Fin n → ℝ) : 𝓢(E, ℂ) :=
    HasCompactSupport.toSchwartzMap
      (hK.of_isClosed_subset (isClosed_tsupport _) (hspatialSupp a x)) (hspatial a x)
  -- Joint spatial jets retain smooth parameter dependence, hence Schwartz continuity.
  have hG (a : List (Fin n)) : Continuous (G a) := by
    apply continuous_schwartzMap_of_common_compact_support (G a) K hK (hspatialSupp a)
    intro j
    have hjets (k : ℕ) : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × E ↦
        iteratedFDeriv ℝ k (fun y ↦ D a (p.1, y)) p.2) := by
      induction k with
      | zero =>
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact (continuousMultilinearCurryFin0 ℝ E ℂ).symm.contDiff.comp (hD a)
      | succ k ih =>
        simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
        have hp : ContDiff ℝ ∞ (fun p : ((Fin n → ℝ) × E) × E ↦
            iteratedFDeriv ℝ k (fun y ↦ D a (p.1.1, y)) p.2) :=
          ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
        have hd := hp.fderiv
          (f := fun p : (Fin n → ℝ) × E ↦ fun y : E ↦
            iteratedFDeriv ℝ k (fun z ↦ D a (p.1, z)) y)
          (g := fun p : (Fin n → ℝ) × E ↦ p.2) contDiff_snd
          (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
        exact (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (k + 1) ↦ E) ℂ).symm.contDiff.comp hd
    exact (hjets j).continuous
  have hderiv (a : List (Fin n)) (x v : Fin n → ℝ) (t : ℝ) (y : E) :
      HasDerivAt (fun u ↦ G a (x + u • v) y)
        (∑ i : Fin n, v i • G (i :: a) (x + t • v) y) t := by
    have hpath : HasDerivAt (fun u : ℝ ↦ (x + u • v, y)) (v, 0) t := by
      simpa only [one_smul, id_eq] using
        (((hasDerivAt_id t).smul_const v).const_add x).prodMk (hasDerivAt_const t y)
    have h := ((hD a).differentiable (by simp) (x + t • v, y)).hasFDerivAt.comp_hasDerivAt
      t hpath
    have hdecomp : (v, (0 : E)) =
        ∑ i : Fin n, v i • (Pi.single i (1 : ℝ), (0 : E)) := by
      apply Prod.ext
      · change v = (ContinuousLinearMap.fst ℝ (Fin n → ℝ) E) _
        rw [map_sum]
        ext j
        simp [Pi.single_apply]
      · change (0 : E) = (ContinuousLinearMap.snd ℝ (Fin n → ℝ) E) _
        rw [map_sum]
        simp
    have heq : fderiv ℝ (D a) (x + t • v, y) (v, 0) =
        ∑ i : Fin n, v i • G (i :: a) (x + t • v) y := by
      rw [hdecomp, map_sum]
      simp only [map_smul]
      rfl
    rw [heq] at h
    exact h
  have hbase : G [] = F := by
    funext x
    ext y
    rfl
  exact ⟨G, hbase, hspatialSupp, hG, hderiv⟩

/-- A smooth family with common compact spatial support remains smooth under
a continuous Schwartz operator with Banach values. -/
theorem contDiff_schwartzMap_of_common_compact_support
    (F : (Fin n → ℝ) → 𝓢(E, ℂ))
    (hF : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × E ↦ F p.1 p.2))
    (K : Set E) (hK : IsCompact K) (hsupport : ∀ x, tsupport (F x) ⊆ K)
    (L : 𝓢(E, ℂ) →L[ℂ] V) : ContDiff ℝ ∞ (fun x ↦ L (F x)) := by
  obtain ⟨G, hbase, _, hG, hderiv⟩ :=
    exists_schwartz_derivative_tower_of_common_compact_support F hF K hK hsupport
  simpa only [hbase] using
    contDiff_schwartzMap_of_coordinate_derivatives G hG hderiv L

end AtiyahSinger
