/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EuclideanDeRhamSuspension
public import AtiyahSinger.Geometry.EuclideanFormIntegral

/-!
# The integral of the actual compact-support suspension tail

Public module ID: M1220.

The first coordinate is integrated before the remaining coordinates. The
specified line and transverse inclusion retain the original ordered basis,
so the tail integral equals the original top-form integral with no hidden
orientation sign.

Source: Fubini in the compact-support de Rham argument, Bott--Tu, Chapter I.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff

set_option maxHeartbeats 1500000 in
-- The actual coordinate insertion, tensor evaluation and integrable line slice are retained.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In the ordered first-coordinate splitting,
the actual suspension tail preserves the top integral. -/
theorem euclideanTopFormIntegral_suspension (n : ℕ)
    (e : EuclideanSpace ℝ (Fin (n + 1)))
    (j : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hcoords : ∀ (t : ℝ) (y : Fin n → ℝ),
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (Fin.cons t y) =
        j ((EuclideanSpace.equiv (Fin n) ℝ).symm y) + t • e)
    (hframe : Fin.cons e (fun i ↦ j (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      ⇑(EuclideanSpace.basisFun (Fin (n + 1)) ℝ))
    (α : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin (n + 1)]→L[ℝ] ℂ)
    (hα : ContDiff ℝ ∞ α) (hc : HasCompactSupport α)
    (θ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℂ)
    (hθ : ∀ y, θ y =
      (∫ t : ℝ, (α (j y + t • e)).curryLeft e).compContinuousLinearMap j) :
    euclideanTopFormIntegral n θ = euclideanTopFormIntegral (n + 1) α := by
  classical
  let V := EuclideanSpace ℝ (Fin (n + 1))
  let U := EuclideanSpace ℝ (Fin n)
  let E : (Fin (n + 1) → ℝ) ≃L[ℝ] V := (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
  let F : (Fin n → ℝ) ≃L[ℝ] U := (EuclideanSpace.equiv (Fin n) ℝ).symm
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  let a := EuclideanSpace.basisFun (Fin n) ℝ
  let B : (V [⋀^Fin (n + 1)]→L[ℝ] ℂ) →L[ℝ] V [⋀^Fin n]→L[ℝ] ℂ :=
    (ContinuousLinearMap.apply ℝ (V [⋀^Fin n]→L[ℝ] ℂ) e).comp
      ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap
  let ev : (V [⋀^Fin n]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    ContinuousAlternatingMap.apply ℝ V ℂ (fun i ↦ j (a i))
  let f (x : Fin (n + 1) → ℝ) : ℂ := α (E x) b
  have hfcont : Continuous f :=
    (ContinuousAlternatingMap.apply ℝ V ℂ b).continuous.comp (hα.continuous.comp E.continuous)
  have hfc : HasCompactSupport f :=
    (hc.comp_homeomorph E.toHomeomorph).comp_left
      (ContinuousAlternatingMap.apply ℝ V ℂ b).map_zero
  have hfi : Integrable f := hfcont.integrable_of_hasCompactSupport hfc
  have hslice (y : Fin n → ℝ) : θ (F y) a = ∫ t : ℝ, f (Fin.cons t y) := by
    let line (t : ℝ) : V := j (F y) + t • e
    have hline : line = E ∘ Function.update (Fin.cons 0 y) 0 := by
      funext t
      simp only [Function.comp_apply, Fin.update_cons_zero]
      exact (hcoords t y).symm
    have hlineEmbedding : Topology.IsClosedEmbedding line := by
      rw [hline]
      exact E.toHomeomorph.isClosedEmbedding.comp
        (isClosedEmbedding_update (Fin.cons (0 : ℝ) y : Fin (n + 1) → ℝ) 0)
    have hlineCont : Continuous line := continuous_const.add (continuous_id.smul continuous_const)
    have hgi : Integrable (fun t : ℝ ↦ B (α (line t))) :=
      (B.continuous.comp (hα.continuous.comp hlineCont)).integrable_of_hasCompactSupport
        ((hc.comp_isClosedEmbedding hlineEmbedding).comp_left B.map_zero)
    rw [hθ]
    change ev (∫ t : ℝ, B (α (line t))) = _
    rw [← ev.integral_comp_comm hgi]
    apply integral_congr_ae
    filter_upwards [] with t
    change α (line t) (Fin.cons e (fun i ↦ j (a i))) = α (E (Fin.cons t y)) b
    rw [hframe, hcoords]
  -- The same measurable coordinate split computes the original integral by these slices.
  let s := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have hs : MeasurePreserving s := volume_preserving_piFinSuccAbove _ 0
  have hsapply (z : ℝ × (Fin n → ℝ)) : s.symm z = Fin.cons z.1 z.2 := by
    funext k
    refine Fin.cases ?_ (fun i ↦ ?_) k <;> rfl
  have hprod : Integrable (fun z ↦ f (s.symm z)) := hs.symm.integrable_comp_of_integrable hfi
  change (∫ y : Fin n → ℝ, θ (F y) a) = ∫ x : Fin (n + 1) → ℝ, f x
  calc
    _ = ∫ y : Fin n → ℝ, ∫ t : ℝ, f (Fin.cons t y) :=
      integral_congr_ae (Filter.Eventually.of_forall hslice)
    _ = ∫ z : ℝ × (Fin n → ℝ), f (s.symm z) := by
      convert! (integral_prod_symm _ hprod).symm using 1
      simp only [hsapply]
    _ = ∫ x : Fin (n + 1) → ℝ, f x := hs.symm.integral_comp' f

end AtiyahSinger
