/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EuclideanDirectionalPrimitive

/-!
# The lower-dimensional tail in compact-support de Rham induction

Public module ID: M1216.

A specified splitting into one real coordinate and its transverse Euclidean
space retains the actual inclusion, projection and coordinate functional.
The directional primitive of a closed compactly supported form has a smooth
closed compactly supported tail on that transverse space. Above the original
support, the primitive is exactly the pullback of this same tail.

This is the dimensional-reduction step in the standard compact-support
Poincaré argument (Bott--Tu, Chapter I). No compact support of the directional
primitive itself is asserted; the remaining tail must still be removed or
identified in the lower-dimensional cohomology calculation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set
open scoped BigOperators ContDiff Topology

variable {n : ℕ}

set_option maxHeartbeats 1500000 in
-- Keep the specified split maps, integral primitive and compact tail in one argument.
set_option maxRecDepth 5000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A compactly supported closed form has a directional primitive whose upper tail
is the actual pullback of a closed compactly supported form in one lower dimension. -/
theorem exists_smooth_euclideanForm_tail (p : ℕ)
    (e : EuclideanSpace ℝ (Fin (n + 1)))
    (l : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (j : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (q : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hle : l e = 1) (hlj : ∀ y, l (j y) = 0) (hqe : q e = 0)
    (hqj : ∀ y, q (j y) = y) (hsplit : ∀ x, j (q x) = x - l x • e)
    (α : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin (p + 1)]→L[ℝ] ℂ)
    (hα : ContDiff ℝ ∞ α) (hcompact : HasCompactSupport α)
    (hclosed : ∀ x, extDeriv α x = 0) :
    ∃ R : ℝ, 0 < R ∧ (∀ x, α x ≠ 0 → |l x| < R) ∧
      ∃ η : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin p]→L[ℝ] ℂ,
        ContDiff ℝ ∞ η ∧ (∀ x, extDeriv η x = α x) ∧
        (∀ x, l x ≤ -R → η x = 0) ∧
        (∀ x, q x ∉ q '' tsupport α → η x = 0) ∧
        ∃ θ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ,
          ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ (∀ y, extDeriv θ y = 0) ∧
          (∀ y, θ y = (η ((R + 1) • e + j y)).compContinuousLinearMap j) ∧
          (∀ y, θ y = (∫ t : ℝ, (α (j y + t • e)).curryLeft e).compContinuousLinearMap j) ∧
          ∀ x, R ≤ l x → η x = (θ (q x)).compContinuousLinearMap q := by
  classical
  let V := EuclideanSpace ℝ (Fin (n + 1))
  let U := EuclideanSpace ℝ (Fin n)
  obtain ⟨R, hR, hbound, η, hη, hdη, hformula, hbelow, hhorizontal, htail⟩ :=
    exists_smooth_euclideanDirectionalPrimitive p e l hle α hα hcompact hclosed
  let i (y : U) : V := (R + 1) • e + j y
  have hi : ContDiff ℝ ∞ i := contDiff_const.add j.contDiff
  have hdi (y : U) : fderiv ℝ i y = j := by
    have h := (hasFDerivAt_const ((R + 1) • e) y).add (j.hasFDerivAt (x := y))
    convert h.fderiv using 1
    simp
  have hli (y : U) : l (i y) = R + 1 := by simp [i, map_add, map_smul, hle, hlj]
  have hqi (y : U) : q (i y) = y := by simp [i, map_add, map_smul, hqe, hqj]
  have hzeroi (y : U) : α (i y) = 0 := by
    by_contra hne
    have h := hbound (i y) hne
    rw [hli] at h
    linarith [le_abs_self (R + 1)]
  -- Restriction to one hyperplane above the original support gives the actual tail.
  let θ (y : U) : U [⋀^Fin p]→L[ℝ] ℂ := (η (i y)).compContinuousLinearMap j
  have hθ : ContDiff ℝ ∞ θ := by
    let C : (V [⋀^Fin p]→L[ℝ] ℂ) →L[ℝ] U [⋀^Fin p]→L[ℝ] ℂ :=
      ContinuousAlternatingMap.compContinuousLinearMapCLM j
    change ContDiff ℝ ∞ (fun y ↦ C (η (i y)))
    exact C.contDiff.comp (hη.comp hi)
  have hdθ (y : U) : extDeriv θ y = 0 := by
    have h := extDeriv_pullback (hη.differentiable (by simp) (i y)) hi.contDiffAt
      (by simp : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω))
    simp_rw [hdi] at h
    change extDeriv θ y = (extDeriv η (i y)).compContinuousLinearMap j at h
    rw [h, hdη, hzeroi]
    ext v
    rfl
  -- The directional primitive vanishes outside the projection of the same original support.
  have hoff (x : V) (hx : q x ∉ q '' tsupport α) : η x = 0 := by
    have hz (t : ℝ) : α (x - t • e) = 0 := by
      by_contra hne
      apply hx
      refine ⟨x - t • e, subset_tsupport α hne, ?_⟩
      simp [map_sub, map_smul, hqe]
    rw [hformula]
    calc
      (∫ t in (0 : ℝ)..R + l x, (α (x - t • e)).curryLeft e) =
          ∫ _ in (0 : ℝ)..R + l x, (0 : V [⋀^Fin p]→L[ℝ] ℂ) := by
        apply intervalIntegral.integral_congr
        intro t _
        change (α (x - t • e)).curryLeft e = 0
        rw [hz, ContinuousAlternatingMap.curryLeft_zero, zero_apply]
      _ = 0 := intervalIntegral.integral_zero
  have hK : IsCompact (q '' tsupport α) := hcompact.image q.continuous
  have hθcompact : HasCompactSupport θ := by
    apply hK.of_isClosed_subset (isClosed_tsupport θ)
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hnot
    have hzero : η (i y) = 0 := hoff (i y) (by rwa [hqi])
    apply hy
    change (η (i y)).compContinuousLinearMap j = 0
    rw [hzero]
    ext v
    rfl
  -- Horizontality identifies the original p-tensor with its pullback from the transverse space.
  have hproject (x : V) :
      (η x).compContinuousLinearMap (j.comp q) = η x := by
    ext v
    let w (k : Fin p) : V := j (q (v k))
    have hdiff : η x v - η x w =
        ∑ k : Fin p, η x (fun a ↦
          if a < k then v a else if k = a then v a - w a else w a) := by
      have h := (η x).toContinuousMultilinearMap.toMultilinearMap.map_sub_map_piecewise
        v w Finset.univ
      simp only [Finset.piecewise_univ, Finset.mem_univ, true_implies] at h
      convert! h
    have hsum : (∑ k : Fin p, η x (fun a ↦
        if a < k then v a else if k = a then v a - w a else w a)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      let z (a : Fin p) : V :=
        if a < k then v a else if k = a then v a - w a else w a
      have hzk : z k = l (v k) • e := by
        simp only [z, lt_self_iff_false, ↓reduceIte, w, hsplit]
        module
      have hzupdate : z = Function.update z k (l (v k) • e) := by
        funext a
        by_cases ha : a = k
        · subst a
          simpa using hzk
        · simp [ha]
      change η x z = 0
      rw [hzupdate, ContinuousAlternatingMap.map_update_smul]
      rw [hhorizontal x (Function.update z k e) k (by simp), smul_zero]
    rw [hsum] at hdiff
    exact (sub_eq_zero.mp hdiff).symm
  have hupper (x : V) (hx : R ≤ l x) : η x = (θ (q x)).compContinuousLinearMap q := by
    have hupperi : R ≤ l (i (q x)) := by rw [hli]; linarith
    have hbase : i (q x) - l (i (q x)) • e = x - l x • e := by
      rw [hli]
      change (R + 1) • e + j (q x) - (R + 1) • e = _
      rw [hsplit]
      module
    have hxTail := htail x hx
    have hiTail := htail (i (q x)) hupperi
    rw [hbase] at hiTail
    have hvalue : η x = η (i (q x)) := hxTail.trans hiTail.symm
    rw [hvalue]
    have h := hproject (i (q x))
    exact h.symm
  have hθintegral (y : U) :
      θ y = (∫ t : ℝ, (α (j y + t • e)).curryLeft e).compContinuousLinearMap j := by
    have h := htail (i y) (by rw [hli]; linarith)
    have hi : i y - l (i y) • e = j y := by
      rw [hli]
      dsimp only [i]
      module
    rw [hi] at h
    exact congrArg (fun a : V [⋀^Fin p]→L[ℝ] ℂ ↦ a.compContinuousLinearMap j) h
  exact ⟨R, hR, hbound, η, hη, hdη, hbelow, hoff, θ, hθ, hθcompact, hdθ,
    (fun _ ↦ rfl), hθintegral, hupper⟩

end AtiyahSinger
