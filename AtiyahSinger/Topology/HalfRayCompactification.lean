/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# The compactified half-ray product and its pointed contraction

Public module ID: M1874.

Karoubi II.4.8 uses the closed pair `X × {0} ⊆ X × [0,∞)` and the real
coordinate on its open complement. We use the literal product `X × ℝ≥0`.
Its zero section is identified with the original `X`; logarithm identifies
its positive part with `X × ℝ`, in the increasing direction.

The actual one-point compactification contracts to its existing infinity.
For time `u < 1`, its finite formula is `(x,r) ↦ (x,(r+u)/(1-u))`.
At time one every point goes to infinity, which stays fixed throughout.
No compactness or nonemptiness assumption is imposed on `X`: the continuity
certificate requires exactly local compactness and Hausdorffness.

Source correction: II.4.8, printed p. 84 / PDF p. 101, prints
`1 + (1-t)u` in its compact interval formula. This leaves the interval and
does not start at the identity. The corrected formula is `t + (1-t)u`.
With `t = r/(1+r)`, it gives exactly the half-ray formula used here.
This file supplies geometry only, without K-group vanishing or exactness claims.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint Topology
open scoped NNReal unitInterval

variable (X : Type*) [TopologicalSpace X]

/-- The original closed copy of `X` at the zero end of the literal half-ray product. -/
def halfRayZeroSection : Set (X × ℝ≥0) := {p | p.2 = 0}

/-- The zero section is closed for any topological base. -/
theorem isClosed_halfRayZeroSection : IsClosed (halfRayZeroSection X) := by
  /- The section is the inverse image of the closed zero singleton in `ℝ≥0`
  under the continuous second projection. No separation property of `X` is needed. -/
  exact isClosed_singleton.preimage continuous_snd

/-- The specified zero-section homeomorphism inserts zero and forgets only that coordinate. -/
def halfRayZeroSectionHomeomorph : X ≃ₜ halfRayZeroSection X where
  toFun x := ⟨(x, 0), rfl⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl p.property.symm
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk _
  continuous_invFun := continuous_subtype_val.fst

/-- The open complement uses the actual logarithm of the positive radial coordinate.
Its inverse uses the positive exponential, so this comparison does not reverse the real axis. -/
def halfRayComplementHomeomorph :
    ((halfRayZeroSection X)ᶜ : Set (X × ℝ≥0)) ≃ₜ X × ℝ where
  toFun p := (p.val.1, Real.log (p.val.2 : ℝ))
  invFun p :=
    ⟨(p.1, ⟨Real.exp p.2, (Real.exp_pos p.2).le⟩), by
      change (⟨Real.exp p.2, (Real.exp_pos p.2).le⟩ : ℝ≥0) ≠ 0
      intro h
      exact (Real.exp_pos p.2).ne' (congrArg NNReal.toReal h)⟩
  left_inv p := by
    -- Positivity of the original radial coordinate makes exp after log recover it.
    have hp : (p.val.2 : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr p.property
    apply Subtype.ext
    exact Prod.ext rfl (NNReal.eq
      (Real.exp_log (lt_of_le_of_ne p.val.2.property hp.symm)))
  right_inv p := by
    -- The inverse keeps the base point and log after exp recovers the real parameter.
    exact Prod.ext rfl (Real.log_exp p.2)
  continuous_toFun := continuous_subtype_val.fst.prodMk
    ((NNReal.continuous_coe.comp continuous_subtype_val.snd).log
      (fun p ↦ by
        change (p.val.2 : ℝ) ≠ 0
        exact NNReal.coe_ne_zero.mpr p.property))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk
      ((Real.continuous_exp.comp continuous_snd).subtype_mk _)

open scoped Classical in
/-- The concrete contraction moves finite radial coordinates to infinity and fixes infinity. -/
def halfRayCompactificationContraction :
    I × OnePoint (X × ℝ≥0) → OnePoint (X × ℝ≥0) :=
  fun p ↦ p.2.elim ∞ (fun xr ↦
    if (p.1 : ℝ) < 1 then
      (((xr.1, (⟨((xr.2 : ℝ) + (p.1 : ℝ)) / (1 - (p.1 : ℝ)),
        div_nonneg (add_nonneg xr.2.property p.1.property.1)
          (sub_nonneg.mpr p.1.property.2)⟩ : ℝ≥0)) : X × ℝ≥0) : OnePoint (X × ℝ≥0))
    else ∞)

/-- The explicit contraction is jointly continuous and fixes the existing infinity. -/
theorem halfRayCompactificationContraction_properties [LocallyCompactSpace X] [T2Space X] :
    Continuous (halfRayCompactificationContraction X) ∧
      (∀ z : OnePoint (X × ℝ≥0), halfRayCompactificationContraction X (0, z) = z) ∧
      (∀ z : OnePoint (X × ℝ≥0), halfRayCompactificationContraction X (1, z) = ∞) ∧
      (∀ u : I, halfRayCompactificationContraction X (u, ∞) = ∞) := by
  classical
  /- On the finite locus before time one, the rational formula is continuous.
  At infinity and time one, use the inverse formula `r = (1-u)s-u`: the inverse
  image of a finite compact set is the continuous image of a closed subset of
  its product with the compact time interval. This handles noncompact and empty
  bases without choosing a base point or imposing a bound on the base. -/
  let H := halfRayCompactificationContraction X
  let F (u : I) (xr : X × ℝ≥0) : X × ℝ≥0 :=
    (xr.1, ⟨((xr.2 : ℝ) + (u : ℝ)) / (1 - (u : ℝ)),
      div_nonneg (add_nonneg xr.2.property u.property.1)
        (sub_nonneg.mpr u.property.2)⟩)
  have hfinite (u : I) (xr : X × ℝ≥0) (hu : (u : ℝ) < 1) :
      H (u, (xr : OnePoint (X × ℝ≥0))) = (F u xr : OnePoint (X × ℝ≥0)) := by
    simp only [H, halfRayCompactificationContraction, OnePoint.elim_some, ite_eq_left hu, F]
  have hlast (u : I) (xr : X × ℝ≥0) (hu : ¬(u : ℝ) < 1) :
      H (u, (xr : OnePoint (X × ℝ≥0))) = ∞ := by
    simp only [H, halfRayCompactificationContraction, OnePoint.elim_some, ite_eq_right hu]
  -- The open finite part uses the ordinary continuous rational map.
  let T := {u : I // (u : ℝ) < 1}
  let e : T × (X × ℝ≥0) → I × OnePoint (X × ℝ≥0) :=
    Prod.map Subtype.val OnePoint.some
  have he : IsOpenMap e :=
    (isOpen_lt continuous_subtype_val continuous_const).isOpenMap_subtype_val.prodMap
      OnePoint.isOpenMap_coe
  have hF : Continuous (fun p : T × (X × ℝ≥0) ↦ F p.1.val p.2) := by
    apply Continuous.prodMk continuous_snd.fst
    apply Continuous.subtype_mk
    exact ((NNReal.continuous_coe.comp continuous_snd.snd).add
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))).div
      (continuous_const.sub
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)))
      (fun p ↦ sub_ne_zero.mpr (ne_of_gt p.1.property))
  -- Inverse radial parametrization gives compact preimages of finite compact sets.
  let rad (q : I × (X × ℝ≥0)) : ℝ :=
    (1 - (q.1 : ℝ)) * (q.2.2 : ℝ) - (q.1 : ℝ)
  have hrad : Continuous rad :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (NNReal.continuous_coe.comp continuous_snd.snd)).sub
      (continuous_subtype_val.comp continuous_fst)
  let B (q : I × (X × ℝ≥0)) : I × OnePoint (X × ℝ≥0) :=
    (q.1, ((q.2.1, Real.toNNReal (rad q)) : X × ℝ≥0))
  have hB : Continuous B :=
    continuous_fst.prodMk (OnePoint.continuous_coe.comp
      (continuous_snd.fst.prodMk (continuous_real_toNNReal.comp hrad)))
  have hcompact (K : Set (X × ℝ≥0)) (hK : IsCompact K) :
      IsClosed (H ⁻¹' (((↑) : X × ℝ≥0 → OnePoint (X × ℝ≥0)) '' K)) := by
    let S : Set (I × (X × ℝ≥0)) :=
      ((Set.univ : Set I) ×ˢ K) ∩ {q | 0 ≤ rad q}
    have hS : IsCompact S :=
      (isCompact_univ.prod hK).inter_right (isClosed_le continuous_const hrad)
    have himage : B '' S =
        H ⁻¹' (((↑) : X × ℝ≥0 → OnePoint (X × ℝ≥0)) '' K) := by
      ext p
      constructor
      · rintro ⟨⟨u, xs⟩, hq, rfl⟩
        have hn : 0 ≤ rad (u, xs) := hq.2
        have hu : (u : ℝ) < 1 := by
          by_contra h
          have hu1 : (u : ℝ) = 1 := le_antisymm u.property.2 (not_lt.mp h)
          simp only [rad, hu1, sub_self, zero_mul, zero_sub] at hn
          norm_num at hn
        refine ⟨xs, hq.1.2, ?_⟩
        change (xs : OnePoint (X × ℝ≥0)) =
          H (u, ((xs.1, Real.toNNReal (rad (u, xs))) : X × ℝ≥0))
        rw [hfinite u _ hu]
        apply congrArg OnePoint.some
        refine Prod.ext (by rfl) ?_
        apply NNReal.eq
        change (xs.2 : ℝ) =
          ((Real.toNNReal (rad (u, xs)) : ℝ) + (u : ℝ)) / (1 - (u : ℝ))
        rw [Real.coe_toNNReal _ hn]
        apply (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hu))).mpr
        dsimp [rad]
        ring
      · intro hp
        rcases p with ⟨u, z⟩
        cases z using OnePoint.rec with
        | infty =>
          obtain ⟨xs, _, hx⟩ := hp
          exact (OnePoint.coe_ne_infty xs hx).elim
        | coe xr =>
          by_cases hu : (u : ℝ) < 1
          · obtain ⟨xs, hxK, hx⟩ := hp
            rw [hfinite u xr hu] at hx
            have hxF : xs = F u xr := OnePoint.coe_injective hx
            subst xs
            have hr : rad (u, F u xr) = (xr.2 : ℝ) := by
              change (1 - (u : ℝ)) *
                (((xr.2 : ℝ) + (u : ℝ)) / (1 - (u : ℝ))) - (u : ℝ) = (xr.2 : ℝ)
              have hden : (1 : ℝ) - (u : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hu)
              field_simp [hden]
              ring
            refine ⟨(u, F u xr), ⟨⟨Set.mem_univ _, hxK⟩, ?_⟩, ?_⟩
            · change 0 ≤ rad (u, F u xr)
              rw [hr]
              exact xr.2.property
            · refine Prod.ext (by rfl) ?_
              apply congrArg OnePoint.some
              refine Prod.ext (by rfl) ?_
              apply NNReal.eq
              change (Real.toNNReal (rad (u, F u xr)) : ℝ) = (xr.2 : ℝ)
              rw [hr]
              exact Real.coe_toNNReal _ xr.2.property
          · obtain ⟨xs, _, hx⟩ := hp
            rw [hlast u xr hu] at hx
            exact (OnePoint.coe_ne_infty xs hx).elim
    rw [← himage]
    exact (hS.image hB).isClosed
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply continuous_def.mpr
    intro s hs
    by_cases hinfty : ∞ ∈ s
    · -- A neighborhood of infinity has finite compact complement.
      let K : Set (X × ℝ≥0) := (((↑) : X × ℝ≥0 → OnePoint (X × ℝ≥0)) ⁻¹' s)ᶜ
      have hK : IsCompact K := ((OnePoint.isOpen_iff_of_mem hinfty).mp hs).2
      have hcompl : sᶜ = (((↑) : X × ℝ≥0 → OnePoint (X × ℝ≥0)) '' K) := by
        ext z
        cases z using OnePoint.rec with
        | infty => simp [hinfty]
        | coe xr => simp [K]
      have hc := hcompact K hK
      rw [← hcompl, Set.preimage_compl] at hc
      simpa only [compl_compl] using hc.isOpen_compl
    · -- A finite open set is reached only in the open locus `u < 1`.
      have hsfinite : IsOpen (((↑) : X × ℝ≥0 → OnePoint (X × ℝ≥0)) ⁻¹' s) :=
        OnePoint.continuous_coe.isOpen_preimage s hs
      have hopen := he _ (hF.isOpen_preimage _ hsfinite)
      have heq : H ⁻¹' s =
          e '' ((fun p : T × (X × ℝ≥0) ↦ F p.1.val p.2) ⁻¹'
            (((↑) : X × ℝ≥0 → OnePoint (X × ℝ≥0)) ⁻¹' s)) := by
        ext p
        constructor
        · intro hp
          rcases p with ⟨u, z⟩
          cases z using OnePoint.rec with
          | infty => exact (hinfty hp).elim
          | coe xr =>
            by_cases hu : (u : ℝ) < 1
            · refine ⟨(⟨u, hu⟩, xr), ?_, rfl⟩
              change (F u xr : OnePoint (X × ℝ≥0)) ∈ s
              change H (u, (xr : OnePoint (X × ℝ≥0))) ∈ s at hp
              rwa [hfinite u xr hu] at hp
            · change H (u, (xr : OnePoint (X × ℝ≥0))) ∈ s at hp
              rw [hlast u xr hu] at hp
              exact (hinfty hp).elim
        · rintro ⟨⟨u, xr⟩, hp, rfl⟩
          change H (u.val, (xr : OnePoint (X × ℝ≥0))) ∈ s
          rwa [hfinite u.val xr u.property]
      rw [heq]
      exact hopen
  · -- At time zero the rational expression is the original radius.
    intro z
    cases z using OnePoint.rec with
    | infty => rfl
    | coe xr =>
      change H (0, (xr : OnePoint (X × ℝ≥0))) = (xr : OnePoint (X × ℝ≥0))
      rw [hfinite 0 xr (by norm_num)]
      apply congrArg OnePoint.some
      refine Prod.ext (by rfl) ?_
      apply NNReal.eq
      change ((xr.2 : ℝ) + 0) / (1 - 0) = (xr.2 : ℝ)
      simp
  · -- Time one takes the infinity branch, including on finite points.
    intro z
    cases z using OnePoint.rec with
    | infty => rfl
    | coe xr => exact hlast 1 xr (by norm_num)
  · intro u
    rfl

/-- The pointed contraction of the actual compactified half-ray product. -/
def halfRayCompactificationHomotopy [LocallyCompactSpace X] [T2Space X] :
    ContinuousMap.Homotopy (ContinuousMap.id (OnePoint (X × ℝ≥0)))
      (ContinuousMap.const (OnePoint (X × ℝ≥0)) ∞) where
  toFun := halfRayCompactificationContraction X
  continuous_toFun := (halfRayCompactificationContraction_properties X).1
  map_zero_left := (halfRayCompactificationContraction_properties X).2.1
  map_one_left := (halfRayCompactificationContraction_properties X).2.2.1

end AtiyahSinger
