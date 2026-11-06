/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SubmersionCotangentSplitting
public import AtiyahSinger.Geometry.TangentMusical
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# A metric compatible with a specified horizontal lift

Public module ID: M1279.

Given a smooth right inverse of a submersion differential, combine the base
metric on the horizontal component with a supplied metric on the vertical
component. The result keeps the original tangent topology and makes the
specified lift the metric adjoint of the differential. Its flat map therefore
agrees with pullback of base covectors on horizontal vectors.

This construction supplies the musical compatibility needed for an adapted
frame-sphere lift. Adaptation of the lift alone does not imply compatibility
with an arbitrary metric on the total space.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set Topology
open scoped Manifold ContDiff Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

omit [FiniteDimensional ℝ F] in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1800000 in
-- The metric and lift are compared in the native tangent and pulled tangent atlases.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A smooth metric can be chosen so the specified lift is adjoint to the differential,
relative to the supplied base metric. -/
theorem SmoothHorizontalLift.exists_compatibleMetric
    (q : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) (H : SmoothHorizontalLift q)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F (TangentSpace 𝓘(ℝ, F) : N → Type _))
    (h₀ : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    ∃ h : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _),
      (∀ (x : M) (u v : TangentSpace 𝓘(ℝ, E) x),
        h.inner x u v =
          g.inner (q x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) q x u)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) q x v) +
          h₀.inner x (u - H.lift x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) q x u))
            (v - H.lift x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) q x v))) ∧
      ∀ (x : M) (v : TangentSpace 𝓘(ℝ, F) (q x)),
        h.inner x (H.lift x v) =
          (g.inner (q x) v).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) q x) := by
  classical
  let I := 𝓘(ℝ, E)
  let J := 𝓘(ℝ, F)
  let D (x : M) : TangentSpace I x →L[ℝ] TangentSpace J (q x) := mfderiv I J q x
  let R (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
    ContinuousLinearMap.id ℝ _ - (H.lift x).comp (D x)
  let b (x : M) :=
    (g.inner (q x)).bilinearComp (D x) (D x) + (h₀.inner x).bilinearComp (R x) (R x)
  have hg_nonneg (x : N) (v : TangentSpace J x) : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hh_nonneg (x : M) (v : TangentSpace I x) : 0 ≤ h₀.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (h₀.pos x v hv).le
  -- The horizontal and vertical terms cannot both vanish on a nonzero vector.
  have hpos (x : M) (v : TangentSpace I x) (hv : v ≠ 0) : 0 < b x v v := by
    change 0 < g.inner (q x) (D x v) (D x v) + h₀.inner x (R x v) (R x v)
    by_cases hD : D x v = 0
    · have hR : R x v = v := by
        change v - H.lift x (D x v) = v
        rw [hD, map_zero, sub_zero]
      rw [hD, map_zero, zero_add, hR]
      exact h₀.pos x v hv
    · exact add_pos_of_pos_of_nonneg (g.pos (q x) (D x v) hD) (hh_nonneg x (R x v))
  have hbounded (x : M) : Bornology.IsVonNBounded ℝ {v | b x v v < 1} := by
    -- Decompose the new unit ball into the sum of two bounded original metric balls.
    apply (((g.isVonNBounded (q x)).image (H.lift x)).add (h₀.isVonNBounded x)).subset
    intro v hv
    change g.inner (q x) (D x v) (D x v) + h₀.inner x (R x v) (R x v) < 1 at hv
    have hDv : g.inner (q x) (D x v) (D x v) < 1 :=
      lt_of_le_of_lt (le_add_of_nonneg_right (hh_nonneg x (R x v))) hv
    have hRv : h₀.inner x (R x v) (R x v) < 1 :=
      lt_of_le_of_lt (le_add_of_nonneg_left (hg_nonneg (q x) (D x v))) hv
    refine ⟨H.lift x (D x v), ⟨D x v, hDv, rfl⟩, R x v, hRv, ?_⟩
    change H.lift x (D x v) + (v - H.lift x (D x v)) = v
    abel
  have hsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (b x)) := by
    intro x
    let a := trivializationAt E (TangentSpace I : M → Type _) x
    let t := trivializationAt F (TangentSpace J : N → Type _) (q x)
    let s := trivializationAt ℝ (Bundle.Trivial M ℝ) x
    let aDual := a.continuousLinearMap (RingHom.id ℝ) s
    have hax : x ∈ a.baseSet := mem_baseSet_trivializationAt _ _ _
    have htx : q x ∈ t.baseSet := mem_baseSet_trivializationAt _ _ _
    let v (u : E) (y : M) := a.symmL ℝ y u
    have hv (u : E) : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun y ↦ (⟨y, v u y⟩ : TangentBundle I M)) x := by
      apply (a.contMDiffAt_iff (a.mem_source.mpr hax)).mpr
      refine ⟨contMDiffAt_id, ?_⟩
      apply (contMDiffAt_const (c := u)).congr_of_eventuallyEq
      filter_upwards [a.open_baseSet.mem_nhds hax] with y hy
      rw [← a.continuousLinearMapAt_apply_of_mem ℝ hy]
      exact a.continuousLinearMapAt_symmL hy u
    have hDv (u : E) : ContMDiffAt I (J.prod 𝓘(ℝ, F)) ∞
        (fun y ↦ (⟨q y, D y (v u y)⟩ : TangentBundle J N)) x :=
      (q.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).contMDiffAt.comp x (hv u)
    have hRv (u : E) : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun y ↦ (⟨y, R y (v u y)⟩ : TangentBundle I M)) x := by
      let pt := t.pullback q
      let : MemTrivializationAtlas pt := ⟨⟨t, inferInstance, rfl⟩⟩
      have hp : ContMDiffAt I (I.prod 𝓘(ℝ, F)) ∞
          (fun y ↦ (⟨y, D y (v u y)⟩ :
            TotalSpace F ((q : M → N) *ᵖ (TangentSpace J)))) x := by
        apply (pt.contMDiffAt_iff (pt.mem_source.mpr (show x ∈ pt.baseSet from htx))).mpr
        exact ⟨contMDiffAt_id, ((t.contMDiffAt_iff (t.mem_source.mpr htx)).mp (hDv u)).2⟩
      have hH := H.contMDiff_lift.contMDiffAt.comp x hp
      have hc₀ := (a.contMDiffAt_iff (a.mem_source.mpr hax)).mp (hv u)
      have hc₁ := (a.contMDiffAt_iff (a.mem_source.mpr hax)).mp hH
      apply (a.contMDiffAt_iff (a.mem_source.mpr hax)).mpr
      refine ⟨contMDiffAt_id, (hc₀.2.sub hc₁.2).congr_of_eventuallyEq ?_⟩
      filter_upwards [a.open_baseSet.mem_nhds hax] with y hy
      exact (a.linearEquivAt ℝ y hy).map_sub _ _
    have heval (u w : E) : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y ↦ b y (v u y) (v w y)) x := by
      have h₁ : ContMDiffAt I (J.prod 𝓘(ℝ, ℝ)) ∞
          (fun y ↦ (⟨q y, g.inner (q y) (D y (v u y)) (D y (v w y))⟩ :
            TotalSpace ℝ (Bundle.Trivial N ℝ))) x := by
        apply ContMDiffAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
        · exact g.contMDiff.contMDiffAt.comp x q.contMDiff.contMDiffAt
        · exact hDv u
        · exact hDv w
      have h₂ : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
          (fun y ↦ (⟨y, h₀.inner y (R y (v u y)) (R y (v w y))⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ))) x := by
        apply ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
        · exact h₀.contMDiff.contMDiffAt
        · exact hRv u
        · exact hRv w
      simp only [contMDiffAt_totalSpace] at h₁ h₂
      exact h₁.2.add h₂.2
    -- Smoothness of scalar evaluations detects the full finite-dimensional bilinear matrix.
    let B (y : M) : E →L[ℝ] E →L[ℝ] ℝ :=
      (b y).bilinearComp (a.symmL ℝ y) (a.symmL ℝ y)
    have hB : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B x := by
      rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
      apply contDiffWithinAt_clm_apply.mpr
      intro u
      apply contDiffWithinAt_clm_apply.mpr
      intro w
      have h := heval u w
      rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at h
      exact h
    apply (contMDiffAt_hom_bundle (fun y : M ↦ TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) y (b y))).mpr
    refine ⟨contMDiffAt_id, hB.congr_of_eventuallyEq ?_⟩
    filter_upwards [a.open_baseSet.mem_nhds hax] with y hy
    ext u w
    change ((aDual.continuousLinearMapAt ℝ y) (b y (a.symmL ℝ y u))) w = _
    rw [aDual.continuousLinearMapAt_apply_of_mem ℝ ⟨hy, by simp [s]⟩]
    change (s.continuousLinearMapAt ℝ y) (b y (a.symmL ℝ y u) (a.symmL ℝ y w)) = _
    have hs : s.continuousLinearMapAt ℝ y = ContinuousLinearMap.id ℝ ℝ :=
      Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
    rw [hs]
    rfl
  let h : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _) :=
    { inner := b
      symm := fun x u v ↦ by
        change g.inner (q x) (D x u) (D x v) + h₀.inner x (R x u) (R x v) = _
        rw [g.symm, h₀.symm]
        rfl
      pos := hpos
      isVonNBounded := hbounded
      contMDiff := hsmooth }
  refine ⟨h, fun _ _ _ ↦ rfl, ?_⟩
  intro x v
  -- A lifted vector has zero vertical component, so its metric covector is exactly dq* flat(v).
  have hr : R x (H.lift x v) = 0 := by
    change H.lift x v - H.lift x (D x (H.lift x v)) = 0
    rw [H.right_inv, sub_self]
  ext w
  change g.inner (q x) (D x (H.lift x v)) (D x w) +
    h₀.inner x (R x (H.lift x v)) (R x w) = g.inner (q x) v (D x w)
  rw [H.right_inv, hr, map_zero, zero_apply, add_zero]

end AtiyahSinger
