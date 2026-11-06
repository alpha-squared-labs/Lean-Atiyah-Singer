/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SubmersionCotangentSplitting
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# A reflection-adapted horizontal lift along a fixed section

Public module ID: M1349.

Average a given horizontal lift with its pushforward by an involution over
the same base. If the involution fixes a section and negates the vertical
vectors there, the average agrees with the section's actual differential.
The average is still a right inverse of the original projection, with the
same native smooth bundles.

This supplies the adaptation needed at the south section of a frame sphere.
The involution and its vertical derivative must be verified on the actual
geometric model before applying this theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1400000 in
-- The reflection is pulled through the original submersion's tangent pullback bundle.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A vertical reflection fixing a section gives a horizontal lift equal to its derivative. -/
theorem exists_reflection_adaptedHorizontalLift
    (q : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) (H : SmoothHorizontalLift q)
    (d : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M)
    (hd : Function.Involutive d) (hqd : ∀ x, q (d x) = q x)
    (j : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, E) N M ∞)
    (hqj : ∀ y, q (j y) = y) (hdj : ∀ y, d (j y) = j y)
    (hvertical : ∀ (y : N) (w : TangentSpace 𝓘(ℝ, E) (j y)),
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) q (j y) w = 0 →
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) d (j y) w = -w) :
    ∃ K : SmoothHorizontalLift q,
      ∀ y : N, K.lift (j y) = mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) j y := by
  let I := 𝓘(ℝ, E)
  let J := 𝓘(ℝ, F)
  let PB := ((q : M → N) *ᵖ (TangentSpace J))
  let U := TotalSpace F PB
  let D (x : M) : E →L[ℝ] E := mfderiv I I d x
  let H₁ (x : M) : TangentSpace J (q x) →L[ℝ] TangentSpace I x :=
    (D (d x)).comp (H.lift (d x))
  -- Pull the same base vector to the reflected point; the base equality retains its native fiber.
  let A (z : U) : U := ⟨d z.proj, z.snd⟩
  have hA : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞ A := by
    intro z
    let e := trivializationAt F (TangentSpace J : N → Type _) (q z.proj)
    let t := e.pullback q
    let : MemTrivializationAtlas t := ⟨⟨e, inferInstance, rfl⟩⟩
    have hz : q z.proj ∈ e.baseSet := mem_baseSet_trivializationAt F (TangentSpace J) (q z.proj)
    have hAz : d z.proj ∈ t.baseSet := by
      change q (d z.proj) ∈ e.baseSet
      rw [hqd]
      exact hz
    apply (t.contMDiffAt_iff (f := A) (t.mem_source.mpr hAz)).mpr
    have hid : ContMDiffAt (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (id : U → U) z := contMDiffAt_id
    have hparts := (t.contMDiffAt_iff (f := id)
      (t.mem_source.mpr (show z.proj ∈ t.baseSet from hz))).mp hid
    refine ⟨d.contMDiff.contMDiffAt.comp z hparts.1, ?_⟩
    apply hparts.2.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro w
    change (e ⟨q (d w.proj), w.snd⟩).2 = (e ⟨q w.proj, w.snd⟩).2
    rw [hqd]
  have hH₁ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E)) ∞
      (fun z : U ↦ (⟨z.proj, H₁ z.proj z.snd⟩ : TangentBundle I M)) := by
    have h := (d.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp
      (H.contMDiff_lift.comp hA)
    apply h.congr
    intro z
    symm
    apply TotalSpace.ext (hd z.proj)
    apply heq_of_eq
    rfl
  have hright₁ (x : M) (v : TangentSpace J (q x)) :
      mfderiv I J q x (H₁ x v) = v := by
    have hfun : (q : M → N) ∘ d = q := funext hqd
    have hchain := mfderiv_comp (d x) (q.contMDiff.mdifferentiable (by simp) _)
      (d.contMDiff.mdifferentiable (by simp) _)
    rw [hfun, hd] at hchain
    change mfderiv I J q x (D (d x) (H.lift (d x) v)) = v
    exact (DFunLike.congr_fun hchain (H.lift (d x) v)).symm.trans (H.right_inv (d x) v)
  -- Average in each actual tangent fiber; local linear charts prove smoothness of the sum.
  let L (x : M) : TangentSpace J (q x) →L[ℝ] TangentSpace I x :=
    (1 / 2 : ℝ) • (H.lift x + H₁ x)
  have hL : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E)) ∞
      (fun z : U ↦ (⟨z.proj, L z.proj z.snd⟩ : TangentBundle I M)) := by
    intro z
    let t := trivializationAt E (TangentSpace I : M → Type _) z.proj
    have hz : z.proj ∈ t.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) z.proj
    apply (t.contMDiffAt_iff (t.mem_source.mpr hz)).mpr
    have h₀ := (t.contMDiffAt_iff (t.mem_source.mpr hz)).mp (H.contMDiff_lift z)
    have h₁ := (t.contMDiffAt_iff (t.mem_source.mpr hz)).mp (hH₁ z)
    refine ⟨h₀.1, ?_⟩
    let mult : E →L[ℝ] E := (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ E
    have hc := mult.contDiff.contMDiff.contMDiffAt.comp z (h₀.2.add h₁.2)
    apply hc.congr_of_eventuallyEq
    filter_upwards [h₀.1.continuousAt.preimage_mem_nhds (t.open_baseSet.mem_nhds hz)] with w hw
    exact (t.linearEquivAt ℝ w.proj hw).map_smul (1 / 2 : ℝ)
      (H.lift w.proj w.snd + H₁ w.proj w.snd) |>.trans
        (congrArg ((1 / 2 : ℝ) • ·) ((t.linearEquivAt ℝ w.proj hw).map_add _ _))
  have hright (x : M) (v : TangentSpace J (q x)) : mfderiv I J q x (L x v) = v := by
    change mfderiv I J q x ((1 / 2 : ℝ) • (H.lift x v + H₁ x v)) = v
    rw [map_smul, map_add, H.right_inv, hright₁, ← two_smul ℝ v, smul_smul]
    norm_num
  let K : SmoothHorizontalLift q := ⟨L, hL, hright⟩
  refine ⟨K, ?_⟩
  intro y
  -- At the fixed section, averaging cancels the actual vertical discrepancy.
  have hqfun : (q : M → N) ∘ j = id := funext hqj
  have hdjfun : (d : M → M) ∘ j = j := funext hdj
  have hqD := mfderiv_comp y (q.contMDiff.mdifferentiable (by simp) _)
    (j.contMDiff.mdifferentiable (by simp) _)
  rw [hqfun, mfderiv_id] at hqD
  have hdD := mfderiv_comp y (d.contMDiff.mdifferentiable (by simp) _)
    (j.contMDiff.mdifferentiable (by simp) _)
  rw [hdjfun] at hdD
  ext v
  let Jv := mfderiv J I j y v
  have hv : mfderiv I J q (j y) (H.lift (j y) v - Jv) = 0 := by
    rw [map_sub, H.right_inv]
    have h := DFunLike.congr_fun hqD v
    change v = mfderiv I J q (j y) Jv at h
    rw [← h, sub_self]
  have hfix : D (j y) Jv = Jv := (DFunLike.congr_fun hdD v).symm
  have hneg := hvertical y (H.lift (j y) v - Jv) hv
  change D (j y) (H.lift (j y) v - Jv) = -(H.lift (j y) v - Jv) at hneg
  rw [map_sub, hfix] at hneg
  have heq : D (j y) (H.lift (j y) v) = -(H.lift (j y) v - Jv) + Jv :=
    (sub_eq_iff_eq_add).mp hneg
  change (1 / 2 : ℝ) • (H.lift (j y) v + H₁ (j y) v) = Jv
  have hH₁val : H₁ (j y) v = D (j y) (H.lift (j y) v) := by
    dsimp only [H₁, ContinuousLinearMap.comp_apply]
    rw [hdj]
    rfl
  rw [hH₁val, heq]
  module

end AtiyahSinger
