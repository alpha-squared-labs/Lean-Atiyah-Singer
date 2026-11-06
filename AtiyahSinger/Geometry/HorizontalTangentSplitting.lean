/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleSubbundle
public import AtiyahSinger.Geometry.SubmersionCotangentSplitting

/-!
# Tangent assembly for a specified horizontal lift

Public module ID: M1280.

The original tangent bundle of a submersion is the smooth direct sum of its
pulled base tangent bundle and its vertical kernel. The assembly map is the
given horizontal lift plus the actual vertical inclusion. Its inverse uses
the same differential, so the two ordered components are fixed.

This is the standard tangent splitting underlying the frame-sphere tube
comparison. It preserves the selected native atlases and assumes neither a
compatible metric nor a global frame. Only the supplied smooth lift is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Topology
open scoped ContDiff

attribute [local instance] verticalTangentTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (q : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1400000 in
-- The original horizontal and vertical maps are assembled in one native bundle chart.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A specified horizontal lift assembles the two actual tangent summands smoothly. -/
theorem SmoothHorizontalLift.exists_tangentAssemblyEquiv
    (hq : IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ q) (H : SmoothHorizontalLift q) :
    letI := verticalTangentFiberBundle q hq
    letI := verticalTangentVectorBundle q hq
    letI := verticalTangentContMDiffVectorBundle q hq
    let K := VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) q
    let B := (q : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))
    ∃ e : ∀ x, (TangentSpace 𝓘(ℝ, F) (q x) × K x) ≃L[ℝ]
        TangentSpace 𝓘(ℝ, E) x,
      (∀ x v, e x v = H.lift x v.1 + v.2.val) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F × VerticalTangentModel E F))
        (𝓘(ℝ, E).tangent) ∞
        (fun z : TotalSpace (F × VerticalTangentModel E F) (B ×ᵇ K) ↦
          (⟨z.proj, e z.proj z.snd⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      ContMDiff (𝓘(ℝ, E).tangent)
        (𝓘(ℝ, E).prod 𝓘(ℝ, F × VerticalTangentModel E F)) ∞
        (fun z : TangentBundle 𝓘(ℝ, E) M ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ :
            TotalSpace (F × VerticalTangentModel E F) (B ×ᵇ K))) := by
  classical
  let I := 𝓘(ℝ, E)
  let J := 𝓘(ℝ, F)
  let := verticalTangentFiberBundle q hq
  let := verticalTangentVectorBundle q hq
  let := verticalTangentContMDiffVectorBundle q hq
  let K := VerticalTangentFiber I J q
  let B := (q : M → N) *ᵖ (TangentSpace J)
  let (x : M) : AddCommGroup (B x) := by
    change AddCommGroup (TangentSpace J (q x))
    infer_instance
  let (x : M) : Module ℝ (B x) := by
    change Module ℝ (TangentSpace J (q x))
    infer_instance
  let (x : M) : IsTopologicalAddGroup (B x) := by
    change IsTopologicalAddGroup (TangentSpace J (q x))
    infer_instance
  let (x : M) : ContinuousSMul ℝ (B x) := by
    change ContinuousSMul ℝ (TangentSpace J (q x))
    infer_instance
  let (x : M) : T2Space (B x) := by
    change T2Space (TangentSpace J (q x))
    infer_instance
  let (x : M) : FiniteDimensional ℝ (B x) := by
    change FiniteDimensional ℝ (TangentSpace J (q x))
    infer_instance
  let V := VerticalTangentModel E F
  let W := B ×ᵇ K
  let D (x : M) : TangentSpace I x →L[ℝ] TangentSpace J (q x) := mfderiv I J q x
  let Q (x : M) : W x →L[ℝ] TangentSpace I x :=
    (H.lift x).comp (ContinuousLinearMap.fst ℝ (B x) (K x)) +
      (LinearMap.ker (D x).toLinearMap).subtypeL.comp
        (ContinuousLinearMap.snd ℝ (B x) (K x))
  -- The differential recovers the first component; subtraction recovers the vertical one.
  have hbij (x : M) : Bijective (Q x) := by
    constructor
    · intro u v h
      have hfirst : u.1 = v.1 := by
        have hd := congrArg (D x) h
        change D x (H.lift x u.1 + u.2.val) = D x (H.lift x v.1 + v.2.val) at hd
        have hu : D x (H.lift x u.1) = u.1 := H.right_inv x u.1
        have hv : D x (H.lift x v.1) = v.1 := H.right_inv x v.1
        have hku : D x u.2.val = 0 := u.2.property
        have hkv : D x v.2.val = 0 := v.2.property
        simpa only [map_add, hu, hv, hku, hkv, add_zero] using hd
      apply Prod.ext hfirst
      apply Subtype.val_injective
      change H.lift x u.1 + u.2.val = H.lift x v.1 + v.2.val at h
      rw [hfirst] at h
      exact add_left_cancel h
    · intro w
      let v : K x := ⟨w - H.lift x (D x w), by
        change D x (w - H.lift x (D x w)) = 0
        rw [map_sub, H.right_inv x, sub_self]⟩
      refine ⟨(D x w, v), ?_⟩
      change H.lift x (D x w) + (w - H.lift x (D x w)) = w
      abel
  let e (x : M) : W x ≃L[ℝ] TangentSpace I x := by
    let l : W x ≃ₗ[ℝ] TangentSpace I x := LinearEquiv.ofBijective (Q x).toLinearMap (hbij x)
    exact LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ) (E := W x)
      (F := TangentSpace I x) l
  have he (x : M) (v : W x) : e x v = H.lift x v.1 + v.2.val := rfl
  -- Both summands are smooth in the original tangent atlas, with the same base point.
  have hfirst : ContMDiff (I.prod 𝓘(ℝ, F × V)) (I.prod 𝓘(ℝ, F)) ∞
      (fun z : TotalSpace (F × V) W ↦ (⟨z.proj, z.snd.1⟩ : TotalSpace F B)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj W, ?_⟩
    have hc := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id : ContMDiffAt (I.prod 𝓘(ℝ, F × V))
        (I.prod 𝓘(ℝ, F × V)) ∞ id z)).2
    exact (ContinuousLinearMap.fst ℝ F V).contDiff.contMDiff.contMDiffAt.comp z hc
  have hsecond : ContMDiff (I.prod 𝓘(ℝ, F × V)) (I.prod 𝓘(ℝ, V)) ∞
      (fun z : TotalSpace (F × V) W ↦ (⟨z.proj, z.snd.2⟩ : TotalSpace V K)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj W, ?_⟩
    have hc := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id : ContMDiffAt (I.prod 𝓘(ℝ, F × V))
        (I.prod 𝓘(ℝ, F × V)) ∞ id z)).2
    exact (ContinuousLinearMap.snd ℝ F V).contDiff.contMDiff.contMDiffAt.comp z hc
  have hH := H.contMDiff_lift.comp hfirst
  have hK := (smoothVerticalTangentInclusion q hq).contMDiff.comp hsecond
  have hQ : ContMDiff (I.prod 𝓘(ℝ, F × V)) I.tangent ∞
      (fun z : TotalSpace (F × V) W ↦
        (⟨z.proj, e z.proj z.snd⟩ : TangentBundle I M)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj W, ?_⟩
    let t := trivializationAt E (TangentSpace I) z.proj
    have hs := (Bundle.contMDiffAt_totalSpace.mp (hH z)).2.add
      (Bundle.contMDiffAt_totalSpace.mp (hK z)).2
    apply hs.congr_of_eventuallyEq
    filter_upwards [(FiberBundle.continuous_proj (F × V) W).continuousAt
      (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) z.proj))]
        with w hw
    change (t ⟨w.proj, e w.proj w.snd⟩).2 =
      (t ⟨w.proj, H.lift w.proj w.snd.1⟩).2 + (t ⟨w.proj, w.snd.2.val⟩).2
    rw [he]
    simp only [← t.continuousLinearMapAt_apply_of_mem ℝ hw, map_add]
  refine ⟨e, he, hQ, ?_⟩
  -- The smooth inverse is detected through this same injective assembly map.
  apply contMDiff_bundleMap_of_comp_injective (I := I)
    (W := W) (V₀ := TangentSpace I) (Z := TangentSpace I)
    (F := F × V) (G := E) (H := E)
    (fun x ↦ (e x).toContinuousLinearMap) (fun x ↦ (e x).symm.toContinuousLinearMap)
    hQ (fun x ↦ (e x).injective)
  apply contMDiff_id.congr
  intro z
  change (⟨z.proj, e z.proj ((e z.proj).symm z.snd)⟩ : TangentBundle I M) = z
  rw [(e z.proj).apply_symm_apply]

end AtiyahSinger
