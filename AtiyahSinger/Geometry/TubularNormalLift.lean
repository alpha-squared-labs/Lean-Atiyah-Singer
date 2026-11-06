/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TubularNeighborhood
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The normal lift induced by a specified tubular neighborhood

Public module ID: M1506.

Differentiate the given tube in its own normal fibers at zero. Normalization
makes this a right inverse of the original quotient. Its smooth dependence is
proved by differentiating the jointly smooth radial family, so no unrelated
splitting or connection replaces the actual derivative of the chosen tube.

This is the same-witness lift needed in the SG III.13 nested-tube comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)

local notation "V" => NormalModel E F
local notation "ν" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- The actual zero-fiber derivative of a chosen tube is a smooth normal right inverse. -/
theorem TubularNeighborhood.exists_normalLift (T : TubularNeighborhood f hf) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    ∃ L : ∀ x : M, ν x →L[ℝ] TangentSpace 𝓘(ℝ, F) (f x),
      (∀ x v, (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
        (L x v) = v) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, V)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
        (fun z : TotalSpace V ν ↦ (⟨z.proj, L z.proj z.snd⟩ :
          TotalSpace F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))))) ∧
      ∀ x v,
        let e := (trivializationAt V ν x).continuousLinearEquivAt ℝ x
          (mem_baseSet_trivializationAt V ν x)
        L x v = mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F)
          (fun w ↦ (T.diffeomorph ⟨x, e.symm w⟩ : N)) 0
            ((NormedSpace.fromTangentSpace (0 : V)).symm (e v)) := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let NB := TotalSpace V ν
  let I := 𝓘(ℝ, E).prod 𝓘(ℝ, V)
  let e (x : M) := (trivializationAt V ν x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt V ν x)
  let b (x : M) : V → N := fun w ↦ T.diffeomorph ⟨x, (e x).symm w⟩
  let L (x : M) : ν x →L[ℝ] TangentSpace 𝓘(ℝ, F) (f x) :=
    ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) (b x) 0).comp
      (NormedSpace.fromTangentSpace (0 : V)).symm.toContinuousLinearMap).comp
        (e x).toContinuousLinearMap
  have hT : ContMDiff I 𝓘(ℝ, F) ∞ (T.totalMap f hf) :=
    contMDiff_subtype_val.comp T.diffeomorph.contMDiff
  have hb (x : M) : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, F) ∞ (b x) := by
    apply hT.comp
    intro w
    let t := trivializationAt V ν x
    have hx : x ∈ t.baseSet := mem_baseSet_trivializationAt V ν x
    rw [t.contMDiffAt_iff (t.mem_source.mpr hx)]
    refine ⟨contMDiffAt_const, ?_⟩
    apply contMDiffAt_id.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro u
    change (t ⟨x, (e x).symm u⟩).2 = u
    rw [t.apply_eq_prod_continuousLinearEquivAt ℝ x hx]
    exact (e x).apply_symm_apply u
  -- Differentiating radial curves identifies this chart definition intrinsically.
  let r (z : NB) (a : ℝ) : N := T.totalMap f hf ⟨z.proj, a • z.snd⟩
  have hr0 (z : NB) : r z 0 = f z.proj := by
    simp only [r, zero_smul]
    exact T.map_zero z.proj
  have hr : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ (Function.uncurry r) := by
    apply hT.comp
    intro p
    apply Bundle.contMDiffAt_totalSpace.mpr
    have hbase : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : NB × ℝ ↦ q.1.proj) p :=
      (Bundle.contMDiffAt_proj ν).comp p contMDiffAt_fst
    refine ⟨hbase, ?_⟩
    let t := trivializationAt V ν p.1.proj
    have hvec := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_fst : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : NB × ℝ ↦ q.1) p)).2
    apply (contMDiffAt_snd.smul hvec).congr_of_eventuallyEq
    filter_upwards [hbase.continuousAt
      (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt V ν p.1.proj))] with q hq
    change (t ⟨q.1.proj, q.2 • q.1.snd⟩).2 = q.2 • (t q.1).2
    simp only [← t.continuousLinearMapAt_apply_of_mem ℝ hq, map_smul]
    rw [t.continuousLinearMapAt_apply_of_mem ℝ hq]
  have hradial (z : NB) : @Eq F (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (r z) 0
      ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)) (L z.proj z.snd) := by
    let c : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight (e z.proj z.snd)
    have heq : r z = b z.proj ∘ c := by
      funext a
      change T.totalMap f hf ⟨z.proj, a • z.snd⟩ =
        T.totalMap f hf ⟨z.proj, (e z.proj).symm (a • e z.proj z.snd)⟩
      rw [map_smul, (e z.proj).symm_apply_apply]
    have hc0 : c (0 : ℝ) = 0 := c.map_zero
    have hcder : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) c 0 =
        ((NormedSpace.fromTangentSpace (c 0)).symm.toContinuousLinearMap.comp c).comp
          (NormedSpace.fromTangentSpace (0 : ℝ)).toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv, c.fderiv]
      rfl
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, V))
      (I'' := 𝓘(ℝ, F)) 0
      (show MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, F) (b z.proj) (c 0) from by
        rw [hc0]
        exact (hb z.proj).mdifferentiableAt (x := 0) (by simp))
      ((c.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp))
    rw [hcder] at hchain
    have hpoint := DFunLike.congr_fun hchain
      ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (b z.proj ∘ c) 0
        ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) =
      mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) (b z.proj) (c 0)
        ((NormedSpace.fromTangentSpace (c 0)).symm
          (c ((NormedSpace.fromTangentSpace (0 : ℝ))
            ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)))) at hpoint
    rw [ContinuousLinearEquiv.apply_symm_apply] at hpoint
    have hc1 : c (1 : ℝ) = e z.proj z.snd := by
      simp only [c, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul]
    -- Compare at the equal base points by congruence, keeping native tangent instances intact.
    calc
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (r z) 0
          ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : F) =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (b z.proj ∘ c) 0
          ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) :=
        congrArg (fun k : ℝ → N ↦ (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) k 0
          ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : F)) heq
      _ = mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) (b z.proj) (c 0)
          ((NormedSpace.fromTangentSpace (c 0)).symm (e z.proj z.snd)) :=
        hpoint.trans (congrArg (fun v : V ↦
          mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) (b z.proj) (c 0)
            ((NormedSpace.fromTangentSpace (c 0)).symm v)) hc1)
      _ = mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) (b z.proj) 0
          ((NormedSpace.fromTangentSpace (0 : V)).symm (e z.proj z.snd)) :=
        congrArg (fun u : V ↦ (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) (b z.proj) u
          ((NormedSpace.fromTangentSpace u).symm (e z.proj z.snd)) : F)) hc0
      _ = L z.proj z.snd := rfl
  refine ⟨L, ?_, ?_, fun _ _ ↦ rfl⟩
  · intro x v
    exact (T.normal_deriv x (e x v)).trans ((e x).symm_apply_apply v)
  · -- Smooth differentiation of the same radial family gives the native bundle map.
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj ν, ?_⟩
    have hd := ContMDiffAt.mfderiv_apply r (fun _ : NB ↦ (0 : ℝ)) id
      (fun _ : NB ↦ (1 : ℝ)) (hr (z, 0)) contMDiffAt_const contMDiffAt_id
        contMDiffAt_const (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)
    apply hd.congr_of_eventuallyEq
    let t := trivializationAt F (TangentSpace 𝓘(ℝ, F)) (f z.proj)
    have hbase := f.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj ν)
    filter_upwards [hbase.continuousAt
      (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F
        (TangentSpace 𝓘(ℝ, F)) (f z.proj)))] with w hw
    dsimp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, id_eq,
      ContinuousLinearMap.comp_apply]
    rw [TangentBundle.symmL_model_space]
    change (t ⟨f w.proj, L w.proj w.snd⟩).2 =
      (trivializationAt F (TangentSpace 𝓘(ℝ, F)) (r z 0)).continuousLinearMapAt ℝ (r w 0)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (r w) 0
          ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))
    rw [hradial]
    rw [hr0 z, hr0 w]
    change (t ⟨f w.proj, L w.proj w.snd⟩).2 =
      t.continuousLinearMapAt ℝ (f w.proj) (L w.proj w.snd)
    exact (t.continuousLinearMapAt_apply_of_mem ℝ hw _).symm

end AtiyahSinger
