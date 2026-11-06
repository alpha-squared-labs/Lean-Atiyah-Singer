/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.NormalBundle
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# The normal derivative of a map from a vector bundle

Public module ID: M1108.

A smooth map whose zero section is a specified immersion has a smooth normal
derivative on the original vector fibers. Its value is the derivative of the
actual radial curve, followed by the original quotient normal map. Native
bundle charts are retained; no invertibility or tubular property is assumed.

This standard normal differential supplies the radial map used to normalize
the actual frame-sphere tangent coordinates. Exact-sequence identities and
invertibility enter as additional results in that application.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (V : M → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace G V)] [FiberBundle G V] [VectorBundle ℝ G V]
  [ContMDiffVectorBundle ∞ G V 𝓘(ℝ, E)]

set_option maxSynthPendingDepth 35 in
set_option maxHeartbeats 1500000 in
-- One joint radial family gives the derivative in the original pulled tangent atlas.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual radial derivative descends smoothly to the prescribed quotient normal bundle. -/
theorem exists_bundle_normalDerivative
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (a : ContMDiffMap (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) (TotalSpace G V) N ∞)
    (hzero : ∀ x, a ⟨x, 0⟩ = f x) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    ∃ D : ∀ x, V x →L[ℝ] NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x,
      (∀ x v, D x v =
        (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun t : ℝ ↦ a ⟨x, t • v⟩) 0
            ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G))
        (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) ∞
        (fun z : TotalSpace G V ↦
          (⟨z.proj, D z.proj z.snd⟩ :
            TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f))) := by
  classical
  let I := 𝓘(ℝ, E)
  let J := 𝓘(ℝ, F)
  let A := I.prod 𝓘(ℝ, G)
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let ν := NormalBundle I J f
  let T := (f : M → N) *ᵖ (TangentSpace J)
  let φ (x : M) (v : V x) : N := a ⟨x, v⟩
  have hφ (x : M) : ContMDiff 𝓘(ℝ, V x) J ∞ (φ x) := by
    apply a.contMDiff.comp
    intro v
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_const, ?_⟩
    let t := trivializationAt G V x
    have hx : x ∈ t.baseSet := mem_baseSet_trivializationAt G V x
    apply (t.continuousLinearMapAt ℝ x).contDiff.contMDiff.contMDiffAt.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall
      (fun w ↦ (t.continuousLinearMapAt_apply_of_mem ℝ hx w).symm)
  let L (x : M) : V x →L[ℝ] F := mfderiv 𝓘(ℝ, V x) J (φ x) 0
  let ρ (z : TotalSpace G V) (t : ℝ) : N := a ⟨z.proj, t • z.snd⟩
  have hρ0 (z : TotalSpace G V) : ρ z 0 = f z.proj := by
    simpa only [ρ, zero_smul] using hzero z.proj
  -- The chain rule identifies the linear fiber derivative with each actual radial curve.
  have hradial (z : TotalSpace G V) :
      (mfderiv 𝓘(ℝ, ℝ) J (ρ z) 0
        ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : F) = L z.proj z.snd := by
    let l : ℝ →L[ℝ] V z.proj := (ContinuousLinearMap.id ℝ ℝ).smulRight z.snd
    have hfun : ρ z = φ z.proj ∘ l := rfl
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, V z.proj)) (I'' := J) 0
      ((hφ z.proj).mdifferentiable (by simp) (l 0))
      (l.hasFDerivAt.hasMFDerivAt.mdifferentiableAt)
    have hl : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V z.proj) l 0 = l :=
      l.hasFDerivAt.hasMFDerivAt.mfderiv
    rw [← hfun, show l 0 = 0 from map_zero l, hl] at hchain
    have h := DFunLike.congr_fun hchain
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1)
    have hunit : l ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) = z.snd := by
      change (1 : ℝ) • z.snd = z.snd
      exact one_smul ℝ z.snd
    change (mfderiv 𝓘(ℝ, ℝ) J (ρ z) 0
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) : F) =
        L z.proj (l ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1)) at h
    rw [hunit] at h
    exact h
  have hρ : ContMDiff (A.prod 𝓘(ℝ, ℝ)) J ∞ (Function.uncurry ρ) := by
    apply a.contMDiff.comp
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    have hb : ContMDiffAt (A.prod 𝓘(ℝ, ℝ)) I ∞
        (fun w : TotalSpace G V × ℝ ↦ w.1.proj) z :=
      (Bundle.contMDiffAt_proj V).comp z contMDiffAt_fst
    refine ⟨hb, ?_⟩
    have hv := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_fst : ContMDiffAt (A.prod 𝓘(ℝ, ℝ)) A ∞
        (fun w : TotalSpace G V × ℝ ↦ w.1) z)).2
    apply (contMDiffAt_snd.smul hv).congr_of_eventuallyEq
    let t := trivializationAt G V z.1.proj
    filter_upwards [hb.continuousAt
      (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt G V z.1.proj))] with w hw
    change (t ⟨w.1.proj, w.2 • w.1.snd⟩).2 = w.2 • (t w.1).2
    simp only [← t.continuousLinearMapAt_apply_of_mem ℝ hw, map_smul]
  -- Joint differentiation proves smoothness before passing to the original normal quotient.
  have hL : ContMDiff A (I.prod 𝓘(ℝ, F)) ∞
      (fun z : TotalSpace G V ↦ (⟨z.proj, L z.proj z.snd⟩ : TotalSpace F T)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj V, ?_⟩
    have hd := ContMDiffAt.mfderiv_apply ρ (fun _ : TotalSpace G V ↦ (0 : ℝ)) id
      (fun _ : TotalSpace G V ↦ (1 : ℝ)) (hρ (z, 0)) contMDiffAt_const contMDiffAt_id
      contMDiffAt_const (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)
    apply hd.congr_of_eventuallyEq
    let t := trivializationAt F (TangentSpace J) (f z.proj)
    have hb := f.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj V)
    filter_upwards [hb.continuousAt
      (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F (TangentSpace J) (f z.proj)))]
        with w hw
    dsimp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, id_eq,
      ContinuousLinearMap.comp_apply]
    rw [TangentBundle.symmL_model_space]
    change (t ⟨f w.proj, L w.proj w.snd⟩).2 =
      (trivializationAt F (TangentSpace J) (ρ z 0)).continuousLinearMapAt ℝ (ρ w 0)
        (mfderiv 𝓘(ℝ, ℝ) J (ρ w) 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))
    rw [hradial, hρ0 z, hρ0 w]
    exact (t.continuousLinearMapAt_apply_of_mem ℝ hw _).symm
  let D (x : M) : V x →L[ℝ] ν x :=
    (LinearMap.range (mfderiv I J f x).toLinearMap).mkQL.comp (L x)
  refine ⟨D, ?_, (smoothNormalQuotientMap f hf).contMDiff.comp hL⟩
  intro x v
  change (LinearMap.range (mfderiv I J f x).toLinearMap).mkQ (L x v) = _
  rw [← hradial ⟨x, v⟩]

end AtiyahSinger
