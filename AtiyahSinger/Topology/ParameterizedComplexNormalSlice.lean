/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ParameterizedNormalBundle
public import AtiyahSinger.Topology.ComplexificationBundleMap
public import AtiyahSinger.Topology.ComplexificationPullbackTopology
public import AtiyahSinger.Topology.ComplexifiedNormalPullback

/-!
# Complexification of the actual normal comparison on a parameter slice

Public module ID: M1986.

The real quotient comparison is pulled back along the original tangent
projection and then extended from real to complex scalars. The native topology
of the parameter slice is retained, including both pullback layers. The resulting
isomorphism is the actual scalar extension, with the prescribed ordered real and
imaginary coordinates used by the tangent embedding Thom construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold
open scoped ContDiff TensorProduct

attribute [local instance] productFullChartedSpace product_full_isManifold
  tangentBundleFullChartedSpace tangentBundle_full_isManifold
  normalBundleTopology complexifiedNormalPullbackTopology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (β : ContMDiffMap 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) (ℝ × M) (ℝ × N) ∞)
  (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hβ : IsImmersion 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞ β)

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "νf" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
local notation "νβ" => NormalBundle 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) β
local notation "Vf" => NormalModel E F
local notation "Vβ" => NormalModel (ℝ × E) (ℝ × F)
local notation "V" =>
  ((fun p : ℝ × TM ↦ (Prod.fst p, Bundle.TotalSpace.proj (Prod.snd p))) *ᵖ νβ)

set_option maxHeartbeats 600000 in
-- Compare the native iterated pullbacks before introducing their scalar extensions.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual scalar extension of the slice normal comparison is a complex bundle isomorphism. -/
theorem exists_parameterSlice_complexifiedNormalIso (t : ℝ)
    (e : ∀ x, νf x ≃L[ℝ] νβ (t, x))
    (hes :
      letI := normalBundleFiberBundle f hf
      letI := normalBundleVectorBundle f hf
      letI := normalBundleContMDiffVectorBundle f hf
      letI := normalBundleFiberBundle β hβ
      letI := normalBundleVectorBundle β hβ
      letI := normalBundleContMDiffVectorBundle β hβ
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) (𝓘(ℝ, E).prod 𝓘(ℝ, Vβ)) ∞
        (fun z : TotalSpace Vf νf ↦ (⟨z.proj, e z.proj z.snd⟩ :
          TotalSpace Vβ ((smoothParameterSlice E M t : M → ℝ × M) *ᵖ νβ))))
    (heis :
      letI := normalBundleFiberBundle f hf
      letI := normalBundleVectorBundle f hf
      letI := normalBundleContMDiffVectorBundle f hf
      letI := normalBundleFiberBundle β hβ
      letI := normalBundleVectorBundle β hβ
      letI := normalBundleContMDiffVectorBundle β hβ
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vβ)) (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) ∞
        (fun z : TotalSpace Vβ ((smoothParameterSlice E M t : M → ℝ × M) *ᵖ νβ) ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace Vf νf))) :
    letI : ∀ p : ℝ × TM, AddCommGroup (V p) :=
      fun p ↦ by change AddCommGroup (νβ (p.1, p.2.proj)); infer_instance
    letI : ∀ p : ℝ × TM, Module ℝ (V p) :=
      fun p ↦ by change Module ℝ (νβ (p.1, p.2.proj)); infer_instance
    letI := ComplexBundle.complexificationTopology Vβ V
    let B : (ℝ × TM) → Type _ := fun p : ℝ × TM ↦ ℂ ⊗[ℝ] V p
    let D : TM → Type _ := (fun z : TM ↦ (t, z)) *ᵖ B
    letI gD : ∀ z : TM, AddCommGroup (D z) := fun z ↦ by
      change AddCommGroup (ℂ ⊗[ℝ] V (t, z)); infer_instance
    letI mD : ∀ z : TM, Module ℂ (D z) := fun z ↦ by
      change Module ℂ (ℂ ⊗[ℝ] V (t, z)); infer_instance
    letI tD : TopologicalSpace (TotalSpace Unit D) :=
      Pullback.TotalSpace.topologicalSpace Unit B (fun z : TM ↦ (t, z))
    letI gF : ∀ z : TM, AddCommGroup (ComplexifiedNormalPullback f z) := fun z ↦ by
      change AddCommGroup (ℂ ⊗[ℝ] νf z.proj); infer_instance
    letI mF : ∀ z : TM, Module ℂ (ComplexifiedNormalPullback f z) := fun z ↦ by
      change Module ℂ (ℂ ⊗[ℝ] νf z.proj); infer_instance
    let l (z : TM) : ComplexifiedNormalPullback f z ≃ₗ[ℂ] D z := by
      change (ℂ ⊗[ℝ] νf z.proj) ≃ₗ[ℂ] (ℂ ⊗[ℝ] νβ (t, z.proj))
      exact (e z.proj).toLinearEquiv.baseChange ℝ ℂ _ _
    ∃ U : @ComplexBundle.Iso TM (ComplexifiedNormalPullback f) D gF mF gD mD
        (complexifiedNormalPullbackTopology f) tD,
      ∀ (z : TM) (v : ComplexifiedNormalPullback f z), U.linearEquiv z v = l z v := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let := normalBundleFiberBundle β hβ
  let := normalBundleVectorBundle β hβ
  let := normalBundleContMDiffVectorBundle β hβ
  let (p : ℝ × TM) : AddCommGroup (V p) := by
    change AddCommGroup (νβ (p.1, p.2.proj))
    infer_instance
  let (p : ℝ × TM) : Module ℝ (V p) := by
    change Module ℝ (νβ (p.1, p.2.proj))
    infer_instance
  let := ComplexBundle.complexificationTopology Vβ V
  let p : C(TM, M) := ⟨fun z ↦ z.proj, FiberBundle.continuous_proj _ _⟩
  let s : C(TM, ℝ × TM) := ⟨fun z ↦ (t, z), continuous_const.prodMk continuous_id⟩
  let i : C(M, ℝ × M) := ⟨smoothParameterSlice E M t,
    (smoothParameterSlice E M t).contMDiff.continuous⟩
  let ψ : C(ℝ × TM, ℝ × M) :=
    ⟨fun z ↦ (z.1, z.2.proj), continuous_fst.prodMk (p.continuous.comp continuous_snd)⟩
  let W := (p : TM → M) *ᵖ νf
  let Z := (s : TM → ℝ × TM) *ᵖ V
  let (z : TM) : AddCommGroup (W z) := by change AddCommGroup (νf z.proj); infer_instance
  let (z : TM) : Module ℝ (W z) := by change Module ℝ (νf z.proj); infer_instance
  let (z : TM) : AddCommGroup (Z z) := by
    change AddCommGroup (νβ (t, z.proj)); infer_instance
  let (z : TM) : Module ℝ (Z z) := by change Module ℝ (νβ (t, z.proj)); infer_instance
  let L (z : TM) : W z ≃ₗ[ℝ] Z z := (e z.proj).toLinearEquiv
  -- Lift to the original normal bundles, then retain each of the two pullback bases.
  have hL : Continuous (fun z : TotalSpace Vf W ↦
      (⟨z.proj, L z.proj z.snd⟩ : TotalSpace Vβ Z)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Vβ V s).continuous_iff]
    refine (Pullback.continuous_proj Vf νf p).prodMk ?_
    rw [(inducing_pullbackTotalSpaceEmbedding Vβ νβ ψ).continuous_iff]
    refine (s.continuous.comp (Pullback.continuous_proj Vf νf p)).prodMk ?_
    exact (Pullback.continuous_lift Vβ νβ i).comp
      (hes.continuous.comp (Pullback.continuous_lift Vf νf p))
  have hLi : Continuous (fun z : TotalSpace Vβ Z ↦
      (⟨z.proj, (L z.proj).symm z.snd⟩ : TotalSpace Vf W)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Vf νf p).continuous_iff]
    refine (Pullback.continuous_proj Vβ V s).prodMk ?_
    let k : TotalSpace Vβ Z → TotalSpace Vβ ((i : M → ℝ × M) *ᵖ νβ) :=
      fun z ↦ ⟨z.proj.proj, z.snd⟩
    have hk : Continuous k := by
      rw [(inducing_pullbackTotalSpaceEmbedding Vβ νβ i).continuous_iff]
      exact (p.continuous.comp (Pullback.continuous_proj Vβ V s)).prodMk
        ((Pullback.continuous_lift Vβ νβ ψ).comp (Pullback.continuous_lift Vβ V s))
    exact heis.continuous.comp hk
  have htop := ComplexBundle.complexificationTopology_pullback Vβ V s
  let B := fun q : ℝ × TM ↦ ℂ ⊗[ℝ] V q
  let D := (s : TM → ℝ × TM) *ᵖ B
  let (z : TM) : AddCommGroup (D z) := by
    change AddCommGroup (ℂ ⊗[ℝ] V (t, z)); infer_instance
  let (z : TM) : Module ℂ (D z) := by
    change Module ℂ (ℂ ⊗[ℝ] V (t, z)); infer_instance
  let : TopologicalSpace (TotalSpace Unit D) :=
    Pullback.TotalSpace.topologicalSpace Unit B (s : TM → ℝ × TM)
  let U : ComplexBundle.Iso (X := TM) (ComplexifiedNormalPullback f) D := {
    linearEquiv z := (L z).baseChange ℝ ℂ _ _
    continuous_total := by
      have hc := ComplexBundle.continuous_complexification_map
        (fun z ↦ (L z).toLinearMap) hL
      change @Continuous _ _ (ComplexBundle.complexificationTopology Vf W)
        (ComplexBundle.complexificationTopology Vβ Z) _ at hc
      rw [htop] at hc
      exact hc
    continuous_symm := by
      have hc := ComplexBundle.continuous_complexification_map
        (fun z ↦ (L z).symm.toLinearMap) hLi
      change @Continuous _ _ (ComplexBundle.complexificationTopology Vβ Z)
        (ComplexBundle.complexificationTopology Vf W) _ at hc
      rw [htop] at hc
      exact hc }
  exact ⟨U, fun _ _ ↦ rfl⟩

end AtiyahSinger
