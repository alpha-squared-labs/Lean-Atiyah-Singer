/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ZeroVelocityNormalPullback
public import AtiyahSinger.Topology.ComplexificationBundle

/-!
# The complex normal bundle of a parameterized tangent embedding

Public module ID: M1985.

Pull the original real normal bundle of the parameter embedding back to the
vertical tangent cylinder and complexify it with the prescribed real/imaginary
order. The zero-velocity normal comparison and a normalized tangent splitting
identify its actual total space with the normal bundle of the vertical tangent
cylinder. Both directions use the native bundle and pullback topologies.

This constructs the fixed complex family used by the moving-embedding Thom
comparison in SG III.13; it does not posit a compatible family of splittings.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff TensorProduct

attribute [local instance] productFullChartedSpace product_full_isManifold
  tangentBundleFullChartedSpace tangentBundle_full_isManifold normalBundleTopology

/-- Forget the tangent vector while retaining the original parameter and base point. -/
def parameterTangentProjection (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] :
    ContMDiffMap 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × E)
      (ℝ × TangentBundle 𝓘(ℝ, E) M) (ℝ × M) ∞ :=
  ⟨fun p ↦ (p.1, p.2.proj), by
    simpa only [modelWithCornersSelf_prod] using!
      ((contMDiff_id (I := 𝓘(ℝ, ℝ)) (M := ℝ)).prodMap
        (smoothTangentBundleProjection E M).contMDiff)⟩

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  (β : ContMDiffMap 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) (ℝ × M) (ℝ × N) ∞)
  (hβ : IsSmoothEmbedding 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞ β)
  (H : ContMDiffMap 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F))
    (ℝ × TangentBundle 𝓘(ℝ, E) M) (ℝ × TangentBundle 𝓘(ℝ, F) N) ∞)
  (hH : IsImmersion 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) ∞ H)

local notation "P" => ℝ × TangentBundle 𝓘(ℝ, E) M
local notation "A" => ℝ × (E × E)
local notation "Vβ" => NormalModel (ℝ × E) (ℝ × F)
local notation "VTβ" => NormalModel ((ℝ × E) × (ℝ × E)) ((ℝ × F) × (ℝ × F))
local notation "VH" => NormalModel (ℝ × (E × E)) (ℝ × (F × F))
local notation "νβ" => NormalBundle 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) β
local notation "νTβ" => NormalBundle 𝓘(ℝ, (ℝ × E) × (ℝ × E))
  𝓘(ℝ, (ℝ × F) × (ℝ × F)) (smoothTangentMap β)
local notation "νH" => NormalBundle 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) H
local notation "ψ" => parameterTangentProjection E M
local notation "jM" => zeroVelocityInclusion E M
local notation "V" => ((ψ : P → ℝ × M) *ᵖ νβ)

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The fixed complex normal family has the exact ordered total-space identification. -/
theorem exists_parameterizedComplexNormal_homeomorph
    (eZ : ∀ p : P, νH p ≃L[ℝ] νTβ (jM p))
    (heZ :
      letI := normalBundleFiberBundle H hH
      letI := normalBundleVectorBundle H hH
      letI := normalBundleContMDiffVectorBundle H hH
      letI := normalBundleFiberBundle (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
      letI := normalBundleVectorBundle (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
      letI := normalBundleContMDiffVectorBundle
        (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
      ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, VH)) (𝓘(ℝ, A).prod 𝓘(ℝ, VTβ)) ∞
        (fun z : TotalSpace VH νH ↦
          (⟨z.proj, eZ z.proj z.snd⟩ : TotalSpace VTβ ((jM : _ → _) *ᵖ νTβ))))
    (Sβ : TangentNormalSplitting β hβ) :
    letI : ∀ p : P, AddCommGroup (V p) :=
      fun p ↦ by change AddCommGroup (νβ (ψ p)); infer_instance
    letI : ∀ p : P, Module ℝ (V p) :=
      fun p ↦ by change Module ℝ (νβ (ψ p)); infer_instance
    letI := ComplexBundle.complexificationTopology Vβ V
    let r (p : P) : (ℂ ⊗[ℝ] V p) ≃ₗ[ℝ] (V p × V p) := complexificationReIm (V p)
    ComplexBundle.IsFiniteRank (fun p : P ↦ ℂ ⊗[ℝ] V p) ∧
      ∃ C : TotalSpace Unit (fun p : P ↦ ℂ ⊗[ℝ] V p) ≃ₜ TotalSpace VH νH,
        ∀ (p : P) (v : ℂ ⊗[ℝ] V p), C ⟨p, v⟩ = ⟨p, (eZ p).symm
          ((Sβ.equiv (jM p)).symm (r p v))⟩ := by
  classical
  let := normalBundleFiberBundle β hβ.isImmersion
  let := normalBundleVectorBundle β hβ.isImmersion
  let := normalBundleContMDiffVectorBundle β hβ.isImmersion
  let := normalBundleFiberBundle H hH
  let := normalBundleVectorBundle H hH
  let := normalBundleContMDiffVectorBundle H hH
  let := normalBundleFiberBundle (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
  let := normalBundleVectorBundle (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
  let (p : P) : AddCommGroup (V p) := by
    change AddCommGroup (νβ (ψ p))
    infer_instance
  let (p : P) : Module ℝ (V p) := by
    change Module ℝ (νβ (ψ p))
    infer_instance
  let (p : P) : IsTopologicalAddGroup (V p) :=
    inferInstanceAs (IsTopologicalAddGroup (νβ (ψ p)))
  let (p : P) : ContinuousSMul ℝ (V p) := inferInstanceAs (ContinuousSMul ℝ (νβ (ψ p)))
  let := ComplexBundle.complexificationTopology Vβ V
  let D := V ×ᵇ V
  let (p : P) : AddCommGroup (D p) := inferInstanceAs (AddCommGroup (V p × V p))
  let (p : P) : Module ℝ (D p) := inferInstanceAs (Module ℝ (V p × V p))
  let (p : P) : IsTopologicalAddGroup (D p) :=
    inferInstanceAs (IsTopologicalAddGroup (V p × V p))
  let (p : P) : ContinuousSMul ℝ (D p) :=
    inferInstanceAs (ContinuousSMul ℝ (V p × V p))
  let d (p : P) : νH p ≃L[ℝ] D p := (eZ p).trans (Sβ.equiv (jM p))
  -- Lift the same quotient comparison, then apply the supplied normalized splitting.
  have hLift : ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, VH))
      (𝓘(ℝ, (ℝ × E) × (ℝ × E)).prod 𝓘(ℝ, VTβ)) ∞
      (fun z : TotalSpace VH νH ↦ (⟨jM z.proj, eZ z.proj z.snd⟩ : TotalSpace VTβ νTβ)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨(zeroVelocityInclusion E M).contMDiff.contMDiffAt.comp z
        (Bundle.contMDiffAt_proj νH),
      (Bundle.contMDiffAt_totalSpace.mp (heZ z)).2⟩
  have hSplit := Sβ.contMDiff_toFun.comp hLift
  have hforward : ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, VH))
      (𝓘(ℝ, A).prod 𝓘(ℝ, Vβ × Vβ)) ∞
      (fun z : TotalSpace VH νH ↦ (⟨z.proj, d z.proj z.snd⟩ : TotalSpace (Vβ × Vβ) D)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨Bundle.contMDiffAt_proj νH, (Bundle.contMDiffAt_totalSpace.mp (hSplit z)).2⟩
  -- Smooth fiberwise invertibility gives continuity of the inverse in the same native atlas.
  have hinverse : ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, Vβ × Vβ))
      (𝓘(ℝ, A).prod 𝓘(ℝ, VH)) ∞
      (fun z : TotalSpace (Vβ × Vβ) D ↦ (⟨z.proj, (d z.proj).symm z.snd⟩ :
        TotalSpace VH νH)) := by
    apply contMDiff_bundleMap_of_comp_surjective (F := VH) (G := Vβ × Vβ) (H := VH)
      (W := νH) (V₀ := D) (Z := νH)
      (fun p ↦ (d p).toContinuousLinearMap) (fun p ↦ (d p).symm.toContinuousLinearMap)
      hforward (fun p ↦ (d p).surjective)
    apply contMDiff_id.congr
    intro z
    exact congrArg (TotalSpace.mk z.proj) ((d z.proj).symm_apply_apply z.snd)
  let q : TotalSpace VH νH ≃ₜ TotalSpace (Vβ × Vβ) D := {
    toFun z := ⟨z.proj, d z.proj z.snd⟩
    invFun z := ⟨z.proj, (d z.proj).symm z.snd⟩
    left_inv z := congrArg (TotalSpace.mk z.proj) ((d z.proj).symm_apply_apply z.snd)
    right_inv z := congrArg (TotalSpace.mk z.proj) ((d z.proj).apply_symm_apply z.snd)
    continuous_toFun := hforward.continuous
    continuous_invFun := hinverse.continuous }
  refine ⟨ComplexBundle.isFiniteRank_complexification Vβ V, ?_⟩
  exact ⟨(ComplexBundle.complexificationDoubleTotalHomeomorph Vβ V).trans q.symm,
    fun _ _ ↦ rfl⟩

end AtiyahSinger
