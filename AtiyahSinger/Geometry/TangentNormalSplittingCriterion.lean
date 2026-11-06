/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleSubbundle
public import AtiyahSinger.Geometry.TangentNormalBundle

/-!
# Recognizing a splitting of the original tangent normal sequence

Public module ID: M1495.

A smooth assembly of the two original normal factors is invertible when its
first quotient component and its restriction to the second factor agree with
the original normal exact sequence. Its inverse is therefore an admissible
ordered tangent-normal splitting. An unrestricted lower-left component is
retained, as required for derivatives involving a varying horizontal lift.

This is the exact-sequence splitting criterion used by the frame-sphere tube.
It does not replace either canonical map or assume a normal isomorphism.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology tangentBundleFullChartedSpace
  tangentBundle_full_isManifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)

local notation "ν" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
local notation "νT" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
local notation "V" => NormalModel E F
local notation "VT" => NormalModel (E × E) (F × F)
local notation "νP" => ((smoothTangentBundleProjection E M : TangentBundle 𝓘(ℝ, E) M → M)
  *ᵖ ν)

set_option maxSynthPendingDepth 45 in
set_option maxHeartbeats 1500000 in
-- Only the two original exact-sequence identities constrain the assembly.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A smooth assembly respecting both canonical normal maps gives an ordered splitting. -/
theorem exists_tangentNormalSplitting_of_assembly :
    letI := normalBundleFiberBundle f hf.isImmersion
    letI := normalBundleVectorBundle f hf.isImmersion
    letI := normalBundleContMDiffVectorBundle f hf.isImmersion
    letI := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleContMDiffVectorBundle
      (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    ∀ (R : ∀ z : TangentBundle 𝓘(ℝ, E) M, (ν z.proj × ν z.proj) →L[ℝ] νT z),
      ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT)) ∞
        (fun z : TotalSpace (V × V) (νP ×ᵇ νP) ↦
          (⟨z.proj, R z.proj z.snd⟩ : TotalSpace VT νT)) →
      (∀ z v, tangentNormalProjection f hf z (R z v) = v.1) →
      (∀ z v, R z (0, v) = tangentNormalVerticalMap f hf z v) →
      ∃ S : TangentNormalSplitting f hf,
        ∀ z v, (S.equiv z).symm v = R z v := by
  classical
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  intro R hR hfirst hvertical
  let i := tangentNormalVerticalMap f hf
  let p := tangentNormalProjection f hf
  have hseq (z : TangentBundle 𝓘(ℝ, E) M) : Injective (i z) ∧ Surjective (p z) ∧
      LinearMap.range (i z).toLinearMap = LinearMap.ker (p z).toLinearMap :=
    (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec.2.2.2.2 z
  -- Exactness recovers both input factors from a zero image and supplies every target vector.
  have hbij (z : TangentBundle 𝓘(ℝ, E) M) : Bijective (R z) := by
    constructor
    · apply (injective_iff_map_eq_zero (R z)).mpr
      intro v hv
      have hv₁ : v.1 = 0 := by
        rw [← hfirst z v, hv, map_zero]
      have hv₂ : v.2 = 0 := by
        apply (hseq z).1
        rw [map_zero, ← hvertical z v.2]
        have hpair : (0, v.2) = v := Prod.ext hv₁.symm rfl
        rw [hpair, hv]
      exact Prod.ext hv₁ hv₂
    · intro v
      let u := p z v
      have hkernel : v - R z (u, 0) ∈ LinearMap.ker (p z).toLinearMap := by
        change p z (v - R z (u, 0)) = 0
        rw [map_sub, hfirst]
        exact sub_self _
      rw [← (hseq z).2.2] at hkernel
      obtain ⟨w, hw⟩ := hkernel
      change i z w = v - R z (u, 0) at hw
      refine ⟨(u, w), ?_⟩
      calc
        R z (u, w) = R z (u, 0) + R z (0, w) := by
          rw [← map_add]
          congr 1
          simp
        _ = R z (u, 0) + i z w := by rw [hvertical]
        _ = v := by
          rw [hw]
          abel
  let e (z : TangentBundle 𝓘(ℝ, E) M) : (ν z.proj × ν z.proj) ≃L[ℝ] νT z :=
    LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ) (E := ν z.proj × ν z.proj) (F := νT z)
      (LinearEquiv.ofBijective (R z).toLinearMap (hbij z))
  let (z : TangentBundle 𝓘(ℝ, E) M) : AddCommGroup (νP z) := by
    change AddCommGroup (ν z.proj)
    infer_instance
  let (z : TangentBundle 𝓘(ℝ, E) M) : Module ℝ (νP z) := by
    change Module ℝ (ν z.proj)
    infer_instance
  let (z : TangentBundle 𝓘(ℝ, E) M) : IsTopologicalAddGroup (νP z) := by
    change IsTopologicalAddGroup (ν z.proj)
    infer_instance
  let (z : TangentBundle 𝓘(ℝ, E) M) : ContinuousSMul ℝ (νP z) := by
    change ContinuousSMul ℝ (ν z.proj)
    infer_instance
  have hinverse : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V)) ∞
      (fun z : TotalSpace VT νT ↦
        (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace (V × V) (νP ×ᵇ νP))) := by
    apply contMDiff_bundleMap_of_comp_injective (I := 𝓘(ℝ, E × E))
      (W := νP ×ᵇ νP) (V₀ := νT) (Z := νT) (F := V × V) (G := VT) (H := VT)
      R (fun z ↦ (e z).symm.toContinuousLinearMap) hR (fun z ↦ (hbij z).1)
    apply contMDiff_id.congr
    intro z
    change (⟨z.proj, e z.proj ((e z.proj).symm z.snd)⟩ : TotalSpace VT νT) = z
    rw [(e z.proj).apply_symm_apply]
  let S : TangentNormalSplitting f hf :=
    { equiv := fun z ↦ (e z).symm
      contMDiff_toFun := hinverse
      contMDiff_invFun := hR
      fst_equiv := by
        intro z v
        have h := hfirst z ((e z).symm v)
        change p z (e z ((e z).symm v)) = ((e z).symm v).1 at h
        rw [(e z).apply_symm_apply] at h
        exact h.symm
      equiv_vertical := by
        intro z v
        apply (e z).injective
        rw [(e z).apply_symm_apply]
        exact (hvertical z v).symm }
  exact ⟨S, fun _ _ ↦ rfl⟩

end AtiyahSinger
