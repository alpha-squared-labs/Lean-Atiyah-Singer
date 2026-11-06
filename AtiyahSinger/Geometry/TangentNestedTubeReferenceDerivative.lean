/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentNestedTubeReference

/-!
# The actual nested derivative in the native sum frame

Public module ID: M1489.

The derivative of the original nested geometric map is identified with the
same reference fiber map after passing through the representative-preserving
normal comparison. The domain frame is exactly the native product/pullback
frame of the sum bundle, not a newly selected frame.

This is the same-witness adapter between the two partial-derivative calculation
and normalization of the actual reference-tube overlap in SG III.12.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Set Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology tangentBundleFullChartedSpace
  tangentBundle_full_isManifold

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (g : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, G) N P ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hg : IsSmoothEmbedding 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g)

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
local notation "TP" => TangentBundle 𝓘(ℝ, G) P
local notation "TfMap" => smoothTangentMap f
local notation "TgMap" => smoothTangentMap g
local notation "TgfMap" => smoothTangentMap (g.comp f)
local notation "νTf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) TfMap
local notation "νTg" => NormalBundle 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) TgMap
local notation "νTC" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, G × G)
  (ContMDiffMap.comp (smoothTangentMap g) (smoothTangentMap f))
local notation "νTgf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) TgfMap
local notation "VTf" => NormalModel (E × E) (F × F)
local notation "VTg" => NormalModel (F × F) (G × G)
local notation "VTC" => NormalModel (E × E) (G × G)
local notation "Vg" => NormalModel F G
local notation "Bg" => (smoothTangentBundleProjection F N : TN → N) *ᵖ
  (NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g)
local notation "Dg" => Bg ×ᵇ Bg
local notation "Wg" => Vg × Vg
local notation "Rsum" => νTf ×ᵇ ((TfMap : TM → TN) *ᵖ Dg)

set_option maxSynthPendingDepth 50 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- The actual nested derivative equals the specified reference map in the native sum frame. -/
theorem tangentNestedTube_reference_normalDerivative
    (Tf : TubularNeighborhood TfMap (isImmersion_smoothTangentMap f hf))
    (Tg : TubularNeighborhood TgMap (isImmersion_smoothTangentMap g hg))
    (Sg : TangentNormalSplitting g hg)
    (hTC : IsImmersion 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) ∞ ((TgMap).comp TfMap))
    (ST : NormalEmbeddingCompositionSplitting TfMap TgMap
      (isImmersion_smoothTangentMap f hf) (isImmersion_smoothTangentMap g hg) hTC)
    (c : ∀ z : TM, νTC z ≃L[ℝ] νTgf z) :
    letI := normalBundleFiberBundle g hg.isImmersion
    letI := normalBundleVectorBundle g hg.isImmersion
    letI := normalBundleContMDiffVectorBundle g hg.isImmersion
    letI := normalBundleFiberBundle TfMap (isImmersion_smoothTangentMap f hf)
    letI := normalBundleVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
    letI := normalBundleContMDiffVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
    letI := normalBundleFiberBundle TgMap (isImmersion_smoothTangentMap g hg)
    letI := normalBundleVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
    letI := normalBundleContMDiffVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
    ∀ z : TM,
      let ef := (trivializationAt VTf νTf z).continuousLinearEquivAt ℝ z
        (mem_baseSet_trivializationAt VTf νTf z)
      let eg := trivializationAt Wg Dg (TfMap z)
      let er := (trivializationAt (VTf × Wg) Rsum z).continuousLinearEquivAt ℝ z
        (mem_baseSet_trivializationAt (VTf × Wg) Rsum z)
      let b : VTf → TN := fun v ↦
        Tf.totalMap TfMap (isImmersion_smoothTangentMap f hf) ⟨z, ef.symm v⟩
      let φ : VTf × Wg → TP := fun p ↦
        Tg.totalMap TgMap (isImmersion_smoothTangentMap g hg)
          ⟨b p.1, (Sg.equiv (b p.1)).symm (eg.symm (b p.1) p.2)⟩
      (∀ (v : VTf) (w : Wg),
        (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G)
          ((TgMap).comp TfMap) z).toLinearMap).mkQ
          (mfderiv 𝓘(ℝ, VTf × Wg) 𝓘(ℝ, G × G) φ 0
            ((NormedSpace.fromTangentSpace (0 : VTf × Wg)).symm (v, w))) =
          (ST.equiv z).symm
            (ef.symm v, (Sg.equiv (TfMap z)).symm (eg.symm (TfMap z) w))) →
      (∀ v : G × G,
        c z ((LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G)
          ((TgMap).comp TfMap) z).toLinearMap).mkQ v) =
          (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) TgfMap z).toLinearMap).mkQ v) →
      ∀ L : Rsum z ≃L[ℝ] νTgf z,
        (∀ u, L u = c z ((ST.equiv z).symm
          (u.1, (Sg.equiv (TfMap z)).symm u.2))) →
        ∀ p : VTf × Wg,
          (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) TgfMap z).toLinearMap).mkQ
            (mfderiv 𝓘(ℝ, VTf × Wg) 𝓘(ℝ, G × G) φ 0
              ((NormedSpace.fromTangentSpace (0 : VTf × Wg)).symm p)) = L (er.symm p) := by
  classical
  let := normalBundleFiberBundle g hg.isImmersion
  let := normalBundleVectorBundle g hg.isImmersion
  let := normalBundleContMDiffVectorBundle g hg.isImmersion
  let := normalBundleFiberBundle TfMap (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
  let := normalBundleFiberBundle TgMap (isImmersion_smoothTangentMap g hg)
  let := normalBundleVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
  let := normalBundleContMDiffVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
  intro z ef eg er b φ hST hc L hL p
  -- The native product/pullback frame has precisely the original ef and eg components.
  have hframe : er.symm p = (ef.symm p.1, eg.symm (TfMap z) p.2) := by
    have hzeg : TfMap z ∈ eg.baseSet := mem_baseSet_trivializationAt Wg Dg (TfMap z)
    apply er.injective
    rw [er.apply_symm_apply]
    change p = (ef (ef.symm p.1),
      (eg.continuousLinearEquivAt ℝ (TfMap z) hzeg)
        ((eg.continuousLinearEquivAt ℝ (TfMap z) hzeg).symm p.2))
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  -- Apply the supplied quotient comparison to the given normal-derivative identity.
  rw [hL, hframe, ← hc]
  exact congrArg (c z) (hST p.1 p.2)

end AtiyahSinger
