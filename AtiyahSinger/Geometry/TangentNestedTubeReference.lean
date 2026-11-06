/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentNestedTubeDerivative
public import AtiyahSinger.Geometry.TangentNormalComposition

/-!
# The reference normal identification for nested tangent tubes

Public module ID: M1488.

The native direct sum used by nested tangent tubes is smoothly identified with
the original normal bundle of the composite tangent embedding. The comparison
uses the supplied normal-composition splitting, second tangent-normal splitting,
and the supplied smooth fiber comparison. Composing this identification
with a composite tube gives a reference tube with those same witnesses.

Source: the ordered normal identification in the tubular composition argument
of SG III.12; this is a smooth total-space realization of the same fiber map.
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
  (hgf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ (g.comp f))

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
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
local notation "Rnormal" => νTf ×ᵇ ((TfMap : TM → TN) *ᵖ νTg)

set_option maxSynthPendingDepth 50 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option maxHeartbeats 1600000 in
-- Both native product atlases and their normal comparison are elaborated together.
/-- The specified ordered fiber comparison is a diffeomorphism of the native normal totals. -/
theorem exists_tangentNestedTube_referenceDiffeomorph
    (hTC : IsImmersion 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) ∞ ((TgMap).comp TfMap))
    (ST : NormalEmbeddingCompositionSplitting TfMap TgMap
      (isImmersion_smoothTangentMap f hf) (isImmersion_smoothTangentMap g hg) hTC)
    (Sg : TangentNormalSplitting g hg) (c : ∀ z : TM, νTC z ≃L[ℝ] νTgf z) :
    letI := normalBundleFiberBundle g hg.isImmersion
    letI := normalBundleVectorBundle g hg.isImmersion
    letI := normalBundleContMDiffVectorBundle g hg.isImmersion
    letI := normalBundleFiberBundle TfMap (isImmersion_smoothTangentMap f hf)
    letI := normalBundleVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
    letI := normalBundleContMDiffVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
    letI := normalBundleFiberBundle TgMap (isImmersion_smoothTangentMap g hg)
    letI := normalBundleVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
    letI := normalBundleContMDiffVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
    letI := normalBundleFiberBundle ((TgMap).comp TfMap) hTC
    letI := normalBundleVectorBundle ((TgMap).comp TfMap) hTC
    letI := normalBundleContMDiffVectorBundle ((TgMap).comp TfMap) hTC
    letI := normalBundleFiberBundle TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
    letI := normalBundleVectorBundle TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
    letI := normalBundleContMDiffVectorBundle TgfMap
      (isImmersion_smoothTangentMap (g.comp f) hgf)
    ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTC))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTC)) ∞
      (fun z : TotalSpace VTC νTC ↦ (⟨z.proj, c z.proj z.snd⟩ : TotalSpace VTC νTgf)) →
    ∃ Q : Diffeomorph (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTC))
        (TotalSpace (VTf × Wg) Rsum) (TotalSpace VTC νTgf) ∞,
      ∀ z : TotalSpace (VTf × Wg) Rsum,
        Q z = ⟨z.proj, c z.proj ((ST.equiv z.proj).symm
          (z.snd.1, (Sg.equiv (TfMap z.proj)).symm z.snd.2))⟩ := by
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
  let := normalBundleFiberBundle ((TgMap).comp TfMap) hTC
  let := normalBundleVectorBundle ((TgMap).comp TfMap) hTC
  let := normalBundleContMDiffVectorBundle ((TgMap).comp TfMap) hTC
  let := normalBundleFiberBundle TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
  let := normalBundleVectorBundle TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
  let := normalBundleContMDiffVectorBundle TgfMap
    (isImmersion_smoothTangentMap (g.comp f) hgf)
  intro hc
  -- The second factor is evaluated over the original tangent map, in its native pullback.
  have hsecond : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg))
      (𝓘(ℝ, F × F).prod 𝓘(ℝ, Wg)) ∞
      (fun z : TotalSpace (VTf × Wg) Rsum ↦
        (⟨TfMap z.proj, z.snd.2⟩ : TotalSpace Wg Dg)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨(TfMap).contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj Rsum), ?_⟩
    have hz := (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg)) ∞ id z from contMDiffAt_id)).2
    exact (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : VTf × Wg → Wg))
      |>.contDiffAt.comp_contMDiffAt hz
  have hproduct : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × VTg)) ∞
      (fun z : TotalSpace (VTf × Wg) Rsum ↦
        (⟨z.proj, (z.snd.1, (Sg.equiv (TfMap z.proj)).symm z.snd.2)⟩ :
          TotalSpace (VTf × VTg) Rnormal)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj Rsum, ?_⟩
    have hz := (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg)) ∞ id z from contMDiffAt_id)).2
    have h₁ := (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : VTf × Wg → VTf))
      |>.contDiffAt.comp_contMDiffAt hz
    have h₂ := (Bundle.contMDiffAt_totalSpace.mp
      ((Sg.contMDiff_invFun.comp hsecond) z)).2
    exact h₁.prodMk_space h₂
  -- The fiber map is the supplied splitting inverse followed by the original comparison.
  let L (z : TM) : Rsum z ≃L[ℝ] νTgf z :=
    ((ContinuousLinearEquiv.refl ℝ (νTf z)).prodCongr (Sg.equiv (TfMap z)).symm)
      |>.trans (ST.equiv z).symm |>.trans (c z)
  have hL : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTC)) ∞
      (fun z : TotalSpace (VTf × Wg) Rsum ↦
        (⟨z.proj, L z.proj z.snd⟩ : TotalSpace VTC νTgf)) :=
    hc.comp (ST.contMDiff_invFun.comp hproduct)
  -- The inverse of the supplied smooth fiber comparison is smooth in the normal atlases.
  have hci : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTC))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTC)) ∞
      (fun z : TotalSpace VTC νTgf ↦
        (⟨z.proj, (c z.proj).symm z.snd⟩ : TotalSpace VTC νTC)) := by
    apply contMDiff_bundleMap_of_comp_surjective (E := E × E) (M := TM)
      (F := VTC) (G := VTC) (H := VTC) (W := νTC) (V₀ := νTgf) (Z := νTC)
      (fun z ↦ (c z).toContinuousLinearMap) (fun z ↦ (c z).symm.toContinuousLinearMap) hc
    · exact fun z ↦ (c z).surjective
    · apply contMDiff_id.congr
      intro z
      exact congrArg (fun v ↦ (⟨z.proj, v⟩ : TotalSpace VTC νTC))
        ((c z.proj).symm_apply_apply z.snd)
  -- Reversing the same ordered product uses Sg itself over the identical pullback map.
  have hsecondInv : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × VTg))
      (𝓘(ℝ, F × F).prod 𝓘(ℝ, VTg)) ∞
      (fun z : TotalSpace (VTf × VTg) Rnormal ↦
        (⟨TfMap z.proj, z.snd.2⟩ : TotalSpace VTg νTg)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨(TfMap).contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj Rnormal), ?_⟩
    have hz := (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × VTg))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × VTg)) ∞ id z from contMDiffAt_id)).2
    exact (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : VTf × VTg → VTg))
      |>.contDiffAt.comp_contMDiffAt hz
  have hproductInv : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × VTg))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg)) ∞
      (fun z : TotalSpace (VTf × VTg) Rnormal ↦
        (⟨z.proj, (z.snd.1, Sg.equiv (TfMap z.proj) z.snd.2)⟩ :
          TotalSpace (VTf × Wg) Rsum)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj Rnormal, ?_⟩
    have hz := (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × VTg))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × VTg)) ∞ id z from contMDiffAt_id)).2
    have h₁ := (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : VTf × VTg → VTf))
      |>.contDiffAt.comp_contMDiffAt hz
    have h₂ := (Bundle.contMDiffAt_totalSpace.mp
      ((Sg.contMDiff_toFun.comp hsecondInv) z)).2
    exact h₁.prodMk_space h₂
  have hLi : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTC))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg)) ∞
      (fun z : TotalSpace VTC νTgf ↦
        (⟨z.proj, (L z.proj).symm z.snd⟩ : TotalSpace (VTf × Wg) Rsum)) :=
    hproductInv.comp (ST.contMDiff_toFun.comp hci)
  let Q : Diffeomorph (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTC))
      (TotalSpace (VTf × Wg) Rsum) (TotalSpace VTC νTgf) ∞ :=
    { toFun := fun z ↦ ⟨z.proj, L z.proj z.snd⟩
      invFun := fun z ↦ ⟨z.proj, (L z.proj).symm z.snd⟩
      left_inv := fun z ↦ TotalSpace.ext rfl (heq_of_eq ((L z.proj).symm_apply_apply z.snd))
      right_inv := fun z ↦ TotalSpace.ext rfl (heq_of_eq ((L z.proj).apply_symm_apply z.snd))
      contMDiff_toFun := hL
      contMDiff_invFun := hLi }
  exact ⟨Q, fun _ ↦ rfl⟩

end AtiyahSinger
