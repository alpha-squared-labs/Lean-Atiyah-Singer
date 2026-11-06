/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleSum
public import AtiyahSinger.Topology.TangentEmbeddingPushforward

/-!
# The original complex normal sum in native nested-tube coordinates

Public module ID: M2240.

The specified first tangent-normal splitting and the original real/imaginary
map on the pulled-back second normal give a homeomorphism from the complex
Thom direct sum to the native real bundle used by nested tubes. The factor
order is unchanged: first normal, then the pulled-back second normal.

This is a real coordinate comparison of the actual complex sum, with explicit
pointwise formulas. It does not replace the complex Thom isomorphism by an
arbitrary real bundle equivalence.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Manifold
open scoped ContDiff TensorProduct

attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology sumTopology
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

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

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
local notation "νf" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
local notation "νTf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
local notation "VTf" => NormalModel (E × E) (F × F)
local notation "Vg" => NormalModel F G
local notation "Bg" => (π F (TangentSpace 𝓘(ℝ, F)) : TN → N) *ᵖ
  (NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g)
local notation "Dg" => Bg ×ᵇ Bg
local notation "Wg" => Vg × Vg
local notation "Tfc" => (smoothTangentMap f : TM → TN)

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified first splitting and original second real/imaginary map on the actual sum. -/
def tangentNormalSumHomeomorph (Sf : TangentNormalSplitting f hf) :
    TotalSpace Unit ((ComplexifiedNormalPullback f) ×ᵇ
      (Tfc *ᵖ (ComplexifiedNormalPullback g))) ≃ₜ
      TotalSpace (VTf × Wg) (νTf ×ᵇ (Tfc *ᵖ Dg)) := by
  let := complexificationTopology Vg Bg
  let Tf : C(TM, TN) := ⟨smoothTangentMap f, (smoothTangentMap f).contMDiff.continuous⟩
  let Hf := complexifiedNormalTotalHomeomorph f hf Sf
  let Hg := complexificationDoubleTotalHomeomorph Vg Bg
  let Q : TotalSpace Unit (Tfc *ᵖ (ComplexifiedNormalPullback g)) ≃ₜ
      TotalSpace Wg (Tfc *ᵖ Dg) :=
    { toFun z := ⟨z.proj, complexificationReIm (Bg (Tf z.proj)) z.snd⟩
      invFun z := ⟨z.proj, (complexificationReIm (Bg (Tf z.proj))).symm z.snd⟩
      left_inv z := by
        cases z
        simp
      right_inv z := by
        cases z
        simp
      continuous_toFun := by
        rw [(inducing_pullbackTotalSpaceEmbedding Wg Dg Tf).continuous_iff]
        exact (Pullback.continuous_proj Unit (ComplexifiedNormalPullback g) Tf).prodMk
          (Hg.continuous.comp (Pullback.continuous_lift Unit (ComplexifiedNormalPullback g) Tf))
      continuous_invFun := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (ComplexifiedNormalPullback g)
          Tf).continuous_iff]
        exact (Pullback.continuous_proj Wg Dg Tf).prodMk
          (Hg.symm.continuous.comp (Pullback.continuous_lift Wg Dg Tf)) }
  let C := (ComplexifiedNormalPullback f) ×ᵇ (Tfc *ᵖ (ComplexifiedNormalPullback g))
  let R := νTf ×ᵇ (Tfc *ᵖ Dg)
  have hC : Continuous (fun z : TotalSpace Unit C ↦
      ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit (ComplexifiedNormalPullback f)),
        (⟨z.proj, z.snd.2⟩ : TotalSpace Unit (Tfc *ᵖ (ComplexifiedNormalPullback g))))) :=
    continuous_induced_dom
  have hR : Continuous (fun z : TotalSpace (VTf × Wg) R ↦
      ((⟨z.proj, z.snd.1⟩ : TotalSpace VTf νTf),
        (⟨z.proj, z.snd.2⟩ : TotalSpace Wg (Tfc *ᵖ Dg)))) := continuous_induced_dom
  refine
    { toFun := fun z ↦ ⟨z.proj,
        ((Sf.equiv z.proj).symm (complexificationReIm (νf z.proj.proj) z.snd.1),
          complexificationReIm (Bg (Tf z.proj)) z.snd.2)⟩
      invFun := fun z ↦ ⟨z.proj,
        ((complexificationReIm (νf z.proj.proj)).symm (Sf.equiv z.proj z.snd.1),
          (complexificationReIm (Bg (Tf z.proj))).symm z.snd.2)⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := continuous_induced_rng.mpr
        ((Hf.continuous.comp (continuous_fst.comp hC)).prodMk
          (Q.continuous.comp (continuous_snd.comp hC)))
      continuous_invFun := continuous_induced_rng.mpr
        ((Hf.symm.continuous.comp (continuous_fst.comp hR)).prodMk
          (Q.symm.continuous.comp (continuous_snd.comp hR))) }
  · intro z
    cases z
    simp
  · intro z
    cases z
    simp

end AtiyahSinger
