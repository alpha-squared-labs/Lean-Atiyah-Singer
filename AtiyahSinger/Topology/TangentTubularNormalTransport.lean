/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.TangentTubularRealTransport

/-!
# Complex tubular transport on the actual second tangent normal

Public module ID: M2243.

The specified normalized second splitting conjugates the original complex
transport to transport of the actual quotient normal of the second tangent
embedding. Both native total maps are continuous. Its formula explicitly
retains the original complex isomorphism, real/imaginary convention and splitting,
and its zero-section value is the vector identity.

These are the actual normal fibers used to construct the nested open map and
compare its normal derivative with the real normal composition sequence.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Manifold
open scoped ContDiff TensorProduct

attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]
  [T2Space N] [SecondCountableTopology N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (g : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, G) N P ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hg : IsSmoothEmbedding 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g)
  (Tf : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
local notation "νTf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
local notation "νTg" => NormalBundle 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) (smoothTangentMap g)
local notation "VTf" => NormalModel (E × E) (F × F)
local notation "VTg" => NormalModel (F × F) (G × G)
local notation "Vg" => NormalModel F G
local notation "Bg" => (π F (TangentSpace 𝓘(ℝ, F)) : TN → N) *ᵖ
  (NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g)
local notation "Dg" => Bg ×ᵇ Bg
local notation "Wg" => Vg × Vg
local notation "X" => TotalSpace VTf νTf

set_option maxSynthPendingDepth 50 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in

/-- The same complex transport acts on the actual second tangent normal, with identity at zero. -/
theorem exists_tangentTubular_normal_transport
    (Sf : TangentNormalSplitting f hf) (Sg : TangentNormalSplitting g hg) :
    letI := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    let a : C(X, TN) := ⟨fun z ↦ smoothTangentMap f z.proj,
      (smoothTangentMap f).contMDiff.continuous.comp (FiberBundle.continuous_proj VTf νTf)⟩
    let b := Tf.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    ∃ e : Iso ((a : X → TN) *ᵖ (ComplexifiedNormalPullback g))
        ((b : X → TN) *ᵖ (ComplexifiedNormalPullback g)),
      ∃ R : ∀ x : X, νTg (a x) ≃L[ℝ] νTg (b x),
        (∀ x v, Sg.equiv (b x) (R x v) = complexificationReIm (Bg (b x))
          (e.linearEquiv x ((complexificationReIm (Bg (a x))).symm (Sg.equiv (a x) v)))) ∧
        Continuous (fun z : TotalSpace VTg ((a : X → TN) *ᵖ νTg) ↦
          (⟨z.proj, R z.proj z.snd⟩ : TotalSpace VTg ((b : X → TN) *ᵖ νTg))) ∧
        Continuous (fun z : TotalSpace VTg ((b : X → TN) *ᵖ νTg) ↦
          (⟨z.proj, (R z.proj).symm z.snd⟩ : TotalSpace VTg ((a : X → TN) *ᵖ νTg))) ∧
        (∀ (z : TM) (v : νTg (a ⟨z, 0⟩)), HEq (R ⟨z, 0⟩ v) v) := by
  classical
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleFiberBundle g hg.isImmersion
  let := normalBundleVectorBundle g hg.isImmersion
  let := normalBundleContMDiffVectorBundle g hg.isImmersion
  let := normalBundleFiberBundle (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
  let := normalBundleVectorBundle (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
  let proj : C(TN, N) := ⟨π F (TangentSpace 𝓘(ℝ, F)),
    FiberBundle.continuous_proj F (TangentSpace 𝓘(ℝ, F))⟩
  let := FiberBundle.pullback (F := Vg)
    (E := NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g) proj
  let := VectorBundle.pullback (𝕜 := ℝ) (F := Vg)
    (E := NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g) proj
  let := complexificationTopology Vg Bg
  let : RealBundle.IsFiniteRank Vg Bg := RealBundle.isFiniteRank_of_vectorBundle _ _
  have hfinite : IsFiniteRank (fun y ↦ ℂ ⊗[ℝ] Bg y) := isFiniteRank_complexification Vg Bg
  let a : C(X, TN) := ⟨fun z ↦ smoothTangentMap f z.proj,
    (smoothTangentMap f).contMDiff.continuous.comp (FiberBundle.continuous_proj VTf νTf)⟩
  let b := Tf.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  dsimp only
  have htransport := exists_tangentTubular_real_transport f hf Tf Vg Bg Sf hfinite
  rcases htransport with ⟨e, D, hD, hDc, hDic, _, hDzero⟩
  let R (x : X) : νTg (a x) ≃L[ℝ] νTg (b x) :=
    ((Sg.equiv (a x)).toLinearEquiv.trans
      ((D x).trans (Sg.equiv (b x)).symm.toLinearEquiv)).toContinuousLinearEquiv
  let Q (d : C(X, TN)) : TotalSpace VTg ((d : X → TN) *ᵖ νTg) ≃ₜ
      TotalSpace Wg ((d : X → TN) *ᵖ Dg) :=
    { toFun z := ⟨z.proj, Sg.equiv (d z.proj) z.snd⟩
      invFun z := ⟨z.proj, (Sg.equiv (d z.proj)).symm z.snd⟩
      left_inv z := by
        cases z
        simp
      right_inv z := by
        cases z
        simp
      continuous_toFun := by
        rw [(inducing_pullbackTotalSpaceEmbedding Wg Dg d).continuous_iff]
        exact (Pullback.continuous_proj VTg νTg d).prodMk
          ((Sg.totalHomeomorph g hg).continuous.comp (Pullback.continuous_lift VTg νTg d))
      continuous_invFun := by
        rw [(inducing_pullbackTotalSpaceEmbedding VTg νTg d).continuous_iff]
        exact (Pullback.continuous_proj Wg Dg d).prodMk
          ((Sg.totalHomeomorph g hg).symm.continuous.comp (Pullback.continuous_lift Wg Dg d)) }
  refine ⟨e, R, ?_, ?_, ?_, ?_⟩
  · intro x v
    change Sg.equiv (b x) ((Sg.equiv (b x)).symm (D x (Sg.equiv (a x) v))) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, hD]
    rfl
  · exact (Q b).symm.continuous.comp (hDc.comp (Q a).continuous)
  · exact (Q a).symm.continuous.comp (hDic.comp (Q b).continuous)
  · intro z v
    have hbase : b ⟨z, 0⟩ = a ⟨z, 0⟩ := Tf.map_zero z
    have hsymm {y y' : TN} (hy : y = y') (u : Dg y) (v : Dg y') (hu : HEq u v) :
        HEq ((Sg.equiv y).symm u) ((Sg.equiv y').symm v) := by
      subst y'
      cases hu
      rfl
    change HEq ((Sg.equiv (b ⟨z, 0⟩)).symm (D ⟨z, 0⟩ (Sg.equiv (a ⟨z, 0⟩) v))) v
    have h := hsymm hbase _ _ (hDzero z (Sg.equiv (a ⟨z, 0⟩) v))
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

end AtiyahSinger
