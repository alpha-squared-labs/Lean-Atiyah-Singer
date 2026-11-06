/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexificationBundleMap
public import AtiyahSinger.Geometry.NormalEmbeddingComposition
public import AtiyahSinger.Geometry.TangentNormalBundle
public import AtiyahSinger.Topology.ComplexificationPullbackTopology
public import AtiyahSinger.Topology.ComplexifiedNormalPullback
public import AtiyahSinger.Topology.RealComplexification

import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Complexification of the actual composite normal splitting

Public module ID: M1741.

The real splitting of the original normal short exact sequence is extended to
complex scalars and pulled back to TM. Its ordered factors are exactly the
fixed complex normal of f and the pullback, by the actual tangent map of f,
of the fixed complex normal of g. Tensor distributivity retains this order.

The pointwise pure-tensor formula ensures the map is the scalar extension of
the supplied real splitting. It therefore preserves the SG real/imaginary
complex structure (u,v) mapped to (-v,u), without selecting a different real
identification of the doubled normal. All induced total topologies are the
existing normal, pullback, sum and complexification topologies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Manifold Topology
open scoped ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
  (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hg : IsImmersion 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g)
  (hgf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ (g.comp f))

set_option maxHeartbeats 1600000 in
-- The actual tensor maps pass through nested pullback and real/imaginary topologies.
/-- Complexify the supplied real normal splitting on the original tangent-bundle carriers. -/
theorem exists_complexifiedNormalPullback_composition_iso
    (S : NormalEmbeddingCompositionSplitting f g hf hg hgf) :
    ∃ e : Iso (ComplexifiedNormalPullback (g.comp f))
        ((ComplexifiedNormalPullback f) ×ᵇ
          ((smoothTangentMap f : TangentBundle 𝓘(ℝ, E) M → TangentBundle 𝓘(ℝ, F) N) *ᵖ
            (ComplexifiedNormalPullback g))),
      ∀ (z : TangentBundle 𝓘(ℝ, E) M) (a : ℂ)
        (v : NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) z.proj),
        e.linearEquiv z (a ⊗ₜ[ℝ] v) =
          (a ⊗ₜ[ℝ] (S.equiv z.proj v).1, a ⊗ₜ[ℝ] (S.equiv z.proj v).2) := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let := normalBundleFiberBundle g hg
  let := normalBundleVectorBundle g hg
  let := normalBundleContMDiffVectorBundle g hg
  let := normalBundleFiberBundle (g.comp f) hgf
  let := normalBundleVectorBundle (g.comp f) hgf
  let := normalBundleContMDiffVectorBundle (g.comp f) hgf
  let TM := TangentBundle 𝓘(ℝ, E) M
  let TN := TangentBundle 𝓘(ℝ, F) N
  let νf := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let νg := NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g
  let νgf := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f)
  let Vf := NormalModel E F
  let Vg := NormalModel F G
  let Vgf := NormalModel E G
  let πM : C(TM, M) :=
    ⟨TotalSpace.proj, FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))⟩
  let πN : C(TN, N) :=
    ⟨TotalSpace.proj, FiberBundle.continuous_proj F (TangentSpace 𝓘(ℝ, F))⟩
  let Tf : C(TM, TN) := ⟨smoothTangentMap f, (smoothTangentMap f).contMDiff.continuous⟩
  let fc : C(M, N) := ⟨f, f.contMDiff.continuous⟩
  let Rf := (πM : TM → M) *ᵖ νf
  let Rg := (πN : TN → N) *ᵖ νg
  let Rgf := (πM : TM → M) *ᵖ νgf
  let R₂ := (Tf : TM → TN) *ᵖ Rg
  let Rsum := Rf ×ᵇ R₂
  let νgP := (fc : M → N) *ᵖ νg
  let L (z : TM) : Rgf z ≃ₗ[ℝ] Rsum z := (S.equiv z.proj).toLinearEquiv
  let : RealBundle.IsFiniteRank Vf Rf := RealBundle.isFiniteRank_of_vectorBundle _ _
  let : RealBundle.IsFiniteRank Vg R₂ := RealBundle.isFiniteRank_of_vectorBundle _ _
  -- Pull back the real splitting through the actual projection and tangent map.
  have hpair : Continuous (fun z : TotalSpace (Vf × Vg) (νf ×ᵇ νgP) ↦
      ((⟨z.proj, z.snd.1⟩ : TotalSpace Vf νf),
        (⟨z.proj, z.snd.2⟩ : TotalSpace Vg νgP))) := continuous_induced_dom
  have hS := S.contMDiff_toFun.continuous.comp (Pullback.continuous_lift Vgf νgf πM)
  have hfirst := (continuous_fst.comp hpair).comp hS
  have hsecond := (continuous_snd.comp hpair).comp hS
  have hbase : Continuous (fun z : TotalSpace Vgf Rgf ↦ z.proj) :=
    Pullback.continuous_proj Vgf νgf πM
  have hLf : Continuous (fun z : TotalSpace Vgf Rgf ↦
      (⟨z.proj, (L z.proj z.snd).1⟩ : TotalSpace Vf Rf)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Vf νf πM).continuous_iff]
    exact hbase.prodMk hfirst
  have hLg : Continuous (fun z : TotalSpace Vgf Rgf ↦
      (⟨z.proj, (L z.proj z.snd).2⟩ : TotalSpace Vg R₂)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Vg Rg Tf).continuous_iff]
    refine hbase.prodMk ?_
    rw [(inducing_pullbackTotalSpaceEmbedding Vg νg πN).continuous_iff]
    exact (Tf.continuous.comp hbase).prodMk
      ((Pullback.continuous_lift Vg νg fc).comp hsecond)
  have hL : Continuous (fun z : TotalSpace Vgf Rgf ↦
      (⟨z.proj, L z.proj z.snd⟩ : TotalSpace (Vf × Vg) Rsum)) :=
    continuous_induced_rng.mpr (hLf.prodMk hLg)
  have hsumPair : Continuous (fun z : TotalSpace (Vf × Vg) Rsum ↦
      ((⟨z.proj, z.snd.1⟩ : TotalSpace Vf Rf),
        (⟨z.proj, z.snd.2⟩ : TotalSpace Vg R₂))) := continuous_induced_dom
  have hsumBase : Continuous (fun z : TotalSpace (Vf × Vg) Rsum ↦ z.proj) :=
    (Pullback.continuous_proj Vf νf πM).comp (continuous_fst.comp hsumPair)
  have hsumFirst := (Pullback.continuous_lift Vf νf πM).comp (continuous_fst.comp hsumPair)
  have hsumSecond : Continuous (fun z : TotalSpace (Vf × Vg) Rsum ↦
      (⟨πM z.proj, z.snd.2⟩ : TotalSpace Vg νgP)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Vg νg fc).continuous_iff]
    exact (πM.continuous.comp hsumBase).prodMk
      ((Pullback.continuous_lift Vg νg πN).comp
        ((Pullback.continuous_lift Vg Rg Tf).comp (continuous_snd.comp hsumPair)))
  have hsumDown : Continuous (fun z : TotalSpace (Vf × Vg) Rsum ↦
      (⟨πM z.proj, z.snd⟩ : TotalSpace (Vf × Vg) (νf ×ᵇ νgP))) :=
    continuous_induced_rng.mpr (hsumFirst.prodMk hsumSecond)
  have hLinv : Continuous (fun z : TotalSpace (Vf × Vg) Rsum ↦
      (⟨z.proj, (L z.proj).symm z.snd⟩ : TotalSpace Vgf Rgf)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Vgf νgf πM).continuous_iff]
    exact hsumBase.prodMk (S.contMDiff_invFun.continuous.comp hsumDown)
  -- Extend that same real isomorphism to complex scalars, then distribute in the prescribed order.
  let t₂ := complexificationTopology Vg R₂
  let t₂' : TopologicalSpace (TotalSpace Unit (fun z : TM ↦ ℂ ⊗[ℝ] R₂ z)) :=
    @Pullback.TotalSpace.topologicalSpace TN Unit (ComplexifiedNormalPullback g)
      TM (Tf : TM → TN) _ (complexifiedNormalPullbackTopology g)
  have ht₂ : t₂ = t₂' := complexificationTopology_pullback Vg Rg Tf
  let Ψ (t : TopologicalSpace (TotalSpace Unit (fun z : TM ↦ ℂ ⊗[ℝ] R₂ z))) : Prop :=
    letI := complexificationTopology Vf Rf
    letI := t
    letI := sumTopology (E := fun z ↦ ℂ ⊗[ℝ] Rf z) (F := fun z ↦ ℂ ⊗[ℝ] R₂ z)
    ∃ e : Iso (ComplexifiedNormalPullback (g.comp f))
        (fun z ↦ (ℂ ⊗[ℝ] Rf z) × (ℂ ⊗[ℝ] R₂ z)),
      ∀ (z : TM) (a : ℂ) (v : Rgf z), e.linearEquiv z (a ⊗ₜ[ℝ] v) =
        (a ⊗ₜ[ℝ] (L z v).1, a ⊗ₜ[ℝ] (L z v).2)
  have hresult : Ψ t₂ := by
    let := complexificationTopology Vf Rf
    let := complexificationTopology Vg R₂
    let := complexificationTopology (Vf × Vg) Rsum
    let := sumTopology (E := fun z ↦ ℂ ⊗[ℝ] Rf z) (F := fun z ↦ ℂ ⊗[ℝ] R₂ z)
    let c : Iso (ComplexifiedNormalPullback (g.comp f)) (fun z ↦ ℂ ⊗[ℝ] Rsum z) := {
      linearEquiv z := (L z).baseChange ℝ ℂ _ _
      continuous_total := continuous_complexification_map (fun z ↦ (L z).toLinearMap) hL
      continuous_symm := continuous_complexification_map (fun z ↦ (L z).symm.toLinearMap) hLinv }
    let d := RealBundle.complexificationSumIso Vf Rf Vg R₂
    refine ⟨c.trans d, ?_⟩
    intro z a v
    change TensorProduct.prodRight ℝ ℂ ℂ (Rf z) (R₂ z)
      (((L z).baseChange ℝ ℂ _ _) (a ⊗ₜ[ℝ] v)) = _
    rw [LinearEquiv.baseChange_tmul, TensorProduct.prodRight_tmul]
  rw [ht₂] at hresult
  exact hresult

end AtiyahSinger
