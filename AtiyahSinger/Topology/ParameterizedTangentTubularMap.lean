/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ParameterizedTangentNormalSlice
public import AtiyahSinger.Geometry.ParameterizedTubularSlice
public import AtiyahSinger.Topology.ParameterizedComplexNormal
public import AtiyahSinger.Topology.ParameterizedComplexNormalSlice
public import AtiyahSinger.Topology.TangentEmbeddingPushforward

/-!
# The actual tangent tubular map on a parameter slice

Public module ID: M1987.

The same real quotient comparisons determine both the normalized tangent-normal
splitting and the normalized tube at an endpoint. Complexifying the slice normal
comparison therefore intertwines its actual tangent tubular map with the original
parameter tube and ordered complex-normal identification. No choices are compared
only by rank or by unrelated existence statements.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
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
  (H : ContMDiffMap 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F))
    (ℝ × TangentBundle 𝓘(ℝ, E) M) (ℝ × TangentBundle 𝓘(ℝ, F) N) ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hβ : IsSmoothEmbedding 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞ β)
  (hH : IsImmersion 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) ∞ H)

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
local notation "TP" => TangentBundle 𝓘(ℝ, ℝ × E) (ℝ × M)
local notation "νf" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
local notation "νβ" => NormalBundle 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) β
local notation "νTf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
local notation "νTβ" => NormalBundle 𝓘(ℝ, (ℝ × E) × (ℝ × E))
  𝓘(ℝ, (ℝ × F) × (ℝ × F)) (smoothTangentMap β)
local notation "νH" => NormalBundle 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) H
local notation "Vf" => NormalModel E F
local notation "Vβ" => NormalModel (ℝ × E) (ℝ × F)
local notation "VTf" => NormalModel (E × E) (F × F)
local notation "VTβ" => NormalModel ((ℝ × E) × (ℝ × E)) ((ℝ × F) × (ℝ × F))
local notation "VH" => NormalModel (ℝ × (E × E)) (ℝ × (F × F))
local notation "jM" => zeroVelocityInclusion E M
local notation "jN" => zeroVelocityInclusion F N

local notation "P" => ℝ × TM
local notation "V" => ((parameterTangentProjection E M : P → ℝ × M) *ᵖ νβ)

set_option maxHeartbeats 1600000 in
-- This compares the actual nested quotient, pullback and tensor structures at one slice.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same parameter geometry restricts to the original complexified tangent tubular map. -/
theorem exists_parameterSlice_tangentTubularMap
    (t : ℝ) (hβtime : ∀ p, (β p).1 = p.1) (hHtime : ∀ p, (H p).1 = p.1)
    (hβslice : ∀ x, β (t, x) = (t, f x))
    (hHslice : ∀ z, H (t, z) = (t, smoothTangentMap f z))
    (eZ : ∀ p : P, νH p ≃L[ℝ] νTβ (jM p))
    (heZ : ∀ (p : ℝ × TM) (v : ℝ × (F × F)),
      eZ p ((LinearMap.range (mfderiv 𝓘(ℝ, ℝ × (E × E))
        𝓘(ℝ, ℝ × (F × F)) H p).toLinearMap).mkQ v) =
          (LinearMap.range (mfderiv 𝓘(ℝ, (ℝ × E) × (ℝ × E))
            𝓘(ℝ, (ℝ × F) × (ℝ × F)) (smoothTangentMap β) (jM p)).toLinearMap).mkQ
              (mfderiv 𝓘(ℝ, ℝ × (F × F)) 𝓘(ℝ, (ℝ × F) × (ℝ × F)) jN (H p) v))
    (heZs :
      letI := normalBundleFiberBundle H hH
      letI := normalBundleVectorBundle H hH
      letI := normalBundleContMDiffVectorBundle H hH
      letI := normalBundleFiberBundle (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
      letI := normalBundleVectorBundle (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
      letI := normalBundleContMDiffVectorBundle
        (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
      ContMDiff (𝓘(ℝ, ℝ × (E × E)).prod 𝓘(ℝ, VH))
        (𝓘(ℝ, ℝ × (E × E)).prod 𝓘(ℝ, VTβ)) ∞
        (fun z : TotalSpace VH νH ↦ (⟨z.proj, eZ z.proj z.snd⟩ :
          TotalSpace VTβ ((jM : ℝ × TM → TP) *ᵖ νTβ))))
    (Sβ : TangentNormalSplitting β hβ) (T : TubularNeighborhood H hH)
    (hTtime : ∀ z, (T.totalMap H hH z).1 = z.proj.1) :
    letI : ∀ p : P, AddCommGroup (V p) :=
      fun p ↦ by change AddCommGroup (νβ (p.1, p.2.proj)); infer_instance
    letI : ∀ p : P, Module ℝ (V p) :=
      fun p ↦ by change Module ℝ (νβ (p.1, p.2.proj)); infer_instance
    letI := ComplexBundle.complexificationTopology Vβ V
    let B : P → Type _ := fun p : P ↦ ℂ ⊗[ℝ] V p
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
    let r (p : P) : (ℂ ⊗[ℝ] V p) ≃ₗ[ℝ] (V p × V p) := complexificationReIm (V p)
    ∀ C : TotalSpace Unit B ≃ₜ TotalSpace VH νH,
      (∀ (p : P) (v : B p), C ⟨p, v⟩ =
        ⟨p, (eZ p).symm ((Sβ.equiv (jM p)).symm (r p v))⟩) →
      ∃ (S : TangentNormalSplitting f hf)
        (Tf : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
        (U : @ComplexBundle.Iso TM (ComplexifiedNormalPullback f) D gF mF gD mD
          (complexifiedNormalPullbackTopology f) tD),
        ∀ w : TotalSpace Unit (ComplexifiedNormalPullback f),
          tangentEmbeddingTubularMap f hf S Tf w =
            (T.totalMap H hH (C ⟨(t, w.proj), U.linearEquiv w.proj w.snd⟩)).2 := by
  classical
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let := normalBundleFiberBundle β hβ.isImmersion
  let := normalBundleVectorBundle β hβ.isImmersion
  let := normalBundleContMDiffVectorBundle β hβ.isImmersion
  let := normalBundleFiberBundle H hH
  let := normalBundleVectorBundle H hH
  let := normalBundleContMDiffVectorBundle H hH
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let (p : P) : AddCommGroup (V p) := by
    change AddCommGroup (νβ (p.1, p.2.proj)); infer_instance
  let (p : P) : Module ℝ (V p) := by
    change Module ℝ (νβ (p.1, p.2.proj)); infer_instance
  let := ComplexBundle.complexificationTopology Vβ V
  change ∀ C : TotalSpace Unit (fun p : P ↦ ℂ ⊗[ℝ] V p) ≃ₜ TotalSpace VH νH, _
  intro C hC
  -- Both slice equivalences use the same zero parameter-velocity representative formula.
  obtain ⟨e, he, hes, heis⟩ := exists_parameterSlice_normalEquiv
    f β hf.isImmersion hβ.isImmersion hβtime t hβslice
  obtain ⟨eH, heH, heHs, _⟩ := exists_parameterSlice_normalEquiv
    (smoothTangentMap f) H (isImmersion_smoothTangentMap f hf) hH hHtime t hHslice
  obtain ⟨S, hS⟩ := exists_parameterSlice_tangentNormalSplitting f β H hf hβ hH
    t hβslice hHslice e eH eZ he heH heZ heis heHs heZs Sβ
  obtain ⟨Tf, hTf⟩ := exists_tubularNeighborhood_parameterSlice (smoothTangentMap f) H
    (isImmersion_smoothTangentMap f hf) hH hHtime t hHslice eH heH T hTtime
  obtain ⟨U, hU⟩ := exists_parameterSlice_complexifiedNormalIso f β hf.isImmersion
    hβ.isImmersion t e hes heis
  refine ⟨S, Tf, U, ?_⟩
  rcases U with ⟨ue, hUs, hUi⟩
  intro w
  -- Scalar extension acts on the two ordered real factors by this same real equivalence.
  let rf : ComplexifiedNormalPullback f w.proj ≃ₗ[ℝ]
      (νf w.proj.proj × νf w.proj.proj) := complexificationReIm (νf w.proj.proj)
  let rβ : (ℂ ⊗[ℝ] V (t, w.proj)) ≃ₗ[ℝ]
      (V (t, w.proj) × V (t, w.proj)) := complexificationReIm (V (t, w.proj))
  -- Use the actual fiber map before comparing its two definitionally equal pullback forms.
  let u := ue w.proj
  let l : ComplexifiedNormalPullback f w.proj ≃ₗ[ℂ] (ℂ ⊗[ℝ] V (t, w.proj)) :=
    (e w.proj.proj).toLinearEquiv.baseChange ℝ ℂ _ _
  have hu (v : ComplexifiedNormalPullback f w.proj) : u v = l v := hU w.proj v
  have hcoords (v : ComplexifiedNormalPullback f w.proj) :
      rβ (u v) = (e w.proj.proj (rf v).1, e w.proj.proj (rf v).2) := by
    rw [hu]
    induction v using TensorProduct.inductionOn with
    | tmul z v =>
      change complexificationReIm _
        (((e w.proj.proj).toLinearEquiv.baseChange ℝ ℂ _ _) (z ⊗ₜ[ℝ] v)) = _
      rw [LinearEquiv.baseChange_tmul, (complexificationReIm_properties _).1]
      change _ = (e w.proj.proj ((complexificationReIm _ (z ⊗ₜ[ℝ] v)).1),
        e w.proj.proj ((complexificationReIm _ (z ⊗ₜ[ℝ] v)).2))
      rw [(complexificationReIm_properties _).1, map_smul, map_smul]
      rfl
    | add u v hu hv =>
      simp only [map_add, hu, hv, Prod.fst_add, Prod.snd_add]
      rfl
  let a := rf w.snd
  let v : νTf w.proj := (S.equiv w.proj).symm a
  have hv : eH w.proj v = (eZ (t, w.proj)).symm
      ((Sβ.equiv (jM (t, w.proj))).symm (rβ (u w.snd))) := by
    apply (eZ (t, w.proj)).injective
    apply (Sβ.equiv (jM (t, w.proj))).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
      hS, hcoords]
    change (e w.proj.proj ((S.equiv w.proj) ((S.equiv w.proj).symm a)).1,
      e w.proj.proj ((S.equiv w.proj) ((S.equiv w.proj).symm a)).2) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  change Tf.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf) ⟨w.proj, v⟩ = _
  rw [hTf, hC, hv]
  rfl

end AtiyahSinger
