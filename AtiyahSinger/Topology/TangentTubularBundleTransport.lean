/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RetractionBundleHomotopy
public import AtiyahSinger.Topology.TangentEmbeddingPushforward
public import AtiyahSinger.Topology.RealBundleSupport

/-!
# Actual bundle transport along a tangent tubular map

Public module ID: M2242.

Radial scaling on the original tangent normal, conjugated by the specified
complexification and normalized splitting, gives a homotopy from the
zero-section restriction Tf to the actual tubular map. The resulting complex bundle isomorphism is
normalized to the vector identity on that zero section.

This is the bundle comparison required before Thom transitivity: the bundle
pulled back by the tube is compared with the pullback of (Tf)*B by the bundle
projection. The contraction is not claimed proper. Its only use is ordinary
bundle homotopy invariance, with the original finite-rank bundles and vectors.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Manifold Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [T2Space N] [SecondCountableTopology N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (S : TangentNormalSplitting f hf)
  (T : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
  (B : TangentBundle 𝓘(ℝ, F) N → Type*)
  [∀ z, AddCommGroup (B z)] [∀ z, Module ℂ (B z)]
  [TopologicalSpace (TotalSpace Unit B)] [IsFiniteRank B]

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tube pullback is the projection pullback, normalized at its original zero section. -/
theorem exists_tangentTubular_pullback_iso :
    ∃ e : Iso
        ((π Unit (ComplexifiedNormalPullback f)) *ᵖ
          ((smoothTangentMap f : TangentBundle 𝓘(ℝ, E) M → TangentBundle 𝓘(ℝ, F) N) *ᵖ B))
        ((tangentEmbeddingTubularMap f hf S T :
          TotalSpace Unit (ComplexifiedNormalPullback f) → TangentBundle 𝓘(ℝ, F) N) *ᵖ B),
      ∀ (z : TangentBundle 𝓘(ℝ, E) M) (v : B (smoothTangentMap f z)),
        HEq (e.linearEquiv ⟨z, 0⟩ v) v := by
  classical
  let TM := TangentBundle 𝓘(ℝ, E) M
  let TN := TangentBundle 𝓘(ℝ, F) N
  let X := TotalSpace Unit (ComplexifiedNormalPullback f)
  let νT := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
  let VT := NormalModel (E × E) (F × F)
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let : RealBundle.IsFiniteRank VT νT := RealBundle.isFiniteRank_of_vectorBundle _ _
  let : IsFiniteRank (ComplexifiedNormalPullback f) :=
    isFiniteRank_complexifiedNormalPullback f hf.isImmersion
  let : T2Space TN := (tangentBundle_topology F N).1
  let : SecondCountableTopology TN := (tangentBundle_topology F N).2.1
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  let τ := tangentEmbeddingTubularMap f hf S T
  let he := isOpenEmbedding_tangentEmbeddingTubularMap f hf S T
  let : T2Space X := he.isEmbedding.t2Space
  let : SecondCountableTopology X := he.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace X := he.locallyCompactSpace
  let : ParacompactSpace X := inferInstance
  let q : C(X, TM) := ⟨TotalSpace.proj, continuous_proj⟩
  let Tf : C(TM, TN) := ⟨smoothTangentMap f, (smoothTangentMap f).contMDiff.continuous⟩
  let r : C(X, X) :=
    ⟨fun z ↦ ⟨z.proj, 0⟩, (continuous_zero_section (ComplexifiedNormalPullback f)).comp
      q.continuous⟩
  let C := complexifiedNormalTotalHomeomorph f hf S
  have hCzero (z : TM) : C ⟨z, 0⟩ = (⟨z, 0⟩ : TotalSpace VT νT) := by
    change (⟨z, (S.equiv z).symm (complexificationReIm
      (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj) 0)⟩ : TotalSpace VT νT) = _
    simp only [map_zero]
  have hCzeroInv (z : TM) : C.symm (⟨z, 0⟩ : TotalSpace VT νT) = (⟨z, 0⟩ : X) := by
    apply C.injective
    rw [C.apply_symm_apply, hCzero]
  have hτzero (z : TM) : τ ⟨z, 0⟩ = Tf z := by
    change T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
      (C ⟨z, 0⟩) = Tf z
    rw [hCzero]
    exact T.map_zero z
  -- Contract the actual normal fibers, then return through the same supplied splitting.
  let J := RealBundle.scalingHomotopy VT νT
  let H : ContinuousMap.Homotopy (τ.comp r) τ := {
    toFun p := τ (C.symm (J (p.1, C p.2)))
    continuous_toFun := τ.continuous.comp (C.symm.continuous.comp (J.continuous.comp
      (continuous_fst.prodMk (C.continuous.comp continuous_snd))))
    map_zero_left z := by
      rw [J.apply_zero]
      change τ (C.symm (⟨z.proj, 0⟩ : TotalSpace VT νT)) = τ (r z)
      rw [hCzeroInv]
      rfl
    map_one_left z := by
      rw [J.apply_one]
      change τ (C.symm (C z)) = τ z
      rw [C.symm_apply_apply] }
  have hr (z : X) : r (r z) = r z := rfl
  obtain ⟨e, hezero⟩ := exists_pullback_iso_of_homotopic_retraction B τ r hr ⟨H⟩
  -- The endpoint map at time zero is exactly Tf after projection, on the same original source.
  have hk : τ.comp r = Tf.comp q := by
    apply ContinuousMap.ext
    intro z
    exact hτzero z.proj
  let Ψ (k : C(X, TN)) : Prop :=
    ∃ e : Iso ((k : X → TN) *ᵖ B) ((τ : X → TN) *ᵖ B),
      ∀ (z : TM) (v : B (k ⟨z, 0⟩)), HEq (e.linearEquiv ⟨z, 0⟩ v) v
  have hresult : Ψ (τ.comp r) := ⟨e, fun z v ↦ hezero ⟨z, 0⟩ rfl v⟩
  rw [hk] at hresult
  obtain ⟨e₀, he₀⟩ := hresult
  let c := pullbackCompIso (E := B) Tf q
  refine ⟨c.trans e₀, ?_⟩
  intro z v
  change HEq (e₀.linearEquiv ⟨z, 0⟩ (c.linearEquiv ⟨z, 0⟩ v)) v
  rw [pullbackCompIso_apply]
  exact he₀ z v

end AtiyahSinger
