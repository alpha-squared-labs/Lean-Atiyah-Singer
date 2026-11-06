/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentNormalHomotopy
public import AtiyahSinger.Geometry.TubularIsotopy
public import AtiyahSinger.Topology.ComplexifiedNormalPullback
public import AtiyahSinger.Topology.HermitianSupportedThom

/-!
# The actual tangent embedding pushforward

Public module ID: M2235.

The fixed complex bundle is the complexification of the original normal bundle
pulled back to TM. Its ordered real/imaginary map, a normalized splitting of the
canonical tangent-normal exact sequence, and a normalized tube give an actual
open embedding into TN. The pushforward is the existing supported Thom operator
followed by open extension along precisely that composite map.

The order is SG III.12, printed p.241: quotient direction first, vertical second,
with multiplication by I acting as (u,v) ↦ (-v,u). Karoubi IV.5.21, printed p.230,
supports the Thom/tube construction and tube-choice comparison, but uses the
conjugate complex structure for a different convention. Its sign convention is
not silently transferred here. The composition and projection formulas are
proved in `TangentEmbeddingComposition` and `TangentEmbeddingProjection`.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff unitInterval

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
local notation "ν" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
local notation "νT" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
local notation "VT" => NormalModel (E × E) (F × F)

/-- The actual real identification of the fixed complexification with the tangent normal bundle. -/
def complexifiedNormalTotalHomeomorph (S : TangentNormalSplitting f hf) :
    TotalSpace Unit (ComplexifiedNormalPullback f) ≃ₜ TotalSpace VT νT := by
  let proj := smoothTangentBundleProjection E M
  letI : ∀ z, AddCommGroup ((proj *ᵖ ν) z) :=
    fun z ↦ inferInstanceAs (AddCommGroup (ν (proj z)))
  let e : TotalSpace Unit (ComplexifiedNormalPullback f) ≃ₜ
      TotalSpace (NormalModel E F × NormalModel E F)
        (((proj : TM → M) *ᵖ ν) ×ᵇ ((proj : TM → M) *ᵖ ν)) :=
    ComplexBundle.complexificationDoubleTotalHomeomorph (NormalModel E F)
      ((proj : TM → M) *ᵖ ν)
  exact e.trans (S.totalHomeomorph f hf).symm

/-- Complexification, the inverse normalized splitting, and the original tube as one actual map. -/
def tangentEmbeddingTubularMap (S : TangentNormalSplitting f hf)
    (T : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)) :
    C(TotalSpace Unit (ComplexifiedNormalPullback f), TN) :=
  (T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)).comp
    ⟨complexifiedNormalTotalHomeomorph f hf S,
      (complexifiedNormalTotalHomeomorph f hf S).continuous⟩

set_option linter.defProp false in
/-- The open-embedding certificate is composed from the same three actual maps. -/
def isOpenEmbedding_tangentEmbeddingTubularMap (S : TangentNormalSplitting f hf)
    (T : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)) :
    IsOpenEmbedding (tangentEmbeddingTubularMap f hf S T) := by
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  exact (T.target.isOpen.isOpenEmbedding_subtypeVal.comp
    T.diffeomorph.toHomeomorph.isOpenEmbedding).comp
      (complexifiedNormalTotalHomeomorph f hf S).isOpenEmbedding

variable [T2Space M] [T2Space N]
  [SecondCountableTopology M] [SecondCountableTopology N]

/-- The geometric pushforward with its splitting, tube and continuous Hermitian metric explicit. -/
def tangentEmbeddingPushforwardWith (S : TangentNormalSplitting f hf)
    (T : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
    (h : ComplexBundle.ContinuousHermitianMetric (ComplexifiedNormalPullback f)) :
    letI : T2Space TM := (tangentBundle_topology E M).1
    letI : T2Space TN := (tangentBundle_topology F N).1
    letI : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
    letI : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
    CompactSupportKZero TM →+ CompactSupportKZero TN := by
  letI : T2Space TM := (tangentBundle_topology E M).1
  letI : T2Space TN := (tangentBundle_topology F N).1
  letI : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  letI : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  letI := isFiniteRank_complexifiedNormalPullback f hf.isImmersion
  let he := isOpenEmbedding_tangentEmbeddingTubularMap f hf S T
  letI := he.isEmbedding.t2Space
  letI := he.locallyCompactSpace
  exact (compactSupportKZeroOpenPushforward (tangentEmbeddingTubularMap f hf S T) he).comp
    h.supportedThomHom


/-- The actual Thom-to-tube pushforward is independent of all three auxiliary choices. -/
theorem tangentEmbeddingPushforwardWith_eq (S₀ S₁ : TangentNormalSplitting f hf)
    (T₀ T₁ : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
    (h₀ h₁ : ComplexBundle.ContinuousHermitianMetric (ComplexifiedNormalPullback f)) :
    tangentEmbeddingPushforwardWith f hf S₀ T₀ h₀ =
      tangentEmbeddingPushforwardWith f hf S₁ T₁ h₁ := by
  classical
  let : T2Space TM := (tangentBundle_topology E M).1
  let : T2Space TN := (tangentBundle_topology F N).1
  let : ParacompactSpace TM := (tangentBundle_topology E M).2.2
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := isFiniteRank_complexifiedNormalPullback f hf.isImmersion
  let X := TotalSpace Unit (ComplexifiedNormalPullback f)
  let h₀₀ := isOpenEmbedding_tangentEmbeddingTubularMap f hf S₀ T₀
  let h₁₀ := isOpenEmbedding_tangentEmbeddingTubularMap f hf S₁ T₀
  let h₁₁ := isOpenEmbedding_tangentEmbeddingTubularMap f hf S₁ T₁
  let := h₀₀.isEmbedding.t2Space
  let := h₀₀.locallyCompactSpace
  -- The original ordered real/imaginary map is fixed during the affine splitting path.
  let proj := smoothTangentBundleProjection E M
  let (z : TM) : AddCommGroup ((proj *ᵖ ν) z) :=
    inferInstanceAs (AddCommGroup (ν (proj z)))
  let A : X ≃ₜ TotalSpace (NormalModel E F × NormalModel E F)
      (((proj : TM → M) *ᵖ ν) ×ᵇ ((proj : TM → M) *ᵖ ν)) :=
    ComplexBundle.complexificationDoubleTotalHomeomorph (NormalModel E F)
      ((proj : TM → M) *ᵖ ν)
  obtain ⟨H, hH, _⟩ := TangentNormalSplitting.exists_inverseAffineHomotopy f hf S₀ S₁
  let τ₀ := TubularNeighborhood.totalMap (smoothTangentMap f)
    (isImmersion_smoothTangentMap f hf) T₀
  have hτ₀ : IsOpenEmbedding τ₀ :=
    T₀.target.isOpen.isOpenEmbedding_subtypeVal.comp T₀.diffeomorph.toHomeomorph.isOpenEmbedding
  let HS : ContinuousMap.Homotopy (tangentEmbeddingTubularMap f hf S₀ T₀)
      (tangentEmbeddingTubularMap f hf S₁ T₀) :=
    (ContinuousMap.Homotopy.refl τ₀).comp (H.compContinuousMap ⟨A, A.continuous⟩)
  have hHS : IsOpenEmbedding (fun p : I × X ↦ (p.1, HS p)) :=
    (IsOpenEmbedding.id.prodMap hτ₀).comp
      (hH.comp (IsOpenEmbedding.id.prodMap A.isOpenEmbedding))
  have hS := compactSupportKZeroOpenPushforward_eq_of_isotopy h₀₀ h₁₀ HS hHS
  -- Keeping the second splitting fixed, compare the two original whole-total tubes.
  let B := complexifiedNormalTotalHomeomorph f hf S₁
  obtain ⟨K, hK, _⟩ := TubularNeighborhood.exists_openIsotopy (smoothTangentMap f)
    (isImmersion_smoothTangentMap f hf) T₀ T₁
  let HT : ContinuousMap.Homotopy (tangentEmbeddingTubularMap f hf S₁ T₀)
      (tangentEmbeddingTubularMap f hf S₁ T₁) :=
    K.compContinuousMap ⟨B, B.continuous⟩
  have hHT : IsOpenEmbedding (fun p : I × X ↦ (p.1, HT p)) :=
    hK.comp (IsOpenEmbedding.id.prodMap B.isOpenEmbedding)
  have hT := compactSupportKZeroOpenPushforward_eq_of_isotopy h₁₀ h₁₁ HT hHT
  -- Both comparisons compose with the same supported Thom operator, whose metric is independent.
  change (compactSupportKZeroOpenPushforward _ h₀₀).comp h₀.supportedThomHom =
    (compactSupportKZeroOpenPushforward _ h₁₁).comp h₁.supportedThomHom
  rw [hS, hT, h₀.supportedThomHom_eq h₁]

/-- The tangent embedding pushforward for a proper smooth embedding, using actual chosen data. -/
def tangentEmbeddingPushforward (hp : IsProperMap f) :
    letI : T2Space TM := (tangentBundle_topology E M).1
    letI : T2Space TN := (tangentBundle_topology F N).1
    letI : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
    letI : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
    CompactSupportKZero TM →+ CompactSupportKZero TN := by
  -- Supply the original tangent spaces' topology properties, without changing their topology.
  letI : T2Space TM := (tangentBundle_topology E M).1
  letI : T2Space TN := (tangentBundle_topology F N).1
  letI : SecondCountableTopology TM := (tangentBundle_topology E M).2.1
  letI : SecondCountableTopology TN := (tangentBundle_topology F N).2.1
  letI : ParacompactSpace TM := (tangentBundle_topology E M).2.2
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  letI : ParacompactSpace M := inferInstance
  -- The normal and tube belong to the original tangent map, with its inherited embedding.
  let S := tangentNormalSplitting f hf
  let T := (nonempty_tubularNeighborhood (smoothTangentMap f)
    (isImmersion_smoothTangentMap f hf) (isSmoothEmbedding_tangentMap hf).isEmbedding
    (isProperMap_tangentMap hf hp)).some
  -- Select a metric on the same fixed complexification, then use the actual composite above.
  letI := isFiniteRank_complexifiedNormalPullback f hf.isImmersion
  let h := (ComplexBundle.nonempty_continuousHermitianMetric (ComplexifiedNormalPullback f)).some
  exact tangentEmbeddingPushforwardWith f hf S T h

end AtiyahSinger
