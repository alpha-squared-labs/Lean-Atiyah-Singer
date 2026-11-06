/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportActionFunctoriality
public import AtiyahSinger.Topology.CompactSupportModule
public import AtiyahSinger.Topology.RealBundleSupport
public import AtiyahSinger.Topology.SupportedThomModule
public import AtiyahSinger.Topology.TangentEmbeddingPushforward

/-!
# The compact-support projection formula for the actual tangent pushforward

Public module ID: M2234.

The product is the existing proper-graph action. Both factors here have compact
support. This is the corresponding specialization of Karoubi IV.5.22(b), whose
coefficient factor belongs to the generally larger homotopy K group of bundles
without compact-support conditions. No identification of those two coefficient
groups on a noncompact tangent space is asserted.

The tangent map, pushforward and graph action are the original constructions.
The tubular contraction is generally not proper; the multiplication homotopy
uses a proper graph and the fixed compact control of the Thom representative.
Source: SG Appendix C.1 and III.12; KA IV.5.22(b), printed pp.231--232.
The proof retains the same compact Thom representative, actual normal-bundle
contraction and proper graph throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
  normalBundleTopology complexifiedNormalPullbackTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (hp : IsProperMap f)

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N

set_option maxHeartbeats 1000000 in
-- Normalize the original Thom action and open tube in the projection formula.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tangent pushforward satisfies the projection formula for compact-support factors. -/
theorem tangentEmbeddingPushforward_action :
    letI : T2Space TM := (tangentBundle_topology E M).1
    letI : T2Space TN := (tangentBundle_topology F N).1
    letI : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
    letI : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
    ∀ (a : CompactSupportKZero TM) (b : CompactSupportKZero TN),
      tangentEmbeddingPushforward f hf hp
          (compactSupportKZeroAction
            ⟨smoothTangentMap f, (smoothTangentMap f).contMDiff.continuous⟩ b a) =
        compactSupportKZeroAction (ContinuousMap.id TN) b
          (tangentEmbeddingPushforward f hf hp a) := by
  classical
  let : T2Space TM := (tangentBundle_topology E M).1
  let : T2Space TN := (tangentBundle_topology F N).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  intro a b
  let Tf : C(TM, TN) := ⟨smoothTangentMap f, (smoothTangentMap f).contMDiff.continuous⟩
  have hWith (S : TangentNormalSplitting f hf)
      (T : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
      (h : ComplexBundle.ContinuousHermitianMetric (ComplexifiedNormalPullback f)) :
      tangentEmbeddingPushforwardWith f hf S T h (compactSupportKZeroAction Tf b a) =
        compactSupportKZeroAction (ContinuousMap.id TN) b
          (tangentEmbeddingPushforwardWith f hf S T h a) := by
    let V := ComplexifiedNormalPullback f
    let X := TotalSpace Unit V
    let τ := tangentEmbeddingTubularMap f hf S T
    have hτ : IsOpenEmbedding τ := isOpenEmbedding_tangentEmbeddingTubularMap f hf S T
    let : T2Space X := hτ.isEmbedding.t2Space
    let : LocallyCompactSpace X := hτ.locallyCompactSpace
    let := isFiniteRank_complexifiedNormalPullback f hf.isImmersion
    let p : C(X, TM) := ⟨π Unit V, ComplexBundle.continuous_proj⟩
    -- On the actual normal bundle, contraction joins the zero section to the original tube.
    let VT := NormalModel (E × E) (F × F)
    let νT := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
    let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    let : RealBundle.IsFiniteRank VT νT := RealBundle.isFiniteRank_of_vectorBundle VT νT
    let C := complexifiedNormalTotalHomeomorph f hf S
    let K := RealBundle.scalingHomotopy VT νT
    let tube := T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    let H : ContinuousMap.Homotopy (Tf.comp p) τ :=
      { toFun z := tube (K (z.1, C z.2))
        continuous_toFun := tube.continuous.comp
          (K.continuous.comp (continuous_fst.prodMk (C.continuous.comp continuous_snd)))
        map_zero_left := by
          intro z
          change tube (K (0, C z)) = smoothTangentMap f z.proj
          rw [K.apply_zero]
          exact T.map_zero z.proj
        map_one_left := by
          intro z
          change tube (K (1, C z)) = τ z
          rw [K.apply_one]
          rfl }
    -- Retaining the total-space coordinate makes the graph homotopy proper at every time.
    have haction := compactSupportKZeroAction_eq_of_homotopy H
    have hvalue := DFunLike.congr_fun (DFunLike.congr_fun haction b) (h.supportedThomHom a)
    -- Tensor reassociation gives the module formula before extension by the very same tube.
    change compactSupportKZeroOpenPushforward τ hτ
        (h.supportedThomHom (compactSupportKZeroAction Tf b a)) =
      compactSupportKZeroAction (ContinuousMap.id TN) b
        (compactSupportKZeroOpenPushforward τ hτ (h.supportedThomHom a))
    rw [h.supportedThomHom_action Tf b a, hvalue]
    exact (compactSupportKZeroAction_openPushforward
      (ContinuousMap.id TN) τ hτ b (h.supportedThomHom a)).symm
  -- The chosen original splitting, tube and metric are one instance of this calculation.
  unfold tangentEmbeddingPushforward
  exact hWith _ _ _

end AtiyahSinger
