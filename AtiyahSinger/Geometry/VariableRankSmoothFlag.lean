/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothAtlasRestriction
public import AtiyahSinger.Geometry.SmoothAtlasTopologyTransport
public import AtiyahSinger.Geometry.SmoothHermitianFlagSplitting
public import AtiyahSinger.Topology.VariableRankFlagSplitting

/-!
# The original smooth splitting on every actual rank stratum

Public module ID: M1510.

C01. The original smooth atlas and metric give smooth flag fibrations on the
actual clopen rank strata. Each selected atlas has real dimension n+r(r-1).
There is no assertion of one fixed-dimensional smooth model on the union when
ranks vary. The global topological projection is still proper.

The bridge restricts the original atlas, transports it only through the exact
identity-on-vectors total-topology equality, and applies the fixed-rank smooth
flag construction. Smoothness of arbitrary native continuous charts is never
assumed. The line, sum and pullback atlases below are on the existing original
range families and total topologies, and their splitting is rankFlagSplitting.

Sources: SG III.11 Proposition 11.1; Hatcher VBKT pp.71,80--81 for the
componentwise splitting. The restriction and model conversions retain the
original rank-stratum topologies and identity maps on fiber vectors.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

universe u v w

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  (E : M → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E) (A : SmoothComplexBundleAtlas.{w} (n := n) E)
  (hh : A.IsSmoothHermitianMetric h)

attribute [local instance] rankFlagTopology variableRankFlagTopology
  rankFlagLineTopology rankFlagSumTopology

include hM hh

set_option maxHeartbeats 1600000 in
-- Transport the original splitting atlases on each clopen rank piece, including rank zero.
/-- On each original rank piece the same projection, lines and splitting have smooth atlases. -/
theorem exists_rankFlag_smoothSplitting (r : ℕ) :
    ∃ hC : ChartedSpace (EuclideanSpace ℝ (Fin (n + r * (r - 1))))
        (RankFlagBundle E h r),
      letI := hC
      IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1)))) ∞
          (RankFlagBundle E h r) ∧
        Manifold.IsSubmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1))))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (rankFlagProjection E h r) ∧
        ∃ L : ∀ i : Fin r, SmoothComplexBundleAtlas.{max u v w}
            (n := n + r * (r - 1)) (RankFlagLine E h r i),
          ∃ S : SmoothComplexBundleAtlas.{max u v w}
              (n := n + r * (r - 1)) (RankFlagSum E h r),
            ∃ P : SmoothComplexBundleAtlas.{max u v w} (n := n + r * (r - 1))
                ((rankFlagProjection E h r : RankFlagBundle E h r → rankStratum E r) *ᵖ
                  (Restrict E (rankStratum E r))),
              IsSmoothAtlasBundleMapOver P A
                  (fun p : RankFlagBundle E h r ↦ (rankFlagProjection E h r p).val)
                  (fun _ ↦ LinearMap.id) ∧
                (∀ i : Fin r, IsSmoothAtlasBundleMap (L i) P
                  (fun _ ↦ Submodule.subtype _)) ∧
                (∀ i : Fin r, IsSmoothAtlasBundleMap S (L i)
                  (fun _ ↦ LinearMap.proj i)) ∧
                IsSmoothAtlasBundleMap S P
                  (fun p ↦ ((rankFlagSplitting E h r).linearEquiv p).toLinearMap) ∧
                IsSmoothAtlasBundleMap P S
                  (fun p ↦ ((rankFlagSplitting E h r).linearEquiv p).symm.toLinearMap) :=
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let U := rankStratum E r
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) U := inferInstance
  let F : U → Type v := Restrict E U
  let A₀ := A.restrictOpen U
  let hF := rankHermitianMetric E h r
  have hA₀ : A₀.IsSmoothHermitianMetric hF :=
    A.isSmoothHermitianMetric_restrictOpen U h hh
  let : IsFiniteRank F := isFiniteRank_restrict (E := E) U
  let : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  let := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
  let := hF.nativeFiberBundle r (fun x ↦ x.property)
  let := hF.nativeVectorBundle r (fun x ↦ x.property)
  have ht := ContinuousHermitianMetric.modelTopology_nativeModelTopology (E := F) r
  let hN := hF.nativeModelMetric r
  let := hermitianFlagTopology r F hN
  let AN := A₀.congrTopology ht.symm
  have hAN : letI := modelTopology (EuclideanSpace ℂ (Fin r)) F
      AN.IsSmoothHermitianMetric hN := by
    exact A₀.isSmoothHermitianMetric_congrTopology ht.symm hF hN rfl hA₀
  -- The inverse phantom-model conversions recover each original induced total topology.
  have hline (i : Fin r) : hermitianFlagLineTopology r F hN i =
      rankFlagLineTopology E h r i := by
    exact congrArg (fun t : TopologicalSpace (TotalSpace Unit F) ↦
      letI := t
      TopologicalSpace.induced
        (fun z : TotalSpace Unit (RankFlagLine E h r i) ↦
          (⟨z.proj, z.snd.val⟩ : TotalSpace Unit
            ((rankFlagProjection E h r : RankFlagBundle E h r → rankStratum E r) *ᵖ F)))
        inferInstance) ht
  have hsum : hermitianFlagSumTopology r F hN = rankFlagSumTopology E h r := by
    exact congrArg (fun t : ∀ i : Fin r,
        TopologicalSpace (TotalSpace Unit (RankFlagLine E h r i)) ↦
      letI := t
      TopologicalSpace.induced
        (fun z : TotalSpace Unit (RankFlagSum E h r) ↦
          (z.proj, fun i : Fin r ↦
            (⟨z.proj, z.snd i⟩ : TotalSpace Unit (RankFlagLine E h r i))))
        inferInstance) (funext hline)
  have hpullback :
      @Pullback.TotalSpace.topologicalSpace _ Unit F _ (rankFlagProjection E h r)
        (rankFlagTopology E h r) (modelTopology (EuclideanSpace ℂ (Fin r)) F) =
      @Pullback.TotalSpace.topologicalSpace _ Unit F _ (rankFlagProjection E h r)
        (rankFlagTopology E h r) inferInstance := by
    exact congrArg (fun t : TopologicalSpace (TotalSpace Unit F) ↦
      @Pullback.TotalSpace.topologicalSpace _ Unit F _ (rankFlagProjection E h r)
        (rankFlagTopology E h r) t) ht
  -- Use the fixed-rank theorem on this original rank stratum and this transported atlas.
  let C := hermitianFlagChartedSpace r F hN AN hAN
  refine ⟨C, ?_⟩
  let := C
  refine ⟨hermitianFlagIsManifold r F hN AN hAN,
    hermitianFlagProjection_isSubmersion r F hN AN hAN, ?_⟩
  obtain ⟨LN, SN, PN, hPN, hLN, hSN, hforward, hbackward⟩ :=
    exists_hermitianFlag_smoothSplittingAtlases r F hN AN hAN
  let L (i : Fin r) := (LN i).congrTopology (hline i)
  let S := SN.congrTopology hsum
  let P := PN.congrTopology hpullback
  have hAN₀ : AN.congrTopology ht = A₀ := A₀.congrTopology_symm ht.symm
  have hP₀ : IsSmoothAtlasBundleMapOver P A₀ (rankFlagProjection E h r)
      (fun _ ↦ LinearMap.id) := by
    have hnative := (SmoothComplexBundleAtlas.isSmoothAtlasBundleMapOver_congrTopology
      PN AN hpullback ht (rankFlagProjection E h r) (fun _ ↦ LinearMap.id)).mpr hPN
    exact (congrArg (fun B ↦ IsSmoothAtlasBundleMapOver P B
      (rankFlagProjection E h r) (fun _ ↦ LinearMap.id)) hAN₀).mp hnative
  have htoA : IsSmoothAtlasBundleMapOver P A
      (fun p : RankFlagBundle E h r ↦ (rankFlagProjection E h r p).val)
      (fun _ ↦ LinearMap.id) := by
    refine ⟨(contMDiff_subtype_val (U := U)).comp hP₀.1, ?_⟩
    intro i j k
    have hs := hP₀.2 i j k
    have hbase : (A₀.chart j).baseSet =
        (Subtype.val : U → M) ⁻¹' (A.chart j).baseSet :=
      (A.exists_restrictOpenChart U j).choose_spec.1
    rw [hbase] at hs
    apply hs.congr
    intro p hp
    simp only [dite_eq_left hp.1]
    exact ((A.exists_restrictOpenChart U j).choose_spec.2
      ⟨rankFlagProjection E h r p, (P.frameLinearEquiv i p hp.1).symm
        (Pi.single k 1)⟩).symm
  refine ⟨L, S, P, htoA, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (SmoothComplexBundleAtlas.isSmoothAtlasBundleMapOver_congrTopology
      (LN i) PN (hline i) hpullback id (fun _ ↦ Submodule.subtype _)).mpr (hLN i)
  · intro i
    exact (SmoothComplexBundleAtlas.isSmoothAtlasBundleMapOver_congrTopology
      SN (LN i) hsum (hline i) id (fun _ ↦ LinearMap.proj i)).mpr (hSN i)
  · exact (SmoothComplexBundleAtlas.isSmoothAtlasBundleMapOver_congrTopology
      SN PN hsum hpullback id
        (fun p ↦ ((rankFlagSplitting E h r).linearEquiv p).toLinearMap)).mpr hforward
  · exact (SmoothComplexBundleAtlas.isSmoothAtlasBundleMapOver_congrTopology
      PN SN hpullback hsum id
        (fun p ↦ ((rankFlagSplitting E h r).linearEquiv p).symm.toLinearMap)).mpr hbackward

/-- The smooth atlas on this original rank-piece flag space. -/
@[reducible]
def rankFlagChartedSpace (r : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + r * (r - 1)))) (RankFlagBundle E h r) :=
  (exists_rankFlag_smoothSplitting E h A hh r).choose

/-- The chosen rank-piece atlas is smooth on the original topology. -/
instance rankFlagIsManifold (r : ℕ) :
    letI := rankFlagChartedSpace E h A hh r
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1)))) ∞
      (RankFlagBundle E h r) :=
  (exists_rankFlag_smoothSplitting E h A hh r).choose_spec.1

/-- The same original rank projection is a submersion for its chosen atlas. -/
theorem rankFlagProjection_isSubmersion (r : ℕ) :
    letI := rankFlagChartedSpace E h A hh r
    Manifold.IsSubmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1))))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (rankFlagProjection E h r) := by
  /- Use the submersion certificate of the same selected atlas. Its local
  product charts come from the original restricted A-frames and h, and the
  map is the original base projection, including the identity case r=0. -/
  exact (exists_rankFlag_smoothSplitting E h A hh r).choose_spec.2.1

/-- The selected smooth atlas on each original range line in this rank stratum. -/
@[reducible]
def rankFlagLineSmoothAtlas (r : ℕ) (i : Fin r) :
    letI := rankFlagChartedSpace E h A hh r
    SmoothComplexBundleAtlas.{max u v w} (n := n + r * (r - 1))
      (RankFlagLine E h r i) :=
  (exists_rankFlag_smoothSplitting E h A hh r).choose_spec.2.2.choose i

/-- The selected atlas on the same finite sum of original range lines. -/
@[reducible]
def rankFlagSumSmoothAtlas (r : ℕ) :
    letI := rankFlagChartedSpace E h A hh r
    SmoothComplexBundleAtlas.{max u v w} (n := n + r * (r - 1))
      (RankFlagSum E h r) :=
  (exists_rankFlag_smoothSplitting E h A hh r).choose_spec.2.2.choose_spec.choose

/-- The selected atlas on the original restricted pullback, with its existing topology. -/
@[reducible]
def rankFlagPullbackSmoothAtlas (r : ℕ) :
    letI := rankFlagChartedSpace E h A hh r
    SmoothComplexBundleAtlas.{max u v w} (n := n + r * (r - 1))
      ((rankFlagProjection E h r : RankFlagBundle E h r → rankStratum E r) *ᵖ
        (Restrict E (rankStratum E r))) :=
  (exists_rankFlag_smoothSplitting E h A hh r).choose_spec.2.2.choose_spec.choose_spec.choose

/-- Smoothness of the unchanged rank-piece splitting and inverse, with original-atlas compatibility.
This grouped certificate retains the same three selected atlases and original structural maps. -/
theorem rankFlagSmoothSplitting_compatibility (r : ℕ) :
    letI := rankFlagChartedSpace E h A hh r
    IsSmoothAtlasBundleMapOver (rankFlagPullbackSmoothAtlas E h A hh r) A
        (fun p : RankFlagBundle E h r ↦ (rankFlagProjection E h r p).val)
        (fun _ ↦ LinearMap.id) ∧
      (∀ i : Fin r, IsSmoothAtlasBundleMap (rankFlagLineSmoothAtlas E h A hh r i)
        (rankFlagPullbackSmoothAtlas E h A hh r) (fun _ ↦ Submodule.subtype _)) ∧
      (∀ i : Fin r, IsSmoothAtlasBundleMap (rankFlagSumSmoothAtlas E h A hh r)
        (rankFlagLineSmoothAtlas E h A hh r i) (fun _ ↦ LinearMap.proj i)) ∧
      IsSmoothAtlasBundleMap (rankFlagSumSmoothAtlas E h A hh r)
        (rankFlagPullbackSmoothAtlas E h A hh r)
        (fun p ↦ ((rankFlagSplitting E h r).linearEquiv p).toLinearMap) ∧
      IsSmoothAtlasBundleMap (rankFlagPullbackSmoothAtlas E h A hh r)
        (rankFlagSumSmoothAtlas E h A hh r)
        (fun p ↦ ((rankFlagSplitting E h r).linearEquiv p).symm.toLinearMap) := by
  /- All atlases are projections of one selected existence witness. Transfer
  its original structural-map certificates without choosing new line, sum
  or pullback atlases. The same sum/projection formulas give the displayed
  actual Iso and inverse on every original fiber in this rank stratum. -/
  have hspec := (exists_rankFlag_smoothSplitting E h A hh r).choose_spec.2.2
  exact hspec.choose_spec.choose_spec.choose_spec

omit hM hh in
/-- The global original flag projection is proper without a uniform rank bound. -/
theorem variableRankFlagProjection_isProperMap :
    IsProperMap (variableRankFlagProjection E h) := by
  /- Stage 1: each rank projection is the original native fixed-rank flag
  projection, so it is proper by hermitianFlagProjection_isProperMap.
  Stage 2: the original base is the disjoint union of its clopen rank strata,
  and the global domain is the corresponding topological sum of rank flags.
  Closedness of a map is local on the target, so the global projection is
  closed. Its fibers are precisely the compact flag fibers on their unique
  rank piece. Continuity and the closed-map/compact-fiber criterion give
  properness, with no compactness or separation assumption on the base. -/
  classical
  have hp (r : ℕ) : IsProperMap (rankFlagProjection E h r) := by
    let F := Restrict E (rankStratum E r)
    let : IsFiniteRank F := isFiniteRank_restrict (E := E) (rankStratum E r)
    let hF := rankHermitianMetric E h r
    let : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
    let : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
    let := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
    let := hF.nativeFiberBundle r (fun x ↦ x.property)
    let := hF.nativeVectorBundle r (fun x ↦ x.property)
    exact hermitianFlagProjection_isProperMap r F (hF.nativeModelMetric r)
  let P := variableRankFlagProjection E h
  let U (r : ℕ) : TopologicalSpace.Opens M := rankStratum E r
  have hU : TopologicalSpace.IsOpenCover U := by
    apply TopologicalSpace.IsOpenCover.of_sets (fun r ↦ (rankStratum E r).isOpen)
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨Module.finrank ℂ (E x), rfl⟩
  -- On an open rank stratum, the image of a closed set is the original rank-piece image.
  have hclosed : IsClosedMap P := by
    intro S hS
    apply hU.isClosed_iff_coe_preimage.mpr
    intro r
    have heq : (Subtype.val : rankStratum E r → M) ⁻¹' (P '' S) =
        rankFlagProjection E h r '' (Sigma.mk r ⁻¹' S) := by
      ext x
      constructor
      · rintro ⟨⟨k, z⟩, hz, hzx⟩
        have hk : k = r := by
          have hk' := (rankFlagProjection E h k z).property
          change Module.finrank ℂ (E (P ⟨k, z⟩)) = k at hk'
          rw [hzx] at hk'
          exact hk'.symm.trans x.property
        subst k
        exact ⟨z, hz, Subtype.ext hzx⟩
      · rintro ⟨z, hz, hzx⟩
        exact ⟨⟨r, z⟩, hz, congrArg Subtype.val hzx⟩
    rw [heq]
    exact (hp r).isClosedMap _ (hS.preimage continuous_sigmaMk)
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨P.continuous, hclosed, ?_⟩
  intro x
  let r := Module.finrank ℂ (E x)
  let xr : rankStratum E r := ⟨x, rfl⟩
  -- Each global fiber is the continuous image of the one compact fiber at its actual rank.
  have heq : P ⁻¹' {x} = Sigma.mk r '' ((rankFlagProjection E h r) ⁻¹' {xr}) := by
    ext z
    constructor
    · intro hz
      rcases z with ⟨k, z⟩
      have hz' : P ⟨k, z⟩ = x := hz
      have hk : k = r := by
        have hk' := (rankFlagProjection E h k z).property
        change Module.finrank ℂ (E (P ⟨k, z⟩)) = k at hk'
        rw [hz'] at hk'
        exact hk'.symm
      subst k
      exact ⟨z, Subtype.ext hz', rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact congrArg Subtype.val (show rankFlagProjection E h r w = xr from hw)
  rw [heq]
  exact ((hp r).isCompact_preimage isCompact_singleton).image continuous_sigmaMk


end AtiyahSinger.ComplexBundle
