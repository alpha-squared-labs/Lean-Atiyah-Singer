/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationExternalProduct
public import AtiyahSinger.Analysis.EquivariantAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantClopenProduct
public import AtiyahSinger.Analysis.EquivariantSymbolProduct
public import AtiyahSinger.Geometry.CotangentProduct
public import AtiyahSinger.Topology.EquivariantCotangentClopenExtension
public import AtiyahSinger.Topology.EquivariantDifferentGroupProduct

/-!
# The full equivariant analytic index of an external product

Public module ID: M0529.

Two compact Lie groups act separately on two compact smooth manifolds without
boundary. Their original cotangent support classes have an external product
on the actual cotangent bundle of the product manifold. It is the existing
support product pulled back through the specified canonical cotangent splitting,
with the fixed concatenated Euclidean atlas and the native cotangent actions.
Its full analytic index is the external product in the representation rings.

Sources: ASI I section 4, B3'' and its different-group reformulation, pp.504--505,
under the compact-manifold convention on p.501; the proof is in section 9,
pp.526--529. SG III.13, Multiplicative Property 13.5 and pp.248--253, explains the operator
product and cutoff issue. ASI writes tangent bundles, identified with cotangent
bundles by invariant metrics; the formula here uses the original cotangents
throughout and requires no metric identification as an extra hypothesis.

The proof represents each original class by its finite invariant clopen symbol
family. The same native open extensions reconstruct the two classes. Bilinearity
reduces the result to each pair of original symbols, whose product index is
computed by the closed graded tensor graph and its same-symbol cutoff comparison.
No positive dimension, connectedness, nonempty base, globally constant bundle
rank or trivial action is imposed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff BigOperators

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096

variable {VG VH G H : Type*}
  [NormedAddCommGroup VG] [NormedSpace ℝ VG] [FiniteDimensional ℝ VG]
  [NormedAddCommGroup VH] [NormedSpace ℝ VH] [FiniteDimensional ℝ VH]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace VH H]
  [LieGroup 𝓘(ℝ, VH) ∞ H] [CompactSpace H] [T2Space H]
  [MeasurableSpace H] [BorelSpace H]
  {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [MulAction G M] [ContinuousSMul G M]
  [MulAction H N] [ContinuousSMul H N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ H N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- The original two support classes pulled back to the actual cotangent of the product. -/
def equivariantCotangentKZeroExternalProduct :
    letI : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
    letI : LieGroup 𝓘(ℝ, VG × VH) ∞ (G × H) := by
      rw [modelWithCornersSelf_prod]
      exact Prod.instLieGroup
        (I := 𝓘(ℝ, VG)) (I' := 𝓘(ℝ, VH))
    letI : MulAction (G × H) M :=
      MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) M :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) N :=
      MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) N :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := contMDiffSMul_euclideanProduct (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n))).prod 𝓘(ℝ, CotangentModel (n))) ∞
    letI := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    letI := contMDiffSMul_smoothCotangent (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    letI : ContinuousSMul H (CotangentTotalSpace (n := m) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m))).prod 𝓘(ℝ, CotangentModel (m))) ∞
    letI := smoothCotangentMulAction (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
    letI := contMDiffSMul_smoothCotangent (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
    letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := n + m) (M := M × N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG × VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))).prod 𝓘(ℝ, CotangentModel (n + m))) ∞
    EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) →+
      EquivariantSupportTripleKZero H (CotangentTotalSpace (n := m) (M := N)) →+
        EquivariantSupportTripleKZero (G × H)
          (CotangentTotalSpace (n := n + m) (M := M × N)) := by
  letI : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
  letI : LieGroup 𝓘(ℝ, VG × VH) ∞ (G × H) := by
    rw [modelWithCornersSelf_prod]
    exact Prod.instLieGroup
      (I := 𝓘(ℝ, VG)) (I' := 𝓘(ℝ, VH))
  letI : MulAction (G × H) M :=
    MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
  letI : ContinuousSMul (G × H) M :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  letI : MulAction (G × H) N :=
    MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
  letI : ContinuousSMul (G × H) N :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  letI := euclideanProductChartedSpace (n := n) (m := m) M N
  letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  letI := contMDiffSMul_euclideanProduct (n := n) (m := m)
    (VG := VG) (VH := VH) (G := G) (H := H) M N
  letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n))).prod 𝓘(ℝ, CotangentModel (n))) ∞
  letI := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
  letI := contMDiffSMul_smoothCotangent (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
  letI : ContinuousSMul H (CotangentTotalSpace (n := m) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m))).prod 𝓘(ℝ, CotangentModel (m))) ∞
  letI := smoothCotangentMulAction (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
  letI := contMDiffSMul_smoothCotangent (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
  letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := n + m) (M := M × N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG × VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))).prod 𝓘(ℝ, CotangentModel (n + m))) ∞
  letI : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
  letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  letI : MulAction (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
  letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  -- Keep the original independent-group product and its original compact support.
  let μ := equivariantSupportKZeroDifferentGroupExternalProduct
    (G := G) (H := H)
    (X := CotangentTotalSpace (n := n) (M := M))
    (Y := CotangentTotalSpace (n := m) (M := N))
  let c := cotangentProductHomeomorph (n := n) (m := m) M N
  -- This is proper pullback through the specified inverse-dual and splitting map.
  let p := equivariantSupportTripleKZeroPullback ⟨c, c.continuous⟩
    (cotangentProductHomeomorph_equivariant (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N) c.isProperMap
  exact
    { toFun := fun u ↦ p.comp (μ u)
      map_zero' := by
        apply AddMonoidHom.ext
        intro v
        simp
      map_add' := by
        intro u w
        apply AddMonoidHom.ext
        intro v
        simp }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
-- Retain both finite partitions and every original local action through bilinear assembly.
/-- The full representation-valued analytic index respects independent-group external products. -/
theorem equivariantAnalyticIndexMap_externalProduct :
    letI : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
    letI : LieGroup 𝓘(ℝ, VG × VH) ∞ (G × H) := by
      rw [modelWithCornersSelf_prod]
      exact Prod.instLieGroup
        (I := 𝓘(ℝ, VG)) (I' := 𝓘(ℝ, VH))
    letI : MulAction (G × H) M :=
      MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) M :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) N :=
      MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) N :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := contMDiffSMul_euclideanProduct (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n))).prod 𝓘(ℝ, CotangentModel (n))) ∞
    letI := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    letI := contMDiffSMul_smoothCotangent (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    letI : ContinuousSMul H (CotangentTotalSpace (n := m) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m))).prod 𝓘(ℝ, CotangentModel (m))) ∞
    letI := smoothCotangentMulAction (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
    letI := contMDiffSMul_smoothCotangent (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
    letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := n + m) (M := M × N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG × VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))).prod 𝓘(ℝ, CotangentModel (n + m))) ∞
    letI : MeasurableSpace (G × H) := borel (G × H)
    letI : BorelSpace (G × H) := ⟨rfl⟩
    ∀ (u : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)))
      (v : EquivariantSupportTripleKZero H (CotangentTotalSpace (n := m) (M := N))),
      equivariantAnalyticIndexMap (n := n + m) (VG := VG × VH) (G := G × H) (M := M × N)
          (equivariantCotangentKZeroExternalProduct (n := n) (m := m)
            (VG := VG) (VH := VH) u v) =
        representationExternalProduct
          (equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) (M := M) u)
          (equivariantAnalyticIndexMap (n := m) (VG := VH) (G := H) (M := N) v) := by
  classical
  let : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
  let : LieGroup 𝓘(ℝ, VG × VH) ∞ (G × H) := by
    rw [modelWithCornersSelf_prod]
    exact Prod.instLieGroup
      (I := 𝓘(ℝ, VG)) (I' := 𝓘(ℝ, VH))
  let : MulAction (G × H) M :=
    MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) M :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) N :=
    MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) N :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := contMDiffSMul_euclideanProduct (n := n) (m := m)
    (VG := VG) (VH := VH) (G := G) (H := H) M N
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n))).prod 𝓘(ℝ, CotangentModel (n))) ∞
  let := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
  let := contMDiffSMul_smoothCotangent (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
  let : ContinuousSMul H (CotangentTotalSpace (n := m) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m))).prod 𝓘(ℝ, CotangentModel (m))) ∞
  let := smoothCotangentMulAction (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
  let := contMDiffSMul_smoothCotangent (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
  let : ContinuousSMul (G × H) (CotangentTotalSpace (n := n + m) (M := M × N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG × VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))).prod 𝓘(ℝ, CotangentModel (n + m))) ∞
  let : MeasurableSpace (G × H) := borel (G × H)
  let : BorelSpace (G × H) := ⟨rfl⟩
  intro u v
  -- Choose the actual symbol families; all later extensions use these same pieces.
  obtain ⟨a, ha⟩ := exists_equivariantClopenSymbolFamily (n := n) (VG := VG) u
  obtain ⟨b, hb⟩ := exists_equivariantClopenSymbolFamily (n := m) (VG := VH) v
  let P := a.partition
  let Q := b.partition
  let := P.mulAction
  let := P.continuousSMul
  let := P.contMDiffSMul (n := n) (VG := VG)
  let := P.compactSpace
  let : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := P.piece i)) :=
    fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := P.piece i) 𝓘(ℝ, VG)
  let : ∀ i, ContMDiffSMul 𝓘(ℝ, VG)
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := P.piece i)) :=
    fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := P.piece i) 𝓘(ℝ, VG)
  let : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := P.piece i)) :=
    fun _ ↦ ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := Q.mulAction
  let := Q.continuousSMul
  let := Q.contMDiffSMul (n := m) (VG := VH)
  let := Q.compactSpace
  let : ∀ i, MulAction H (CotangentTotalSpace (n := m) (M := Q.piece i)) :=
    fun i ↦ smoothCotangentMulAction (n := m) (G := H) (M := Q.piece i) 𝓘(ℝ, VH)
  let : ∀ i, ContMDiffSMul 𝓘(ℝ, VH)
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞ H
      (CotangentTotalSpace (n := m) (M := Q.piece i)) :=
    fun i ↦ contMDiffSMul_smoothCotangent (n := m) (G := H) (M := Q.piece i) 𝓘(ℝ, VH)
  let : ∀ i, ContinuousSMul H (CotangentTotalSpace (n := m) (M := Q.piece i)) :=
    fun _ ↦ ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞
  let ΦP := equivariantCotangentClopenEquiv (n := n) 𝓘(ℝ, VG) P.piece P.isClosed
    P.equivariant P.disjoint P.cover
  let extensionP (i : Fin P.size) :
      EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := P.piece i)) →+
        EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) :=
    equivariantSupportTripleKZeroOpenPushforward (G := G)
    ⟨cotangentOpenInclusion (P.piece i),
      (isOpenEmbedding_cotangentOpenInclusion (P.piece i)).continuous⟩
    (isOpenEmbedding_cotangentOpenInclusion (P.piece i))
    (cotangentOpenInclusion_smul 𝓘(ℝ, VG) (P.piece i) (P.equivariant i))
  have hrecP : a.kClass = ∑ i, extensionP i (a.symbols i).kClass := by
    have hrec := equivariantCotangentKZero_eq_sum_clopen_openPushforward P a.kClass
    change a.kClass = ∑ i, extensionP i
      (ΦP (ΦP.symm (fun j ↦ (a.symbols j).kClass)) i) at hrec
    rw [ΦP.apply_symm_apply] at hrec
    exact hrec
  have hindexP := equivariantAnalyticIndexMap_clopen
    (n := n) (M := M) (VG := VG) (G := G)
    P.size P.piece P.isClosed P.disjoint P.cover P.mulAction P.continuousSMul
    (P.contMDiffSMul (n := n) (VG := VG)) P.equivariant P.compactSpace
    (fun i ↦ (a.symbols i).source) (fun i ↦ (a.symbols i).target)
    (fun i ↦ (a.symbols i).sourceAction) (fun i ↦ (a.symbols i).targetAction)
    (fun i ↦ (a.symbols i).source_smooth) (fun i ↦ (a.symbols i).target_smooth)
    (fun i ↦ (a.symbols i).symbol) (fun i ↦ (a.symbols i).elliptic)
    (fun i ↦ (a.symbols i).equivariant)
  change equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) a.kClass =
    ∑ i, (a.symbols i).index at hindexP
  let ΦQ := equivariantCotangentClopenEquiv (n := m) 𝓘(ℝ, VH) Q.piece Q.isClosed
    Q.equivariant Q.disjoint Q.cover
  let extensionQ (i : Fin Q.size) :
      EquivariantSupportTripleKZero H (CotangentTotalSpace (n := m) (M := Q.piece i)) →+
        EquivariantSupportTripleKZero H (CotangentTotalSpace (n := m) (M := N)) :=
    equivariantSupportTripleKZeroOpenPushforward (G := H)
    ⟨cotangentOpenInclusion (Q.piece i),
      (isOpenEmbedding_cotangentOpenInclusion (Q.piece i)).continuous⟩
    (isOpenEmbedding_cotangentOpenInclusion (Q.piece i))
    (cotangentOpenInclusion_smul 𝓘(ℝ, VH) (Q.piece i) (Q.equivariant i))
  have hrecQ : b.kClass = ∑ i, extensionQ i (b.symbols i).kClass := by
    have hrec := equivariantCotangentKZero_eq_sum_clopen_openPushforward Q b.kClass
    change b.kClass = ∑ i, extensionQ i
      (ΦQ (ΦQ.symm (fun j ↦ (b.symbols j).kClass)) i) at hrec
    rw [ΦQ.apply_symm_apply] at hrec
    exact hrec
  have hindexQ := equivariantAnalyticIndexMap_clopen
    (n := m) (M := N) (VG := VH) (G := H)
    Q.size Q.piece Q.isClosed Q.disjoint Q.cover Q.mulAction Q.continuousSMul
    (Q.contMDiffSMul (n := m) (VG := VH)) Q.equivariant Q.compactSpace
    (fun i ↦ (b.symbols i).source) (fun i ↦ (b.symbols i).target)
    (fun i ↦ (b.symbols i).sourceAction) (fun i ↦ (b.symbols i).targetAction)
    (fun i ↦ (b.symbols i).source_smooth) (fun i ↦ (b.symbols i).target_smooth)
    (fun i ↦ (b.symbols i).symbol) (fun i ↦ (b.symbols i).elliptic)
    (fun i ↦ (b.symbols i).equivariant)
  change equivariantAnalyticIndexMap (n := m) (VG := VH) (G := H) b.kClass =
    ∑ i, (b.symbols i).index at hindexQ
  -- Additivity in both original support classes reduces the formula to each pair of pieces.
  rw [← ha, ← hb, hindexP, hindexQ, hrecP, hrecQ]
  simp only [map_sum, AddMonoidHom.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  -- Clopen excision and the fixed-symbol formula keep precisely these actions and symbols.
  exact (equivariantAnalyticIndexMap_clopen_product (VG := VG) (VH := VH)
    (P.piece i) (Q.piece j) (P.equivariant i) (Q.equivariant j)
    (a.symbols i).kClass (b.symbols j).kClass).trans
      (equivariantAnalyticIndexMap_externalProduct_symbol (a.symbols i) (b.symbols j))

end AtiyahSinger
