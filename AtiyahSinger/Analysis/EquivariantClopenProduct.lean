/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantCompactSourceExcision
public import AtiyahSinger.Geometry.OpenProductCoordinates
public import AtiyahSinger.Topology.EquivariantDifferentGroupProduct
public import AtiyahSinger.Topology.EquivariantDifferentGroupOpen
public import AtiyahSinger.Topology.EquivariantOpenHomeomorph

/-!
# The index of a product supported on two clopen pieces

Public module ID: M0483.

The actual open product diffeomorphism and its inverse-dual cotangent map
commute with the specified cotangent splitting. Open extension naturality of
the independent-group support product therefore identifies the same class
on the ambient product. Compact-source excision preserves its full index.
This is the clopen assembly step for the analytic external-product formula;
no fixed rank, nonempty base or positive dimension is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096

variable {VG VH G H : Type*}
  [NormedAddCommGroup VG] [NormedSpace ℝ VG] [FiniteDimensional ℝ VG]
  [NormedAddCommGroup VH] [NormedSpace ℝ VH] [FiniteDimensional ℝ VH]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace VH H]
  [LieGroup 𝓘(ℝ, VH) ∞ H] [CompactSpace H] [T2Space H]
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2400000 in
-- Keep both product atlases and their native action dictionaries in the same cotangent square.
/-- Two compact open pieces retain the full index of their original cotangent product. -/
theorem equivariantAnalyticIndexMap_clopen_product
    (U : Opens M) (V : Opens N)
    [MulAction G U] [ContinuousSMul G U]
    [ContMDiffSMul 𝓘(ℝ, VG) (𝓡 n) ∞ G U]
    [MulAction H V] [ContinuousSMul H V]
    [ContMDiffSMul 𝓘(ℝ, VH) (𝓡 m) ∞ H V]
    [CompactSpace U] [CompactSpace V]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (hV : ∀ (g : H) (x : V), ((g • x : V) : N) = g • x.val) :
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
    letI : MulAction (G × H) U :=
      MulAction.compHom U (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) U :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) V :=
      MulAction.compHom V (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) V :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI := euclideanProductChartedSpace (n := n) (m := m) U V
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) U V
    letI := contMDiffSMul_euclideanProduct (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) U V
    letI := smoothCotangentMulAction (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := U)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n))).prod 𝓘(ℝ, CotangentModel (n))) ∞
    letI := smoothCotangentMulAction (n := m) (G := H) (M := V) 𝓘(ℝ, VH)
    letI := contMDiffSMul_smoothCotangent (n := m) (G := H) (M := V) 𝓘(ℝ, VH)
    letI : ContinuousSMul H (CotangentTotalSpace (n := m) (M := V)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m))).prod 𝓘(ℝ, CotangentModel (m))) ∞
    letI := smoothCotangentMulAction (n := n + m) (G := G × H) (M := U × V) 𝓘(ℝ, VG × VH)
    letI := contMDiffSMul_smoothCotangent (n := n + m) (G := G × H) (M := U × V) 𝓘(ℝ, VG × VH)
    letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := n + m) (M := U × V)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG × VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))).prod 𝓘(ℝ, CotangentModel (n + m))) ∞
    letI : MulAction (G × H) (CotangentTotalSpace (n := n) (M := U)) :=
      MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := n) (M := U)) :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) (CotangentTotalSpace (n := m) (M := V)) :=
      MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := m) (M := V)) :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI : MeasurableSpace (G × H) := borel (G × H)
    letI : BorelSpace (G × H) := ⟨rfl⟩
    ∀ (a : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := U)))
      (b : EquivariantSupportTripleKZero H (CotangentTotalSpace (n := m) (M := V))),
      equivariantAnalyticIndexMap (n := n + m) (VG := VG × VH) (G := G × H) (M := M × N)
        ((equivariantSupportTripleKZeroPullback
        ⟨cotangentProductHomeomorph (n := n) (m := m) M N,
          (cotangentProductHomeomorph (n := n) (m := m) M N).continuous⟩
        (cotangentProductHomeomorph_equivariant (n := n) (m := m)
          (VG := VG) (VH := VH) (G := G) (H := H) M N)
        (cotangentProductHomeomorph (n := n) (m := m) M N).isProperMap
        (equivariantSupportKZeroDifferentGroupExternalProduct
          (equivariantSupportTripleKZeroOpenPushforward
            ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
            (isOpenEmbedding_cotangentOpenInclusion U)
            (cotangentOpenInclusion_smul 𝓘(ℝ, VG) U hU) a)
          (equivariantSupportTripleKZeroOpenPushforward
            ⟨cotangentOpenInclusion V, (isOpenEmbedding_cotangentOpenInclusion V).continuous⟩
            (isOpenEmbedding_cotangentOpenInclusion V)
            (cotangentOpenInclusion_smul 𝓘(ℝ, VH) V hV) b)))) =
        equivariantAnalyticIndexMap (n := n + m) (VG := VG × VH) (G := G × H) (M := U × V)
          ((equivariantSupportTripleKZeroPullback
        ⟨cotangentProductHomeomorph (n := n) (m := m) U V,
          (cotangentProductHomeomorph (n := n) (m := m) U V).continuous⟩
        (cotangentProductHomeomorph_equivariant (n := n) (m := m)
          (VG := VG) (VH := VH) (G := G) (H := H) U V)
        (cotangentProductHomeomorph (n := n) (m := m) U V).isProperMap
        (equivariantSupportKZeroDifferentGroupExternalProduct
          a b))) := by
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
  let : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let : MulAction (G × H) U :=
    MulAction.compHom U (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) U :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) V :=
    MulAction.compHom V (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) V :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let := euclideanProductChartedSpace (n := n) (m := m) U V
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) U V
  let := contMDiffSMul_euclideanProduct (n := n) (m := m)
    (VG := VG) (VH := VH) (G := G) (H := H) U V
  let := smoothCotangentMulAction (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := U)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n))).prod 𝓘(ℝ, CotangentModel (n))) ∞
  let := smoothCotangentMulAction (n := m) (G := H) (M := V) 𝓘(ℝ, VH)
  let := contMDiffSMul_smoothCotangent (n := m) (G := H) (M := V) 𝓘(ℝ, VH)
  let : ContinuousSMul H (CotangentTotalSpace (n := m) (M := V)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m))).prod 𝓘(ℝ, CotangentModel (m))) ∞
  let := smoothCotangentMulAction (n := n + m) (G := G × H) (M := U × V) 𝓘(ℝ, VG × VH)
  let := contMDiffSMul_smoothCotangent (n := n + m) (G := G × H) (M := U × V) 𝓘(ℝ, VG × VH)
  let : ContinuousSMul (G × H) (CotangentTotalSpace (n := n + m) (M := U × V)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG × VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))).prod 𝓘(ℝ, CotangentModel (n + m))) ∞
  let : MulAction (G × H) (CotangentTotalSpace (n := n) (M := U)) :=
    MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) (CotangentTotalSpace (n := n) (M := U)) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) (CotangentTotalSpace (n := m) (M := V)) :=
    MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) (CotangentTotalSpace (n := m) (M := V)) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let : MeasurableSpace (G × H) := borel (G × H)
  let : BorelSpace (G × H) := ⟨rfl⟩
  intro a b
  let : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N)) := Prod.mulAction
  let : SMul (G × H) (CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N)) :=
    (Prod.mulAction : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N))).toSMul
  let : MulAction (G × H) (CotangentTotalSpace (n := n) (M := U) ×
      CotangentTotalSpace (n := m) (M := V)) := Prod.mulAction
  let : SMul (G × H) (CotangentTotalSpace (n := n) (M := U) ×
      CotangentTotalSpace (n := m) (M := V)) :=
    (Prod.mulAction : MulAction (G × H) (CotangentTotalSpace (n := n) (M := U) ×
      CotangentTotalSpace (n := m) (M := V))).toSMul
  let W : Opens (M × N) := ⟨(U : Set M) ×ˢ (V : Set N), U.isOpen.prod V.isOpen⟩
  let f := openProductDiffeomorph (n := n) (m := m) U V
  let c : CotangentTotalSpace (n := n + m) (M := M × N) ≃ₜ
      (CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N)) :=
    cotangentProductHomeomorph (n := n) (m := m) M N
  let d : CotangentTotalSpace (n := n + m) (M := U × V) ≃ₜ
      (CotangentTotalSpace (n := n) (M := U) ×
      CotangentTotalSpace (n := m) (M := V)) :=
    cotangentProductHomeomorph (n := n) (m := m) U V
  have hc := cotangentProductHomeomorph_equivariant
    (n := n) (m := m) (VG := VG) (VH := VH) (G := G) (H := H) M N
  have hd := cotangentProductHomeomorph_equivariant
    (n := n) (m := m) (VG := VG) (VH := VH) (G := G) (H := H) U V
  have hci (g : G × H) (z : CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N)) :
      c.symm (g • z : CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N)) = g • c.symm z := by
    apply c.injective
    rw [c.apply_symm_apply, hc, c.apply_symm_apply]
  have hdi (g : G × H) (z : CotangentTotalSpace (n := n) (M := U) ×
      CotangentTotalSpace (n := m) (M := V)) :
      d.symm (g • z : CotangentTotalSpace (n := n) (M := U) ×
      CotangentTotalSpace (n := m) (M := V)) = g • d.symm z := by
    apply d.injective
    rw [d.apply_symm_apply, hd, d.apply_symm_apply]
  let jU : C(CotangentTotalSpace (n := n) (M := U),
      CotangentTotalSpace (n := n) (M := M)) :=
    ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
  let jV : C(CotangentTotalSpace (n := m) (M := V),
      CotangentTotalSpace (n := m) (M := N)) :=
    ⟨cotangentOpenInclusion V, (isOpenEmbedding_cotangentOpenInclusion V).continuous⟩
  have hjU := isOpenEmbedding_cotangentOpenInclusion (n := n) U
  have hjV := isOpenEmbedding_cotangentOpenInclusion (n := m) V
  have heU := cotangentOpenInclusion_smul (n := n) 𝓘(ℝ, VG) U hU
  have heV := cotangentOpenInclusion_smul (n := m) 𝓘(ℝ, VH) V hV
  let k := jU.prodMap jV
  have hk : IsOpenEmbedding k := hjU.prodMap hjV
  have hke (g : G × H) (z : CotangentTotalSpace (n := n) (M := U) ×
      CotangentTotalSpace (n := m) (M := V)) : k (g • z) = g • k z :=
    Prod.ext (heU g.1 z.1) (heV g.2 z.2)
  let j : C(CotangentTotalSpace (n := n + m) (M := U × V),
      CotangentTotalSpace (n := n + m) (M := M × N)) :=
    ⟨fun z ↦ cotangentOpenInclusion W (cotangentDiffeomorph f z),
      (isOpenEmbedding_cotangentOpenInclusion W).continuous.comp
        (cotangentDiffeomorph f).continuous⟩
  have hj : IsOpenEmbedding j :=
    (isOpenEmbedding_cotangentOpenInclusion W).comp (cotangentDiffeomorph f).isOpenEmbedding
  -- Compare the actual cotangent maps before invoking any support-class identity.
  have hsquare (z : CotangentTotalSpace (n := n + m) (M := U × V)) :
      c (j z) = k (d z) := cotangent_openProductDiffeomorph_split U V z
  have hje (g : G × H) (z : CotangentTotalSpace (n := n + m) (M := U × V)) :
      j (g • z) = g • j z := by
    apply c.injective
    rw [hsquare, hc, hsquare, hd, hke]
  let ci : C(CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N),
      CotangentTotalSpace (n := n + m) (M := M × N)) := ⟨c.symm, c.symm.continuous⟩
  let di : C(CotangentTotalSpace (n := n) (M := U) ×
      CotangentTotalSpace (n := m) (M := V),
      CotangentTotalSpace (n := n + m) (M := U × V)) := ⟨d.symm, d.symm.continuous⟩
  have hcomp : ci.comp k = j.comp di := by
    apply ContinuousMap.ext
    intro z
    apply c.injective
    change c (c.symm (k z)) = c (j (d.symm z))
    rw [c.apply_symm_apply, hsquare, d.apply_symm_apply]
  let w := equivariantSupportKZeroDifferentGroupExternalProduct a b
  have hclass : (equivariantSupportTripleKZeroPullback
        ⟨cotangentProductHomeomorph (n := n) (m := m) M N,
          (cotangentProductHomeomorph (n := n) (m := m) M N).continuous⟩
        (cotangentProductHomeomorph_equivariant (n := n) (m := m)
          (VG := VG) (VH := VH) (G := G) (H := H) M N)
        (cotangentProductHomeomorph (n := n) (m := m) M N).isProperMap
        (equivariantSupportKZeroDifferentGroupExternalProduct
          (equivariantSupportTripleKZeroOpenPushforward jU hjU heU a)
          (equivariantSupportTripleKZeroOpenPushforward jV hjV heV b))) =
      equivariantSupportTripleKZeroOpenPushforward j hj hje
        ((equivariantSupportTripleKZeroPullback
        ⟨cotangentProductHomeomorph (n := n) (m := m) U V,
          (cotangentProductHomeomorph (n := n) (m := m) U V).continuous⟩
        (cotangentProductHomeomorph_equivariant (n := n) (m := m)
          (VG := VG) (VH := VH) (G := G) (H := H) U V)
        (cotangentProductHomeomorph (n := n) (m := m) U V).isProperMap
        (equivariantSupportKZeroDifferentGroupExternalProduct
          a b))) := by
    -- Turn both proper pullbacks into extension along their actual inverse homeomorphisms.
    change equivariantSupportTripleKZeroPullback ⟨c, c.continuous⟩ hc c.isProperMap
      (equivariantSupportKZeroDifferentGroupExternalProduct
        (equivariantSupportTripleKZeroOpenPushforward jU hjU heU a)
        (equivariantSupportTripleKZeroOpenPushforward jV hjV heV b)) =
      equivariantSupportTripleKZeroOpenPushforward j hj hje
        (equivariantSupportTripleKZeroPullback ⟨d, d.continuous⟩ hd d.isProperMap w)
    rw [equivariantSupportTripleKZeroPullback_eq_openPushforward_symm c hc hci,
      equivariantSupportTripleKZeroPullback_eq_openPushforward_symm d hd hdi]
    rw [← equivariantSupportKZeroDifferentGroupExternalProduct_openPushforward
      jU hjU heU jV hjV heV a b]
    have hleft := DFunLike.congr_fun
      (equivariantSupportTripleKZeroOpenPushforward_functoriality.2 k hk hke
        ci c.symm.isOpenEmbedding hci) w
    have hright := DFunLike.congr_fun
      (equivariantSupportTripleKZeroOpenPushforward_functoriality.2
        di d.symm.isOpenEmbedding hdi j hj hje) w
    exact hleft.symm.trans (by
      simpa only [hcomp, AddMonoidHom.comp_apply, di] using hright)
  rw [hclass]
  -- Compact-source excision evaluates this same product class on its native open product.
  exact equivariantAnalyticIndexMap_compactSource_openPushforward
    (n := n + m) (VG := VG × VH) (G := G × H) W f
    (fun g x ↦ Prod.ext (hU g.1 x.1) (hV g.2 x.2)) hje
    ((equivariantSupportTripleKZeroPullback
        ⟨cotangentProductHomeomorph (n := n) (m := m) U V,
          (cotangentProductHomeomorph (n := n) (m := m) U V).continuous⟩
        (cotangentProductHomeomorph_equivariant (n := n) (m := m)
          (VG := VG) (VH := VH) (G := G) (H := H) U V)
        (cotangentProductHomeomorph (n := n) (m := m) U V).isProperMap
        (equivariantSupportKZeroDifferentGroupExternalProduct
          a b)))

end AtiyahSinger
