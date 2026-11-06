/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantHomogeneousSymbolProduct

/-!
# The original external product on elliptic symbol data

Public module ID: M0601.

The same native graded graph, its sufficiently small four-block cutoff, and
that cutoff's actual averaged principal symbol give the product formula.
The support comparison uses the original Hermitian exterior of the same
factor symbols and the canonical cotangent splitting.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 50
set_option maxRecDepth 8192

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 12000000 in
-- The original degree-zero representatives are shifted by invertible equivariant radial operators.
/-- The two original homogeneous symbol classes have the external product of their full indices. -/
theorem equivariantAnalyticIndexMap_externalProduct_symbol
    (a : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G))
    (b : EquivariantEllipticSymbolData (n := m) (M := N) (VG := VH) (G := H)) :
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
    equivariantAnalyticIndexMap (n := n + m) (VG := VG × VH) (G := G × H) (M := M × N)
        (letI : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
           MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
         letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
           MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
         letI : MulAction (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
           MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
         letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
           MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
         let c := cotangentProductHomeomorph (n := n) (m := m) M N
         equivariantSupportTripleKZeroPullback ⟨c, c.continuous⟩
           (cotangentProductHomeomorph_equivariant (n := n) (m := m)
             (VG := VG) (VH := VH) (G := G) (H := H) M N) c.isProperMap
           (equivariantSupportKZeroDifferentGroupExternalProduct
             (G := G) (H := H)
             (X := CotangentTotalSpace (n := n) (M := M))
             (Y := CotangentTotalSpace (n := m) (M := N))
             a.kClass
             b.kClass)) = representationExternalProduct a.index b.index := by
  as_aux_lemma =>
    classical
    -- Each first-order factor retains its original class and full section representation index.
    obtain ⟨μ, hμ, hμInv⟩ := exists_invariant_smoothPositiveMeasure G 𝓘(ℝ, VG)
      (n := n) (M := M)
    let := hμ
    obtain ⟨hP₀, hhP₀⟩ := exists_invariant_smoothHermitianMetric 𝓘(ℝ, VG)
      a.sourceAction a.source_smooth
    obtain ⟨hP₁, hhP₁⟩ := exists_invariant_smoothHermitianMetric 𝓘(ℝ, VG)
      a.targetAction a.target_smooth
    obtain ⟨gP, hgP⟩ := exists_invariant_smoothCotangentMetric
      (G := G) (n := n) (M := M) 𝓘(ℝ, VG)
    have gPInv (z : G) (x : M) (ξ : CotangentFiber (n := n) x) :
        gP.length (z • x) (cotangentDiffeomorphMap (Diffeomorph.smul (M := M)
          𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ z) ⟨x, ξ⟩).snd = gP.length x ξ :=
      congrArg Real.sqrt (hgP z x ξ ξ)
    obtain ⟨CP⟩ := nonempty_quantizationPresentation
      (n := n) (r := a.source.rank) (q := a.target.rank)
      (E := a.source.Fiber) (F := a.target.Fiber)
    let pP := CP.regularizedSymbol 0 a.symbol.val a.symbol.property.1 a.symbol.property.2
    have hFixedP (z : G) : equivariantPrincipalSymbolRepresentation
        𝓘(ℝ, VG) a.sourceAction a.targetAction a.source_smooth a.target_smooth 0 z
          (globalPrincipalSymbolClass a.source.Fiber a.target.Fiber 0 pP) =
            globalPrincipalSymbolClass a.source.Fiber a.target.Fiber 0 pP :=
      (CP.equivariant_regularizedSymbol_class_eq_iff 𝓘(ℝ, VG)
        a.sourceAction a.targetAction a.source_smooth a.target_smooth
        CP 0 a.symbol a.symbol z).mpr (a.equivariant z)
    obtain ⟨P₀, hP₀g, hP₀principal⟩ :=
      PseudodifferentialOperator.exists_equivariant_principalSymbol (μ := μ)
        𝓘(ℝ, VG) a.sourceAction a.targetAction a.source_smooth a.target_smooth 0
        (globalPrincipalSymbolClass a.source.Fiber a.target.Fiber 0 pP) hFixedP
    have hP₀ell : P₀.IsElliptic := (P₀.isElliptic_iff_homogeneous
      CP a.symbol hP₀principal).mpr a.elliptic
    have hP₀index := equivariantHomogeneousAnalyticIndex_eq_smooth 𝓘(ℝ, VG)
      a.sourceAction a.targetAction a.source_smooth a.target_smooth
      a.symbol a.elliptic a.equivariant μ CP P₀ hP₀g hP₀ell hP₀principal
    obtain ⟨P, aP, haP, haPEq, hPg, hPell, _UP, _hUP, _hUPEq,
        hPprincipal, _haPRadial, hPindex, hPclass⟩ :=
      P₀.exists_equivariant_orderShift_universe 𝓘(ℝ, VG) a.sourceAction a.targetAction
        a.source_smooth a.target_smooth hP₀ hhP₀ hμInv hP₀g gP gPInv
        CP a.symbol hP₀principal a.elliptic a.equivariant 1
    obtain ⟨ν, hν, hνInv⟩ := exists_invariant_smoothPositiveMeasure H 𝓘(ℝ, VH)
      (n := m) (M := N)
    let := hν
    obtain ⟨hQ₀, hhQ₀⟩ := exists_invariant_smoothHermitianMetric 𝓘(ℝ, VH)
      b.sourceAction b.source_smooth
    obtain ⟨hQ₁, hhQ₁⟩ := exists_invariant_smoothHermitianMetric 𝓘(ℝ, VH)
      b.targetAction b.target_smooth
    obtain ⟨gQ, hgQ⟩ := exists_invariant_smoothCotangentMetric
      (G := H) (n := m) (M := N) 𝓘(ℝ, VH)
    have gQInv (z : H) (x : N) (ξ : CotangentFiber (n := m) x) :
        gQ.length (z • x) (cotangentDiffeomorphMap (Diffeomorph.smul (M := N)
          𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ z) ⟨x, ξ⟩).snd = gQ.length x ξ :=
      congrArg Real.sqrt (hgQ z x ξ ξ)
    obtain ⟨CQ⟩ := nonempty_quantizationPresentation
      (n := m) (r := b.source.rank) (q := b.target.rank)
      (E := b.source.Fiber) (F := b.target.Fiber)
    let pQ := CQ.regularizedSymbol 0 b.symbol.val b.symbol.property.1 b.symbol.property.2
    have hFixedQ (z : H) : equivariantPrincipalSymbolRepresentation
        𝓘(ℝ, VH) b.sourceAction b.targetAction b.source_smooth b.target_smooth 0 z
          (globalPrincipalSymbolClass b.source.Fiber b.target.Fiber 0 pQ) =
            globalPrincipalSymbolClass b.source.Fiber b.target.Fiber 0 pQ :=
      (CQ.equivariant_regularizedSymbol_class_eq_iff 𝓘(ℝ, VH)
        b.sourceAction b.targetAction b.source_smooth b.target_smooth
        CQ 0 b.symbol b.symbol z).mpr (b.equivariant z)
    obtain ⟨Q₀, hQ₀g, hQ₀principal⟩ :=
      PseudodifferentialOperator.exists_equivariant_principalSymbol (μ := ν)
        𝓘(ℝ, VH) b.sourceAction b.targetAction b.source_smooth b.target_smooth 0
        (globalPrincipalSymbolClass b.source.Fiber b.target.Fiber 0 pQ) hFixedQ
    have hQ₀ell : Q₀.IsElliptic := (Q₀.isElliptic_iff_homogeneous
      CQ b.symbol hQ₀principal).mpr b.elliptic
    have hQ₀index := equivariantHomogeneousAnalyticIndex_eq_smooth 𝓘(ℝ, VH)
      b.sourceAction b.targetAction b.source_smooth b.target_smooth
      b.symbol b.elliptic b.equivariant ν CQ Q₀ hQ₀g hQ₀ell hQ₀principal
    obtain ⟨Q, aQ, haQ, haQEq, hQg, hQell, _UQ, _hUQ, _hUQEq,
        hQprincipal, _haQRadial, hQindex, hQclass⟩ :=
      Q₀.exists_equivariant_orderShift_universe 𝓘(ℝ, VH) b.sourceAction b.targetAction
        b.source_smooth b.target_smooth hQ₀ hhQ₀ hνInv hQ₀g gQ gQInv
        CQ b.symbol hQ₀principal b.elliptic b.equivariant 1
    have hProduct := equivariantAnalyticIndexMap_externalProduct_of_homogeneous
      a.source a.target b.source b.target
      a.sourceAction a.source_smooth a.targetAction a.target_smooth
      b.sourceAction b.source_smooth b.targetAction b.target_smooth
      hP₀ hhP₀ hP₁ hhP₁ hQ₀ hhQ₀ hQ₁ hhQ₁
      μ ν hμInv hνInv P Q hPg hQg CP CQ aP aQ haP haQ haPEq haQEq hPprincipal hQprincipal
    rw [hPclass, hQclass] at hProduct
    -- Transfer the two full index equalities only after the product has been computed.
    have hIndices := congrArg₂ (fun x y ↦ representationExternalProduct x y)
      (hPindex.trans hP₀index.symm) (hQindex.trans hQ₀index.symm)
    exact hProduct.trans hIndices

end AtiyahSinger
