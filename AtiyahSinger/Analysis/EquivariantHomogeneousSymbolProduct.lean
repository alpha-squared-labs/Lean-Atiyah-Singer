/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantEllipticSymbolData
public import AtiyahSinger.Analysis.EquivariantFullSymbolAverage
public import AtiyahSinger.Analysis.EquivariantFullSymbolCovariance
public import AtiyahSinger.Analysis.EquivariantGradedGraphCutoffIndex
public import AtiyahSinger.Analysis.EquivariantNativeHermitianSupport
public import AtiyahSinger.Analysis.EquivariantNativeTensorIndex
public import AtiyahSinger.Analysis.EquivariantSmoothIndexOrder
public import AtiyahSinger.Analysis.GradedBundleOperator
public import AtiyahSinger.Analysis.GradedCutoffAverageKClass
public import AtiyahSinger.Analysis.GradedProductCutoffAveragePrincipal
public import AtiyahSinger.Analysis.GradedProductCutoffPrincipal
public import AtiyahSinger.Analysis.GradedTensorCutoffApproximation
public import AtiyahSinger.Geometry.CotangentProduct
public import AtiyahSinger.Geometry.EquivariantNativeSum
public import AtiyahSinger.Topology.EquivariantDifferentGroupProduct

/-!
# The original external product on actual homogeneous realizations

Public module ID: M0525.

The same native graded graph, its sufficiently small four-block cutoff, and
that cutoff's actual averaged principal symbol give the product formula.
The support comparison uses the original Hermitian exterior of the same
factor symbols and the canonical cotangent splitting.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

universe u

private theorem fin_cases_one {α : Fin 2 → Sort u} (a : α 0)
    (b : (i : Fin 1) → α i.succ) : Fin.cases (motive := α) a b 1 = b 0 := rfl

private theorem prod_group_toMonoid {G H : Type*} [Group G] [Group H] :
    (@Prod.instGroup G H inferInstance inferInstance).toMonoid =
      @Prod.instMonoid G H inferInstance inferInstance := rfl

private theorem prod_group_toMulOneClass {G H : Type*} [Group G] [Group H] :
    (@Prod.instGroup G H inferInstance inferInstance).toMulOneClass =
      @Prod.instMulOneClass G H inferInstance inferInstance := rfl

private theorem prod_monoid_toMulOneClass {G H : Type*} [Monoid G] [Monoid H] :
    (@Prod.instMonoid G H inferInstance inferInstance).toMulOneClass =
      @Prod.instMulOneClass G H inferInstance inferInstance := rfl

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

variable (E₀ E₁ : SmoothFiniteComplexBundle (n := n) M)
  (F₀ F₁ : SmoothFiniteComplexBundle (n := m) N)
  (σ₀ : letI := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    EquivariantStructure G E₀.Fiber)
  (hσ₀ : σ₀.IsSmooth (n := n) (r := E₀.rank) 𝓘(ℝ, VG))
  (σ₁ : letI := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    EquivariantStructure G E₁.Fiber)
  (hσ₁ : σ₁.IsSmooth (n := n) (r := E₁.rank) 𝓘(ℝ, VG))
  (τ₀ : letI := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    EquivariantStructure H F₀.Fiber)
  (hτ₀ : τ₀.IsSmooth (n := m) (r := F₀.rank) 𝓘(ℝ, VH))
  (τ₁ : letI := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    EquivariantStructure H F₁.Fiber)
  (hτ₁ : τ₁.IsSmooth (n := m) (r := F₁.rank) 𝓘(ℝ, VH))
  (h₀ : SmoothHermitianMetric (n := n) (r := E₀.rank) E₀.Fiber)
  (hh₀Invariant : letI := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    ∀ (a : G) (x : M) (u v : E₀.Fiber x),
      h₀.pairing (a • x) (σ₀.linearMap a x u) (σ₀.linearMap a x v) =
        h₀.pairing x u v)
  (h₁ : SmoothHermitianMetric (n := n) (r := E₁.rank) E₁.Fiber)
  (hh₁Invariant : letI := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    ∀ (a : G) (x : M) (u v : E₁.Fiber x),
      h₁.pairing (a • x) (σ₁.linearMap a x u) (σ₁.linearMap a x v) =
        h₁.pairing x u v)
  (k₀ : SmoothHermitianMetric (n := m) (r := F₀.rank) F₀.Fiber)
  (hk₀Invariant : letI := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    ∀ (a : H) (x : N) (u v : F₀.Fiber x),
      k₀.pairing (a • x) (τ₀.linearMap a x u) (τ₀.linearMap a x v) =
        k₀.pairing x u v)
  (k₁ : SmoothHermitianMetric (n := m) (r := F₁.rank) F₁.Fiber)
  (hk₁Invariant : letI := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    ∀ (a : H) (x : N) (u v : F₁.Fiber x),
      k₁.pairing (a • x) (τ₁.linearMap a x u) (τ₁.linearMap a x v) =
        k₁.pairing x u v)
  (μ : MeasureTheory.Measure M) (ν : MeasureTheory.Measure N)
  [IsSmoothPositiveMeasure (n := n) μ] [IsSmoothPositiveMeasure (n := m) ν]
  (hμInvariant : ∀ a : G, MeasureTheory.Measure.map (fun x : M ↦ a • x) μ = μ)
  (hνInvariant : ∀ a : H, MeasureTheory.Measure.map (fun x : N ↦ a • x) ν = ν)
  (P : PseudodifferentialOperator (n := n) (r := E₀.rank) (q := E₁.rank)
    E₀.Fiber E₁.Fiber μ 1)
  (Q : PseudodifferentialOperator (n := m) (r := F₀.rank) (q := F₁.rank)
    F₀.Fiber F₁.Fiber ν 1)
  (hPg : P.IsEquivariant 𝓘(ℝ, VG) σ₀ σ₁ hσ₀ hσ₁)
  (hQg : Q.IsEquivariant 𝓘(ℝ, VH) τ₀ τ₁ hτ₀ hτ₁)

include h₀ hh₀Invariant h₁ hh₁Invariant k₀ hk₀Invariant k₁ hk₁Invariant
  hμInvariant hνInvariant

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 45000000 in
-- Retain the same factor operators, native sums, cutoff, and averaged principal symbol.
/-- Two actual homogeneous elliptic realizations satisfy the full original product formula. -/
theorem equivariantAnalyticIndexMap_externalProduct_of_homogeneous
    (C : QuantizationPresentation (n := n) (r := E₀.rank) (q := E₁.rank) E₀.Fiber E₁.Fiber)
    (D : QuantizationPresentation (n := m) (r := F₀.rank) (q := F₁.rank) F₀.Fiber F₁.Fiber)
    (p₀ : homogeneousGlobalSymbolSpace (n := n) (r := E₀.rank) (q := E₁.rank)
      E₀.Fiber E₁.Fiber 1)
    (q₀ : homogeneousGlobalSymbolSpace (n := m) (r := F₀.rank) (q := F₁.rank)
      F₀.Fiber F₁.Fiber 1)
    (hp₀ : IsEllipticGlobalSymbol E₀.Fiber E₁.Fiber p₀.val)
    (hq₀ : IsEllipticGlobalSymbol F₀.Fiber F₁.Fiber q₀.val)
    (hp₀Eq : ∀ (z : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₀ σ₁ z p₀.val x ξ = p₀.val x ξ)
    (hq₀Eq : ∀ (z : H) (x : N) (ξ : CotangentFiber (n := m) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₀ τ₁ z q₀.val x ξ = q₀.val x ξ)
    (hPprincipal : P.principalSymbol = globalPrincipalSymbolClass E₀.Fiber E₁.Fiber 1
      (C.regularizedSymbol 1 p₀.val p₀.property.1 p₀.property.2))
    (hQprincipal : Q.principalSymbol = globalPrincipalSymbolClass F₀.Fiber F₁.Fiber 1
      (D.regularizedSymbol 1 q₀.val q₀.property.1 q₀.property.2)) :
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
             (equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σ₀ σ₁ 1 p₀ hp₀ hp₀Eq)
             (equivariantHomogeneousSymbolKClass 𝓘(ℝ, VH) τ₀ τ₁ 1 q₀ hq₀ hq₀Eq))) =
      representationExternalProduct
        (P.smoothEquivariantAnalyticIndex 𝓘(ℝ, VG) σ₀ σ₁ hσ₀ hσ₁ hPg
          ((P.isElliptic_iff_homogeneous C p₀ hPprincipal).mpr hp₀))
        (Q.smoothEquivariantAnalyticIndex 𝓘(ℝ, VH) τ₀ τ₁ hτ₀ hτ₁ hQg
          ((Q.isElliptic_iff_homogeneous D q₀ hQprincipal).mpr hq₀)) := by
  as_aux_lemma =>
    classical
    let := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    -- Invariant metrics control the original homogeneous tails without changing either class.
    obtain ⟨g, hg⟩ := exists_invariant_smoothCotangentMetric (G := G) (n := n) (M := M) 𝓘(ℝ, VG)
    obtain ⟨k, hk⟩ := exists_invariant_smoothCotangentMetric (G := H) (n := m) (M := N) 𝓘(ℝ, VH)
    have gInv (a : G) (x : M) (ξ : CotangentFiber (n := n) x) :
        g.length (a • x) (cotangentDiffeomorphMap (Diffeomorph.smul (M := M)
          𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ a) ⟨x, ξ⟩).snd = g.length x ξ :=
      congrArg Real.sqrt (hg a x ξ ξ)
    have kInv (a : H) (x : N) (ξ : CotangentFiber (n := m) x) :
        k.length (a • x) (cotangentDiffeomorphMap (Diffeomorph.smul (M := N)
          𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ a) ⟨x, ξ⟩).snd = k.length x ξ :=
      congrArg Real.sqrt (hk a x ξ ξ)
    obtain ⟨p, hpFixed, ⟨R₁, hR₁, hpTail⟩, hpClass⟩ :=
      C.exists_invariant_fullSymbol_eq_at_infinity 𝓘(ℝ, VG) σ₀ σ₁ hσ₀ hσ₁ p₀ hp₀Eq g gInv
    obtain ⟨q, hqFixed, ⟨R₂, hR₂, hqTail⟩, hqClass⟩ :=
      D.exists_invariant_fullSymbol_eq_at_infinity 𝓘(ℝ, VH) τ₀ τ₁ hτ₀ hτ₁ q₀ hq₀Eq k kInv
    have hp := hPprincipal.trans hpClass.symm
    have hq := hQprincipal.trans hqClass.symm
    have hP : P.IsElliptic := (P.isElliptic_iff_homogeneous C p₀ hPprincipal).mpr hp₀
    have hQ : Q.IsElliptic := (Q.isElliptic_iff_homogeneous D q₀ hQprincipal).mpr hq₀
    have hpi := h₀.symbolAdjoint_fixed 𝓘(ℝ, VG) σ₀ σ₁ h₁ hh₀Invariant hh₁Invariant p.val hpFixed
    have hqi := k₀.symbolAdjoint_fixed 𝓘(ℝ, VH) τ₀ τ₁ k₁ hk₀Invariant hk₁Invariant q.val hqFixed
    -- The graph index and norm approximation share the four original metrics and both measures.
    have hNative := exists_gradedProductL2Operator_native_index
      E₀ E₁ F₀ F₁ σ₀ hσ₀ σ₁ hσ₁ τ₀ hτ₀ τ₁ hτ₁
      h₀ hh₀Invariant h₁ hh₁Invariant k₀ hk₀Invariant k₁ hk₁Invariant
      μ ν hμInvariant hνInvariant P Q hPg hQg hP hQ
    have hApprox := exists_gradedProductH1_cutoff_approximation h₀ h₁ k₀ k₁ P Q p q hp hq C D
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
    let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
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
    let := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₀.rank) E₀.Fiber F₀.Fiber
    let := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₀.rank) E₀.Fiber F₀.Fiber
    let := externalTensorTopology (r := E₀.rank) (s := F₀.rank) E₀.Fiber F₀.Fiber
    let := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    let := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    let A₀₀ : SmoothFiniteComplexBundle (n := n + m) (M × N) := {
      rank := E₀.rank * F₀.rank
      Fiber := externalTensorFiber E₀.Fiber F₀.Fiber }
    let θ₀₀ := externalTensorEquivariantStructure E₀.Fiber F₀.Fiber σ₀ τ₀
    let hθ₀₀ := externalTensorEquivariantStructure_isSmooth E₀.Fiber F₀.Fiber
      σ₀ τ₀ hσ₀ hτ₀
    let g₀₀ := externalTensorMetric h₀ k₀
    let hg₀₀ := externalTensorMetric_invariant E₀.Fiber F₀.Fiber
      σ₀ τ₀ h₀ k₀ hh₀Invariant hk₀Invariant
    let := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₁.rank) E₁.Fiber F₁.Fiber
    let := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₁.rank) E₁.Fiber F₁.Fiber
    let := externalTensorTopology (r := E₁.rank) (s := F₁.rank) E₁.Fiber F₁.Fiber
    let := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    let := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    let A₁₁ : SmoothFiniteComplexBundle (n := n + m) (M × N) := {
      rank := E₁.rank * F₁.rank
      Fiber := externalTensorFiber E₁.Fiber F₁.Fiber }
    let θ₁₁ := externalTensorEquivariantStructure E₁.Fiber F₁.Fiber σ₁ τ₁
    let hθ₁₁ := externalTensorEquivariantStructure_isSmooth E₁.Fiber F₁.Fiber
      σ₁ τ₁ hσ₁ hτ₁
    let g₁₁ := externalTensorMetric h₁ k₁
    let hg₁₁ := externalTensorMetric_invariant E₁.Fiber F₁.Fiber
      σ₁ τ₁ h₁ k₁ hh₁Invariant hk₁Invariant
    let := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₀.rank) E₁.Fiber F₀.Fiber
    let := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₀.rank) E₁.Fiber F₀.Fiber
    let := externalTensorTopology (r := E₁.rank) (s := F₀.rank) E₁.Fiber F₀.Fiber
    let := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    let := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    let A₁₀ : SmoothFiniteComplexBundle (n := n + m) (M × N) := {
      rank := E₁.rank * F₀.rank
      Fiber := externalTensorFiber E₁.Fiber F₀.Fiber }
    let θ₁₀ := externalTensorEquivariantStructure E₁.Fiber F₀.Fiber σ₁ τ₀
    let hθ₁₀ := externalTensorEquivariantStructure_isSmooth E₁.Fiber F₀.Fiber
      σ₁ τ₀ hσ₁ hτ₀
    let g₁₀ := externalTensorMetric h₁ k₀
    let hg₁₀ := externalTensorMetric_invariant E₁.Fiber F₀.Fiber
      σ₁ τ₀ h₁ k₀ hh₁Invariant hk₀Invariant
    let := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₁.rank) E₀.Fiber F₁.Fiber
    let := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₁.rank) E₀.Fiber F₁.Fiber
    let := externalTensorTopology (r := E₀.rank) (s := F₁.rank) E₀.Fiber F₁.Fiber
    let := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    let := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    let A₀₁ : SmoothFiniteComplexBundle (n := n + m) (M × N) := {
      rank := E₀.rank * F₁.rank
      Fiber := externalTensorFiber E₀.Fiber F₁.Fiber }
    let θ₀₁ := externalTensorEquivariantStructure E₀.Fiber F₁.Fiber σ₀ τ₁
    let hθ₀₁ := externalTensorEquivariantStructure_isSmooth E₀.Fiber F₁.Fiber
      σ₀ τ₁ hσ₀ hτ₁
    let g₀₁ := externalTensorMetric h₀ k₁
    let hg₀₁ := externalTensorMetric_invariant E₀.Fiber F₁.Fiber
      σ₀ τ₁ h₀ k₁ hh₀Invariant hk₁Invariant
    let := modelTopology (EuclideanSpace ℂ (Fin A₀₀.rank)) A₀₀.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin A₁₁.rank)) A₁₁.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin A₁₀.rank)) A₁₀.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin A₀₁.rank)) A₀₁.Fiber
    let := sumTopology (E := A₀₀.Fiber) (F := A₁₁.Fiber)
    let := sumTopology (E := A₁₀.Fiber) (F := A₀₁.Fiber)
    dsimp only at hNative hApprox
    obtain ⟨hμν, ρ, η, hρ, hη, hρapp, hηapp, hNative⟩ := hNative
    obtain ⟨S, _hSrank, σ, hσ, e, he, he₀, he₁⟩ :=
      exists_equivariant_native_smooth_sum 𝓘(ℝ, VG × VH) θ₀₀ θ₁₁ hθ₀₀ hθ₁₁
    obtain ⟨T, _hTrank, τ, hτ, f, hf, hf₀, hf₁⟩ :=
      exists_equivariant_native_smooth_sum 𝓘(ℝ, VG × VH) θ₁₀ θ₀₁ hθ₁₀ hθ₀₁
    let := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
    obtain ⟨hS, hSInv⟩ := exists_invariant_smoothHermitianMetric 𝓘(ℝ, VG × VH) σ hσ
    obtain ⟨hT, hTInv⟩ := exists_invariant_smoothHermitianMetric 𝓘(ℝ, VG × VH) τ hτ
    let A : Fin 2 → SmoothFiniteComplexBundle (n := n + m) (M × N) := ![A₀₀, A₁₁]
    let B : Fin 2 → SmoothFiniteComplexBundle (n := n + m) (M × N) := ![A₁₀, A₀₁]
    let R : (i : Fin 2) → SmoothBundlePresentation (n := n + m) (r := (A i).rank) (A i).Fiber :=
      fun i ↦ Classical.choice (nonempty_smoothBundlePresentation (E := (A i).Fiber))
    let L : (i : Fin 2) → SmoothBundlePresentation (n := n + m) (r := (B i).rank) (B i).Fiber :=
      fun i ↦ Classical.choice (nonempty_smoothBundlePresentation (E := (B i).Fiber))
    let AS : SmoothBundlePresentation (n := n + m) (r := S.rank) S.Fiber :=
      Classical.choice (nonempty_smoothBundlePresentation (E := S.Fiber))
    let AT : SmoothBundlePresentation (n := n + m) (r := T.rank) T.Fiber :=
      Classical.choice (nonempty_smoothBundlePresentation (E := T.Fiber))
    obtain ⟨γ, hγ, γI, hγI, hγv, Φ, hΦ, hFg, hFred, hIndex⟩ := hNative (R 0) (R 1)
    obtain ⟨cApprox, hcApprox, hApprox⟩ := hApprox (R 0) (R 1) (L 0) (L 1)
    let α : (i : Fin 2) →
        letI := modelTopology (EuclideanSpace ℂ (Fin (A i).rank)) (A i).Fiber
        EquivariantStructure (G × H) (A i).Fiber :=
      Fin.cases θ₀₀ (Fin.cases θ₁₁ (fun i ↦ Fin.elim0 i))
    let β : (i : Fin 2) →
        letI := modelTopology (EuclideanSpace ℂ (Fin (B i).rank)) (B i).Fiber
        EquivariantStructure (G × H) (B i).Fiber :=
      Fin.cases θ₁₀ (Fin.cases θ₀₁ (fun i ↦ Fin.elim0 i))
    have hα (i : Fin 2) : (α i).IsSmooth (n := n + m) (r := (A i).rank) 𝓘(ℝ, VG × VH) :=
      Fin.cases hθ₀₀ (Fin.cases hθ₁₁ (fun j ↦ Fin.elim0 j)) i
    have hβ (i : Fin 2) : (β i).IsSmooth (n := n + m) (r := (B i).rank) 𝓘(ℝ, VG × VH) :=
      Fin.cases hθ₁₀ (Fin.cases hθ₀₁ (fun j ↦ Fin.elim0 j)) i
    let hs : (i : Fin 2) → SmoothHermitianMetric (n := n + m) (r := (A i).rank) (A i).Fiber :=
      Fin.cases g₀₀ (Fin.cases g₁₁ (fun i ↦ Fin.elim0 i))
    let ht : (i : Fin 2) → SmoothHermitianMetric (n := n + m) (r := (B i).rank) (B i).Fiber :=
      Fin.cases g₁₀ (Fin.cases g₀₁ (fun i ↦ Fin.elim0 i))
    have hsInv (i : Fin 2) :
        letI := modelTopology (EuclideanSpace ℂ (Fin (A i).rank)) (A i).Fiber
        ∀ (a : G × H) (x : M × N) (u v : (A i).Fiber x),
          (hs i).pairing (a • x) ((α i).linearMap a x u) ((α i).linearMap a x v) =
            (hs i).pairing x u v :=
      Fin.cases hg₀₀ (Fin.cases hg₁₁ (fun j ↦ Fin.elim0 j)) i
    have htInv (i : Fin 2) :
        letI := modelTopology (EuclideanSpace ℂ (Fin (B i).rank)) (B i).Fiber
        ∀ (a : G × H) (x : M × N) (u v : (B i).Fiber x),
          (ht i).pairing (a • x) ((β i).linearMap a x u) ((β i).linearMap a x v) =
            (ht i).pairing x u v :=
      Fin.cases hg₁₀ (Fin.cases hg₀₁ (fun j ↦ Fin.elim0 j)) i
    let Dg := gradedProductL2Operator h₀ h₁ k₀ k₁ P Q
    have hDg : Dg.IsClosed := by
      let Pe := P.metricL2ClosedRealization h₀ h₁
      let Qe := Q.metricL2ClosedRealization k₀ k₁
      have hPc := P.metricL2ClosedRealization_realization h₀ h₁
      have hQc := Q.metricL2ClosedRealization_realization k₀ k₁
      have hDc := gradedTensorOperator_realization Pe Qe hPc.2.2 hQc.2.2 hPc.2.1 hQc.2.1
      let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
        (externalTensorL2Equiv μ ν h₁ k₁)
      let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
        (externalTensorL2Equiv μ ν h₀ k₁)
      let Cg := Ueven.toContinuousLinearEquiv.prodCongr Uodd.toContinuousLinearEquiv
      rw [LinearPMap.IsClosed, gradedProductL2Operator_graph h₀ h₁ k₀ k₁ P Q]
      exact Cg.toHomeomorph.isClosedMap _ hDc.2.2.1
    have hIndexRadius :=
      exists_radius_smoothEquivariantAnalyticIndex_average_eq_of_graded_graph
        (n := n + m) (M := M × N) (μ := μ.prod ν) 𝓘(ℝ, VG × VH) S T A B
        α hα β hβ σ hσ τ hτ hs hsInv ht htInv
        hS hSInv hT hTInv hμν e.linearEquiv he₀ he₁ he f.linearEquiv hf₀ hf₁ hf
        ρ η hρ hη hρapp hηapp Dg hDg R L AS AT
        (gradedProductH1Extension h₀ h₁ k₀ k₁ P Q (R 0) (R 1))
    -- Reduce the finite metric family and its local instances before identifying the same graph.
    dsimp +instances +zetaDelta only [hs, ht, Fin.cases_zero, fin_cases_one, A, B,
      Matrix.cons_val_zero, Matrix.cons_val_one, A₀₀, A₁₁, A₁₀, A₀₁,
      g₀₀, g₁₁, g₁₀, g₀₁, Dg, prod_group_toMonoid, prod_group_toMulOneClass,
      prod_monoid_toMulOneClass] at hIndexRadius
    have hIndexRadius := hIndexRadius γ hγ γI hγI hγv Φ hΦ hFg hFred
    let δI : ℝ := hIndexRadius.choose
    have hδI : 0 < δI := hIndexRadius.choose_spec.1
    have hStable := hIndexRadius.choose_spec.2
    -- The same native sum identifications compare both the uncut and the averaged support triples.
    have heCov (z : G × H) (x : M × N) v :
        σ.linearMap z x (e.linearEquiv x v) = e.linearEquiv (z • x)
          (TensorProduct.map (σ₀.linearMap z.1 x.1) (τ₀.linearMap z.2 x.2) v.1,
            TensorProduct.map (σ₁.linearMap z.1 x.1) (τ₁.linearMap z.2 x.2) v.2) :=
      (he z x v).symm
    have hfCov (z : G × H) (x : M × N) v :
        τ.linearMap z x (f.linearEquiv x v) = f.linearEquiv (z • x)
          (TensorProduct.map (σ₁.linearMap z.1 x.1) (τ₀.linearMap z.2 x.2) v.1,
            TensorProduct.map (σ₀.linearMap z.1 x.1) (τ₁.linearMap z.2 x.2) v.2) :=
      (hf z x v).symm
    have hpAdj := fun x ξ u v ↦ (h₀.pairing_adjoint h₁ x (p.val x ξ) u v).symm
    have hqAdj := fun x ξ u v ↦ (k₀.pairing_adjoint k₁ x (q.val x ξ) u v).symm
    have hR₁pos : 0 < R₁ := zero_lt_one.trans_le hR₁
    have hR₂pos : 0 < R₂ := zero_lt_one.trans_le hR₂
    have hpBij (x : M) (ξ : CotangentFiber (n := n) x) (hξ : R₁ ≤ g.length x ξ) :
        Function.Bijective (p.val x ξ) := by
      rw [hpTail x ξ hξ]
      apply hp₀ x ξ
      intro hz
      rw [hz, (g.length_eq_zero_iff x 0).mpr rfl] at hξ
      exact (not_le_of_gt hR₁pos) hξ
    have hqBij (x : N) (ξ : CotangentFiber (n := m) x) (hξ : R₂ ≤ k.length x ξ) :
        Function.Bijective (q.val x ξ) := by
      rw [hqTail x ξ hξ]
      apply hq₀ x ξ
      intro hz
      rw [hz, (k.length_eq_zero_iff x 0).mpr rfl] at hξ
      exact (not_le_of_gt hR₂pos) hξ
    obtain ⟨d, hd, hdBoundary, hdProduct⟩ :=
      exists_equivariantNativeHermitianSupport_of_tail E₀ E₁ F₀ F₁ σ₀ σ₁ τ₀ τ₁
        p₀ q₀ hp₀ hq₀ hp₀Eq hq₀Eq p (h₀.symbolSpaceAdjoint h₁ p)
        q (k₀.symbolSpaceAdjoint k₁ q) hpFixed hpi hqFixed hqi g k gInv kInv
        R₁ R₂ hR₁pos.le hR₂pos.le hpTail hqTail h₀ h₁ k₀ k₁ hpAdj hqAdj
        S T σ τ e.linearEquiv f.linearEquiv he₀ he₁ hf₀ hf₁ heCov hfCov
    obtain ⟨δH, hδH, hδHone, hHomogeneous⟩ :=
      exists_gradedProductCutoff_ellipticHomogeneous_average (μ := μ) (ν := ν)
        E₀ E₁ F₀ F₁ σ₀ σ₁ τ₀ τ₁
        C D g k gInv kInv h₀ h₁ k₀ k₁ p q p₀ q₀ hp₀ hq₀
        R₁ R₂ hR₁pos hR₂pos hpTail hqTail hpFixed hpi hqFixed hqi
        S T σ τ e.linearEquiv f.linearEquiv heCov hfCov hσ hτ
    let νG := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (G × H))
    let : IsProbabilityMeasure νG := ⟨Measure.haarMeasure_self⟩
    obtain ⟨δK, hδK, _hδKone, hKClass⟩ :=
      exists_gradedCutoff_average_kClass_eq E₀ E₁ F₀ F₁ σ₀ σ₁ τ₀ τ₁
        p.val (h₀.symbolSpaceAdjoint h₁ p).val q.val (k₀.symbolSpaceAdjoint k₁ q).val
        hpFixed hpi hqFixed hqi C D g k gInv kInv h₀ h₁ k₀ k₁ hpAdj hqAdj
        R₁ R₂ hR₁pos hR₂pos hpBij hqBij νG
        S T σ τ e.linearEquiv f.linearEquiv heCov hfCov hσ hτ
    -- One positive cutoff parameter satisfies the index, ellipticity, and support thresholds.
    obtain ⟨ε, hε, hεlt⟩ := exists_between
      (lt_min (lt_min hδH hδK) (div_pos hδI (by positivity : 0 < cApprox + 1)))
    have hεH : ε ≤ δH := hεlt.le.trans (min_le_left _ _) |>.trans (min_le_left _ _)
    have hεK : ε ≤ δK := hεlt.le.trans (min_le_left _ _) |>.trans (min_le_right _ _)
    have hεone : ε ≤ 1 := hεH.trans hδHone
    have herr : cApprox * ε < δI := by
      have hεI : ε < δI / (cApprox + 1) := hεlt.trans_le (min_le_right _ _)
      have hmul := (lt_div_iff₀ (by positivity : 0 < cApprox + 1)).mp hεI
      nlinarith
    obtain ⟨U, V, W, Z, hU, hV, hW, hZ, herrBound⟩ := hApprox ε hε hεone
    obtain ⟨K, hK, _⟩ := exists_gradedBundlePseudodifferentialOperator S T A B
      e.linearEquiv f.linearEquiv he₀ he₁ hf₀ hf₁ U V W Z R L AS AT 1 0 (by norm_num)
    have hSymbol := exists_gradedProductCutoff_globalSymbol (μ := μ) (ν := ν)
      E₀ E₁ F₀ F₁ C D p q h₀ h₁ k₀ k₁ ε hε
    dsimp only at hSymbol
    obtain ⟨a, haK, ha⟩ := hSymbol S T e.linearEquiv f.linearEquiv he₀ he₁ hf₀ hf₁
      U V W Z K hK
      (by simpa only [Fintype.sum_prod_type] using hU)
      (by simpa only [Fintype.sum_prod_type] using hV)
      (by simpa only [Fintype.sum_prod_type] using hW)
      (by simpa only [Fintype.sum_prod_type] using hZ)
    obtain ⟨h, hh⟩ := exists_invariant_smoothCotangentMetric
      (G := G × H) (n := n + m) (M := M × N) 𝓘(ℝ, VG × VH)
    have hInv (z : G × H) (x : M × N) (ξ : CotangentFiber (n := n + m) x) :
        h.length (z • x) (cotangentDiffeomorphMap (Diffeomorph.smul (M := M × N)
          𝓘(ℝ, VG × VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ z) ⟨x, ξ⟩).snd =
            h.length x ξ := congrArg Real.sqrt (hh z x ξ ξ)
    obtain ⟨Rb, hRb, b, hb, hbTail, hbEq, hbPrincipal, hbElliptic⟩ :=
      hHomogeneous ε hε hεH K a haK ha h hInv
    have hAverage := hKClass ε hε hεK a (fun x ξ v ↦ ha x ξ v.1 v.2)
      h hInv Rb hRb b hb hbEq hbTail d hd hdBoundary
    have hProduct : equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG × VH) σ τ 1 b hb hbEq =
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
             (equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σ₀ σ₁ 1 p₀ hp₀ hp₀Eq)
             (equivariantHomogeneousSymbolKClass 𝓘(ℝ, VH) τ₀ τ₁ 1 q₀ hq₀ hq₀Eq))) :=
      hAverage.symm.trans hdProduct
    let Cb : QuantizationPresentation (n := n + m) (r := S.rank) (q := T.rank)
        S.Fiber T.Fiber := Classical.choice
          (nonempty_quantizationPresentation (E := S.Fiber) (F := T.Fiber))
    have hEval := equivariantAnalyticIndexMap_eq_smooth_of_homogeneous_universe σ τ hσ hτ (μ.prod ν)
      (K.average 𝓘(ℝ, VG × VH) σ τ hσ hτ)
      (K.isEquivariant_average 𝓘(ℝ, VG × VH) σ τ hσ hτ) Cb b (hbPrincipal Cb) hb hbEq
    have hIndexK := hStable U V W Z K hK hbElliptic (herrBound.trans_lt herr)
    exact (congrArg (equivariantAnalyticIndexMap
      (n := n + m) (VG := VG × VH) (G := G × H) (M := M × N)) hProduct).symm.trans
        (hEval.trans (hIndexK.trans hIndex))

end AtiyahSinger
