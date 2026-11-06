/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AnalyticIndexDiffeomorph
public import AtiyahSinger.Analysis.ComponentIndexClopen
public import AtiyahSinger.Topology.FiniteHomotopyComponents
public import AtiyahSinger.Topology.OpenEmbeddingKZeroRestriction

/-!
# Analytic excision from a compact source

Public module ID: M0360.

Finite clopen additivity identifies the index of an open extension from a
compact source with its original index. Diffeomorphism naturality then compares
two compact environments. In particular this supplies the zero-dimensional
branch for a source of finite CW homotopy type, without a fixed virtual rank.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory TopologicalSpace
open scoped Manifold ContDiff BigOperators

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isSmoothPositiveMeasure_comap_opens

/-- Extending from a clopen submanifold preserves its original component analytic index. -/
theorem analyticIndexOfComponents_cotangentOpenExtension_of_isClosed
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (U : Opens M) (hU : IsClosed (U : Set M))
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := U))) :
    letI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
    analyticIndexOfComponents μ (cotangentKZeroOpenExtension U u) =
      analyticIndexOfComponents (μ.comap (Subtype.val : U → M)) u := by
  classical
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  let V : Opens M := ⟨(U : Set M)ᶜ, hU.isOpen_compl⟩
  let : CompactSpace V := isCompact_iff_compactSpace.mp U.isOpen.isClosed_compl.isCompact
  let W : Bool → Opens M := fun b ↦ if b then V else U
  have hclosed (b : Bool) : IsClosed (W b : Set M) := by
    cases b
    · exact hU
    · exact U.isOpen.isClosed_compl
  have hdisjoint : Pairwise (fun i j ↦ Disjoint (W i : Set M) (W j : Set M)) := by
    intro i j h
    cases i <;> cases j
    · exact (h rfl).elim
    · exact disjoint_compl_right
    · exact disjoint_compl_left
    · exact (h rfl).elim
  have hcover : (⋃ b, (W b : Set M)) = Set.univ := by
    ext x
    simp [W, V, Bool.exists_bool, Classical.em]
  -- Restriction of the actual extension is the original class on U and zero on its complement.
  have hself := compactSupportKZeroPullback_openPushforward_self
    (cotangentOpenInclusion (n := n) U) (isOpenEmbedding_cotangentOpenInclusion U)
    (isProperMap_cotangentOpenInclusion U hU) u
  have hsep : Disjoint (Set.range (cotangentOpenInclusion (n := n) U))
      (Set.range (cotangentOpenInclusion (n := n) V)) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, rfl⟩ ⟨y, hxy⟩
    have hbase : y.proj.val = x.proj.val := congrArg Bundle.TotalSpace.proj hxy
    exact y.proj.property (hbase.symm ▸ x.proj.property)
  have hzero := compactSupportKZeroPullback_openPushforward_of_disjoint
    (cotangentOpenInclusion (n := n) U) (isOpenEmbedding_cotangentOpenInclusion U)
    ⟨cotangentOpenInclusion (n := n) V, (isOpenEmbedding_cotangentOpenInclusion V).continuous⟩
    (isProperMap_cotangentOpenInclusion V U.isOpen.isClosed_compl) hsep u
  have hsum := analyticIndexOfComponents_eq_sum_clopen μ W hclosed hdisjoint hcover
    (cotangentKZeroOpenExtension U u)
  rw [Fintype.sum_bool] at hsum
  change _ = analyticIndexOfComponents (μ.comap (Subtype.val : V → M)) _ +
    analyticIndexOfComponents (μ.comap (Subtype.val : U → M)) _ at hsum
  apply hsum.trans
  calc
    _ = analyticIndexOfComponents (μ.comap (Subtype.val : V → M)) 0 +
        analyticIndexOfComponents (μ.comap (Subtype.val : U → M)) u :=
      congrArg₂ (· + ·)
        (congrArg (analyticIndexOfComponents (μ.comap (Subtype.val : V → M))) hzero)
        (congrArg (analyticIndexOfComponents (μ.comap (Subtype.val : U → M))) hself)
    _ = _ := by rw [map_zero, zero_add]

variable {O N : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O] [T2Space O]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]

/-- Compact open sources have the same analytic index in two specified compact environments. -/
theorem analyticIndexOfComponents_excision_of_compactSpace [CompactSpace O]
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := n) ν]
    (U : Opens M) (V : Opens N)
    (f : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U)
    (g : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V) :
    (analyticIndexOfComponents μ).comp (cotangentKZeroOpenEmbedding U f) =
      (analyticIndexOfComponents ν).comp (cotangentKZeroOpenEmbedding V g) := by
  let : CompactSpace U := f.toHomeomorph.compactSpace
  let : CompactSpace V := g.toHomeomorph.compactSpace
  have hU : IsClosed (U : Set M) := (isCompact_iff_compactSpace.mpr
    (inferInstance : CompactSpace U)).isClosed
  have hV : IsClosed (V : Set N) := (isCompact_iff_compactSpace.mpr
    (inferInstance : CompactSpace V)).isClosed
  let d := f.symm.trans g
  have hfd : f.trans d = g := by
    apply Diffeomorph.ext
    intro x
    exact congrArg g (f.symm_apply_apply x)
  have hcot : cotangentDiffeomorph g =
      (cotangentDiffeomorph f).trans (cotangentDiffeomorph d) := by
    rw [← cotangentDiffeomorph_trans, hfd]
  have htransport (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := O))) :
      cotangentKZeroDiffeomorph d (cotangentKZeroDiffeomorph f u) =
        cotangentKZeroDiffeomorph g u := by
    -- Both routes are inverse proper pullbacks along the same cotangent homeomorphism.
    change compactSupportKZeroPullback
      ⟨(cotangentDiffeomorph d).symm, (cotangentDiffeomorph d).symm.continuous⟩ _
      (compactSupportKZeroPullback
        ⟨(cotangentDiffeomorph f).symm, (cotangentDiffeomorph f).symm.continuous⟩ _ u) =
      compactSupportKZeroPullback
        ⟨(cotangentDiffeomorph g).symm, (cotangentDiffeomorph g).symm.continuous⟩ _ u
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp, hcot]
    rfl
  have hindex := analyticIndexOfComponents_diffeomorph
    (μ.comap (Subtype.val : U → M)) (ν.comap (Subtype.val : V → N)) d
  apply AddMonoidHom.ext
  intro u
  change analyticIndexOfComponents μ
    (cotangentKZeroOpenExtension U (cotangentKZeroDiffeomorph f u)) =
      analyticIndexOfComponents ν
        (cotangentKZeroOpenExtension V (cotangentKZeroDiffeomorph g u))
  -- Clopen extension and naturality compare the original two ambient measures directly.
  rw [analyticIndexOfComponents_cotangentOpenExtension_of_isClosed μ U hU,
    analyticIndexOfComponents_cotangentOpenExtension_of_isClosed ν V hV,
    ← htransport]
  exact (DFunLike.congr_fun hindex (cotangentKZeroDiffeomorph f u)).symm

/-- Finite CW type makes the zero-dimensional source compact, so clopen excision applies. -/
theorem analyticIndexOfComponents_excision_of_dim_zero
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (C : Set Y) [Topology.CWComplex C] [Topology.CWComplex.Finite C]
    (e : ContinuousMap.HomotopyEquiv O C) (hn : n = 0)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := n) ν]
    (U : Opens M) (V : Opens N)
    (f : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U)
    (g : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V) :
    (analyticIndexOfComponents μ).comp (cotangentKZeroOpenEmbedding U f) =
      (analyticIndexOfComponents ν).comp (cotangentKZeroOpenEmbedding V g) := by
  subst n
  let : DiscreteTopology O := ChartedSpace.discreteTopology
    (EuclideanSpace ℝ (Fin 0)) O
  let : Finite (ConnectedComponents O) :=
    finite_connectedComponents_of_homotopyEquiv_finiteCW (n := 0) C e
  -- In a discrete source each point is its own component, including the empty case.
  let : Finite O := Finite.of_injective ConnectedComponents.mk (by
    intro x y hxy
    have h := ConnectedComponents.coe_eq_coe.mp hxy
    simpa only [connectedComponent_eq_singleton, Set.singleton_eq_singleton_iff] using h)
  let : CompactSpace O := inferInstance
  exact analyticIndexOfComponents_excision_of_compactSpace μ ν U V f g

end AtiyahSinger
