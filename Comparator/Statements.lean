/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EvenDimensionalTwistedSpinIndex
public import AtiyahSinger.Analysis.FullSymbolCohomologicalIndexTheorem

/-!
# Reviewed Atiyah--Singer comparator statements

The seven propositions spell out the final T01--T04 interfaces independently
of their proofs. T01--T03 each retain both the variable-rank atlas and native
fixed-rank operator. T04 retains the original uniform native even-dimensional
spin input, including its positive empty-frame endpoint in dimension zero.

The mathematical objects are the already accepted production definitions.
This module imports those definitions together with their existing support;
it does not claim to reconstruct them using only mathlib. The comparator
configuration has no definition holes. Object standardness is covered by the
prior source and book review; the comparator checks the stated formal targets.

Sources: SG III.13.2, the two III.13.8 formulas (13.18) and (13.24), and
III.13.10 (13.26). SG is H. Blaine Lawson, Jr. and Marie-Louise Michelsohn,
Spin Geometry, Princeton University Press, 1989, pp.244, 254--257.
Production modules: M2314, M2315 and M2303.
-/

@[expose] public noncomputable section

universe u v w a b

namespace AtiyahSinger.ComparatorStatements

open Bundle ComplexBundle MeasureTheory
open scoped BigOperators Manifold ContDiff TensorProduct

section GeneralIndex

set_option maxSynthPendingDepth 30

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

/-- T01, SG III.13.2: the same variable-rank elliptic atlas PDO and its full symbol. -/
def T01Atlas : Prop :=
  ∀
    {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {E : M → Type v} {F : M → Type w}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)]
    {A : SmoothComplexBundleAtlas.{a, u, v} (n := n) E}
    {B : SmoothComplexBundleAtlas.{b, u, w} (n := n) F}
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m) (hi : P.IsElliptic),
      P.toLinearMap.index = cotangentTopologicalIndex n M (P.fullSymbolKClass hi)

/-- T01, SG III.13.2: the same native elliptic PDO with its original density. -/
def T01Native : Prop :=
  ∀
    {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
    {r q : ℕ} {E : M → Type v} {F : M → Type w}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
    [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
    [IsSmoothComplexBundle (n := n) (r := r) E]
    [IsSmoothComplexBundle (n := n) (r := q) F]
    {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hi : P.IsElliptic),
      P.toLinearMap.index = cotangentTopologicalIndex n M (P.fullSymbolKClass hi)

/-- T02, SG (13.18): the atlas formula with no orientation premise on the base. -/
def T02Atlas : Prop :=
  ∀
    {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {E : M → Type} {F : M → Type}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)]
    {A : SmoothComplexBundleAtlas.{a, 0, 0} (n := n) E}
    {B : SmoothComplexBundleAtlas.{b, 0, 0} (n := n) F}
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m) (hi : P.IsElliptic),
      ((P.toLinearMap.index : ℤ) : ℚ) =
        (-1 : ℚ) ^ n * compactSupportLocallyFinitePairing ℚ
          (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) (2 * n)
          (cotangentIndexCharacteristicClass (P.fullSymbolKClass hi))
          (rationalTangentFundamentalClass (n := n) (M := M))

/-- T02, SG (13.18): the native formula with no orientation premise on the base. -/
def T02Native : Prop :=
  ∀
    {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
    {r q : ℕ} {E : M → Type} {F : M → Type}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
    [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
    [IsSmoothComplexBundle (n := n) (r := r) E]
    [IsSmoothComplexBundle (n := n) (r := q) F]
    {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hi : P.IsElliptic),
      ((P.toLinearMap.index : ℤ) : ℚ) =
        (-1 : ℚ) ^ n * compactSupportLocallyFinitePairing ℚ
          (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) (2 * n)
          (cotangentIndexCharacteristicClass (P.fullSymbolKClass hi))
          (rationalTangentFundamentalClass (n := n) (M := M))

/-- T03, SG (13.24): the atlas formula using the same given integral orientation. -/
def T03Atlas : Prop :=
  ∀
    {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {E : M → Type} {F : M → Type}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)]
    {A : SmoothComplexBundleAtlas.{a, 0, 0} (n := n) E}
    {B : SmoothComplexBundleAtlas.{b, 0, 0} (n := n) F}
    (O : HomologicalOrientation n M)
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m) (hi : P.IsElliptic),
      ((P.toLinearMap.index : ℤ) : ℚ) =
        (-1 : ℚ) ^ (n * (n + 1) / 2) * compactManifoldCohomologyIntegral O
          (cotangentBaseIndexCharacteristicClass O (P.fullSymbolKClass hi))

/-- T03, SG (13.24): the native formula using the same given integral orientation. -/
def T03Native : Prop :=
  ∀
    {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
    {r q : ℕ} {E : M → Type} {F : M → Type}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
    [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
    [IsSmoothComplexBundle (n := n) (r := r) E]
    [IsSmoothComplexBundle (n := n) (r := q) F]
    (O : HomologicalOrientation n M)
    {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hi : P.IsElliptic),
      ((P.toLinearMap.index : ℤ) : ℚ) =
        (-1 : ℚ) ^ (n * (n + 1) / 2) * compactManifoldCohomologyIntegral O
          (cotangentBaseIndexCharacteristicClass O (P.fullSymbolKClass hi))

end GeneralIndex

section TwistedIndex

set_option maxSynthPendingDepth 50

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  ComplexBundle.tensorTopology ComplexBundle.isFiniteRank_tensor
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  t2Space_cotangent locallyCompactSpace_cotangent

set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- T04, SG (13.26), with the proved native zero-dimensional positive-frame continuation. -/
def T04 : Prop :=
  ∀ {m : ℕ} {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
    [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
    {projection : P → M}
    {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
    (g : SmoothTangentMetric (n := 2 * m) (M := M))
    {W : M → Type} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
    [TopologicalSpace (TotalSpace Unit W)]
    (B : SmoothComplexBundleAtlas.{a, 0, 0} (n := 2 * m) W)
    (covW : AtlasComplexConnection B),
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m)))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))) :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞
        (EuclideanSpace ℝ (Fin (2 * m)))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))) :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    letI := B.isFiniteRank
    ∀ S : EvenDimensionalSpinInput hP,
      (((S.twistedDiracPlus g B covW).toLinearMap.index : ℤ) : ℚ) =
        compactManifoldCohomologyIntegral (S.homologicalOrientation g)
          (spinDiracCharacteristicClass
            (evenDimensionalTangentHermitianMetric (m := m) (M := M))
            (ComplexBundle.kZeroClass W))

end TwistedIndex

end AtiyahSinger.ComparatorStatements
