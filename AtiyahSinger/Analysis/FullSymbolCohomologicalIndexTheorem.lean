/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.BaseCohomologicalIndexTheorem
public import AtiyahSinger.Analysis.FullSymbolIndexTheorem
public import AtiyahSinger.Topology.ComplexificationBundle
public import AtiyahSinger.Topology.ContinuousHermitianMetric

/-!
# The original cohomological formulas for general full-symbol operators

Public module ID: M2315.

The two metric selectors are public so that the exposed characteristic definitions
can use them. They choose the same native metrics for both formulas.

The two characteristic classes below package the existing degreewise expressions
from M0344 and M0319 using internally supplied native metric data. M1483 supplies
the original smooth tangent metric; M1724 and M1743 supply a Hermitian metric on
its genuine tensor complexification. The original musical K equivalence transports
the same cotangent symbol class, without changing the tangent topology or fibers.

T02 uses the canonical interleaved tangent orientation and its original locally
finite fundamental class, with factor (-1)^n; the base need not be oriented.
T03 uses the prescribed integral base orientation for both the base-first Thom
inverse and base evaluation, with factor (-1)^(n*(n+1)/2). In dimension zero the
same orientation still controls both signs. The six operator formulas from
M2314 and this module retain the same original operators and genuine full classes.

Sources: SG III.13, the two Theorems 13.8, formulas (13.18) and (13.24),
pp.254--255. SG means H. Blaine Lawson, Jr. and Marie-Louise Michelsohn,
*Spin Geometry* (Princeton University Press, 1989). M0319 retains the base-first
Thom convention from Atiyah--Singer III, (2.13) and footnote 4, p.557.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 30

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "TM" => TangentBundle 𝓘(ℝ, V) M
local notation "T" => (TangentSpace 𝓘(ℝ, V) : M → Type)

/-- The native tangent metric chosen for both exposed characteristic expressions. -/
def indexTangentMetric : SmoothTangentMetric (n := n) (M := M) :=
  Classical.choice SmoothTangentMetric.nonempty

/-- A metric on the original tensor complexification for both exposed expressions. -/
def indexTangentComplexMetric :
    letI := complexificationTopology V T
    ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x) := by
  letI := complexificationTopology V T
  letI := ComplexBundle.isFiniteRank_complexification V T
  exact (nonempty_continuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] T x)).some

/-- The degree-2n supported class ch(u) cup pi*(A-hat(TM)^2) with native metrics internal. -/
def cotangentIndexCharacteristicClass
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
    compactSupportCohomology ℚ TM (2 * n) :=
  tangentIndexCharacteristicClass (indexTangentMetric (n := n) (M := M))
    (indexTangentComplexMetric (n := n) (M := M))
    ((tangentCotangentKZeroEquiv (indexTangentMetric (n := n) (M := M))).symm u)

/-- The degree-n base class pi!(ch(u)) cup A-hat(TM)^2 with the original O-normalized inverse. -/
def cotangentBaseIndexCharacteristicClass (O : HomologicalOrientation n M)
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
    singularCohomology ℚ M n :=
  baseIndexCharacteristicClass O (indexTangentMetric (n := n) (M := M))
    (indexTangentComplexMetric (n := n) (M := M))
    ((tangentCotangentKZeroEquiv (indexTangentMetric (n := n) (M := M))).symm u)

section AtlasOperator

variable {E F : M → Type}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

/-- SG (13.18) for the original general atlas PDO, without an orientation on its base. -/
theorem AtlasPseudodifferentialOperator.index_eq_tangent_characteristic_number_fullSymbol
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m) (hi : P.IsElliptic) :
    ((P.toLinearMap.index : ℤ) : ℚ) =
      (-1 : ℚ) ^ n * compactSupportLocallyFinitePairing ℚ TM (2 * n)
        (cotangentIndexCharacteristicClass (P.fullSymbolKClass hi))
        (rationalTangentFundamentalClass (n := n) (M := M)) := by
  -- Transport this same full class in the original integer index equality.
  have hindex := P.index_eq_cotangentTopologicalIndex_fullSymbol hi
  rw [cotangentTopologicalIndex_eq (indexTangentMetric (n := n) (M := M)),
    AddMonoidHom.comp_apply] at hindex
  change P.toLinearMap.index = topologicalIndex V M
    ((tangentCotangentKZeroEquiv (indexTangentMetric (n := n) (M := M))).symm
      (P.fullSymbolKClass hi)) at hindex
  -- Expand the existing characteristic packaging and use the original tangent formula.
  rw [hindex, cotangentIndexCharacteristicClass]
  exact topologicalIndex_eq_tangent_characteristic_number
    (indexTangentMetric (n := n) (M := M)) (indexTangentComplexMetric (n := n) (M := M))
    ((tangentCotangentKZeroEquiv (indexTangentMetric (n := n) (M := M))).symm
      (P.fullSymbolKClass hi))

/-- SG (13.24) for the original general atlas PDO and the same original base orientation. -/
theorem AtlasPseudodifferentialOperator.index_eq_base_characteristic_number_fullSymbol
    (O : HomologicalOrientation n M)
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m) (hi : P.IsElliptic) :
    ((P.toLinearMap.index : ℤ) : ℚ) =
      (-1 : ℚ) ^ (n * (n + 1) / 2) * compactManifoldCohomologyIntegral O
        (cotangentBaseIndexCharacteristicClass O (P.fullSymbolKClass hi)) := by
  -- Transport this same full class in the original integer index equality.
  have hindex := P.index_eq_cotangentTopologicalIndex_fullSymbol hi
  rw [cotangentTopologicalIndex_eq (indexTangentMetric (n := n) (M := M)),
    AddMonoidHom.comp_apply] at hindex
  change P.toLinearMap.index = topologicalIndex V M
    ((tangentCotangentKZeroEquiv (indexTangentMetric (n := n) (M := M))).symm
      (P.fullSymbolKClass hi)) at hindex
  -- The same O fixes both the base-first Thom inverse and the base integral.
  rw [hindex, cotangentBaseIndexCharacteristicClass]
  exact topologicalIndex_eq_base_characteristic_number O
    (indexTangentMetric (n := n) (M := M)) (indexTangentComplexMetric (n := n) (M := M))
    ((tangentCotangentKZeroEquiv (indexTangentMetric (n := n) (M := M))).symm
      (P.fullSymbolKClass hi))

end AtlasOperator

section NativeOperator

variable [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {r q : ℕ} {E F : M → Type}
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

/-- SG (13.18) retains the same original native operator, its density and its full class. -/
theorem PseudodifferentialOperator.index_eq_tangent_characteristic_number_fullSymbol
    {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hi : P.IsElliptic) :
    ((P.toLinearMap.index : ℤ) : ℚ) =
      (-1 : ℚ) ^ n * compactSupportLocallyFinitePairing ℚ TM (2 * n)
        (cotangentIndexCharacteristicClass (P.fullSymbolKClass hi))
        (rationalTangentFundamentalClass (n := n) (M := M)) := by
  -- Keep the given native P and its original density in the same integer equality.
  have hindex := P.index_eq_cotangentTopologicalIndex_fullSymbol hi
  rw [cotangentTopologicalIndex_eq (indexTangentMetric (n := n) (M := M)),
    AddMonoidHom.comp_apply] at hindex
  change P.toLinearMap.index = topologicalIndex V M
    ((tangentCotangentKZeroEquiv (indexTangentMetric (n := n) (M := M))).symm
      (P.fullSymbolKClass hi)) at hindex
  -- Expand the existing characteristic packaging and use the original tangent formula.
  rw [hindex, cotangentIndexCharacteristicClass]
  exact topologicalIndex_eq_tangent_characteristic_number
    (indexTangentMetric (n := n) (M := M)) (indexTangentComplexMetric (n := n) (M := M))
    ((tangentCotangentKZeroEquiv (indexTangentMetric (n := n) (M := M))).symm
      (P.fullSymbolKClass hi))

/-- SG (13.24) retains the same original native operator and the original O-normalized integral. -/
theorem PseudodifferentialOperator.index_eq_base_characteristic_number_fullSymbol
    (O : HomologicalOrientation n M)
    {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hi : P.IsElliptic) :
    ((P.toLinearMap.index : ℤ) : ℚ) =
      (-1 : ℚ) ^ (n * (n + 1) / 2) * compactManifoldCohomologyIntegral O
        (cotangentBaseIndexCharacteristicClass O (P.fullSymbolKClass hi)) := by
  -- Keep the given native P and its original density in the same integer equality.
  have hindex := P.index_eq_cotangentTopologicalIndex_fullSymbol hi
  rw [cotangentTopologicalIndex_eq (indexTangentMetric (n := n) (M := M)),
    AddMonoidHom.comp_apply] at hindex
  change P.toLinearMap.index = topologicalIndex V M
    ((tangentCotangentKZeroEquiv (indexTangentMetric (n := n) (M := M))).symm
      (P.fullSymbolKClass hi)) at hindex
  -- The same O fixes both the base-first Thom inverse and the base integral.
  rw [hindex, cotangentBaseIndexCharacteristicClass]
  exact topologicalIndex_eq_base_characteristic_number O
    (indexTangentMetric (n := n) (M := M)) (indexTangentComplexMetric (n := n) (M := M))
    ((tangentCotangentKZeroEquiv (indexTangentMetric (n := n) (M := M))).symm
      (P.fullSymbolKClass hi))

end NativeOperator

end AtiyahSinger
