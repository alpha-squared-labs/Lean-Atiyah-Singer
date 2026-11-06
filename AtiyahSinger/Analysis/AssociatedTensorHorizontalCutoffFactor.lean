/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalHorizontalDualApproximation
public import AtiyahSinger.Analysis.AssociatedTensorGlobalHorizontalRegularization
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalPrincipalSymbol
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalSymbolFactor
public import AtiyahSinger.Analysis.AtlasNativePrincipalConjugate
public import AtiyahSinger.Analysis.FiniteRegularizationNormBounds

/-!
# The horizontal cutoff factor

Public module ID: M0162.

For a fixed principal localization and sphere partition, `horizontalCutoffFactor`
is the finite weighted sum of base symbol maps pulled back through associated
product charts. The weights combine the sphere partition and product-frequency
cutoff, and the formula retains the full chart covectors. The real parameter
is unrestricted in this definition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap Topology

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z

variable [T2Space B]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ


variable {a' : ℕ}
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))
local notation "V₀" => EuclideanSpace ℂ (Fin a)
local notation "V₁" => EuclideanSpace ℂ (Fin a')

local notation "T'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

variable [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

variable [SecondCountableTopology B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

variable [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

namespace PrincipalPseudodifferentialLocalization


/-- The scalar-cutoff horizontal symbol factor for a fixed base localization
and fixed sphere partition. It retains the full chart covectors. -/
def horizontalCutoffFactor
    (L : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (J : AtlasBundlePresentation A) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ℝ → ∀ z : Z, CotangentFiber (n := n + r) z → (E (πS z) →ₗ[ℂ] E' (πS z)) := by
  letI := associatedSphereChartedSpace S
  let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  letI := linearModelChartedSpace split.symm Z
  exact fun ε z ξ ↦ ∑ i, ∑ j,
    let chart := associatedSphereProductChart S (L.center i) (L.piece i).chart (J.chart j)
    let cov := split (covectorInChart chart z ξ)
    ((J.cutoff j (associatedSphereTrivialization S (L.center i) z).2 *
      productFrequencyCutoff ε ‖cov.1‖ ‖cov.2‖ : ℝ) : ℂ) •
        ((L.piece i).globalSymbolFunction (πS z)
          (covectorFromChart (L.piece i).chart (πS z) cov.1)).toLinearMap


end PrincipalPseudodifferentialLocalization

end AtiyahSinger
