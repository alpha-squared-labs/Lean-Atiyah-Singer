/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalSymbolFactor
public import AtiyahSinger.Analysis.NativePresentationChartCutoff
public import AtiyahSinger.Geometry.SmoothBundlePresentationSubordinate

/-!
# The coefficient factor of vertical regularization

Public module ID: M0217.

The finite factor uses the supplied base partition and sphere pieces. Each
term transports the complete sphere symbol through the associated frames and
retains the base weight, sphere input and output cutoffs, and frequency cutoff
at the split chart covector. The regularization parameter is unrestricted in
this definition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory Set
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap Topology

attribute [local instance] tensorTopology associatedEquivariantFiberAddCommGroup
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


local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ


variable
  {F' : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F' y)] [∀ y, Module ℂ (F' y)]
  [TopologicalSpace (TotalSpace Unit F')] [IsFiniteRank F']
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')

local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))
local notation "V₀" => EuclideanSpace ℂ (Fin a)



set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in

/-- The actual vertical coefficient symbol for the specified scalar partition and pieces. -/
def verticalCutoffFactor
    (hA : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hA' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')
    (J : SmoothBundlePresentation (n := n) (r := a) E)
    (b : Fin J.size → B) (Npiece : ℕ)
    (Lq : Fin Npiece → AtlasPseudodifferentialPiece A A' 1) (ε : ℝ) :
    letI := modelTopology V₀ E
    letI (z : Z) : AddCommGroup (D z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
    letI (z : Z) : Module ℂ (D z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
    letI (z : Z) : AddCommGroup (D' z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ' z
    letI (z : Z) : Module ℂ (D' z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ' z
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (z : Z) → CotangentFiber (n := n + r) z → D z →ₗ[ℂ] D' z := by
  classical
  letI := modelTopology V₀ E
  letI (z : Z) : AddCommGroup (D z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
  letI (z : Z) : Module ℂ (D z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
  letI (z : Z) : AddCommGroup (D' z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ' z
  letI (z : Z) : Module ℂ (D' z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ' z
  letI := associatedSphereChartedSpace S
  letI := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro z ξ
  let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let AD := associatedSphereSmoothBundleAtlas S A σ hA
  let AD' := associatedSphereSmoothBundleAtlas S A' σ' hA'
  let CPv (k : Fin J.size) (j : Fin Npiece) :=
    associatedSphereProductChart S (b k) (J.chart k) (Lq j).chart
  exact
    ∑ k : Fin J.size, ∑ j : Fin Npiece,
      let y := (associatedSphereTrivialization S (b k) z).2
      let cov := split (covectorInChart (CPv k j) z ξ)
      if hz : z ∈ (CPv k j).source ∩
          (AD.chart (b k, (Lq j).input.frameIndex)).baseSet ∩
          (AD'.chart (b k, (Lq j).output.frameIndex)).baseSet then
        let eIn : D z ≃ₗ[ℂ]
            EuclideanSpace ℂ (Fin (A.rank (Lq j).input.frameIndex)) :=
          (AD.frameLinearEquiv (b k, (Lq j).input.frameIndex) z hz.1.2).trans
            (EuclideanSpace.equiv
              (Fin (A.rank (Lq j).input.frameIndex)) ℂ).symm.toLinearEquiv
        let eOut : D' z ≃ₗ[ℂ]
            EuclideanSpace ℂ (Fin (A'.rank (Lq j).output.frameIndex)) :=
          (AD'.frameLinearEquiv (b k, (Lq j).output.frameIndex) z hz.2).trans
            (EuclideanSpace.equiv
              (Fin (A'.rank (Lq j).output.frameIndex)) ℂ).symm.toLinearEquiv
        (((J.chartCutoff E k).cutoff (J.chart k (πS z)) *
          (Lq j).input.cutoff ((Lq j).chart y) *
          (Lq j).output.cutoff ((Lq j).chart y) *
          productFrequencyCutoff ε ‖cov.2‖ ‖cov.1‖ : ℝ) : ℂ) •
          (eOut.symm.toLinearMap.comp
            (((Lq j).symbol ((Lq j).chart y) cov.2).toLinearMap.comp eIn.toLinearMap)
              : D z →ₗ[ℂ] D' z)
      else (0 : D z →ₗ[ℂ] D' z)

end AtiyahSinger
