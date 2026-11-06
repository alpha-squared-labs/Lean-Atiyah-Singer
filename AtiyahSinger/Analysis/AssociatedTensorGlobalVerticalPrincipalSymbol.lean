/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalPrincipalSymbol
public import AtiyahSinger.Analysis.AtlasPseudodifferentialFiltration
public import AtiyahSinger.Analysis.AtlasPseudodifferentialSumSymbol
public import AtiyahSinger.Analysis.NativePresentationChartCutoff

/-!
# The principal class of a global vertical regularization

Public module ID: M0155.

The supplied cutoff operators retain their full right-product symbols,
base partition, input/output maps and coordinate swaps. Their intrinsic
principal symbols are computed in the same tensor atlas. Finite-sum
additivity then gives the principal class of the double operator sum.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap Topology

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

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

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
-- The extended limit accommodates the finite sum of the specified vertical principal classes.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
open scoped Classical in
/-- The sum of the supplied vertical regularizations has the sum of their intrinsic
principal classes. -/
theorem exists_associatedSphereTensorVerticalGlobal_principalSymbol
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')
    (J : SmoothBundlePresentation (n := n) (r := a) E)
    (b : Fin J.size → B)
    (hJ : ∀ k, tsupport (J.cutoff k) ⊆ (S.trivialization (b k)).baseSet)
    (N : Fin J.size → ℕ)
    (L : ∀ k : Fin J.size, Fin (N k) → AtlasPseudodifferentialPiece A A' 1)
    (γ : ∀ k : Fin J.size, Fin (N k) → X → ℝ)
    (hγ : ∀ k j, ContDiff ℝ ∞ (γ k j)) (hcγ : ∀ k j, HasCompactSupport (γ k j))
    (hsγ : ∀ k j, tsupport (γ k j) ⊆ (J.chart k).target ∩
      (J.chart k).symm ⁻¹' (J.frame k).baseSet)
    (hbγ : ∀ k j, (J.chart k).symm '' tsupport (γ k j) ⊆ (S.trivialization (b k)).baseSet)
    (κ : ∀ k : Fin J.size, Fin (N k) → Y → ℝ)
    (hκ : ∀ k j, ContDiff ℝ ∞ (κ k j)) (hcκ : ∀ k j, HasCompactSupport (κ k j))
    (hsκ : ∀ k j, tsupport (κ k j) ⊆ (L k j).chart.target ∩ (L k j).chart.symm ⁻¹'
      (A'.chart (L k j).output.frameIndex).baseSet)
    (hκInput : ∀ k j, tsupport (κ k j) ⊆ (L k j).chart.symm ⁻¹'
      (A.chart (L k j).input.frameIndex).baseSet) :
    letI := modelTopology V₀ E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI (x : B) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
    let AT : SmoothComplexBundleAtlas (n := n + r) T :=
      associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
      associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
    let Co (k : Fin J.size) (j : Fin (N k)) : BundleChartCutoff E (J.chart k) :=
      { J.chartCutoff E k with
        cutoff := γ k j
        smooth_cutoff := hγ k j
        compact_support := hcγ k j
        support_subset := hsγ k j }
    let Ko (k : Fin J.size) (j : Fin (N k)) : AtlasChartCutoff A' (L k j).chart :=
      { (L k j).output with
        cutoff := κ k j
        smooth_cutoff := hκ k j
        compact_support := hcκ k j
        support_subset := hsκ k j }
    let CP (k : Fin J.size) (j : Fin (N k)) :=
      associatedSphereProductChart S (b k) (J.chart k) (L k j).chart
    let Din (k : Fin J.size) (j : Fin (N k)) := associatedSphereTensorChartCutoff S E A σ hσ
      (b k) (J.chart k) (J.chartCutoff E k)
        (fun _ hx ↦ hJ k (J.chartCutoff_support_subset E k hx)) (L k j).chart (L k j).input
    let Dout (k : Fin J.size) (j : Fin (N k)) :=
      associatedSphereTensorChartCutoff S E A' σ' hσ'
      (b k) (J.chart k) (Co k j) (hbγ k j) (L k j).chart (Ko k j)
    let α (k : Fin J.size) (j : Fin (N k)) :=
      zeroExtendedSymbol Set.univ (L k j).output.cutoff (L k j).symbol
    let β (k : Fin J.size) (j : Fin (N k)) :
        SymbolFunction r (A.rank (L k j).input.frameIndex * a)
        (A'.rank (L k j).output.frameIndex * a) :=
      fun y η ↦ tensorIdentitySymbolMap (A.rank (L k j).input.frameIndex)
        (A'.rank (L k j).output.frameIndex) a (α k j y η)
    ∀ (I : ∀ k : Fin J.size, ∀ j : Fin (N k), AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L k j).input.frameIndex))))
      (O : ∀ k : Fin J.size, ∀ j : Fin (N k),
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L k j).output.frameIndex)))
          →ₗ[ℂ] AT'.smoothSections),
      (∀ k j w z, I k j w z = (Din k j).localizedFunction w z) →
      (∀ k j v z, (O k j v).val z = (Dout k j).extendedFunction v z) →
      ∀ ε : ℝ, 0 < ε →
        ∀ (Q : ∀ k : Fin J.size, Fin (N k) → AtlasPseudodifferentialOperator AT AT' 1)
          (U : ∀ k : Fin J.size, ∀ j : Fin (N k),
            𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L k j).input.frameIndex))) →L[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L k j).output.frameIndex)))),
          (∀ k j, (Q k j).toLinearMap = (O k j).comp ((U k j).toLinearMap.comp (I k j))) →
          (∀ k j v z, U k j v z = quantize
            (rightProductCutoffSymbol (β k j) (γ k j) ε) v z) →
          ∃ g : ∀ k : Fin J.size, Fin (N k) → atlasGlobalSymbolSpace AT AT' 1,
            (∀ k j z ξ, (g k j).val z ξ =
              if hz : z ∈ (CP k j).source ∩ (AT.chart (Din k j).frameIndex).baseSet ∩
                  (AT'.chart (Dout k j).frameIndex).baseSet then
                (((Dout k j).cutoff (CP k j z) * (Din k j).cutoff (CP k j z) : ℝ) : ℂ) •
                  ((AT'.frameLinearEquiv (Dout k j).frameIndex z hz.2).symm.toLinearMap.comp
                    (EuclideanSpace.equiv
                      (Fin (a * A'.rank (L k j).output.frameIndex)) ℂ).toLinearMap).comp
                    ((rightProductCutoffSymbol (β k j) (γ k j) ε (CP k j z)
                      (covectorInChart (CP k j) z ξ)).toLinearMap.comp
                      (((EuclideanSpace.equiv
                        (Fin (a * A.rank (L k j).input.frameIndex)) ℂ).symm.toLinearMap).comp
                          (AT.frameLinearEquiv (Din k j).frameIndex z hz.1.2).toLinearMap))
              else 0) ∧
            ∃ Pε : AtlasPseudodifferentialOperator AT AT' 1,
              Pε.toLinearMap = ∑ k, ∑ j, (Q k j).toLinearMap ∧
              Pε.principalSymbol = atlasGlobalPrincipalSymbolClass AT AT' 1 (∑ k, ∑ j, g k j) := by
  classical
  let := modelTopology V₀ E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let ef := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace ef.symm Z
  let := isManifold_linearModelChartedSpace ef.symm Z
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
  dsimp only
  intro I O hI hO ε hε Q U hQ hU
  have hC (k : Fin J.size) :
      (J.chart k).symm '' tsupport (J.chartCutoff E k).cutoff ⊆
        (S.trivialization (b k)).baseSet :=
    fun _ hx ↦ hJ k (J.chartCutoff_support_subset E k hx)
  -- Apply the local principal computation to exactly the supplied Q/U and I/O at every k,j.
  have hlocal (k : Fin J.size) (j : Fin (N k)) :=
    associatedSphereTensorVerticalPiece_principalSymbol (a := a) S E A σ A' σ' hσ hσ'
      (b k) (J.chart k) (J.chart_mem_atlas k) (J.chartCutoff E k) (hC k) (L k j)
      (γ k j) (hγ k j) (hcγ k j) (hsγ k j) (hbγ k j)
      (κ k j) (hκ k j) (hcκ k j) (hsκ k j) (hκInput k j)
      (I k j) (O k j) (hI k j) (hO k j) ε hε (Q k j) (U k j) (hQ k j) (hU k j)
  choose g hg hprincipal using hlocal
  let Pε : AtlasPseudodifferentialOperator AT AT' 1 :=
    ⟨∑ k, ∑ j, (Q k j).toLinearMap,
      (atlasPseudodifferentialSpace AT AT' 1).sum_mem (fun k _ ↦
        (atlasPseudodifferentialSpace AT AT' 1).sum_mem
          (fun j _ ↦ (Q k j).isPseudodifferentialOperator))⟩
  refine ⟨g, hg, Pε, rfl, ?_⟩
  -- Finite-sum additivity applies to the same original section action.
  have hsum : Pε.toLinearMap = ∑ t : Σ k : Fin J.size, Fin (N k), (Q t.1 t.2).toLinearMap := by
    simp only [Pε, Fintype.sum_sigma]
  calc
    Pε.principalSymbol = ∑ t : Σ k : Fin J.size, Fin (N k), (Q t.1 t.2).principalSymbol :=
      Pε.principalSymbol_eq_sum AT AT' (fun t : Σ k : Fin J.size, Fin (N k) ↦ Q t.1 t.2) hsum
    _ = ∑ k, ∑ j, atlasGlobalPrincipalSymbolClass AT AT' 1 (g k j) := by
      simp only [Fintype.sum_sigma, hprincipal]
      rfl
    _ = atlasGlobalPrincipalSymbolClass AT AT' 1 (∑ k, ∑ j, g k j) := by
      simp only [map_sum]

end AtiyahSinger
