/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalFamilyRegularization

/-!
# Witness tuples for a specified finite vertical family

This type packages the witnesses of the fixed-family regularization theorem.
The number and sphere pieces are parameters, so their dependent coordinate
ranks remain fixed when choosing tuples across a base-indexed family. Each
tuple retains the plateau data, coordinate maps, limiting realization, and
common-parameter error bound. The nonemptiness theorem packages witnesses
provided by the existing finite-family construction.
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
set_option maxHeartbeats 3200000 in

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Witness tuples for finite regularization with the specified sphere pieces and ranks. -/
def AssociatedSphereTensorVerticalFamilyData
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A') (b : B)
    (c : OpenPartialHomeomorph B X) (_hc : c ∈ atlas X B)
    (C : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (N : ℕ) (L : Fin N → AtlasPseudodifferentialPiece A A' 1) :
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
    ∀ (_Li : AtlasBundlePresentation AT) (_Lo : AtlasBundlePresentation AT'), Type _ :=
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
    fun (Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation AT') ↦
      Σ' (γ : Fin N → X → ℝ) (hγ : ∀ j, ContDiff ℝ ∞ (γ j))
          (hcγ : ∀ j, HasCompactSupport (γ j))
          (hsγ : ∀ j, tsupport (γ j) ⊆ c.target ∩ c.symm ⁻¹' C.frame.baseSet)
          (hbγ : ∀ j, c.symm '' tsupport (γ j) ⊆ (S.trivialization b).baseSet)
          (κ : Fin N → Y → ℝ) (hκ : ∀ j, ContDiff ℝ ∞ (κ j))
          (hcκ : ∀ j, HasCompactSupport (κ j))
          (hsκ : ∀ j, tsupport (κ j) ⊆ (L j).chart.target ∩ (L j).chart.symm ⁻¹'
            (A'.chart (L j).output.frameIndex).baseSet),
          let Co (j : Fin N) : BundleChartCutoff E c :=
            { C with
              cutoff := γ j
              smooth_cutoff := hγ j
              compact_support := hcγ j
              support_subset := hsγ j }
          let Ko (j : Fin N) : AtlasChartCutoff A' (L j).chart :=
            { (L j).output with
              cutoff := κ j
              smooth_cutoff := hκ j
              compact_support := hcκ j
              support_subset := hsκ j }
          let Din (j : Fin N) := associatedSphereTensorChartCutoff S E A σ hσ
            b c C hC (L j).chart (L j).input
          let Dout (j : Fin N) := associatedSphereTensorChartCutoff S E A' σ' hσ'
            b c (Co j) (hbγ j) (L j).chart (Ko j)
          let α (j : Fin N) := zeroExtendedSymbol Set.univ (L j).output.cutoff (L j).symbol
          let β (j : Fin N) : SymbolFunction r (A.rank (L j).input.frameIndex * a)
              (A'.rank (L j).output.frameIndex * a) :=
            fun y η ↦ tensorIdentitySymbolMap (A.rank (L j).input.frameIndex)
              (A'.rank (L j).output.frameIndex) a (α j y η)
          let p (j : Fin N) := isometricSymbolTransport (productCoordinateSwap n r)
            (tensorCoordinateSwap a (A.rank (L j).input.frameIndex))
            (tensorCoordinateSwap a (A'.rank (L j).output.frameIndex)).symm
            (liftedProductSymbol (β j) (γ j))
          (∀ j x, x ∈ tsupport C.cutoff → γ j x = 1) ×'
          (∀ j y, y ∈ tsupport (L j).output.cutoff → κ j y = 1) ×'
          (∀ j, tsupport (κ j) ⊆ (L j).chart.symm ⁻¹'
            (A.chart (L j).input.frameIndex).baseSet) ×'
          Σ' (I : ∀ j : Fin N, AT.smoothSections →ₗ[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L j).input.frameIndex))))
            (O : ∀ j : Fin N,
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L j).output.frameIndex)))
                →ₗ[ℂ] AT'.smoothSections),
            (∀ j w z, I j w z = (Din j).localizedFunction w z) ×'
            (∀ j v z, (O j v).val z = (Dout j).extendedFunction v z) ×'
            Σ' (Tj : Fin N → AT.smoothSections →ₗ[ℂ] AT'.smoothSections)
              (R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0),
              (∀ j (w : AT.smoothSections),
                ∃ v : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L j).output.frameIndex))),
                  (∀ z, quantize (p j) (I j w) z = v z) ∧
                  (tsupport v ⊆ EuclideanSpace.finAddEquivProd.symm ''
                    (tsupport C.cutoff ×ˢ tsupport (L j).output.cutoff)) ∧
                  Tj j w = O j v ∧
                  ∀ x : B, x ∈ c.source → x ∈ (S.trivialization b).baseSet →
                    x ∈ C.frame.baseSet → ∀ y : OrthogonalSphere r,
                      let q := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
                      (Tj j w).val (associatedBundleMk G P (OrthogonalSphere r) q y) =
                        (C.cutoff (c x) : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
                          ((tensorSectionOperator (E (projection q)) A.smoothSections
                            A'.smoothSections (L j).toLinearMap
                            (associatedSphereTensorFiberRestriction (a := a)
                              S E A σ hσ q w)).val y)) ×'
              (∀ w : AT.smoothSections, R (Li.smoothToSobolev 1 w) =
                Lo.smoothToSobolev 0 (∑ j, Tj j w)) ×'
              Σ' K : ℝ, 0 ≤ K ×' ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
                ∃ (Qε : Fin N → AtlasPseudodifferentialOperator AT AT' 1)
                  (U : ∀ j : Fin N,
                    𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L j).input.frameIndex))) →L[ℂ]
                      𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L j).output.frameIndex))))
                  (Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0),
                  (∀ j, (Qε j).toLinearMap = (O j).comp ((U j).toLinearMap.comp (I j))) ∧
                  (∀ j v z, U j v z = quantize
                    (rightProductCutoffSymbol (β j) (γ j) ε) v z) ∧
                  (∀ w, Rε (Li.smoothToSobolev 1 w) =
                    Lo.smoothToSobolev 0 (∑ j, (Qε j).toLinearMap w)) ∧
                  ‖Rε - R‖ ≤ K * ε

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 3200000 in

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The existing finite theorem supplies every field of the exact witness package. -/
theorem nonempty_associatedSphereTensorVerticalFamilyData
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A') (b : B)
    (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (C : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (N : ℕ) (L : Fin N → AtlasPseudodifferentialPiece A A' 1) :
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
    ∀ (Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation AT'),
      Nonempty (AssociatedSphereTensorVerticalFamilyData
        S E A σ A' σ' hσ hσ' b c hc C hC N L Li Lo) := by
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
  let AT : SmoothComplexBundleAtlas (n := n + r) T :=
    associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
    associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
  dsimp only
  intro Li Lo
  change AtlasBundlePresentation AT at Li
  change AtlasBundlePresentation AT' at Lo
  obtain ⟨γ, hγ, hcγ, hsγ, hbγ, κ, hκ, hcκ, hsκ,
    hγone, hκone, hκin, I, O, hI, hO, Tj, R, hTj, hR, K, hK, hpositive⟩ :=
    exists_associatedSphereTensorVerticalFamily_regularization
      S E A σ A' σ' hσ hσ' b c hc C hC N L Li Lo
  exact ⟨⟨γ, hγ, hcγ, hsγ, hbγ, κ, hκ, hcκ, hsκ,
    hγone, hκone, hκin, I, O, hI, hO, Tj, R, hTj, hR, K, hK, hpositive⟩⟩

end AtiyahSinger
