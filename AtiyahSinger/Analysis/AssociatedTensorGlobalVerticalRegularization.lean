/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalFamilyRegularization

/-!
# Global vertical regularization with supported smoothing residuals

A finite sphere representation of the full PDO and a subordinate native base
partition give an exact decomposition of the vertical map into local piece
contributions and supported smoothing residuals. The local cutoff PDOs use
one common positive parameter and approximate the piece contribution in
the supplied H¹-to-H⁰ operator norm. Their coordinate maps, complete symbols
and the residual support and fiber formulas remain part of the conclusion.
-/

@[expose] public noncomputable section

set_option Elab.async false


/- The auxiliary proof is closed after expanding its free local let values. -/
open Lean Elab Tactic Meta in
local elab "as_aux_lemma_zeta" " => " s:tacticSeq : tactic => withMainContext do
  let goal ← getMainGoal
  let remaining ← Tactic.run goal (evalTactic s)
  unless remaining.isEmpty do
    throwError "Cannot abstract an unfinished proof"
  let value ← instantiateMVars (mkMVar goal)
  if value.hasSorry then
    throwError "Cannot abstract a proof containing a recovery placeholder"
  let value ← mkAuxTheorem (← goal.getType) value (zetaDelta := true)
  goal.assign value

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

variable [T2Space B]

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- Every local witness is chosen once, then used both for the norm bound and exact reconstruction.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- One parameter regularizes the whole finite vertical family, retaining its exact residual. -/
theorem exists_associatedSphereTensorVerticalGlobal_regularization
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')
    (Q : AtlasPseudodifferentialOperator A A' 1)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (J : SmoothBundlePresentation (n := n) (r := a) E)
    (b : Fin J.size → B)
    (hJ : ∀ k, tsupport (J.cutoff k) ⊆ (S.trivialization (b k)).baseSet) :
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
    let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
    ∀ (Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation AT'),
      ∃ (N : Fin J.size → ℕ)
        (L : ∀ k : Fin J.size, Fin (N k) → AtlasPseudodifferentialPiece A A' 1),
        (∀ k, IsAtlasSmoothingOperator A A' (Q.toLinearMap - ∑ j, (L k j).toLinearMap)) ∧
        ∃ (γ : ∀ k : Fin J.size, Fin (N k) → X → ℝ) (hγ : ∀ k j, ContDiff ℝ ∞ (γ k j))
          (hcγ : ∀ k j, HasCompactSupport (γ k j))
          (hsγ : ∀ k j, tsupport (γ k j) ⊆ (J.chart k).target ∩
            (J.chart k).symm ⁻¹' (J.frame k).baseSet)
          (hbγ : ∀ k j, (J.chart k).symm '' tsupport (γ k j) ⊆ (S.trivialization (b k)).baseSet)
          (κ : ∀ k : Fin J.size, Fin (N k) → Y → ℝ) (hκ : ∀ k j, ContDiff ℝ ∞ (κ k j))
          (hcκ : ∀ k j, HasCompactSupport (κ k j))
          (hsκ : ∀ k j, tsupport (κ k j) ⊆ (L k j).chart.target ∩ (L k j).chart.symm ⁻¹'
            (A'.chart (L k j).output.frameIndex).baseSet),
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
          let p (k : Fin J.size) (j : Fin (N k)) :=
            isometricSymbolTransport (productCoordinateSwap n r)
            (tensorCoordinateSwap a (A.rank (L k j).input.frameIndex))
            (tensorCoordinateSwap a (A'.rank (L k j).output.frameIndex)).symm
            (liftedProductSymbol (β k j) (γ k j))
          (∀ k j x, x ∈ tsupport (J.chartCutoff E k).cutoff → γ k j x = 1) ∧
          (∀ k j y, y ∈ tsupport (L k j).output.cutoff → κ k j y = 1) ∧
          (∀ k j, tsupport (κ k j) ⊆ (L k j).chart.symm ⁻¹'
            (A.chart (L k j).input.frameIndex).baseSet) ∧
          ∃ (I : ∀ k : Fin J.size, ∀ j : Fin (N k), AT.smoothSections →ₗ[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L k j).input.frameIndex))))
            (O : ∀ k : Fin J.size, ∀ j : Fin (N k),
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L k j).output.frameIndex)))
                →ₗ[ℂ] AT'.smoothSections),
            (∀ k j w z, I k j w z = (Din k j).localizedFunction w z) ∧
            (∀ k j v z, (O k j v).val z = (Dout k j).extendedFunction v z) ∧
            ∃ (Tj : ∀ k : Fin J.size, Fin (N k) → AT.smoothSections →ₗ[ℂ] AT'.smoothSections)
              (R : (Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0)),
              (∀ k j (w : AT.smoothSections),
                ∃ v : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L k j).output.frameIndex))),
                  (∀ z, quantize (p k j) (I k j w) z = v z) ∧
                  (tsupport v ⊆ EuclideanSpace.finAddEquivProd.symm ''
                    (tsupport (J.chartCutoff E k).cutoff ×ˢ tsupport (L k j).output.cutoff)) ∧
                  Tj k j w = O k j v ∧
                  ∀ x : B, x ∈ (J.chart k).source → x ∈ (S.trivialization (b k)).baseSet →
                    x ∈ (J.frame k).baseSet → ∀ y : OrthogonalSphere r,
                      let q := (S.trivialization (b k)).toOpenPartialHomeomorph.symm (x, 1)
                      (Tj k j w).val (associatedBundleMk G P (OrthogonalSphere r) q y) =
                        ((J.chartCutoff E k).cutoff (J.chart k x) : ℂ) •
                          associatedSphereTensorFiberEquiv S E σ' q y
                          ((tensorSectionOperator (E (projection q)) A.smoothSections
                            A'.smoothSections (L k j).toLinearMap
                            (associatedSphereTensorFiberRestriction (a := a)
                              S E A σ hσ q w)).val y)) ∧
              (∀ w : AT.smoothSections, R (Li.smoothToSobolev 1 w) =
                Lo.smoothToSobolev 0 (∑ k, ∑ j, Tj k j w)) ∧
              ∃ W : Fin J.size → AT.smoothSections →ₗ[ℂ] AT'.smoothSections,
                V = (∑ k, ∑ j, Tj k j) + ∑ k, W k ∧
                (∀ k (w : AT.smoothSections) z,
                  πS z ∉ tsupport (J.cutoff k) → (W k w).val z = 0) ∧
                (∀ k (w : AT.smoothSections) x, x ∈ (J.chart k).source →
                  x ∈ (S.trivialization (b k)).baseSet → x ∈ (J.frame k).baseSet →
                  ∀ y : OrthogonalSphere r,
                    let q := (S.trivialization (b k)).toOpenPartialHomeomorph.symm (x, 1)
                    (W k w).val (associatedBundleMk G P (OrthogonalSphere r) q y) =
                      (J.cutoff k x : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
                        ((tensorSectionOperator (E (projection q)) A.smoothSections
                          A'.smoothSections (Q.toLinearMap - ∑ j, (L k j).toLinearMap)
                          (associatedSphereTensorFiberRestriction (a := a)
                            S E A σ hσ q w)).val y)) ∧
              ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
                ∃ (Qε : ∀ k : Fin J.size, Fin (N k) → AtlasPseudodifferentialOperator AT AT' 1)
                  (U : ∀ k : Fin J.size, ∀ j : Fin (N k),
                    𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L k j).input.frameIndex))) →L[ℂ]
                      𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L k j).output.frameIndex))))
                  (Rε : (Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0)),
                  (∀ k j, (Qε k j).toLinearMap = (O k j).comp ((U k j).toLinearMap.comp (I k j))) ∧
                  (∀ k j v z, U k j v z = quantize
                    (rightProductCutoffSymbol (β k j) (γ k j) ε) v z) ∧
                  (∀ w, Rε (Li.smoothToSobolev 1 w) =
                    Lo.smoothToSobolev 0 (∑ k, ∑ j, (Qε k j).toLinearMap w)) ∧
                  ‖Rε - R‖ ≤ K * ε := by
  as_aux_lemma_zeta =>
    classical
    -- Choose a finite sphere representation and its exact smoothing residual.
    let N : ℕ := Q.isPseudodifferentialOperator.choose
    let L : Fin N → AtlasPseudodifferentialPiece A A' 1 :=
      Q.isPseudodifferentialOperator.choose_spec.choose
    have hrem : IsAtlasSmoothingOperator A A' (Q.toLinearMap - ∑ j, (L j).toLinearMap) :=
      Q.isPseudodifferentialOperator.choose_spec.choose_spec
    have hregularize := exists_associatedSphereTensorVerticalGlobalFamily_regularization
      (a := a) S E A σ A' σ' hσ hσ' Q hQ N L J b hJ
    -- The same family is allowed at every native base slot; its exact residual is retained.
    dsimp only
    intro Li Lo
    exact ⟨fun _ ↦ N, fun _ ↦ L, fun _ ↦ hrem, hregularize Li Lo⟩

end AtiyahSinger
