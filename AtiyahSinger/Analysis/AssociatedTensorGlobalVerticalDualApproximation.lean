/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalRegularization
public import AtiyahSinger.Analysis.AssociatedTensorVerticalDualApproximation

/-!
# Negative-order approximation with the fixed global vertical residual

Public module ID: M0151.

A native base partition and fixed sphere family give a uniform H⁰-to-H⁻¹
error for the global vertical operator. The same supported residual occurs
on both sides and cancels algebraically. The cutoff and input/output maps
remain fixed, so this forward estimate also supports comparison with the
metric adjoints of the same regularized family.
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

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The original global vertical operator is approximated with its literal residual retained. -/
theorem associatedSphereTensorVerticalGlobal_error_sobolev_neg_one_bound
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')
    (Q : AtlasPseudodifferentialOperator A A' 1)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (N : ℕ) (L : Fin N → AtlasPseudodifferentialPiece A A' 1)
    (J : SmoothBundlePresentation (n := n) (r := a) E)
    (b : Fin J.size → B)
    (hJ : ∀ k, tsupport (J.cutoff k) ⊆ (S.trivialization (b k)).baseSet)
    (Co : ∀ k : Fin J.size, Fin N → BundleChartCutoff (r := a) E (J.chart k))
    (hCo : ∀ k j, (J.chart k).symm '' tsupport (Co k j).cutoff ⊆
      (S.trivialization (b k)).baseSet)
    (κ : Fin J.size → Fin N → Y → ℝ) (hκ : ∀ k j, ContDiff ℝ ∞ (κ k j))
    (hκK : ∀ k j, HasCompactSupport (κ k j))
    (hκsupport : ∀ k j, tsupport (κ k j) ⊆ (L j).chart.target ∩
      (L j).chart.symm ⁻¹' (A'.chart (L j).output.frameIndex).baseSet) :
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
    let Din (k : Fin J.size) (j : Fin N) :=
      associatedSphereTensorChartCutoff S E A σ hσ (b k) (J.chart k) (J.chartCutoff E k)
        (fun _ hx ↦ hJ k (J.chartCutoff_support_subset E k hx)) (L j).chart (L j).input
    let Ko (k : Fin J.size) (j : Fin N) : AtlasChartCutoff A' (L j).chart :=
      { (L j).output with
        cutoff := κ k j
        smooth_cutoff := hκ k j
        compact_support := hκK k j
        support_subset := hκsupport k j }
    let Dout (k : Fin J.size) (j : Fin N) :=
      associatedSphereTensorChartCutoff S E A' σ' hσ' (b k) (J.chart k)
        (Co k j) (hCo k j) (L j).chart (Ko k j)
    let α (j : Fin N) := zeroExtendedSymbol Set.univ (L j).output.cutoff (L j).symbol
    let β (j : Fin N) : SymbolFunction r (A.rank (L j).input.frameIndex * a)
        (A'.rank (L j).output.frameIndex * a) :=
      fun y η ↦ tensorIdentitySymbolMap (A.rank (L j).input.frameIndex)
        (A'.rank (L j).output.frameIndex) a (α j y η)
    let p (k : Fin J.size) (j : Fin N) := isometricSymbolTransport (productCoordinateSwap n r)
      (tensorCoordinateSwap a (A.rank (L j).input.frameIndex))
      (tensorCoordinateSwap a (A'.rank (L j).output.frameIndex)).symm
      (liftedProductSymbol (β j) (Co k j).cutoff)
    ∀ (I : Fin J.size → ∀ j : Fin N, AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L j).input.frameIndex))))
      (O : Fin J.size → ∀ j : Fin N,
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L j).output.frameIndex)))
          →ₗ[ℂ] AT'.smoothSections),
      (∀ k j w z, I k j w z = (Din k j).localizedFunction w z) →
      (∀ k j v z, (O k j v).val z = (Dout k j).extendedFunction v z) →
      ∀ (Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation AT')
        (Tj : Fin J.size → Fin N → AT.smoothSections →ₗ[ℂ] AT'.smoothSections),
        (∀ k j w, ∃ v : 𝓢(XY,
          EuclideanSpace ℂ (Fin (a * A'.rank (L j).output.frameIndex))),
          (∀ z, quantize (p k j) (I k j w) z = v z) ∧ Tj k j w = O k j v) →
        ∀ W : Fin J.size → AT.smoothSections →ₗ[ℂ] AT'.smoothSections,
          V = (∑ k, ∑ j, Tj k j) + ∑ k, W k →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            ∀ U : Fin J.size → ∀ j : Fin N,
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L j).input.frameIndex))) →L[ℂ]
                𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L j).output.frameIndex))),
              (∀ k j v z, U k j v z =
                quantize (rightProductCutoffSymbol (β j) (Co k j).cutoff ε) v z) →
              ∀ w : AT.smoothSections,
                ‖Lo.smoothToSobolev (-1)
                  (V w - ((∑ k, ∑ j, O k j (U k j (I k j w))) + ∑ k, W k w))‖ ≤
                    C * ε * ‖Li.smoothToSobolev 0 w‖ := by
  as_aux_lemma_zeta =>
    classical
    -- Apply the local negative-order estimate in every base chart.
    have hlocal (k : Fin J.size) :=
      associatedSphereTensorVerticalFamily_error_sobolev_neg_one_bound
        S E A σ A' σ' hσ hσ' (b k) (J.chart k) (J.chart_mem_atlas k) (J.chartCutoff E k)
        (fun _ hx ↦ hJ k (J.chartCutoff_support_subset E k hx)) N L
        (Co k) (hCo k) (κ k) (hκ k) (hκK k) (hκsupport k)
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
    let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
    dsimp only
    intro I O hI hO Li Lo Tj hTj W hV
    choose Ck hCk hbound using
      fun k ↦ hlocal k (I k) (O k) (hI k) (hO k) Li Lo (Tj k) (hTj k)
    refine ⟨∑ k, Ck k, Finset.sum_nonneg (fun k _ ↦ hCk k), ?_⟩
    intro ε hε hεone U hU w
    have hvalue : V w = (∑ k, ∑ j, Tj k j w) + ∑ k, W k w := by
      have hv := congrArg (fun R : AT.smoothSections →ₗ[ℂ] AT'.smoothSections ↦ R w) hV
      simpa only [LinearMap.add_apply, LinearMap.sum_apply] using hv
    -- The same original residual occurs on both sides of the approximation.
    have herror : V w - ((∑ k, ∑ j, O k j (U k j (I k j w))) + ∑ k, W k w) =
        ∑ k, ((∑ j, Tj k j w) - ∑ j, O k j (U k j (I k j w))) :=
      (congrArg (fun z : AT'.smoothSections ↦
        z - ((∑ k, ∑ j, O k j (U k j (I k j w))) + ∑ k, W k w)) hvalue).trans
        ((add_sub_add_right_eq_sub _ _ _).trans
          (Finset.sum_sub_distrib (s := Finset.univ) (fun k ↦ ∑ j, Tj k j w)
            (fun k ↦ ∑ j, O k j (U k j (I k j w)))).symm)
    have hcoordinate := (congrArg (Lo.smoothToSobolev (-1)) herror).trans
      (map_sum (Lo.smoothToSobolev (-1))
        (fun k ↦ (∑ j, Tj k j w) - ∑ j, O k j (U k j (I k j w))) Finset.univ)
    have hn := norm_sum_le Finset.univ
      (fun k ↦ Lo.smoothToSobolev (-1)
        ((∑ j, Tj k j w) - ∑ j, O k j (U k j (I k j w))))
    have hp := Finset.sum_le_sum (s := Finset.univ)
      (fun k _ ↦ hbound k ε hε hεone (U k) (hU k) w)
    have heq : (∑ k, Ck k * ε * ‖Li.smoothToSobolev 0 w‖) =
        (∑ k, Ck k) * ε * ‖Li.smoothToSobolev 0 w‖ :=
      (Finset.sum_mul Finset.univ (fun k ↦ Ck k * ε) ‖Li.smoothToSobolev 0 w‖).symm.trans
        (congrArg (· * ‖Li.smoothToSobolev 0 w‖) (Finset.sum_mul Finset.univ Ck ε).symm)
    exact (congrArg norm hcoordinate).trans_le (hn.trans (hp.trans_eq heq))

end AtiyahSinger

