/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedChartExtensionSupport
public import AtiyahSinger.Analysis.AssociatedTensorVerticalFamilyRegularization
public import AtiyahSinger.Analysis.AssociatedTensorVerticalRemainder
public import AtiyahSinger.Geometry.SmoothBundlePresentationSubordinate

/-!
# Global regularization of a specified vertical family

Public module ID: M0153.

A native base partition subordinate to principal charts assembles local
regularizations of the supplied sphere pieces with one common parameter.
The full vertical operator is the sum of the unregularized local maps and
a supported residual carrying the literal difference from the sphere family.
The cutoff PDOs approximate the local-map sum in the supplied H¹-to-H⁰
operator norm, with cutoffs, coordinate maps and constants fixed before
the positive parameter. Their complete symbols and the residual support
and fiber formulas remain part of the conclusion.
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
set_option maxHeartbeats 8000000 in

set_option synthInstance.maxHeartbeats 200000 in
-- Every local witness is chosen once, then used both for the norm bound and exact reconstruction.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- One parameter regularizes the specified vertical family and retains its exact residual. -/
theorem exists_associatedSphereTensorVerticalGlobalFamily_regularization
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')
    (Q : AtlasPseudodifferentialOperator A A' 1)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (N₀ : ℕ) (L₀ : Fin N₀ → AtlasPseudodifferentialPiece A A' 1)
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
      ∃ (γ : ∀ _k : Fin J.size, Fin N₀ → X → ℝ) (hγ : ∀ k j, ContDiff ℝ ∞ (γ k j))
          (hcγ : ∀ k j, HasCompactSupport (γ k j))
          (hsγ : ∀ k j, tsupport (γ k j) ⊆ (J.chart k).target ∩
            (J.chart k).symm ⁻¹' (J.frame k).baseSet)
          (hbγ : ∀ k j, (J.chart k).symm '' tsupport (γ k j) ⊆ (S.trivialization (b k)).baseSet)
          (κ : ∀ _k : Fin J.size, Fin N₀ → Y → ℝ) (hκ : ∀ k j, ContDiff ℝ ∞ (κ k j))
          (hcκ : ∀ k j, HasCompactSupport (κ k j))
          (hsκ : ∀ k j, tsupport (κ k j) ⊆ (L₀ j).chart.target ∩ (L₀ j).chart.symm ⁻¹'
            (A'.chart (L₀ j).output.frameIndex).baseSet),
          let Co (k : Fin J.size) (j : Fin N₀) : BundleChartCutoff E (J.chart k) :=
            { J.chartCutoff E k with
              cutoff := γ k j
              smooth_cutoff := hγ k j
              compact_support := hcγ k j
              support_subset := hsγ k j }
          let Ko (k : Fin J.size) (j : Fin N₀) : AtlasChartCutoff A' (L₀ j).chart :=
            { (L₀ j).output with
              cutoff := κ k j
              smooth_cutoff := hκ k j
              compact_support := hcκ k j
              support_subset := hsκ k j }
          let Din (k : Fin J.size) (j : Fin N₀) := associatedSphereTensorChartCutoff S E A σ hσ
            (b k) (J.chart k) (J.chartCutoff E k)
              (fun _ hx ↦ hJ k (J.chartCutoff_support_subset E k hx)) (L₀ j).chart (L₀ j).input
          let Dout (k : Fin J.size) (j : Fin N₀) :=
            associatedSphereTensorChartCutoff S E A' σ' hσ'
            (b k) (J.chart k) (Co k j) (hbγ k j) (L₀ j).chart (Ko k j)
          let α (_k : Fin J.size) (j : Fin N₀) :=
            zeroExtendedSymbol Set.univ (L₀ j).output.cutoff (L₀ j).symbol
          let β (k : Fin J.size) (j : Fin N₀) :
              SymbolFunction r (A.rank (L₀ j).input.frameIndex * a)
              (A'.rank (L₀ j).output.frameIndex * a) :=
            fun y η ↦ tensorIdentitySymbolMap (A.rank (L₀ j).input.frameIndex)
              (A'.rank (L₀ j).output.frameIndex) a (α k j y η)
          let p (k : Fin J.size) (j : Fin N₀) :=
            isometricSymbolTransport (productCoordinateSwap n r)
            (tensorCoordinateSwap a (A.rank (L₀ j).input.frameIndex))
            (tensorCoordinateSwap a (A'.rank (L₀ j).output.frameIndex)).symm
            (liftedProductSymbol (β k j) (γ k j))
          (∀ k j x, x ∈ tsupport (J.chartCutoff E k).cutoff → γ k j x = 1) ∧
          (∀ k j y, y ∈ tsupport (L₀ j).output.cutoff → κ k j y = 1) ∧
          (∀ k j, tsupport (κ k j) ⊆ (L₀ j).chart.symm ⁻¹'
            (A.chart (L₀ j).input.frameIndex).baseSet) ∧
          ∃ (I : ∀ _k : Fin J.size, ∀ j : Fin N₀, AT.smoothSections →ₗ[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L₀ j).input.frameIndex))))
            (O : ∀ _k : Fin J.size, ∀ j : Fin N₀,
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L₀ j).output.frameIndex)))
                →ₗ[ℂ] AT'.smoothSections),
            (∀ k j w z, I k j w z = (Din k j).localizedFunction w z) ∧
            (∀ k j v z, (O k j v).val z = (Dout k j).extendedFunction v z) ∧
            ∃ (Tj : ∀ _k : Fin J.size, Fin N₀ → AT.smoothSections →ₗ[ℂ] AT'.smoothSections)
              (R : (Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0)),
              (∀ k j (w : AT.smoothSections),
                ∃ v : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L₀ j).output.frameIndex))),
                  (∀ z, quantize (p k j) (I k j w) z = v z) ∧
                  (tsupport v ⊆ EuclideanSpace.finAddEquivProd.symm ''
                    (tsupport (J.chartCutoff E k).cutoff ×ˢ tsupport (L₀ j).output.cutoff)) ∧
                  Tj k j w = O k j v ∧
                  ∀ x : B, x ∈ (J.chart k).source → x ∈ (S.trivialization (b k)).baseSet →
                    x ∈ (J.frame k).baseSet → ∀ y : OrthogonalSphere r,
                      let q := (S.trivialization (b k)).toOpenPartialHomeomorph.symm (x, 1)
                      (Tj k j w).val (associatedBundleMk G P (OrthogonalSphere r) q y) =
                        ((J.chartCutoff E k).cutoff (J.chart k x) : ℂ) •
                          associatedSphereTensorFiberEquiv S E σ' q y
                          ((tensorSectionOperator (E (projection q)) A.smoothSections
                            A'.smoothSections (L₀ j).toLinearMap
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
                          A'.smoothSections (Q.toLinearMap - ∑ j, (L₀ j).toLinearMap)
                          (associatedSphereTensorFiberRestriction (a := a)
                            S E A σ hσ q w)).val y)) ∧
              ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
                ∃ (Qε : ∀ _k : Fin J.size, Fin N₀ → AtlasPseudodifferentialOperator AT AT' 1)
                  (U : ∀ _k : Fin J.size, ∀ j : Fin N₀,
                    𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L₀ j).input.frameIndex))) →L[ℂ]
                      𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L₀ j).output.frameIndex))))
                  (Rε : (Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0)),
                  (∀ k j, (Qε k j).toLinearMap = (O k j).comp ((U k j).toLinearMap.comp (I k j))) ∧
                  (∀ k j v z, U k j v z = quantize
                    (rightProductCutoffSymbol (β k j) (γ k j) ε) v z) ∧
                  (∀ w, Rε (Li.smoothToSobolev 1 w) =
                    Lo.smoothToSobolev 0 (∑ k, ∑ j, (Qε k j).toLinearMap w)) ∧
                  ‖Rε - R‖ ≤ K * ε := by
  as_aux_lemma_zeta =>
    classical
    have hfiniteNorm {𝓔 : Type _} [NormedAddCommGroup 𝓔] {ι : Type _} [Fintype ι]
        (f g : ι → 𝓔) (c : ι → ℝ) (ε : ℝ)
        (h : ∀ i, ‖f i - g i‖ ≤ c i * ε) :
        ‖(∑ i, f i) - ∑ i, g i‖ ≤ (∑ i, c i) * ε := by
      calc
        ‖(∑ i, f i) - ∑ i, g i‖ = ‖∑ i, (f i - g i)‖ :=
          congrArg norm (Finset.sum_sub_distrib (s := Finset.univ) f g).symm
        _ ≤ ∑ i, ‖f i - g i‖ := norm_sum_le _ _
        _ ≤ ∑ i, c i * ε := Finset.sum_le_sum (fun i _ ↦ h i)
        _ = (∑ i, c i) * ε := (Finset.sum_mul _ _ _).symm
    have hC (k : Fin J.size) :
        (J.chart k).symm '' tsupport (J.chartCutoff E k).cutoff ⊆
          (S.trivialization (b k)).baseSet :=
      fun _ hx ↦ hJ k (J.chartCutoff_support_subset E k hx)
    -- Apply local regularization to each base chart with the supplied sphere family.
    have hdata (k : Fin J.size) := exists_associatedSphereTensorVerticalFamily_regularization
      (a := a) S E A σ A' σ' hσ hσ' (b k) (J.chart k) (J.chart_mem_atlas k)
      (J.chartCutoff E k) (hC k) N₀ L₀
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
    -- Relate support of the coordinate zero extension to its base projection.
    have hzeroTensor (b₀ : B) (c : OpenPartialHomeomorph B X)
        (Co : BundleChartCutoff E c)
        (hb : c.symm '' tsupport Co.cutoff ⊆ (S.trivialization b₀).baseSet)
        (d : OpenPartialHomeomorph (OrthogonalSphere r) Y)
        (Ko : AtlasChartCutoff A' d)
        (v : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank Ko.frameIndex))))
        (K : Set X) (hv : ∀ x ∈ tsupport v, (ef x).1 ∈ K)
        (z : Z) (hz : πS z ∉ c.symm '' K) :
        (associatedSphereTensorChartCutoff S E A' σ' hσ' b₀ c Co hb d Ko).extendedFunction
          v z = 0 := by
      exact associatedSphereChart_extendedFunction_eq_zero_of_notMem_base S b₀ c d T' AT'
        (associatedSphereTensorChartCutoff S E A' σ' hσ' b₀ c Co hb d Ko) v K hv z hz
    let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
    dsimp only
    intro Li Lo
    change AtlasBundlePresentation AT at Li
    change AtlasBundlePresentation AT' at Lo
    -- Select the local cutoffs, maps and estimates for the supplied sphere pieces.
    choose γ hγ hcγ hsγ hbγ κ hκ hcκ hsκ hγone hκone hκin I O hI hO Tj Rj
      hTj hRj Kj hKj hpositive using fun k ↦ hdata k Li Lo
    let N (_k : Fin J.size) := N₀
    let L (_k : Fin J.size) := L₀
    -- The full coordinate Schwartz support controls the original base support.
    have hTzero (k : Fin J.size) (j : Fin (N k)) (w : AT.smoothSections) (z : Z)
        (hz : πS z ∉ tsupport (J.cutoff k)) : (Tj k j w).val z = 0 := by
      let v := (hTj k j w).choose
      have hv := (hTj k j w).choose_spec
      have hbase (x : XY) (hx : x ∈ tsupport v) :
          (ef x).1 ∈ tsupport (J.chartCutoff E k).cutoff := by
        obtain ⟨p, hp, hpx⟩ := hv.2.1 hx
        have hp' : ef x = p := by rw [← hpx, ef.apply_symm_apply]
        rw [hp']
        exact hp.1
      have hz' : πS z ∉ (J.chart k).symm '' tsupport (J.chartCutoff E k).cutoff :=
        fun h ↦ hz (J.chartCutoff_support_subset E k h)
      rw [hv.2.2.1, hO k j v z]
      let Co : BundleChartCutoff E (J.chart k) :=
        { J.chartCutoff E k with
          cutoff := γ k j
          smooth_cutoff := hγ k j
          compact_support := hcγ k j
          support_subset := hsγ k j }
      let Ko : AtlasChartCutoff A' (L₀ j).chart :=
        { (L₀ j).output with
          cutoff := κ k j
          smooth_cutoff := hκ k j
          compact_support := hcκ k j
          support_subset := hsκ k j }
      exact hzeroTensor (b k) (J.chart k) Co (hbγ k j) (L₀ j).chart Ko v
        (tsupport (J.chartCutoff E k).cutoff) hbase z hz'
    have hTreturn (k : Fin J.size) (j : Fin (N k)) (w : AT.smoothSections)
        (x : B) (hx : x ∈ (J.chart k).source)
        (hxb : x ∈ (S.trivialization (b k)).baseSet) (hxe : x ∈ (J.frame k).baseSet)
        (y : OrthogonalSphere r) :
        let q := (S.trivialization (b k)).toOpenPartialHomeomorph.symm (x, 1)
        (Tj k j w).val (associatedBundleMk G P (OrthogonalSphere r) q y) =
          (J.cutoff k x : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
            ((tensorSectionOperator (E (projection q)) A.smoothSections A'.smoothSections
              (L k j).toLinearMap (associatedSphereTensorFiberRestriction (a := a)
                S E A σ hσ q w)).val y) := by
      have hweight : (J.chartCutoff E k).cutoff (J.chart k x) = J.cutoff k x := by
        simpa only [ite_eq_left hx] using J.chartCutoff_pullback E k x
      have hreturn := (hTj k j w).choose_spec.2.2.2 x hx hxb hxe y
      simpa only [hweight] using hreturn
    have hremainder := exists_associatedSphereTensorVertical_remainders (a := a)
      S E A σ A' σ' hσ hσ' Q hQ J b N L Tj hTzero hTreturn
    let W : Fin J.size → AT.smoothSections →ₗ[ℂ] AT'.smoothSections := hremainder.choose
    have hW := hremainder.choose_spec.1
    have hWzero := hremainder.choose_spec.2.1
    have hWreturn := hremainder.choose_spec.2.2
    let R : (Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0) := ∑ k, Rj k
    refine ⟨γ, hγ, hcγ, hsγ, hbγ, κ, hκ, hcκ, hsκ, ?_⟩
    refine ⟨hγone, hκone, hκin, I, O, hI, hO, Tj, R, hTj, ?_, ?_⟩
    · -- The same geometric Sobolev realization acts on the actual finite sum.
      intro w
      calc
        R (Li.smoothToSobolev 1 w) = ∑ k, Rj k (Li.smoothToSobolev 1 w) :=
          sum_apply Finset.univ (fun k ↦ Rj k) (Li.smoothToSobolev 1 w)
        _ = ∑ k, Lo.smoothToSobolev 0 (∑ j, Tj k j w) :=
          Finset.sum_congr rfl (fun k _ ↦ hRj k w)
        _ = Lo.smoothToSobolev 0 (∑ k, ∑ j, Tj k j w) :=
          (map_sum (Lo.smoothToSobolev 0) (fun k ↦ ∑ j, Tj k j w) Finset.univ).symm
    · refine ⟨W, hW, hWzero, hWreturn,
        ∑ k, Kj k, Finset.sum_nonneg (fun k _ ↦ hKj k), ?_⟩
      intro ε hε hεone
      choose Qε U Rε hQε hU hRε herror using fun k ↦ hpositive k ε hε hεone
      refine ⟨Qε, U, ∑ k, Rε k, hQε, hU, ?_, ?_⟩
      · intro w
        calc
          (∑ k, Rε k) (Li.smoothToSobolev 1 w) = ∑ k, Rε k (Li.smoothToSobolev 1 w) :=
            sum_apply Finset.univ (fun k ↦ Rε k) (Li.smoothToSobolev 1 w)
          _ = ∑ k, Lo.smoothToSobolev 0 (∑ j, (Qε k j).toLinearMap w) :=
            Finset.sum_congr rfl (fun k _ ↦ hRε k w)
          _ = Lo.smoothToSobolev 0 (∑ k, ∑ j, (Qε k j).toLinearMap w) :=
            (map_sum (Lo.smoothToSobolev 0)
              (fun k ↦ ∑ j, (Qε k j).toLinearMap w) Finset.univ).symm
      · -- Apply the finite numerical estimate to these same actual bounded maps.
        exact hfiniteNorm (𝓔 := (Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0)) (ι := Fin J.size)
          Rε Rj Kj ε herror

end AtiyahSinger
