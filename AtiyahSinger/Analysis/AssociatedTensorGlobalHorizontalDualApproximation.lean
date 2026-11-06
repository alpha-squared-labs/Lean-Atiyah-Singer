/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalLift
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalDualApproximation

/-!
# Negative-order error for the original global horizontal cutoff

Public module ID: M0146.

All original principal pieces and the same sphere partition are used in the
finite sum. Their literal cutoff errors give a uniform H⁰-to-H⁻¹ estimate
for the full original horizontal lift. The chosen cutoffs and input/output
maps are parameters, so the estimate applies to the already constructed
regularization without reselecting its witnesses.
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

variable [SecondCountableTopology B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

namespace PrincipalPseudodifferentialLocalization

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The full original horizontal cutoff error is uniformly small from H⁰ to H⁻¹. -/
theorem horizontalLift_error_sobolev_neg_one_bound
    (L : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (J : AtlasBundlePresentation A)
    (Co : ∀ k : Fin L.size, BundleChartCutoff (r := a') E' (L.piece k).chart)
    (hCoFrame : ∀ k, (Co k).frame = (L.piece k).output.frame)
    (hCo : ∀ k, (L.piece k).chart.symm '' tsupport (Co k).cutoff ⊆
      (S.trivialization (L.center k)).baseSet)
    (hCoOne : ∀ k x, x ∈ tsupport (L.piece k).output.cutoff → (Co k).cutoff x = 1)
    (κ : Fin L.size → Fin J.size → Y → ℝ)
    (hκ : ∀ k j, ContDiff ℝ ∞ (κ k j)) (hκK : ∀ k j, HasCompactSupport (κ k j))
    (hκsupport : ∀ k j, tsupport (κ k j) ⊆ (J.chart j).target ∩
      (J.chart j).symm ⁻¹' (A.chart (J.frameIndex j)).baseSet)
    (hκone : ∀ k j y, y ∈ tsupport (J.chartCutoff j).cutoff → κ k j y = 1) :
    letI := modelTopology V₀ E
    letI := modelTopology V₁ E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT : SmoothComplexBundleAtlas (n := n + r) T :=
      associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
      associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
    let Kout (k : Fin L.size) (j : Fin J.size) : AtlasChartCutoff A (J.chart j) :=
      ⟨J.frameIndex j, κ k j, hκ k j, hκK k j, hκsupport k j⟩
    let Din (k : Fin L.size) (j : Fin J.size) :=
      associatedSphereTensorChartCutoff S E A σ hσ (L.center k) (L.piece k).chart
        (L.piece k).input (fun _ ⟨x, hx, hxy⟩ ↦
          L.piece_support k ⟨x, Or.inr hx, hxy⟩) (J.chart j) (J.chartCutoff j)
    let Dout (k : Fin L.size) (j : Fin J.size) :=
      associatedSphereTensorChartCutoff S E' A σ hσ (L.center k) (L.piece k).chart
        (Co k) (hCo k) (J.chart j) (Kout k j)
    let α (k : Fin L.size) :=
      zeroExtendedSymbol Set.univ (L.piece k).output.cutoff (L.piece k).symbol
    ∀ (I : Fin L.size → ∀ j : Fin J.size, AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))))
      (O : Fin L.size → ∀ j : Fin J.size,
        𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))) →ₗ[ℂ] AT'.smoothSections),
      (∀ k j w z, I k j w z = (Din k j).localizedFunction w z) →
      (∀ k j v z, (O k j v).val z = (Dout k j).extendedFunction v z) →
      ∀ (Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation AT'),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∀ U : Fin L.size → ∀ j : Fin J.size,
            𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))) →L[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))),
            (∀ k j v z, U k j v z = quantize
              (fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
                (productCutoffSymbol (α k) (κ k j) ε x ξ)) v z) →
            ∀ w : AT.smoothSections,
              ‖Lo.smoothToSobolev (-1)
                (L.horizontalLift S E A σ E' hσ w - ∑ k, ∑ j, O k j (U k j (I k j w)))‖ ≤
                  C * ε * ‖Li.smoothToSobolev 0 w‖ := by
  classical
  have hinput (k : Fin L.size) :
      (L.piece k).chart.symm '' tsupport (L.piece k).input.cutoff ⊆
        (S.trivialization (L.center k)).baseSet :=
    fun _ ⟨x, hx, hxy⟩ ↦ L.piece_support k ⟨x, Or.inr hx, hxy⟩
  have houtput (k : Fin L.size) :
      (L.piece k).chart.symm '' tsupport (L.piece k).output.cutoff ⊆
        (S.trivialization (L.center k)).baseSet :=
    fun _ ⟨x, hx, hxy⟩ ↦ L.piece_support k ⟨x, Or.inl hx, hxy⟩
  -- Apply the local H⁰-to-H⁻¹ error bound to each principal piece.
  have hlocal (k : Fin L.size) := associatedSphereTensorLocalHorizontal_error_sobolev_neg_one_bound
    (a := a) S E A σ E' (L.piece k) hσ (L.center k) (hinput k) (houtput k)
    (L.inputCutoff k) (L.smooth_inputCutoff k) (L.inputCutoff_support k)
    (L.inputCutoff_eq_one k) J (Co k) (hCoFrame k) (hCo k) (hCoOne k)
    (κ k) (hκ k) (hκK k) (hκsupport k) (hκone k)
  let := modelTopology V₀ E
  let := modelTopology V₁ E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace e.symm Z
  let := isManifold_linearModelChartedSpace e.symm Z
  let AT : SmoothComplexBundleAtlas (n := n + r) T :=
    associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
    associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
  dsimp only
  intro I O hI hO Li Lo
  -- Fix every local constant before epsilon, with one common target Sobolev presentation.
  choose Ck hCk hbound using fun k ↦ hlocal k (I k) (O k) (hI k) (hO k) Li Lo
  refine ⟨∑ k, Ck k, Finset.sum_nonneg (fun k _ ↦ hCk k), ?_⟩
  intro ε hε hεone U hU w
  let H (k : Fin L.size) : AT.smoothSections →ₗ[ℂ] AT'.smoothSections :=
    associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' (L.piece k)
      hσ (L.center k) (L.inputCutoff k) (L.smooth_inputCutoff k)
      (L.inputCutoff_support k) (houtput k)
  have hglobal : L.horizontalLift S E A σ E' hσ w = ∑ k, H k w :=
    LinearMap.sum_apply Finset.univ H w
  have herror : L.horizontalLift S E A σ E' hσ w - ∑ k, ∑ j, O k j (U k j (I k j w)) =
      ∑ k, (H k w - ∑ j, O k j (U k j (I k j w))) :=
    (congrArg (fun z : AT'.smoothSections ↦ z - ∑ k, ∑ j, O k j (U k j (I k j w)))
      hglobal).trans (Finset.sum_sub_distrib (s := Finset.univ) (fun k ↦ H k w)
        (fun k ↦ ∑ j, O k j (U k j (I k j w)))).symm
  have hcoordinate := (congrArg (Lo.smoothToSobolev (-1)) herror).trans
    (map_sum (Lo.smoothToSobolev (-1))
      (fun k ↦ H k w - ∑ j, O k j (U k j (I k j w))) Finset.univ)
  -- Sum the original section errors in this same negative-order norm.
  have hn := norm_sum_le Finset.univ
    (fun k ↦ Lo.smoothToSobolev (-1) (H k w - ∑ j, O k j (U k j (I k j w))))
  have hp := Finset.sum_le_sum (s := Finset.univ)
    (fun k _ ↦ hbound k ε hε hεone (U k) (hU k) w)
  have heq : (∑ k, Ck k * ε * ‖Li.smoothToSobolev 0 w‖) =
      (∑ k, Ck k) * ε * ‖Li.smoothToSobolev 0 w‖ :=
    (Finset.sum_mul Finset.univ (fun k ↦ Ck k * ε) ‖Li.smoothToSobolev 0 w‖).symm.trans
      (congrArg (· * ‖Li.smoothToSobolev 0 w‖) (Finset.sum_mul Finset.univ Ck ε).symm)
  exact (congrArg norm hcoordinate).trans_le (hn.trans (hp.trans_eq heq))

end PrincipalPseudodifferentialLocalization

end AtiyahSinger
