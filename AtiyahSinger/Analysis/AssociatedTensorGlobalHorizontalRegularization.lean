/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalLift
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalRegularization

/-!
# Global regularization of the specified horizontal lift

Public module ID: M0147.

A finite principal localization and a fixed sphere presentation determine
product-cutoff regularizations of the horizontal lift. The cutoffs, input/output
maps, limiting extension and error constant are chosen independently of the
positive parameter. For each parameter at most one, the local cutoff PDOs
retain their complete amplified symbols, and their finite sum approximates
the global lift in the supplied H¹-to-H⁰ norm with a linear error bound.
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

namespace PrincipalPseudodifferentialLocalization

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original finite horizontal lift is the norm limit of its actual local cutoff PDOs. -/
theorem exists_horizontalLift_regularization
    (L : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (J : AtlasBundlePresentation A) :
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
    ∀ (Li : AtlasBundlePresentation (n := n + r) (M := Z) (E := T) AT)
      (Lo : AtlasBundlePresentation (n := n + r) (M := Z) (E := T') AT'),
      ∃ (Co : ∀ k : Fin L.size, BundleChartCutoff (r := a') E' (L.piece k).chart)
        (hCo : ∀ k, (L.piece k).chart.symm '' tsupport (Co k).cutoff ⊆
          (S.trivialization (L.center k)).baseSet)
        (κ : Fin L.size → Fin J.size → Y → ℝ)
        (hκ : ∀ k j, ContDiff ℝ ∞ (κ k j))
        (hκK : ∀ k j, HasCompactSupport (κ k j))
        (hκsupport : ∀ k j, tsupport (κ k j) ⊆ (J.chart j).target ∩
          (J.chart j).symm ⁻¹' (A.chart (J.frameIndex j)).baseSet),
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
        (∀ k, (Co k).frame = (L.piece k).output.frame) ∧
        (∀ k, tsupport (Co k).cutoff ⊆
          (L.piece k).chart.symm ⁻¹' (L.piece k).input.frame.baseSet) ∧
        (∀ k x, x ∈ tsupport (L.piece k).output.cutoff → (Co k).cutoff x = 1) ∧
        (∀ k j y, y ∈ tsupport (J.chartCutoff j).cutoff → κ k j y = 1) ∧
        ∃ (I : Fin L.size → ∀ j : Fin J.size, AT.smoothSections →ₗ[ℂ]
            𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))))
          (O : Fin L.size → ∀ j : Fin J.size,
            𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j))))
              →ₗ[ℂ] AT'.smoothSections),
          (∀ k j w z, I k j w z = (Din k j).localizedFunction w z) ∧
          (∀ k j v z, (O k j v).val z = (Dout k j).extendedFunction v z) ∧
          ∃ R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0,
            (∀ w : AT.smoothSections, R (Li.smoothToSobolev 1 w) =
              Lo.smoothToSobolev 0 (L.horizontalLift S E A σ E' hσ w)) ∧
            ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
              ∃ (Q : Fin L.size → Fin J.size → AtlasPseudodifferentialOperator AT AT' 1)
                (U : Fin L.size → ∀ j : Fin J.size,
                  𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))) →L[ℂ]
                    𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))))
                (Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0),
                (∀ k j, (Q k j).toLinearMap =
                  (O k j).comp ((U k j).toLinearMap.comp (I k j))) ∧
                (∀ k j v z, U k j v z = quantize
                  (fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
                    (productCutoffSymbol (α k) (κ k j) ε x ξ)) v z) ∧
                (∀ w, Rε (Li.smoothToSobolev 1 w) =
                  Lo.smoothToSobolev 0 (∑ k, ∑ j, (Q k j).toLinearMap w)) ∧
                  ‖Rε - R‖ ≤ C * ε := by
  classical
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
  intro Li Lo
  change AtlasBundlePresentation AT at Li
  change AtlasBundlePresentation AT' at Lo
  -- Every local regularization uses the stored piece and its original base plateau.
  have hinput (k : Fin L.size) :
      (L.piece k).chart.symm '' tsupport (L.piece k).input.cutoff ⊆
        (S.trivialization (L.center k)).baseSet :=
    fun _ ⟨x, hx, hxy⟩ ↦ L.piece_support k ⟨x, Or.inr hx, hxy⟩
  have houtput (k : Fin L.size) :
      (L.piece k).chart.symm '' tsupport (L.piece k).output.cutoff ⊆
        (S.trivialization (L.center k)).baseSet :=
    fun _ ⟨x, hx, hxy⟩ ↦ L.piece_support k ⟨x, Or.inl hx, hxy⟩
  have hlocal (k : Fin L.size) := exists_associatedSphereTensorLocalHorizontal_regularization
    (a := a) S E A σ E' (L.piece k) hσ (L.center k) (hinput k) (houtput k)
    (L.inputCutoff k) (L.smooth_inputCutoff k) (L.inputCutoff_support k)
    (L.inputCutoff_eq_one k) J Li Lo
  choose Co hCo κ hκ hκK hκsupport hCoFrame hCoInput hCoOne hκone I O hI hO
    Rk hRk Ck hCk hbound using hlocal
  let H (k : Fin L.size) : AT.smoothSections →ₗ[ℂ] AT'.smoothSections :=
    associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' (L.piece k)
      hσ (L.center k) (L.inputCutoff k) (L.smooth_inputCutoff k)
      (L.inputCutoff_support k) (houtput k)
  change ∀ k w, Rk k (Li.smoothToSobolev 1 w) = Lo.smoothToSobolev 0 (H k w) at hRk
  let R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := ∑ k, Rk k
  refine ⟨Co, hCo, κ, hκ, hκK, hκsupport, hCoFrame, hCoInput, hCoOne, hκone,
    I, O, hI, hO, R, ?_, ∑ k, Ck k, Finset.sum_nonneg (fun k _ ↦ hCk k), ?_⟩
  · -- The limiting sum is the unchanged global horizontal map, including every original piece.
    intro w
    change (∑ k, Rk k) (Li.smoothToSobolev 1 w) = _
    have hglobal : (∑ k, H k w) = L.horizontalLift S E A σ E' hσ w := by
      change (∑ k, H k w) = (∑ k, H k) w
      exact (LinearMap.sum_apply Finset.univ H w).symm
    calc
      (∑ k, Rk k) (Li.smoothToSobolev 1 w) =
          ∑ k, Rk k (Li.smoothToSobolev 1 w) :=
        sum_apply Finset.univ Rk (Li.smoothToSobolev 1 w)
      _ = ∑ k, Lo.smoothToSobolev 0 (H k w) :=
        Finset.sum_congr rfl (fun k _ ↦ hRk k w)
      _ = Lo.smoothToSobolev 0 (∑ k, H k w) :=
        (map_sum (Lo.smoothToSobolev 0) (fun k ↦ H k w) Finset.univ).symm
      _ = _ := congrArg (Lo.smoothToSobolev 0) hglobal
  · intro ε hε hε1
    -- Choose all positive pieces at the same epsilon while retaining the fixed I/O maps.
    have hpositive (k : Fin L.size) := hbound k ε hε hε1
    choose Q U Rεk hQ hU hRεk herror using hpositive
    let Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := ∑ k, Rεk k
    refine ⟨Q, U, Rε, hQ, hU, ?_, ?_⟩
    · intro w
      change (∑ k, Rεk k) (Li.smoothToSobolev 1 w) = _
      calc
        (∑ k, Rεk k) (Li.smoothToSobolev 1 w) =
            ∑ k, Rεk k (Li.smoothToSobolev 1 w) :=
          sum_apply Finset.univ Rεk (Li.smoothToSobolev 1 w)
        _ = ∑ k, Lo.smoothToSobolev 0 (∑ j, (Q k j).toLinearMap w) :=
          Finset.sum_congr rfl (fun k _ ↦ hRεk k w)
        _ = Lo.smoothToSobolev 0 (∑ k, ∑ j, (Q k j).toLinearMap w) :=
          (map_sum (Lo.smoothToSobolev 0)
            (fun k ↦ ∑ j, (Q k j).toLinearMap w) Finset.univ).symm
    · -- The finite sum of the actual local errors retains one common linear epsilon bound.
      change ‖(∑ k, Rεk k) - ∑ k, Rk k‖ ≤ (∑ k, Ck k) * ε
      calc
        ‖(∑ k, Rεk k) - ∑ k, Rk k‖ = ‖∑ k, (Rεk k - Rk k)‖ :=
          congrArg norm (Finset.sum_sub_distrib (s := Finset.univ) Rεk Rk).symm
        _ ≤ ∑ k, ‖Rεk k - Rk k‖ := norm_sum_le Finset.univ (fun k ↦ Rεk k - Rk k)
        _ ≤ ∑ k, Ck k * ε := Finset.sum_le_sum (fun k _ ↦ herror k)
        _ = (∑ k, Ck k) * ε := (Finset.sum_mul Finset.univ Ck ε).symm

end PrincipalPseudodifferentialLocalization

end AtiyahSinger
