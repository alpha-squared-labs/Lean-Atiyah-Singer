/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalRegularization
public import AtiyahSinger.Analysis.AtlasIsometricProductDualBound

/-!
# Negative-order error for a specified vertical cutoff family

Public module ID: M0200.

The supplied sphere pieces, base chart, input localization, and output
extension are fixed throughout the estimate. Orthogonal coordinate
permutations transport each full right-factor error to the associated tensor
atlas. A single constant controls their finite sum from H⁰ to H⁻¹ before the
positive regularization parameter and its Schwartz realizations are chosen.
The uncut piece actions are supplied through their exact Fourier formulas.
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

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The specified vertical cutoff error is uniformly small from H⁰ to H⁻¹. -/
theorem associatedSphereTensorVerticalFamily_error_sobolev_neg_one_bound
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A') (b : B)
    (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (C : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (N : ℕ) (L : Fin N → AtlasPseudodifferentialPiece A A' 1)
    (Co : Fin N → BundleChartCutoff (r := a) E c)
    (hCo : ∀ j, c.symm '' tsupport (Co j).cutoff ⊆ (S.trivialization b).baseSet)
    (κ : Fin N → Y → ℝ) (hκ : ∀ j, ContDiff ℝ ∞ (κ j))
    (hκK : ∀ j, HasCompactSupport (κ j))
    (hκsupport : ∀ j, tsupport (κ j) ⊆ (L j).chart.target ∩
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
    let AT : SmoothComplexBundleAtlas (n := n + r) T :=
      associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
      associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
    let Din (j : Fin N) :=
      associatedSphereTensorChartCutoff S E A σ hσ b c C hC (L j).chart (L j).input
    let Ko (j : Fin N) : AtlasChartCutoff A' (L j).chart :=
      { (L j).output with
        cutoff := κ j
        smooth_cutoff := hκ j
        compact_support := hκK j
        support_subset := hκsupport j }
    let Dout (j : Fin N) :=
      associatedSphereTensorChartCutoff S E A' σ' hσ' b c (Co j) (hCo j) (L j).chart (Ko j)
    let α (j : Fin N) := zeroExtendedSymbol Set.univ (L j).output.cutoff (L j).symbol
    let β (j : Fin N) : SymbolFunction r (A.rank (L j).input.frameIndex * a)
        (A'.rank (L j).output.frameIndex * a) :=
      fun y η ↦ tensorIdentitySymbolMap (A.rank (L j).input.frameIndex)
        (A'.rank (L j).output.frameIndex) a (α j y η)
    let p (j : Fin N) := isometricSymbolTransport (productCoordinateSwap n r)
      (tensorCoordinateSwap a (A.rank (L j).input.frameIndex))
      (tensorCoordinateSwap a (A'.rank (L j).output.frameIndex)).symm
      (liftedProductSymbol (β j) (Co j).cutoff)
    ∀ (I : ∀ j : Fin N, AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L j).input.frameIndex))))
      (O : ∀ j : Fin N,
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L j).output.frameIndex)))
          →ₗ[ℂ] AT'.smoothSections),
      (∀ j w z, I j w z = (Din j).localizedFunction w z) →
      (∀ j v z, (O j v).val z = (Dout j).extendedFunction v z) →
      ∀ (Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation AT')
        (Tj : Fin N → AT.smoothSections →ₗ[ℂ] AT'.smoothSections),
        (∀ j w, ∃ v : 𝓢(XY,
          EuclideanSpace ℂ (Fin (a * A'.rank (L j).output.frameIndex))),
          (∀ z, quantize (p j) (I j w) z = v z) ∧ Tj j w = O j v) →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∀ U : ∀ j : Fin N,
            𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L j).input.frameIndex))) →L[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L j).output.frameIndex))),
            (∀ j v z, U j v z =
              quantize (rightProductCutoffSymbol (β j) (Co j).cutoff ε) v z) →
            ∀ w : AT.smoothSections,
              ‖Lo.smoothToSobolev (-1) ((∑ j, Tj j w) - ∑ j, O j (U j (I j w)))‖ ≤
                K * ε * ‖Li.smoothToSobolev 0 w‖ := by
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
  let AT : SmoothComplexBundleAtlas (n := n + r) T :=
    associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
    associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
  let CP (j : Fin N) : OpenPartialHomeomorph Z XY :=
    associatedSphereProductChart S b c (L j).chart
  let Din (j : Fin N) : AtlasChartCutoff AT (CP j) :=
    associatedSphereTensorChartCutoff S E A σ hσ b c C hC (L j).chart (L j).input
  let Ko (j : Fin N) : AtlasChartCutoff A' (L j).chart :=
    { (L j).output with
      cutoff := κ j
      smooth_cutoff := hκ j
      compact_support := hκK j
      support_subset := hκsupport j }
  let Dout (j : Fin N) : AtlasChartCutoff AT' (CP j) :=
    associatedSphereTensorChartCutoff S E A' σ' hσ' b c (Co j) (hCo j) (L j).chart (Ko j)
  let α (j : Fin N) := zeroExtendedSymbol Set.univ (L j).output.cutoff (L j).symbol
  let β (j : Fin N) : SymbolFunction r (A.rank (L j).input.frameIndex * a)
      (A'.rank (L j).output.frameIndex * a) :=
    fun y η ↦ tensorIdentitySymbolMap (A.rank (L j).input.frameIndex)
      (A'.rank (L j).output.frameIndex) a (α j y η)
  have hβ (j : Fin N) : IsSymbol Set.univ 1 (β j) :=
    isSymbol_continuousLinearMap 1 (α j)
      (isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 1 (L j).output.cutoff
        (L j).output.smooth_cutoff (L j).output.compact_support (Set.subset_univ _)
        (L j).symbol (L j).isSymbol)
      ((tensorIdentitySymbolMap (A.rank (L j).input.frameIndex)
        (A'.rank (L j).output.frameIndex) a).restrictScalars ℝ)
  have hβK (j : Fin N) : HasCompactSupport (β j) := by
    apply (L j).output.compact_support.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport (L j).output.cutoff)
    intro y hy
    by_contra hout
    apply hy
    funext η
    change tensorIdentitySymbolMap (A.rank (L j).input.frameIndex)
      (A'.rank (L j).output.frameIndex) a
      (zeroExtendedSymbol Set.univ (L j).output.cutoff (L j).symbol y η) = 0
    simp [zeroExtendedSymbol, image_eq_zero_of_notMem_tsupport hout]
  dsimp only
  intro I O hI hO Li Lo Tj hTj
  change AtlasBundlePresentation AT at Li
  change AtlasBundlePresentation AT' at Lo
  -- Each original piece is estimated with its prescribed coordinate permutations.
  have hlocal (j : Fin N) := norm_isometricProductCutoff_error_sobolev_neg_one_le
    AT AT' (CP j)
    (associatedSphereProductChart_mem_maximalAtlas S b c hc (L j).chart (L j).chart_mem_atlas)
    (Din j) (Dout j) (I j) (O j) (hI j) (hO j) (productCoordinateSwap n r)
    (tensorCoordinateSwap a (A.rank (L j).input.frameIndex))
    (tensorCoordinateSwap a (A'.rank (L j).output.frameIndex)).symm
    (β j) (hβ j) (hβK j) (Co j).cutoff (Co j).smooth_cutoff (Co j).compact_support Li Lo
  choose Cj hCj hbound using hlocal
  refine ⟨∑ j, Cj j, Finset.sum_nonneg (fun j _ ↦ hCj j), ?_⟩
  intro ε hε hεone U hU w
  have herror (j : Fin N) :
      ‖Lo.smoothToSobolev (-1) (Tj j w - O j (U j (I j w)))‖ ≤
        Cj j * ε * ‖Li.smoothToSobolev 0 w‖ := by
    let v : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L j).output.frameIndex))) :=
      (hTj j w).choose
    have hv := (hTj j w).choose_spec.1
    have hTv : Tj j w = O j v := (hTj j w).choose_spec.2
    have hcut (z : XY) :
        quantize (rightProductCutoffSymbol (β j) (Co j).cutoff ε) (I j w) z =
          U j (I j w) z := (hU j (I j w) z).symm
    have h := hbound j ε hε hεone w v (U j (I j w)) hv hcut
    have hsection : Tj j w - O j (U j (I j w)) = O j (v - U j (I j w)) :=
      (congrArg (fun z : AT'.smoothSections ↦ z - O j (U j (I j w))) hTv).trans
        ((O j).map_sub v (U j (I j w))).symm
    exact (congrArg (fun z : AT'.smoothSections ↦ ‖Lo.smoothToSobolev (-1) z‖)
      hsection).trans_le h
  -- The same finite family is summed; the constant was chosen before epsilon.
  have hsum : (∑ j, Tj j w) - ∑ j, O j (U j (I j w)) =
      ∑ j, (Tj j w - O j (U j (I j w))) :=
    (Finset.sum_sub_distrib (s := Finset.univ) (fun j ↦ Tj j w)
      (fun j ↦ O j (U j (I j w)))).symm
  have hcoordinate := (congrArg (Lo.smoothToSobolev (-1)) hsum).trans
    (map_sum (Lo.smoothToSobolev (-1))
      (fun j ↦ Tj j w - O j (U j (I j w))) Finset.univ)
  have hboundSum : ‖∑ j, Lo.smoothToSobolev (-1) (Tj j w - O j (U j (I j w)))‖ ≤
      (∑ j, Cj j) * ε * ‖Li.smoothToSobolev 0 w‖ := by
    have hn := norm_sum_le Finset.univ
      (fun j ↦ Lo.smoothToSobolev (-1) (Tj j w - O j (U j (I j w))))
    have hp := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ herror j)
    have heq : (∑ j, Cj j * ε * ‖Li.smoothToSobolev 0 w‖) =
        (∑ j, Cj j) * ε * ‖Li.smoothToSobolev 0 w‖ :=
      (Finset.sum_mul Finset.univ (fun j ↦ Cj j * ε) ‖Li.smoothToSobolev 0 w‖).symm.trans
        (congrArg (· * ‖Li.smoothToSobolev 0 w‖) (Finset.sum_mul Finset.univ Cj ε).symm)
    exact hn.trans (hp.trans_eq heq)
  exact (congrArg norm hcoordinate).trans_le hboundSum

end AtiyahSinger

