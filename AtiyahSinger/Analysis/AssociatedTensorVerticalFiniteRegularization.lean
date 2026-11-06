/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalRegularization

/-!
# Finite vertical regularization with a smoothing remainder

Choose a finite representation of the specified whole sphere PDO and retain
its literal smoothing remainder. Each selected piece is regularized with the
same base input cutoff, geometric Sobolev spaces, and complete right-product
symbol. Its localization and extension maps remain fixed through the finite
sum. Injectivity of the Sobolev-zero embedding makes the unregularized piece
actions linear on smooth sections.

The remainder is the actual difference from Q; its retention asserts no
compactness on associated L² spaces.
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
/-- A finite representation of Q admits common-parameter regularization with its full remainder. -/
theorem exists_associatedSphereTensorVerticalFinite_regularization
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A') (b : B)
    (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (C : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (Q : AtlasPseudodifferentialOperator A A' 1) :
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
      ∃ (N : ℕ) (L : Fin N → AtlasPseudodifferentialPiece A A' 1),
        IsAtlasSmoothingOperator A A' (Q.toLinearMap - ∑ j, (L j).toLinearMap) ∧
        ∃ (γ : Fin N → X → ℝ) (hγ : ∀ j, ContDiff ℝ ∞ (γ j))
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
          (∀ j x, x ∈ tsupport C.cutoff → γ j x = 1) ∧
          (∀ j y, y ∈ tsupport (L j).output.cutoff → κ j y = 1) ∧
          (∀ j, tsupport (κ j) ⊆ (L j).chart.symm ⁻¹'
            (A.chart (L j).input.frameIndex).baseSet) ∧
          ∃ (I : ∀ j : Fin N, AT.smoothSections →ₗ[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (L j).input.frameIndex))))
            (O : ∀ j : Fin N,
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank (L j).output.frameIndex)))
                →ₗ[ℂ] AT'.smoothSections),
            (∀ j w z, I j w z = (Din j).localizedFunction w z) ∧
            (∀ j v z, (O j v).val z = (Dout j).extendedFunction v z) ∧
            ∃ (Tj : Fin N → AT.smoothSections →ₗ[ℂ] AT'.smoothSections)
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
                              S E A σ hσ q w)).val y)) ∧
              (∀ w : AT.smoothSections, R (Li.smoothToSobolev 1 w) =
                Lo.smoothToSobolev 0 (∑ j, Tj j w)) ∧
              ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
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
                  ‖Rε - R‖ ≤ K * ε := by
  classical
  -- Choose an actual representation of Q and preserve its literal full remainder.
  let representation := Q.isPseudodifferentialOperator
  let N : ℕ := representation.choose
  let L : Fin N → AtlasPseudodifferentialPiece A A' 1 := representation.choose_spec.choose
  have hrem : IsAtlasSmoothingOperator A A' (Q.toLinearMap - ∑ j, (L j).toLinearMap) :=
    representation.choose_spec.choose_spec
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
  have hlocal (j : Fin N) := exists_associatedSphereTensorVerticalPiece_regularization
    (a := a) S E A σ A' σ' hσ hσ' b c hc C hC (L j) Li Lo
  choose γ hγ hcγ hsγ hbγ κ hκ hcκ hsκ hγone hκone hκin I O hI hO
    Rj hRj Kj hKj hpositive using hlocal
  -- The same Sobolev realization determines a linear map of original smooth sections.
  let f (j : Fin N) (w : AT.smoothSections) : AT'.smoothSections :=
    O j (hRj j w).choose
  have hf (j : Fin N) (w : AT.smoothSections) :
      Rj j (Li.smoothToSobolev 1 w) = Lo.smoothToSobolev 0 (f j w) :=
    (hRj j w).choose_spec.2.2.1
  let Tj (j : Fin N) : AT.smoothSections →ₗ[ℂ] AT'.smoothSections := {
    toFun := f j
    map_add' w w' := by
      apply Lo.smoothToSobolev_injective 0
      calc
        Lo.smoothToSobolev 0 (f j (w + w')) =
            Rj j (Li.smoothToSobolev 1 (w + w')) := (hf j (w + w')).symm
        _ = Rj j (Li.smoothToSobolev 1 w) + Rj j (Li.smoothToSobolev 1 w') :=
          (congrArg (Rj j) ((Li.smoothToSobolev 1).map_add w w')).trans
            ((Rj j).map_add _ _)
        _ = Lo.smoothToSobolev 0 (f j w) + Lo.smoothToSobolev 0 (f j w') :=
          congrArg₂ (· + ·) (hf j w) (hf j w')
        _ = Lo.smoothToSobolev 0 (f j w + f j w') :=
          ((Lo.smoothToSobolev 0).map_add _ _).symm
    map_smul' z w := by
      apply Lo.smoothToSobolev_injective 0
      calc
        Lo.smoothToSobolev 0 (f j (z • w)) =
            Rj j (Li.smoothToSobolev 1 (z • w)) := (hf j (z • w)).symm
        _ = z • Rj j (Li.smoothToSobolev 1 w) :=
          (congrArg (Rj j) ((Li.smoothToSobolev 1).map_smul z w)).trans
            ((Rj j).map_smul z _)
        _ = z • Lo.smoothToSobolev 0 (f j w) := congrArg (z • ·) (hf j w)
        _ = Lo.smoothToSobolev 0 (z • f j w) :=
          ((Lo.smoothToSobolev 0).map_smul z _).symm }
  let R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := ∑ j, Rj j
  refine ⟨N, L, hrem, γ, hγ, hcγ, hsγ, hbγ, κ, hκ, hcκ, hsκ,
    hγone, hκone, hκin, I, O, hI, hO, Tj, R, ?_, ?_,
    ∑ j, Kj j, Finset.sum_nonneg (fun j _ ↦ hKj j), ?_⟩
  · intro j w
    exact ⟨(hRj j w).choose, (hRj j w).choose_spec.1,
      (hRj j w).choose_spec.2.1, rfl, (hRj j w).choose_spec.2.2.2⟩
  · -- The finite limiting sum uses the same smooth maps and the same completion maps.
    intro w
    change (∑ j, Rj j) (Li.smoothToSobolev 1 w) = _
    calc
      (∑ j, Rj j) (Li.smoothToSobolev 1 w) =
          ∑ j, Rj j (Li.smoothToSobolev 1 w) :=
        sum_apply Finset.univ Rj (Li.smoothToSobolev 1 w)
      _ = ∑ j, Lo.smoothToSobolev 0 (Tj j w) :=
        Finset.sum_congr rfl (fun j _ ↦ hf j w)
      _ = Lo.smoothToSobolev 0 (∑ j, Tj j w) :=
        (map_sum (Lo.smoothToSobolev 0) (fun j ↦ Tj j w) Finset.univ).symm
  · intro ε hε hε1
    -- All original local symbols are cut off at a common epsilon.
    have heach (j : Fin N) := hpositive j ε hε hε1
    choose Qε U Rεj hQε hU hRεj herror using heach
    let Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := ∑ j, Rεj j
    refine ⟨Qε, U, Rε, hQε, hU, ?_, ?_⟩
    · intro w
      change (∑ j, Rεj j) (Li.smoothToSobolev 1 w) = _
      calc
        (∑ j, Rεj j) (Li.smoothToSobolev 1 w) =
            ∑ j, Rεj j (Li.smoothToSobolev 1 w) :=
          sum_apply Finset.univ Rεj (Li.smoothToSobolev 1 w)
        _ = ∑ j, Lo.smoothToSobolev 0 ((Qε j).toLinearMap w) :=
          Finset.sum_congr rfl (fun j _ ↦ hRεj j w)
        _ = Lo.smoothToSobolev 0 (∑ j, (Qε j).toLinearMap w) :=
          (map_sum (Lo.smoothToSobolev 0)
            (fun j ↦ (Qε j).toLinearMap w) Finset.univ).symm
    · -- Summing the actual local errors preserves one uniform linear bound.
      change ‖(∑ j, Rεj j) - ∑ j, Rj j‖ ≤ (∑ j, Kj j) * ε
      calc
        ‖(∑ j, Rεj j) - ∑ j, Rj j‖ = ‖∑ j, (Rεj j - Rj j)‖ :=
          congrArg norm (Finset.sum_sub_distrib (s := Finset.univ) Rεj Rj).symm
        _ ≤ ∑ j, ‖Rεj j - Rj j‖ := norm_sum_le Finset.univ (fun j ↦ Rεj j - Rj j)
        _ ≤ ∑ j, Kj j * ε := Finset.sum_le_sum (fun j _ ↦ herror j)
        _ = (∑ j, Kj j) * ε := (Finset.sum_mul Finset.univ Kj ε).symm

end AtiyahSinger
