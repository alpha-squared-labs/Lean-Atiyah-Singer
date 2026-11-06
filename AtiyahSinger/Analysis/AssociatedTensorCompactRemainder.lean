/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalRemainderBound
public import AtiyahSinger.Analysis.AtlasSobolevMaps

/-!
# Compact realization of the actual vertical smoothing residuals (M2323)

The original global metric bounds are transferred to the specified atlas H⁰
norms. Dense smooth sections determine bounded zero-order extensions of the
same residuals. Composition with the original Rellich inclusion gives compact
H¹-to-H⁰ realizations of each residual and their literal finite sum.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

/-- Each residual admits a bounded H⁰ extension with compact H¹ restriction,
and the finite sum agrees with the corresponding smooth sum. -/
def HasCompactAtlasResidualRealizations
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {U U' : M → Type*} [∀ x, AddCommGroup (U x)] [∀ x, Module ℂ (U x)]
    [TopologicalSpace (TotalSpace Unit U)]
    [∀ x, AddCommGroup (U' x)] [∀ x, Module ℂ (U' x)]
    [TopologicalSpace (TotalSpace Unit U')]
    (A : SmoothComplexBundleAtlas (n := d) U) (A' : SmoothComplexBundleAtlas (n := d) U')
    (L : AtlasBundlePresentation A) (L' : AtlasBundlePresentation A')
    {ι : Type*} [Fintype ι] (W : ι → A.smoothSections →ₗ[ℂ] A'.smoothSections) : Prop :=
  ∃ (R₀ : ι → L.SobolevSpace 0 →L[ℂ] L'.SobolevSpace 0)
    (R₁ : ι → L.SobolevSpace 1 →L[ℂ] L'.SobolevSpace 0),
    (∀ j (w : A.smoothSections),
      R₀ j (L.smoothToSobolev 0 w) = L'.smoothToSobolev 0 (W j w)) ∧
    (∀ j, R₁ j = (R₀ j).comp (L.sobolevInclusion 1 0 zero_le_one)) ∧
    (∀ j, IsCompactOperator (R₁ j)) ∧
    (∀ j (w : A.smoothSections),
      R₁ j (L.smoothToSobolev 1 w) = L'.smoothToSobolev 0 (W j w)) ∧
    IsCompactOperator (∑ j, R₁ j : L.SobolevSpace 1 →L[ℂ] L'.SobolevSpace 0) ∧
    ∀ w : A.smoothSections,
      (∑ j, R₁ j) (L.smoothToSobolev 1 w) = L'.smoothToSobolev 0 (∑ j, W j w)

private theorem hasCompactAtlasResidualRealizations_of_bound
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {U U' : M → Type*} [∀ x, AddCommGroup (U x)] [∀ x, Module ℂ (U x)]
    [TopologicalSpace (TotalSpace Unit U)]
    [∀ x, AddCommGroup (U' x)] [∀ x, Module ℂ (U' x)]
    [TopologicalSpace (TotalSpace Unit U')]
    (A : SmoothComplexBundleAtlas (n := d) U) (A' : SmoothComplexBundleAtlas (n := d) U')
    (L : AtlasBundlePresentation A) (L' : AtlasBundlePresentation A')
    {ι : Type*} [Fintype ι] (W : ι → A.smoothSections →ₗ[ℂ] A'.smoothSections)
    (C : ι → ℝ) (hbound : ∀ j (w : A.smoothSections),
      ‖L'.smoothToSobolev 0 (W j w)‖ ≤ C j * ‖L.smoothToSobolev 0 w‖) :
    HasCompactAtlasResidualRealizations A A' L L' W := by
  classical
  -- Dense smooth sections determine the original zero-order extension.
  let f (j : ι) := (L'.smoothToSobolev 0).comp (W j)
  let R₀ (j : ι) : L.SobolevSpace 0 →L[ℂ] L'.SobolevSpace 0 :=
    (f j).extendOfNorm (L.smoothToSobolev 0)
  have hR₀ (j : ι) (w : A.smoothSections) :
      R₀ j (L.smoothToSobolev 0 w) = L'.smoothToSobolev 0 (W j w) :=
    (f j).extendOfNorm_eq (L.denseRange_smoothToSobolev 0) ⟨C j, hbound j⟩ w
  -- Rellich is applied to the original input presentation.
  let inc := L.sobolevInclusion 1 0 zero_le_one
  have hinc : IsCompactOperator inc := L.isCompactOperator_sobolevInclusion 1 0 zero_lt_one
  let R₁ (j : ι) : L.SobolevSpace 1 →L[ℂ] L'.SobolevSpace 0 := (R₀ j).comp inc
  have hR₁ (j : ι) (w : A.smoothSections) :
      R₁ j (L.smoothToSobolev 1 w) = L'.smoothToSobolev 0 (W j w) :=
    (congrArg (R₀ j) (L.sobolevInclusion_smoothToSobolev 1 0 zero_le_one w)).trans
      (hR₀ j w)
  have hsum : (∑ j, R₁ j) = (∑ j, R₀ j).comp inc := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [R₁, sum_apply, ContinuousLinearMap.comp_apply]
  refine ⟨R₀, R₁, hR₀, fun _ ↦ rfl, fun j ↦ hinc.clm_comp (R₀ j), hR₁, ?_, ?_⟩
  · rw [hsum]
    exact hinc.clm_comp (∑ j, R₀ j)
  · -- The compact finite sum still acts as the same finite sum on smooth sections.
    intro w
    calc
      (∑ j, R₁ j) (L.smoothToSobolev 1 w) = ∑ j, R₁ j (L.smoothToSobolev 1 w) :=
        sum_apply Finset.univ R₁ (L.smoothToSobolev 1 w)
      _ = ∑ j, L'.smoothToSobolev 0 (W j w) :=
        Finset.sum_congr rfl (fun j _ ↦ hR₁ j w)
      _ = L'.smoothToSobolev 0 (∑ j, W j w) :=
        (map_sum (L'.smoothToSobolev 0) (fun j ↦ W j w) Finset.univ).symm

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
  (F F' : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)

variable
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber)
  (σ' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F'.Fiber)
  (hσ : σ.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r))
  (hσ' : σ'.IsSmooth (n := r) (r := F'.rank) 𝓘(ℝ, OrthogonalGroupModel r))
  (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
  (k' : SmoothHermitianMetric (n := r) (r := F'.rank) F'.Fiber)
  [T2Space B]

local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

include k k' in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 3600000 in
-- The extended limit accommodates the localized residual estimates and compact Sobolev realization.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual vertical residuals and their finite sum have compact H¹-to-H⁰ realizations. -/
theorem exists_associatedSphereTensorVerticalRemainder_compact_realization
    (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν]
    (L : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L' : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber)
    (J : SmoothBundlePresentation (n := n) (r := a) E)
    (b : Fin J.size → B)
    (hJ : ∀ j, tsupport (J.cutoff j) ⊆ (S.trivialization (b j)).baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    ∀ (Q : AtlasPseudodifferentialOperator A A' 1)
      (Npiece : Fin J.size → ℕ)
      (Ppiece : ∀ j : Fin J.size, Fin (Npiece j) → AtlasPseudodifferentialPiece A A' 1),
      (∀ j, IsAtlasSmoothingOperator A A'
        (Q.toLinearMap - ∑ i, (Ppiece j i).toLinearMap)) →
      letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
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
      let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
      let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
      ∀ W : Fin J.size → AT.smoothSections →ₗ[ℂ] AT'.smoothSections,
        (∀ j (w : AT.smoothSections) z,
          πS z ∉ tsupport (J.cutoff j) → (W j w).val z = 0) →
        (∀ j (w : AT.smoothSections) x, x ∈ (J.chart j).source →
          x ∈ (S.trivialization (b j)).baseSet → x ∈ (J.frame j).baseSet → ∀ y : Y,
            let q := (S.trivialization (b j)).toOpenPartialHomeomorph.symm (x, 1)
            (W j w).val (associatedBundleMk G P Y q y) =
              (J.cutoff j x : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
                ((tensorSectionOperator (E (projection q)) A.smoothSections A'.smoothSections
                  (Q.toLinearMap - ∑ i, (Ppiece j i).toLinearMap)
                  (associatedSphereTensorFiberRestriction (a := a) S E A σ hA q w)).val y)) →
        ∀ (G₀ : AtlasBundlePresentation AT) (G₀' : AtlasBundlePresentation AT')
          (l : ContinuousHermitianMetric T) (_hl : AT.IsSmoothHermitianMetric l)
          (l' : ContinuousHermitianMetric T') (_hl' : AT'.IsSmoothHermitianMetric l')
          (N N' : SmoothFiniteComplexBundle (n := n + r) Z)
          (kGlobal : SmoothHermitianMetric (n := n + r) (r := N.rank) N.Fiber)
          (kGlobal' : SmoothHermitianMetric (n := n + r) (r := N'.rank) N'.Fiber)
          (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η],
          letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
          letI := modelTopology (EuclideanSpace ℂ (Fin N'.rank)) N'.Fiber
          ∀ (e : Iso T N.Fiber)
            (_he : IsSmoothAtlasBundleMap AT (nativeSmoothComplexBundleAtlas N.Fiber)
              e.toHom.linearMap)
            (_hi : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N.Fiber) AT
              e.symm.toHom.linearMap)
            (e' : Iso T' N'.Fiber)
            (_he' : IsSmoothAtlasBundleMap AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
              e'.toHom.linearMap)
            (_hi' : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N'.Fiber) AT'
              e'.symm.toHom.linearMap),
            (∀ (z : Z) (v w : T z),
              kGlobal.pairing z (e.linearEquiv z v) (e.linearEquiv z w) =
                (l.toCore z).inner v w) →
            (∀ (z : Z) (v w : T' z),
              kGlobal'.pairing z (e'.linearEquiv z v) (e'.linearEquiv z w) =
                (l'.toCore z).inner v w) →
            HasCompactAtlasResidualRealizations AT AT' G₀ G₀' W := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
  let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
  let hA := σ.isSmoothAtlas_native IG hσ
  let hA' := σ'.isSmoothAtlas_native IG hσ'
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
  let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
  dsimp only
  intro Q Npiece Ppiece hrem W hWzero hreturn G₀ G₀' l hl l' hl' N N' kGlobal kGlobal' η hη
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N'.rank)) N'.Fiber
  intro e he hi e' he' hi' hpair hpair'
  let sectionEquiv :=
    (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas N.Fiber) e he hi).trans
      (nativeSmoothSectionLinearEquiv N.Fiber)
  let sectionEquiv' :=
    (atlasSmoothSectionEquiv AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
      e' he' hi').trans (nativeSmoothSectionLinearEquiv N'.Fiber)
  let inclusion := (kGlobal.smoothToL2 η).comp sectionEquiv.toLinearMap
  let inclusion' := (kGlobal'.smoothToL2 η).comp sectionEquiv'.toLinearMap
  -- Transfer the native L² bounds for the specified residuals to the atlas Sobolev norms.
  obtain ⟨C, hC, hWbound, _⟩ :=
    exists_associatedSphereTensorVerticalRemainder_global_l2_bound (a := a)
      S E F F' σ σ' hσ hσ' k k' ν L L' J b hJ Q Npiece Ppiece hrem W hWzero hreturn
      G₀ G₀' l hl l' hl' N N' kGlobal kGlobal' η e he hi e' he' hi' hpair hpair'
  obtain ⟨Cinput, Dinput, _, hDinput, hinput⟩ :=
    AT.exists_sobolevZero_l2_comparison G₀ l hl N kGlobal η e he hi hpair
  obtain ⟨Coutput, Doutput, hCoutput, _, houtput⟩ :=
    AT'.exists_sobolevZero_l2_comparison G₀' l' hl' N' kGlobal' η e' he' hi' hpair'
  have hchain (x y z t c₁ c₂ c₃ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
      (hxy : x ≤ c₁ * y) (hyz : y ≤ c₂ * z) (hzt : z ≤ c₃ * t) :
      x ≤ (c₁ * c₂ * c₃) * t := by
    calc
      x ≤ c₁ * (c₂ * z) := hxy.trans (mul_le_mul_of_nonneg_left hyz hc₁)
      _ ≤ c₁ * (c₂ * (c₃ * t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzt hc₂) hc₁
      _ = (c₁ * c₂ * c₃) * t := by simp only [mul_assoc]
  have hbound (j : Fin J.size) (w : AT.smoothSections) :
      ‖G₀'.smoothToSobolev 0 (W j w)‖ ≤
        (Coutput * C j * Dinput) * ‖G₀.smoothToSobolev 0 w‖ :=
    hchain _ _ _ _ Coutput (C j) Dinput hCoutput.le (hC j)
      (houtput (W j w)).1 (hWbound j w) (hinput w).2
  -- Apply the exact generic Rellich construction to these original residual bounds.
  exact hasCompactAtlasResidualRealizations_of_bound AT AT' G₀ G₀' W
    (fun j ↦ Coutput * C j * Dinput) hbound

end AtiyahSinger
