/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalL2Bound

/-!
# The whole vertical operator in specified native L² spaces

Public module ID: M0207.

A supplied bounded Sobolev-zero realization of the sphere operator gives a
global L² bound for its associated vertical lift. This extends the lift along
the dense smooth inclusion of the specified native metric model. The resulting
continuous linear map retains the exact smooth-input formula, sphere operator,
and both upstairs bundle isomorphisms.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

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
set_option maxHeartbeats 1200000 in
-- Normalize the bounded original vertical lift and its metric-completion extension.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A bounded fiber H⁰ realization extends the vertical lift to the specified native L² spaces. -/
theorem exists_associatedSphereTensorVertical_global_l2_realization
    {m : ℝ} (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν]
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
    ∀ (Q : AtlasPseudodifferentialOperator A A' m)
      (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hA hA')
      (Q₀ : L.toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
        L'.toAtlasBundlePresentation.SobolevSpace 0),
      (∀ u : A.smoothSections, Q₀ (L.toAtlasBundlePresentation.smoothToSobolev 0 u) =
        L'.toAtlasBundlePresentation.smoothToSobolev 0 (Q.toLinearMap u)) →
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
      let V :=
        associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' Q hQ
        ∀ (_G₀ : AtlasBundlePresentation AT) (_G₀' : AtlasBundlePresentation AT')
          (l : ContinuousHermitianMetric T) (_hl : AT.IsSmoothHermitianMetric l)
          (l' : ContinuousHermitianMetric T') (_hl' : AT'.IsSmoothHermitianMetric l')
          (N N' : SmoothFiniteComplexBundle (n := n + r) Z)
          (kGlobal : SmoothHermitianMetric (n := n + r) (r := N.rank) N.Fiber)
          (kGlobal' : SmoothHermitianMetric (n := n + r) (r := N'.rank) N'.Fiber)
          (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η],
          letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
          letI := modelTopology (EuclideanSpace ℂ (Fin N'.rank)) N'.Fiber
          ∀ (e : Iso T N.Fiber)
            (he : IsSmoothAtlasBundleMap AT (nativeSmoothComplexBundleAtlas N.Fiber)
              e.toHom.linearMap)
            (hi : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N.Fiber) AT
              e.symm.toHom.linearMap)
            (e' : Iso T' N'.Fiber)
            (he' : IsSmoothAtlasBundleMap AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
              e'.toHom.linearMap)
            (hi' : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N'.Fiber) AT'
              e'.symm.toHom.linearMap),
            (∀ (z : Z) (v w : T z),
              kGlobal.pairing z (e.linearEquiv z v) (e.linearEquiv z w) =
                (l.toCore z).inner v w) →
            (∀ (z : Z) (v w : T' z),
              kGlobal'.pairing z (e'.linearEquiv z v) (e'.linearEquiv z w) =
                (l'.toCore z).inner v w) →
            let sectionEquiv :=
              (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas N.Fiber) e he hi).trans
                (nativeSmoothSectionLinearEquiv N.Fiber)
            let sectionEquiv' :=
              (atlasSmoothSectionEquiv AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
                e' he' hi').trans (nativeSmoothSectionLinearEquiv N'.Fiber)
            let inclusion := (kGlobal.smoothToL2 η).comp sectionEquiv.toLinearMap
            let inclusion' := (kGlobal'.smoothToL2 η).comp sectionEquiv'.toLinearMap
            ∃ V₀ : kGlobal.L2SectionSpace η →L[ℂ] kGlobal'.L2SectionSpace η,
              ∀ w : AT.smoothSections, V₀ (inclusion w) = inclusion' (V w) := by
  classical
  have hbound := exists_associatedSphereTensorVertical_global_l2_bound
    (a := a) (m := m) S E F F' σ σ' hσ hσ' k k' ν L L' J b hJ
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
  intro Q hQ Q₀ hQ₀ G₀ G₀' l hl l' hl' N N' kGlobal kGlobal' η hη
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
  let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' Q hQ
  obtain ⟨C, _hC, hCbound⟩ := hbound Q hQ Q₀ hQ₀ G₀ G₀' l hl l' hl'
    N N' kGlobal kGlobal' η e he hi e' he' hi' hpair hpair'
  -- The same section equivalence preserves the dense range of the native smooth inclusion.
  have hdense : DenseRange inclusion := by
    have hrange : Set.range inclusion = Set.range (kGlobal.smoothToL2 η) := by
      ext v
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨sectionEquiv u, rfl⟩
      · rintro ⟨u, rfl⟩
        refine ⟨sectionEquiv.symm u, ?_⟩
        change kGlobal.smoothToL2 η (sectionEquiv (sectionEquiv.symm u)) = _
        rw [LinearEquiv.apply_symm_apply]
    change Dense (Set.range inclusion)
    rw [hrange]
    exact kGlobal.denseRange_smoothToL2 η
  -- Extend precisely the output inclusion composed with the original smooth vertical map.
  let f := inclusion'.comp V
  let V₀ : kGlobal.L2SectionSpace η →L[ℂ] kGlobal'.L2SectionSpace η :=
    f.extendOfNorm inclusion
  refine ⟨V₀, ?_⟩
  intro w
  exact f.extendOfNorm_eq hdense ⟨C, hCbound⟩ w

end AtiyahSinger
