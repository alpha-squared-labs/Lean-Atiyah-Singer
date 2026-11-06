/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalVerticalCommutation
public import AtiyahSinger.Analysis.AtlasJointL2Realization
public import AtiyahSinger.Geometry.AssociatedProductDensity

/-!
# The two actual associated joint graphs in four specified L² models

Public module ID: M0176.

Use the same four native models, bundle isomorphisms and metric pairings for
both simultaneous closures. The actual horizontal lift of the supplied principal
localization and the full vertical sphere operator determine the first joint
map; their supplied integral adjoints determine the second. Original horizontal-
vertical commutation gives the cross-pairing identity on smooth sections, then
continuity extends it to both joint closures. No separate-domain intersection,
replacement tensor-product Hilbert space, or new model choice occurs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct ComplexConjugate

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  tensorTopology continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

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
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  {F' : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F' y)]
  [∀ y, Module ℂ (F' y)] [TopologicalSpace (TotalSpace Unit F')] [IsFiniteRank F']
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')
  (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z


local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z

variable {a' : ℕ} [T2Space B]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "U" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z
local notation "U'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

variable [SecondCountableTopology B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ] [IsFiniteMeasure μ]
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 3200000 in
-- Normalize the two original horizontal-vertical graph closures and their cross pairing.
/-- The original associated operators give two closed joint graphs with the same cross pairing. -/
theorem PrincipalPseudodifferentialLocalization.exists_closed_horizontalVertical_jointRealizations
    {m d : ℝ} (C₀ : PrincipalPseudodifferentialLocalization S E E' μ m)
    (Q : AtlasPseudodifferentialOperator A A' d)
    (J : AtlasPseudodifferentialOperator A' A d)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (hJ : J.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ' σ hσ' hσ)
    (ν : Measure (OrthogonalSphere r)) [IsFiniteMeasure ν]
    [IsSmoothPositiveMeasure (n := r) ν]
    (hν : ∀ g : G, Measure.map (fun y : OrthogonalSphere r ↦ g • y) ν = ν) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    letI : TopologicalSpace (TotalSpace Unit U) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI : TopologicalSpace (TotalSpace Unit U') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let η := associatedProductMeasure S.toIsPrincipalBundle μ ν hν
    letI : IsSmoothPositiveMeasure (n := n + r) η :=
      isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
    let A₀₀ := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let A₁₀ := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
    let A₀₁ := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
    let A₁₁ := associatedSphereTensorBundleAtlas (a := a') S E' A' σ' hσ'
    let H₀ := C₀.horizontalLift S E A σ E' hσ
    let H₁ := C₀.horizontalLift S E A' σ' E' hσ'
    let V₀ := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
    let V₁ := associatedSphereTensorVerticalOperator (a := a') S E' A σ hσ A' σ' hσ' Q hQ
    let V₀a := associatedSphereTensorVerticalOperator (a := a) S E A' σ' hσ' A σ hσ J hJ
    let V₁a := associatedSphereTensorVerticalOperator (a := a') S E' A' σ' hσ' A σ hσ J hJ
    ∀ (l₀₀ : ContinuousHermitianMetric T) (l₁₀ : ContinuousHermitianMetric U)
      (l₀₁ : ContinuousHermitianMetric T') (l₁₁ : ContinuousHermitianMetric U')
      (N₀₀ N₁₀ N₀₁ N₁₁ : SmoothFiniteComplexBundle (n := n + r) Z)
      (k₀₀ : SmoothHermitianMetric (n := n + r) (r := N₀₀.rank) N₀₀.Fiber)
      (k₁₀ : SmoothHermitianMetric (n := n + r) (r := N₁₀.rank) N₁₀.Fiber)
      (k₀₁ : SmoothHermitianMetric (n := n + r) (r := N₀₁.rank) N₀₁.Fiber)
      (k₁₁ : SmoothHermitianMetric (n := n + r) (r := N₁₁.rank) N₁₁.Fiber),
      letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
      ∀ (e₀₀ : Iso T N₀₀.Fiber)
        (e₁₀ : Iso U N₁₀.Fiber)
        (e₀₁ : Iso T' N₀₁.Fiber)
        (e₁₁ : Iso U' N₁₁.Fiber)
        (he₀₀ : IsSmoothAtlasBundleMap A₀₀
          (nativeSmoothComplexBundleAtlas N₀₀.Fiber) e₀₀.toHom.linearMap)
        (hi₀₀ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₀₀.Fiber)
          A₀₀ e₀₀.symm.toHom.linearMap)
        (he₁₀ : IsSmoothAtlasBundleMap A₁₀
          (nativeSmoothComplexBundleAtlas N₁₀.Fiber) e₁₀.toHom.linearMap)
        (hi₁₀ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₁₀.Fiber)
          A₁₀ e₁₀.symm.toHom.linearMap)
        (he₀₁ : IsSmoothAtlasBundleMap A₀₁
          (nativeSmoothComplexBundleAtlas N₀₁.Fiber) e₀₁.toHom.linearMap)
        (hi₀₁ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₀₁.Fiber)
          A₀₁ e₀₁.symm.toHom.linearMap)
        (he₁₁ : IsSmoothAtlasBundleMap A₁₁
          (nativeSmoothComplexBundleAtlas N₁₁.Fiber) e₁₁.toHom.linearMap)
        (hi₁₁ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₁₁.Fiber)
          A₁₁ e₁₁.symm.toHom.linearMap),
        (∀ (z : Z) (v w : T z),
          k₀₀.pairing z (e₀₀.linearEquiv z v) (e₀₀.linearEquiv z w) =
            (l₀₀.toCore z).inner v w) →
        (∀ (z : Z) (v w : U z),
          k₁₀.pairing z (e₁₀.linearEquiv z v) (e₁₀.linearEquiv z w) =
            (l₁₀.toCore z).inner v w) →
        (∀ (z : Z) (v w : T' z),
          k₀₁.pairing z (e₀₁.linearEquiv z v) (e₀₁.linearEquiv z w) =
            (l₀₁.toCore z).inner v w) →
        (∀ (z : Z) (v w : U' z),
          k₁₁.pairing z (e₁₁.linearEquiv z v) (e₁₁.linearEquiv z w) =
            (l₁₁.toCore z).inner v w) →
        ∀ (H₀a : A₁₀.smoothSections →ₗ[ℂ] A₀₀.smoothSections)
          (H₁a : A₁₁.smoothSections →ₗ[ℂ] A₀₁.smoothSections),
        (∀ u v, (∫ z, (l₁₀.toCore z).inner ((H₀ u).val z) (v.val z) ∂η) =
          ∫ z, (l₀₀.toCore z).inner (u.val z) ((H₀a v).val z) ∂η) →
        (∀ u v, (∫ z, (l₁₁.toCore z).inner ((H₁ u).val z) (v.val z) ∂η) =
          ∫ z, (l₀₁.toCore z).inner (u.val z) ((H₁a v).val z) ∂η) →
        (∀ u v, (∫ z, (l₀₁.toCore z).inner ((V₀ u).val z) (v.val z) ∂η) =
          ∫ z, (l₀₀.toCore z).inner (u.val z) ((V₀a v).val z) ∂η) →
        (∀ u v, (∫ z, (l₁₁.toCore z).inner ((V₁ u).val z) (v.val z) ∂η) =
          ∫ z, (l₁₀.toCore z).inner (u.val z) ((V₁a v).val z) ∂η) →
        let S₀₀ := (atlasSmoothSectionEquiv A₀₀ (nativeSmoothComplexBundleAtlas N₀₀.Fiber)
          e₀₀ he₀₀ hi₀₀).trans (nativeSmoothSectionLinearEquiv N₀₀.Fiber)
        let i₀₀ := (k₀₀.smoothToL2 η).comp S₀₀.toLinearMap
        let S₁₀ := (atlasSmoothSectionEquiv A₁₀ (nativeSmoothComplexBundleAtlas N₁₀.Fiber)
          e₁₀ he₁₀ hi₁₀).trans (nativeSmoothSectionLinearEquiv N₁₀.Fiber)
        let i₁₀ := (k₁₀.smoothToL2 η).comp S₁₀.toLinearMap
        let S₀₁ := (atlasSmoothSectionEquiv A₀₁ (nativeSmoothComplexBundleAtlas N₀₁.Fiber)
          e₀₁ he₀₁ hi₀₁).trans (nativeSmoothSectionLinearEquiv N₀₁.Fiber)
        let i₀₁ := (k₀₁.smoothToL2 η).comp S₀₁.toLinearMap
        let S₁₁ := (atlasSmoothSectionEquiv A₁₁ (nativeSmoothComplexBundleAtlas N₁₁.Fiber)
          e₁₁ he₁₁ hi₁₁).trans (nativeSmoothSectionLinearEquiv N₁₁.Fiber)
        let i₁₁ := (k₁₁.smoothToL2 η).comp S₁₁.toLinearMap
        ∃ (R₀ : k₀₀.L2SectionSpace η →ₗ.[ℂ] (k₁₀.L2SectionSpace η × k₀₁.L2SectionSpace η))
          (R₁ : k₁₁.L2SectionSpace η →ₗ.[ℂ] (k₁₀.L2SectionSpace η × k₀₁.L2SectionSpace η)),
          R₀.graph = (i₀₀.prod ((i₁₀.comp H₀).prod (i₀₁.comp V₀))).range.topologicalClosure ∧
          R₀.IsClosed ∧ Dense (R₀.domain : Set (k₀₀.L2SectionSpace η)) ∧
          R₁.graph = (i₁₁.prod ((i₁₀.comp V₁a).prod (i₀₁.comp H₁a))).range.topologicalClosure ∧
          R₁.IsClosed ∧ Dense (R₁.domain : Set (k₁₁.L2SectionSpace η)) ∧
          ∀ (u : R₀.domain) (v : R₁.domain),
            inner ℂ (R₀ u).1 (R₁ v).1 = inner ℂ (R₀ u).2 (R₁ v).2 := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let : TopologicalSpace (TotalSpace Unit U) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let : TopologicalSpace (TotalSpace Unit U') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let lm := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let := linearModelChartedSpace lm Z
  let := isManifold_linearModelChartedSpace lm Z
  intro η
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
  intro A₀₀ A₁₀ A₀₁ A₁₁ H₀ H₁ V₀ V₁ V₀a V₁a l₀₀ l₁₀ l₀₁ l₁₁
    N₀₀ N₁₀ N₀₁ N₁₁ k₀₀ k₁₀ k₀₁ k₁₁
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
  intro e₀₀ e₁₀ e₀₁ e₁₁ he₀₀ hi₀₀ he₁₀ hi₁₀ he₀₁ hi₀₁ he₁₁ hi₁₁
    hk₀₀ hk₁₀ hk₀₁ hk₁₁ H₀a H₁a hH₀ hH₁ hV₀ hV₁
  let S₀₀ := (atlasSmoothSectionEquiv A₀₀ (nativeSmoothComplexBundleAtlas N₀₀.Fiber)
    e₀₀ he₀₀ hi₀₀).trans (nativeSmoothSectionLinearEquiv N₀₀.Fiber)
  let i₀₀ := (k₀₀.smoothToL2 η).comp S₀₀.toLinearMap
  let S₁₀ := (atlasSmoothSectionEquiv A₁₀ (nativeSmoothComplexBundleAtlas N₁₀.Fiber)
    e₁₀ he₁₀ hi₁₀).trans (nativeSmoothSectionLinearEquiv N₁₀.Fiber)
  let i₁₀ := (k₁₀.smoothToL2 η).comp S₁₀.toLinearMap
  let S₀₁ := (atlasSmoothSectionEquiv A₀₁ (nativeSmoothComplexBundleAtlas N₀₁.Fiber)
    e₀₁ he₀₁ hi₀₁).trans (nativeSmoothSectionLinearEquiv N₀₁.Fiber)
  let i₀₁ := (k₀₁.smoothToL2 η).comp S₀₁.toLinearMap
  let S₁₁ := (atlasSmoothSectionEquiv A₁₁ (nativeSmoothComplexBundleAtlas N₁₁.Fiber)
    e₁₁ he₁₁ hi₁₁).trans (nativeSmoothSectionLinearEquiv N₁₁.Fiber)
  let i₁₁ := (k₁₁.smoothToL2 η).comp S₁₁.toLinearMap
  -- Reverse the two actual adjunctions by Hermitian symmetry on the same integral forms.
  have hV₁rev (u : A₁₁.smoothSections) (v : A₁₀.smoothSections) :
      (∫ z, (l₁₀.toCore z).inner ((V₁a u).val z) (v.val z) ∂η) =
        ∫ z, (l₁₁.toCore z).inner (u.val z) ((V₁ v).val z) ∂η := by
    calc
      _ = conj (∫ z, (l₁₀.toCore z).inner (v.val z) ((V₁a u).val z) ∂η) := by
        rw [← integral_conj]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ (l₁₀.toCore z).conj_inner_symm _ _ |>.symm
      _ = conj (∫ z, (l₁₁.toCore z).inner ((V₁ v).val z) (u.val z) ∂η) :=
        congrArg conj (hV₁ v u).symm
      _ = _ := by
        rw [← integral_conj]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ (l₁₁.toCore z).conj_inner_symm _ _
  have hH₁rev (u : A₁₁.smoothSections) (v : A₀₁.smoothSections) :
      (∫ z, (l₀₁.toCore z).inner ((H₁a u).val z) (v.val z) ∂η) =
        ∫ z, (l₁₁.toCore z).inner (u.val z) ((H₁ v).val z) ∂η := by
    calc
      _ = conj (∫ z, (l₀₁.toCore z).inner (v.val z) ((H₁a u).val z) ∂η) := by
        rw [← integral_conj]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ (l₀₁.toCore z).conj_inner_symm _ _ |>.symm
      _ = conj (∫ z, (l₁₁.toCore z).inner ((H₁ v).val z) (u.val z) ∂η) :=
        congrArg conj (hH₁ v u).symm
      _ = _ := by
        rw [← integral_conj]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ (l₁₁.toCore z).conj_inner_symm _ _
  -- The two joint closures share precisely the already specified four native models and metrics.
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hjoint₀ := A₀₀.exists_closed_jointL2Realization A₁₀ A₀₁
    l₀₀ l₁₀ l₀₁ N₀₀ N₁₀ N₀₁ k₀₀ k₁₀ k₀₁ η e₀₀ e₁₀ e₀₁
    he₀₀ hi₀₀ he₁₀ hi₁₀ he₀₁ hi₀₁ hk₀₀ hk₁₀ hk₀₁ H₀ V₀ H₀a V₀a hH₀ hV₀
  obtain ⟨R₀, hR₀, hc₀, hd₀⟩ := hjoint₀
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hjoint₁ := A₁₁.exists_closed_jointL2Realization A₁₀ A₀₁
    l₁₁ l₁₀ l₀₁ N₁₁ N₁₀ N₀₁ k₁₁ k₁₀ k₀₁ η e₁₁ e₁₀ e₀₁
    he₁₁ hi₁₁ he₁₀ hi₁₀ he₀₁ hi₀₁ hk₁₁ hk₁₀ hk₀₁ V₁a H₁a V₁ H₁ hV₁rev hH₁rev
  obtain ⟨R₁, hR₁, hc₁, hd₁⟩ := hjoint₁
  have hinner₁₀ (u v : A₁₀.smoothSections) : inner ℂ (i₁₀ u) (i₁₀ v) =
      ∫ z, (l₁₀.toCore z).inner (u.val z) (v.val z) ∂η := by
    change inner ℂ (k₁₀.smoothToL2 η (S₁₀ u)) (k₁₀.smoothToL2 η (S₁₀ v)) = _
    rw [k₁₀.inner_smoothToL2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ hk₁₀ z (u.val z) (v.val z)
  have hinner₀₁ (u v : A₀₁.smoothSections) : inner ℂ (i₀₁ u) (i₀₁ v) =
      ∫ z, (l₀₁.toCore z).inner (u.val z) (v.val z) ∂η := by
    change inner ℂ (k₀₁.smoothToL2 η (S₀₁ u)) (k₀₁.smoothToL2 η (S₀₁ v)) = _
    rw [k₀₁.inner_smoothToL2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ hk₀₁ z (u.val z) (v.val z)
  -- The original commutation identifies the two compositions before taking their inner products.
  have hcross (u : A₀₀.smoothSections) (v : A₁₁.smoothSections) :
      inner ℂ (i₁₀ (H₀ u)) (i₁₀ (V₁a v)) =
        inner ℂ (i₀₁ (V₀ u)) (i₀₁ (H₁a v)) := by
    rw [hinner₁₀, hinner₀₁, ← hV₁ (H₀ u) v, ← hH₁ (V₀ u) v]
    have hcomm := DFunLike.congr_fun
      (C₀.horizontalLift_vertical_commute S E A σ hσ A' σ' hσ' E' Q hQ) u
    change V₁ (H₀ u) = H₁ (V₀ u) at hcomm
    rw [hcomm]
  have hgraphCross (x : k₀₀.L2SectionSpace η × k₁₀.L2SectionSpace η × k₀₁.L2SectionSpace η)
      (hx : x ∈ R₀.graph)
      (y : k₁₁.L2SectionSpace η × k₁₀.L2SectionSpace η × k₀₁.L2SectionSpace η)
      (hy : y ∈ R₁.graph) : inner ℂ x.2.1 y.2.1 = inner ℂ x.2.2 y.2.2 := by
    rw [hR₀] at hx
    rw [hR₁] at hy
    -- Continuous pairings extend first in one original graph variable, then in the other.
    have hyclosed : IsClosed {y : k₁₁.L2SectionSpace η ×
        k₁₀.L2SectionSpace η × k₀₁.L2SectionSpace η |
        inner ℂ x.2.1 y.2.1 = inner ℂ x.2.2 y.2.2} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    apply hyclosed.closure_subset_iff.mpr ?_ hy
    rintro _ ⟨v, rfl⟩
    have hxclosed : IsClosed {x : k₀₀.L2SectionSpace η ×
        k₁₀.L2SectionSpace η × k₀₁.L2SectionSpace η |
        inner ℂ x.2.1 (i₁₀ (V₁a v)) = inner ℂ x.2.2 (i₀₁ (H₁a v))} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    apply hxclosed.closure_subset_iff.mpr ?_ hx
    rintro _ ⟨u, rfl⟩
    exact hcross u v
  refine ⟨R₀, R₁, hR₀, hc₀, hd₀, hR₁, hc₁, hd₁, ?_⟩
  intro u v
  exact hgraphCross (u.val, R₀ u) (R₀.mem_graph u) (v.val, R₁ v) (R₁.mem_graph v)

end AtiyahSinger
