/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorJointL2Realization

/-!
# The opposite pair of associated joint graphs

Public module ID: M0188.

Retain the original four native models and all four integral adjunctions.
The original sphere reverse operator commutes with the same horizontal lift.
This gives the other two simultaneous closed graphs and their exact cross
pairing, on the original odd source blocks. These are the joint domains needed
for the opposite graded operator; no reverse localization or new model occurs.
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

namespace PrincipalPseudodifferentialLocalization

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 16000000 in
-- Normalize the original opposite joint graphs and the same cross pairing.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in

/-- The same original adjunctions give the opposite joint graphs and their cross pairing. -/
theorem exists_closed_opposite_horizontalVertical_jointRealizations
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
        ∃ (R₁₀ : k₁₀.L2SectionSpace η →ₗ.[ℂ] (k₀₀.L2SectionSpace η × k₁₁.L2SectionSpace η))
          (R₀₁ : k₀₁.L2SectionSpace η →ₗ.[ℂ] (k₀₀.L2SectionSpace η × k₁₁.L2SectionSpace η)),
          R₁₀.graph = (i₁₀.prod ((i₀₀.comp H₀a).prod (i₁₁.comp V₁))).range.topologicalClosure ∧
          R₁₀.IsClosed ∧ Dense (R₁₀.domain : Set (k₁₀.L2SectionSpace η)) ∧
          R₀₁.graph = (i₀₁.prod ((i₀₀.comp V₀a).prod (i₁₁.comp H₁))).range.topologicalClosure ∧
          R₀₁.IsClosed ∧ Dense (R₀₁.domain : Set (k₀₁.L2SectionSpace η)) ∧
          ∀ (u : R₁₀.domain) (v : R₀₁.domain),
            inner ℂ (R₁₀ u).1 (R₀₁ v).1 = inner ℂ (R₁₀ u).2 (R₀₁ v).2 := by
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
  have hV₀rev (u : A₀₁.smoothSections) (v : A₀₀.smoothSections) :
      (∫ z, (l₀₀.toCore z).inner ((V₀a u).val z) (v.val z) ∂η) =
        ∫ z, (l₀₁.toCore z).inner (u.val z) ((V₀ v).val z) ∂η := by
    calc
      _ = conj (∫ z, (l₀₀.toCore z).inner (v.val z) ((V₀a u).val z) ∂η) := by
        rw [← integral_conj]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ (l₀₀.toCore z).conj_inner_symm _ _ |>.symm
      _ = conj (∫ z, (l₀₁.toCore z).inner ((V₀ v).val z) (u.val z) ∂η) :=
        congrArg conj (hV₀ v u).symm
      _ = _ := by
        rw [← integral_conj]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ (l₀₁.toCore z).conj_inner_symm _ _
  have hH₀rev (u : A₁₀.smoothSections) (v : A₀₀.smoothSections) :
      (∫ z, (l₀₀.toCore z).inner ((H₀a u).val z) (v.val z) ∂η) =
        ∫ z, (l₁₀.toCore z).inner (u.val z) ((H₀ v).val z) ∂η := by
    calc
      _ = conj (∫ z, (l₀₀.toCore z).inner (v.val z) ((H₀a u).val z) ∂η) := by
        rw [← integral_conj]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ (l₀₀.toCore z).conj_inner_symm _ _ |>.symm
      _ = conj (∫ z, (l₁₀.toCore z).inner ((H₀ v).val z) (u.val z) ∂η) :=
        congrArg conj (hH₀ v u).symm
      _ = _ := by
        rw [← integral_conj]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ (l₁₀.toCore z).conj_inner_symm _ _
  -- Close both original odd-source pairs simultaneously in their fixed target models.
  obtain ⟨R₁₀, hR₁₀, hc₁₀, hd₁₀⟩ := A₁₀.exists_closed_jointL2Realization A₀₀ A₁₁
    l₁₀ l₀₀ l₁₁ N₁₀ N₀₀ N₁₁ k₁₀ k₀₀ k₁₁ η e₁₀ e₀₀ e₁₁
    he₁₀ hi₁₀ he₀₀ hi₀₀ he₁₁ hi₁₁ hk₁₀ hk₀₀ hk₁₁ H₀a V₁ H₀ V₁a hH₀rev hV₁
  obtain ⟨R₀₁, hR₀₁, hc₀₁, hd₀₁⟩ := A₀₁.exists_closed_jointL2Realization A₀₀ A₁₁
    l₀₁ l₀₀ l₁₁ N₀₁ N₀₀ N₁₁ k₀₁ k₀₀ k₁₁ η e₀₁ e₀₀ e₁₁
    he₀₁ hi₀₁ he₀₀ hi₀₀ he₁₁ hi₁₁ hk₀₁ hk₀₀ hk₁₁ V₀a H₁ V₀ H₁a hV₀rev hH₁
  have hinner₀₀ (u v : A₀₀.smoothSections) : inner ℂ (i₀₀ u) (i₀₀ v) =
      ∫ z, (l₀₀.toCore z).inner (u.val z) (v.val z) ∂η := by
    change inner ℂ (k₀₀.smoothToL2 η (S₀₀ u)) (k₀₀.smoothToL2 η (S₀₀ v)) = _
    rw [k₀₀.inner_smoothToL2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ hk₀₀ z (u.val z) (v.val z)
  have hinner₁₁ (u v : A₁₁.smoothSections) : inner ℂ (i₁₁ u) (i₁₁ v) =
      ∫ z, (l₁₁.toCore z).inner (u.val z) (v.val z) ∂η := by
    change inner ℂ (k₁₁.smoothToL2 η (S₁₁ u)) (k₁₁.smoothToL2 η (S₁₁ v)) = _
    rw [k₁₁.inner_smoothToL2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ hk₁₁ z (u.val z) (v.val z)
  -- The original reverse sphere operator commutes with this same forward horizontal lift.
  have hcomm (v : A₀₁.smoothSections) : V₁a (H₁ v) = H₀ (V₀a v) := by
    exact DFunLike.congr_fun
      (C₀.horizontalLift_vertical_commute S E A' σ' hσ' A σ hσ E' J hJ) v
  have hcross (u : A₁₀.smoothSections) (v : A₀₁.smoothSections) :
      inner ℂ (i₀₀ (H₀a u)) (i₀₀ (V₀a v)) =
        inner ℂ (i₁₁ (V₁ u)) (i₁₁ (H₁ v)) := by
    rw [hinner₀₀, hinner₁₁]
    calc
      _ = ∫ z, (l₁₀.toCore z).inner (u.val z) ((H₀ (V₀a v)).val z) ∂η :=
        hH₀rev u (V₀a v)
      _ = ∫ z, (l₁₀.toCore z).inner (u.val z) ((V₁a (H₁ v)).val z) ∂η := by
        rw [hcomm]
      _ = _ := (hV₁ u (H₁ v)).symm
  have hgraphCross (x : k₁₀.L2SectionSpace η × k₀₀.L2SectionSpace η × k₁₁.L2SectionSpace η)
      (hx : x ∈ R₁₀.graph)
      (y : k₀₁.L2SectionSpace η × k₀₀.L2SectionSpace η × k₁₁.L2SectionSpace η)
      (hy : y ∈ R₀₁.graph) : inner ℂ x.2.1 y.2.1 = inner ℂ x.2.2 y.2.2 := by
    rw [hR₁₀] at hx
    rw [hR₀₁] at hy
    -- Continuous pairings extend first in one original graph variable, then in the other.
    have hyclosed : IsClosed {y : k₀₁.L2SectionSpace η ×
        k₀₀.L2SectionSpace η × k₁₁.L2SectionSpace η |
        inner ℂ x.2.1 y.2.1 = inner ℂ x.2.2 y.2.2} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    apply hyclosed.closure_subset_iff.mpr ?_ hy
    rintro _ ⟨v, rfl⟩
    have hxclosed : IsClosed {x : k₁₀.L2SectionSpace η ×
        k₀₀.L2SectionSpace η × k₁₁.L2SectionSpace η |
        inner ℂ x.2.1 (i₀₀ (V₀a v)) = inner ℂ x.2.2 (i₁₁ (H₁ v))} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    apply hxclosed.closure_subset_iff.mpr ?_ hx
    rintro _ ⟨u, rfl⟩
    exact hcross u v
  refine ⟨R₁₀, R₀₁, hR₁₀, hc₁₀, hd₁₀, hR₀₁, hc₀₁, hd₀₁, ?_⟩
  intro u v
  exact hgraphCross (u.val, R₁₀ u) (R₁₀.mem_graph u) (v.val, R₀₁ v) (R₀₁.mem_graph v)

end PrincipalPseudodifferentialLocalization

end AtiyahSinger
