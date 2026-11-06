/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalAdjunction
public import AtiyahSinger.Geometry.AssociatedProductMeasure
public import AtiyahSinger.Geometry.AtlasHermitianMetric

/-!
# The actual associated vertical formal adjunction

Public module ID: M0203.

The original equivariant sphere adjunction passes to the original upstairs
smooth vertical maps for the actual associated product measure. Smoothness
of the specified metrics gives continuous integrands, and the exact complex
Fubini formula reduces the global pairing to the already proved whole-fiber
adjunction. No Hilbert adjoint or closed-domain equality is inferred here.
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
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z


local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "T'" => fun z : Z ↦ E (q z) ⊗[ℂ] D' z

variable [MeasurableSpace B] [BorelSpace B] [CompactSpace B]
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in
-- Normalize the original associated fiber integral and invariant product pairing.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original vertical maps are formally adjoint for the actual associated product measure. -/
theorem associatedSphereTensorVerticalOperator_integral_adjoint {m : ℝ}
    (Q : AtlasPseudodifferentialOperator A A' m)
    (J : AtlasPseudodifferentialOperator A' A m)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (hJ : J.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ' σ hσ' hσ)
    (μ : Measure B) [IsFiniteMeasure μ]
    (ν : Measure (OrthogonalSphere r)) [IsFiniteMeasure ν]
    (hν : ∀ g : G, Measure.map (fun y : OrthogonalSphere r ↦ g • y) ν = ν)
    (hE : ∀ x, InnerProductSpace.Core ℂ (E x))
    (hF : ∀ y, InnerProductSpace.Core ℂ (F y))
    (hF' : ∀ y, InnerProductSpace.Core ℂ (F' y))
    (hInt : ∀ s t : A.smoothSections,
      Integrable (fun y ↦ (hF y).inner (s.val y) (t.val y)) ν)
    (hInt' : ∀ s t : A'.smoothSections,
      Integrable (fun y ↦ (hF' y).inner (s.val y) (t.val y)) ν)
    (hAdj : ∀ (s : A.smoothSections) (t : A'.smoothSections),
      (∫ y, (hF' y).inner ((Q.toLinearMap s).val y) (t.val y) ∂ν) =
        ∫ y, (hF y).inner (s.val y) ((J.toLinearMap t).val y) ∂ν) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ (l : ContinuousHermitianMetric T) (l' : ContinuousHermitianMetric T'),
      (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).IsSmoothHermitianMetric l →
      (associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ').IsSmoothHermitianMetric l' →
      (∀ (p : P) (y : OrthogonalSphere r) (u v : E (projection p)) (s t : F y),
        (l.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
            (associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] s))
            (associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] t)) =
          (hE (projection p)).inner u v * (hF y).inner s t) →
      (∀ (p : P) (y : OrthogonalSphere r) (u v : E (projection p)) (s t : F' y),
        (l'.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
            (associatedSphereTensorFiberEquiv S E σ' p y (u ⊗ₜ[ℂ] s))
            (associatedSphereTensorFiberEquiv S E σ' p y (v ⊗ₜ[ℂ] t)) =
          (hE (projection p)).inner u v * (hF' y).inner s t) →
      ∀ (s : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections)
        (t : (associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ').smoothSections),
        (∫ z, (l'.toCore z).inner
            ((associatedSphereTensorVerticalOperator (a := a)
              S E A σ hσ A' σ' hσ' Q hQ s).val z) (t.val z)
              ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν) =
          ∫ z, (l.toCore z).inner (s.val z)
            ((associatedSphereTensorVerticalOperator (a := a)
              S E A' σ' hσ' A σ hσ J hJ t).val z)
              ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν := by
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let := linearModelChartedSpace e Z
  let := isManifold_linearModelChartedSpace e Z
  intro l l' hl hl' hpair hpair' s t
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
  let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
  let J' := associatedSphereTensorVerticalOperator (a := a) S E A' σ' hσ' A σ hσ J hJ
  let f : C(Z, ℂ) := ⟨fun z ↦ (l'.toCore z).inner ((V s).val z) (t.val z),
    (AT'.contMDiff_pairing l' hl' (V s) t).continuous⟩
  let g : C(Z, ℂ) := ⟨fun z ↦ (l.toCore z).inner (s.val z) ((J' t).val z),
    (AT.contMDiff_pairing l hl s (J' t)).continuous⟩
  change (∫ z, f z ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν) =
    ∫ z, g z ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν
  -- Fubini uses the actual constructed measure on the same associated quotient.
  rw [integral_associatedProductMeasure_complex, integral_associatedProductMeasure_complex]
  apply integral_congr_ae
  filter_upwards with b
  obtain ⟨p, rfl⟩ := S.toIsPrincipalBundle.projection_properties.2.2 b
  rw [associatedFiberIntegral_apply S.toIsPrincipalBundle ν hν,
    associatedFiberIntegral_apply S.toIsPrincipalBundle ν hν]
  -- At this representative the pairing is exactly the full-fiber adjunction.
  exact associatedSphereTensorVerticalOperator_integral_fiber_adjoint (a := a)
    S E A σ hσ A' σ' hσ' Q J hQ hJ ν hE hF hF' l.toCore l'.toCore
      hpair hpair' hInt hInt' hAdj s t p

end AtiyahSinger
