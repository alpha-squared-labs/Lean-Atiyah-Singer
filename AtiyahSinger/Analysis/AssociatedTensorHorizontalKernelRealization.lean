/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalKernel
public import AtiyahSinger.Analysis.AssociatedTensorVerticalKernelRealization

/-!
# The actual horizontal operator on the full vertical kernel

Public module ID: M0169.

The full kernel representation of the same sphere PDO gives the source and
target coefficient equivalences. Their evaluation maps agree on every original
associated representative. Under these actual equivalences, the horizontal
operator is the already constructed coefficient PDO for the same localization.

Source: the finite kernel-coefficient argument in SG III.13.6. No index equality
or independent replacement of the source and target evaluation is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology tensorTopology continuousSMul_orthogonalSphere
  lieGroup_orthogonalGroup

variable {n r a a' : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
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
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))
  {μ : MeasureTheory.Measure B} [IsSmoothPositiveMeasure (n := n) μ]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "K" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "U" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z
local notation "U'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z

set_option maxSynthPendingDepth 30 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same coefficient PDO realizes the horizontal map between the two full vertical kernels. -/
theorem PrincipalPseudodifferentialLocalization.exists_horizontalLift_coefficientKernelRealization
    {m d : ℝ} (C₀ : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m)
    (Q : AtlasPseudodifferentialOperator A A' d)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] Q.toLinearMap.ker)
    (he : ∀ (g : G) (y : OrthogonalSphere r) (v : Fin ρ.dimension → ℂ),
      (e (ρ.representation g v)).val.val (g • y) =
        σ.linearMap g y ((e v).val.val y)) :
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
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∃ ev : Hom ((πS : Z → B) *ᵖ K) D,
      (∀ (p : P) (y : OrthogonalSphere r) (v : Fin ρ.dimension → ℂ),
        ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
            (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((e v).val.val y)) ∧
      ∃ Φ : (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
          (associatedOrthogonalRepresentationAtlas S ρ)).smoothSections ≃ₗ[ℂ]
          (associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ).ker,
        ∃ Ψ : (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
            (associatedOrthogonalRepresentationAtlas S ρ)).smoothSections ≃ₗ[ℂ]
            (associatedSphereTensorVerticalOperator (a := a') S E' A σ hσ A' σ' hσ' Q hQ).ker,
          (∀ u z, (Φ u).val.val z =
            TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
          (∀ u z, (Ψ u).val.val z =
            TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
          ∀ u, C₀.horizontalLift S E A σ E' hσ (Φ u).val =
            (Ψ ((C₀.coefficientOperator S E E' ρ).toLinearMap u)).val := by
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
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  -- Obtain both actual full-kernel equivalences for this same Q and full representation.
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hE := exists_associatedSphereTensorVerticalKernelRealization (a := a)
    S E A σ hσ A' σ' hσ' ρ Q hQ e he
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hE' := exists_associatedSphereTensorVerticalKernelRealization (a := a')
    S E' A σ hσ A' σ' hσ' ρ Q hQ e he
  obtain ⟨ev, hev, Φ, hΦ⟩ := hE
  obtain ⟨ev', hev', Ψ, hΨ⟩ := hE'
  -- Equality on every original representative identifies the two evaluation witnesses.
  have hevEq : ev' = ev := by
    apply Hom.ext
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      apply LinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := (associatedVectorFiberMk_bijective S.toIsPrincipalBundle
        ρ.representation z.1 rfl).2 v
      exact (hev' z.1 z.2 w).trans (hev z.1 z.2 w).symm
  rw [hevEq] at hΨ
  refine ⟨ev, hev, Φ, Ψ, hΦ, hΨ, ?_⟩
  intro u
  -- The public horizontal comparison now uses precisely that common evaluation and PDO.
  apply Subtype.ext
  funext z
  let s : (Fin ρ.dimension → ℂ) →ₗ[ℂ] A.smoothSections :=
    Q.toLinearMap.ker.subtype.comp e.toLinearMap
  have h := C₀.horizontalLift_coefficientOperator S E A σ ρ E' s ev hev hσ
    (Φ u).val u (hΦ u) z
  exact h.trans (hΨ ((C₀.coefficientOperator S E E' ρ).toLinearMap u) z).symm

end AtiyahSinger
