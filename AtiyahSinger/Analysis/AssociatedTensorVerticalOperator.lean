/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorFiberSmoothness
public import AtiyahSinger.Analysis.AssociatedTensorVerticalSection
public import AtiyahSinger.Analysis.AtlasPseudodifferentialManifoldParameter

/-!
# The smooth vertical lift of a sphere PDO

Public module ID: M0208.

The supplied equivariant sphere PDO defines a linear operator between the
upstairs smooth tensor-section spaces, retaining its complete action and
smoothing remainder. Its restrictions equal the whole vertical family at
every principal representative. Smoothness follows from base-frame
contractions and joint parameter regularity of the same sphere PDO.
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

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original equivariant sphere PDO acts on actual upstairs smooth tensor sections. -/
theorem exists_associatedSphereTensorVerticalOperator {m : ℝ}
    (Q : AtlasPseudodifferentialOperator A A' m)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ') :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∃ V : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections →ₗ[ℂ]
        (associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ').smoothSections,
      ∀ (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections)
        (p : P) (y : OrthogonalSphere r),
        (V w).val (associatedBundleMk G P (OrthogonalSphere r) p y) =
          associatedSphereTensorFiberEquiv S E σ' p y
            ((associatedSphereTensorVerticalFamilyOperator (a := a) S E A σ hσ A'
              Q.toLinearMap w p).val y) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
  let R := associatedSphereTensorFiberRestriction (a := a) S E A σ hσ
  let F := associatedSphereTensorVerticalFamilyOperator (a := a) S E A σ hσ A' Q.toLinearMap
  obtain ⟨V, hV⟩ := exists_associatedSphereTensorVerticalSectionOperator (a := a)
    S E A σ hσ A' σ' hσ' Q.toLinearMap hQ
  have hsmooth (w : AT.smoothSections) : AT'.IsSmoothSection (V w) := by
    have hinput := (isSmoothSection_associatedSphereTensor_iff_jointFiberCoordinates (a := a)
      S E A σ hσ w.val (fun p ↦ R p w)
      (fun p y ↦ (associatedSphereTensorFiberRestriction_apply (a := a)
        S E A σ hσ p w y).symm)).mp w.property
    apply (isSmoothSection_associatedSphereTensor_iff_jointFiberCoordinates (a := a)
      S E A' σ' hσ' (V w) (F w) (hV w)).mpr
    intro b e he i j
    let u := associatedSphereTensorLocalFiberCoordinates S E A b e he i (fun p ↦ R p w)
    -- Each original base-coordinate contraction commutes with the same tensorized sphere PDO.
    have heq : associatedSphereTensorLocalFiberCoordinates S E A' b e he i (F w) =
        fun x ↦ Q.toLinearMap (u x) := by
      funext x
      by_cases hx : x ∈ (S.trivialization b).baseSet ∩ e.baseSet
      · let := he
        let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
        let φ : E (projection p) →ₗ[ℂ] ℂ := (LinearMap.proj i).comp
          ((EuclideanSpace.equiv (Fin a) ℂ).toLinearMap.comp
            ((e.linearEquivAt ℂ x hx.2).toLinearMap.comp
              (LinearEquiv.cast (R := ℂ) (M := E)
                ((S.trivialization b).proj_symm_apply' hx.1)).toLinearMap))
        apply Subtype.ext
        have h := tensorSectionOperator_contract (E (projection p)) A.smoothSections
          A'.smoothSections Q.toLinearMap (R p w) φ
        simpa only [associatedSphereTensorLocalFiberCoordinates, u, dite_eq_left hx,
          F, associatedSphereTensorVerticalFamilyOperator, LinearMap.pi_apply,
          LinearMap.comp_apply] using h
      · simp only [associatedSphereTensorLocalFiberCoordinates, u, dite_eq_right hx, map_zero]
    -- The entire original PDO preserves these jointly smooth manifold-parameter families.
    have hreg := Q.contMDiffOn_apply_manifold_parameter A A'
      ((S.trivialization b).baseSet ∩ e.baseSet)
      ((S.trivialization b).open_baseSet.inter e.open_baseSet) u
      (fun j ↦ hinput b e he i j) j
    simpa only [heq] using hreg
  let V' : AT.smoothSections →ₗ[ℂ] AT'.smoothSections := V.codRestrict AT'.smoothSections hsmooth
  exact ⟨V', hV⟩

set_option maxSynthPendingDepth 30 in
/-- The specified whole sphere PDO on the original upstairs smooth tensor sections. -/
def associatedSphereTensorVerticalOperator {m : ℝ}
    (Q : AtlasPseudodifferentialOperator A A' m)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ') :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections →ₗ[ℂ]
      (associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ').smoothSections :=
  (exists_associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ).choose

set_option maxSynthPendingDepth 30 in
/-- Every original whole-fiber value agrees with the existing vertical family operator. -/
theorem associatedSphereTensorVerticalOperator_apply {m : ℝ}
    (Q : AtlasPseudodifferentialOperator A A' m)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ') :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections)
      (p : P) (y : OrthogonalSphere r),
      (associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ w).val
          (associatedBundleMk G P (OrthogonalSphere r) p y) =
        associatedSphereTensorFiberEquiv S E σ' p y
          ((associatedSphereTensorVerticalFamilyOperator (a := a) S E A σ hσ A'
            Q.toLinearMap w p).val y) :=
  (exists_associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ).choose_spec

end AtiyahSinger
