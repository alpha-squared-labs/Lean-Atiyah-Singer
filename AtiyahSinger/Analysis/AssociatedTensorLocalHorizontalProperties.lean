/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorLocalHorizontalLift

/-!
# Support and cutoff independence of the actual local horizontal lift

Public module ID: M0182.

These properties concern the map between the original associated tensor
section spaces. The full sphere factor remains present: agreement of base
cutoffs on the original input support determines the whole output, and the
original output support is preserved upstairs by inverse image.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

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

variable {a' : ℕ} [T2Space B]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "T'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z


set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Changing the base cutoff away from the original input support leaves the actual lift equal. -/
theorem associatedSphereTensorLocalHorizontalLift_eq_of_eq_on_support {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ χ' : B → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχ' : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ')
    (hχsupport' : tsupport χ' ⊆ (S.trivialization b).baseSet)
    (hcutoff : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, χ x = χ' x)
    (houtput : L.chart.symm '' tsupport L.output.cutoff ⊆ (S.trivialization b).baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ b χ
      hχ hχsupport houtput =
    associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ b χ'
      hχ' hχsupport' houtput := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  -- Base-cutoff agreement determines the complete horizontal family.
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext z
  rw [associatedSphereTensorLocalHorizontalLift_apply,
    associatedSphereTensorLocalHorizontalLift_apply]
  have hfamily :
      (fun y x ↦ (associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ
        b χ hχ hχsupport y w).val x) =
      (fun y x ↦ (associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ
        b χ' hχ' hχsupport' y w).val x) := by
    funext y x
    exact congrArg (fun u ↦ u.val x)
      (associatedSphereTensorHorizontalFamily_eq_of_eq_on_support (a := a)
        S E A σ E' L hσ b χ χ' hχ hχsupport hχ' hχsupport' hcutoff y w)
  rw [hfamily]

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual lift vanishes above the complement of the original base output support. -/
theorem associatedSphereTensorLocalHorizontalLift_apply_eq_zero {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (houtput : L.chart.symm '' tsupport L.output.cutoff ⊆ (S.trivialization b).baseSet)
    (z : Z) (hz : πS z ∉ L.chart.symm '' tsupport L.output.cutoff) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections,
      (associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ b χ
        hχ hχsupport houtput w).val z = 0 := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro w
  rw [associatedSphereTensorLocalHorizontalLift_apply]
  -- The return is linear in the single family value above this base point.
  have hzero (y : OrthogonalSphere r) :=
    associatedSphereTensorHorizontalFamily_apply_eq_zero (a := a)
      S E A σ E' L hσ b χ hχ hχsupport (πS z) hz y w
  by_cases hsource : z ∈ (associatedSphereTrivialization S b).source
  · simp only [associatedSphereTensorBaseExtension, LinearMap.pi_apply,
      dite_eq_left hsource, LinearMap.comp_apply, LinearMap.proj_apply,
      hzero, map_zero]
  · simp only [associatedSphereTensorBaseExtension, LinearMap.pi_apply,
      dite_eq_right hsource, LinearMap.zero_apply]

end AtiyahSinger
