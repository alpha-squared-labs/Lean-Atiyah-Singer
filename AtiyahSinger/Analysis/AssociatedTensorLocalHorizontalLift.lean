/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorBaseExtensionSmoothness
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalFamily

/-!
# A local horizontal map in the associated tensor atlas

Public module ID: M0181.

Apply the same base PDO to the full normalized sphere family and return its
output through the principal chart. The output support lies inside that chart,
so the return gives a linear map between the prescribed associated tensor
smooth-section spaces. Only a base cutoff is used on the input.
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
/-- The actual local horizontal action returns a smooth section in the same principal atlas. -/
def associatedSphereTensorLocalHorizontalLift {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
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
    (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections →ₗ[ℂ]
      (associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ).smoothSections := by
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
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
  let U : AT.smoothSections →ₗ[ℂ] ∀ y : OrthogonalSphere r, ∀ x : B, F y ⊗[ℂ] E' x :=
    LinearMap.pi fun y ↦ (dualTensorSections (F y) (smoothSections E')).subtype.comp
      (associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ b χ hχ hχsupport y)
  let R := (associatedSphereTensorBaseExtension S E' σ b).comp U
  let K := L.chart.symm '' tsupport L.output.cutoff
  have hK : IsCompact K := L.output.compact_support.image_of_continuousOn
    (L.chart.continuousOn_symm.mono (fun x hx ↦ (L.output.support_subset hx).1))
  -- The same output support makes the actual return smooth across the principal boundary.
  refine R.codRestrict AT'.smoothSections ?_
  intro w
  apply isSmoothSection_associatedSphereTensorBaseExtension (a := a')
    S E' A σ hσ b K hK.isClosed houtput (U w)
  · intro y x hx
    exact associatedSphereTensorHorizontalFamily_apply_eq_zero (a := a)
      S E A σ E' L hσ b χ hχ hχsupport x hx y w
  · intro j k e he
    let l (y : OrthogonalSphere r) : F y →ₗ[ℂ] ℂ :=
      if hy : y ∈ (A.chart j).baseSet then
        (LinearMap.proj k).comp (A.frameLinearEquiv j y hy).toLinearMap
      else 0
    have hl (y : OrthogonalSphere r) (hy : y ∈ (A.chart j).baseSet) :
        l y = (LinearMap.proj k).comp (A.frameLinearEquiv j y hy).toLinearMap :=
      dite_eq_left hy
    have h := contMDiffOn_associatedSphereTensorHorizontalFamily (a := a)
      S E A σ E' L hσ b χ hχ hχsupport j k l hl e he w
    apply h.congr
    intro z hz
    rw [dite_eq_left hz.1, hl z.1 hz.1]
    rfl

set_option maxSynthPendingDepth 30 in
/-- The local lift evaluates the same horizontal family through the same raw chart return. -/
theorem associatedSphereTensorLocalHorizontalLift_apply {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
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
    ∀ (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections) (z : Z),
      (associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ b χ
        hχ hχsupport houtput w).val z =
      associatedSphereTensorBaseExtension S E' σ b
        (fun y x ↦ (associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ
          b χ hχ hχsupport y w).val x) z := by
  intros
  rfl

end AtiyahSinger
