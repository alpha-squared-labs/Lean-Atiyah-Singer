/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorBaseExtensionSmoothness
public import AtiyahSinger.Analysis.AssociatedTensorBaseSections
public import AtiyahSinger.Analysis.NativePseudodifferentialHorizontalTensor

/-!
# Supported horizontal lifts of complete native PDOs

Public module ID: M0192.

A complete native PDO with output supported in one original principal chart
acts on the whole normalized sphere family and returns a smooth section of
the original associated tensor bundle. The displayed pointwise formula keeps
its full section map, all smoothing terms, the supplied base cutoff, and the
original principal return. No sphere cutoff is introduced.

This applies in particular to actual native metric formal adjoints once their
two-sided support is transferred by the original integral adjunction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
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

variable [SecondCountableTopology B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole supported native PDO has its actual horizontal lift in the same principal chart. -/
theorem exists_associatedSphereTensorSupportedHorizontalLift {m : ℝ}
    (Q : PseudodifferentialOperator (n := n) (r := a) (q := a') E E' μ m)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (K : Set B) (hK : IsCompact K) (hKb : K ⊆ (S.trivialization b).baseSet)
    (hQ : ∀ (u : smoothSections (n := n) (r := a) E) (x : B),
      x ∉ K → (Q.toLinearMap u).val x = 0) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI (y : OrthogonalSphere r) : FiniteDimensional ℂ (F y) :=
      .of_injective (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).toLinearMap
        (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).injective
    ∃ H : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections →ₗ[ℂ]
      (associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ).smoothSections,
      ∀ w z, (H w).val z = associatedSphereTensorBaseExtension S E' σ b
        (fun y x ↦ ((tensorSectionOperator (F y) (smoothSections E) (smoothSections E')
          Q.toLinearMap)
            (associatedSphereTensorCutoffBaseRestriction (a := a)
              S E A σ hσ b χ hχ hχsupport y w)).val x) z := by
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
  let (y : OrthogonalSphere r) : FiniteDimensional ℂ (F y) :=
    .of_injective (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).toLinearMap
      (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).injective
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
  let V (y : OrthogonalSphere r) :=
    (tensorSectionOperator (F y) (smoothSections E) (smoothSections E') Q.toLinearMap).comp
      (associatedSphereTensorCutoffBaseRestriction (a := a)
        S E A σ hσ b χ hχ hχsupport y)
  let U : AT.smoothSections →ₗ[ℂ] ∀ y : OrthogonalSphere r, ∀ x : B, F y ⊗[ℂ] E' x :=
    LinearMap.pi fun y ↦ (dualTensorSections (F y) (smoothSections E')).subtype.comp (V y)
  let R := (associatedSphereTensorBaseExtension S E' σ b).comp U
  -- Every dual contraction retains the full native operator and its actual output support.
  have hsmooth (w : AT.smoothSections) : AT'.IsSmoothSection (R w) := by
    apply isSmoothSection_associatedSphereTensorBaseExtension (a := a')
      S E' A σ hσ b K hK.isClosed hKb (U w)
    · intro y x hx
      let e := A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec
      let u := associatedSphereTensorCutoffBaseRestriction (a := a)
        S E A σ hσ b χ hχ hχsupport y w
      let Q' := tensorSectionOperator (F y) (smoothSections E) (smoothSections E') Q.toLinearMap
      have hzero (φ : F y →ₗ[ℂ] ℂ) :
          TensorProduct.lid ℂ (E' x) (TensorProduct.map φ LinearMap.id ((Q' u).val x)) = 0 := by
        have h := congrFun (tensorSectionOperator_contract (F y)
          (smoothSections E) (smoothSections E') Q.toLinearMap u φ) x
        exact h.trans (hQ _ x hx)
      let v (k : Fin (A.rank (A.covers y).choose)) : F y := e.symm (Pi.single k 1)
      let l (k : Fin (A.rank (A.covers y).choose)) : F y →ₗ[ℂ] ℂ :=
        (LinearMap.proj k).comp e.toLinearMap
      have hsum (u : F y) : (∑ k, e u k • v k) = u := by
        apply e.injective
        simp only [map_sum, map_smul, v, LinearEquiv.apply_symm_apply]
        funext k
        simp [Pi.single_apply]
      have hdecomp (t : F y ⊗[ℂ] E' x) :
          (∑ k, v k ⊗ₜ[ℂ] TensorProduct.lid ℂ (E' x)
            (TensorProduct.map (l k) LinearMap.id t)) = t := by
        induction t using TensorProduct.inductionOn with
        | tmul u v =>
          simp only [l, TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.proj_apply,
            LinearEquiv.coe_coe, LinearMap.id_apply, TensorProduct.lid_tmul,
            TensorProduct.tmul_smul, TensorProduct.smul_tmul']
          rw [← TensorProduct.sum_tmul, hsum]
        | add u v hu hv =>
          simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
          exact congrArg₂ (· + ·) hu hv
      change (Q' u).val x = 0
      rw [← hdecomp ((Q' u).val x)]
      exact Finset.sum_eq_zero (fun k _ ↦ by rw [hzero, TensorProduct.tmul_zero])
    · -- Complete PDO parameter regularity gives the original moving-frame smoothness.
      intro j k e he
      let l (y : OrthogonalSphere r) : F y →ₗ[ℂ] ℂ :=
        if hy : y ∈ (A.chart j).baseSet then
          (LinearMap.proj k).comp (A.frameLinearEquiv j y hy).toLinearMap
        else 0
      have hl (y : OrthogonalSphere r) (hy : y ∈ (A.chart j).baseSet) :
          l y = (LinearMap.proj k).comp (A.frameLinearEquiv j y hy).toLinearMap :=
        dite_eq_left hy
      have h := Q.contMDiffOn_tensorSectionOperator F (A.chart j).baseSet
        (A.chart j).open_baseSet
        (fun y ↦ associatedSphereTensorCutoffBaseRestriction (a := a)
          S E A σ hσ b χ hχ hχsupport y w) l
        (fun c hc ↦ contMDiffOn_associatedSphereTensorCutoffBaseFamily (a := a)
          S E A σ hσ b χ hχ hχsupport j k l hl c hc w) e he
      apply h.congr
      intro z hz
      rw [dite_eq_left hz.1, hl z.1 hz.1]
      rfl
  exact ⟨R.codRestrict AT'.smoothSections hsmooth, fun _ _ ↦ rfl⟩

end AtiyahSinger
