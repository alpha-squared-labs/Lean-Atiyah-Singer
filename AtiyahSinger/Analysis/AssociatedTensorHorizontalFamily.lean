/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorBaseSections

/-!
# The horizontal tensor family in a principal chart

Public module ID: M0165.

A PDO piece acts on the base-section factor of the normalized whole-sphere
family and leaves the sphere coefficient unchanged. Sphere-frame coordinates
remain jointly smooth. The output depends on the base cutoff only on the
input support and vanishes outside the prescribed output cutoff support.
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

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original PDO acts only on the base factor of the full normalized sphere family. -/
def associatedSphereTensorHorizontalFamily {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ y : OrthogonalSphere r,
      (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections →ₗ[ℂ]
        dualTensorSections (F y) (smoothSections (n := n) (r := a') E') := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro y
  let e := A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec
  let : FiniteDimensional ℂ (F y) := .of_injective e.toLinearMap e.injective
  exact (tensorSectionOperator (F y) (smoothSections E) (smoothSections E') L.toLinearMap).comp
    (associatedSphereTensorCutoffBaseRestriction (a := a) S E A σ hσ b χ hχ hχsupport y)

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every specified original sphere coordinate remains jointly smooth after the same PDO. -/
theorem contMDiffOn_associatedSphereTensorHorizontalFamily {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (j : A.Index) (k : Fin (A.rank j)) (l : ∀ y, F y →ₗ[ℂ] ℂ)
    (hl : ∀ (y : OrthogonalSphere r) (hy : y ∈ (A.chart j).baseSet),
      l y = (LinearMap.proj k).comp (A.frameLinearEquiv j y hy).toLinearMap)
    (e : Trivialization (EuclideanSpace ℂ (Fin a'))
      (π (EuclideanSpace ℂ (Fin a')) E')) (he : MemTrivializationAtlas e) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections,
      ContMDiffOn ((𝓡 r).prod (𝓡 n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin a')) ∞
        (fun z : OrthogonalSphere r × B ↦ (e ⟨z.2, TensorProduct.lid ℂ (E' z.2)
          (TensorProduct.map (l z.1) LinearMap.id
            ((associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ b χ
              hχ hχsupport z.1 w).val z.2))⟩).2)
        ((A.chart j).baseSet ×ˢ e.baseSet) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let (y : OrthogonalSphere r) : FiniteDimensional ℂ (F y) :=
    .of_injective (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).toLinearMap
      (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).injective
  intro w
  apply L.contMDiffOn_tensorSectionOperator F (A.chart j).baseSet (A.chart j).open_baseSet
    (fun y ↦ associatedSphereTensorCutoffBaseRestriction (a := a)
      S E A σ hσ b χ hχ hχsupport y w) l ?_ e he
  intro c hc
  exact contMDiffOn_associatedSphereTensorCutoffBaseFamily (a := a)
    S E A σ hσ b χ hχ hχsupport j k l hl c hc w

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The horizontal family depends on its base cutoff only on the original input support. -/
theorem associatedSphereTensorHorizontalFamily_eq_of_eq_on_support {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ χ' : B → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχ' : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ')
    (hχsupport' : tsupport χ' ⊆ (S.trivialization b).baseSet)
    (hcutoff : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, χ x = χ' x) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ (y : OrthogonalSphere r)
      (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections),
      associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ b χ hχ hχsupport y w =
        associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ b χ'
          hχ' hχsupport' y w := by
  as_aux_lemma =>
    classical
    let := modelTopology (EuclideanSpace ℂ (Fin a)) E
    let : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    let := associatedSphereChartedSpace S
    let := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    intro y w
    let e := A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec
    let : FiniteDimensional ℂ (F y) := .of_injective e.toLinearMap e.injective
    let u := associatedSphereTensorCutoffBaseRestriction (a := a)
      S E A σ hσ b χ hχ hχsupport y w
    let v := associatedSphereTensorCutoffBaseRestriction (a := a)
      S E A σ hσ b χ' hχ' hχsupport' y w
    let L' := tensorSectionOperator (F y) (smoothSections E) (smoothSections E') L.toLinearMap
    -- Each dual contraction yields base sections agreeing on the input cutoff support.
    have hcontract (φ : F y →ₗ[ℂ] ℂ) :
        (fun x ↦ TensorProduct.lid ℂ (E' x)
          (TensorProduct.map φ LinearMap.id ((L' u).val x))) =
        (fun x ↦ TensorProduct.lid ℂ (E' x)
          (TensorProduct.map φ LinearMap.id ((L' v).val x))) := by
      let su : smoothSections (n := n) (r := a) E :=
        ⟨fun x ↦ TensorProduct.lid ℂ (E x)
          (TensorProduct.map φ LinearMap.id (u.val x)), u.property φ⟩
      let sv : smoothSections (n := n) (r := a) E :=
        ⟨fun x ↦ TensorProduct.lid ℂ (E x)
          (TensorProduct.map φ LinearMap.id (v.val x)), v.property φ⟩
      have heq : L.toLinearMap su = L.toLinearMap sv := by
        apply L.toLinearMap_eq_of_eq_on_support
        intro x hx
        have hraw : associatedSphereTensorCutoffBaseFamily (a := a)
            S E A σ hσ b χ y w x =
              associatedSphereTensorCutoffBaseFamily (a := a) S E A σ hσ b χ' y w x := by
          simp only [associatedSphereTensorCutoffBaseFamily, LinearMap.pi_apply, hcutoff x hx]
        exact congrArg (fun t ↦ TensorProduct.lid ℂ (E x)
          (TensorProduct.map φ LinearMap.id t)) hraw
      have hu := tensorSectionOperator_contract (F y) (smoothSections E) (smoothSections E')
        L.toLinearMap u φ
      have hv := tensorSectionOperator_contract (F y) (smoothSections E) (smoothSections E')
        L.toLinearMap v φ
      exact hu.trans ((congrArg Subtype.val heq).trans hv.symm)
    -- Finite dual coordinates determine the actual tensor in every original output fiber.
    apply Subtype.ext
    funext x
    let ec : F y ⊗[ℂ] E' x ≃ₗ[ℂ] (Fin (A.rank (A.covers y).choose) → E' x) :=
      (TensorProduct.congr e (LinearEquiv.refl ℂ (E' x))).trans
        ((TensorProduct.comm ℂ (Fin (A.rank (A.covers y).choose) → ℂ) (E' x)).trans
          (TensorProduct.piScalarRight ℂ ℂ (E' x) (Fin (A.rank (A.covers y).choose))))
    have hcoord (t : F y ⊗[ℂ] E' x) (i : Fin (A.rank (A.covers y).choose)) :
        ec t i = TensorProduct.lid ℂ (E' x)
          (TensorProduct.map ((LinearMap.proj i).comp e.toLinearMap) LinearMap.id t) := by
      induction t using TensorProduct.inductionOn with
      | tmul u v => simp [ec]
      | add u v hu hv => simp only [map_add, Pi.add_apply, hu, hv]
    apply ec.injective
    funext i
    rw [hcoord, hcoord]
    exact congrFun (hcontract ((LinearMap.proj i).comp e.toLinearMap)) x

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole tensor output vanishes outside the original PDO output support. -/
theorem associatedSphereTensorHorizontalFamily_apply_eq_zero {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (x : B) (hx : x ∉ L.chart.symm '' tsupport L.output.cutoff) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ (y : OrthogonalSphere r)
      (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections),
      (associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ b χ
        hχ hχsupport y w).val x = 0 := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro y w
  let e := A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec
  let : FiniteDimensional ℂ (F y) := .of_injective e.toLinearMap e.injective
  let u := associatedSphereTensorCutoffBaseRestriction (a := a)
    S E A σ hσ b χ hχ hχsupport y w
  let L' := tensorSectionOperator (F y) (smoothSections E) (smoothSections E') L.toLinearMap
  -- Every dual contraction is the original output, with its original support.
  have hzero (φ : F y →ₗ[ℂ] ℂ) :
      TensorProduct.lid ℂ (E' x) (TensorProduct.map φ LinearMap.id ((L' u).val x)) = 0 := by
    have h := congrFun (tensorSectionOperator_contract (F y)
      (smoothSections E) (smoothSections E') L.toLinearMap u φ) x
    exact h.trans (L.toLinearMap_eq_zero _ x hx)
  -- Finite frame reconstruction turns the dual vanishing statements into tensor vanishing.
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
  change (L' u).val x = 0
  rw [← hdecomp ((L' u).val x)]
  exact Finset.sum_eq_zero (fun k _ ↦ by rw [hzero, TensorProduct.tmul_zero])

end AtiyahSinger
