/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyThom
public import AtiyahSinger.Topology.ComplexBundleRealOrientation
public import AtiyahSinger.Topology.ComplexOrientationClass

/-!
# Native real models and normalized local classes for complex lines

Public module ID: M1715.

The fixed-rank real model retains the original complex bundle vectors and total
space topology through the existing nativeModelTopology. Unlike the Hermitian
metric construction, this adapter uses the already supplied fiber norms only;
finite dimension compares them with each original linear chart. No continuously
varying metric is needed. The rank-one normalization uses the actual complex
plane class, and is independent of the selected complex-linear coordinate.

Sources: the original finite-rank local charts and finite-dimensional norm
uniqueness; Milnor--Stasheff, Sections 9 and 14, for the complex orientation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory

universe u

namespace ComplexBundle

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hFinite : IsFiniteRank E]

include hFinite in
/-- Original linear charts give a real native model using the existing fiber norms. -/
theorem exists_realNativeFiberBundle_of_normedFibers (r : ℕ)
    (hr : ∀ x : X, Module.finrank ℂ (E x) = r) :
    letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
    ∃ b : FiberBundle (EuclideanSpace ℝ (Fin (2 * r))) E,
      letI := b
      VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * r))) E := by
  classical
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let : ∀ x, FiniteDimensional ℝ (E x) := fun x ↦ Module.Finite.trans ℂ (E x)
  let V := EuclideanSpace ℝ (Fin (2 * r))
  let := nativeModelTopology E V
  -- Retype original charts and their fixed coordinates, keeping every underlying vector.
  have hcharts (x : X) : ∃ e : Trivialization V (π V E),
      x ∈ e.baseSet ∧ e.IsLinear ℝ := by
    obtain ⟨n, e, hx, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := E) x
    let l : E x ≃ₗ[ℂ] (Fin n → ℂ) :=
      { toFun := fun v ↦ (e ⟨x, v⟩).2
        invFun := fun v ↦ cast (congrArg E (e.proj_symm_apply' hx))
          (e.toOpenPartialHomeomorph.symm (x, v)).snd
        left_inv := by
          intro v
          rw [cast_eq_iff_heq]
          exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd)
            (e.symm_apply_mk_proj (x := ⟨x, v⟩) (e.mem_source.mpr hx))
        right_inv := by
          intro v
          have hp := TotalSpace.mk_cast (F := Unit) (E := E)
            (e.proj_symm_apply' (x := v) hx) (e.toOpenPartialHomeomorph.symm (x, v)).snd
          exact (congrArg (fun z : TotalSpace Unit E ↦ (e z).2) hp).trans
            (congrArg Prod.snd (e.apply_symm_apply' hx))
        map_add' := (hlinear x hx).map_add
        map_smul' := (hlinear x hx).map_smul }
    have hdim : Module.finrank ℂ (E x) = n := by simpa using l.finrank_eq
    have hn : n = r := hdim.symm.trans (hr x)
    clear hdim
    subst n
    let c : (Fin r → ℂ) ≃L[ℝ] V :=
      ((complexBasisRealification (Pi.basisFun ℂ (Fin r))).equivFun.trans
        (EuclideanSpace.equiv (Fin (2 * r)) ℝ).symm.toLinearEquiv).toContinuousLinearEquiv
    let e' : Trivialization V (π V E) :=
      (e.transFiberHomeomorph c.toHomeomorph).compHomeomorph (nativeModelTotalHomeomorph E V)
    refine ⟨e', hx, ⟨?_⟩⟩
    intro y hy
    constructor
    · intro v w
      change c (e ⟨y, v + w⟩).2 = c (e ⟨y, v⟩).2 + c (e ⟨y, w⟩).2
      rw [(hlinear y hy).map_add, map_add]
    · intro a v
      change c (e ⟨y, a • v⟩).2 = a • c (e ⟨y, v⟩).2
      rw [← IsScalarTower.algebraMap_smul ℂ a v, (hlinear y hy).map_smul,
        IsScalarTower.algebraMap_smul, map_smul]
  choose chart hchart hlinear using hcharts
  -- Finite-dimensional norm uniqueness identifies each original fiber topology.
  have hmk (x : X) : Topology.IsInducing (@TotalSpace.mk X V E x) := by
    let := hlinear x
    let c : E x ≃L[ℝ] V :=
      ((chart x).linearEquivAt ℝ x (hchart x)).toContinuousLinearEquiv
    let f : E x → ((π V E) ⁻¹' ({x} : Set X)) := fun v ↦ ⟨⟨x, v⟩, rfl⟩
    have hf : Topology.IsInducing f := by
      apply ((chart x).preimageSingletonHomeomorph (hchart x)).isInducing.of_comp_iff.mp
      exact c.toHomeomorph.isInducing
    exact Topology.IsInducing.subtypeVal.comp hf
  let b : FiberBundle V E :=
    { totalSpaceMk_isInducing' := hmk
      trivializationAtlas' := {e | e.IsLinear ℝ}
      trivializationAt' := chart
      mem_baseSet_trivializationAt' := hchart
      trivialization_mem_atlas' := hlinear }
  refine ⟨b, ?_⟩
  let := b
  refine { trivialization_linear' := fun e he ↦ he.out, continuousOn_coordChange' := ?_ }
  intro e e' he he'
  let : e.IsLinear ℝ := he.out
  let : e'.IsLinear ℝ := he'.out
  -- In the finite-dimensional model, continuous operator families are detected on vectors.
  apply continuousOn_clm_apply.mpr
  intro v
  have hin : ContinuousOn (fun y : X ↦ (y, v)) (e.baseSet ∩ e'.baseSet) :=
    continuousOn_id.prodMk continuousOn_const
  have hback := e.continuousOn_symm.comp hin fun y hy ↦ ⟨hy.1, Set.mem_univ v⟩
  have hout := e'.continuousOn.comp hback fun y hy ↦ by
    apply e'.mem_source.mpr
    exact hy.2
  apply hout.snd.congr
  intro y hy
  exact e.coordChangeL_apply e' hy v


section LineOrientation

variable (hline : ∀ x : X, Module.finrank ℂ (E x) = 1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Complex coordinates give the same integral class on the actual line fiber. -/
theorem complexOrientationClass_pullback_eq {V : Type u} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (e f : V ≃L[ℂ] ULift.{u} ℂ) :
    relativeSingularCohomologyPullback ℤ ⟨e, e.continuous⟩
        (A := {v : V | v ≠ 0}) (B := {z : ULift.{u} ℂ | z ≠ 0})
        (fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))) 2
        complexOrientationClass =
      relativeSingularCohomologyPullback ℤ ⟨f, f.continuous⟩
        (A := {v : V | v ≠ 0}) (B := {z : ULift.{u} ℂ | z ≠ 0})
        (fun _ hv hz ↦ hv (f.injective (hz.trans f.map_zero.symm))) 2
        complexOrientationClass := by
  -- Factor one coordinate through the other and use the positive complex change of coordinates.
  let g := f.symm.trans e
  have hg := complexOrientationClass_pullback g
  have hcomp : (⟨g, g.continuous⟩ : C(ULift.{u} ℂ, _)).comp
      (⟨f, f.continuous⟩ : C(V, _)) = ⟨e, e.continuous⟩ := by
    apply ContinuousMap.ext
    intro v
    exact congrArg e (f.symm_apply_apply v)
  have h := relativeSingularCohomologyPullback_comp ℤ
    (⟨f, f.continuous⟩ : C(V, _)) (⟨g, g.continuous⟩ : C(ULift.{u} ℂ, _))
    (A := {v : V | v ≠ 0}) (B := {z : ULift.{u} ℂ | z ≠ 0})
    (C := {z : ULift.{u} ℂ | z ≠ 0})
    (fun _ hv hz ↦ hv (f.injective (hz.trans f.map_zero.symm)))
    (fun _ hv hz ↦ hv (g.injective (hz.trans g.map_zero.symm))) 2
  simp only [hcomp] at h
  rw [h, ModuleCat.comp_apply, hg]

attribute [local instance] nativeModelTopology

variable [FiberBundle (EuclideanSpace ℝ (Fin 2)) E]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hline in
/-- Original complex charts give a locally compatible integral orientation without a metric. -/
theorem exists_complexLineCohomologyOrientation :
    ∃ o : CohomologyOrientation ℤ 2 E, ∀ (x : X) (e : E x ≃L[ℂ] ULift.{u} ℂ),
      relativeSingularCohomologyPullback ℤ ⟨e.symm, e.symm.continuous⟩
        (A := {z : ULift.{u} ℂ | z ≠ 0}) (B := {v : E x | v ≠ 0})
        (fun _ hz hv ↦ hz (e.symm.injective (hv.trans e.symm.map_zero.symm))) 2
        (o.fiberClass x) = complexOrientationClass := by
  classical
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let d (x : X) : E x ≃L[ℂ] ULift.{u} ℂ :=
    (LinearEquiv.ofFinrankEq (E x) (ULift.{u} ℂ) (by simpa using hline x)).toContinuousLinearEquiv
  let c (x : X) : relativeSingularCohomology ℤ {v : E x | v ≠ 0} 2 :=
    relativeSingularCohomologyPullback ℤ ⟨d x, (d x).continuous⟩
      (A := {v : E x | v ≠ 0}) (B := {z : ULift.{u} ℂ | z ≠ 0})
      (fun _ hv hz ↦ hv ((d x).injective (hz.trans (d x).map_zero.symm))) 2
      complexOrientationClass
  have hgen (x : X) : Function.Bijective (fun a : ℤ ↦ a • c x) := by
    let e := d x
    let f : C(E x, ULift.{u} ℂ) := ⟨e, e.continuous⟩
    let g : C(ULift.{u} ℂ, E x) := ⟨e.symm, e.symm.continuous⟩
    have hf : Set.MapsTo f {v : E x | v ≠ 0} {z : ULift.{u} ℂ | z ≠ 0} :=
      fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))
    have hg : Set.MapsTo g {z : ULift.{u} ℂ | z ≠ 0} {v : E x | v ≠ 0} :=
      fun _ hz hv ↦ hz (e.symm.injective (hv.trans e.symm.map_zero.symm))
    let := isIso_relativeSingularCohomologyPullback_of_inverse ℤ f g hf hg
      (by apply ContinuousMap.ext; intro v; exact e.symm_apply_apply v)
      (by apply ContinuousMap.ext; intro z; exact e.apply_symm_apply z) 2
    have h := (ConcreteCategory.bijective_of_isIso
      (relativeSingularCohomologyPullback ℤ f hf 2)).comp
      complexOrientationClass_is_generator
    simpa only [Function.comp_def, map_zsmul] using h
  -- One original complex chart extends the normalized class over its full base set.
  have hlocal (x : X) : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ a : relativeSingularCohomology ℤ (bundleNonzeroOver 2 E U) 2,
        ∀ (y : X) (hy : y ∈ U),
          relativeSingularCohomologyPullback ℤ (bundleFiberInclusionOver 2 E U y hy)
            (A := {v : E y | v ≠ 0}) (B := bundleNonzeroOver 2 E U)
            (fun _ hv ↦ hv) 2 a = c y := by
    obtain ⟨m, t, hx, ht⟩ := IsFiniteRank.exists_linear_trivialization (E := E) x
    let l (y : X) (hy : y ∈ t.baseSet) : E y ≃ₗ[ℂ] (Fin m → ℂ) :=
      { toFun := fun v ↦ (t ⟨y, v⟩).2
        invFun := fun v ↦ cast (congrArg E (t.proj_symm_apply' hy))
          (t.toOpenPartialHomeomorph.symm (y, v)).snd
        left_inv := by
          intro v
          rw [cast_eq_iff_heq]
          exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd)
            (t.symm_apply_mk_proj (x := ⟨y, v⟩) (t.mem_source.mpr hy))
        right_inv := by
          intro v
          have hp := TotalSpace.mk_cast (F := Unit) (E := E)
            (t.proj_symm_apply' (x := v) hy) (t.toOpenPartialHomeomorph.symm (y, v)).snd
          exact (congrArg (fun z : TotalSpace Unit E ↦ (t z).2) hp).trans
            (congrArg Prod.snd (t.apply_symm_apply' hy))
        map_add' := (ht y hy).map_add
        map_smul' := (ht y hy).map_smul }
    have hm : m = 1 := by
      have hd := (l x hx).finrank_eq
      simpa [hline x] using hd.symm
    subst m
    let k : (Fin 1 → ℂ) ≃L[ℂ] ULift.{u} ℂ :=
      (LinearEquiv.ofFinrankEq (Fin 1 → ℂ) (ULift.{u} ℂ) (by simp)).toContinuousLinearEquiv
    let U := t.baseSet
    let H := nativeModelTotalHomeomorph E (EuclideanSpace ℝ (Fin 2))
    let p : C(BundleTotalOver 2 E U, ULift.{u} ℂ) :=
      ⟨fun z ↦ k (t (H z.val)).2, k.continuous.comp
        (t.toOpenPartialHomeomorph.continuousOn.comp_continuous
          (H.continuous.comp continuous_subtype_val)
          (fun z ↦ t.mem_source.mpr z.property)).snd⟩
    let e (y : X) (hy : y ∈ U) : E y ≃L[ℂ] ULift.{u} ℂ :=
      ((l y hy).toContinuousLinearEquiv).trans k
    have hp : Set.MapsTo p (bundleNonzeroOver 2 E U) {z : ULift.{u} ℂ | z ≠ 0} := by
      intro z hz hzero
      apply hz
      exact (e z.val.proj z.property).injective
        (hzero.trans (e z.val.proj z.property).map_zero.symm)
    refine ⟨U, t.open_baseSet, hx, relativeSingularCohomologyPullback ℤ p hp 2
      complexOrientationClass, ?_⟩
    intro y hy
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    exact complexOrientationClass_pullback_eq (e y hy) (d y)
  let o : CohomologyOrientation ℤ 2 E :=
    { fiberClass := c
      is_generator := by
        intro x
        change Function.Bijective (fun a : ℤ ↦
          (relativeSingularCohomology ℤ {v : E x | v ≠ 0} 2).isModule.smul a (c x))
        simp_rw [int_smul_eq_zsmul]
        exact hgen x
      locally_compatible := hlocal }
  refine ⟨o, ?_⟩
  intro x e
  change relativeSingularCohomologyPullback ℤ _ _ 2 (c x) = _
  have hc := complexOrientationClass_pullback_eq (d x) e
  change c x = relativeSingularCohomologyPullback ℤ _ _ 2 complexOrientationClass at hc
  rw [hc, ← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
  have hcomp : (⟨e, e.continuous⟩ : C(E x, _)).comp
      (⟨e.symm, e.symm.continuous⟩ : C(ULift.{u} ℂ, _)) = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro z
    exact e.apply_symm_apply z
  simp only [hcomp]
  simp [relativeSingularCohomologyPullback, relativeSingularChainsMap,
    CategoryTheory.Limits.cokernel.map]

end LineOrientation

end ComplexBundle

end AtiyahSinger
