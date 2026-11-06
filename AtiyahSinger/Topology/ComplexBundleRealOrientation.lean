/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.GeometricCohomologyOrientation
public import AtiyahSinger.Topology.HermitianFixedRankModel
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# The canonical real orientation of the original complex bundle

Public module ID: M1699.

The real frame of a complex frame is interleaved as (v1,i v1,...,vr,i vr).
It is constructed by the actual scalar-tower basis and the explicit
row-major finite-product reindexing. A complex change of frame has positive
real determinant, so all these frames determine one real orientation.
Local complex frames make that orientation locally compatible, providing
the existing geometrically normalized integral cohomological orientation.

The native real model retains the original fibers and total-space topology
through nativeModelTopology. The norm is precisely the supplied Hermitian
metric's existing fiber norm; the real inner product is its real part.
Only native chart data is selected after existence on this fixed topology.
No replacement bundle, unrelated norm, global frame or arbitrary choice
of real orientation is an input.

Sources: Milnor--Stasheff, section 14, for the canonical orientation of a
complex bundle; Husemoller, III.9, for continuous metrics and local frames.
The explicit native interfaces and interleaved finite indices are project
adapters. Rank zero uses the canonical empty frame and is included.
The native real atlas, its original Riemannian metric and canonical locally
compatible real orientation are proved below. The final integral cohomological
orientation still depends on the separate normalized fiber-class theorems.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

universe u v

/-- Realification of a complex basis in the ordered pairs (v1,i v1,...,vr,i vr). -/
def complexBasisRealification {r : ℕ} {V : Type v} [AddCommGroup V]
    [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
    (b : Module.Basis (Fin r) ℂ V) : Module.Basis (Fin (2 * r)) ℝ V :=
  (Complex.basisOneI.smulTower' b).reindex
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm r 2)))

namespace ComplexBundle.ContinuousHermitianMetric

variable {X : Type u} [TopologicalSpace X]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] (h : ContinuousHermitianMetric E)

/-- The real part of the supplied Hermitian product, with its original induced fiber norm. -/
@[reducible]
def realFiberInnerProductSpace (x : X) :
    letI := h.fiberNormedAddCommGroup x
    InnerProductSpace ℝ (E x) :=
  letI := h.fiberNormedAddCommGroup x
  letI := h.fiberInnerProductSpace x
  InnerProductSpace.rclikeToReal ℂ (E x)

variable [hFinite : IsFiniteRank E]

include hFinite in
/-- Complex local charts give real linear native charts on precisely the original topology. -/
theorem exists_realNativeFiberBundle (r : ℕ)
    (hr : ∀ x : X, Module.finrank ℂ (E x) = r) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
    ∃ b : FiberBundle (EuclideanSpace ℝ (Fin (2 * r))) E,
      letI := b
      VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * r))) E := by
  classical
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
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
  -- The metric norm gives precisely the topology of each original fiber inclusion.
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

/-- Native real chart data selected on the fixed identity-on-vectors total topology. -/
@[reducible]
def realNativeFiberBundle (r : ℕ) (hr : ∀ x : X, Module.finrank ℂ (E x) = r) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
    FiberBundle (EuclideanSpace ℝ (Fin (2 * r))) E :=
  (h.exists_realNativeFiberBundle r hr).choose

set_option linter.defProp false in
/-- The chosen original real native atlas has the specified real-linear transitions. -/
@[reducible]
def realNativeVectorBundle (r : ℕ) (hr : ∀ x : X, Module.finrank ℂ (E x) = r) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
    letI := h.realNativeFiberBundle r hr
    VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * r))) E :=
  (h.exists_realNativeFiberBundle r hr).choose_spec

/-- The real part of the same original metric is continuous in the original real native charts. -/
theorem realNativeRiemannianBundle (r : ℕ)
    (hr : ∀ x : X, Module.finrank ℂ (E x) = r) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
    letI := h.realNativeFiberBundle r hr
    letI := h.realNativeVectorBundle r hr
    IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * r))) E := by
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let V := EuclideanSpace ℝ (Fin (2 * r))
  let := nativeModelTopology E V
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  refine ⟨fun x ↦ innerSL ℝ, ?_, fun _ _ _ ↦ rfl⟩
  -- In finite real charts, continuity of the bilinear form is detected on model vectors.
  rw [continuous_iff_continuousAt]
  intro x
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  apply continuousAt_clm_apply.mpr
  intro v
  apply continuousAt_clm_apply.mpr
  intro w
  let e := trivializationAt V E x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt V E x
  have hcolumn (v : V) :
      ContinuousAt (fun y ↦ (⟨y, e.symm y v⟩ : TotalSpace Unit E)) x := by
    have hc : ContinuousOn (fun y ↦ (⟨y, e.symm y v⟩ : TotalSpace V E)) e.baseSet :=
      e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun y hy ↦ ⟨hy, Set.mem_univ v⟩)
    exact (nativeModelTotalHomeomorph E V).continuous.continuousAt.comp
      (hc.continuousAt (e.open_baseSet.mem_nhds hx))
  -- Evaluate the supplied original Hermitian pairing on those same two chart columns.
  let := sumTopology (E := E) (F := E)
  have hcolumns : ContinuousAt
      (fun y ↦ (⟨y, (e.symm y v, e.symm y w)⟩ : TotalSpace Unit (E ×ᵇ E))) x := by
    let j : TotalSpace Unit (E ×ᵇ E) → TotalSpace Unit E × TotalSpace Unit E :=
      fun z ↦ (⟨z.proj, z.snd.1⟩, ⟨z.proj, z.snd.2⟩)
    have hj : Topology.IsInducing j := ⟨rfl⟩
    apply hj.continuousAt_iff.mpr
    exact (hcolumn v).prodMk (hcolumn w)
  have hpair : ContinuousAt (fun y ↦ inner ℝ (e.symm y v) (e.symm y w)) x :=
    (Complex.continuous_re.continuousAt.comp
      (h.continuous_pairing.continuousAt.comp hcolumns))
  -- The native bilinear coordinates agree near x with that exact real-part pairing.
  apply hpair.congr
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  rw [inCoordinates_apply_eq₂ hy hy (Set.mem_univ y)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq, e]
  exact (innerSL_apply_apply ℝ _ _).symm

include hFinite in
/-- All interleaved complex frames specify exactly one real orientation of each original fiber. -/
theorem existsUnique_complexRealOrientation (r : ℕ)
    (hr : ∀ x : X, Module.finrank ℂ (E x) = r) (x : X) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
    ∃! o : Orientation ℝ (E x) (Fin (2 * r)),
      ∀ b : Module.Basis (Fin r) ℂ (E x), (complexBasisRealification b).orientation = o := by
  classical
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let : FiniteDimensional ℂ (E x) := finite_fiber (E := E) x
  -- The real determinant is the positive squared norm of the complex determinant.
  have sameOrientation (a b : Module.Basis (Fin r) ℂ (E x)) :
      (complexBasisRealification a).orientation = (complexBasisRealification b).orientation := by
    let f : (E x) ≃ₗ[ℂ] (E x) := b.equiv a (Equiv.refl (Fin r))
    have hmap : (complexBasisRealification b).map (f.restrictScalars ℝ) =
        complexBasisRealification a := by
      apply DFunLike.ext
      intro i
      simp only [Module.Basis.map_apply, complexBasisRealification, Module.Basis.reindex_apply,
        Module.Basis.smulTower'_apply, LinearEquiv.restrictScalars_apply]
      rw [map_smul]
      congr 1
      simp only [f, Module.Basis.equiv_apply, Equiv.refl_apply]
    rw [← hmap]
    apply ((complexBasisRealification b).orientation_comp_linearEquiv_eq_iff_det_pos
      (f.restrictScalars ℝ)).mpr
    change 0 < (f.toLinearMap.restrictScalars ℝ).det
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
    exact Complex.normSq_pos.mpr f.isUnit_det'.ne_zero
  -- An actual Fin r basis witnesses existence and uniqueness, including rank zero.
  let b := Module.finBasisOfFinrankEq ℂ (E x) (hr x)
  refine ⟨(complexBasisRealification b).orientation, ?_, ?_⟩
  · intro a
    exact sameOrientation a b
  · intro o ho
    exact (ho b).symm

/-- The canonical orientation specified by every interleaved complex frame. -/
def complexRealOrientation (r : ℕ) (hr : ∀ x : X, Module.finrank ℂ (E x) = r) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
    ∀ x : X, Orientation ℝ (E x) (Fin (2 * r)) :=
  fun x ↦ (h.existsUnique_complexRealOrientation r hr x).exists.choose

/-- Every actual complex frame has the specified canonical interleaved real orientation. -/
theorem complexRealOrientation_basis (r : ℕ)
    (hr : ∀ x : X, Module.finrank ℂ (E x) = r) (x : X)
    (b : Module.Basis (Fin r) ℂ (E x)) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
    (complexBasisRealification b).orientation = h.complexRealOrientation r hr x := by
  -- Evaluate the all-bases normalization of the same chosen orientation.
  exact (h.existsUnique_complexRealOrientation r hr x).exists.choose_spec b

/-- Original complex local frames make the canonical real orientation locally compatible. -/
theorem complexRealOrientation_locally_compatible (r : ℕ)
    (hr : ∀ x : X, Module.finrank ℂ (E x) = r) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
    IsLocallyCompatibleBundleOrientation (2 * r) E (h.complexRealOrientation r hr) := by
  classical
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let C := EuclideanSpace ℂ (Fin r)
  let V := EuclideanSpace ℝ (Fin (2 * r))
  let := nativeModelTopology E V
  let := nativeModelTopology E C
  let := h.nativeFiberBundle r hr
  let := h.nativeVectorBundle r hr
  intro x
  let e := trivializationAt C E x
  let b (y : e.baseSet) : Module.Basis (Fin r) ℂ (E y.val) :=
    (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.map
      (e.continuousLinearEquivAt ℂ y.val y.property).symm.toLinearEquiv
  -- Pull back the actual complex model frame, then interleave each column with its i multiple.
  refine ⟨e.baseSet, e.open_baseSet, mem_baseSet_trivializationAt C E x,
    fun y ↦ complexBasisRealification (b y), ?_, ?_⟩
  · intro y
    exact h.complexRealOrientation_basis r hr y.val (b y)
  · intro j
    let v : C := complexBasisRealification (EuclideanSpace.basisFun (Fin r) ℂ).toBasis j
    have hvalue (y : e.baseSet) :
        complexBasisRealification (b y) j = e.symm y.val v := by
      rw [← e.symmL_apply (R := ℂ) y.property v,
        ← e.symm_continuousLinearEquivAt_eq y.property]
      simp [complexBasisRealification, b, v, Module.Basis.smulTower'_apply]
    -- The same fixed model vector gives a continuous column on this original chart domain.
    have hc : Continuous (fun y : e.baseSet ↦
        (⟨y.val, e.symm y.val v⟩ : TotalSpace C E)) :=
      e.continuousOn_symm.comp_continuous
        (continuous_subtype_val.prodMk continuous_const)
        (fun y ↦ ⟨y.property, Set.mem_univ v⟩)
    have hret : Continuous (fun z : TotalSpace C E ↦
        (⟨z.proj, z.snd⟩ : TotalSpace V E)) :=
      (nativeModelTotalHomeomorph E V).symm.continuous.comp
        (nativeModelTotalHomeomorph E C).continuous
    -- Both retypings preserve the original point and vector, hence also the chosen orientation.
    exact (hret.comp hc).congr (fun y ↦ by rw [hvalue y]; rfl)

/-- The original integral Thom orientation normalized by the canonical complex orientation. -/
def complexCohomologyOrientation (r : ℕ)
    (hr : ∀ x : X, Module.finrank ℂ (E x) = r) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
    letI := h.realNativeFiberBundle r hr
    letI := h.realNativeVectorBundle r hr
    CohomologyOrientation ℤ (2 * r) E := by
  letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  letI := h.realNativeFiberBundle r hr
  letI := h.realNativeVectorBundle r hr
  exact geometricCohomologyOrientation (2 * r) E (h.complexRealOrientation r hr)
    (h.complexRealOrientation_locally_compatible r hr)

end ComplexBundle.ContinuousHermitianMetric

end AtiyahSinger
