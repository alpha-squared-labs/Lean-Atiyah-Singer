/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleComplement
public import AtiyahSinger.Topology.ContinuousHermitianMetric
public import AtiyahSinger.Topology.FiniteBundle
public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Bundle homotopy invariance and finite complements

Public module ID: M1575.

The cylinder theorem and homotopic pullback theorem are Hatcher, Vector Bundles
and K-Theory, Proposition 1.7 and Theorem 1.6, pp.20--21. They supply the
homotopy-invariance step needed in SG III.13 Lemma 13.3. The finite-complement
consequence uses an actual homotopy equivalence to a finite CW complex, not just
finitely many cells in each dimension. No homotopy here is used as a proper Kc map.
The statements allow locally varying ranks; the source is paracompact Hausdorff.
The proof below uses the standard locally finite dual-frame argument to construct
continuous near-diagonal transport, then a continuous positive time step and locally
stationary finite compositions. This is a project implementation of the cylinder
argument; it does not replace the original bundle by a globally bounded-rank model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Topology unitInterval

section DiagonalTransport

attribute [local instance] isFiniteRank_pullback

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Local chart sums retain the specified total-space topologies.
/-- A globally continuous linear transport restricts to the identity on the diagonal. -/
private theorem exists_diagonal_transport :
    ∃ T : Hom ((ContinuousMap.fst : C(X × X, X)) *ᵖ E)
        ((ContinuousMap.snd : C(X × X, X)) *ᵖ E),
      ∀ x, T.linearMap (x, x) = LinearMap.id := by
  classical
  -- Extend the actual chart frames and their duals with square-root partition weights.
  choose r e he hlinear using (IsFiniteRank.exists_linear_trivialization (E := E))
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : X ↦ (e i).baseSet) (fun i ↦ (e i).open_baseSet) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, he x⟩)
  have hbase : Continuous (π Unit E) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (e z.proj).continuousAt_proj ((e z.proj).mem_source.mpr (he z.proj))
  -- The inverse coordinate maps retain the transport supplied by each actual chart.
  let coord (i : X) (x : X) (hx : x ∈ (e i).baseSet) :
      E x ≃ₗ[ℂ] (Fin (r i) → ℂ) :=
    { toFun := fun v ↦ ((e i) ⟨x, v⟩).2
      invFun := fun w ↦ cast (congrArg E ((e i).proj_symm_apply' hx))
        ((e i).toOpenPartialHomeomorph.symm (x, w)).2
      left_inv := by
        intro v
        rw [cast_eq_iff_heq]
        exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.2)
          ((e i).symm_apply_mk_proj (x := ⟨x, v⟩) ((e i).mem_source.mpr hx))
      right_inv := by
        intro w
        have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
          ((e i).proj_symm_apply' (x := w) hx)
          ((e i).toOpenPartialHomeomorph.symm (x, w)).2
        exact (congrArg (fun z : TotalSpace Unit E ↦ ((e i) z).2) hpoint).trans
          (congrArg Prod.snd ((e i).apply_symm_apply' hx))
      map_add' := (hlinear i x hx).map_add
      map_smul' := (hlinear i x hx).map_smul }
  let w (i : X) : C(X, ℂ) :=
    ⟨fun x ↦ (Real.sqrt (ρ i x) : ℂ),
      Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (ρ i).continuous)⟩
  have hwzero (i : X) (x : X) (hx : x ∉ tsupport (ρ i)) : w i x = 0 := by
    simp only [w, ContinuousMap.coe_mk, image_eq_zero_of_notMem_tsupport hx,
      Real.sqrt_zero, Complex.ofReal_zero]
  have hwsq (i : X) (x : X) : w i x * w i x = (ρ i x : ℂ) := by
    change (Real.sqrt (ρ i x) : ℂ) * (Real.sqrt (ρ i x) : ℂ) = _
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (ρ.nonneg i x)]
  let FrameIndex := (i : X) × Fin (r i)
  let sval (a : FrameIndex) (x : X) : E x :=
    if hx : x ∈ (e a.1).baseSet then
      (coord a.1 x hx).symm (w a.1 x • Pi.single a.2 (1 : ℂ)) else 0
  have hs (a : FrameIndex) : Continuous (fun x ↦ (⟨x, sval a x⟩ : TotalSpace Unit E)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ (e a.1).baseSet
    · -- Inside the original chart the weighted basis vector is an ordinary continuous vector.
      apply (e a.1).continuousAt_of_comp_left
        (f := fun y ↦ (⟨y, sval a y⟩ : TotalSpace Unit E)) continuousAt_id hx
      have hweight : ContinuousAt
          (fun y ↦ w a.1 y • Pi.single a.2 (1 : ℂ)) x :=
        (w a.1).continuous.continuousAt.smul continuousAt_const
      apply (continuousAt_id.prodMk hweight).congr_of_eventuallyEq
      filter_upwards [(e a.1).open_baseSet.mem_nhds hx] with y hy
      refine Prod.ext ((e a.1).proj_toFun ⟨y, sval a y⟩
        ((e a.1).mem_source.mpr hy)) ?_
      change coord a.1 y hy (sval a y) = _
      simp only [sval, dite_eq_left hy, LinearEquiv.apply_symm_apply]
    · -- Closed support containment makes the zero extension locally identically zero.
      have hxs : x ∉ tsupport (ρ a.1) := fun h ↦ hx (hρ a.1 h)
      apply (continuous_zero_section E).continuousAt.congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (ρ a.1)).isOpen_compl.mem_nhds hxs] with y hy
      change (⟨y, sval a y⟩ : TotalSpace Unit E) = ⟨y, 0⟩
      congr 1
      simp only [sval, hwzero a.1 y hy, zero_smul, map_zero, dite_eq_ite, ite_self]
  let s (a : FrameIndex) : continuousSections E := ⟨sval a, hs a⟩
  let l (a : FrameIndex) (x : X) : E x →ₗ[ℂ] ℂ :=
    if hx : x ∈ (e a.1).baseSet then
      w a.1 x • ((LinearMap.proj a.2).comp (coord a.1 x hx).toLinearMap) else 0
  have hl (a : FrameIndex) : Continuous (fun z : TotalSpace Unit E ↦ l a z.proj z.snd) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z.proj ∈ (e a.1).baseSet
    · have hcoord := (continuous_apply a.2).continuousAt.comp
        (((e a.1).continuousAt ((e a.1).mem_source.mpr hz)).snd)
      have hweight : ContinuousAt (fun y : TotalSpace Unit E ↦ w a.1 y.proj) z :=
        ((w a.1).continuous.comp hbase).continuousAt
      apply (hweight.mul hcoord).congr_of_eventuallyEq
      filter_upwards [hbase.continuousAt.preimage_mem_nhds
        ((e a.1).open_baseSet.mem_nhds hz)] with y hy
      change y.proj ∈ (e a.1).baseSet at hy
      simp only [l, dite_eq_left hy, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearMap.proj_apply, smul_eq_mul]
      rfl
    · have hzs : z.proj ∉ tsupport (ρ a.1) := fun h ↦ hz (hρ a.1 h)
      apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hbase.continuousAt.preimage_mem_nhds
        ((isClosed_tsupport (ρ a.1)).isOpen_compl.mem_nhds hzs)] with y hy
      simp only [l, hwzero a.1 y.proj hy, zero_smul, dite_eq_ite, ite_self,
        LinearMap.zero_apply]
  have hblock (i x : X) (v : E x) :
      ∑ j : Fin (r i), l ⟨i, j⟩ x v • (s ⟨i, j⟩).val x = (ρ i x : ℂ) • v := by
    by_cases hx : x ∈ (e i).baseSet
    · have hcoordinates :
          ∑ j : Fin (r i), (coord i x hx v) j • Pi.single j (1 : ℂ) =
            coord i x hx v := by
        ext j
        simp [Pi.single_apply]
      calc
        _ = (coord i x hx).symm
            (∑ j : Fin (r i), (w i x * w i x) •
              ((coord i x hx v) j • Pi.single j (1 : ℂ))) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [l, s, sval, dite_eq_left hx, LinearMap.smul_apply,
            LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply,
            map_smul, smul_smul, smul_eq_mul]
          congr 1
          ring
        _ = (coord i x hx).symm ((ρ i x : ℂ) • coord i x hx v) := by
          rw [hwsq, ← Finset.smul_sum, hcoordinates]
        _ = (ρ i x : ℂ) • v := by rw [map_smul, LinearEquiv.symm_apply_apply]
    · have hzero : ρ i x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρ i h))
      simp only [l, s, sval, dite_eq_right hx, LinearMap.zero_apply, zero_smul,
        Finset.sum_const_zero, hzero, Complex.ofReal_zero]
  have hlzero (i x : X) (hi : i ∉ ρ.finsupport x) (j : Fin (r i)) :
      l ⟨i, j⟩ x = 0 := by
    have hρzero : ρ i x = 0 := by
      by_contra h
      exact hi ((ρ.mem_finsupport x).mpr h)
    have hw : w i x = 0 := by simp [w, hρzero]
    simp only [l, hw, zero_smul, dite_eq_ite, ite_self]
  let T (x y : X) : E x →ₗ[ℂ] E y :=
    ∑ i ∈ ρ.finsupport x, ∑ j : Fin (r i), (l ⟨i, j⟩ x).smulRight ((s ⟨i, j⟩).val y)
  have hdiag (x : X) : T x x = LinearMap.id := by
    apply LinearMap.ext
    intro v
    simp only [T, LinearMap.sum_apply, LinearMap.smulRight_apply]
    simp_rw [hblock]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, ρ.sum_finsupport (Set.mem_univ x),
      Complex.ofReal_one, one_smul]
    rfl
  -- The source partition is locally finite, while each weighted rank-one map is continuous.
  let q : C(X × X, X) := ContinuousMap.fst
  let p : C(X × X, X) := ContinuousMap.snd
  let S := (q : X × X → X) *ᵖ E
  let D := TotalSpace Unit S
  let b : C(D, X) := ⟨fun z ↦ z.proj.2, continuous_snd.comp continuous_proj⟩
  let V := (b : D → X) *ᵖ E
  let terms (a : FrameIndex) : continuousSections V :=
    ⟨fun z ↦ l a z.proj.1 z.snd • (s a).val z.proj.2, by
      apply continuous_smul_section V
        (⟨fun z ↦ l a z.proj.1 z.snd,
          (hl a).comp (Pullback.continuous_lift Unit E q)⟩ : C(D, ℂ))
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E b).continuous_iff]
      exact continuous_id.prodMk ((s a).property.comp b.continuous)⟩
  have hfinite (J : Finset X) : Continuous (fun z : D ↦
      (⟨z.proj.2, ∑ i ∈ J, ∑ j : Fin (r i), l ⟨i, j⟩ z.proj.1 z.snd •
        (s ⟨i, j⟩).val z.proj.2⟩ : TotalSpace Unit E)) := by
    let frameSum : continuousSections V := ∑ i ∈ J, ∑ j : Fin (r i), terms ⟨i, j⟩
    have hc := (Pullback.continuous_lift Unit E b).comp frameSum.property
    simpa only [frameSum, terms, Submodule.coe_sum, Finset.sum_apply, Function.comp_def,
      Pullback.lift, b, ContinuousMap.coe_mk] using hc
  have hcontinuous : Continuous (fun z : D ↦
      (⟨z.proj.2, T z.proj.1 z.proj.2 z.snd⟩ : TotalSpace Unit E)) := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    obtain ⟨J, hJ⟩ := ρ.exists_finset_nhds z₀.proj.1
    apply (hfinite J).continuousAt.congr_of_eventuallyEq
    have hx : Continuous (fun z : D ↦ z.proj.1) := continuous_fst.comp continuous_proj
    filter_upwards [hx.continuousAt.eventually hJ] with z hz
    congr 1
    change (∑ i ∈ ρ.finsupport z.proj.1, ∑ j : Fin (r i),
      (l ⟨i, j⟩ z.proj.1).smulRight ((s ⟨i, j⟩).val z.proj.2)) z.snd = _
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
    apply Finset.sum_subset
    · intro i hi
      exact hz.2 ((ρ.mem_finsupport z.proj.1).mp hi)
    · intro i _ hi
      simp only [hlzero i z.proj.1 hi, LinearMap.zero_apply, zero_smul,
        Finset.sum_const_zero]
  refine ⟨{ linearMap z := T z.1 z.2, continuous_total := ?_ }, hdiag⟩
  rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
  exact continuous_proj.prodMk hcontinuous


omit [T2Space X] [ParacompactSpace X] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Fiberwise bijectivity is open for a continuous map of locally finite-rank bundles. -/
private theorem Hom.isOpen_setOf_bijective
    {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F] (f : Hom E F) :
    IsOpen {x | Function.Bijective (f.linearMap x)} := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨r, e, he, hlinearE⟩ :=
    IsFiniteRank.exists_linear_trivialization (E := E) x
  obtain ⟨s, d, hd, hlinearF⟩ :=
    IsFiniteRank.exists_linear_trivialization (E := F) x
  -- Stage 1: keep the original chart maps and their actual inverse fiber vectors.
  let eLin (y : X) (hy : y ∈ e.baseSet) : E y ≃ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun v ↦ (e ⟨y, v⟩).2
      invFun := fun v ↦ cast (congrArg E (e.proj_symm_apply' hy))
        (e.toOpenPartialHomeomorph.symm (y, v)).snd
      left_inv := by
        intro v
        rw [cast_eq_iff_heq]
        exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd)
          (e.symm_apply_mk_proj (x := ⟨y, v⟩) (e.mem_source.mpr hy))
      right_inv := by
        intro v
        have hp := TotalSpace.mk_cast (F := Unit) (E := E)
          (e.proj_symm_apply' (x := v) hy) (e.toOpenPartialHomeomorph.symm (y, v)).snd
        exact (congrArg (fun z : TotalSpace Unit E ↦ (e z).2) hp).trans
          (congrArg Prod.snd (e.apply_symm_apply' hy))
      map_add' := (hlinearE y hy).map_add
      map_smul' := (hlinearE y hy).map_smul }
  let dLin (y : X) (hy : y ∈ d.baseSet) : F y ≃ₗ[ℂ] (Fin s → ℂ) :=
    { toFun := fun v ↦ (d ⟨y, v⟩).2
      invFun := fun v ↦ cast (congrArg F (d.proj_symm_apply' hy))
        (d.toOpenPartialHomeomorph.symm (y, v)).snd
      left_inv := by
        intro v
        rw [cast_eq_iff_heq]
        exact congr_arg_heq (fun z : TotalSpace Unit F ↦ z.snd)
          (d.symm_apply_mk_proj (x := ⟨y, v⟩) (d.mem_source.mpr hy))
      right_inv := by
        intro v
        have hp := TotalSpace.mk_cast (F := Unit) (E := F)
          (d.proj_symm_apply' (x := v) hy) (d.toOpenPartialHomeomorph.symm (y, v)).snd
        exact (congrArg (fun z : TotalSpace Unit F ↦ (d z).2) hp).trans
          (congrArg Prod.snd (d.apply_symm_apply' hy))
      map_add' := (hlinearF y hy).map_add
      map_smul' := (hlinearF y hy).map_smul }
  have hpointE (y : X) (hy : y ∈ e.baseSet) (v : Fin r → ℂ) :
      (⟨y, (eLin y hy).symm v⟩ : TotalSpace Unit E) = e.toOpenPartialHomeomorph.symm (y, v) :=
    TotalSpace.mk_cast (F := Unit) (E := E) (e.proj_symm_apply' hy) _
  let U : Set X := e.baseSet ∩ d.baseSet
  let A (y : U) : (Fin r → ℂ) →L[ℂ] (Fin s → ℂ) :=
    ((dLin y.val y.property.2).toLinearMap.comp ((f.linearMap y.val).comp
      (eLin y.val y.property.1).symm.toLinearMap)).toContinuousLinearMap
  have hA : Continuous (fun y : U ↦ A y) := by
    apply continuous_clm_apply.mpr
    intro v
    have heinv : Continuous (fun y : U ↦
        (⟨y.val, (eLin y.val y.property.1).symm v⟩ : TotalSpace Unit E)) := by
      have hc := e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
        (continuous_subtype_val.prodMk (continuous_const (y := v)))
        (fun y : U ↦ e.mem_target.mpr y.property.1)
      apply hc.congr
      intro y
      exact (hpointE y.val y.property.1 v).symm
    have hf : Continuous (fun y : U ↦
        (⟨y.val, f.linearMap y.val ((eLin y.val y.property.1).symm v)⟩ :
          TotalSpace Unit F)) := f.continuous_total.comp heinv
    exact continuous_snd.comp
      (d.toOpenPartialHomeomorph.continuousOn.comp_continuous hf
        (fun y : U ↦ d.mem_source.mpr y.property.2))
  have hbij (y : U) : (A y).IsInvertible ↔ Function.Bijective (f.linearMap y.val) := by
    have hlinear : Function.Bijective (A y) ↔ Function.Bijective (f.linearMap y.val) := by
      constructor
      · intro h
        have hf : (f.linearMap y.val : E y.val → F y.val) =
            (dLin y.val y.property.2).symm ∘ A y ∘ eLin y.val y.property.1 := by
          funext v
          change f.linearMap y.val v = (dLin y.val y.property.2).symm
            (dLin y.val y.property.2 (f.linearMap y.val
              ((eLin y.val y.property.1).symm (eLin y.val y.property.1 v))))
          rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
        rw [hf]
        exact (dLin y.val y.property.2).symm.bijective.comp
          (h.comp (eLin y.val y.property.1).bijective)
      · intro h
        exact (dLin y.val y.property.2).bijective.comp
          (h.comp (eLin y.val y.property.1).symm.bijective)
    constructor
    · intro h
      exact hlinear.mp h.bijective
    · intro h
      refine ⟨(LinearEquiv.ofBijective (A y).toLinearMap
        (hlinear.mpr h)).toContinuousLinearEquiv, ?_⟩
      ext v
      rfl
  have hgood : IsOpen {y : U | Function.Bijective (f.linearMap y.val)} := by
    have hopen := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hA
    simpa only [Set.preimage_ofPred_eq, hbij] using hopen
  have hU : IsOpen U := e.open_baseSet.inter d.open_baseSet
  have hO := hU.isOpenMap_subtype_val _ hgood
  apply Filter.mem_of_superset (hO.mem_nhds ⟨⟨x, he, hd⟩, hx, rfl⟩)
  rintro _ ⟨y, hy, rfl⟩
  exact hy

open scoped Topology unitInterval in
/-- An open neighborhood of every time diagonal admits one continuous positive step size. -/
private theorem exists_continuous_time_step (U : Set (X × (unitInterval × unitInterval)))
    (hU : IsOpen U) (hdiag : ∀ x t, (x, t, t) ∈ U) :
    ∃ ε : C(X, ℝ), (∀ x, 0 < ε x) ∧
      ∀ x (s t : unitInterval), dist s t ≤ ε x → (x, s, t) ∈ U := by
  classical
  -- Compactness of the time diagonal supplies locally uniform spatial neighborhoods.
  let K : Set (unitInterval × unitInterval) := Set.range (fun t : unitInterval ↦ (t, t))
  have hK : IsCompact K := isCompact_range (continuous_id.prodMk continuous_id)
  have hlocal (x : X) : ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ W, ∀ s t : unitInterval, dist s t < δ → (y, s, t) ∈ U := by
    have hsub : ({x} : Set X) ×ˢ K ⊆ U := by
      rintro ⟨y, s, t⟩ ⟨hy, ⟨z, hz⟩⟩
      have hs := congrArg Prod.fst hz
      have ht := congrArg Prod.snd hz
      change z = s at hs
      change z = t at ht
      have hy' : y = x := hy
      simpa only [← hs, ← ht, hy'] using hdiag x z
    obtain ⟨W, V, hW, hV, hxW, hKV, hWV⟩ :=
      generalized_tube_lemma isCompact_singleton hK hU hsub
    obtain ⟨δ, hδ, hδV⟩ := hK.exists_thickening_subset_open hV hKV
    refine ⟨W, hW, hxW (Set.mem_singleton x), δ, hδ, ?_⟩
    intro y hy s t hst
    apply hWV ⟨hy, hδV ?_⟩
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(s, s), ⟨s, rfl⟩, ?_⟩
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_comm] using hst
  choose W hW hxW δ hδ hnear using hlocal
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ W hW (by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxW x⟩)
  let εval (x : X) : ℝ := ∑ᶠ i, ρ i x • (δ i / 2)
  have hε : Continuous εval := ρ.continuous_finsum_smul
    (fun _ _ _ ↦ continuousAt_const)
  have hεsum (x : X) : εval x = ∑ i ∈ ρ.finsupport x, ρ i x * (δ i / 2) := by
    exact (ρ.sum_finsupport_smul_eq_finsum (x₀ := x) (fun i _ ↦ δ i / 2)).symm
  have hεpos (x : X) : 0 < εval x := by
    rw [hεsum]
    obtain ⟨i, hi⟩ := ρ.exists_pos (Set.mem_univ x)
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (ρ.nonneg j x) (half_pos (hδ j)).le
    · exact ⟨i, (ρ.mem_finsupport x).mpr (ne_of_gt hi), mul_pos hi (half_pos (hδ i))⟩
  refine ⟨⟨εval, hε⟩, hεpos, ?_⟩
  intro x s t hst
  -- Some active local radius exceeds the weighted half-radius; no minimum is chosen.
  have hlarge : ∃ i ∈ ρ.finsupport x, εval x < δ i := by
    by_contra! hn
    have hle : εval x ≤ εval x / 2 := by
      calc
        εval x = ∑ i ∈ ρ.finsupport x, ρ i x * (δ i / 2) := hεsum x
        _ ≤
            ∑ i ∈ ρ.finsupport x, ρ i x * (εval x / 2) :=
          Finset.sum_le_sum (fun i hi ↦
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hn i hi) (by norm_num))
              (ρ.nonneg i x))
        _ = εval x / 2 := by rw [← Finset.sum_mul, ρ.sum_finsupport (Set.mem_univ x), one_mul]
    linarith [hεpos x]
  obtain ⟨i, hi, hlarge⟩ := hlarge
  apply hnear i x (hρ i (subset_closure ((ρ.mem_finsupport x).mp hi))) s t
  exact lt_of_le_of_lt hst hlarge

end DiagonalTransport

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [hT : T2Space X] [hP : ParacompactSpace X]

attribute [local instance] isFiniteRank_pullback sumTopology trivialTopology

include hT hP

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Compose original fiber maps until the continuous clipped time grid is locally stationary.
/-- Hatcher 1.7: a bundle on a paracompact cylinder has isomorphic endpoint pullbacks. -/
theorem nonempty_endpoint_pullback_iso (E : FiniteBundle (X × unitInterval)) :
    Nonempty (Iso
      (((⟨fun x ↦ (x, (0 : unitInterval)), continuous_id.prodMk continuous_const⟩ :
        C(X, X × unitInterval)) : X → X × unitInterval) *ᵖ E.Fiber)
      (((⟨fun x ↦ (x, (1 : unitInterval)), continuous_id.prodMk continuous_const⟩ :
        C(X, X × unitInterval)) : X → X × unitInterval) *ᵖ E.Fiber)) := by
  classical
  let B := X × unitInterval
  let pr₁ : C(B × B, B) := ContinuousMap.fst
  let pr₂ : C(B × B, B) := ContinuousMap.snd
  obtain ⟨T, hT⟩ := exists_diagonal_transport E.Fiber
  let U : Set (X × (unitInterval × unitInterval)) :=
    {z | Function.Bijective (T.linearMap ((z.1, z.2.1), (z.1, z.2.2)))}
  have hU : IsOpen U := (Hom.isOpen_setOf_bijective ((pr₁ : B × B → B) *ᵖ E.Fiber) T).preimage
    ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  have hdiag : ∀ x t, (x, t, t) ∈ U := by
    intro x t
    change Function.Bijective (T.linearMap ((x, t), (x, t)))
    rw [hT]
    exact Function.bijective_id
  obtain ⟨ε, hε, hnear⟩ := exists_continuous_time_step U hU hdiag
  -- The clipped uniform grid is continuous and reaches the endpoint locally in finitely many steps.
  let time (n : ℕ) (x : X) : unitInterval :=
    ⟨min 1 ((n : ℝ) * ε x), le_min zero_le_one (mul_nonneg (Nat.cast_nonneg n) (hε x).le),
      min_le_left _ _⟩
  have htime (n : ℕ) : Continuous (time n) :=
    (continuous_const.min (continuous_const.mul ε.continuous)).subtype_mk _
  have hmono (x : X) : Monotone (fun n ↦ time n x) := by
    intro n m hnm
    exact min_le_min_left 1 (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm) (hε x).le)
  have hstep (n : ℕ) (x : X) : dist (time n x) (time (n + 1) x) ≤ ε x := by
    change |min 1 ((n : ℝ) * ε x) - min 1 (((n + 1 : ℕ) : ℝ) * ε x)| ≤ ε x
    have hreal : (time n x : ℝ) ≤ (time (n + 1) x : ℝ) := hmono x (Nat.le_succ n)
    rw [abs_of_nonpos (sub_nonpos.mpr hreal)]
    have hn : (n : ℝ) * ε x ≤ ((n + 1 : ℕ) : ℝ) * ε x :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) (hε x).le
    dsimp only [time]
    rw [Nat.cast_add, Nat.cast_one]
    by_cases hsmall : (n : ℝ) * ε x ≤ 1
    · rw [min_eq_right hsmall]
      have hle := min_le_right (1 : ℝ) (((n : ℝ) + 1) * ε x)
      nlinarith
    · rw [min_eq_left (le_of_not_ge hsmall), min_eq_left (by
        push_cast at hn
        linarith)]
      linarith [hε x]
  let f (n : ℕ) : C(X, B) := ⟨fun x ↦ (x, time n x), continuous_id.prodMk (htime n)⟩
  let p₀ : C(X, B) := ⟨fun x ↦ (x, 0), continuous_id.prodMk continuous_const⟩
  let p₁ : C(X, B) := ⟨fun x ↦ (x, 1), continuous_id.prodMk continuous_const⟩
  let pair (n : ℕ) : C(X, B × B) := (f n).prodMk (f (n + 1))
  let step (n : ℕ) : Hom ((f n : X → B) *ᵖ E.Fiber)
      ((f (n + 1) : X → B) *ᵖ E.Fiber) :=
    { linearMap x := T.linearMap (pair n x)
      continuous_total := by
        have hin : Continuous (fun z : TotalSpace Unit ((f n : X → B) *ᵖ E.Fiber) ↦
            (⟨pair n z.proj, z.snd⟩ : TotalSpace Unit (pr₁ *ᵖ E.Fiber))) := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber pr₁).continuous_iff]
          exact ((pair n).continuous.comp continuous_proj).prodMk
            (Pullback.continuous_lift Unit E.Fiber (f n))
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber (f (n + 1))).continuous_iff]
        exact continuous_proj.prodMk
          ((Pullback.continuous_lift Unit E.Fiber pr₂).comp (T.continuous_total.comp hin)) }
  have hbij (n : ℕ) (x : X) : Function.Bijective ((step n).linearMap x) :=
    hnear x (time n x) (time (n + 1) x) (hstep n x)
  let S (n : ℕ) := (step n).toIso (hbij n)
  have hf : f 0 = p₀ := by
    apply ContinuousMap.ext
    intro x
    change (x, time 0 x) = (x, (0 : unitInterval))
    congr 1
    apply Subtype.ext
    simp only [time, Nat.cast_zero, zero_mul, min_eq_right zero_le_one, Set.Icc.coe_zero]
  let M₀ : Iso ((p₀ : X → B) *ᵖ E.Fiber) ((f 0 : X → B) *ᵖ E.Fiber) := by
    rw [hf]
    exact Iso.refl _
  let M : (n : ℕ) → Iso ((p₀ : X → B) *ᵖ E.Fiber) ((f n : X → B) *ᵖ E.Fiber) :=
    Nat.rec M₀ (fun n a ↦ a.trans (S n))
  let D := TotalSpace Unit ((p₀ : X → B) *ᵖ E.Fiber)
  let A (n : ℕ) (z : D) : TotalSpace Unit E.Fiber :=
    ⟨f n z.proj, (M n).linearEquiv z.proj z.snd⟩
  have hA (n : ℕ) : Continuous (A n) :=
    (Pullback.continuous_lift Unit E.Fiber (f n)).comp (M n).continuous_total
  have hstationary {a b : B} (hab : a = b) (v : E.Fiber a) :
      (⟨b, T.linearMap (a, b) v⟩ : TotalSpace Unit E.Fiber) = ⟨a, v⟩ := by
    subst b
    rw [hT]
    rfl
  have hdone (n : ℕ) (x : X) (hn : time n x = 1) (m : ℕ) (hnm : n ≤ m) :
      time m x = 1 := le_antisymm (time m x).property.2 (by
        rw [← hn]
        exact hmono x hnm)
  have hsucc (n : ℕ) (z : D) (hn : time n z.proj = 1) : A (n + 1) z = A n z := by
    change (⟨f (n + 1) z.proj, T.linearMap (f n z.proj, f (n + 1) z.proj)
      ((M n).linearEquiv z.proj z.snd)⟩ : TotalSpace Unit E.Fiber) = _
    exact hstationary (congrArg (fun t ↦ (z.proj, t))
      (hn.trans (hdone n z.proj hn (n + 1) (Nat.le_succ n)).symm)) _
  have hstable (n m : ℕ) (hnm : n ≤ m) (z : D) (hn : time n z.proj = 1) :
      A m z = A n z := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih => exact (hsucc m z (hdone n z.proj hn m hnm)).trans ih
  have hreach (x : X) : ∃ n : ℕ, 1 < (n : ℝ) * ε x := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε x)
    exact ⟨n, (div_lt_iff₀ (hε x)).mp hn⟩
  choose N hN using hreach
  have hNtime (x : X) : time (N x) x = 1 :=
    Subtype.ext (min_eq_left (hN x).le)
  let castFiber (x : X) (s t : unitInterval) (hst : s = t) :
      E.Fiber (x, s) ≃ₗ[ℂ] E.Fiber (x, t) := by
    subst t
    exact LinearEquiv.refl _ _
  have hcast (x : X) (s t : unitInterval) (hst : s = t) (v : E.Fiber (x, s)) :
      (⟨(x, t), castFiber x s t hst v⟩ : TotalSpace Unit E.Fiber) = ⟨(x, s), v⟩ := by
    subst t
    rfl
  let L (x : X) : E.Fiber (x, 0) ≃ₗ[ℂ] E.Fiber (x, 1) :=
    ((M (N x)).linearEquiv x).trans (castFiber x (time (N x) x) 1 (hNtime x))
  have hL (z : D) : (⟨p₁ z.proj, L z.proj z.snd⟩ : TotalSpace Unit E.Fiber) =
      A (N z.proj) z := hcast z.proj _ _ (hNtime z.proj) _
  -- Local finite stabilization proves continuity even when the chosen stopping index jumps.
  have hcont : Continuous (fun z : D ↦
      (⟨p₁ z.proj, L z.proj z.snd⟩ : TotalSpace Unit E.Fiber)) := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    let n := N z₀.proj
    have hnbhd : ∀ᶠ x in 𝓝 z₀.proj, 1 < (n : ℝ) * ε x :=
      (continuous_const.mul ε.continuous).continuousAt.eventually
        (Ioi_mem_nhds (hN z₀.proj))
    apply (hA n).continuousAt.congr_of_eventuallyEq
    filter_upwards [(continuous_proj (E := (p₀ : X → B) *ᵖ E.Fiber)).continuousAt.eventually
      hnbhd] with z hz
    rw [hL]
    have hn : time n z.proj = 1 := Subtype.ext (min_eq_left hz.le)
    calc
      A (N z.proj) z = A (max n (N z.proj)) z :=
        (hstable (N z.proj) (max n (N z.proj)) (le_max_right _ _) z (hNtime z.proj)).symm
      _ = A n z := hstable n (max n (N z.proj)) (le_max_left _ _) z hn
  let result : Hom ((p₀ : X → B) *ᵖ E.Fiber) ((p₁ : X → B) *ᵖ E.Fiber) :=
    { linearMap x := (L x).toLinearMap
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber p₁).continuous_iff]
        exact continuous_proj.prodMk hcont }
  exact ⟨result.toIso (fun x ↦ (L x).bijective)⟩

/-- Hatcher 1.6: homotopic maps induce isomorphic actual pullback bundles. -/
theorem nonempty_pullback_iso_of_homotopic (E : FiniteBundle Y)
    (f g : C(X, Y)) (hfg : f.Homotopic g) :
    Nonempty (Iso ((f : X → Y) *ᵖ E.Fiber) ((g : X → Y) *ᵖ E.Fiber)) := by
  obtain ⟨H⟩ := hfg
  let c : C(X × unitInterval, Y) :=
    ⟨fun z ↦ H (z.2, z.1), H.continuous.comp continuous_swap⟩
  let p₀ : C(X, X × unitInterval) :=
    ⟨fun x ↦ (x, 0), continuous_id.prodMk continuous_const⟩
  let p₁ : C(X, X × unitInterval) :=
    ⟨fun x ↦ (x, 1), continuous_id.prodMk continuous_const⟩
  obtain ⟨i⟩ := nonempty_endpoint_pullback_iso (E.pullback c)
  have hf : c.comp p₀ = f := by
    apply ContinuousMap.ext
    intro x
    exact H.apply_zero x
  have hg : c.comp p₁ = g := by
    apply ContinuousMap.ext
    intro x
    exact H.apply_one x
  rw [← hf, ← hg]
  exact ⟨(pullbackCompIso (E := E.Fiber) c p₀).symm.trans
    (i.trans (pullbackCompIso (E := E.Fiber) c p₁))⟩

attribute [local instance] isFiniteRank_sum isFiniteRank_trivial
  IdempotentMatrix.fiberTotalSpaceTopology IdempotentMatrix.isFiniteRank_fiber

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A bundle over a space of finite CW homotopy type has a finite trivial complement. -/
theorem FiniteBundle.exists_complement_of_homotopyEquiv_finiteCW
    [T2Space Y] (C : Set Y) [Topology.CWComplex C] [Topology.CWComplex.Finite C]
    (e : ContinuousMap.HomotopyEquiv X C) (E : FiniteBundle X) :
    ∃ (G : FiniteBundle X) (r : ℕ),
      Nonempty (Iso (E.Fiber ×ᵇ G.Fiber) (Bundle.Trivial X (Fin r → ℂ))) := by
  classical
  -- A finite CW complex is compact, so its actual pulled-back bundle has a finite complement.
  let : Finite (Σ n, Topology.RelCWComplex.cell C n) :=
    Topology.RelCWComplex.finite_cells_of_finite
  have hC : IsCompact C := by
    have hc := isCompact_iUnion (fun ni : (Σ n, Topology.RelCWComplex.cell C n) ↦
      Topology.RelCWComplex.isCompact_closedCell (C := C) (n := ni.1) (i := ni.2))
    simpa only [Set.iUnion_sigma, Topology.CWComplex.union] using hc
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let c : C(X, C) := e.toFun
  let d : C(C, X) := e.invFun
  let F₀ := E.pullback d
  obtain ⟨p, ⟨j⟩⟩ := exists_complement_bundle (E := F₀.Fiber)
  let G₀ : FiniteBundle C := FiniteBundle.ofFamily (fun y ↦ p.complement.fiber y)
  let G := G₀.pullback c
  -- The original homotopy equivalence identifies the double pullback with E itself.
  obtain ⟨h⟩ := nonempty_pullback_iso_of_homotopic E (d.comp c) (ContinuousMap.id X) e.left_inv
  let k : Iso ((c : X → C) *ᵖ F₀.Fiber) E.Fiber :=
    (pullbackCompIso (E := E.Fiber) d c).trans (h.trans (pullbackIdIso (E := E.Fiber)))
  -- The sum/pullback comparison is the identity on the two specified original vectors.
  let sumMap : Hom (((c : X → C) *ᵖ F₀.Fiber) ×ᵇ ((c : X → C) *ᵖ G₀.Fiber))
      ((c : X → C) *ᵖ (F₀.Fiber ×ᵇ G₀.Fiber)) :=
    { linearMap _ := LinearMap.id
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (F₀.Fiber ×ᵇ G₀.Fiber) c).continuous_iff]
        apply continuous_proj.prodMk
        apply continuous_induced_rng.mpr
        exact ((Pullback.continuous_lift Unit F₀.Fiber c).comp
          (continuous_sum_fst (E := c *ᵖ F₀.Fiber) (F := c *ᵖ G₀.Fiber))).prodMk
            ((Pullback.continuous_lift Unit G₀.Fiber c).comp
              (continuous_sum_snd (E := c *ᵖ F₀.Fiber) (F := c *ᵖ G₀.Fiber))) }
  let s := sumMap.toIso (fun _ ↦ Function.bijective_id)
  refine ⟨G, p.size, ⟨?_⟩⟩
  exact (k.symm.sum (Iso.refl G.Fiber)).trans
    (s.trans ((j.pullback c).trans (pullbackTrivialIso c p.size)))

end AtiyahSinger.ComplexBundle
