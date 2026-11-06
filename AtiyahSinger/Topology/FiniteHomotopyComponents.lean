/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ManifoldComponents
public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Components of a manifold of finite CW homotopy type

Public module ID: M1853.

The inverse of a specified homotopy equivalence maps a compact finite CW model
onto the component quotient. Its fibers are finite subcomplexes, and restricting
both maps and their homotopies gives actual finite CW models for the original
open manifold components. No compactness of the manifold is inferred.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open TopologicalSpace ContinuousMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [hchart : ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {Y : Type*} [TopologicalSpace Y] [T2Space Y]

include hchart

omit [T2Space Y] in
/-- Finite CW homotopy type gives finitely many components of the original manifold. -/
theorem finite_connectedComponents_of_homotopyEquiv_finiteCW
    (C : Set Y) [Topology.CWComplex C] [Topology.CWComplex.Finite C]
    (e : HomotopyEquiv M C) : Finite (ConnectedComponents M) := by
  classical
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  -- Compactness belongs to the finite model, and its image in the discrete quotient is finite.
  let : Finite (Σ j, Topology.RelCWComplex.cell C j) :=
    Topology.RelCWComplex.finite_cells_of_finite
  have hC : IsCompact C := by
    have hc := isCompact_iUnion (fun ji : (Σ j, Topology.RelCWComplex.cell C j) ↦
      Topology.RelCWComplex.isCompact_closedCell (C := C) (n := ji.1) (i := ji.2))
    simpa only [Set.iUnion_sigma, Topology.CWComplex.union] using hc
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let f : C → ConnectedComponents M := fun y ↦ ConnectedComponents.mk (e.symm y)
  have hf : Continuous f := ConnectedComponents.continuous_coe.comp e.symm.continuous
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨H⟩ := e.left_inv
    have hc : Continuous (fun t : unitInterval ↦ ConnectedComponents.mk (H (t, x))) :=
      ConnectedComponents.continuous_coe.comp
        (H.continuous.comp (continuous_id.prodMk continuous_const))
    refine ⟨e x, ?_⟩
    simpa only [H.apply_zero, H.apply_one, ContinuousMap.comp_apply,
      ContinuousMap.id_apply, f, HomotopyEquiv.symm] using
        ((inferInstance : PreconnectedSpace unitInterval).constant hc (x := 0) (y := 1))
  have hr : Set.range f = Set.univ := Set.range_eq_univ.mpr hsurj
  have hfinite := (isCompact_range hf).finite_of_discrete
  rw [hr] at hfinite
  exact Set.finite_univ_iff.mp hfinite

/-- Each original open component has an actual finite CW homotopy model. -/
theorem exists_homotopyEquiv_finiteCW_manifoldComponent
    (C : Set Y) [Topology.CWComplex C] [Topology.CWComplex.Finite C]
    (e : HomotopyEquiv M C) (c : ConnectedComponents M) :
    ∃ D : Set Y, ∃ _hD : Topology.CWComplex D, ∃ _ : Topology.CWComplex.Finite D,
      Nonempty (HomotopyEquiv (manifoldComponent (n := n) c) D) := by
  classical
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let f : C(C, ConnectedComponents M) :=
    ⟨fun y ↦ ConnectedComponents.mk (e.symm y),
      ConnectedComponents.continuous_coe.comp e.symm.continuous⟩
  let D : Set Y := Subtype.val '' (f ⁻¹' {c})
  have hmem (y : Y) : y ∈ D ↔ ∃ hy : y ∈ C, f ⟨y, hy⟩ = c := by
    simp only [D, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨y, hy⟩, h, rfl⟩
      exact ⟨hy, h⟩
    · rintro ⟨hy, h⟩
      exact ⟨⟨y, hy⟩, h, rfl⟩
  have hDC : D ⊆ C := fun y hy ↦ ((hmem y).mp hy).choose
  have hDclosed : IsClosed D :=
    (Topology.RelCWComplex.isClosed (C := C)).isClosedEmbedding_subtypeVal.isClosedMap
      _ (isClosed_singleton.preimage f.continuous)
  -- A characteristic cell cannot cross a fiber of the discrete component quotient.
  have hcell (k : ℕ) (i : Topology.CWComplex.cell C k)
      (x y : Y) (hx : x ∈ Topology.CWComplex.openCell (C := C) k i)
      (hy : y ∈ Topology.CWComplex.openCell (C := C) k i) :
      f ⟨x, Topology.CWComplex.openCell_subset_complex (C := C) k i hx⟩ =
        f ⟨y, Topology.CWComplex.openCell_subset_complex (C := C) k i hy⟩ := by
    have hc : IsPreconnected (Topology.CWComplex.openCell (C := C) k i) :=
      (convex_ball (0 : Fin k → ℝ) 1).isPreconnected.image _
        ((Topology.CWComplex.continuousOn (C := C) k i).mono Metric.ball_subset_closedBall)
    let j : (Topology.CWComplex.openCell (C := C) k i) → C :=
      fun z ↦ ⟨z.val, Topology.CWComplex.openCell_subset_complex (C := C) k i z.property⟩
    have hj : Continuous j := continuous_subtype_val.subtype_mk _
    exact (isPreconnected_iff_preconnectedSpace.mp hc).constant
      (f.continuous.comp hj) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)
  let S : Topology.CWComplex.Subcomplex C :=
    { carrier := D
      I k := {i | Topology.CWComplex.openCell (C := C) k i ⊆ D}
      closed' := hDclosed
      union' := by
        rw [Set.empty_union]
        apply Set.Subset.antisymm
        · rintro x hx
          obtain ⟨k, ⟨i, hi⟩, hx⟩ := Set.mem_iUnion.mp hx |>.imp fun _ ↦ Set.mem_iUnion.mp
          exact hi hx
        · intro x hx
          have hxC := hDC hx
          rw [← Topology.CWComplex.iUnion_openCell_eq_complex (C := C)] at hxC
          obtain ⟨k, i, hxi⟩ := Set.mem_iUnion.mp hxC |>.imp fun _ ↦ Set.mem_iUnion.mp
          have hi : Topology.CWComplex.openCell (C := C) k i ⊆ D := by
            intro y hy
            apply (hmem y).mpr
            refine ⟨Topology.CWComplex.openCell_subset_complex (C := C) k i hy, ?_⟩
            exact (hcell k i y x hy hxi).trans ((hmem x).mp hx).choose_spec
          exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩⟩ }
  let hD : Topology.CWComplex D := Topology.CWComplex.Subcomplex.instCWComplex S
  let hDf : Topology.CWComplex.Finite D :=
    Topology.RelCWComplex.Subcomplex.finite_subcomplex_of_finite S
  obtain ⟨H⟩ := e.left_inv
  obtain ⟨J⟩ := e.right_inv
  have hH (t : unitInterval) (x : M) :
      ConnectedComponents.mk (H (t, x)) = ConnectedComponents.mk x := by
    have hc : Continuous (fun s : unitInterval ↦ ConnectedComponents.mk (H (s, x))) :=
      ConnectedComponents.continuous_coe.comp
        (H.continuous.comp (continuous_id.prodMk continuous_const))
    simpa only [H.apply_one, ContinuousMap.id_apply] using
      ((inferInstance : PreconnectedSpace unitInterval).constant hc (x := t) (y := 1))
  have hJ (t : unitInterval) (y : C) : f (J (t, y)) = f y := by
    have hc : Continuous (fun s : unitInterval ↦ f (J (s, y))) :=
      f.continuous.comp (J.continuous.comp (continuous_id.prodMk continuous_const))
    simpa only [J.apply_one, ContinuousMap.id_apply] using
      ((inferInstance : PreconnectedSpace unitInterval).constant hc (x := t) (y := 1))
  -- Restrict the given maps, and restrict the whole two homotopies to these same fibers.
  let r : C(D, C) := ⟨fun y ↦ ⟨y.val, hDC y.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  have hr (y : D) : f (r y) = c := ((hmem y.val).mp y.property).choose_spec
  let a : C(manifoldComponent (n := n) c, D) :=
    ⟨fun x ↦ ⟨(e x.val).val, (hmem _).mpr ⟨(e x.val).property, by
        simpa [f, HomotopyEquiv.symm] using
          (hH 0 x.val).trans x.property⟩⟩,
      (continuous_subtype_val.comp (e.continuous.comp continuous_subtype_val)).subtype_mk _⟩
  let b : C(D, manifoldComponent (n := n) c) :=
    ⟨fun y ↦ ⟨e.symm (r y), hr y⟩,
      (e.symm.continuous.comp r.continuous).subtype_mk _⟩
  let L : ContinuousMap.Homotopy (b.comp a) (ContinuousMap.id _) :=
    { toFun z := ⟨H (z.1, z.2.val), (hH z.1 z.2.val).trans z.2.property⟩
      continuous_toFun := (H.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left x := Subtype.ext (H.apply_zero x.val)
      map_one_left x := Subtype.ext (H.apply_one x.val) }
  let R : ContinuousMap.Homotopy (a.comp b) (ContinuousMap.id _) :=
    { toFun z := ⟨(J (z.1, r z.2)).val,
        (hmem _).mpr ⟨(J (z.1, r z.2)).property, (hJ z.1 (r z.2)).trans (hr z.2)⟩⟩
      continuous_toFun := (continuous_subtype_val.comp (J.continuous.comp
        (continuous_fst.prodMk (r.continuous.comp continuous_snd)))).subtype_mk _
      map_zero_left y := by
        apply Subtype.ext
        change (J (0, r y)).val = (e.toFun (e.invFun (r y))).val
        exact congrArg (fun z : C ↦ z.val) (J.apply_zero (r y))
      map_one_left y := by
        apply Subtype.ext
        exact congrArg (fun z : C ↦ z.val) (J.apply_one (r y)) }
  exact ⟨D, hD, hDf, ⟨⟨a, b, ⟨L⟩, ⟨R⟩⟩⟩⟩

end AtiyahSinger
