/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Separation and local compactness of the original fiber-bundle total space

Public module ID: M1846.

The native FiberBundle charts transfer the standard product properties to the
unchanged total-space topology. These general facts supply the topological
hypotheses needed for compact-support K theory of a real vector-bundle total
space. Neither a vector-space structure nor a spin structure is required.

These are standard consequences of local triviality, supplied here because the
current mathlib FiberBundle API has no corresponding total-space instances.
They complement its existing fiberwise separation theorem. The chart argument
is the same as for the project's finite complex bundles, with the native
FiberBundle charts retained throughout.
-/

@[expose] public section

namespace AtiyahSinger

open Bundle

variable {B : Type*} [TopologicalSpace B]
  (F : Type*) [TopologicalSpace F] (E : B → Type*)
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [hE : FiberBundle F E]

include hE

/-- A fiber bundle with Hausdorff base and model fiber has a Hausdorff total space. -/
theorem t2Space_fiberBundleTotal [T2Space B] [T2Space F] :
    T2Space (TotalSpace F E) := by
  /- Stage 1: if the base points differ, separate them in B and pull their
  disjoint neighborhoods back by the original continuous bundle projection.
  Stage 2: over one base point choose a native trivialization containing both
  total-space points. Its source is open and its target is the product of an
  open base neighborhood with F. Separate the two images in this Hausdorff
  product and pull the disjoint open neighborhoods back through that chart.
  This proves separation for the original total topology, without replacing
  the bundle or assuming that arbitrary locally Hausdorff spaces are Hausdorff. -/
  apply t2Space_iff_disjoint_nhds.mpr
  intro x y hxy
  by_cases hbase : x.proj = y.proj
  · -- One chart separates points in the same fiber by their actual coordinates.
    let e := trivializationAt F E x.proj
    have hx : x ∈ e.source := e.mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
    have hy : y ∈ e.source := e.mem_source.mpr (hbase ▸ e.mem_source.mp hx)
    have hcoords : e x ≠ e y := fun h ↦ hxy (e.injOn hx hy h)
    exact (e.continuousAt hx).disjoint (disjoint_nhds_nhds.mpr hcoords)
      (e.continuousAt hy)
  · -- Distinct base points are separated by the original continuous projection.
    exact (FiberBundle.continuous_proj F E).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase) (FiberBundle.continuous_proj F E).continuousAt

/-- A fiber bundle with locally compact base and model fiber has locally compact total space. -/
theorem locallyCompactSpace_fiberBundleTotal [LocallyCompactSpace B]
    [LocallyCompactSpace F] : LocallyCompactSpace (TotalSpace F E) := by
  /- Stage 1: choose a native trivialization around the base of a given point.
  Its target is the product of an open base neighborhood with the original
  model fiber. Local compactness is preserved by these open subspaces and
  products. Stage 2: transfer a compact neighborhood through the inverse
  chart. Since the chart source is open in the original total space, this
  gives the required local compactness there. No Hausdorffness, compact base,
  fixed algebraic dimension or linearity of transition maps is needed. -/
  constructor
  intro x s hs
  -- Transport the requested neighborhood into a single native bundle chart.
  let e := (trivializationAt F E x.proj).toOpenPartialHomeomorph
  have hx : x ∈ e.source :=
    (trivializationAt F E x.proj).mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
  have ht : e x ∈ e.target := e.map_source hx
  have hn : e.symm ⁻¹' s ∩ e.target ∈ nhds (e x) :=
    Filter.inter_mem (e.tendsto_symm hx hs) (e.open_target.mem_nhds ht)
  obtain ⟨K, hKn, hKs, hK⟩ := local_compact_nhds hn
  -- Pull a compact neighborhood back through the continuous inverse on its target.
  refine ⟨e.symm '' K, ?_, ?_, ?_⟩
  · simpa only [e.left_inv hx] using e.symm.image_mem_nhds ht hKn
  · rintro _ ⟨y, hy, rfl⟩
    exact (hKs hy).1
  · exact hK.image_of_continuousOn (e.continuousOn_symm.mono fun y hy ↦ (hKs hy).2)

end AtiyahSinger
