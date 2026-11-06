/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Separation and local compactness of finite vector-bundle total spaces

Public module ID: M1849.

The existing local finite-rank condition allows different ranks on different open
components. The actual total-space topology, rather than a fiberwise coproduct
or a newly chosen topology, inherits Hausdorffness and local compactness from the
base and finite complex coordinate spaces. These standard bundle facts supply the
ambient spaces for SG Appendix C's compact-support Thom construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]

include hE

/-- A finite complex bundle over a Hausdorff base has a Hausdorff total space. -/
theorem t2Space_totalSpace [T2Space X] : T2Space (TotalSpace Unit E) := by
  /- For two points with distinct base points, pull back disjoint base neighborhoods
  using the existing continuous projection. For points over the same base point,
  choose one local linear trivialization. Its source is open and its target is an
  open subset of X times a finite complex coordinate space, hence Hausdorff.
  Separate the two coordinate vectors there and return through that same chart.
  The ranks need not agree on disjoint trivializing neighborhoods. -/
  apply t2Space_iff_disjoint_nhds.mpr
  intro z w hzw
  by_cases hbase : z.proj = w.proj
  · -- One finite chart separates both points lying over the same base point.
    obtain ⟨r, e, hz, _⟩ := IsFiniteRank.exists_linear_trivialization (E := E) z.proj
    have hzs : z ∈ e.source := e.mem_source.mpr hz
    have hws : w ∈ e.source := e.mem_source.mpr (hbase ▸ hz)
    have hcoords : e z ≠ e w := fun h ↦ hzw (e.injOn hzs hws h)
    exact (e.continuousAt hzs).disjoint (disjoint_nhds_nhds.mpr hcoords)
      (e.continuousAt hws)
  · -- Distinct base points are separated by the original continuous projection.
    exact (continuous_proj (E := E)).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase) (continuous_proj (E := E)).continuousAt

/-- A finite complex bundle over a locally compact base has a locally compact total space. -/
theorem locallyCompactSpace_totalSpace [LocallyCompactSpace X] :
    LocallyCompactSpace (TotalSpace Unit E) := by
  /- Around the base of a given total-space point choose a finite linear chart.
  Its open target is a product of a base neighborhood and a finite complex space.
  The latter is proper and locally compact; products and open subspaces preserve
  local compactness. Transfer a compact neighborhood through the local
  homeomorphism. Since the chart source is open, this is local compactness in the
  original total topology. Empty bases and zero-rank charts are included. -/
  constructor
  intro z s hs
  -- Work in one chart, whose dimension is allowed to depend on the base point.
  obtain ⟨r, t, hz, _⟩ := IsFiniteRank.exists_linear_trivialization (E := E) z.proj
  let e := t.toOpenPartialHomeomorph
  have hzs : z ∈ e.source := t.mem_source.mpr hz
  have hzt : e z ∈ e.target := e.map_source hzs
  have hn : e.symm ⁻¹' s ∩ e.target ∈ nhds (e z) :=
    Filter.inter_mem (e.tendsto_symm hzs hs) (e.open_target.mem_nhds hzt)
  obtain ⟨K, hKn, hKs, hK⟩ := local_compact_nhds hn
  -- Transfer a compact neighborhood back through this same inverse chart.
  refine ⟨e.symm '' K, ?_, ?_, ?_⟩
  · simpa only [e.left_inv hzs] using e.symm.image_mem_nhds hzt hKn
  · rintro _ ⟨y, hy, rfl⟩
    exact (hKs hy).1
  · exact hK.image_of_continuousOn (e.continuousOn_symm.mono fun y hy ↦ (hKs hy).2)

end AtiyahSinger.ComplexBundle
