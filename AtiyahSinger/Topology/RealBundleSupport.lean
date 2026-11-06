/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Finite real bundles on their original total spaces

Public module ID: M2038.

The real vector bundle rank may vary between components. The standard
local finite-rank condition below retains the supplied total-space topology and
uses finite real coordinate spaces only inside local trivializations. The parameter
`G` is the phantom parameter of `Bundle.TotalSpace`, not a chosen global model fiber.

The projection, zero section and fiberwise scaling give the actual homotopy
equivalence with the base. The separation and countability certificates provide
the ambient hypotheses for compact-support K theory. A native finite-dimensional
mathlib vector bundle satisfies this local condition without changing its total
space. These are standard consequences of local linear triviality, used in the
bundle-representative argument of Spin Geometry, III.13, pp. 245–246.

The continuity and topological certificates use the original local charts. The maps
and homotopy have the stated formulas; the contraction is not asserted
to be proper and does not define a compact-support K-theory pullback.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RealBundle

open Bundle
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X]

section LocallyFinite

variable (G : Type*) (V : X → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace G V)]

/-- A continuous real vector bundle with locally finite, possibly varying rank.
The local linear charts refer to the original total-space topology. -/
class IsFiniteRank : Prop where
  /-- Finite-dimensional linear trivializations cover the base. -/
  exists_linear_trivialization :
    ∀ x : X, ∃ (r : ℕ) (e : Trivialization (Fin r → ℝ) (π G V)),
      x ∈ e.baseSet ∧ ∀ y ∈ e.baseSet,
        IsLinearMap ℝ (fun v : V y ↦ (e ⟨y, v⟩).2)

variable [hV : IsFiniteRank G V]

include hV

/-- Local triviality makes the original total-space projection continuous. -/
theorem continuous_projection : Continuous (π G V) := by
  /- In a local trivialization the original projection is the first coordinate.
  The chart sources are open and cover the original total space, so the local
  continuity statements give continuity of this same projection everywhere. -/
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨r, e, hz, _⟩ := hV.exists_linear_trivialization z.proj
  -- In this chart the same projection is the first coordinate.
  exact e.continuousAt_proj (e.mem_source.mpr hz)

/-- The original real-bundle projection as a continuous map. -/
def projection : C(TotalSpace G V, X) where
  toFun := π G V
  continuous_toFun := continuous_projection G V

/-- Local linear triviality makes the actual zero section continuous. -/
theorem continuous_zeroSection :
    Continuous (fun x : X ↦ (⟨x, 0⟩ : TotalSpace G V)) := by
  /- In a linear chart the zero section is x ↦ (x,0). This map is continuous
  into the chart target, and the inverse chart is continuous on that target.
  Apply this argument on the open base sets covering X. -/
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨r, e, hx, hlin⟩ := hV.exists_linear_trivialization x
  -- The chart criterion reduces continuity to the base and zero fiber coordinate.
  apply (e.tendsto_nhds_iff (e.mem_source.mpr hx)).mpr
  refine ⟨continuousAt_id, ?_⟩
  rw [(hlin x hx).map_zero]
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact (hlin y hy).map_zero.symm

/-- The actual zero section into the original total space. -/
def zeroSection : C(X, TotalSpace G V) where
  toFun := fun x ↦ ⟨x, 0⟩
  continuous_toFun := continuous_zeroSection G V

/-- Scalar multiplication is jointly continuous on the original real-bundle total space. -/
theorem continuous_scaling :
    Continuous (fun p : ℝ × TotalSpace G V ↦
      (⟨p.2.proj, p.1 • p.2.snd⟩ : TotalSpace G V)) := by
  /- Stage 1: around the base of a given total-space point choose one finite
  linear chart. Scaling preserves this base, so both the input and output stay
  in the same chart source. Linearity identifies the coordinate expression
  with (t,(x,v)) ↦ (x,t • v), continuous in finite real coordinates.
  Stage 2: compose with the chart and its inverse and use this open cover of
  the product domain. No topology or norm on an auxiliary global model G is
  introduced, and ranks on different components need not agree. -/
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨r, e, hz, hlin⟩ := hV.exists_linear_trivialization z.2.proj
  have hsource : z.2 ∈ e.source := e.mem_source.mpr hz
  have houtput : (⟨z.2.proj, z.1 • z.2.snd⟩ : TotalSpace G V) ∈ e.source :=
    e.mem_source.mpr hz
  -- Scaling preserves the base, so both sides use the same local linear chart.
  apply (e.tendsto_nhds_iff houtput).mpr
  refine ⟨((continuous_projection G V).comp continuous_snd).continuousAt, ?_⟩
  have hcoords : ContinuousAt (fun p : ℝ × TotalSpace G V ↦ p.1 • (e p.2).2) z :=
    continuousAt_fst.smul ((e.continuousAt hsource).comp continuousAt_snd).snd
  rw [(hlin z.2.proj hz).map_smul]
  apply Filter.Tendsto.congr' _ hcoords
  have hbase := ((continuous_projection G V).comp continuous_snd).continuousAt
    (e.open_baseSet.mem_nhds hz)
  filter_upwards [hbase] with p hp
  exact ((hlin p.2.proj hp).map_smul p.1 p.2.snd).symm

/-- Fiberwise scaling from the zero-section retraction to the identity. -/
def scalingHomotopy :
    ContinuousMap.Homotopy ((zeroSection G V).comp (projection G V))
      (ContinuousMap.id (TotalSpace G V)) where
  toFun := fun p ↦ ⟨p.2.proj, (p.1 : ℝ) • p.2.snd⟩
  continuous_toFun := (continuous_scaling G V).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left := by
    intro z
    change (⟨z.proj, (0 : ℝ) • z.snd⟩ : TotalSpace G V) = ⟨z.proj, 0⟩
    simp only [zero_smul]
  map_one_left := by
    intro z
    change (⟨z.proj, (1 : ℝ) • z.snd⟩ : TotalSpace G V) = z
    simp only [one_smul]

/-- The actual bundle projection and zero section form a homotopy equivalence. -/
def homotopyEquiv : ContinuousMap.HomotopyEquiv (TotalSpace G V) X where
  toFun := projection G V
  invFun := zeroSection G V
  left_inv := ⟨scalingHomotopy G V⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id X)⟩

/-- A finite real bundle over a Hausdorff base has a Hausdorff total space. -/
theorem t2Space_totalSpace [T2Space X] : T2Space (TotalSpace G V) := by
  /- Stage 1: points with distinct bases are separated by the inverse images
  of disjoint base neighborhoods under the continuous original projection.
  Stage 2: points over the same base lie in one finite linear chart source.
  Separate their images in the Hausdorff product of X with a finite real
  coordinate space and pull those open neighborhoods back through that chart.
  Its source is open in the original total topology. -/
  apply t2Space_iff_disjoint_nhds.mpr
  intro x y hxy
  by_cases hbase : x.proj = y.proj
  · -- A single chart contains both points when their bases agree.
    obtain ⟨r, e, hx, _⟩ := hV.exists_linear_trivialization x.proj
    have hxs : x ∈ e.source := e.mem_source.mpr hx
    have hys : y ∈ e.source := e.mem_source.mpr (hbase ▸ hx)
    have hcoords : e x ≠ e y := fun h ↦ hxy (e.injOn hxs hys h)
    exact (e.continuousAt hxs).disjoint (disjoint_nhds_nhds.mpr hcoords)
      (e.continuousAt hys)
  · -- For different bases, pull separation back along the original projection.
    exact (continuous_projection G V).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase) (continuous_projection G V).continuousAt

/-- A finite real bundle over a locally compact base has a locally compact total space. -/
theorem locallyCompactSpace_totalSpace [LocallyCompactSpace X] :
    LocallyCompactSpace (TotalSpace G V) := by
  /- Choose a finite linear chart around the base of a given point. Its target
  is the product of an open base neighborhood with a finite real coordinate
  space, hence locally compact. Transfer a compact neighborhood through the
  inverse chart and use openness of the chart source in the original total
  space. This also covers zero-rank charts and requires no global rank bound. -/
  constructor
  intro x s hs
  obtain ⟨r, t, hx, _⟩ := hV.exists_linear_trivialization x.proj
  let e := t.toOpenPartialHomeomorph
  have hxs : x ∈ e.source := t.mem_source.mpr hx
  have ht : e x ∈ e.target := e.map_source hxs
  -- Choose a compact coordinate neighborhood inside the chart and the requested set.
  have hn : e.symm ⁻¹' s ∩ e.target ∈ nhds (e x) :=
    Filter.inter_mem (e.tendsto_symm hxs hs) (e.open_target.mem_nhds ht)
  obtain ⟨K, hKn, hKs, hK⟩ := local_compact_nhds hn
  refine ⟨e.symm '' K, ?_, ?_, ?_⟩
  · simpa only [e.left_inv hxs] using e.symm.image_mem_nhds ht hKn
  · rintro _ ⟨y, hy, rfl⟩
    exact (hKs hy).1
  · -- Compactness transfers through the actual inverse, continuous on this target.
    exact hK.image_of_continuousOn (e.continuousOn_symm.mono fun y hy ↦ (hKs hy).2)

/-- A finite real bundle over a second-countable base has a second-countable total space. -/
theorem secondCountableTopology_totalSpace [SecondCountableTopology X] :
    SecondCountableTopology (TotalSpace G V) := by
  /- Stage 1: the trivializing base sets form an open cover of the Lindelof
  base. Choose a countable subcover; their full inverse images cover the total
  space. Each such source is homeomorphic to an open base subset times a
  finite real coordinate space, hence has a countable topological basis.
  Stage 2: take the union of these countably many local bases. Since every
  chart source is open in the original total space, this is a countable basis
  for its original topology. The ranks may vary across the selected charts. -/
  classical
  choose r e hx hlin using hV.exists_linear_trivialization
  -- Second countability of the base supplies a countable subcover of chart base sets.
  obtain ⟨s, hs, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x ↦ (e x).baseSet) (fun x ↦ (e x).open_baseSet)
  let : Countable s := hs.to_subtype
  let (i : s) : SecondCountableTopology (e i.val).source :=
    (e i.val).toOpenPartialHomeomorph.secondCountableTopology_source
  -- Each open total-space chart has a countable basis in its own finite dimension.
  apply TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun i : s ↦ (e i.val).source) (fun i ↦ (e i.val).open_source)
  apply Set.eq_univ_of_forall
  intro z
  have hz : z.proj ∈ ⋃ x ∈ s, (e x).baseSet := by
    rw [hcover]
    exact Set.mem_iUnion.mpr ⟨z.proj, hx z.proj⟩
  obtain ⟨x, hxs⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hxs, hz⟩ := Set.mem_iUnion.mp hxs
  exact Set.mem_iUnion.mpr ⟨⟨x, hxs⟩, (e x).mem_source.mpr hz⟩

end LocallyFinite

/-- A native finite-dimensional real vector bundle satisfies local finite rank
on precisely the same total space and topology. -/
theorem isFiniteRank_of_vectorBundle
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (V : X → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V] : IsFiniteRank F V := by
  /- Stage 1: choose the native linear trivialization at each base point.
  A finite basis identifies its model F continuously and linearly with
  Fin (Module.finrank ℝ F) → ℝ, including the zero-dimensional case.
  Stage 2: postcompose only the fiber coordinate of the native chart with
  this equivalence. The base set and source topology do not change. Its
  fiber maps are linear, yielding the required local finite-rank witness
  without retyping the total space or choosing a replacement topology. -/
  classical
  -- Change only the model coordinate, using the same finite basis in both directions.
  let g : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv
  constructor
  intro x
  let e := trivializationAt F V x
  refine ⟨Module.finrank ℝ F, e.transFiberHomeomorph g.toHomeomorph,
    mem_baseSet_trivializationAt F V x, ?_⟩
  intro y hy
  -- The original linear fiber chart followed by g is again linear.
  exact (g.toLinearMap.comp (e.linearEquivAt ℝ y hy).toLinearMap).isLinear

end AtiyahSinger.RealBundle
