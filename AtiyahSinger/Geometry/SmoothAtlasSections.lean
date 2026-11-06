/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothComplexBundleAtlas

/-!
# Smooth sections of a locally finite-rank complex bundle

Public module ID: M1367.

D01: the usual space of smooth sections is an actual submodule of the
original dependent function space. Its carrier uses the specified smooth
atlas, with no new fibers, topology or global rank choice. The closure
certificate is an implementation obligation for this standard object,
not an additional mathematical DAG node. Smooth sections are continuous
in the same total-space topology used by the topological bundle theory.

Sources: Spin Geometry III.1, p.167, for the space of smooth sections;
Hatcher, Vector Bundles and K-Theory, section 2.1, p.39, for the convention
allowing different ranks on different components. The coordinate closure
and continuity arguments below are explicit elementary supplements.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

namespace SmoothComplexBundleAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] (A : SmoothComplexBundleAtlas (n := n) E)

/-- The grouped closure certificate used to construct the standard space of smooth sections.
The three clauses are implementation fields, rather than independent mathematical nodes. -/
theorem isSmoothSection_closure :
    A.IsSmoothSection 0 ∧
      (∀ s t : ∀ x : M, E x,
        A.IsSmoothSection s → A.IsSmoothSection t → A.IsSmoothSection (s + t)) ∧
      (∀ (c : ℂ) (s : ∀ x : M, E x),
        A.IsSmoothSection s → A.IsSmoothSection (c • s)) := by
  /- First fix one atlas chart. Its complex linearity identifies the coordinates
  of zero, a sum and a constant scalar multiple with the corresponding coordinate
  operations. These identifications are needed only on the chart base set.
  Next use the constant, addition and scalar multiplication rules for real smooth
  maps into the finite coordinate space. The argument applies separately in each
  chart, so it requires neither a global rank nor agreement of disjoint ranks. -/
  constructor
  · intro i
    apply (contMDiffOn_const (c := (0 : Fin (A.rank i) → ℂ))).congr
    intro x hx
    exact (A.linear i x hx).map_zero
  constructor
  · intro s t hs ht i
    apply ((hs i).add (ht i)).congr
    intro x hx
    exact (A.linear i x hx).map_add (s x) (t x)
  · intro c s hs i
    -- A fixed complex scalar defines a real continuous linear coordinate map.
    have hscale := ((c • ContinuousLinearMap.id ℂ (Fin (A.rank i) → ℂ)).restrictScalars
      ℝ).contMDiff (n := ∞)
    apply (hscale.comp_contMDiffOn (hs i)).congr
    intro x hx
    exact (A.linear i x hx).map_smul c (s x)

/-- The complex vector space of smooth sections of the original locally finite-rank bundle. -/
def smoothSections : Submodule ℂ (∀ x : M, E x) where
  carrier := {s | A.IsSmoothSection s}
  zero_mem' := A.isSmoothSection_closure.1
  add_mem' := fun hs ht ↦ A.isSmoothSection_closure.2.1 _ _ hs ht
  smul_mem' := fun c _ hs ↦ A.isSmoothSection_closure.2.2 c _ hs

/-- Smooth sections are continuous as maps into the original total space. -/
theorem continuous_section (s : ∀ x : M, E x) (hs : A.IsSmoothSection s) :
    Continuous (fun x : M ↦ (⟨x, s x⟩ : TotalSpace Unit E)) := by
  /- At any base point choose a covering chart. The coordinates of s are smooth
  and hence continuous on its open base set. Pair them with the identity base map
  and apply the inverse of this very trivialization, obtaining the original total
  section on that neighborhood. Continuity is local on the covering open sets.
  This uses the given total-space topology, not a newly imposed section topology. -/
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨i, hx⟩ := A.covers x
  -- On this open chart, the section coordinates and the base coordinate are continuous.
  have hcoords := (hs i).continuousOn.continuousAt ((A.chart i).open_baseSet.mem_nhds hx)
  apply (A.chart i).continuousAt_of_comp_left
    (f := fun y ↦ (⟨y, s y⟩ : TotalSpace Unit E)) continuousAt_id hx
  apply (continuousAt_id.prodMk hcoords).congr_of_eventuallyEq
  filter_upwards [(A.chart i).open_baseSet.mem_nhds hx] with y hy
  exact Prod.ext ((A.chart i).proj_toFun ⟨y, s y⟩
    ((A.chart i).mem_source.mpr hy)) rfl

end SmoothComplexBundleAtlas

end AtiyahSinger
