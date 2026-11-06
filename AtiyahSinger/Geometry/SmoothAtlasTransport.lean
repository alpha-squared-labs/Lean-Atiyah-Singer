/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothComplexBundleAtlas
public import AtiyahSinger.Topology.BundleIso

/-!
# Transport of a smooth atlas through a continuous bundle isomorphism

Public module ID: M1370.

The actual total-space homeomorphism pulls a smooth atlas back to the original
bundle. Its forward and inverse maps cancel on overlaps, so every transition
column is precisely the corresponding column of the supplied atlas. This is
the standard transport used in continuous-to-smooth bundle realization; it
does not assert smoothness for arbitrary original continuous frames.
On a compact base, `finiteSubatlas` separately selects finitely many of the
original charts and reindexes them by a small finite type.
-/

@[expose] public noncomputable section

universe v

namespace AtiyahSinger.ComplexBundle.Iso

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- Pull the specified smooth atlas back through the original bundle isomorphism. -/
def smoothAtlas (e : Iso E F) (A : SmoothComplexBundleAtlas.{v} (n := n) F) :
    SmoothComplexBundleAtlas.{v} (n := n) E where
  Index := A.Index
  rank := A.rank
  chart i := (A.chart i).compHomeomorph e.totalHomeomorph
  covers := A.covers
  linear := by
    intro i x hx
    constructor
    · intro u w
      change (A.chart i ⟨x, e.linearEquiv x (u + w)⟩).2 = _
      rw [map_add]
      exact (A.linear i x hx).map_add _ _
    · intro c u
      change (A.chart i ⟨x, e.linearEquiv x (c • u)⟩).2 = _
      rw [map_smul]
      exact (A.linear i x hx).map_smul c _
  contMDiffOn_coordChange := by
    intro i j a
    -- The same homeomorphism and its inverse cancel before taking either chart coordinate.
    apply (A.contMDiffOn_coordChange i j a).congr
    intro x _
    change (A.chart j (e.totalHomeomorph
      (e.totalHomeomorph.symm ((A.chart i).toPartialEquiv.symm (x, Pi.single a 1))))).2 = _
    rw [Homeomorph.apply_symm_apply]

end AtiyahSinger.ComplexBundle.Iso

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- A finite subatlas uses only original charts and has a small finite index type. -/
def finiteSubatlas (A : SmoothComplexBundleAtlas.{v} (n := n) E) :
    SmoothComplexBundleAtlas.{0} (n := n) E := by
  classical
  -- Compactness selects finitely many original chart domains covering the same base.
  have hcover : Set.univ ⊆ ⋃ i, (A.chart i).baseSet := by
    intro x _
    exact Set.mem_iUnion.mpr (A.covers x)
  let h := isCompact_univ.elim_finite_subcover
    (fun i ↦ (A.chart i).baseSet) (fun i ↦ (A.chart i).open_baseSet) hcover
  let s := h.choose
  have hs := h.choose_spec
  let e : Fin s.card ≃ s := s.equivFin.symm
  exact
    { Index := Fin s.card
      rank := fun j ↦ A.rank (e j)
      chart := fun j ↦ A.chart (e j)
      covers := by
        intro x
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
        refine ⟨e.symm ⟨i, hi⟩, ?_⟩
        have he := congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)
        change x ∈ (A.chart (e (e.symm ⟨i, hi⟩))).baseSet
        rw [he]
        exact hxi
      linear := fun j ↦ A.linear (e j)
      contMDiffOn_coordChange := fun i j ↦ A.contMDiffOn_coordChange (e i) (e j) }

end AtiyahSinger.SmoothComplexBundleAtlas
