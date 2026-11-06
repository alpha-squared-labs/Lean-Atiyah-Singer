/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexBundle
public import AtiyahSinger.Topology.EquivariantVectorBundle
public import AtiyahSinger.Topology.ModelBundleTopology
public import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Smoothness of an original equivariant complex bundle

Public module ID: M1390.

SG III.9, printed p.211, requires jointly smooth actions on the base and on
the original complex bundle, with complex-linear maps on moving fibers.
The definition below requires the jointly smooth base action and records the
fiber condition through all original local matrix columns. Its parameter is
the given group manifold model, and its domain is the actual moving overlap
of the two specified bundle frames. The base condition remains present at rank zero.

The original continuous equivariant structure is retained. Its `Unit`-tagged
total-space topology is fixed by `ComplexBundle.modelTopology` from the same
modeled total space; no independent topology or replacement bundle is supplied.
Joint smoothness is not replaced by smoothness separately for each group element.
This generic interface does not construct a Lie atlas for the orthogonal group.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- Joint smoothness of the original bundle action over the specified smooth base action. -/
def EquivariantStructure.IsSmooth
    [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E) : Prop :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  ∀ (e f : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f], ∀ j : Fin r,
      ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
        (fun p : G × M ↦
          (f ⟨p.1 • p.2,
            σ.linearMap p.1 p.2 (e.symmL ℂ p.2 (EuclideanSpace.single j 1))⟩).2)
        {p : G × M | p.2 ∈ e.baseSet ∧ p.1 • p.2 ∈ f.baseSet}

end AtiyahSinger.ComplexBundle
