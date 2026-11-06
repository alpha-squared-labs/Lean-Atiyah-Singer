/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SmoothFiniteRepresentation
public import AtiyahSinger.Geometry.EquivariantBundleMapApproximation
public import AtiyahSinger.Geometry.EquivariantFixedRankModel
public import AtiyahSinger.Geometry.EquivariantSmoothImageModel
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Topology.EquivariantBundleEmbedding

/-!
# Smooth realization of an original constant-rank equivariant bundle

Public module ID: M1177.

A continuous complex equivariant bundle of one fixed rank over a compact
smooth manifold is continuously equivariantly isomorphic to a smooth bundle
with a jointly smooth action of the original compact finite-dimensional Lie
group. The result retains the given base action, the original continuous
bundle topology and its original action through an actual equivariant `Iso`.
The target carries a newly chosen compatible smooth atlas. It does not assert
that arbitrary original continuous frames are already smooth.

The fixed-rank hypothesis is explicit because `SmoothFiniteComplexBundle`
has one global model rank. Neither connectedness nor positive rank is needed.
This result does not assemble bundles of varying local ranks, smooth an
arbitrary continuous nonlinear action, or realize an equivariant K-symbol.

SG Appendix A, Remark A.1, printed pp.372--373, gives ordinary smooth bundle
classification, and SG III.9 gives compact-group averaging. Their equivariant
combination here is a standard supplementary theorem, not the literal claim
of Remark A.1. The finite representation complement is supplied by Karoubi
I.9.31(d),(g). The equivariant smoothing argument is a project supplement
to these cited results.
The proof uses a finite invariant image, smooth conjugation averaging and
the analytic idempotent correction, retaining the specified group action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff Matrix

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [hLie : LieGroup 𝓘(ℝ, VG) ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]

attribute [local instance] trivialTopology

include hDim hLie hGC hGT hM hT hSC hC hAction hE

set_option linter.unusedSectionVars false in

/-- An original constant-rank equivariant bundle admits a smooth equivariantly isomorphic model. -/
theorem EquivariantStructure.exists_smooth_bundle_iso
    (σ : EquivariantStructure G E) (r : ℕ)
    (hRank : ∀ x : M, Module.finrank ℂ (E x) = r) :
    ∃ F : SmoothFiniteComplexBundle (n := n) M, F.rank = r ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∃ τ : EquivariantStructure G F.Fiber,
        τ.IsSmooth (n := n) (r := F.rank) 𝓘(ℝ, VG) ∧
          ∃ e : Iso E F.Fiber, e.IsEquivariant σ τ := by
  classical
  obtain ⟨p, hp⟩ := σ.exists_smooth_image_model (VG := VG) (n := n)
  let := IdempotentMatrix.fiberTotalSpaceTopology p
  obtain ⟨τ, e, he, B, hB⟩ := hp
  have hpRank (x : M) : Module.finrank ℂ (p.fiber x) = r :=
    (e.linearEquiv x).finrank_eq.symm.trans (hRank x)
  -- The common smooth image already carries the exact equivariant action.
  -- Constant rank permits its native model, retaining the same fiber maps.
  obtain ⟨F, hF, hmodel⟩ :=
    B.exists_equivariant_smooth_model_of_rank 𝓘(ℝ, VG) τ r hpRank hB
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  obtain ⟨υ, hυ, f, hf⟩ := hmodel
  refine ⟨F, hF, υ, hυ, e.trans f, ?_⟩
  intro g x v
  exact (congrArg (f.linearEquiv (g • x)) (he g x v)).trans (hf g x (e.linearEquiv x v))

end AtiyahSinger.ComplexBundle
