/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantRankStrata
public import AtiyahSinger.Topology.HermitianFixedRankModel
public import AtiyahSinger.Topology.HermitianMetricPullback

/-!
# The full flag bundle on the original locally constant rank pieces

Public module ID: M2270.

C01. Restrict the original fibers and metric to their actual rank strata and
apply the existing Hermitian flag construction on each piece. The global flag
space is their topological disjoint union. Its projection returns the original
base point, without requiring connectedness or a global bound on the ranks.
Rank zero retains a singleton flag over each original zero-dimensional fiber.

The native model is only the identity-on-vectors adapter of
HermitianFixedRankModel. The resulting flags are the same original projection
tuples, not flags of an unrelated replacement bundle. The rank strata are
clopen because actual fiber dimension is locally constant. This is the usual
componentwise extension of SG III.11.1 and Hatcher VBKT Proposition 3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u v

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E)

attribute [local instance] isFiniteRank_restrict

/-- Restrict the original Hermitian form to the actual rank-r subspace. -/
def rankHermitianMetric (r : ℕ) :
    ContinuousHermitianMetric (Restrict E (rankStratum E r)) :=
  h.pullback ⟨Subtype.val, continuous_subtype_val⟩

/-- The existing fixed-rank flag, on precisely the original fibers in the rank-r stratum. -/
def RankFlagBundle (r : ℕ) : Type (max u v) :=
  let F := Restrict E (rankStratum E r)
  let hF := rankHermitianMetric E h r
  letI : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  letI := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
  HermitianFlagBundle r F (hF.nativeModelMetric r)

/-- Each rank piece retains the original fixed-rank flag topology. -/
@[reducible]
def rankFlagTopology (r : ℕ) : TopologicalSpace (RankFlagBundle E h r) :=
  let F := Restrict E (rankStratum E r)
  let hF := rankHermitianMetric E h r
  letI : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  letI := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
  letI := hF.nativeFiberBundle r (fun x ↦ x.property)
  letI := hF.nativeVectorBundle r (fun x ↦ x.property)
  hermitianFlagTopology r F (hF.nativeModelMetric r)

attribute [local instance] rankFlagTopology

/-- The original native flag projection on the actual rank-r subspace. -/
def rankFlagProjection (r : ℕ) : C(RankFlagBundle E h r, rankStratum E r) :=
  let F := Restrict E (rankStratum E r)
  let hF := rankHermitianMetric E h r
  letI : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  letI := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
  letI := hF.nativeFiberBundle r (fun x ↦ x.property)
  letI := hF.nativeVectorBundle r (fun x ↦ x.property)
  hermitianFlagProjection r F (hF.nativeModelMetric r)

/-- The global flag space is the disjoint union over the original locally constant ranks. -/
def VariableRankFlagBundle : Type (max u v) :=
  (r : ℕ) × RankFlagBundle E h r

/-- The topological sum of the original rank-piece flag topologies. -/
@[reducible]
def variableRankFlagTopology : TopologicalSpace (VariableRankFlagBundle E h) :=
  inferInstanceAs (TopologicalSpace ((r : ℕ) × RankFlagBundle E h r))

attribute [local instance] variableRankFlagTopology

/-- Include an original rank-piece flag without changing its base, projections or range lines. -/
def rankFlagInclusion (r : ℕ) : C(RankFlagBundle E h r, VariableRankFlagBundle E h) where
  toFun := fun p ↦ ⟨r, p⟩
  continuous_toFun := continuous_sigmaMk

/-- The actual global flag projection, with the rank-stratum inclusion on each piece. -/
def variableRankFlagProjection : C(VariableRankFlagBundle E h, X) where
  toFun := fun p ↦ (rankFlagProjection E h p.1 p.2).val
  continuous_toFun := continuous_sigma fun r ↦
    continuous_subtype_val.comp (rankFlagProjection E h r).continuous

/-- Each original rank stratum is also closed, so the componentwise construction is clopen. -/
theorem isClosed_rankStratum (r : ℕ) : IsClosed (rankStratum E r : Set X) := by
  /- Actual fiber rank is locally constant on the original base. Its fiber
  at r is closed because its complement is the union of the other open rank
  fibers. This uses neither compactness nor a finite number of rank values. -/
  exact (isLocallyConstant_finrank E).isClosed_fiber r

end AtiyahSinger.ComplexBundle
