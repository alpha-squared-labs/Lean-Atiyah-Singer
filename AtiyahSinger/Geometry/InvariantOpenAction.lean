/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# The original action on an invariant open submanifold

Public module ID: M1285.

This implementation adapter equips a specified invariant open subset with
the restriction of the ambient action. Continuity and smoothness use the
inherited open-submanifold charts, and the underlying point is unchanged.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open TopologicalSpace
open scoped Manifold ContDiff

variable {G M : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace M] [MulAction G M]

/-- The specified ambient action restricted to the given invariant open subset. -/
@[reducible]
def invariantOpenMulAction (U : Opens M)
    (hU : ∀ (g : G) (x : M), g • x ∈ U ↔ x ∈ U) : MulAction G U where
  smul g x := ⟨g • x.val, (hU g x.val).mpr x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

/-- Restricting the original continuous action preserves its continuity. -/
theorem continuousSMul_invariantOpen [ContinuousSMul G M] (U : Opens M)
    (hU : ∀ (g : G) (x : M), g • x ∈ U ↔ x ∈ U) :
    letI := invariantOpenMulAction U hU
    ContinuousSMul G U := by
  let := invariantOpenMulAction U hU
  exact ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

variable {VG HG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG) [ChartedSpace HG G]
  {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The inherited charts preserve smoothness of the same restricted action. -/
theorem contMDiffSMul_invariantOpen
    [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
    (U : Opens M) (hU : ∀ (g : G) (x : M), g • x ∈ U ↔ x ∈ U) :
    letI := invariantOpenMulAction U hU
    ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G U := by
  let := invariantOpenMulAction U hU
  refine ⟨?_⟩
  apply (ContMDiff.subtypeVal_comp_iff U (fun p : G × U ↦ p.1 • p.2)).mp
  change ContMDiff (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun p : G × U ↦ p.1 • p.2.val)
  exact contMDiff_fst.smul ((contMDiff_subtype_val (U := U)).comp contMDiff_snd)

end AtiyahSinger
