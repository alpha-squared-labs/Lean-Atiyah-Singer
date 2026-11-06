/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OrthogonalSphere
public import AtiyahSinger.Topology.PrincipalBundle

/-!
# Smooth orthogonal principal transition atlases

Public module ID: M1407.

A smooth principal atlas consists of actual right-equivariant trivializations
of the original projection and smooth transition functions on their base
overlaps. Here the structure group is mathlib's matrix orthogonal group.
Smoothness of a transition is expressed by its actual matrix entries, without
choosing a Lie-group atlas on that group or assuming a smooth associated
total space.

The chart convention is `e(p*g) = (projection p, gamma(p)*g)`. Accordingly,
the transition from chart i to chart j is the original group coordinate of
`e_j(e_i.symm(b,1))`. Its action on an associated fiber is a left action.
The selected charts cover the base and retain the original total topology,
projection and right action. Forgetting smoothness gives the existing
`IsPrincipalBundle` certificate by an explicit construction.

Sources: SG Appendix A, pp.370--372, and II.3; HU IV.7 local triviality and
transition functions. The entrywise matrix presentation describes the standard
smooth orthogonal transition condition, not a new associated-sphere axiom.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Matrix.Norms.Elementwise

variable (r : ℕ)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {P B : Type*} [TopologicalSpace P] [TopologicalSpace B] [ChartedSpace H B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  (projection : P → B)

/-- A standard smooth principal atlas given by original charts and smooth matrix transitions. -/
structure SmoothOrthogonalPrincipalAtlas where
  /-- The specified right action preserves the original projection. -/
  projection_smul : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) (p : P),
    projection (MulOpposite.op A • p) = projection p
  /-- A native principal trivialization selected above each base point. -/
  trivialization : B → Trivialization (Matrix.orthogonalGroup (Fin r) ℝ) projection
  /-- These original chart domains cover the base. -/
  mem_baseSet : ∀ b : B, b ∈ (trivialization b).baseSet
  /-- The selected chart uses right multiplication in its group coordinate. -/
  equivariant : ∀ (b : B) (A : Matrix.orthogonalGroup (Fin r) ℝ) (p : P),
    projection p ∈ (trivialization b).baseSet →
      (trivialization b (MulOpposite.op A • p)).2 = (trivialization b p).2 * A
  /-- The actual transition from the first chart to the second is smooth on their overlap. -/
  contMDiffOn_transition : ∀ b₀ b₁ : B,
    ContMDiffOn I 𝓘(ℝ, Fin r → Fin r → ℝ) ∞
      (fun (b : B) (i j : Fin r) ↦
        ((trivialization b₁)
          ((trivialization b₀).toOpenPartialHomeomorph.symm (b, 1))).2.val i j)
      ((trivialization b₀).baseSet ∩ (trivialization b₁).baseSet)

namespace SmoothOrthogonalPrincipalAtlas

variable {r I projection}

set_option linter.defProp false in
/-- Forget smooth transitions while retaining the same original principal charts and action. -/
@[reducible]
def toIsPrincipalBundle (S : SmoothOrthogonalPrincipalAtlas r I projection) :
    IsPrincipalBundle (Matrix.orthogonalGroup (Fin r) ℝ) projection where
  projection_smul := S.projection_smul
  exists_trivialization b := ⟨S.trivialization b, S.mem_baseSet b, S.equivariant b⟩

end SmoothOrthogonalPrincipalAtlas

end AtiyahSinger
