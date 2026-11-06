/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinTopology
public import AtiyahSinger.Algebra.SpinZero
public import AtiyahSinger.Topology.PrincipalBundle
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# Smooth principal atlases on the original native spin group

Public module ID: M1414.

S01. The principal charts act on the original total space and original right
Spin action. Their transition functions are smooth in the original finite
real Clifford coordinates. This is the standard smooth transition criterion
for the embedded spin group; it does not use the vector-action topology,
which would identify the two central lifts in positive dimension.

Forgetting smoothness retains precisely the same charts and projection. At
rank zero the native generated spin group is trivial, so its principal charts
have constant transition functions. That endpoint does not assert a twofold
cover of SO(0). Associated full and half-spin atlases are constructed separately
from these original charts, without changing any quotient fibers or topology.

Sources: Lawson--Michelsohn, Spin Geometry I.2 and II.1--3; the smooth principal
transition description is the standard local description of these bundles.
The zero convention is the original native group convention in SpinZero.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup

variable (m : ℕ)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {P B : Type*} [TopologicalSpace P] [TopologicalSpace B] [ChartedSpace H B]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  (projection : P → B)

/-- Original spin principal charts with smooth transitions in real Clifford coordinates. -/
structure SmoothSpinPrincipalAtlas where
  /-- The original right action preserves the specified projection. -/
  projection_smul : ∀ (g : spinGroup (realSpinorQuadraticForm m)) (p : P),
    projection (MulOpposite.op g • p) = projection p
  /-- One original equivariant principal chart above each base point. -/
  trivialization : B → Trivialization (spinGroup (realSpinorQuadraticForm m)) projection
  /-- The selected principal chart domains cover the original base. -/
  mem_baseSet : ∀ b : B, b ∈ (trivialization b).baseSet
  /-- Group coordinates transform by the original right multiplication. -/
  equivariant : ∀ (b : B) (g : spinGroup (realSpinorQuadraticForm m)) (p : P),
    projection p ∈ (trivialization b).baseSet →
      (trivialization b (MulOpposite.op g • p)).2 = (trivialization b p).2 * g
  /-- The actual spin transition, including its central lift, is smooth. -/
  contMDiffOn_transition : ∀ b₀ b₁ : B,
    ContMDiffOn I
      𝓘(ℝ, Finset (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin m)))) → ℝ) ∞
      (fun b : B ↦ realSpinorCliffordCoordinates m
        (((trivialization b₁)
          ((trivialization b₀).toOpenPartialHomeomorph.symm (b, 1))).2.val))
      ((trivialization b₀).baseSet ∩ (trivialization b₁).baseSet)

namespace SmoothSpinPrincipalAtlas

variable {m I projection}

set_option linter.defProp false in
/-- Retain the identical original principal charts while forgetting transition smoothness. -/
@[reducible]
def toIsPrincipalBundle (S : SmoothSpinPrincipalAtlas m I projection) :
    IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection where
  projection_smul := S.projection_smul
  exists_trivialization b := ⟨S.trivialization b, S.mem_baseSet b, S.equivariant b⟩

end SmoothSpinPrincipalAtlas

section Zero

variable {E₀ H₀ P₀ B₀ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀]
  (I₀ : ModelWithCorners ℝ E₀ H₀)
  [TopologicalSpace P₀] [TopologicalSpace B₀] [ChartedSpace H₀ B₀]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P₀]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P₀]
  {projection₀ : P₀ → B₀}

/-- The original trivial native spin group makes every rank-zero principal atlas smooth. -/
theorem exists_smoothSpinPrincipalAtlas_zero
    (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection₀) :
    Nonempty (SmoothSpinPrincipalAtlas 0 I₀ projection₀) := by
  -- Keep exactly the equivariant principal charts supplied on the original total space.
  choose e he hequiv using hP.exists_trivialization
  refine ⟨{
    projection_smul := hP.projection_smul
    trivialization := e
    mem_baseSet := he
    equivariant := hequiv
    contMDiffOn_transition := ?_ }⟩
  intro b₀ b₁
  -- The native zero-dimensional group is a singleton, so its transitions are constant.
  have hconstant : (fun b : B₀ ↦ realSpinorCliffordCoordinates 0
      (((e b₁) ((e b₀).toOpenPartialHomeomorph.symm (b, 1))).2.val)) =
      fun _ ↦ realSpinorCliffordCoordinates 0
        ((1 : spinGroup (realSpinorQuadraticForm 0)) :
          CliffordAlgebra (realSpinorQuadraticForm 0)) := by
    funext b
    exact congrArg (fun g : spinGroup (realSpinorQuadraticForm 0) ↦
      realSpinorCliffordCoordinates 0 g.val) (Subsingleton.elim _ 1)
  rw [hconstant]
  exact contMDiffOn_const

/-- A smooth atlas selected on the same rank-zero native principal bundle. -/
def smoothSpinPrincipalAtlasZero
    (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection₀) :
    SmoothSpinPrincipalAtlas 0 I₀ projection₀ :=
  (exists_smoothSpinPrincipalAtlas_zero I₀ hP).some

end Zero

end AtiyahSinger
