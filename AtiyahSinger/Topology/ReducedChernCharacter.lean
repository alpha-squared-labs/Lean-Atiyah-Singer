/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ChernCharacterKZero
public import AtiyahSinger.Topology.CompactSupportKZero
public import AtiyahSinger.Topology.PointRelativeCohomology

/-!
# The actual reduced Chern character with values in point-relative cohomology

Public module ID: M2050.

Restrict the existing absolute Chern-character component to
the actual reduced K group. Naturality at the specified base point places
its value in the original reduced cohomology kernel. The inverse of the
specified point-relative comparison then gives its unique relative class.

Sources: SG III.11 Corollary 11.17 for the absolute Chern character, and
the standard reduced theory obtained from the split point inclusion;
Hatcher, Algebraic Topology, Section 3.1. This is an explicit supplementary
bridge between the project's existing models, not a new characteristic
map chosen from arbitrary lifts. The K kernel uses evaluation into ℂ,
whereas cohomology uses the actual map from PUnit; the compatibility
certificate below retains this distinction and its ring factorization.

Compact Hausdorff X is the scope of the existing absolute character.
This module does not identify reduced cohomology of X⁺ with H_c(X),
and does not assert any unsupported comparison for general compact pairs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Naturality at the same point sends the original reduced K kernel to reduced cohomology. -/
theorem chernCharacterKZeroComponent_mem_reduced (x₀ : X) (k : ℕ)
    (a : reducedComplexKZero x₀) :
    chernCharacterKZeroComponent X k a.val ∈
      reducedSingularCohomology ℚ x₀ (2 * k) := by
  /- Stage 1: precomposition with the actual map PUnit → X, constant at x₀,
  factors as evaluation C(X,ℂ) → ℂ followed by the constant-function ring
  map ℂ → C(PUnit,ℂ). Functoriality of kZeroMap therefore sends a.val to
  zero in ComplexKZero PUnit, since a.property is precisely vanishing
  under the first ring-induced map. No rank surrogate for that kernel is
  used, and the point can lie in any connected component of X.
  Stage 2: apply chernCharacterKZeroComponent_pullback to this actual point
  map. The character of its zero K class is zero by additivity, so the
  ordinary character of a.val restricts to zero on PUnit. This is exactly
  membership in reducedSingularCohomology, including component k = 0. -/
  let f : C(PUnit.{u + 1}, X) := ContinuousMap.const _ x₀
  let ev := (ContinuousMap.evalAlgHom ℂ ℂ x₀).toRingHom
  let c : ℂ →+* C(PUnit.{u + 1}, ℂ) := ContinuousMap.C
  -- Precomposition with the point map is the actual evaluation followed by constants.
  have hfactor : (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom = c.comp ev := by
    ext b x
    rfl
  have ha : complexKZeroPullback f a.val = 0 := by
    change kZeroMap (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom a.val = 0
    rw [hfactor, kZeroMap_comp, AddMonoidHom.comp_apply]
    have heval : kZeroMap ev a.val = 0 := a.property
    rw [heval, map_zero]
  -- The original character's naturality now gives vanishing in the precise reduced kernel.
  change singularCohomologyPullback ℚ f (2 * k)
    (chernCharacterKZeroComponent X k a.val) = 0
  rw [← chernCharacterKZeroComponent_pullback f a.val k, ha, map_zero]

/-- The reduced character is the unique point-relative lift through the specified comparison. -/
def reducedChernCharacterComponent (x₀ : X) (k : ℕ) :
    reducedComplexKZero x₀ →+
      relativeSingularCohomology ℚ ({x₀} : Set X) (2 * k) := by
  -- Restrict the original absolute component to its actual point-evaluation kernel.
  let reduced : reducedComplexKZero x₀ →+ reducedSingularCohomology ℚ x₀ (2 * k) :=
    { toFun := fun a ↦ ⟨chernCharacterKZeroComponent X k a.val,
        chernCharacterKZeroComponent_mem_reduced x₀ k a⟩
      map_zero' := Subtype.ext (map_zero (chernCharacterKZeroComponent X k))
      map_add' := fun a b ↦ Subtype.ext (map_add (chernCharacterKZeroComponent X k) a.val b.val) }
  -- Invert only the proven canonical comparison, so the relative lift is determined.
  exact (pointRelativeCohomologyEquivReduced ℚ x₀ (2 * k)).symm.toLinearMap.toAddMonoidHom.comp
    reduced

/-- Forgetting the point-relative condition recovers the same absolute Chern character. -/
theorem reducedChernCharacterComponent_toOrdinary (x₀ : X) (k : ℕ)
    (a : reducedComplexKZero x₀) :
    relativeSingularCohomologyToOrdinary ℚ ({x₀} : Set X) (2 * k)
        (reducedChernCharacterComponent x₀ k a) =
      chernCharacterKZeroComponent X k a.val := by
  /- Apply the forward point-relative equivalence to its inverse used in
  reducedChernCharacterComponent. Its underlying ordinary value is by
  construction the original relative-to-ordinary map, and the kernel
  element on the other side has the displayed absolute character as its
  value. No independent choice of a relative representative is involved. -/
  -- Apply the forward equivalence to the chosen inverse, then take its ordinary value.
  have h := (pointRelativeCohomologyEquivReduced ℚ x₀ (2 * k)).apply_symm_apply
    ⟨chernCharacterKZeroComponent X k a.val,
      chernCharacterKZeroComponent_mem_reduced x₀ k a⟩
  exact congrArg Subtype.val h

end AtiyahSinger
