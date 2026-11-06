/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SuspendedKTheory
public import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Order.IsLocallyClosed

/-!
# The actual cylinder used by the K-theory connecting homomorphism

Public module ID: M1915.

Karoubi II.4.9, printed p.85, constructs the boundary map using
Z = X×{0} ∪ A×[0,1), with A closed in a locally compact Hausdorff space X.
This module keeps Z as that literal subspace of X×ℝ. Its two relevant open
pieces are (X\A)×{0} and A×(0,1); neither piece is replaced by an abstract space.
They do not cover Z: the common attaching locus A×{0} is omitted from both.

The tube parameter is fixed by mathlib's increasing order isomorphism
ℝ ≃ (-1,1), followed by u ↦ (u+1)/2. Thus ℝ is identified with (0,1) in the
increasing direction. This choice fixes the boundary sign; it is not a reflection.

For suspended boundaries the new real coordinate is placed FIRST, by vecCons.
The inverse takes the head coordinate and the tail. A convention placing it last
requires an explicit coordinate permutation and its induced sign comparison.
This file only constructs the spaces and coordinate maps: it does not assert
invertibility of extension into Z, define a connecting map, or prove exactness.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X : Type*}

/-- KA II.4.9: the literal half-open cylinder attached along a closed subset. -/
abbrev BoundaryCylinder (A : Set X) : Type _ :=
  {p : X × ℝ // 0 ≤ p.2 ∧ p.2 < 1 ∧ (p.2 = 0 ∨ p.1 ∈ A)}

/-- The base open part of the boundary cylinder is the complement of A at height zero. -/
def boundaryCylinderBaseOpen (A : Set X) : Set (BoundaryCylinder A) :=
  {z | z.val.1 ∉ A}

/-- The tube open part of the boundary cylinder has strictly positive height. -/
def boundaryCylinderTubeOpen (A : Set X) : Set (BoundaryCylinder A) :=
  {z | 0 < z.val.2}

variable [TopologicalSpace X]

/-- The boundary cylinder of a closed subset of a locally compact space is locally compact. -/
theorem locallyCompactSpace_boundaryCylinder [LocallyCompactSpace X]
    (A : Set X) (hA : IsClosed A) : LocallyCompactSpace (BoundaryCylinder A) := by
  /- Stage 1: in X×ℝ the conditions t≥0 and (t=0 or x∈A) define a closed set,
  using the closedness of A and the real zero singleton. The condition t<1 is
  open. Their intersection is the literal defining subset of BoundaryCylinder.
  Stage 2: this subset is locally closed in the locally compact product X×ℝ.
  Apply the standard local-closed-subspace local compactness theorem. Its subtype
  topology is already the one on BoundaryCylinder; no transported or quotient
  topology is selected. Hausdorffness, when needed, is inherited directly from
  the ambient product by mathlib's existing subtype instance. -/
  -- Separate the strict upper bound from the closed attaching conditions.
  have hopen : IsOpen {p : X × ℝ | p.2 < 1} := isOpen_lt continuous_snd continuous_const
  have hclosed : IsClosed {p : X × ℝ | 0 ≤ p.2 ∧ (p.2 = 0 ∨ p.1 ∈ A)} :=
    (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_eq continuous_snd continuous_const).union (hA.preimage continuous_fst))
  have hlocal : IsLocallyClosed
      {p : X × ℝ | 0 ≤ p.2 ∧ p.2 < 1 ∧ (p.2 = 0 ∨ p.1 ∈ A)} := by
    refine ⟨_, _, hopen, hclosed, ?_⟩
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  exact hlocal.locallyCompactSpace

/-- The base piece is open precisely because its projected complement is open. -/
theorem isOpen_boundaryCylinderBaseOpen (A : Set X) (hA : IsClosed A) :
    IsOpen (boundaryCylinderBaseOpen A) := by
  /- This set is the inverse image of the open set Aᶜ under the continuous
  first-coordinate projection of the actual subspace of X×ℝ. Within the cylinder
  the defining disjunction forces its second coordinate to be zero. -/
  exact hA.isOpen_compl.preimage continuous_subtype_val.fst

/-- The positive-height tube is an open subspace of the actual boundary cylinder. -/
theorem isOpen_boundaryCylinderTubeOpen (A : Set X) :
    IsOpen (boundaryCylinderTubeOpen A) := by
  /- This is the inverse image of the open real interval (0,∞) under the
  second-coordinate projection. The cylinder equation forces x∈A at positive
  height; no closedness assumption on A is needed for this open-set assertion. -/
  exact isOpen_lt continuous_const continuous_subtype_val.snd

/-- The base-piece homeomorphism inserts height zero and its inverse retains x. -/
def boundaryCylinderBaseHomeomorph (A : Set X) :
    (Aᶜ : Set X) ≃ₜ boundaryCylinderBaseOpen A where
  toFun x := ⟨⟨(x.val, 0), le_rfl, zero_lt_one, Or.inl rfl⟩, x.property⟩
  invFun z := ⟨z.val.val.1, z.property⟩
  left_inv x := rfl
  right_inv z := by
    -- Outside A the defining cylinder equation forces precisely height zero.
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (z.val.property.2.2.resolve_right z.property).symm
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The tube homeomorphism uses the increasing standard real-to-open-interval parameter. -/
def boundaryCylinderTubeHomeomorph (A : Set X) :
    (A × ℝ) ≃ₜ boundaryCylinderTubeOpen A :=
  let affine := affineHomeomorph (1 / 2 : ℝ) (1 / 2) (by norm_num)
  let interval : Set.Ioo (-1 : ℝ) 1 ≃ₜ Set.Ioo (0 : ℝ) 1 :=
    affine.subtype (by
      intro t
      change (-1 < t ∧ t < 1) ↔ (0 < 1 / 2 * t + 1 / 2 ∧ 1 / 2 * t + 1 / 2 < 1)
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2])
  let parameter := (orderIsoIooNegOneOne ℝ).toHomeomorph.trans interval
  { toFun p :=
      ⟨⟨(p.1.val, (parameter p.2).val),
        (parameter p.2).property.1.le, (parameter p.2).property.2, Or.inr p.1.property⟩,
          (parameter p.2).property.1⟩
    invFun z :=
      (⟨z.val.val.1, z.val.property.2.2.resolve_left (ne_of_gt z.property)⟩,
        parameter.symm ⟨z.val.val.2, z.property, z.val.property.2.1⟩)
    left_inv p := by
      -- The real coordinate is recovered by the same specified parameter inverse.
      apply Prod.ext
      · rfl
      · exact parameter.symm_apply_apply p.2
    right_inv z := by
      -- The original height is recovered; subtype certificates do not alter the point.
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl (congrArg Subtype.val
        (parameter.apply_symm_apply ⟨z.val.val.2, z.property, z.val.property.2.1⟩))
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-- Suspension coordinates place the new real variable first, followed by the old tuple. -/
def suspensionCoordinateHomeomorph (X : Type*) [TopologicalSpace X] (n : ℕ) :
    ((X × ℝ) × (Fin n → ℝ)) ≃ₜ X × (Fin (n + 1) → ℝ) where
  toFun p := (p.1.1, Matrix.vecCons p.1.2 p.2)
  invFun p := ((p.1, p.2 0), Matrix.vecTail p.2)
  left_inv p := by
    -- Head and tail recover the new variable and every old coordinate separately.
    rcases p with ⟨⟨x, t⟩, s⟩
    simp
  right_inv p := by
    exact Prod.ext rfl (Matrix.cons_head_tail p.2)
  continuous_toFun := by fun_prop
  continuous_invFun := by
    change Continuous (fun p : X × (Fin (n + 1) → ℝ) ↦
      ((p.1, p.2 0), fun i : Fin n ↦ p.2 i.succ))
    fun_prop

end AtiyahSinger
