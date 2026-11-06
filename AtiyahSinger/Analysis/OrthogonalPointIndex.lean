/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LowSpherePointIndex
public import AtiyahSinger.Analysis.OrthogonalSphereIndexProduct

/-!
# All-dimensional orthogonal point normalization

Public module ID: M0843.

AR04: ASI I Proposition (4.4), printed p.505. The first theorem retains the
source's arbitrary-index implication on the actual tangent support groups.
Its hypotheses are the binary block restriction/product instance of excision
and independent-group multiplicativity, and the O(1) and SO(2) values from AL03.
Normalization on all block subgroups is derived, not assumed. The actual
analytic specializations then use the original index and positive pole maps.

Zero dimension is derived from the product with the normalized one-dimensional
factor. Both poles are retained. The coefficient formula states the full
R(O(r))-linear point normalization, not just its integer dimension. No Euler
class is cancelled, and no final index theorem is used. The analytic
specializations apply the same binary product and low-dimensional inputs,
then retain every representation coefficient by the original module action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphereTangent

set_option maxSynthPendingDepth 30

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The source's all-dimensional normalization for arbitrary index maps on the original classes. -/
theorem orthogonalSphere_point_index_eq_one_of_axioms
    (J : (r : ℕ) →
      EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
          (TangentBundle (𝓡 r) (OrthogonalSphere r)) →+
        RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ))
    (hProduct : ∀ (p q : ℕ) (b : Bool),
      representationRestrictionRingHom (orthogonalDirectSumInclusion p q)
          (J (p + q) (orthogonalSpherePolePushforward (p + q) b 1)) =
        representationExternalProduct
          (J p (orthogonalSpherePolePushforward p b 1))
          (J q (orthogonalSpherePolePushforward q b 1)))
    (hLine : ∀ b : Bool, J 1 (orthogonalSpherePolePushforward 1 b 1) = 1)
    (hPlane : ∀ b : Bool,
      representationRestrictionRingHom (specialOrthogonalGroupInclusion 2)
        (J 2 (orthogonalSpherePolePushforward 2 b 1)) = 1)
    (r : ℕ) (atInfinity : Bool) :
    J r (orthogonalSpherePolePushforward r atInfinity 1) = 1 := by
  /- Stage 1: fix this pole and write x_r for J_r of its positive point
  class. Evaluate hProduct at each pair of matrices to obtain the binary
  character product. The line and plane assumptions give character value one
  on O(1) and SO(2). Applying the binary product at p=0, q=1 then gives
  character value one on O(0), without a zero-dimensional unit premise.
  Stage 2: induct over the ordered blocks O(1)^a times SO(2)^b. The actual
  matrix equalities orthogonalBlockInclusion_line_succ and
  orthogonalBlockInclusion_plane_succ, with their dimension casts, reduce
  each block character to the already normalized factors. Both empty block
  families are included; only the SO(2) restriction of x_2 is needed.
  Stage 3: every real orthogonal matrix is conjugate to one of these blocks.
  Conjugation invariance makes the original character identically one, and
  compact character injectivity gives x_r=1. For the analytic specialization,
  common-open excision and independent-group multiplicativity supply hProduct.
  No inverse of K restriction or arbitrary-class lift enters the argument. -/
  let x (k : ℕ) := J k (orthogonalSpherePolePushforward k atInfinity 1)
  -- Evaluate the actual binary restriction at each pair of original matrices.
  have hcharProduct (p q : ℕ) (g : Matrix.orthogonalGroup (Fin p) ℝ)
      (h : Matrix.orthogonalGroup (Fin q) ℝ) :
      representationCharacter _ (x (p + q)) (orthogonalDirectSumInclusion p q (g, h)) =
        representationCharacter _ (x p) g * representationCharacter _ (x q) h := by
    have hfst : ContinuousMonoidHom.fst
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ) (g, h) = g := rfl
    have hsnd : ContinuousMonoidHom.snd
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ) (g, h) = h := rfl
    have heq := congrArg (fun z ↦ representationCharacter _ z (g, h))
      (hProduct p q atInfinity)
    simpa only [x, representationExternalProduct, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      map_mul, Pi.mul_apply, representationCharacter_restrict,
      hfst, hsnd] using heq
  have hLineChar (g : Matrix.orthogonalGroup (Fin 1) ℝ) :
      representationCharacter _ (x 1) g = 1 := by
    change representationCharacter _ (J 1 _) g = 1
    rw [hLine, map_one]
    rfl
  have hPlaneChar (g : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
      representationCharacter _ (x 2) (specialOrthogonalGroupInclusion 2 g) = 1 := by
    have h := congrArg (fun z ↦ representationCharacter _ z g) (hPlane atInfinity)
    simpa only [representationCharacter_restrict, map_one, Pi.one_apply] using h
  have hZeroChar (g : Matrix.orthogonalGroup (Fin 0) ℝ) :
      representationCharacter _ (x 0) g = 1 := by
    have h := hcharProduct 0 1 g 1
    rw [hLineChar, hLineChar, mul_one] at h
    exact h.symm
  -- Dimension casts retain the given matrix, including both empty block families.
  have hcast (s t : ℕ) (h : s = t)
      (u : Matrix.orthogonalGroup (Fin s) ℝ) (v : Matrix.orthogonalGroup (Fin t) ℝ)
      (hv : v.val = u.val.submatrix (Fin.cast h.symm) (Fin.cast h.symm)) :
      representationCharacter _ (x t) v = representationCharacter _ (x s) u := by
    subst t
    have huv : v = u := by
      apply Subtype.ext
      simpa only [Fin.cast_refl, Matrix.submatrix_id_id] using hv
    rw [huv]
  have hblock (a b : ℕ)
      (g : (Fin a → Matrix.orthogonalGroup (Fin 1) ℝ) ×
        (Fin b → Matrix.specialOrthogonalGroup (Fin 2) ℝ)) :
      representationCharacter _ (x (a + b * 2)) (orthogonalBlockInclusion a b g) = 1 := by
    induction a with
    | zero =>
      induction b with
      | zero => exact hZeroChar _
      | succ b ih =>
        rw [hcast _ _ (by omega) _ _ (orthogonalBlockInclusion_plane_succ 0 b g),
          hcharProduct, ih, hPlaneChar, one_mul]
    | succ a ih =>
      rw [hcast _ _ (by omega) _ _ (orthogonalBlockInclusion_line_succ a b g),
        hcharProduct, hLineChar, ih, one_mul]
  -- Every original orthogonal matrix is conjugate to one of these exact blocks.
  let : CompactSpace (Matrix.orthogonalGroup (Fin r) ℝ) := compactSpace_orthogonalGroup r
  apply representationCharacter_injective
  funext A
  obtain ⟨a, b, hDim, g, Q, hA⟩ := exists_orthogonalBlock_conjugate r A
  let B : Matrix.orthogonalGroup (Fin r) ℝ := hDim ▸ orthogonalBlockInclusion a b g
  have hB : B.val = (orthogonalBlockInclusion a b g).val.submatrix
      (Fin.cast hDim.symm) (Fin.cast hDim.symm) := by
    subst r
    rfl
  have hconj : A = Q * B * Q⁻¹ := by
    apply Subtype.ext
    change A.val = Q.val * B.val * (Q⁻¹).val
    rw [hB]
    exact hA
  rw [hconj, representationCharacter_conj]
  simpa only [map_one, Pi.one_apply] using
    (hcast _ _ hDim _ B hB).trans (hblock a b g)

/-- The original O(r)-equivariant analytic index of either positive pole class is one. -/
theorem orthogonalSpherePoleIndex_eq_one (r : ℕ) (atInfinity : Bool) :
    orthogonalSphereTangentAnalyticIndex r
      (orthogonalSpherePolePushforward r atInfinity 1) = 1 := by
  /- Instantiate the preceding generic theorem with the original tangent
  analytic index in every dimension. orthogonalSpherePoleIndex_directSum
  supplies the binary identity from the actual common-open excision and
  compact-product analytic index, using the same inverse round musical map.
  orthogonalCirclePoleIndex_eq_one supplies the O(1) input; the original
  specialOrthogonalPlanePoleIndex_eq_one supplies precisely the SO(2)
  restriction of the O(2) input. All three statements concern the same
  original Bott/open-extension classes. The generic argument consequently
  applies to either pole and includes r=0 without a separate unit premise. -/
  -- Use precisely the same family of original indices and both proved low-dimensional values.
  exact orthogonalSphere_point_index_eq_one_of_axioms
    orthogonalSphereTangentAnalyticIndex orthogonalSpherePoleIndex_directSum
    orthogonalCirclePoleIndex_eq_one specialOrthogonalPlanePoleIndex_eq_one r atInfinity

/-- Every representation coefficient is recovered by the original positive point pushforward. -/
theorem orthogonalSphereTangentAnalyticIndex_polePushforward
    (r : ℕ) (atInfinity : Bool)
    (a : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ)) :
    orthogonalSphereTangentAnalyticIndex r
      (orthogonalSpherePolePushforward r atInfinity a) = a := by
  /- The original pole pushforward is an R(O(r))-linear map from the
  representation ring itself, hence its value at a is a times its value
  at one. Apply the established module linearity of the same tangent
  analytic index and the preceding unit normalization. This gives the
  coefficient a in the original representation ring, not merely its
  dimension or its character at the identity. This is the full point
  normalization used by subsequent equivariant embedding arguments. -/
  -- The original linear point map is determined on every coefficient by its value at one.
  have hpush : orthogonalSpherePolePushforward r atInfinity a =
      a • orthogonalSpherePolePushforward r atInfinity 1 := by
    have h := (orthogonalSpherePolePushforward r atInfinity).map_smul a
      (1 : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ))
    simpa only [smul_eq_mul, mul_one] using h
  -- Apply representation-linearity to that same class before using unit normalization.
  rw [hpush, orthogonalSphereTangentAnalyticIndex_smul, orthogonalSpherePoleIndex_eq_one]
  exact mul_one a

end AtiyahSinger
