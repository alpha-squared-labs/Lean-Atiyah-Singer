/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorTopology
public import AtiyahSinger.Algebra.SpinorWeights
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Trace

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Characters of the specified half-spin representations

Public module ID: M0063.

The character is the ordinary complex trace of the existing representation on
the original exterior parity subspace. The normalized-volume comparison in
SpinorChirality identifies these spaces with positive and negative chirality.
No independently chosen representation or formal character replaces that trace.

The coordinate rotation parameters are spin angles: the vector representation
rotates each real two-plane by twice that angle. With the interleaved complex
orientation, the unoccupied exterior factor has weight exp(-i theta) and the
occupied factor has weight exp(i theta). Thus positive minus negative character
is the product of exp(-i theta) minus exp(i theta), in that order.

Sources: Lawson--Michelsohn, Spin Geometry I.6, equations (6.14)--(6.15),
printed pp.43--44; III.11.23, printed p.238. These are representation-level
formulas. Substituting cohomology classes and identifying a Chern character
require the later characteristic-class construction and splitting argument.
All formulas include m=0: the positive trace is one and the negative trace zero.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The character of the existing positive or negative half-spin representation. -/
def complexHalfSpinCharacter (m : ℕ) (i : ZMod 2)
    (g : spinGroup (realSpinorQuadraticForm m)) : ℂ :=
  LinearMap.trace ℂ
    (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i)
    (complexSpinParityRepresentation m i g).toLinearMap

/-- The actual half-spin trace is the sum of its exterior-basis weights. -/
theorem complexHalfSpinCharacter_spinTorusElement_sum (m : ℕ) (i : ZMod 2)
    (theta : Fin m → ℝ) :
    complexHalfSpinCharacter m i (spinTorusElement m theta) =
      ∑ s : {s : Finset (Fin m) // (s.card : ZMod 2) = i},
        spinorWeight m s.val theta := by
  /- Stage 1: use the actual complexSpinorParityBasis of the original parity
  submodule. The restricted action scales each basis vector by
  spinorWeight m s.val theta. This is a basis of the same space on
  which complexHalfSpinCharacter takes the trace, without a new representation.
  Stage 2: LinearMap.trace_eq_matrix_trace computes the trace as the sum of
  these diagonal entries. For m=0 the positive basis has the empty subset as
  its single index, and the negative basis is empty. -/
  classical
  -- Compute the trace in the original parity basis of the same representation space.
  rw [complexHalfSpinCharacter,
    LinearMap.trace_eq_matrix_trace ℂ (complexSpinorParityBasis m i)]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change (complexSpinorParityBasis m i).repr
    (complexSpinParityRepresentation m i (spinTorusElement m theta)
      (complexSpinorParityBasis m i s)) s = _
  -- Its diagonal matrix entry is precisely the previously proved spin weight.
  rw [complexSpinParityRepresentation_spinTorusElement_basis]
  simp

/-- The two actual half-spin characters are the parity-selected product formulas. -/
theorem complexHalfSpinCharacter_spinTorusElement (m : ℕ) (i : ZMod 2)
    (theta : Fin m → ℝ) :
    complexHalfSpinCharacter m i (spinTorusElement m theta) =
      (1 / 2 : ℂ) *
        ((∏ j : Fin m, (Complex.exp (-Complex.I * (theta j : ℂ)) +
            Complex.exp (Complex.I * (theta j : ℂ)))) +
          (-1 : ℂ) ^ i.val *
            ∏ j : Fin m, (Complex.exp (-Complex.I * (theta j : ℂ)) -
              Complex.exp (Complex.I * (theta j : ℂ)))) := by
  /- Stage 1: expand each product by choosing an occupied or unoccupied
  factor at each coordinate. Multiplicativity of the complex exponential
  identifies the corresponding term with the specified spinorWeight.
  Stage 2: the sum product has coefficient one for every subset; the
  difference product has coefficient (-1)^card. Adding or subtracting them
  and dividing by two selects the subset parity i. The preceding trace sum
  therefore gives the displayed formula for the actual representation.
  Empty products give one and zero for positive and negative rank-zero spaces. -/
  classical
  -- Occupied and unoccupied coordinate factors multiply to the specified weight.
  let p (j : Fin m) : ℂ := Complex.exp (Complex.I * (theta j : ℂ))
  let q (j : Fin m) : ℂ := Complex.exp (-Complex.I * (theta j : ℂ))
  have hweight (s : Finset (Fin m)) :
      (∏ j ∈ s, p j) * (∏ j ∈ sᶜ, q j) = spinorWeight m s theta := by
    simp only [p, q, ← Complex.exp_sum, ← Complex.exp_add, spinorWeight]
    congr 1
    rw [Finset.mul_sum]
    simp_rw [mul_ite]
    rw [Finset.sum_ite]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_notMem_eq_sdiff,
      ← Finset.compl_eq_univ_sdiff, mul_neg, neg_mul]
  -- Expand both products over the identical finite subsets of the coordinate set.
  have hsum : (∏ j : Fin m, (q j + p j)) =
      ∑ s : Finset (Fin m), spinorWeight m s theta := by
    simp only [add_comm (q _), Fintype.prod_add, hweight]
  have hdiff : (∏ j : Fin m, (q j - p j)) =
      ∑ s : Finset (Fin m), (-1 : ℂ) ^ s.card * spinorWeight m s theta := by
    rw [Finset.prod_sub]
    simp only [Finset.powerset_univ, ← Finset.compl_eq_univ_sdiff]
    apply Finset.sum_congr rfl
    intro s _
    rw [← hweight]
    ring
  -- The scalar parity projector selects exactly one of the two degree classes.
  have hselector (n : ℕ) :
      (1 / 2 : ℂ) * (1 + (-1 : ℂ) ^ i.val * (-1 : ℂ) ^ n) =
        if (n : ZMod 2) = i then 1 else 0 := by
    have hp : (-1 : ℂ) ^ n = (-1 : ℂ) ^ (n : ZMod 2).val := by
      rw [ZMod.val_natCast, neg_one_pow_eq_pow_mod_two]
    rw [hp]
    generalize (n : ZMod 2) = j
    fin_cases i <;> fin_cases j <;> norm_num [ZMod.val]
    · rfl
    · exact one_ne_zero
    · exact zero_ne_one
    · rfl
  -- Apply that projector to the complete weight sum, retaining the actual trace.
  rw [complexHalfSpinCharacter_spinTorusElement_sum]
  change _ = (1 / 2 : ℂ) *
    ((∏ j : Fin m, (q j + p j)) + (-1 : ℂ) ^ i.val * ∏ j : Fin m, (q j - p j))
  rw [hsum, hdiff, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  calc
    _ = ∑ s : Finset (Fin m),
        if (s.card : ZMod 2) = i then spinorWeight m s theta else 0 := by
      symm
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [show (1 / 2 : ℂ) *
          (spinorWeight m s theta + (-1 : ℂ) ^ i.val *
            ((-1 : ℂ) ^ s.card * spinorWeight m s theta)) =
          ((1 / 2 : ℂ) * (1 + (-1 : ℂ) ^ i.val * (-1 : ℂ) ^ s.card)) *
            spinorWeight m s theta by ring, hselector]
      split_ifs <;> simp

/-- The positive-minus-negative spin character has the fixed SG chirality sign. -/
theorem complexHalfSpinCharacter_sub_spinTorusElement (m : ℕ)
    (theta : Fin m → ℝ) :
    complexHalfSpinCharacter m 0 (spinTorusElement m theta) -
        complexHalfSpinCharacter m 1 (spinTorusElement m theta) =
      ∏ j : Fin m, (Complex.exp (-Complex.I * (theta j : ℂ)) -
        Complex.exp (Complex.I * (theta j : ℂ))) := by
  /- Stage 1: apply the two parity character formulas to the same Spin
  element, keeping positive chirality equal to even exterior degree.
  Stage 2: subtract: the sum-product terms cancel, and the difference-product
  terms add. The order of subtraction matches the normalized volume and
  original Bott symbol. The vector angle is 2*theta, so these spin weights
  correspond to half the vector weights in the later Chern-root formula.
  This argument establishes no cohomological substitution or Euler cancellation. -/
  -- Subtract the two traces for this same spin element; the sum-product terms cancel.
  rw [complexHalfSpinCharacter_spinTorusElement,
    complexHalfSpinCharacter_spinTorusElement]
  simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul, neg_one_mul]
  ring

end AtiyahSinger
