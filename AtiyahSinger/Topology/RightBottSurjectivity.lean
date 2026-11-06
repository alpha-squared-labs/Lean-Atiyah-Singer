/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BottSurjectivity
public import AtiyahSinger.Topology.RightBottLoop

/-!
# Surjectivity of the right-projective Bott loop map

Public module ID: M2108.

Laurent approximation, polynomial shifts, affine reduction and the Wiener
contraction give surjectivity for the
actual map defined in RightBottLoop. All matrices remain over the original
possibly noncommutative unital complex Banach algebra. The affine projector
is exactly p=1-a0*b0 for the same specified bilateral inverse b.

The one-sided factors yield a normalized contraction.
Right normalization leaves the positive loop z*p+(1-p); neither a
conjugate projector nor the complementary projector is substituted. No
inverse to the Bott map, geometric periodicity, or index theorem is used.

Sources: Karoubi, K-Theory, III.1.21--1.25, pp.120--122. Completeness is
needed for Wiener inversion and approximation here; it was unnecessary
for the definition of the Bott map itself.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RightKTheory

universe u

open scoped Matrix.Norms.Operator

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

local instance matrixCompleteSpace (n : ℕ) :
    CompleteSpace (Matrix (Fin n) (Fin n) A) :=
  inferInstanceAs (CompleteSpace (Fin n → Fin n → A))

/-- The right-projective presentation of the original affine Wiener projector 1-a0*b0. -/
def affineBottIdempotentMatrix {n : ℕ} (a₀ a₁ : Matrix (Fin n) (Fin n) A)
    (hbase : a₀ + a₁ = 1) (b : WienerLoop (Matrix (Fin n) (Fin n) A))
    (hleft : WienerLoop.affine a₀ a₁ * b = 1)
    (hright : b * WienerLoop.affine a₀ a₁ = 1) : IdempotentMatrix A where
  size := n
  matrix := WienerLoop.affineBottIdempotent a₀ b
  mul_self := WienerLoop.affineBottIdempotent_isIdempotentElem a₀ a₁ hbase b hleft hright

/-- The original normalized affine contraction gives the Bott loop of this exact right projector. -/
theorem affine_stableClass_eq_bott {n : ℕ} (a₀ a₁ : Matrix (Fin n) (Fin n) A)
    (hbase : a₀ + a₁ = 1)
    (hunit : ∀ z : Circle, IsUnit (a₀ + (z : ℂ) • a₁))
    (b : WienerLoop (Matrix (Fin n) (Fin n) A))
    (hleft : WienerLoop.affine a₀ a₁ * b = 1)
    (hright : b * WienerLoop.affine a₀ a₁ = 1) :
    (LaurentMatrixLoop.affine a₀ a₁ hbase hunit).stableClass =
      bottMatrixLoopClass (affineBottIdempotentMatrix a₀ a₁ hbase b hleft hright) := by
  let B := Matrix (Fin n) (Fin n) A
  let P : B := WienerLoop.affineBottIdempotent a₀ b
  let p := affineBottIdempotentMatrix a₀ a₁ hbase b hleft hright
  let q := LaurentMatrixLoop.affine a₀ a₁ hbase hunit
  let H := WienerLoop.affineBottHomotopy a₀ a₁ hbase b hleft hright
  -- Identify the two given affine evaluations, retaining their exact projector and parameter.
  have heval (x y : B) (z : Circle) : (WienerLoop.affine x y).eval z =
      x + (z : ℂ) • y := by
    classical
    change (∑' k : ℤ, (z : ℂ) ^ k •
      ((lp.single 1 0 x + lp.single 1 1 y : WienerLoop B) k)) = _
    simp only [lp.coeFn_add, lp.coeFn_single, Pi.add_apply]
    rw [tsum_eq_sum (s := ({0, 1} : Finset ℤ))]
    · simp [Pi.single_apply]
    · intro k hk
      have hk' : k ≠ 0 ∧ k ≠ 1 := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
      simp [hk'.1, hk'.2]
  let value (st : unitInterval × unitInterval) : B :=
    H (st.1, Circle.exp (2 * Real.pi * (st.2 : ℝ)))
  have hvalue : Continuous value := H.continuous.comp
    (continuous_fst.prodMk (by fun_prop))
  have hvalueUnit (st : unitInterval × unitInterval) : IsUnit (value st) :=
    (H.prop' st.1).2 _
  -- Lift the very same normalized family to units, including its continuous inverse.
  have hcontinuous : Continuous (fun st ↦ (hvalueUnit st).unit) := by
    apply Units.continuous_iff.mpr
    constructor
    · simp only [Function.comp_def, IsUnit.unit_spec]
      exact hvalue
    · simp only [← Ring.inverse_unit, IsUnit.unit_spec]
      apply continuous_iff_continuousAt.mpr
      intro st
      have hi := NormedRing.inverse_continuousAt (hvalueUnit st).unit
      simp only [IsUnit.unit_spec] at hi
      exact hi.comp hvalue.continuousAt
  have hpath : (bottMatrixPath p).Homotopic q.toFiniteMatrixLoop.loop := by
    refine ⟨{ toFun := fun st ↦ (hvalueUnit st).unit
              continuous_toFun := hcontinuous
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro t
      apply Units.ext
      simp only [IsUnit.unit_spec]
      change H (0, Circle.exp (2 * Real.pi * (t : ℝ))) =
        (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ) • P + (1 - P)
      refine (H.map_zero_left _).trans ?_
      change (WienerLoop.affine (1 - P) P).eval _ = _
      rw [heval, add_comm]
    · intro t
      apply Units.ext
      simp only [IsUnit.unit_spec]
      change H (1, Circle.exp (2 * Real.pi * (t : ℝ))) =
        laurentPolynomialCircleValue
          (LaurentPolynomial.C a₀ + LaurentPolynomial.C a₁ * LaurentPolynomial.T 1) _
      refine (H.map_one_left _).trans ?_
      change (WienerLoop.affine a₀ a₁).eval _ =
        laurentPolynomialCircleValue
          (LaurentPolynomial.C a₀ + LaurentPolynomial.C a₁ * LaurentPolynomial.T 1) _
      rw [heval]
      rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C]
      simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_add,
        AddMonoidAlgebra.coeff_single]
      simp [Finsupp.sum_add_index, smul_add]
    · intro s t ht
      rcases ht with ht | ht
      · subst t
        erw [(bottMatrixPath p).source]
        apply Units.ext
        change H (s, Circle.exp (2 * Real.pi * (0 : ℝ))) = 1
        simp only [mul_zero, Circle.exp_zero]
        exact (H.prop' s).1
      · have ht' : t = 1 := ht
        subst t
        erw [(bottMatrixPath p).target]
        apply Units.ext
        change H (s, Circle.exp (2 * Real.pi * (1 : ℝ))) = 1
        simp only [mul_one, Circle.exp_two_pi]
        exact (H.prop' s).1
  -- Append empty identity blocks only to express this unstabilized based homotopy.
  have hzero (r : FiniteMatrixLoop A) : (r.stabilize 0).loop = r.loop := by
    apply Path.ext
    funext t
    apply Units.ext
    ext i j
    change (matrixUnitBlockSum (r.loop t) (1 : (Matrix (Fin 0) (Fin 0) A)ˣ) :
      Matrix (Fin (r.size + 0)) (Fin (r.size + 0)) A) i j =
      (r.loop t : Matrix (Fin r.size) (Fin r.size) A) i j
    refine Fin.addCases (fun i ↦ ?_) (fun i : Fin 0 ↦ Fin.elim0 i) i
    refine Fin.addCases (fun j ↦ ?_) (fun j : Fin 0 ↦ Fin.elim0 j) j
    change Matrix.fromBlocks (r.loop t : Matrix (Fin r.size) (Fin r.size) A)
      (0 : Matrix (Fin r.size) (Fin 0) A) 0 1
        (finSumFinEquiv.symm (Fin.castAdd 0 i))
        (finSumFinEquiv.symm (Fin.castAdd 0 j)) = _
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  apply Eq.symm
  apply (stableMatrixLoopClass_eq_iff _ _).mpr
  refine ⟨0, 0, rfl, ?_⟩
  change Path.Homotopic ((bottMatrixLoop p).stabilize 0).loop
    (q.toFiniteMatrixLoop.stabilize 0).loop
  rw [hzero, hzero]
  exact hpath

/-- KA III.1.25: the specified right-projective Bott homomorphism is surjective. -/
theorem kZeroBottLoop_surjective : Function.Surjective (kZeroBottLoop A) := by
  /- Stage 1: use the existing continuous/Laurent stable comparison to
  choose an actual Laurent representative. The original polynomial
  difference lemma writes its class as the difference of two positive
  polynomial-loop classes, retaining the prescribed scalar shifts.
  Stage 2: apply the existing stable affine reduction to each polynomial.
  Finite-support Wiener inversion supplies a single bilateral inverse
  for each resulting affine loop, with both ordered inverse equations.
  The preceding same-projector comparison identifies its stable class
  with the Bott loop of exactly 1-a0*b0 in the right-projective model.
  Stage 3: subtract the two original idempotent K-zero classes. The
  generator formula and additivity of kZeroBottLoop send this virtual
  right-projective class to the required stable loop class. This constructs
  a preimage without assuming a cokernel inverse or Bott injectivity.
  Zero matrix size and the zero coefficient ring remain admissible. -/
  classical
  -- Each polynomial class is the Bott image of its actual affine Wiener projector.
  have polynomial_preimage (p : LaurentMatrixLoop A) (hp : p.IsPolynomial) :
      ∃ x : KZero A, kZeroBottLoop A x = p.stableClass := by
    obtain ⟨n, a₀, a₁, hbase, hunit, hclass⟩ := p.exists_affine_representative hp
    let f : WienerLoop (Matrix (Fin n) (Fin n) A) := WienerLoop.affine a₀ a₁
    have hfinite : (Function.support (fun k : ℤ ↦ f k)).Finite := by
      refine ((Set.finite_singleton (0 : ℤ)).union (Set.finite_singleton 1)).subset ?_
      intro k hk
      by_cases hk0 : k = 0
      · exact Or.inl hk0
      by_cases hk1 : k = 1
      · exact Or.inr hk1
      exact False.elim (hk (by
        change (lp.single 1 0 a₀ : WienerLoop _) k +
          (lp.single 1 1 a₁ : WienerLoop _) k = 0
        have hzero : (lp.single 1 0 a₀ : WienerLoop _) k = 0 :=
          lp.single_apply_ne (E := fun _ : ℤ ↦ Matrix (Fin n) (Fin n) A) 1 0 a₀ hk0
        have hone : (lp.single 1 1 a₁ : WienerLoop _) k = 0 :=
          lp.single_apply_ne (E := fun _ : ℤ ↦ Matrix (Fin n) (Fin n) A) 1 1 a₁ hk1
        exact (congrArg₂ (· + ·) hzero hone).trans (zero_add 0)))
    have heval (z : Circle) : f.eval z = a₀ + (z : ℂ) • a₁ := by
      change (∑' k : ℤ, (z : ℂ) ^ k •
        ((lp.single 1 0 a₀ + lp.single 1 1 a₁ : WienerLoop _) k)) = _
      simp only [lp.coeFn_add, lp.coeFn_single, Pi.add_apply]
      rw [tsum_eq_sum (s := ({0, 1} : Finset ℤ))]
      · simp [Pi.single_apply]
      · intro k hk
        have hk' : k ≠ 0 ∧ k ≠ 1 := by
          simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
        simp [hk'.1, hk'.2]
    have hfunit : IsUnit f := WienerLoop.isUnit_of_finiteSupport f hfinite (by
      intro z
      rw [heval]
      exact hunit z)
    -- Use one unit witness for both ordered inverse equations and the exact projector.
    let b : WienerLoop (Matrix (Fin n) (Fin n) A) := ↑(hfunit.unit⁻¹)
    have hleft : WienerLoop.affine a₀ a₁ * b = 1 := by
      change f * ↑(hfunit.unit⁻¹) = 1
      simpa only [IsUnit.unit_spec] using (Units.mul_inv hfunit.unit)
    have hright : b * WienerLoop.affine a₀ a₁ = 1 := by
      change ↑(hfunit.unit⁻¹) * f = 1
      simpa only [IsUnit.unit_spec] using (Units.inv_mul hfunit.unit)
    let q := affineBottIdempotentMatrix a₀ a₁ hbase b hleft hright
    refine ⟨kZeroClass A q, ?_⟩
    rw [kZeroBottLoop_class]
    exact (affine_stableClass_eq_bott a₀ a₁ hbase hunit b hleft hright).symm.trans
      hclass.symm
  -- Preserve the actual Laurent representative and the two prescribed scalar shifts.
  intro x
  obtain ⟨v, rfl⟩ := Quotient.exists_rep x
  obtain ⟨p, hp⟩ := v.exists_laurent_representative
  obtain ⟨k, hk, hmonomial, hdifference⟩ := p.exists_polynomial_difference
  obtain ⟨y, hy⟩ := polynomial_preimage (p.shift (k : ℤ)) hk
  obtain ⟨z, hz⟩ := polynomial_preimage (LaurentMatrixLoop.monomial p.size (k : ℤ))
    hmonomial
  -- Subtract the two genuine finite-projective classes using the original homomorphism.
  refine ⟨y - z, ?_⟩
  rw [map_sub, hy, hz, ← hdifference]
  exact hp

end AtiyahSinger.RightKTheory
