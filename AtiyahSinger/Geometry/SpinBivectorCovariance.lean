/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.EuclideanSpin

/-!
# Covariance of the Clifford contraction under the original spin action

Public module ID: M1444.

The orthonormal contraction of an endomorphism with Clifford multiplication is
independent of the orthonormal basis. Conjugating it by an original Spin element
therefore conjugates the vector endomorphism by its same vector representation.
For a skew endomorphism, one quarter of this contraction is the spin bivector.

Source: the orthogonal covariance of the spin Lie algebra inclusion,
Spin Geometry I.2 and II.4. No change of Clifford sign convention is made.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators

/-- The original spin action intertwines the orthonormal Clifford contraction. -/
theorem euclideanSpin_conjugate_bivector (r : ℕ)
    (g : spinGroup (euclideanSpinQuadraticForm r))
    (A : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin r)) :
    let b := EuclideanSpace.basisFun (Fin r) ℝ
    let j := CliffordAlgebra.ι (euclideanSpinQuadraticForm r)
    let G := euclideanSpinVectorRepresentation r g
    g.val * (∑ i : Fin r, j (b i) * j (A (b i))) *
        (g⁻¹ : spinGroup (euclideanSpinQuadraticForm r)).val =
      ∑ i : Fin r, j (b i) * j (G (A (G.symm (b i)))) := by
  classical
  dsimp only
  let V := EuclideanSpace ℝ (Fin r)
  let Q := euclideanSpinQuadraticForm r
  let C := CliffordAlgebra Q
  let b := EuclideanSpace.basisFun (Fin r) ℝ
  let j := CliffordAlgebra.ι Q
  let G := euclideanSpinVectorRepresentation r g
  let L : V ≃ₗᵢ[ℝ] V :=
    { toLinearEquiv := G
      norm_map' := fun v ↦ (euclideanSpinVectorRepresentation_properties r g v).2.1 }
  let b' := b.map L
  -- Any bilinear contraction has the same diagonal sum in two real orthonormal bases.
  have htrace (T : V →ₗ[ℝ] V →ₗ[ℝ] C) :
      (∑ i : Fin r, T (b' i) (b' i)) = ∑ i : Fin r, T (b i) (b i) := by
    have hexpand (v : V) : (∑ i : Fin r, inner ℝ v (b' i) • b' i) = v := by
      simpa only [real_inner_comm v] using b'.sum_repr' v
    calc
      (∑ i : Fin r, T (b' i) (b' i)) =
          ∑ i : Fin r, ∑ k : Fin r, inner ℝ (b k) (b' i) • T (b k) (b' i) := by
        apply Finset.sum_congr rfl
        intro i _
        nth_rw 1 [← b.sum_repr' (b' i)]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      _ = ∑ k : Fin r, ∑ i : Fin r, inner ℝ (b k) (b' i) • T (b k) (b' i) :=
        Finset.sum_comm
      _ = ∑ k : Fin r, T (b k) (b k) := by
        apply Finset.sum_congr rfl
        intro k _
        simp_rw [← map_smul]
        rw [← map_sum, hexpand]
  let A' : V →ₗ[ℝ] V := G.toLinearMap.comp (A.comp G.symm.toLinearMap)
  let T : V →ₗ[ℝ] V →ₗ[ℝ] C :=
    (LinearMap.mul ℝ C).compl₁₂ j (j.comp A')
  have hconjugate (v : V) : g.val * j v * (g⁻¹ : spinGroup Q).val = j (G v) :=
    (euclideanSpinVectorRepresentation_properties r g v).1.symm
  have hinverse : (g⁻¹ : spinGroup Q).val * g.val = 1 :=
    spinGroup.star_mul_self_of_mem g.property
  -- Each term transforms using the original conjugation of both generating vectors.
  have hterm (i : Fin r) :
      g.val * (j (b i) * j (A (b i))) * (g⁻¹ : spinGroup Q).val =
        T (b' i) (b' i) := by
    change _ = j (G (b i)) * j (G (A (G.symm (G (b i)))))
    rw [G.symm_apply_apply, ← hconjugate, ← hconjugate]
    simp only [mul_assoc]
    rw [← mul_assoc (g⁻¹ : spinGroup Q).val g.val, hinverse, one_mul]
  calc
    _ = ∑ i : Fin r, g.val * (j (b i) * j (A (b i))) *
        (g⁻¹ : spinGroup Q).val := by rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : Fin r, T (b' i) (b' i) := Finset.sum_congr rfl (fun i _ ↦ hterm i)
    _ = ∑ i : Fin r, T (b i) (b i) := htrace T
    _ = _ := rfl

end AtiyahSinger
