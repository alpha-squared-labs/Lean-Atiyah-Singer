/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianFlagLocalFrames
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Matrix coordinates of the local Hermitian flag lift

Public module ID: M1267.

The reference orthonormal basis identifies normalized projection columns
with unitary matrices having positive real diagonal. The reverse map uses
the actual rank-one operators of these columns. These formulas connect the
Gram slice with the original projection-flag subtype.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ComplexConjugate ContDiff Matrix.Norms.Elementwise

variable {r : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

local notation "Mat" r:arg => Matrix (Fin r) (Fin r) ℂ
local notation "Ops" r:arg => Fin r → V →L[ℂ] V

/-- The normalized projected frame, in the same reference basis. -/
def hermitianFlagFrameMatrix (b : OrthonormalBasis (Fin r) ℂ V) (Q : Ops r) : Mat r :=
  fun k i ↦ b.repr (hermitianFlagLocalFrame b Q i) k

/-- Matrix columns regarded as vectors in the specified reference frame. -/
def hermitianFlagMatrixVectors (b : OrthonormalBasis (Fin r) ℂ V) (A : Mat r) : Fin r → V :=
  fun i ↦ b.repr.symm (WithLp.toLp 2 (fun k ↦ A k i))

/-- The rank-one operators of the actual matrix columns. -/
def hermitianFlagMatrixProjections (b : OrthonormalBasis (Fin r) ℂ V) (A : Mat r) : Ops r :=
  fun i ↦ InnerProductSpace.rankOne ℂ
    (hermitianFlagMatrixVectors b A i) (hermitianFlagMatrixVectors b A i)

omit [FiniteDimensional ℂ V] in
/-- The actual local lift satisfies the Gram equations and recovers the original projectors. -/
theorem hermitianFlagFrameMatrix_properties (b : OrthonormalBasis (Fin r) ℂ V)
    (Q : HermitianFlagSpace r V InnerProductSpace.toCore)
    (hQ : ∀ i : Fin r, Q.val i (b i) ≠ 0) :
    (∀ i j : Fin r, (∑ k : Fin r,
      conj (hermitianFlagFrameMatrix b Q.val k i) * hermitianFlagFrameMatrix b Q.val k j) =
        if i = j then 1 else 0) ∧
      (∀ i : Fin r, (hermitianFlagFrameMatrix b Q.val i i).im = 0) ∧
      (∀ i : Fin r, 0 < (hermitianFlagFrameMatrix b Q.val i i).re) ∧
      hermitianFlagMatrixProjections b (hermitianFlagFrameMatrix b Q.val) = Q.val := by
  classical
  obtain ⟨hon, hrec, hdiag⟩ := hermitianFlagLocalFrame_properties b Q hQ
  have hrep (i : Fin r) : hermitianFlagFrameMatrix b Q.val i i = (‖Q.val i (b i)‖ : ℂ) := by
    exact (b.repr_apply_apply _ _).trans (hdiag i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    calc
      _ = inner ℂ (b.repr (hermitianFlagLocalFrame b Q.val i))
          (b.repr (hermitianFlagLocalFrame b Q.val j)) := by
        rw [PiLp.inner_apply]
        simp only [hermitianFlagFrameMatrix, RCLike.inner_apply, mul_comm]
      _ = inner ℂ (hermitianFlagLocalFrame b Q.val i)
          (hermitianFlagLocalFrame b Q.val j) := b.repr.inner_map_map _ _
      _ = _ := orthonormal_iff_ite.mp hon i j
  · intro i
    rw [hrep]
    rfl
  · intro i
    rw [hrep]
    exact norm_pos_iff.mpr (hQ i)
  · funext i
    apply ContinuousLinearMap.ext
    intro v
    simpa [hermitianFlagMatrixProjections, hermitianFlagMatrixVectors,
      hermitianFlagFrameMatrix] using (hrec i v).symm

/-- A unitary matrix with positive real diagonal gives a flag with precisely that local lift. -/
theorem hermitianFlagMatrixProjections_flag (b : OrthonormalBasis (Fin r) ℂ V)
    (A : Mat r)
    (hgram : ∀ i j : Fin r, (∑ k : Fin r, conj (A k i) * A k j) =
      if i = j then 1 else 0)
    (him : ∀ i : Fin r, (A i i).im = 0) (hpos : ∀ i : Fin r, 0 < (A i i).re) :
    ∃ Q : HermitianFlagSpace r V InnerProductSpace.toCore,
      Q.val = hermitianFlagMatrixProjections b A ∧
        (∀ i : Fin r, Q.val i (b i) ≠ 0) ∧ hermitianFlagFrameMatrix b Q.val = A := by
  classical
  let v := hermitianFlagMatrixVectors b A
  have hon : Orthonormal ℂ v := by
    apply orthonormal_iff_ite.mpr
    intro i j
    rw [← b.repr.inner_map_map]
    simpa [v, hermitianFlagMatrixVectors, PiLp.inner_apply, mul_comm]
      using hgram i j
  let c : OrthonormalBasis (Fin r) ℂ V := OrthonormalBasis.mk hon
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank'
      (Module.finrank_eq_card_basis b.toBasis).symm).ge
  let Q := orthonormalBasisFlag c
  have hval : Q.val = hermitianFlagMatrixProjections b A := by
    funext i
    change InnerProductSpace.rankOne ℂ (c i) (c i) = _
    simp only [c, OrthonormalBasis.coe_mk]
    rfl
  have hcoeff (i : Fin r) : inner ℂ (v i) (b i) = ((A i i).re : ℂ) := by
    have he : inner ℂ (b i) (v i) = A i i := by
      rw [← b.repr_apply_apply]
      simp [v, hermitianFlagMatrixVectors]
    rw [← inner_conj_symm, he]
    apply Complex.ext <;> simp [him]
  have happ (i : Fin r) : Q.val i (b i) = (A i i).re • v i := by
    rw [hval]
    change inner ℂ (v i) (b i) • v i = _
    rw [hcoeff, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hn (i : Fin r) : ‖Q.val i (b i)‖ = (A i i).re := by
    rw [happ, norm_smul, hon.1 i, mul_one, Real.norm_eq_abs, abs_of_pos (hpos i)]
  refine ⟨Q, hval, ?_, ?_⟩
  · intro i
    exact norm_pos_iff.mp (by rw [hn]; exact hpos i)
  · funext k i
    change b.repr (‖Q.val i (b i)‖⁻¹ • Q.val i (b i)) k = _
    rw [hn, happ, smul_smul, inv_mul_cancel₀ (ne_of_gt (hpos i)), one_smul]
    simp [v, hermitianFlagMatrixVectors]

/-- The local phase lift is smooth on its actual ambient nonzero-column domain. -/
theorem hermitianFlagFrameMatrix_contDiffAt (b : OrthonormalBasis (Fin r) ℂ V)
    (Q : Ops r) (hQ : ∀ i : Fin r, Q i (b i) ≠ 0) :
    ContDiffAt ℝ ∞ (hermitianFlagFrameMatrix b) Q := by
  apply contDiffAt_pi.mpr
  intro k
  apply contDiffAt_pi.mpr
  intro i
  let ev : Ops r →L[ℝ] V := LinearMap.toContinuousLinearMap
    { toFun := fun P ↦ P i (b i)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hv : ContDiffAt ℝ ∞ (fun P : Ops r ↦ P i (b i)) Q := ev.contDiff.contDiffAt
  have hw := ((hv.norm ℂ (hQ i)).inv (norm_ne_zero_iff.mpr (hQ i))).smul hv
  simp only [hermitianFlagFrameMatrix, b.repr_apply_apply]
  exact contDiffAt_const.inner ℂ hw

/-- The projection tuple is polynomial in the real and imaginary matrix entries. -/
theorem hermitianFlagMatrixProjections_contDiff (b : OrthonormalBasis (Fin r) ℂ V) :
    ContDiff ℝ ∞ (hermitianFlagMatrixProjections b) := by
  classical
  let e : (V →L[ℂ] V) ≃L[ℝ] Mat r :=
    ((LinearMap.toContinuousLinearMap.symm.trans
      (LinearMap.toMatrix b.toBasis b.toBasis)).restrictScalars ℝ).toContinuousLinearEquiv
  apply contDiff_pi.mpr
  intro i
  apply e.comp_contDiff_iff.mp
  have he (A : Mat r) : e (hermitianFlagMatrixProjections b A i) =
      fun k j ↦ A k i * conj (A j i) := by
    simp [e, hermitianFlagMatrixProjections, InnerProductSpace.toMatrix_rankOne,
      Matrix.vecMulVec, hermitianFlagMatrixVectors]
    rfl
  have hc : ContDiff ℝ ∞ (fun A : Mat r ↦ fun k j ↦ A k i * conj (A j i)) := by
    have hconj : ContDiff ℝ ∞ (starRingEnd ℂ) := Complex.conjCLE.contDiff
    fun_prop
  convert! hc using 1
  funext A
  exact he A

end AtiyahSinger.ComplexBundle
