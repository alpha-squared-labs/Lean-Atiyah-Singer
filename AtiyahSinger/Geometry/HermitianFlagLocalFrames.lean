/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianFlagOrthonormalBasis
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Local orthonormal lifts of projection flags

Public module ID: M1265.

Projecting a fixed reference frame and normalizing its nonzero columns fixes
the phases of a nearby flag. These are the actual ordered projection ranges,
and their positive diagonal entries give the inverse of the local unitary
frame slice. No global continuous lift is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

variable {r : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- The original ordered projection flag associated to an orthonormal basis. -/
def orthonormalBasisFlag (b : OrthonormalBasis (Fin r) ℂ V) :
    HermitianFlagSpace r V InnerProductSpace.toCore := by
  classical
  refine ⟨fun i ↦ InnerProductSpace.rankOne ℂ (b i) (b i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact InnerProductSpace.isIdempotentElem_rankOne_self (b.orthonormal.1 i)
  · intro i
    have h := InnerProductSpace.rank_rankOne (𝕜 := ℂ) (b.toBasis.ne_zero i) (b.toBasis.ne_zero i)
    exact Module.rank_eq_one_iff_finrank_eq_one.mp h
  · intro i j hij
    rw [InnerProductSpace.rankOne_comp_rankOne, b.orthonormal.2 hij, zero_smul]
  · exact b.sum_rankOne_eq_id
  · intro i u v
    exact InnerProductSpace.isSymmetric_rankOne_self (b i) u v

/-- The local phase choice obtained by normalizing the actual projected reference vectors. -/
def hermitianFlagLocalFrame (b : Fin r → V) (Q : Fin r → V →L[ℂ] V) (i : Fin r) : V :=
  ‖Q i (b i)‖⁻¹ • Q i (b i)

omit [FiniteDimensional ℂ V] in
/-- The normalized projected reference frame is orthonormal and recovers the same flag.
Its reference diagonal is positive real, fixing the phases required by the local slice. -/
theorem hermitianFlagLocalFrame_properties (b : OrthonormalBasis (Fin r) ℂ V)
    (Q : HermitianFlagSpace r V InnerProductSpace.toCore)
    (hQ : ∀ i : Fin r, Q.val i (b i) ≠ 0) :
    Orthonormal ℂ (hermitianFlagLocalFrame b Q.val) ∧
      (∀ (i : Fin r) (v : V), Q.val i v =
        inner ℂ (hermitianFlagLocalFrame b Q.val i) v • hermitianFlagLocalFrame b Q.val i) ∧
      ∀ i : Fin r, inner ℂ (b i) (hermitianFlagLocalFrame b Q.val i) =
        (‖Q.val i (b i)‖ : ℂ) := by
  classical
  let w := hermitianFlagLocalFrame b Q.val
  have hnorm (i : Fin r) : ‖w i‖ = 1 := by
    exact norm_smul_inv_norm (hQ i)
  have hfixed (i : Fin r) : Q.val i (w i) = w i := by
    have h := congrArg (fun L : V →L[ℂ] V ↦ L (b i)) (Q.property.1 i)
    change Q.val i (‖Q.val i (b i)‖⁻¹ • Q.val i (b i)) = _
    exact (((Q.val i).restrictScalars ℝ).map_smul ‖Q.val i (b i)‖⁻¹
      (Q.val i (b i))).trans (congrArg (fun v : V ↦ ‖Q.val i (b i)‖⁻¹ • v) h)
  have hzero (i j : Fin r) (hij : i ≠ j) : Q.val i (w j) = 0 := by
    have h := congrArg (fun L : V →L[ℂ] V ↦ L (b j)) (Q.property.2.2.1 i j hij)
    change Q.val i (‖Q.val j (b j)‖⁻¹ • Q.val j (b j)) = 0
    have hs := (((Q.val i).restrictScalars ℝ).map_smul ‖Q.val j (b j)‖⁻¹
      (Q.val j (b j))).trans (congrArg (fun v : V ↦ ‖Q.val j (b j)‖⁻¹ • v) h)
    exact hs.trans (smul_zero _)
  -- Orthogonality is inherited from the original self-adjoint projections.
  have hon : Orthonormal ℂ w := by
    refine ⟨hnorm, ?_⟩
    intro i j hij
    rw [← hfixed i, Q.property.2.2.2.2 i, hzero i j hij, inner_zero_right]
  refine ⟨hon, ?_, ?_⟩
  · intro i v
    let wi : LinearMap.range (Q.val i).toLinearMap := ⟨w i, ⟨w i, hfixed i⟩⟩
    have hwi : wi ≠ 0 := by
      intro h
      have hw : w i = 0 := congrArg Subtype.val h
      have hn := hnorm i
      rw [hw, norm_zero] at hn
      norm_num at hn
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (Q.property.2.1 i) hwi
      (⟨Q.val i v, LinearMap.mem_range_self _ v⟩ : LinearMap.range (Q.val i).toLinearMap)
    have hv : c • w i = Q.val i v := congrArg Subtype.val hc
    have hcoeff : inner ℂ (w i) v = c := by
      calc
        inner ℂ (w i) v = inner ℂ (w i) (Q.val i v) := by
          rw [← Q.property.2.2.2.2 i, hfixed]
        _ = c := by rw [← hv, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm]; simp
    rw [hcoeff]
    exact hv.symm
  · intro i
    -- Self-adjoint idempotence makes the reference diagonal the squared norm.
    have hd : inner ℂ (b i) (Q.val i (b i)) = (‖Q.val i (b i)‖ : ℂ) ^ 2 := by
      have h := congrArg (fun L : V →L[ℂ] V ↦ L (b i)) (Q.property.1 i)
      calc
        inner ℂ (b i) (Q.val i (b i)) =
            inner ℂ (Q.val i (b i)) (Q.val i (b i)) := by
          rw [Q.property.2.2.2.2 i]
          exact congrArg (inner ℂ (b i)) h.symm
        _ = _ := inner_self_eq_norm_sq_to_K _
    change inner ℂ (b i) (‖Q.val i (b i)‖⁻¹ • Q.val i (b i)) = _
    rw [inner_smul_right_eq_smul, hd]
    have hn : (‖Q.val i (b i)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hQ i)
    simp only [Complex.real_smul, Complex.ofReal_inv]
    field_simp

end AtiyahSinger.ComplexBundle
