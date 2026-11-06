/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianFlagBundle
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthonormal representatives of the original Hermitian flags

Public module ID: M1268.

Each original ordered projection flag admits an orthonormal basis of its same
ranges. Its projectors are the actual rank-one inner-product operators in
that basis. This supplies reference frames for the local smooth flag charts;
no global phase choice or continuous frame selection is asserted.

Source: the orthogonal flag description in Spin Geometry III.11.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open scoped BigOperators

/-- A projection flag has an orthonormal basis of the same ordered lines. -/
theorem HermitianFlagSpace.exists_orthonormalBasis {r : ℕ}
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (hr : Module.finrank ℂ V = r)
    (P : HermitianFlagSpace r V InnerProductSpace.toCore) :
    ∃ b : OrthonormalBasis (Fin r) ℂ V,
      ∀ (i : Fin r) (v : V), P.val i v = inner ℂ (b i) v • b i := by
  classical
  -- Choose one unit vector in each original rank-one range.
  have hunit (i : Fin r) :
      ∃ v : LinearMap.range (P.val i).toLinearMap, ‖v‖ = 1 := by
    let : Nontrivial (LinearMap.range (P.val i).toLinearMap) :=
      Module.nontrivial_of_finrank_pos (by rw [P.property.2.1 i]; exact Nat.zero_lt_one)
    exact exists_norm_eq (LinearMap.range (P.val i).toLinearMap) (by norm_num : (0 : ℝ) ≤ 1)
  choose u hu using hunit
  let v (i : Fin r) : V := (u i).val
  have hfixed (i : Fin r) : P.val i (v i) = v i := by
    obtain ⟨w, hw⟩ := (u i).property
    change P.val i ((u i).val) = _
    change P.val i ((u i).val) = (u i).val
    rw [← hw]
    exact congrArg (fun L : V →L[ℂ] V ↦ L w) (P.property.1 i)
  have hnorm (i : Fin r) : ‖v i‖ = 1 := hu i
  have hzero (i j : Fin r) (hij : i ≠ j) : P.val i (v j) = 0 := by
    rw [← hfixed j]
    exact congrArg (fun L : V →L[ℂ] V ↦ L (v j)) (P.property.2.2.1 i j hij)
  -- Self-adjointness and orthogonality of the projectors give the same inner products.
  have hon : Orthonormal ℂ v := by
    refine ⟨hnorm, ?_⟩
    intro i j hij
    calc
      inner ℂ (v i) (v j) = inner ℂ (P.val i (v i)) (v j) := by rw [hfixed]
      _ = inner ℂ (v i) (P.val i (v j)) := P.property.2.2.2.2 i _ _
      _ = 0 := by rw [hzero i j hij, inner_zero_right]
  let b : OrthonormalBasis (Fin r) ℂ V :=
    OrthonormalBasis.mk hon
      (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by simpa using hr.symm)).ge
  refine ⟨b, ?_⟩
  intro i w
  -- Read the rank-one coefficient using its unit vector and the original self-adjoint map.
  have hui : u i ≠ 0 := by
    intro h
    have := hu i
    rw [h, norm_zero] at this
    norm_num at this
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (P.property.2.1 i) hui
    (⟨P.val i w, LinearMap.mem_range_self _ w⟩ : LinearMap.range (P.val i).toLinearMap)
  have hval : c • v i = P.val i w := congrArg Subtype.val hc
  have hin : inner ℂ (v i) (P.val i w) = inner ℂ (v i) w := by
    rw [← P.property.2.2.2.2 i, hfixed]
  have hcoeff : inner ℂ (v i) w = c := by
    rw [← hin, ← hval, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm]
    simp
  simp only [b, OrthonormalBasis.coe_mk]
  rw [hcoeff]
  exact hval.symm

end AtiyahSinger.ComplexBundle
