/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BanachUnitLifting
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.TietzeExtension

/-!
# Lifting commuting matrix-unit paths from a closed subspace

Public module ID: M1958.

Restriction of continuous matrices has the path-lifting property for units
commuting with a specified continuous idempotent. The original matrix and
restriction map remain fixed. The standard closed centralizer subalgebra gives
a unital real Banach algebra even when the idempotent is not self-adjoint.

Sources: Karoubi II.2.21--2.24; Tietze extension and the standard block-diagonal
projection onto the centralizer of an idempotent.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Topology
open scoped Matrix Matrix.Norms.Operator unitInterval

/-- A matrix-unit path commuting with an idempotent lifts from a closed subspace,
with its exact specified initial unit and its entire boundary path preserved. -/
theorem exists_unit_path_lift_restrict_commuting
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P)
    (A : Set X) (hA : IsClosed A) :
    let r : Matrix (Fin n) (Fin n) C(X, ℂ) →+*
        Matrix (Fin n) (Fin n) C(A, ℂ) :=
      (ContinuousMap.compRightAlgHom ℂ ℂ
        ⟨(Subtype.val : A → X), continuous_subtype_val⟩).toRingHom.mapMatrix
    ∀ (a : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ), Commute (a : Matrix _ _ _) P →
      ∀ (b : C(I, (Matrix (Fin n) (Fin n) C(A, ℂ))ˣ)),
        (∀ t, Commute (b t : Matrix _ _ _) (r P)) →
        b 0 = Units.map r.toMonoidHom a →
        ∃ c : C(I, (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ), c 0 = a ∧
          (∀ t, Units.map r.toMonoidHom (c t) = b t) ∧
          ∀ t, Commute (c t : Matrix _ _ _) P := by
  classical
  let : CompactSpace A := hA.isClosedEmbedding_subtypeVal.compactSpace
  let : TietzeExtension ℂ := TietzeExtension.of_homeo Complex.equivRealProdCLM.toHomeomorph
  dsimp only
  intro a ha b hb hzero
  let MX := Matrix (Fin n) (Fin n) C(X, ℂ)
  let MA := Matrix (Fin n) (Fin n) C(A, ℂ)
  let r : MX →+* MA :=
    (ContinuousMap.compRightAlgHom ℂ ℂ
      ⟨(Subtype.val : A → X), continuous_subtype_val⟩).toRingHom.mapMatrix
  have hr : Continuous r := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (ContinuousMap.compRightAlgHom_continuous ℂ ℂ
      ⟨(Subtype.val : A → X), continuous_subtype_val⟩).comp
      ((continuous_apply j).comp (continuous_apply i))
  let S := Subalgebra.centralizer ℝ ({P} : Set MX)
  let T := Subalgebra.centralizer ℝ ({r P} : Set MA)
  let : CompleteSpace MX := inferInstanceAs (CompleteSpace (Fin n → Fin n → C(X, ℂ)))
  let : CompleteSpace MA := inferInstanceAs (CompleteSpace (Fin n → Fin n → C(A, ℂ)))
  let : CompleteSpace S := (Set.isClosed_centralizer ({P} : Set MX)).completeSpace_coe
  let : CompleteSpace T := (Set.isClosed_centralizer ({r P} : Set MA)).completeSpace_coe
  have hSmem (z : MX) : z ∈ S ↔ P * z = z * P := by
    simp only [S, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  have hTmem (z : MA) : z ∈ T ↔ r P * z = z * r P := by
    simp only [T, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  let f : S →+* T :=
    { toFun := fun z ↦ ⟨r z.val, hTmem _ |>.mpr (by
        simpa only [map_mul] using congrArg r ((hSmem z.val).mp z.property))⟩
      map_zero' := Subtype.ext r.map_zero
      map_one' := Subtype.ext r.map_one
      map_add' := fun z w ↦ Subtype.ext (r.map_add z.val w.val)
      map_mul' := fun z w ↦ Subtype.ext (r.map_mul z.val w.val) }
  have hf : Continuous f := (hr.comp continuous_subtype_val).subtype_mk _
  -- Extend the whole parameter family by Tietze, then keep exactly its two diagonal blocks.
  have hI : Function.Surjective (f.compLeftContinuous I hf) := by
    intro q
    let qij (i j : Fin n) : C(I × A, ℂ) :=
      ⟨fun z ↦ (q z.1).val i j z.2, by
        have hq : Continuous (fun t ↦ (q t).val) := continuous_subtype_val.comp q.continuous
        have hcoord : Continuous (fun t ↦ (q t).val i j) :=
          (continuous_apply j).comp ((continuous_apply i).comp hq)
        exact (hcoord.comp continuous_fst).eval continuous_snd⟩
    have hemb : IsClosedEmbedding (fun z : I × A ↦ (z.1, z.2.val)) :=
      IsClosedEmbedding.id.prodMap hA.isClosedEmbedding_subtypeVal
    choose g hg using fun i j ↦ (qij i j).exists_extension hemb
    let raw : C(I, MX) :=
      ⟨fun t i j ↦ (g i j).curry t,
        continuous_pi (fun i ↦ continuous_pi (fun j ↦ (g i j).curry.continuous))⟩
    have hraw (t : I) : r (raw t) = (q t).val := by
      ext i j x
      exact congrArg (fun z : C(I × A, ℂ) ↦ z (t, x)) (hg i j)
    let lift : C(I, S) :=
      ⟨fun t ↦ ⟨P * raw t * P + (1 - P) * raw t * (1 - P), by
          apply (hSmem _).mpr
          have hPc : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
          have hCp : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
          calc
            _ = P * raw t * P := by
              simp only [mul_add, ← mul_assoc, hP, hPc, zero_mul, add_zero]
            _ = _ := by
              simp only [add_mul, mul_assoc, hP, hCp, mul_zero, add_zero]⟩,
        by
          apply Continuous.subtype_mk
          exact ((continuous_const.mul raw.continuous).mul continuous_const).add
            ((continuous_const.mul raw.continuous).mul continuous_const)⟩
    refine ⟨lift, ?_⟩
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    change r (P * raw t * P + (1 - P) * raw t * (1 - P)) = (q t).val
    simp only [map_add, map_mul, map_sub, map_one, hraw]
    have hPP : r P * r P = r P := by rw [← map_mul, hP]
    have hcomm := (hTmem (q t).val).mp (q t).property
    have hcorner : r P * (q t).val * r P = r P * (q t).val := by
      calc
        _ = (q t).val * (r P * r P) := by rw [hcomm, mul_assoc]
        _ = (q t).val * r P := by rw [hPP]
        _ = _ := hcomm.symm
    simp only [sub_mul, mul_sub, one_mul, mul_one]
    rw [hcorner]
    rw [hcomm]
    abel
  have hs : Function.Surjective f := by
    intro z
    obtain ⟨q, hq⟩ := hI (ContinuousMap.const I z)
    exact ⟨q 0, congrArg (fun c : C(I, T) ↦ c 0) hq⟩
  -- Lift inside the closed centralizer, so the lifted units still preserve the same image.
  let aS : Sˣ :=
    { val := ⟨a.val, (hSmem _).mpr ha.eq.symm⟩
      inv := ⟨(a⁻¹).val, (hSmem _).mpr ha.units_inv_left.eq.symm⟩
      val_inv := Subtype.ext a.val_inv
      inv_val := Subtype.ext a.inv_val }
  let bT : C(I, Tˣ) :=
    ⟨fun t ↦
      { val := ⟨(b t).val, (hTmem _).mpr (hb t).eq.symm⟩
        inv := ⟨((b t)⁻¹).val, (hTmem _).mpr (hb t).units_inv_left.eq.symm⟩
        val_inv := Subtype.ext (b t).val_inv
        inv_val := Subtype.ext (b t).inv_val }, by
      apply Units.continuous_iff.mpr
      exact ⟨(Units.continuous_val.comp b.continuous).subtype_mk _,
        (Units.continuous_coe_inv.comp b.continuous).subtype_mk _⟩⟩
  have hbzero : bT 0 = Units.map f.toMonoidHom aS := by
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val hzero
  obtain ⟨cS, hcSzero, hcS⟩ := exists_unit_path_lift f hf hs hI aS bT hbzero
  let c : C(I, MXˣ) :=
    ⟨fun t ↦ Units.map S.val.toMonoidHom (cS t),
      (continuous_unitsMap S.val.toRingHom continuous_subtype_val).comp cS.continuous⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · apply Units.ext
    have h := congrArg (fun u : Sˣ ↦ (u.val : MX)) hcSzero
    exact h
  · intro t
    apply Units.ext
    exact congrArg (fun u : Tˣ ↦ (u.val : MA)) (hcS t)
  · intro t
    exact ((hSmem _).mp (cS t).val.property).symm

end AtiyahSinger
