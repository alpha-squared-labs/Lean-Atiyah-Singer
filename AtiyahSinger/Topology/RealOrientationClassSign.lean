/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RealOrientationClass

/-!
# Signs of the geometrically normalized fiber class

Public module ID: M2044.

Changing the native orientation changes the signed simplex and its dual
normalized integral cohomology class by the same sign. The proof uses the
original cap evaluation, including rank zero. This supplies the sign in
real/complex Thom comparisons without replacing the chosen fiber generator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

variable {r : ℕ} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (b : Module.Basis (Fin r) ℝ V) (o : Orientation ℝ V (Fin r))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Negating the native orientation reverses its actual signed local cycle. -/
theorem realOrientationCycle_neg :
    realOrientationCycle b (-o) = -realOrientationCycle b o := by
  classical
  have hsign : (if b.orientation = -o then (1 : ℤ) else -1) =
      -(if b.orientation = o then 1 else -1) := by
    rcases b.orientation_eq_or_eq_neg o with h | h
    · subst o
      simp [Module.Ray.ne_neg_self]
    · rw [h]
      simp [Module.Ray.ne_neg_self]
  -- The same simplex is retained; only its integral coefficient changes.
  unfold realOrientationCycle
  rw [← map_neg]
  congr 1
  apply Subtype.ext
  change realOrientationRelativeChain b (-o) = -realOrientationRelativeChain b o
  unfold realOrientationRelativeChain
  rw [hsign]
  erw [← map_neg, ← map_neg]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Negating the native orientation negates its normalized integral fiber class. -/
theorem realOrientationClass_neg :
    realOrientationClass b (-o) = -realOrientationClass b o := by
  apply (existsUnique_realOrientationClass b (-o)).unique
  · exact realOrientationClass_evaluation b (-o)
  · -- Two signs cancel in the original cap pairing, so evaluation remains one.
    unfold realOrientationEvaluation
    rw [realOrientationCycle_neg]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
    exact realOrientationClass_evaluation b o

/-- Any integral orientation sign acts on the normalized class by that same sign. -/
theorem realOrientationClass_units_smul (s : ℤˣ) :
    realOrientationClass b (s • o) = (s : ℤ) • realOrientationClass b o := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp
  · have hsign : (-1 : ℤˣ) • o = -o := by
      induction o using Module.Ray.ind with
      | h f hf =>
        simp only [smul_rayOfNeZero, Units.smul_def, Units.val_neg, Units.val_one,
          neg_one_smul, neg_rayOfNeZero]
    rw [hsign]
    simpa using realOrientationClass_neg b o

/-- A dimension equality transports the actual normalized class without changing its basis order. -/
theorem realOrientationClass_reindex {n : ℕ} (h : r = n) :
    cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℤ {v : V | v ≠ 0} k)) h)
      (realOrientationClass b o) =
    realOrientationClass (b.reindex (finCongr h)) (Orientation.reindex ℝ V (finCongr h) o) := by
  subst n
  simp only [cast_eq, finCongr_refl, Module.Basis.reindex_refl,
    Orientation.reindex_refl, Equiv.refl_apply]

end AtiyahSinger
