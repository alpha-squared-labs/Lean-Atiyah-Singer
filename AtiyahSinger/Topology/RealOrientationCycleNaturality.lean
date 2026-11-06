/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RealOrientationCycleSign
public import AtiyahSinger.Topology.PositiveLinearHomotopy

/-!
# Basis independence of the geometrically signed local cycle

Public module ID: M2046.

Positive determinant changes act through an actual homotopy of the punctured
pair. A standard reflection has determinant -1 and swaps the first two
vertices of the original simplex. The chain-level sign calculation therefore
matches the native orientation comparison for every basis. The empty basis
case is retained separately, with either native orientation sign.
-/
@[expose] public noncomputable section
namespace AtiyahSinger
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The signed primitive simplex class is independent of the auxiliary coordinate basis. -/
theorem realOrientationCycle_basis_independent {r : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b c : Module.Basis (Fin r) ℝ V) (o : Orientation ℝ V (Fin r)) :
    realOrientationCycle b o = realOrientationCycle c o := by
  classical
  let : FiniteDimensional ℝ V := Module.Finite.of_basis b
  -- Positive changes preserve the original cycle through the actual punctured-pair map.
  have hpositive (b c : Module.Basis (Fin r) ℝ V) (h : c.orientation = b.orientation) :
      realOrientationCycle c c.orientation = realOrientationCycle b b.orientation := by
    let e := (b.equiv c (Equiv.refl _)).toContinuousLinearEquiv
    have he : b.map e.toLinearEquiv = c := by
      apply Module.Basis.eq_of_apply_eq
      intro i
      exact b.equiv_apply i c (Equiv.refl _)
    have hdet : 0 < LinearMap.det e.toLinearMap :=
      (b.orientation_comp_linearEquiv_eq_iff_det_pos e.toLinearEquiv).mp (he ▸ h)
    have hmap := congrArg (fun F ↦ F (realOrientationCycle b b.orientation))
      (relativeSingularHomologyMap_eq_id_of_det_pos ℤ b e hdet r)
    rw [realOrientationCycle_map_basis, he] at hmap
    exact hmap
  have hsign (b : Module.Basis (Fin r) ℝ V) (h : b.orientation ≠ o) :
      realOrientationCycle b o = -realOrientationCycle b b.orientation := by
    unfold realOrientationCycle
    rw [← map_neg]
    congr 1
    apply Subtype.ext
    change realOrientationRelativeChain b o = -realOrientationRelativeChain b b.orientation
    simp only [realOrientationRelativeChain, h, ite_false, ite_true]
    erw [← map_neg, ← map_neg]
    rfl
  -- In positive rank a reflection compares the two orientation components.
  cases r with
  | zero =>
    have heq : b = c := Module.Basis.eq_of_apply_eq fun i ↦ Fin.elim0 i
    rw [heq]
  | succ n =>
    have hnegative (h : c.orientation = -b.orientation) :
        realOrientationCycle c c.orientation = -realOrientationCycle b b.orientation := by
      -- The standard reflection replaces the first basis vector by the negative sum.
      -- Its basis matrix is the identity with first column -1, hence determinant -1.
      have hreflection : ∃ e : V ≃L[ℝ] V, LinearMap.det e.toLinearMap < 0 ∧
          e (b 0) = -∑ i, b i ∧ ∀ i : Fin n, e (b i.succ) = b i.succ := by
        classical
        let : FiniteDimensional ℝ V := Module.Finite.of_basis b
        let x := b 0 + ∑ i, b i
        have hx : b.coord 0 x = 2 := by norm_num [x, Module.Basis.coord_apply]
        let e := (Module.reflection hx).toContinuousLinearEquiv
        have he0 : e (b 0) = -∑ i, b i := by
          change Module.reflection hx (b 0) = _
          simp [Module.reflection_apply, Module.Basis.coord_apply, x]
        have hes (i : Fin n) : e (b i.succ) = b i.succ := by
          change Module.reflection hx (b i.succ) = _
          simp [Module.reflection_apply, Module.Basis.coord_apply]
        have hm : LinearMap.toMatrix b b e.toLinearMap =
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).updateCol 0 (fun _ ↦ -1) := by
          ext i j
          refine Fin.cases ?_ (fun j ↦ ?_) j
          · simp [LinearMap.toMatrix_apply, he0]
          · simp [LinearMap.toMatrix_apply, hes, Matrix.one_apply, Finsupp.single_apply, eq_comm]
        have hd : LinearMap.det e.toLinearMap = -1 := by
          rw [← LinearMap.det_toMatrix b, hm]
          have hsum := Matrix.det_updateCol_sum
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0 (fun _ ↦ (-1 : ℝ))
          simpa [Matrix.one_apply] using hsum
        exact ⟨e, by rw [hd]; norm_num, he0, hes⟩
      obtain ⟨e, hdet, he₀, he₁⟩ := hreflection
      let d := b.map e.toLinearEquiv
      have hd : d.orientation = -b.orientation :=
        (b.orientation_comp_linearEquiv_eq_neg_iff_det_neg e.toLinearEquiv).mpr hdet
      exact (hpositive d c (h.trans hd.symm)).trans
        (realOrientationCycle_reflection b e he₀ he₁)
    by_cases hbc : c.orientation = b.orientation
    · by_cases hb : b.orientation = o
      · have hc : c.orientation = o := hbc.trans hb
        simpa only [hb, hc] using (hpositive b c hbc).symm
      · have hc : c.orientation ≠ o := fun h ↦ hb (hbc.symm.trans h)
        rw [hsign b hb, hsign c hc, hpositive b c hbc]
    · have hbcneg : c.orientation = -b.orientation :=
        (b.orientation_ne_iff_eq_neg c.orientation).mp hbc
      rcases b.orientation_eq_or_eq_neg o with ho | ho
      · have hc : c.orientation ≠ o := fun h ↦ hbc (h.trans ho)
        rw [hsign c hc, hnegative hbcneg, neg_neg, ho]
      · have hb : b.orientation ≠ o := by
          rw [ho]
          exact Module.Ray.ne_neg_self _
        have hoc : o = c.orientation := ho.trans hbcneg.symm
        rw [hsign b hb, hoc, hnegative hbcneg]

end AtiyahSinger
