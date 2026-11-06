/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorParity
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Finite homogeneous coordinates of the original exterior parity spaces

Public module ID: M0021.

The original Clifford parity at the zero quadratic form is the finite direct
sum of the actual exterior powers of matching degree. The map uses the canonical
natural grading, and its inverse is the sum of the original homogeneous
inclusions. No basis is chosen for this equivalence. Finite dimension is used
only to remove exterior powers above the dimension bound.

Source: the standard graded exterior algebra decomposition, SG Appendix C.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators DirectSum

variable (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (n : ℕ) (hn : Module.finrank ℂ V = n) (i : ZMod 2)

set_option maxHeartbeats 1200000 in
-- Keep the two original gradings and the finite dependent degree coordinates together.
/-- Canonical homogeneous coordinates on the original exterior parity carrier. -/
def exteriorParityDegreesEquiv :
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i ≃ₗ[ℂ]
      ((p : {p : Fin (n + 1) // (p.val : ZMod 2) = i}) → ⋀[ℂ]^p.val.val V) := by
  classical
  let grade (p : ℕ) : Submodule ℂ (ExteriorAlgebra ℂ V) :=
    ⋀[ℂ]^p V
  let : DirectSum.Decomposition grade :=
    inferInstanceAs (DirectSum.Decomposition (fun k : ℕ ↦ ⋀[ℂ]^k V))
  let D := DirectSum.decomposeLinearEquiv grade
  let J := {p : Fin (n + 1) // (p.val : ZMod 2) = i}
  let parity := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
  have hmem (p : J) (v : ⋀[ℂ]^p.val.val V) : (v : ExteriorAlgebra ℂ V) ∈ parity := by
    exact (le_iSup (fun q : {k : ℕ // (k : ZMod 2) = i} ↦ grade q.val)
      ⟨p.val.val, p.property⟩) v.property
  let L : parity →ₗ[ℂ] ((p : J) → ⋀[ℂ]^p.val.val V) := {
    toFun v p := D v.val p.val.val
    map_add' v w := by
      funext p
      exact congrArg (fun z ↦ z p.val.val) (D.map_add v.val w.val)
    map_smul' c v := by
      funext p
      exact congrArg (fun z ↦ z p.val.val) (D.map_smul c v.val) }
  let S : ((p : J) → ⋀[ℂ]^p.val.val V) → parity := fun v ↦
    ⟨∑ p : J, (v p : ExteriorAlgebra ℂ V), parity.sum_mem (fun p _ ↦ hmem p (v p))⟩
  -- Every supplied finite coordinate returns under the natural grading projection.
  have hright (v : (p : J) → ⋀[ℂ]^p.val.val V) : L (S v) = v := by
    funext q
    change ((DirectSum.component ℂ ℕ (fun p ↦ grade p) q.val.val).comp D.toLinearMap)
      (∑ p : J, (v p : ExteriorAlgebra ℂ V)) = v q
    rw [map_sum]
    change (∑ p : J, D (v p : ExteriorAlgebra ℂ V) q.val.val) = v q
    rw [Finset.sum_eq_single q]
    · exact congrArg (fun z ↦ z q.val.val) (DirectSum.decompose_coe grade (v q)) |>.trans
        (DirectSum.of_eq_same _ _)
    · intro p _ hp
      have hne : q.val.val ≠ p.val.val := by
        intro h
        apply hp
        apply Subtype.ext
        exact Fin.ext h.symm
      change DirectSum.decompose grade (v p : ExteriorAlgebra ℂ V) q.val.val = 0
      rw [DirectSum.decompose_coe]
      exact DirectSum.of_eq_of_ne _ _ _ hne
    · simp
  -- The other parity has zero projection on this submodule, directly from its defining supremum.
  have hother (k : ℕ) (hk : (k : ZMod 2) ≠ i) (v : parity) : D v.val k = 0 := by
    let component := (DirectSum.component ℂ ℕ (fun p ↦ grade p) k).comp D.toLinearMap
    have hle : parity ≤ component.ker := by
      change (⨆ p : {p : ℕ // (p : ZMod 2) = i}, grade p.val) ≤ component.ker
      apply iSup_le
      intro p x hx
      change DirectSum.decompose grade x k = 0
      rw [DirectSum.decompose_of_mem grade hx]
      apply DirectSum.of_eq_of_ne
      intro h
      exact hk (h ▸ p.property)
    exact hle v.property
  have hinjective : Function.Injective L := by
    intro v w hvw
    apply Subtype.ext
    apply D.injective
    apply DFinsupp.ext
    intro k
    by_cases hk : k < n + 1
    · by_cases hi : (k : ZMod 2) = i
      · exact congrArg (fun z ↦ z (⟨⟨k, hk⟩, hi⟩ : J)) hvw
      · exact (hother k hi v).trans (hother k hi w).symm
    · -- All higher exterior powers vanish; their empty basis is sufficient in dimension zero too.
      let b := Module.finBasis ℂ V
      let : Subsingleton (grade k) := exteriorPower.subsingleton_of_span_eq_top_of_card_lt
        (R := ℂ) b b.span_eq k (by
          have hnk : n < k := by omega
          simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, hn] using hnk)
      exact Subsingleton.elim _ _
  exact { L with
    invFun := S
    left_inv := fun v ↦ hinjective (hright (L v))
    right_inv := hright }

/-- Forward coordinates are the original natural-degree projections. -/
theorem exteriorParityDegreesEquiv_apply
    (v : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i)
    (p : {p : Fin (n + 1) // (p.val : ZMod 2) = i}) :
    exteriorParityDegreesEquiv V n hn i v p =
      DirectSum.decompose (fun k : ℕ ↦ ⋀[ℂ]^k V) v.val p.val.val := rfl

/-- Inverse coordinates sum the original homogeneous inclusions, with no basis-dependent map. -/
theorem exteriorParityDegreesEquiv_symm_coe
    (v : (p : {p : Fin (n + 1) // (p.val : ZMod 2) = i}) → ⋀[ℂ]^p.val.val V) :
    ((exteriorParityDegreesEquiv V n hn i).symm v : ExteriorAlgebra ℂ V) =
      ∑ p, (v p : ExteriorAlgebra ℂ V) := rfl

/-- The finite homogeneous inverse commutes with every linear exterior map. -/
theorem exteriorParityDegreesEquiv_symm_naturality
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (hW : Module.finrank ℂ W = n) (f : V →ₗ[ℂ] W)
    (v : (p : {p : Fin (n + 1) // (p.val : ZMod 2) = i}) → ⋀[ℂ]^p.val.val V) :
    ExteriorAlgebra.map f ((exteriorParityDegreesEquiv V n hn i).symm v).val =
      ((exteriorParityDegreesEquiv W n hW i).symm
        (fun p ↦ exteriorPower.map p.val.val f (v p)) : ExteriorAlgebra ℂ W) := by
  rw [exteriorParityDegreesEquiv_symm_coe, exteriorParityDegreesEquiv_symm_coe, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact (exteriorPower.coe_map f (v p)).symm

end AtiyahSinger
