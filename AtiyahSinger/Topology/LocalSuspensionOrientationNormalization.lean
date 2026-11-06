/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.LocalHomologyLinearization
public import AtiyahSinger.Topology.SimplexLocalHomology

/-!
# Standard-coordinate normalization of the local suspension

Public module ID: M1946.

The original simplex suspension uses the sum coordinate and differences from
the first coordinate. A continuous family of invertible real linear maps joins
that splitting to the standard first-coordinate splitting. It therefore gives
the same map on the original punctured pair and the same positive local cycle.

The coordinate family has determinant `1 + n * t^2`, positive throughout, with
endpoint determinant `n + 1`. The proof verifies invertibility directly from
its coordinate equations, without changing the chosen cycle or orientation.
This fixes the normalization used in the local Thom cup evaluation argument.

Source: the actual simplex suspension in SimplexLocalHomology and relative
homotopy invariance, Hatcher, Algebraic Topology, Section 3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The standard first-coordinate suspension preserves the same positive local generator. -/
theorem realOrientationCycle_standard_suspension (n : ℕ) :
    let b := (Pi.basisFun ℝ (Fin (n + 1))).map
      (ULift.moduleEquiv : ULift.{u} (Fin (n + 1) → ℝ) ≃ₗ[ℝ] _).symm
    let c := (Pi.basisFun ℝ (Fin n)).map
      (ULift.moduleEquiv : ULift.{u} (Fin n → ℝ) ≃ₗ[ℝ] _).symm
    (euclideanLocalSuspensionIso ℤ (ULift.{u} (Fin n → ℝ)) n).hom
      ((euclideanLocalCoordinateSplitHomologyIso.{u} ℤ n (n + 1)).hom
        (realOrientationCycle b b.orientation)) = realOrientationCycle c c.orientation := by
  /- Join the two actual coordinate maps through invertible linear maps of
  the punctured pair. Their induced homology maps agree, so the already
  normalized simplex suspension gives the standard-coordinate statement. -/
  let V := ULift.{u} (Fin (n + 1) → ℝ)
  let E := ULift.{u} (Fin n → ℝ)
  let s := euclideanLocalCoordinateSplit.{u} n
  let e := (simplexCoordinateSplitting.{u} n).toContinuousLinearEquiv
  let f : C(V, ℝ × E) := ⟨s, s.continuous⟩
  let g : C(V, ℝ × E) := ⟨e, e.continuous⟩
  let H : f.Homotopy g :=
    { toFun := fun z ↦
        (z.2.down 0 + (z.1 : ℝ) * ∑ i : Fin n, z.2.down i.succ,
          ULift.up (fun i ↦ z.2.down i.succ - (z.1 : ℝ) * z.2.down 0))
      continuous_toFun := by
        dsimp only [V, E]
        fun_prop
      map_zero_left := by
        intro x
        change (x.down 0 + (0 : ℝ) * ∑ i : Fin n, x.down i.succ,
          ULift.up (fun i ↦ x.down i.succ - (0 : ℝ) * x.down 0)) = f x
        simp only [zero_mul, add_zero, sub_zero]
        rfl
      map_one_left := by
        intro x
        apply Prod.ext
        · change x.down 0 + (1 : ℝ) * ∑ i : Fin n, x.down i.succ =
            ∑ i : Fin (n + 1), x.down i
          rw [one_mul, Fin.sum_univ_succ]
        · apply ULift.ext
          funext i
          change x.down i.succ - (1 : ℝ) * x.down 0 = x.down i.succ - x.down 0
          rw [one_mul] }
  -- A zero image would force (1 + n*t^2)*x₀ = 0 and then every coordinate to vanish.
  have hH (t : unitInterval) (x : V) (hx : x ≠ 0) : H (t, x) ≠ 0 := by
    intro hz
    have hfirst := congrArg Prod.fst hz
    change x.down 0 + (t : ℝ) * ∑ i : Fin n, x.down i.succ = 0 at hfirst
    have htail (i : Fin n) : x.down i.succ = (t : ℝ) * x.down 0 := by
      have h := congrArg (fun y : ℝ × E ↦ y.2.down i) hz
      change x.down i.succ - (t : ℝ) * x.down 0 = 0 at h
      exact sub_eq_zero.mp h
    simp only [htail, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hfirst
    have hpositive : 0 < 1 + (n : ℝ) * (t : ℝ) ^ 2 := by positivity
    have hx0 : x.down 0 = 0 := by
      have hmul : (1 + (n : ℝ) * (t : ℝ) ^ 2) * x.down 0 = 0 := by
        calc
          _ = x.down 0 + (t : ℝ) * ((n : ℝ) * ((t : ℝ) * x.down 0)) := by ring
          _ = 0 := hfirst
      exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hpositive)
    apply hx
    apply ULift.ext
    funext i
    refine Fin.cases hx0 (fun j ↦ ?_) i
    change x.down j.succ = 0
    simpa only [hx0, mul_zero] using htail j
  have hf : Set.MapsTo f {x : V | x ≠ 0} {y : ℝ × E | y ≠ 0} := by
    intro x hx hz
    exact hx (s.injective (hz.trans (show s 0 = 0 from rfl).symm))
  have hg : Set.MapsTo g {x : V | x ≠ 0} {y : ℝ × E | y ≠ 0} := by
    intro x hx hz
    exact hx (e.injective (hz.trans e.map_zero.symm))
  have hmap := relativeSingularHomologyMap_eq_of_homotopy ℤ hf hg H hH (n + 1)
  -- Retain the same basis cycles; only their already specified coordinate map changes.
  change (euclideanLocalSuspensionIso ℤ E n).hom
    (relativeSingularHomologyMap ℤ f hf (n + 1)
      (realOrientationCycle _ _)) = _
  rw [hmap]
  exact realOrientationCycle_suspension.{u} n

end AtiyahSinger
