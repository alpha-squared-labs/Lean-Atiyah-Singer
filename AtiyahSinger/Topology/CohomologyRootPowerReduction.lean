/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RootPowerReduction
public import AtiyahSinger.Topology.EvenCohomologyNaturality
public import AtiyahSinger.Topology.SingularCohomologyPowerCombination

/-!
# Homogeneous coefficients of the split root relation

Public module ID: M1628.

The vanishing product relation gives exactly the signed elementary symmetric
coefficients in the original degreewise cup-power combination. Homogeneous
inclusion is injective, so finite polynomial evaluation proves this equality
in the original integral singular cohomology group, with all degree transports.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

/-- A vanishing split root product gives the actual homogeneous lower-power coefficients. -/
theorem singularCohomologyPowerCombination_esymm_eq_pow
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (r : ℕ) (x : Fin r → singularCohomology ℤ X 2)
    (t : singularCohomology ℤ Y 2)
    (h : ∏ i : Fin r, (singularEvenCohomologyOf ℤ Y 1 t -
      singularEvenCohomologyPullback ℤ π (singularEvenCohomologyOf ℤ X 1 (x i))) = 0) :
    singularCohomologyPowerCombination ℤ π t r r (fun i ↦ Nat.le_of_lt i.isLt)
        (fun i ↦ (-1 : ℤ) ^ (r - i.val + 1) •
          singularCohomologyElementarySymmetric ℤ X (List.ofFn x) (r - i.val)) =
      singularCohomologyDegreeTwoPow ℤ Y t r := by
  classical
  let T := singularEvenCohomologyOf ℤ Y 1 t
  let y (i : Fin r) :=
    singularEvenCohomologyPullback ℤ π (singularEvenCohomologyOf ℤ X 1 (x i))
  have hmap (k : ℕ) :
      singularEvenCohomologyPullback ℤ π
          ((Finset.univ.val.map (fun i : Fin r ↦
            singularEvenCohomologyOf ℤ X 1 (x i))).esymm k) =
        (Finset.univ.val.map y).esymm k := by
    simp only [Finset.esymm_map_val, map_sum, map_prod, y]
  -- Embed each original homogeneous cup summand, preserving its specified total degree.
  apply singularEvenCohomologyOf_injective ℤ Y r
  rw [singularCohomologyPowerCombination_apply, map_sum,
    singularEvenCohomologyOf_degreeTwoPow]
  have hsum :
      (∑ i : Fin r, (-1 : SingularEvenCohomology ℤ Y) ^ (r - i.val + 1) *
          (Finset.univ.val.map y).esymm (r - i.val) * T ^ i.val) = T ^ r :=
    (pow_eq_sum_esymm_of_prod_sub_eq_zero r y T h).symm
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [singularEvenCohomologyOf_eqToIso ℤ Y (Nat.sub_add_cancel (Nat.le_of_lt i.isLt)),
    singularEvenCohomologyOf_cup,
    singularEvenCohomologyOf_degreeTwoPow, map_zsmul, map_zsmul,
    ← singularEvenCohomologyPullback_of, singularEvenCohomologyOf_elementarySymmetric,
    ← Fin.univ_val_map, Multiset.map_map]
  simp only [Function.comp_def]
  rw [hmap]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, T]

end AtiyahSinger
