/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.NewtonPolynomial
public import AtiyahSinger.Topology.EvenCohomologyNaturality

/-!
# Newton power sums in the original singular cohomology

Public module ID: M1830.

Evaluate the integral power-sum polynomial on the original homogeneous
cohomology classes, then project to its prescribed degree. This constructs a
class before any splitting-space descent is invoked. For elementary symmetric
inputs it recovers the actual sum of cup powers, and it commutes with the
original pullback. No infinite sum or bound on cohomological dimension occurs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- The degree-2k Newton power sum evaluated on the specified even cohomology classes. -/
def singularCohomologyNewtonPowerSum (r : ℕ)
    (c : (j : ℕ) → singularCohomology R X (2 * j)) (k : ℕ) :
    singularCohomology R X (2 * k) :=
  singularEvenCohomologyComponent R X k
    (MvPolynomial.aeval (fun i : Fin r ↦ singularEvenCohomologyOf R X (i.val + 1) (c (i.val + 1)))
      (newtonPowerSumPolynomial r k))

/-- Actual elementary symmetric inputs recover the cup power sum of the same root family. -/
theorem singularCohomologyNewtonPowerSum_elementarySymmetric (r k : ℕ)
    (x : Fin r → singularCohomology R X 2) :
    singularCohomologyNewtonPowerSum R X r
        (fun j ↦ singularCohomologyElementarySymmetric R X (List.ofFn x) j) k =
      ∑ i : Fin r, singularCohomologyDegreeTwoPow R X (x i) k := by
  let y : Fin r → SingularEvenCohomology R X := fun i ↦ singularEvenCohomologyOf R X 1 (x i)
  have hcoeff (i : Fin r) :
      singularEvenCohomologyOf R X (i.val + 1)
          (singularCohomologyElementarySymmetric R X (List.ofFn x) (i.val + 1)) =
        (Finset.univ.val.map y).esymm (i.val + 1) := by
    rw [singularEvenCohomologyOf_elementarySymmetric, ← Fin.univ_val_map, Multiset.map_map]
    rfl
  -- The universal polynomial identity is valid in this actual cup ring.
  change singularEvenCohomologyComponent R X k (MvPolynomial.aeval _ _) = _
  simp_rw [hcoeff]
  rw [newtonPowerSumPolynomial_eval, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change singularEvenCohomologyComponent R X k (singularEvenCohomologyOf R X 1 (x i) ^ k) = _
  rw [← singularEvenCohomologyOf_degreeTwoPow, singularEvenCohomologyComponent_of]

variable {X}

/-- The constructed Newton power sum commutes with the specified original pullback. -/
theorem singularCohomologyNewtonPowerSum_pullback {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (r k : ℕ) (c : (j : ℕ) → singularCohomology R Y (2 * j)) :
    singularCohomologyPullback R f (2 * k) (singularCohomologyNewtonPowerSum R Y r c k) =
      singularCohomologyNewtonPowerSum R X r
        (fun j ↦ singularCohomologyPullback R f (2 * j) (c j)) k := by
  -- Integral polynomial evaluation commutes with the same ring pullback.
  unfold singularCohomologyNewtonPowerSum
  rw [← singularEvenCohomologyComponent_pullback]
  have h := MvPolynomial.comp_aeval_apply
    (singularEvenCohomologyPullback R f).toIntAlgHom
    (f := fun i : Fin r ↦ singularEvenCohomologyOf R Y (i.val + 1) (c (i.val + 1)))
    (newtonPowerSumPolynomial r k)
  simp only [RingHom.toIntAlgHom_apply, singularEvenCohomologyPullback_of] at h
  exact congrArg (singularEvenCohomologyComponent R X k) h

end AtiyahSinger
