/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RealOrientationChangeCoefficients

/-!
# Coefficient change of an actual integral local generator

Public module ID: M1935.

Any specified integral generator of the local cohomology of a real vector
space differs from its normalized orientation class by an integral unit.
The original coefficient map preserves that unit multiple. Consequently its
image generates local cohomology over every commutative ring, using the
already proved coefficient theorem for the normalized orientation class.

The argument includes dimension zero and the zero ring. It does not assume
that arbitrary cohomology groups are obtained by tensoring coefficients.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

/-- Every actual integral local generator remains a generator after the original coefficient map. -/
theorem relativeSingularCohomologyChangeCoefficients_is_generator (R : Type) [CommRing R]
    {r : ℕ} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin r) ℝ V)
    (τ : relativeSingularCohomology ℤ {v : V | v ≠ 0} r)
    (hτ : Function.Bijective (fun a : ℤ ↦ a • τ)) :
    Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyChangeCoefficients R {v : V | v ≠ 0} r τ) := by
  let A : Set V := {v | v ≠ 0}
  let u := realOrientationClass b b.orientation
  have hu : Function.Bijective (fun a : ℤ ↦ a • u) :=
    realOrientationClass_is_generator b b.orientation
  -- Compare the two actual integral generators in both directions to obtain inverse scalars.
  obtain ⟨z, hz⟩ := hu.surjective τ
  obtain ⟨w, hw⟩ := hτ.surjective u
  change z • u = τ at hz
  change w • τ = u at hw
  have hwz : w * z = 1 := by
    apply hu.injective
    change (w * z) • u = (1 : ℤ) • u
    rw [mul_smul, hz, hw, one_smul]
  have hwzR : (w : R) * (z : R) = 1 := by
    rw [← Int.cast_mul, hwz, Int.cast_one]
  let uR := relativeSingularCohomologyChangeCoefficients R A r u
  have huR : Function.Bijective (fun a : R ↦ a • uR) :=
    realOrientationClass_changeCoefficients_is_generator R b b.orientation
  have hτR : relativeSingularCohomologyChangeCoefficients R A r τ = (z : R) • uR := by
    rw [← hz, map_zsmul]
    exact (Int.cast_smul_eq_zsmul R z uR).symm
  -- Multiplication by the changed integral unit is invertible over the original target ring.
  constructor
  · intro a c hac
    change a • relativeSingularCohomologyChangeCoefficients R A r τ =
      c • relativeSingularCohomologyChangeCoefficients R A r τ at hac
    have heq : a * (z : R) = c * (z : R) := by
      apply huR.injective
      simpa only [hτR, smul_smul] using hac
    calc
      a = (a * (z : R)) * (w : R) := by
        rw [mul_assoc, mul_comm (z : R) (w : R), hwzR, mul_one]
      _ = (c * (z : R)) * (w : R) := congrArg (fun x ↦ x * (w : R)) heq
      _ = c := by rw [mul_assoc, mul_comm (z : R) (w : R), hwzR, mul_one]
  · intro x
    obtain ⟨a, ha⟩ := huR.surjective x
    refine ⟨a * (w : R), ?_⟩
    change (a * (w : R)) • relativeSingularCohomologyChangeCoefficients R A r τ = x
    rw [hτR, smul_smul, mul_assoc, hwzR, mul_one]
    exact ha

end AtiyahSinger
