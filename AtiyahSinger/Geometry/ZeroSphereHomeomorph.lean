/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SphereTangentCoordinates

/-!
# The original zero sphere as its two specified poles

The actual zero-dimensional sphere is homeomorphic to the discrete two-point
space, in the existing south/north order. This permits finite clopen arguments
to keep the two original fibers separate when their bundle ranks differ.
The proof uses the existing height-gradient characterization of the two poles;
no alternate sphere model or new pole is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The two original poles identify the zero sphere with the discrete Boolean space. -/
theorem exists_zeroSphere_homeomorph :
    ∃ e : Bool ≃ₜ OrthogonalSphere 0, ∀ b, e b = orthogonalSpherePole 0 b := by
  have hinj : Function.Injective (orthogonalSpherePole 0) := by
    intro b c h
    have hh := congrArg (fun x : OrthogonalSphere 0 ↦ x.val.snd) h
    cases b <;> cases c
    all_goals first | rfl | norm_num [orthogonalSpherePole, orthogonalSphereNorth] at hh
  have hsurj : Function.Surjective (orthogonalSpherePole 0) := by
    intro x
    have hzero : orthogonalSphereHeightGradient 0 x = 0 := by
      change (_ : EuclideanSpace ℝ (Fin 0)) = _
      exact Subsingleton.elim _ _
    have hx := (orthogonalSphereHeightGradient_eq_zero_iff 0 x).mp hzero
    rcases hx with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩
  -- A continuous bijection from the compact discrete source has continuous inverse.
  let e := Equiv.ofBijective (orthogonalSpherePole 0) ⟨hinj, hsurj⟩
  exact ⟨(continuous_of_discreteTopology (f := e)).homeoOfEquivCompactToT2, fun _ ↦ rfl⟩

end AtiyahSinger
