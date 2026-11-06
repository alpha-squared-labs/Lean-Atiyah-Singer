/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationRing

/-!
# The representation ring of the trivial group

Public module ID: M0072.

For a trivial structure group the original representation class is its integer
dimension times the actual tensor unit. The proof uses equivariant coordinate
isomorphisms and direct sums of the original finite representations. This permits
the associated coefficient in SG III.13.6 to reduce to an integer when
its structure group is trivial.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {G : Type*} [Group G] [Subsingleton G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every class of a trivial group is its integer dimension in the original representation ring. -/
theorem representation_eq_intCast_dimension_of_subsingleton
    (x : RepresentationGrothendieckGroup G) :
    x = (representationDimension G x : RepresentationGrothendieckGroup G) := by
  let τ (n : ℕ) : FiniteContinuousRepresentation G := {
    dimension := n
    representation := ContRepresentation.trivial ℂ G (Fin n → ℂ)
    continuous_action := continuous_snd }
  -- The specified finite direct sums identify the rank-n trivial action with n tensor units.
  have hsum (n m : ℕ) : finiteRepresentationClass (τ (n + m)) =
      finiteRepresentationClass (τ n) + finiteRepresentationClass (τ m) := by
    rw [← finiteRepresentationClass_directSum]
    apply finiteRepresentationClass_eq_of_isEquivalent
    refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
    intro g
    apply ContinuousLinearMap.ext
    intro v
    let d : (Fin (n + m) → ℂ) ≃L[ℂ] (Fin n → ℂ) × (Fin m → ℂ) :=
      (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n ⊕ Fin m ↦ ℂ)
        finSumFinEquiv.symm).trans
        (ContinuousLinearEquiv.sumPiEquivProdPi ℂ (Fin n) (Fin m) (fun _ ↦ ℂ))
    change v = d.symm (d v)
    exact (d.symm_apply_apply v).symm
  have hzero : finiteRepresentationClass (τ 0) = 0 := by
    have h := hsum 0 0
    exact (add_left_cancel (show finiteRepresentationClass (τ 0) +
      finiteRepresentationClass (τ 0) = finiteRepresentationClass (τ 0) + 0 by
        simpa only [add_zero] using h.symm))
  have hnat (n : ℕ) : finiteRepresentationClass (τ n) =
      (n : RepresentationGrothendieckGroup G) := by
    induction n with
    | zero => exact hzero
    | succ n ih =>
      rw [hsum, ih, Nat.cast_add, Nat.cast_one]
      rfl
  have hgen (ρ : FiniteContinuousRepresentation G) :
      finiteRepresentationClass ρ =
        (representationDimension G (finiteRepresentationClass ρ) :
          RepresentationGrothendieckGroup G) := by
    have hρ : ρ.IsEquivalent (τ ρ.dimension) := by
      refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
      intro g
      have hg : g = 1 := Subsingleton.elim _ _
      subst g
      simp
    rw [representationDimension_finiteClass, Int.cast_natCast]
    exact (finiteRepresentationClass_eq_of_isEquivalent ρ (τ ρ.dimension) hρ).trans
      (hnat ρ.dimension)
  -- The original presentation extends the equality to all virtual classes.
  have h : AddMonoidHom.id (RepresentationGrothendieckGroup G) =
      (Int.castAddHom (RepresentationGrothendieckGroup G)).comp (representationDimension G) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact hgen
  exact DFunLike.congr_fun h x

end AtiyahSinger
