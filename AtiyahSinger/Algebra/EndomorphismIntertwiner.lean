/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The defining module of a full endomorphism algebra

Public module ID: M0013.

A unital representation of the full endomorphism algebra on a vector space of
the same finite dimension is equivalent to its defining representation. The
proof chooses one nonzero diagonal matrix-unit image and constructs the
intertwiner from its column. It uses algebra multiplication, not only a linear
isomorphism between the two endomorphism spaces.

This standard matrix-algebra module uniqueness argument is used to compare the
original complex Clifford action with its dual action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u v w

/-- A representation of the full endomorphism algebra in the same dimension is conjugate to it. -/
theorem exists_linearEquiv_intertwining_algHom
    (K : Type u) [Field K] (E : Type v) [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [Nontrivial E]
    (F : Type w) [AddCommGroup F] [Module K F] [FiniteDimensional K F] [Nontrivial F]
    (hdim : Module.finrank K E = Module.finrank K F)
    (ρ : Module.End K E →ₐ[K] Module.End K F) :
    ∃ e : E ≃ₗ[K] F, ∀ (A : Module.End K E) (x : E), e (A x) = ρ A (e x) := by
  classical
  let b := Module.finBasis K E
  let M (i j : Fin (Module.finrank K E)) : Module.End K E := (b.coord j).smulRight (b i)
  -- The diagonal matrix units sum to the identity, so one has a nonzero image under ρ.
  have hdiag : ∑ i, M i i = 1 := by
    ext x
    simpa only [M, LinearMap.sum_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
      Module.End.one_apply] using b.sum_repr x
  have hex : ∃ i, ρ (M i i) ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : (1 : Module.End K F) = 0 := by
      calc
        (1 : Module.End K F) = ρ (∑ i, M i i) := by rw [hdiag, map_one]
        _ = 0 := by simp only [map_sum, h, Finset.sum_const_zero]
    exact one_ne_zero hzero
  obtain ⟨i, hi⟩ := hex
  obtain ⟨w, hw⟩ : ∃ w : F, ρ (M i i) w ≠ 0 := by
    by_contra h
    push Not at h
    exact hi (LinearMap.ext h)
  let φ : E →ₗ[K] F := b.constr K (fun j ↦ ρ (M j i) w)
  have hφ (j : Fin (Module.finrank K E)) : φ (b j) = ρ (M j i) w := b.constr_basis _ _ j
  -- The same matrix-unit column intertwines every endomorphism, as checked on the original basis.
  have hcolumn (A : Module.End K E) (j : Fin (Module.finrank K E)) :
      ∑ l, b.repr (A (b j)) l • M l i = A * M j i := by
    apply b.ext
    intro k
    by_cases hik : i = k
    · subst k
      simp [M]
    · simp [M, hik]
  have hinter (A : Module.End K E) (x : E) : φ (A x) = ρ A (φ x) := by
    have hmaps : φ.comp A = (ρ A).comp φ := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, hφ]
      calc
        φ (A (b j)) = ∑ l, b.repr (A (b j)) l • ρ (M l i) w := by
          conv_lhs => rw [← b.sum_repr (A (b j))]
          simp only [map_sum, map_smul, hφ]
        _ = ρ (∑ l, b.repr (A (b j)) l • M l i) w := by
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
        _ = ρ A (ρ (M j i) w) := by rw [hcolumn, map_mul, Module.End.mul_apply]
    exact congrArg (fun T : E →ₗ[K] F ↦ T x) hmaps
  -- A rank-one operator would send any nonzero kernel vector to the chosen nonzero column.
  have hinj : Function.Injective φ := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    by_contra hxne
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K hxne
    have h := hinter (l.smulRight (b i)) x
    rw [LinearMap.smulRight_apply, hl, one_smul, hφ, hx, map_zero] at h
    exact hw h
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ) hdim).mp hinj
  exact ⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, hinter⟩

end AtiyahSinger
