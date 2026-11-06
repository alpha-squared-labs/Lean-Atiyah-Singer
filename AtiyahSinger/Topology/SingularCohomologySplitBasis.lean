/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologySequence

/-!
# Lifting a cohomology basis through a pair

Public module ID: M2138.

Suppose specified ambient classes give a bijective parametrization of the
cohomology of a subspace in every degree. The relative long exact sequence
then splits: the specified lifts, together with the relative classes, give
a bijective parametrization of ambient cohomology. Surjectivity in the
preceding degree makes the relative-to-ordinary map injective; degree zero
uses the start of the original cochain sequence.

This is the elementary pair-sequence step in the projective-space basis
induction. All maps are the original singular pullbacks and relative maps;
the coefficient ring and spaces are arbitrary.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex

universe u

variable (R : Type) [CommRing R] {Y : Type u} [TopologicalSpace Y]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Specified lifts of a subspace cohomology basis complement the original relative classes. -/
theorem singularCohomology_split_bijective (A : Set Y) (L : ℕ → ModuleCat.{u} R)
    (f : ∀ n : ℕ, L n ⟶ singularCohomology R Y n)
    (hf : ∀ n : ℕ, Function.Bijective (fun a : L n ↦
      singularCohomologyPullback R (ContinuousMap.subtypeVal A) n (f n a))) (n : ℕ) :
    Function.Bijective (fun a : L n × relativeSingularCohomology R A n ↦
      f n a.1 + relativeSingularCohomologyToOrdinary R A n a.2) := by
  let S := singularSubspaceCochainsSequence R A
  have hS := shortExact_singularSubspaceCochains R A
  let j (k : ℕ) := relativeSingularCohomologyToOrdinary R A k
  let r (k : ℕ) := singularCohomologyPullback R (ContinuousMap.subtypeVal A) k
  have hepi (k : ℕ) : Epi (homologyMap S.g k) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro b
    obtain ⟨a, ha⟩ := (hf k).surjective b
    exact ⟨f k a, ha⟩
  -- All connecting maps vanish because the preceding restriction is surjective.
  have hmono (k : ℕ) : Mono (homologyMap S.f k) := by
    cases k with
    | zero =>
      have := hS.mono_f
      exact mono_homologyMap_of_mono_of_not_rel S.f 0 (by intro i hi; simp at hi)
    | succ k =>
      have := hepi k
      apply (hS.homology_exact₁ k (k + 1) rfl).mono_g_iff.mpr
      apply (cancel_epi (homologyMap S.g k)).mp
      simp
  have hj : Function.Injective (j n) :=
    (ModuleCat.mono_iff_injective (homologyMap S.f n)).mp (hmono n)
  have hzero (a : relativeSingularCohomology R A n) : r n (j n a) = 0 :=
    congrArg (fun g ↦ g a)
      ((S.map (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n)).zero)
  have hexact : ∀ b : singularCohomology R Y n, r n b = 0 →
      ∃ a : relativeSingularCohomology R A n, j n a = b :=
    (ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₂ n)
  constructor
  · -- Restriction detects the lifted coefficient, then injectivity detects the relative one.
    rintro ⟨a, c⟩ ⟨b, d⟩ hab
    have hrestrict := congrArg (r n) hab
    change r n (f n a + j n c) = r n (f n b + j n d) at hrestrict
    rw [map_add, map_add, hzero, hzero, add_zero, add_zero] at hrestrict
    have hab' : a = b := (hf n).injective hrestrict
    subst b
    have hcd : j n c = j n d := add_left_cancel hab
    exact Prod.ext rfl (hj hcd)
  · -- Remove the chosen lift; exactness supplies the remaining relative class.
    intro b
    obtain ⟨a, ha⟩ := (hf n).surjective (r n b)
    change r n (f n a) = r n b at ha
    have hrem : r n (b - f n a) = 0 := by
      rw [map_sub, ha, sub_self]
    obtain ⟨c, hc⟩ := hexact (b - f n a) hrem
    refine ⟨(a, c), ?_⟩
    change f n a + j n c = b
    rw [hc]
    abel

end AtiyahSinger
