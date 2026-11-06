/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyPolynomialEvaluation
public import AtiyahSinger.Topology.SingularCohomologyPowerCombination

/-!
# Degree-two detection by the two projective axes

Public module ID: M2011.

A two-term Leray--Hirsch decomposition on an iterated projective line bundle
makes restriction to its two axes jointly injective in degree two. The first
axis detects the base term. The second detects the degree-zero coefficient
of the tautological root; degree-zero pullback identifies that coefficient
with a class on the original base. There is no mixed term in degree two.

This formulation keeps the actual pullback maps and root restrictions as
explicit hypotheses, so it applies to the original projector model without
replacing its spaces or maps. It is the degree-two consequence of the ordinary
Leray--Hirsch theorem used in the line-bundle tensor formula.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite

universe u

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- With two powers, the degree-two comparison has exactly its base and root terms. -/
theorem singularCohomology_two_term_bijective_of_powerCombination
    (R : Type) [CommRing R] {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (p : C(Y, X)) (t : singularCohomology R Y 2)
    (hb : Function.Bijective (singularCohomologyPowerCombination R p t 2 1
      (fun i ↦ Nat.le_of_lt_succ i.isLt))) :
    Function.Bijective (fun v : singularCohomology R X 2 × singularCohomology R X 0 ↦
      singularCohomologyPullback R p 2 v.1 +
        singularCohomologyCup R Y 0 2 (singularCohomologyPullback R p 0 v.2) t) := by
  let e := LinearEquiv.piFinTwo R
    (fun i : Fin 2 ↦ (singularCohomology R X (2 * (1 - i.val)) : Type u))
  let C := singularCohomologyPowerCombination R p t 2 1
    (fun i ↦ Nat.le_of_lt_succ i.isLt)
  have h (v : singularCohomology R X 2 × singularCohomology R X 0) :
      C (e.symm v) = singularCohomologyPullback R p 2 v.1 +
        singularCohomologyCup R Y 0 2 (singularCohomologyPullback R p 0 v.2) t := by
    have he₀ : (e.symm v) 0 = v.1 := congrArg Prod.fst (e.apply_symm_apply v)
    have he₁ : (e.symm v) 1 = v.2 := congrArg Prod.snd (e.apply_symm_apply v)
    apply singularEvenCohomologyOf_injective R Y 1
    rw [singularCohomologyPowerCombination_apply, map_sum, Fin.sum_univ_two, map_add]
    simp only [singularEvenCohomologyOf_eqToIso, singularEvenCohomologyOf_cup,
      singularEvenCohomologyOf_degreeTwoPow, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      mul_one]
    have hcup : singularEvenCohomologyOf R Y 1
        (singularCohomologyCup R Y 0 2 (singularCohomologyPullback R p 0 v.2) t) =
        singularEvenCohomologyOf R Y 0 (singularCohomologyPullback R p 0 v.2) *
          singularEvenCohomologyOf R Y 1 t :=
      singularEvenCohomologyOf_cup R Y 0 1 _ _
    rw [hcup]
    congr 1
  have he : Function.Bijective (fun v : singularCohomology R X 2 ×
      singularCohomology R X 0 ↦ C (e.symm v)) := hb.comp e.symm.bijective
  simpa only [h] using he

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The two axes detect degree-two cohomology in successive projective-line decompositions. -/
theorem singularCohomology_eq_zero_of_projective_axes
    (R : Type) [CommRing R] {X Y Z W : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
    (p₁ : C(Y, X)) (p₂ : C(Z, X)) (q : C(W, Y))
    (a : C(Y, W)) (b : C(Z, W))
    (ha : q.comp a = ContinuousMap.id Y) (hb : p₁.comp (q.comp b) = p₂)
    (η : singularCohomology R W 2) (τ : singularCohomology R Z 2)
    (hηa : singularCohomologyPullback R a 2 η = 0)
    (hηb : singularCohomologyPullback R b 2 η = τ)
    (hzero : Function.Surjective (singularCohomologyPullback R p₁ 0))
    (hdecomp : ∀ c : singularCohomology R W 2,
      ∃ A : singularCohomology R Y 2, ∃ B : singularCohomology R Y 0,
        c = singularCohomologyPullback R q 2 A +
          singularCohomologyCup R W 0 2 (singularCohomologyPullback R q 0 B) η)
    (hinj : Function.Injective (fun v : singularCohomology R X 2 ×
        singularCohomology R X 0 ↦
      singularCohomologyPullback R p₂ 2 v.1 +
        singularCohomologyCup R Z 0 2 (singularCohomologyPullback R p₂ 0 v.2) τ))
    (c : singularCohomology R W 2)
    (hca : singularCohomologyPullback R a 2 c = 0)
    (hcb : singularCohomologyPullback R b 2 c = 0) : c = 0 := by
  -- Pullback composition is used only for these actual maps, with their original cochain functor.
  have hcomp {U V T : Type u} [TopologicalSpace U] [TopologicalSpace V]
      [TopologicalSpace T] (f : C(V, U)) (g : C(T, V)) (k : ℕ)
      (x : singularCohomology R U k) :
      singularCohomologyPullback R g k (singularCohomologyPullback R f k x) =
        singularCohomologyPullback R (f.comp g) k x := by
    exact (congrArg (fun m ↦ m x)
      ((singularCohomologyFunctor R k).map_comp
        (TopCat.ofHom f).op (TopCat.ofHom g).op)).symm
  obtain ⟨A, B, hc⟩ := hdecomp c
  obtain ⟨B₀, rfl⟩ := hzero B
  -- The root vanishes on the first axis, so the whole degree-two base coefficient vanishes.
  have hA : A = 0 := by
    have h := congrArg (singularCohomologyPullback R a 2) hc
    rw [hca, map_add, singularCohomologyPullback_cup R a 0 2, hηa, map_zero, add_zero,
      hcomp, ha] at h
    have hid : singularCohomologyPullback R (ContinuousMap.id Y) 2 = 𝟙 _ :=
      (singularCohomologyFunctor R 2).map_id _
    rw [hid] at h
    exact h.symm
  rw [hA, map_zero, zero_add] at hc
  -- On the second axis the remaining term is the pulled-back base coefficient times τ.
  have hB : singularCohomologyCup R Z 0 2
      (singularCohomologyPullback R p₂ 0 B₀) τ = 0 := by
    have h := congrArg (singularCohomologyPullback R b 2) hc
    rw [hcb, singularCohomologyPullback_cup R b 0 2, hηb, hcomp, hcomp, hb] at h
    exact h.symm
  have hB₀ : B₀ = 0 := by
    have hpair : ((0 : singularCohomology R X 2), B₀) = (0, (0 : singularCohomology R X 0)) := by
      apply hinj
      simpa only [map_zero, zero_add, LinearMap.zero_apply] using hB
    exact congrArg Prod.snd hpair
  -- Both original Leray--Hirsch coefficients are now zero.
  simpa only [hB₀, map_zero, LinearMap.zero_apply] using hc

end AtiyahSinger
