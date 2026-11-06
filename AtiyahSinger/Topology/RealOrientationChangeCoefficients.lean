/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RealOrientationClass
public import AtiyahSinger.Topology.RelativeEvaluationChangeCoefficients
public import AtiyahSinger.Topology.SingularProjectiveEvaluation

/-!
# The specified real orientation class over arbitrary coefficients

Public module ID: M2042.

The actual integer coefficient map sends the normalized integral orientation
class to a generator over every commutative ring. The proof uses the local
homology calculation and projective lower-boundary splittings. Evaluation on
the same changed integral cycle is one, so the resulting rank-one coordinate
is a unit. No nonzero-ring assumption or division is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual coefficient image of the normalized integral real orientation is a generator. -/
theorem realOrientationClass_changeCoefficients_is_generator (R : Type) [CommRing R]
    {r : ℕ} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin r) ℝ V) (o : Orientation ℝ V (Fin r)) :
    Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyChangeCoefficients R {v : V | v ≠ 0} r
        (realOrientationClass b o)) := by
  -- The native basis chart transports the original rank-one local homology calculation.
  let A : Set V := {v | v ≠ 0}
  let : FiniteDimensional ℝ V := Module.Finite.of_basis b
  let e : V ≃L[ℝ] (Fin r → ℝ) := b.equivFun.toContinuousLinearEquiv
  let f : C(V, ULift.{u} (Fin r → ℝ)) :=
    ⟨fun v ↦ ULift.up (e v), continuous_uliftUp.comp e.continuous⟩
  let g : C(ULift.{u} (Fin r → ℝ), V) :=
    ⟨fun y ↦ e.symm y.down, e.symm.continuous.comp continuous_uliftDown⟩
  have hf : Set.MapsTo f A {y | y ≠ 0} := by
    intro v hv h
    apply hv
    apply e.injective
    simpa [f] using congrArg ULift.down h
  have hg : Set.MapsTo g {y | y ≠ 0} A := by
    intro y hy h
    apply hy
    apply ULift.ext
    simpa [g] using congrArg e h
  let : CategoryTheory.IsIso (relativeSingularHomologyMap R f hf r) :=
    isIso_relativeSingularHomologyMap_of_inverse R f g hf hg
      (by apply ContinuousMap.ext; intro v; exact e.symm_apply_apply v)
      (by apply ContinuousMap.ext; intro y; exact congrArg ULift.up (e.apply_symm_apply y.down)) r
  let H : R ≃ₗ[R] relativeSingularHomology R A r :=
    (euclideanLocalHomologyEquiv.{u} R r).trans
      (CategoryTheory.asIso (relativeSingularHomologyMap R f hf r)).symm.toLinearEquiv
  let D := singularCochainHomologyEvaluation R (relativeSingularChains R A) r
  let ev : relativeSingularCohomology R A r →ₗ[R] R :=
    { toFun := fun a ↦ (D a (H 1)).down
      map_add' := by intros; simp [map_add]
      map_smul' := by intros; simp [map_smul] }
  have hbelow (k : ℕ) (hk : k < r) :
      Subsingleton (relativeSingularHomology R A k) :=
    subsingleton_relativeSingularHomology_below_dim_of_continuousLinearEquiv R e k hk
  have hgen : Function.Bijective (fun a : R ↦ a • H 1) := by
    have hfun : (fun a : R ↦ a • H 1) = H := by
      funext a
      rw [← H.map_smul, smul_eq_mul, mul_one]
    rw [hfun]
    exact H.bijective
  have hev : Function.Bijective ev := by
    have h := relativeSingularCapProduct_augmentation_bijective_of_exact_below
      R A r (H 1) hgen hbelow
    convert h using 1
    funext a
    exact (congrArg ULift.down
      (relativeSingularCapProduct_augmentation R A r a (H 1))).symm
  -- Evaluation on the same integral cycle remains one after both coefficient maps.
  let a := relativeSingularCohomologyChangeCoefficients R A r (realOrientationClass b o)
  let z := relativeSingularHomologyChangeCoefficients R A r (realOrientationCycle b o)
  have hnorm : (singularCochainHomologyEvaluation ℤ
      (relativeSingularChains ℤ A) r (realOrientationClass b o)
        (realOrientationCycle b o)).down = 1 := by
    rw [← relativeSingularCapProduct_augmentation]
    exact realOrientationClass_evaluation b o
  have hpair := singularCochainHomologyEvaluation_changeCoefficients R A r
    (realOrientationClass b o) (realOrientationCycle b o)
  rw [hnorm] at hpair
  obtain ⟨t, ht⟩ := H.surjective z
  have hscaled : H t = t • H 1 := by
    rw [← H.map_smul, smul_eq_mul, mul_one]
  have hunit : t * ev a = 1 := by
    change (D a z).down = ((1 : ℤ) : R) at hpair
    rw [← ht, hscaled, map_smul] at hpair
    exact hpair.trans (Int.cast_one (R := R))
  -- This explicit inverse proves the scalar map bijective, including over the zero ring.
  constructor
  · intro s q h
    have heq := congrArg ev h
    change ev (s • a) = ev (q • a) at heq
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at heq
    calc
      s = (s * ev a) * t := by rw [mul_assoc, mul_comm (ev a) t, hunit, mul_one]
      _ = (q * ev a) * t := congrArg (fun x ↦ x * t) heq
      _ = q := by rw [mul_assoc, mul_comm (ev a) t, hunit, mul_one]
  · intro c
    refine ⟨ev c * t, hev.injective ?_⟩
    change ev ((ev c * t) • a) = ev c
    rw [map_smul, smul_eq_mul, mul_assoc, hunit, mul_one]

end AtiyahSinger
