/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RealOrientationClass
public import AtiyahSinger.Topology.RelativeEvaluationRationalization

/-!
# Rational evaluation on the specified oriented local cycle

Public module ID: M2033.

The actual rationalization of the signed integral orientation cycle freely
generates rational top local homology. Kronecker evaluation on that same cycle
therefore identifies top local cohomology with the rational coefficients.
The sign of a zero-dimensional orientation is retained.

Source: integral local orientation normalization and the universal coefficient
pairing, Hatcher, Algebraic Topology, Sections 3.1 and 3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Rational local cohomology is detected by the rational image of the original signed cycle. -/
theorem rationalRealOrientationEvaluation_bijective {n : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (b : Module.Basis (Fin n) ℝ V)
    (o : Orientation ℝ V (Fin n)) :
    Function.Bijective (fun a : relativeSingularCohomology ℚ {v : V | v ≠ 0} n ↦
      (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ {v : V | v ≠ 0}) n a
        (relativeSingularHomologyRationalization {v : V | v ≠ 0} n
          (realOrientationCycle b o))).down) := by
  let : FiniteDimensional ℝ V := Module.Finite.of_basis b
  let A : Set V := {v | v ≠ 0}
  let e := b.equivFun.toContinuousLinearEquiv
  let f : C(V, ULift.{u} (Fin n → ℝ)) :=
    ⟨fun v ↦ ULift.up (e v), continuous_uliftUp.comp e.continuous⟩
  let g : C(ULift.{u} (Fin n → ℝ), V) :=
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
  let : IsIso (relativeSingularHomologyMap ℚ f hf n) :=
    isIso_relativeSingularHomologyMap_of_inverse ℚ f g hf hg
      (by apply ContinuousMap.ext; intro v; exact e.symm_apply_apply v)
      (by apply ContinuousMap.ext; intro y; exact congrArg ULift.up (e.apply_symm_apply y.down)) n
  let H : ℚ ≃ₗ[ℚ] relativeSingularHomology ℚ A n :=
    (euclideanLocalHomologyEquiv.{u} ℚ n).trans
      (asIso (relativeSingularHomologyMap ℚ f hf n)).symm.toLinearEquiv
  let z := relativeSingularHomologyRationalization A n (realOrientationCycle b o)
  -- The normalization one survives coefficient change on these same two representatives.
  have hz : z ≠ 0 := by
    intro hz
    have hnorm : (singularCochainHomologyEvaluation ℤ (relativeSingularChains ℤ A) n
        (realOrientationClass b o) (realOrientationCycle b o)).down = 1 := by
      rw [← relativeSingularCapProduct_augmentation]
      exact realOrientationClass_evaluation b o
    have hpair := singularCochainHomologyEvaluation_rationalization A n
      (realOrientationClass b o) (realOrientationCycle b o)
    change (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ A) n
      (relativeSingularCohomologyRationalization A n (realOrientationClass b o)) z).down = _
      at hpair
    rw [hz, map_zero, hnorm] at hpair
    norm_num at hpair
  have hscalar : H.symm z ≠ 0 := by
    intro h
    exact hz (H.symm.injective (h.trans (map_zero H.symm).symm))
  have hgen : Function.Bijective (fun t : ℚ ↦ t • z) := by
    constructor
    · intro s t h
      have h' := congrArg H.symm h
      change H.symm (s • z) = H.symm (t • z) at h'
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h'
      exact mul_right_cancel₀ hscalar h'
    · intro c
      refine ⟨H.symm c / H.symm z, H.symm.injective ?_⟩
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hscalar]
  -- Below-dimension vanishing, or n = 0, makes evaluation on this generator bijective.
  have hprev : n = 0 ∨ Subsingleton (relativeSingularHomology ℚ A (n - 1)) := by
    by_cases hn : n = 0
    · exact Or.inl hn
    · exact Or.inr (subsingleton_relativeSingularHomology_below_dim_of_continuousLinearEquiv
        ℚ e (n - 1) (by omega))
  have heval := relativeSingularCapProduct_augmentation_bijective_of_generator ℚ A n z
    hgen hprev
  convert heval using 1
  funext a
  exact (congrArg ULift.down (relativeSingularCapProduct_augmentation ℚ A n a z)).symm

end AtiyahSinger
