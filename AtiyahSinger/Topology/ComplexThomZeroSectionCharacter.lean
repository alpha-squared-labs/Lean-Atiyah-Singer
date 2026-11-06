/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexThomDefectDefinition
public import AtiyahSinger.Topology.ThomZeroSection

/-!
# The ordinary zero-section character of the exterior Thom symbol

Public module ID: M1723.

The actual supported character restricts to the Chern character of the original
alternating exterior class. This uses the same zero section in supported K-theory
and in singular cohomology; it does not cancel the Euler class or infer supported
equality from ordinary equality.

Source: SG III.12, Lemma 12.3 and the zero-section part of the Thom character argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

universe u

attribute [local instance] t2Space_totalSpace locallyCompactSpace_totalSpace

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction of the original supported Thom character is the character of its exterior class. -/
theorem zeroSectionPullback_compactSupportChernCharacter_supportedThom_unit
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (r : ℕ)
    (hr : ∀ x, Module.finrank ℂ (E x) = r) (k : ℕ) :
    singularCohomologyPullback ℚ
        (⟨fun x ↦ ⟨x, 0⟩, continuous_zero_section E⟩ : C(X, TotalSpace Unit E)) (2 * k)
        (compactSupportCohomologyToOrdinary ℚ (TotalSpace Unit E) (2 * k)
          (h.compactSupportChernCharacterComponent r hr k
            (h.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm
              (AtiyahSinger.kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1)))))) =
      chernCharacterKZeroComponent X k (lambdaMinusOne E) := by
  let i : C(X, TotalSpace Unit E) := ⟨fun x ↦ ⟨x, 0⟩, continuous_zero_section E⟩
  let j : C(TotalSpace Unit E, OnePoint (TotalSpace Unit E)) :=
    ⟨((↑) : TotalSpace Unit E → OnePoint (TotalSpace Unit E)), OnePoint.continuous_coe⟩
  let oneK := AtiyahSinger.kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1)
  let a := (compactSupportKZeroCompactEquiv X).symm oneK
  let τ := h.supportedThomHom a
  -- Finite-point restriction of this exact proper zero-section pullback gives lambdaMinusOne.
  have hK : complexKZeroPullback (j.comp i) τ.val = lambdaMinusOne E := by
    have hz := zeroSectionPullback_supportedThomHom E h a
    change compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback i i.continuous.isProperMap τ) =
        kZeroMul C(X, ℂ) (lambdaMinusOne E) ((compactSupportKZeroCompactEquiv X) a) at hz
    rw [show (compactSupportKZeroCompactEquiv X) a = oneK from
      (compactSupportKZeroCompactEquiv X).apply_symm_apply oneK] at hz
    change compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback i i.continuous.isProperMap τ) = lambdaMinusOne E * 1 at hz
    rw [mul_one] at hz
    change complexKZeroPullback
      ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
        (complexKZeroPullback (properOnePointMap i i.continuous.isProperMap) τ.val) = _ at hz
    simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp] at hz
    exact hz
  -- Both ordinary pullbacks compose to the same finite zero section in the one-point space.
  rw [h.compactSupportChernCharacterComponent_toOrdinary]
  change singularCohomologyPullback ℚ i (2 * k)
    (singularCohomologyPullback ℚ j (2 * k)
      (chernCharacterKZeroComponent (OnePoint (TotalSpace Unit E)) k τ.val)) = _
  have hcomp (c : singularCohomology ℚ (OnePoint (TotalSpace Unit E)) (2 * k)) :
      singularCohomologyPullback ℚ i (2 * k) (singularCohomologyPullback ℚ j (2 * k) c) =
        singularCohomologyPullback ℚ (j.comp i) (2 * k) c := by
    change (((singularCohomologyFunctor ℚ (2 * k)).map _ ≫
      (singularCohomologyFunctor ℚ (2 * k)).map _) c) = _
    rw [← Functor.map_comp]
    rfl
  rw [hcomp, ← chernCharacterKZeroComponent_pullback, hK]

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
