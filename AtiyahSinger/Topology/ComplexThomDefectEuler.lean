/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyForgetNaturality
public import AtiyahSinger.Topology.CompactSupportCohomologyProperFunctoriality
public import AtiyahSinger.Topology.ComplexThomZeroSectionCharacter
public import AtiyahSinger.Topology.EulerRootProduct

/-!
# The Euler equation for the original complex Thom defect

Public module ID: M1721.

Self-intersection of the original normalized cohomological Thom map and the
actual zero-section character identify the defect times Euler with the exterior
character. The equation holds on the original compact base without any Euler
cancellation assumption. Its homogeneous inclusion keeps all degree transports.

Source: SG III.12, the zero-section equation in the Thom-character calculation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original defect times its canonical Euler class equals the exterior character. -/
theorem complexThomDefectComponent_mul_euler
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (r : ℕ)
    (hr : ∀ x, Module.finrank ℂ (E x) = r) (j : ℕ) :
    singularEvenCohomologyOf ℚ X j (h.complexThomDefectComponent r hr j) *
        singularEvenCohomologyOf ℚ X r (h.complexCohomologyEulerClass r hr) =
      singularEvenCohomologyOf ℚ X (r + j)
        (chernCharacterKZeroComponent X (r + j) (lambdaMinusOne E)) := by
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let V := EuclideanSpace ℝ (Fin (2 * r))
  let := nativeModelTopology E V
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  let := h.realNativeRiemannianBundle r hr
  let o := (h.complexCohomologyOrientation r hr).rationalization
  let H := nativeModelTotalHomeomorph E V
  let f : C(TotalSpace V E, TotalSpace Unit E) := ⟨H, H.continuous⟩
  let i : C(X, TotalSpace Unit E) := ⟨fun x ↦ ⟨x, 0⟩, continuous_zero_section E⟩
  let I := compactSupportCohomologyHomeomorphEquiv ℚ H (2 * j + 2 * r)
  let d := h.complexThomDefectComponent r hr j
  have hforget (b : compactSupportCohomology ℚ (TotalSpace Unit E) (2 * j + 2 * r)) :
      compactSupportCohomologyToOrdinary ℚ (TotalSpace V E) (2 * j + 2 * r) (I b) =
      singularCohomologyPullback ℚ f (2 * j + 2 * r)
        (compactSupportCohomologyToOrdinary ℚ (TotalSpace Unit E) (2 * j + 2 * r) b) := by
    have hn := compactSupportCohomologyProperPullback_toOrdinary ℚ f H.isProperMap
      (2 * j + 2 * r) b
    rw [compactSupportCohomologyProperPullback_homeomorph] at hn
    exact hn
  have hthom : I (h.complexCohomologyThomMap r hr (2 * j) d) =
      cohomologyZeroSectionPushforward ℚ (2 * r) E o (2 * j) d := I.apply_symm_apply _
  have hself := zeroSectionPullback_cohomologyZeroSectionPushforward ℚ (2 * r) E o (2 * j) d
  rw [← hthom, hforget] at hself
  have hcomp (c : singularCohomology ℚ (TotalSpace Unit E) (2 * j + 2 * r)) :
      singularCohomologyPullback ℚ (bundleZeroSection (2 * r) E) (2 * j + 2 * r)
        (singularCohomologyPullback ℚ f (2 * j + 2 * r) c) =
      singularCohomologyPullback ℚ i (2 * j + 2 * r) c := by
    change (((singularCohomologyFunctor ℚ (2 * j + 2 * r)).map _ ≫
      (singularCohomologyFunctor ℚ (2 * j + 2 * r)).map _) c) = _
    rw [← Functor.map_comp]
    rfl
  rw [hcomp] at hself
  let oneK := AtiyahSinger.kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1)
  let t := h.compactSupportChernCharacterComponent r hr (r + j)
    (h.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm oneK))
  let cT {p q : ℕ} (hpq : p = q) : compactSupportCohomology ℚ (TotalSpace Unit E) p →ₗ[ℚ]
      compactSupportCohomology ℚ (TotalSpace Unit E) q :=
    (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit E)) hpq)).hom.hom
  let cH {p q : ℕ} (hpq : p = q) : singularCohomology ℚ X p →ₗ[ℚ]
      singularCohomology ℚ X q :=
    (eqToIso (congrArg (singularCohomology ℚ X) hpq)).hom.hom
  have htransport {p q : ℕ} (hpq : p = q)
      (b : compactSupportCohomology ℚ (TotalSpace Unit E) p) :
      singularCohomologyPullback ℚ i q
        (compactSupportCohomologyToOrdinary ℚ (TotalSpace Unit E) q (cT hpq b)) =
      cH hpq (singularCohomologyPullback ℚ i p
        (compactSupportCohomologyToOrdinary ℚ (TotalSpace Unit E) p b)) := by
    subst q
    rfl
  have ht : h.complexCohomologyThomMap r hr (2 * j) d = cT (by omega) t :=
    h.complexCohomologyThomMap_fiberIntegral r hr (2 * j) _
  rw [ht, htransport (show 2 * (r + j) = 2 * j + 2 * r by omega)] at hself
  have hz := h.zeroSectionPullback_compactSupportChernCharacter_supportedThom_unit r hr (r + j)
  change singularCohomologyPullback ℚ i (2 * (r + j))
    (compactSupportCohomologyToOrdinary ℚ (TotalSpace Unit E) (2 * (r + j)) t) =
      chernCharacterKZeroComponent X (r + j) (lambdaMinusOne E) at hz
  rw [hz] at hself
  -- Include the equality in the even ring only after the original cohomological comparison.
  rw [← singularEvenCohomologyOf_cup]
  change singularEvenCohomologyOf ℚ X (j + r)
    (cH (show 2 * j + 2 * r = 2 * (j + r) by omega)
      (singularCohomologyCup ℚ X (2 * j) (2 * r) d (cohomologyEulerClass ℚ (2 * r) E o))) = _
  rw [← hself]
  have hcast {p q n : ℕ} (hpq : p = q) (hqn : q = n)
      (a : singularCohomology ℚ X p) : cH hqn (cH hpq a) = cH (hpq.trans hqn) a := by
    subst q
    subst n
    rfl
  rw [hcast (show 2 * (r + j) = 2 * j + 2 * r by omega)
    (show 2 * j + 2 * r = 2 * (j + r) by omega)]
  exact singularEvenCohomologyOf_eqToIso ℚ X (Nat.add_comm r j) _

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
