/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyForgetNaturality
public import AtiyahSinger.Topology.CompactSupportCohomologyProperFunctoriality
public import AtiyahSinger.Topology.ComplexLineEulerComparison

/-!
# Self-intersection for the original complex line Thom map

Public module ID: M1712.

The original compact-support Thom map restricts along its actual zero section
to multiplication by the original normalized first Chern class. The native real
self-intersection formula is transported through the same total-space
homeomorphism, and the canonical orientation comparison fixes its sign.

Source: Milnor--Stasheff, sections 9 and 14, zero-section self-intersection.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restricting the actual complex line Thom image gives cup with its original first Chern class. -/
theorem zeroSectionPullback_complexCohomologyThomMap_line
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (hline : ∀ x, Module.finrank ℂ (E x) = 1)
    (p : ℕ) (a : singularCohomology ℚ X p) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    singularCohomologyPullback ℚ
        (⟨fun x ↦ ⟨x, 0⟩, continuous_zero_section E⟩ : C(X, TotalSpace Unit E)) (p + 2)
        (compactSupportCohomologyToOrdinary ℚ (TotalSpace Unit E) (p + 2)
          (h.complexCohomologyThomMap 1 hline p a)) =
      singularCohomologyCup ℚ X p 2 a
        (singularCohomologyRationalization X 2 (firstChernClass E hline)) := by
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let V := EuclideanSpace ℝ (Fin 2)
  let := nativeModelTopology E V
  let := h.realNativeFiberBundle 1 hline
  let := h.realNativeVectorBundle 1 hline
  let := h.realNativeRiemannianBundle 1 hline
  let o := (h.complexCohomologyOrientation 1 hline).rationalization
  let H := nativeModelTotalHomeomorph E V
  let f : C(TotalSpace V E, TotalSpace Unit E) := ⟨H, H.continuous⟩
  let I := compactSupportCohomologyHomeomorphEquiv ℚ H (p + 2)
  have hforget (b : compactSupportCohomology ℚ (TotalSpace Unit E) (p + 2)) :
      compactSupportCohomologyToOrdinary ℚ (TotalSpace V E) (p + 2) (I b) =
      singularCohomologyPullback ℚ f (p + 2)
        (compactSupportCohomologyToOrdinary ℚ (TotalSpace Unit E) (p + 2) b) := by
    have hn := compactSupportCohomologyProperPullback_toOrdinary ℚ f H.isProperMap (p + 2) b
    rw [compactSupportCohomologyProperPullback_homeomorph] at hn
    exact hn
  have hthom : I (h.complexCohomologyThomMap 1 hline p a) =
      cohomologyZeroSectionPushforward ℚ 2 E o p a := I.apply_symm_apply _
  have hself := zeroSectionPullback_cohomologyZeroSectionPushforward ℚ 2 E o p a
  rw [← hthom, hforget] at hself
  -- Compose the native zero section with the actual native-to-Unit homeomorphism.
  have hcomp (c : singularCohomology ℚ (TotalSpace Unit E) (p + 2)) :
      singularCohomologyPullback ℚ (bundleZeroSection 2 E) (p + 2)
        (singularCohomologyPullback ℚ f (p + 2) c) =
      singularCohomologyPullback ℚ
        (⟨fun x ↦ ⟨x, 0⟩, continuous_zero_section E⟩ : C(X, TotalSpace Unit E)) (p + 2) c := by
    change (((singularCohomologyFunctor ℚ (p + 2)).map _ ≫
      (singularCohomologyFunctor ℚ (p + 2)).map _) c) = _
    rw [← Functor.map_comp]
    rfl
  rw [hcomp] at hself
  exact hself.trans (congrArg (singularCohomologyCup ℚ X p 2 a)
    (cohomologyEulerClass_complex_line h hline))

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
