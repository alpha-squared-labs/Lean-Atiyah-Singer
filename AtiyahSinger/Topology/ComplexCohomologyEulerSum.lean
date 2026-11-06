/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyEulerSum
public import AtiyahSinger.Topology.ComplexCohomologyOrientationSum
public import AtiyahSinger.Topology.EvenCohomologyPolynomials

/-!
# Euler multiplication for an actual complex direct sum

Public module ID: M1700.

The original complex Euler class of a bundle identified with an ordered direct
sum is the even cup of the two original Euler classes. The identification is
an actual complex bundle isomorphism, and the three metrics may be independent.
The native real total maps retain every original base point and vector.

Source: Milnor--Stasheff, Sections 9 and 14, the Euler class of a complex sum.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

universe u

attribute [local instance] sumTopology

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  {E F G : X → Type u}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]
  (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F)
  (hG : ContinuousHermitianMetric G) (n r : ℕ)
  (hrE : ∀ x, Module.finrank ℂ (E x) = n)
  (hrF : ∀ x, Module.finrank ℂ (F x) = r)
  (hrG : ∀ x, Module.finrank ℂ (G x) = n + r)

set_option maxHeartbeats 1000000 in
-- Three original native models are compared through actual identity-on-vectors total maps.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An actual complex direct-sum isomorphism multiplies the original rational Euler classes. -/
theorem cohomologyEulerClass_complex_prod (j : Iso G (E ×ᵇ F)) :
    letI : ∀ x, NormedAddCommGroup (E x) := hE.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := hE.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := hE.realFiberInnerProductSpace
    letI : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (F x) := hF.realFiberInnerProductSpace
    letI : ∀ x, NormedAddCommGroup (G x) := hG.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (G x) := hG.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (G x) := hG.realFiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * n)))
    letI := hE.realNativeFiberBundle n hrE
    letI := hE.realNativeVectorBundle n hrE
    letI := nativeModelTopology F (EuclideanSpace ℝ (Fin (2 * r)))
    letI := hF.realNativeFiberBundle r hrF
    letI := hF.realNativeVectorBundle r hrF
    letI := nativeModelTopology G (EuclideanSpace ℝ (Fin (2 * (n + r))))
    letI := hG.realNativeFiberBundle (n + r) hrG
    letI := hG.realNativeVectorBundle (n + r) hrG
    cohomologyEulerClass ℚ (2 * (n + r)) G
        (hG.complexCohomologyOrientation (n + r) hrG).rationalization =
      singularCohomologyEvenCup ℚ X n r
        (cohomologyEulerClass ℚ (2 * n) E (hE.complexCohomologyOrientation n hrE).rationalization)
        (cohomologyEulerClass ℚ (2 * r) F
          (hF.complexCohomologyOrientation r hrF).rationalization) := by
  let : ∀ x, NormedAddCommGroup (E x) := hE.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := hE.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := hE.realFiberInnerProductSpace
  let : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (F x) := hF.realFiberInnerProductSpace
  let : ∀ x, NormedAddCommGroup (G x) := hG.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (G x) := hG.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (G x) := hG.realFiberInnerProductSpace
  let := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * n)))
  let := hE.realNativeFiberBundle n hrE
  let := hE.realNativeVectorBundle n hrE
  let := nativeModelTopology F (EuclideanSpace ℝ (Fin (2 * r)))
  let := hF.realNativeFiberBundle r hrF
  let := hF.realNativeVectorBundle r hrF
  let := nativeModelTopology G (EuclideanSpace ℝ (Fin (2 * (n + r))))
  let := hG.realNativeFiberBundle (n + r) hrG
  let := hG.realNativeVectorBundle (n + r) hrG
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦ finite_fiber (E := F) x
  let : ∀ x, FiniteDimensional ℂ (G x) := fun x ↦ finite_fiber (E := G) x
  let TE := TotalSpace (EuclideanSpace ℝ (Fin (2 * n))) E
  let TF := TotalSpace (EuclideanSpace ℝ (Fin (2 * r))) F
  let TG := TotalSpace (EuclideanSpace ℝ (Fin (2 * (n + r)))) G
  let HE := nativeModelTotalHomeomorph E (EuclideanSpace ℝ (Fin (2 * n)))
  let HF := nativeModelTotalHomeomorph F (EuclideanSpace ℝ (Fin (2 * r)))
  let HG := nativeModelTotalHomeomorph G (EuclideanSpace ℝ (Fin (2 * (n + r))))
  -- Compose the original sum projections and original bundle isomorphism through native retyping.
  let qE : C(TG, TE) :=
    ⟨fun z ↦ ⟨z.proj, (j.linearEquiv z.proj z.snd).1⟩,
      HE.symm.continuous.comp ((continuous_sum_fst (E := E) (F := F)).comp
        (j.continuous_total.comp HG.continuous))⟩
  let qF : C(TG, TF) :=
    ⟨fun z ↦ ⟨z.proj, (j.linearEquiv z.proj z.snd).2⟩,
      HF.symm.continuous.comp ((continuous_sum_snd (E := E) (F := F)).comp
        (j.continuous_total.comp HG.continuous))⟩
  let e (x : X) : G x ≃L[ℂ] E x × F x := (j.linearEquiv x).toContinuousLinearEquiv
  let eR (x : X) : G x ≃L[ℝ] E x × F x :=
    { (e x).toLinearEquiv.restrictScalars ℝ with
      continuous_toFun := (e x).continuous
      continuous_invFun := (e x).symm.continuous }
  have h := cohomologyEulerClass_prod_of_fiberClass ℚ (2 * n) (2 * r) (2 * (n + r))
    (Nat.mul_add 2 n r).symm E F G
    (hE.complexCohomologyOrientation n hrE).rationalization
    (hF.complexCohomologyOrientation r hrF).rationalization
    (hG.complexCohomologyOrientation (n + r) hrG).rationalization qE qF eR
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (by
      intro x
      dsimp only
      intro hP
      exact hE.complexCohomologyOrientation_fiberClass_prod hF hG n r hrE hrF hrG x (e x) hP)
  -- The remaining degree equality is precisely the one defining the original even cup product.
  have hcast {A B : ModuleCat.{u} ℚ} (hAB : A = B) (a : A) :
      (eqToIso hAB).hom a = cast (congrArg ModuleCat.carrier hAB) a := by
    subst B
    rfl
  exact h.trans (hcast _ _).symm

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
