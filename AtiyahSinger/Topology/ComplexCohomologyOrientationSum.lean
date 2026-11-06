/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexOrientationSumCup
public import AtiyahSinger.Topology.RationalCohomologyOrientation

/-!
# Direct sums of the original complex fiber orientations

Public module ID: M1702.

An actual complex continuous linear identification with an ordered product
carries the relative cup of the two original rational fiber classes to the
original rational fiber class of the sum. The metrics may be independently
supplied: the actual fiber equivalence compares their induced topologies.

Source: Milnor--Stasheff, Sections 9 and 14, normalized Thom classes and
the canonical orientation of a complex direct sum.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

universe u

variable {X : Type u} [TopologicalSpace X]
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
-- The same original metrics induce three native real models and the exact fiber transports.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified complex product preserves the normalized original rational fiber classes. -/
theorem complexCohomologyOrientation_fiberClass_prod (x : X) :
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
    ∀ e : G x ≃L[ℂ] E x × F x,
      let A : Set (E x × F x) := {z | z.1 ≠ 0}
      let B : Set (E x × F x) := {z | z.2 ≠ 0}
      let P : Set (E x × F x) := {z | z ≠ 0}
      ∀ hP : Set.MapsTo (ContinuousMap.id (E x × F x)) P (A ∪ B),
      relativeSingularCohomologyPullback ℚ (⟨e, e.continuous⟩ : C(G x, E x × F x))
        (A := {v | v ≠ 0}) (B := P)
        (fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))) (2 * (n + r))
        (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
          (Nat.mul_add 2 n r).symm)
          (relativeSingularCohomologyPullback ℚ (ContinuousMap.id (E x × F x)) hP
            (2 * n + 2 * r)
            (relativeSingularCohomologyUnionCup ℚ A B
              (isOpen_ne_fun continuous_fst continuous_const)
              (isOpen_ne_fun continuous_snd continuous_const) (2 * n) (2 * r)
              (relativeSingularCohomologyPullback ℚ (ContinuousMap.fst : C(E x × F x, E x))
                (A := A) (B := {v | v ≠ 0}) (fun _ hv ↦ hv) (2 * n)
                ((hE.complexCohomologyOrientation n hrE).rationalization.fiberClass x))
              (relativeSingularCohomologyPullback ℚ (ContinuousMap.snd : C(E x × F x, F x))
                (A := B) (B := {v | v ≠ 0}) (fun _ hv ↦ hv) (2 * r)
                ((hF.complexCohomologyOrientation r hrF).rationalization.fiberClass x))))) =
      (hG.complexCohomologyOrientation (n + r) hrG).rationalization.fiberClass x := by
  classical
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
  intro e
  dsimp only
  intro hP
  let : FiniteDimensional ℂ (E x) := finite_fiber (E := E) x
  let : FiniteDimensional ℂ (F x) := finite_fiber (E := F) x
  let bE := Module.finBasisOfFinrankEq ℂ (E x) (hrE x)
  let bF := Module.finBasisOfFinrankEq ℂ (F x) (hrF x)
  let b := (bE.prod bF).reindex (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r))
  let bG := b.map e.symm.toLinearEquiv
  let oE := hE.complexCohomologyOrientation n hrE
  let oF := hF.complexCohomologyOrientation r hrF
  let oG := hG.complexCohomologyOrientation (n + r) hrG
  -- Each supplied orientation is normalized on precisely this original complex frame.
  have hEclass : oE.fiberClass x = realOrientationClass (complexBasisRealification bE)
      (complexBasisRealification bE).orientation := by
    have h := geometricCohomologyOrientation_fiberClass (2 * n) E
      (hE.complexRealOrientation n hrE) (hE.complexRealOrientation_locally_compatible n hrE)
      x (complexBasisRealification bE)
    rw [← hE.complexRealOrientation_basis n hrE x bE] at h
    exact h
  have hFclass : oF.fiberClass x = realOrientationClass (complexBasisRealification bF)
      (complexBasisRealification bF).orientation := by
    have h := geometricCohomologyOrientation_fiberClass (2 * r) F
      (hF.complexRealOrientation r hrF) (hF.complexRealOrientation_locally_compatible r hrF)
      x (complexBasisRealification bF)
    rw [← hF.complexRealOrientation_basis r hrF x bF] at h
    exact h
  have hGclass : oG.fiberClass x = realOrientationClass (complexBasisRealification bG)
      (complexBasisRealification bG).orientation := by
    have h := geometricCohomologyOrientation_fiberClass (2 * (n + r)) G
      (hG.complexRealOrientation (n + r) hrG)
      (hG.complexRealOrientation_locally_compatible (n + r) hrG)
      x (complexBasisRealification bG)
    rw [← hG.complexRealOrientation_basis (n + r) hrG x bG] at h
    exact h
  let eR : G x ≃L[ℝ] E x × F x :=
    { e.toLinearEquiv.restrictScalars ℝ with
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  have hb : (complexBasisRealification bG).map eR.toLinearEquiv =
      complexBasisRealification b := by
    apply DFunLike.ext
    intro i
    simp only [Module.Basis.map_apply, complexBasisRealification, Module.Basis.reindex_apply,
      Module.Basis.smulTower'_apply, bG, eR, LinearEquiv.restrictScalars_apply]
    rw [map_smul]
    exact congrArg (fun v ↦ Complex.basisOneI
      ((finProdFinEquiv.trans (finCongr (Nat.mul_comm (n + r) 2))).symm i).2 • v)
        (e.apply_symm_apply _)
  have ho : Orientation.map (Fin (2 * (n + r))) eR.toLinearEquiv
      (complexBasisRealification bG).orientation = (complexBasisRealification b).orientation := by
    rw [← Module.Basis.orientation_map, hb]
  -- The exact local product has this positive sum frame, including every rank-zero case.
  have hprod := complexOrientationClass_rationalization_prod bE bF hP
  have hnat := realOrientationClass_pullback (complexBasisRealification bG)
    (complexBasisRealification bG).orientation (complexBasisRealification b)
    (complexBasisRealification b).orientation eR ho
  have hrat := (relativeSingularCohomologyRationalization_naturality
    (⟨eR, eR.continuous⟩ : C(G x, E x × F x))
    (A := {v : G x | v ≠ 0}) (B := {v : E x × F x | v ≠ 0})
    (fun _ hv hz ↦ hv (eR.injective (hz.trans eR.map_zero.symm))) (2 * (n + r))
    (realOrientationClass (complexBasisRealification b)
      (complexBasisRealification b).orientation)).symm.trans
      (congrArg (relativeSingularCohomologyRationalization {v : G x | v ≠ 0} (2 * (n + r)))
        hnat)
  change relativeSingularCohomologyPullback ℚ _ _ _
    (cast _ (relativeSingularCohomologyPullback ℚ _ _ _
      (relativeSingularCohomologyUnionCup ℚ _ _ _ _ _ _
        (relativeSingularCohomologyPullback ℚ _ _ _
          (relativeSingularCohomologyRationalization _ _ (oE.fiberClass x)))
        (relativeSingularCohomologyPullback ℚ _ _ _
          (relativeSingularCohomologyRationalization _ _ (oF.fiberClass x)))))) =
    relativeSingularCohomologyRationalization _ _ (oG.fiberClass x)
  rw [hEclass, hFclass, hGclass]
  exact (congrArg (relativeSingularCohomologyPullback ℚ
    (⟨e, e.continuous⟩ : C(G x, E x × F x))
      (A := {v : G x | v ≠ 0}) (B := {v : E x × F x | v ≠ 0})
      (fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))) (2 * (n + r))) hprod).trans hrat

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
