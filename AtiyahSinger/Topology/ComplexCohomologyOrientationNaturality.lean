/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexBundleRealOrientation
public import AtiyahSinger.Topology.RationalCohomologyOrientation

/-!
# Naturality of the canonical complex cohomological orientation

Public module ID: M1701.

An actual complex linear fiber equivalence preserves the specified rational
fiber generator. Interleaving a transported complex basis gives the transported
real basis, so the original geometric orientation is preserved integrally.
Actual coefficient naturality then gives the rational statement needed for Thom
naturality. No global Thom identity or equality of supplied metrics is assumed.

Source: Milnor--Stasheff, section 14, canonical orientation of complex bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : Y → Type u} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F)
  (r : ℕ) (hrE : ∀ x, Module.finrank ℂ (E x) = r)
  (hrF : ∀ y, Module.finrank ℂ (F y) = r)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Complex fiber equivalences preserve the original rationalized complex orientation classes. -/
theorem complexCohomologyOrientation_fiberClass_pullback (x : X) (y : Y) :
    letI : ∀ x, NormedAddCommGroup (E x) := hE.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := hE.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := hE.realFiberInnerProductSpace
    letI : ∀ y, NormedAddCommGroup (F y) := hF.fiberNormedAddCommGroup
    letI : ∀ y, InnerProductSpace ℂ (F y) := hF.fiberInnerProductSpace
    letI : ∀ y, InnerProductSpace ℝ (F y) := hF.realFiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
    letI := hE.realNativeFiberBundle r hrE
    letI := hE.realNativeVectorBundle r hrE
    letI := nativeModelTopology F (EuclideanSpace ℝ (Fin (2 * r)))
    letI := hF.realNativeFiberBundle r hrF
    letI := hF.realNativeVectorBundle r hrF
    ∀ e : E x ≃L[ℂ] F y,
      relativeSingularCohomologyPullback ℚ (⟨e, e.continuous⟩ : C(E x, F y))
        (show Set.MapsTo e {v : E x | v ≠ 0} {v : F y | v ≠ 0} from
          fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))) (2 * r)
        ((hF.complexCohomologyOrientation r hrF).rationalization.fiberClass y) =
      (hE.complexCohomologyOrientation r hrE).rationalization.fiberClass x := by
  classical
  let : ∀ x, NormedAddCommGroup (E x) := hE.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := hE.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := hE.realFiberInnerProductSpace
  let : ∀ y, NormedAddCommGroup (F y) := hF.fiberNormedAddCommGroup
  let : ∀ y, InnerProductSpace ℂ (F y) := hF.fiberInnerProductSpace
  let : ∀ y, InnerProductSpace ℝ (F y) := hF.realFiberInnerProductSpace
  let := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  let := hE.realNativeFiberBundle r hrE
  let := hE.realNativeVectorBundle r hrE
  let := nativeModelTopology F (EuclideanSpace ℝ (Fin (2 * r)))
  let := hF.realNativeFiberBundle r hrF
  let := hF.realNativeVectorBundle r hrF
  intro e
  let : FiniteDimensional ℂ (E x) := finite_fiber (E := E) x
  let b := Module.finBasisOfFinrankEq ℂ (E x) (hrE x)
  let c := b.map e.toLinearEquiv
  let eR : E x ≃L[ℝ] F y :=
    { e.toLinearEquiv.restrictScalars ℝ with
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  let oE := hE.complexCohomologyOrientation r hrE
  let oF := hF.complexCohomologyOrientation r hrF
  -- Transport the actual complex frame, then interleave its real and imaginary columns.
  have hmap : (complexBasisRealification b).map eR.toLinearEquiv =
      complexBasisRealification c := by
    apply DFunLike.ext
    intro i
    simp only [Module.Basis.map_apply, complexBasisRealification, Module.Basis.reindex_apply,
      Module.Basis.smulTower'_apply,
      eR, LinearEquiv.restrictScalars_apply, c]
    rw [map_smul]
  have horientation : Orientation.map (Fin (2 * r)) eR.toLinearEquiv
      (hE.complexRealOrientation r hrE x) = hF.complexRealOrientation r hrF y := by
    rw [← hE.complexRealOrientation_basis r hrE x b,
      ← Module.Basis.orientation_map, hmap, hF.complexRealOrientation_basis r hrF y c]
  have hEx : oE.fiberClass x =
      realOrientationClass (complexBasisRealification b) (hE.complexRealOrientation r hrE x) :=
    geometricCohomologyOrientation_fiberClass (2 * r) E
      (hE.complexRealOrientation r hrE) (hE.complexRealOrientation_locally_compatible r hrE)
      x (complexBasisRealification b)
  have hFy : oF.fiberClass y =
      realOrientationClass (complexBasisRealification c) (hF.complexRealOrientation r hrF y) :=
    geometricCohomologyOrientation_fiberClass (2 * r) F
      (hF.complexRealOrientation r hrF) (hF.complexRealOrientation_locally_compatible r hrF)
      y (complexBasisRealification c)
  let f : C(E x, F y) := ⟨e, e.continuous⟩
  have hf : Set.MapsTo f {v : E x | v ≠ 0} {v : F y | v ≠ 0} :=
    fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))
  have hint : relativeSingularCohomologyPullback ℤ f hf (2 * r) (oF.fiberClass y) =
      oE.fiberClass x := by
    rw [hFy, hEx]
    exact realOrientationClass_pullback (complexBasisRealification b)
      (hE.complexRealOrientation r hrE x) (complexBasisRealification c)
      (hF.complexRealOrientation r hrF y) eR horientation
  -- Rationalize that integral normalization through the same relative pair map.
  exact (relativeSingularCohomologyRationalization_naturality f hf (2 * r)
    (oF.fiberClass y)).symm.trans (congrArg
      (relativeSingularCohomologyRationalization {v : E x | v ≠ 0} (2 * r)) hint)

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
