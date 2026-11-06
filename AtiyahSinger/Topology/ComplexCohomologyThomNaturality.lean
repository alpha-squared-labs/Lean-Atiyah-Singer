/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyProperFunctoriality
public import AtiyahSinger.Topology.CohomologyThomNaturality
public import AtiyahSinger.Topology.ComplexBundleCohomologyThom
public import AtiyahSinger.Topology.ComplexCohomologyOrientationNaturality

/-!
# Naturality of the original complex compact-support Thom maps

Public module ID: M1704.

Actual complex fiber equivalences over a base map preserve the canonically
oriented Thom map, whenever their actual map of total spaces is proper. The
native real Thom naturality is transported through the same identity-on-vectors
homeomorphisms used in the original definition. The fiber integral is the inverse
of precisely this map and consequently has the corresponding naturality.

Source: Milnor--Stasheff, sections 9 and 14, oriented Thom naturality.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

universe u

variable {X Y : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : Y → Type u} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F)
  (r : ℕ) (hrE : ∀ x, Module.finrank ℂ (E x) = r)
  (hrF : ∀ y, Module.finrank ℂ (F y) = r)
  (f : C(X, Y)) (e : ∀ x, E x ≃ₗ[ℂ] F (f x))
  (g : C(TotalSpace Unit E, TotalSpace Unit F))
  (hg : ∀ z, g z = ⟨f z.proj, e z.proj z.snd⟩) (hgProper : IsProperMap g)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
omit [T2Space X] [T2Space Y] in
include hg in
/-- Proper complex bundle maps preserve the specified canonically oriented Thom multiplication. -/
theorem complexCohomologyThomMap_pullback (p : ℕ) (a : singularCohomology ℚ Y p) :
    compactSupportCohomologyProperPullback ℚ g hgProper (p + 2 * r)
        (hF.complexCohomologyThomMap r hrF p a) =
      hE.complexCohomologyThomMap r hrE p (singularCohomologyPullback ℚ f p a) := by
  let : ∀ x, NormedAddCommGroup (E x) := hE.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := hE.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := hE.realFiberInnerProductSpace
  let : ∀ y, NormedAddCommGroup (F y) := hF.fiberNormedAddCommGroup
  let : ∀ y, InnerProductSpace ℂ (F y) := hF.fiberInnerProductSpace
  let : ∀ y, InnerProductSpace ℝ (F y) := hF.realFiberInnerProductSpace
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let : ∀ y, FiniteDimensional ℂ (F y) := fun y ↦ finite_fiber (E := F) y
  let V := EuclideanSpace ℝ (Fin (2 * r))
  let := nativeModelTopology E V
  let := hE.realNativeFiberBundle r hrE
  let := hE.realNativeVectorBundle r hrE
  let := hE.realNativeRiemannianBundle r hrE
  let := nativeModelTopology F V
  let := hF.realNativeFiberBundle r hrF
  let := hF.realNativeVectorBundle r hrF
  let := hF.realNativeRiemannianBundle r hrF
  let HE := nativeModelTotalHomeomorph E V
  let HF := nativeModelTotalHomeomorph F V
  let he : C(TotalSpace V E, TotalSpace Unit E) := ⟨HE, HE.continuous⟩
  let hf : C(TotalSpace V F, TotalSpace Unit F) := ⟨HF, HF.continuous⟩
  let G : C(TotalSpace V E, TotalSpace V F) :=
    (⟨HF.symm, HF.symm.continuous⟩ : C(_, _)).comp (g.comp he)
  have hGProper : IsProperMap G := HF.symm.isProperMap.comp (hgProper.comp HE.isProperMap)
  let eC (x : X) : E x ≃L[ℂ] F (f x) := (e x).toContinuousLinearEquiv
  let eR (x : X) : E x ≃L[ℝ] F (f x) :=
    { (e x).restrictScalars ℝ with
      continuous_toFun := (eC x).continuous
      continuous_invFun := (eC x).symm.continuous }
  have hG (x : X) : G.comp (bundleFiberInclusion (2 * r) E x) =
      (bundleFiberInclusion (2 * r) F (f x)).comp ⟨eR x, (eR x).continuous⟩ := by
    apply ContinuousMap.ext
    intro v
    exact congrArg HF.symm (hg ⟨x, v⟩)
  have hN : Set.MapsTo G (bundleNonzero (2 * r) E) (bundleNonzero (2 * r) F) := by
    rintro ⟨x, v⟩ hv
    have hz : G ⟨x, v⟩ = ⟨f x, eR x v⟩ :=
      congrArg (fun t ↦ t v) (hG x)
    change (G ⟨x, v⟩).snd ≠ 0
    rw [hz]
    exact fun hzero ↦ hv ((eR x).injective (hzero.trans (eR x).map_zero.symm))
  let oE := (hE.complexCohomologyOrientation r hrE).rationalization
  let oF := (hF.complexCohomologyOrientation r hrF).rationalization
  -- The native map preserves the original fiber generators, not merely an unspecified orientation.
  have ho (x : X) : relativeSingularCohomologyPullback ℚ
      (⟨eR x, (eR x).continuous⟩ : C(E x, F (f x)))
      (show Set.MapsTo (eR x) {v : E x | v ≠ 0} {v : F (f x) | v ≠ 0} from
        fun _ hv hz ↦ hv ((eR x).injective (hz.trans (eR x).map_zero.symm))) (2 * r)
      (oF.fiberClass (f x)) = oE.fiberClass x :=
    complexCohomologyOrientation_fiberClass_pullback hE hF r hrE hrF x (f x) (eC x)
  have hnat := cohomologyZeroSectionPushforward_pullback ℚ (2 * r) E F oE oF
    f G hN eR hG ho hGProper p a
  -- The original and native proper pullbacks commute through the same two total homeomorphisms.
  have hsquare (b : compactSupportCohomology ℚ (TotalSpace Unit F) (p + 2 * r)) :
      compactSupportCohomologyHomeomorphPullback ℚ HE (p + 2 * r)
        (compactSupportCohomologyProperPullback ℚ g hgProper (p + 2 * r) b) =
      compactSupportCohomologyProperPullback ℚ G hGProper (p + 2 * r)
        (compactSupportCohomologyHomeomorphPullback ℚ HF (p + 2 * r) b) := by
    rw [← compactSupportCohomologyProperPullback_homeomorph,
      ← compactSupportCohomologyProperPullback_homeomorph,
      ← compactSupportCohomologyProperPullback_comp,
      ← compactSupportCohomologyProperPullback_comp]
    rfl
  let IE := compactSupportCohomologyHomeomorphEquiv ℚ HE (p + 2 * r)
  let IF := compactSupportCohomologyHomeomorphEquiv ℚ HF (p + 2 * r)
  apply IE.injective
  change IE (compactSupportCohomologyProperPullback ℚ g hgProper (p + 2 * r)
    (IF.symm (cohomologyZeroSectionPushforward ℚ (2 * r) F oF p a))) =
    IE (IE.symm (cohomologyZeroSectionPushforward ℚ (2 * r) E oE p
      (singularCohomologyPullback ℚ f p a)))
  rw [IE.apply_symm_apply]
  rw [show IE (compactSupportCohomologyProperPullback ℚ g hgProper (p + 2 * r)
      (IF.symm (cohomologyZeroSectionPushforward ℚ (2 * r) F oF p a))) =
      compactSupportCohomologyProperPullback ℚ G hGProper (p + 2 * r)
        (IF (IF.symm (cohomologyZeroSectionPushforward ℚ (2 * r) F oF p a))) from hsquare _]
  rw [IF.apply_symm_apply]
  exact hnat

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hg in
/-- The original complex Thom inverse is natural under the same proper complex bundle map. -/
theorem complexCohomologyFiberIntegral_pullback (p : ℕ)
    (a : compactSupportCohomology ℚ (TotalSpace Unit F) (p + 2 * r)) :
    hE.complexCohomologyFiberIntegral r hrE p
        (compactSupportCohomologyProperPullback ℚ g hgProper (p + 2 * r) a) =
      singularCohomologyPullback ℚ f p (hF.complexCohomologyFiberIntegral r hrF p a) := by
  -- Recover a by the same original Thom map, use its naturality, then cancel its inverse.
  have h := complexCohomologyThomMap_pullback hE hF r hrE hrF f e g hg hgProper p
    (hF.complexCohomologyFiberIntegral r hrF p a)
  rw [complexCohomologyThomMap_fiberIntegral] at h
  rw [h, complexCohomologyFiberIntegral_thomMap]

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
