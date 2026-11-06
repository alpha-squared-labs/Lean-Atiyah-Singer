/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCharacterNaturality
public import AtiyahSinger.Topology.ComplexCohomologyThomNaturality
public import AtiyahSinger.Topology.ComplexThomDefectDefinition
public import AtiyahSinger.Topology.ThomNaturality

/-!
# Naturality of the original complex Thom defect

Public module ID: M1722.

An actual isomorphism to the pullback bundle gives naturality of the defect
without any characteristic formula as an assumption. The K Thom symbol, its
supported character, and the canonically oriented cohomological integral all
use the same actual map of total spaces. Compactness makes the base map proper.

Source: SG III.12, the natural characteristic defect of the exterior Thom symbol.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory OnePoint

universe u

attribute [local instance] t2Space_totalSpace locallyCompactSpace_totalSpace isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original defect pulls back along an actual isomorphism to the specified pullback bundle. -/
theorem complexThomDefectComponent_eq_pullback_of_iso
    {X Y : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    {F : Y → Type u} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F)
    (r : ℕ) (hrE : ∀ x, Module.finrank ℂ (E x) = r)
    (hrF : ∀ y, Module.finrank ℂ (F y) = r)
    (f : C(X, Y)) (e : Iso E ((f : X → Y) *ᵖ F)) (k : ℕ) :
    hE.complexThomDefectComponent r hrE k =
      singularCohomologyPullback ℚ f (2 * k) (hF.complexThomDefectComponent r hrF k) := by
  let one (Z : Type u) [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] :
      CompactSupportKZero Z := (compactSupportKZeroCompactEquiv Z).symm
        (AtiyahSinger.kZeroClass C(Z, ℂ) (IdempotentMatrix.identity C(Z, ℂ) 1))
  have hf : IsProperMap f := f.continuous.isProperMap
  have hunit : compactSupportKZeroPullback f hf (one Y) = one X := by
    -- The compact-base equivalence is the original finite-point restriction.
    have hfinite (a : CompactSupportKZero Y) :
        compactSupportKZeroToAbsolute (compactSupportKZeroPullback f hf a) =
          complexKZeroPullback f (compactSupportKZeroToAbsolute a) := by
      change complexKZeroPullback
        ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
          (complexKZeroPullback (properOnePointMap f hf) a.val) =
        complexKZeroPullback f (complexKZeroPullback
          ⟨((↑) : Y → OnePoint Y), OnePoint.continuous_coe⟩ a.val)
      simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
      rfl
    apply (compactSupportKZeroCompactEquiv X).injective
    change compactSupportKZeroToAbsolute (compactSupportKZeroPullback f hf (one Y)) =
      (compactSupportKZeroCompactEquiv X) (one X)
    rw [hfinite]
    change complexKZeroPullback f ((compactSupportKZeroCompactEquiv Y) (one Y)) =
      (compactSupportKZeroCompactEquiv X) (one X)
    simp only [one, AddEquiv.apply_symm_apply]
    change kZeroMap _ (AtiyahSinger.kZeroClass _ _) = _
    rw [kZeroMap_class]
    congr 1
    dsimp only [IdempotentMatrix.map, IdempotentMatrix.identity]
    congr 1
    exact map_one _
  let P := (f : X → Y) *ᵖ F
  let hP := hF.pullback f
  let j : C(TotalSpace Unit E, TotalSpace Unit P) :=
    ⟨e.totalHomeomorph, e.totalHomeomorph.continuous⟩
  let q := pullbackTotalMap F f
  have hq : IsProperMap q := (pullbackTotalMap_properties F f).1 hf
  let g := q.comp j
  have hg : IsProperMap g := hq.comp e.totalHomeomorph.isProperMap
  have hbase : hP.supportedThomHom (one X) =
      compactSupportKZeroPullback q hq (hF.supportedThomHom (one Y)) := by
    have ht := DFunLike.congr_fun (hF.supportedThomHom_pullback f hf) (one Y)
    change hP.supportedThomHom (compactSupportKZeroPullback f hf (one Y)) = _ at ht
    rwa [hunit] at ht
  have hiso : compactSupportKZeroPullback j e.totalHomeomorph.isProperMap
      (hP.supportedThomHom (one X)) = hE.supportedThomHom (one X) :=
    DFunLike.congr_fun (supportedThomHom_iso hP hE e.symm) (one X)
  have hK : compactSupportKZeroPullback g hg (hF.supportedThomHom (one Y)) =
      hE.supportedThomHom (one X) := by
    rw [compactSupportKZeroPullback_comp j q e.totalHomeomorph.isProperMap hq,
      AddMonoidHom.comp_apply, ← hbase]
    exact hiso
  -- The same map is complex linear on every original fiber; arbitrary supplied metrics are allowed.
  have hgvalue (z : TotalSpace Unit E) :
      g z = ⟨f z.proj, e.linearEquiv z.proj z.snd⟩ := rfl
  have hcast {m n : ℕ} (hmn : m = n)
      (a : compactSupportCohomology ℚ (TotalSpace Unit F) m) :
      (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit E)) hmn)).hom
        (compactSupportCohomologyProperPullback ℚ g hg m a) =
      compactSupportCohomologyProperPullback ℚ g hg n
        ((eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit F)) hmn)).hom a) := by
    subst n
    rfl
  unfold complexThomDefectComponent
  change hE.complexCohomologyFiberIntegral r hrE (2 * k)
    ((eqToIso (by congr 1; omega) :
      compactSupportCohomology ℚ (TotalSpace Unit E) (2 * (r + k)) ≅
        compactSupportCohomology ℚ (TotalSpace Unit E) (2 * k + 2 * r)).hom
      (hE.compactSupportChernCharacterComponent r hrE (r + k)
        (hE.supportedThomHom (one X)))) = _
  rw [← hK, compactSupportChernCharacterComponent_pullback hE hF r r hrE hrF g hg]
  rw [hcast (by omega)]
  -- Character naturality and the native complex Thom inverse use this exact same g.
  exact complexCohomologyFiberIntegral_pullback hE hF r hrE hrF f e.linearEquiv g hgvalue hg
    (2 * k) _

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
