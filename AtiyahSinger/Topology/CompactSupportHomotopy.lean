/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportKZero
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Proper homotopies and compactly supported pullback

Public module ID: M1675.

D07/K02. Properness is required for the whole cylinder map. Proper time slices
alone do not give a homotopy of the one-point compactifications. The uniform
compact-control condition is stated explicitly and compared with properness.
Sources: SG I.9.26; Karoubi II.4. The continuity and functoriality details below
are project supplements to the standard one-point definition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

open scoped unitInterval

/-- Extend a continuous homotopy pointwise by infinity, before proving continuity. -/
def onePointHomotopyMap {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    I × OnePoint X → OnePoint Y :=
  fun z ↦ z.2.elim ∞ (fun x ↦ (H (z.1, x) : OnePoint Y))

variable [hXL : LocallyCompactSpace X] [hXT : T2Space X]
  [hYL : LocallyCompactSpace Y] [hYT : T2Space Y]

include hXL hXT hYL hYT

set_option linter.unusedSectionVars false in
/-- Cylinder properness is exactly uniform compact control of inverse images. -/
theorem isProperMap_homotopy_iff {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    IsProperMap H ↔ ∀ K : Set Y, IsCompact K →
      ∃ L : Set X, IsCompact L ∧ ∀ t : I, ∀ x : X, H (t, x) ∈ K → x ∈ L := by
  /- A proper cylinder map has compact inverse images; their projections into X
  give the required uniform control. Conversely, each compact inverse image is a
  closed subset of I × L, which is compact. For locally compact Hausdorff spaces
  this compact-preimage property for a continuous map implies properness. -/
  constructor
  · intro hH K hK
    -- One compact projection controls every time slice simultaneously.
    refine ⟨Prod.snd '' (H ⁻¹' K), (hH.isCompact_preimage hK).image continuous_snd, ?_⟩
    intro t x hx
    exact ⟨(t, x), hx, rfl⟩
  · intro h
    apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨H.continuous, ?_⟩
    intro K hK
    obtain ⟨L, hL, hcontrol⟩ := h K hK
    -- The whole inverse image is closed inside the compact cylinder I × L.
    apply (isCompact_univ.prod hL).of_isClosed_subset (hK.isClosed.preimage H.continuous)
    intro z hz
    exact ⟨Set.mem_univ z.1, hcontrol z.1 z.2 hz⟩

omit hXL hXT hYL hYT in
/-- Each slice of a proper homotopy is proper. -/
theorem isProperMap_homotopy_eval {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (hH : IsProperMap H) (t : I) : IsProperMap (fun x ↦ H (t, x)) := by
  /- The fixed-time inclusion X → I × X is a closed embedding and is proper.
  Compose it with the proper cylinder map to obtain properness of the time slice. -/
  have hi : IsProperMap (fun x : X ↦ (t, x)) :=
    isProperMap_of_isClosedMap_of_inj (continuous_const.prodMk continuous_id)
      (fun _ _ h ↦ congrArg Prod.snd h) (isClosedMap_prodMk_left t)
  exact hH.comp hi

set_option linter.unusedSectionVars false in
/-- Uniform control makes the extension jointly continuous at infinity. -/
theorem continuous_onePointHomotopyMap {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (hH : IsProperMap H) : Continuous (onePointHomotopyMap H) := by
  /- Continuity at finite points follows from H. For a compact subset of Y,
  cylinder properness gives one compact subset of X containing its inverse images
  for all times. Outside this set every slice avoids that target compact set,
  establishing joint continuity along the entire interval at infinity. -/
  classical
  let e : I × X → I × OnePoint X := Prod.map id ((↑) : X → OnePoint X)
  have he : Continuous e := continuous_id.prodMap OnePoint.continuous_coe
  apply continuous_def.mpr
  intro s hs
  by_cases hinfty : (∞ : OnePoint Y) ∈ s
  · -- Whole-cylinder properness makes the omitted finite preimage compact, uniformly in time.
    have hK := (OnePoint.isOpen_iff_of_mem hinfty).mp hs
    have hcompact : IsCompact (e '' (H ⁻¹' (((↑) : Y → OnePoint Y) ⁻¹' s)ᶜ)) :=
      (hH.isCompact_preimage hK.2).image he
    have hpre : onePointHomotopyMap H ⁻¹' s =
        (e '' (H ⁻¹' (((↑) : Y → OnePoint Y) ⁻¹' s)ᶜ))ᶜ := by
      ext z
      rcases z with ⟨t, z⟩
      cases z using OnePoint.rec <;> simp [onePointHomotopyMap, e, hinfty]
    rw [hpre]
    exact hcompact.isClosed.isOpen_compl
  · -- Away from infinity, the original joint map is transported through an open embedding.
    have hfinite := (OnePoint.isOpen_iff_of_notMem hinfty).mp hs
    have hpre : onePointHomotopyMap H ⁻¹' s =
        e '' (H ⁻¹' (((↑) : Y → OnePoint Y) ⁻¹' s)) := by
      ext z
      rcases z with ⟨t, z⟩
      cases z using OnePoint.rec <;> simp [onePointHomotopyMap, e, hinfty]
    rw [hpre]
    exact (IsOpenMap.id.prodMap OnePoint.isOpenMap_coe) _ (hfinite.preimage H.continuous)

omit hXL hXT hYL hYT in
/-- The extended homotopy has the extended initial map. -/
theorem onePointHomotopyMap_zero {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (x : OnePoint X) : onePointHomotopyMap H (0, x) = OnePoint.map f x := by
  /- Split x into infinity and an ordinary point. Infinity is fixed by both
  formulas; at an ordinary point the equation is the initial endpoint equation of H. -/
  cases x using OnePoint.rec with
  | infty => rfl
  | coe x =>
    change (H (0, x) : OnePoint Y) = (f x : OnePoint Y)
    rw [H.apply_zero]

omit hXL hXT hYL hYT in
/-- The extended homotopy has the extended terminal map. -/
theorem onePointHomotopyMap_one {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (x : OnePoint X) : onePointHomotopyMap H (1, x) = OnePoint.map g x := by
  /- At infinity both maps equal infinity. At a finite point evaluate the
  endpoint equation H(1,x)=g(x) and include its value in the compactification. -/
  cases x using OnePoint.rec with
  | infty => rfl
  | coe x =>
    change (H (1, x) : OnePoint Y) = (g x : OnePoint Y)
    rw [H.apply_one]

/-- A proper cylinder gives an actual homotopy of compactifications. -/
def properOnePointHomotopy {f g : C(X, Y)} (hf : IsProperMap f) (hg : IsProperMap g)
    (H : ContinuousMap.Homotopy f g) (hH : IsProperMap H) :
    ContinuousMap.Homotopy (properOnePointMap f hf) (properOnePointMap g hg) where
  toFun := onePointHomotopyMap H
  continuous_toFun := continuous_onePointHomotopyMap H hH
  map_zero_left := onePointHomotopyMap_zero H
  map_one_left := onePointHomotopyMap_one H

/-- The extended proper homotopy fixes infinity at every time. -/
theorem properOnePointHomotopy_infty {f g : C(X, Y)} (hf : IsProperMap f) (hg : IsProperMap g)
    (H : ContinuousMap.Homotopy f g) (hH : IsProperMap H) (t : I) :
    properOnePointHomotopy hf hg H hH (t, ∞) = ∞ := by
  /- Evaluate the actual pointwise extension at infinity. The defining eliminator
  selects infinity independently of time, so the homotopy stays pointed throughout. -/
  rfl

/-- Proper homotopies induce equal compactly supported pullbacks. -/
theorem compactSupportKZeroPullback_eq_of_proper_homotopy {f g : C(X, Y)}
    (hf : IsProperMap f) (hg : IsProperMap g) (H : ContinuousMap.Homotopy f g)
    (hH : IsProperMap H) :
    compactSupportKZeroPullback f hf = compactSupportKZeroPullback g hg := by
  /- Use the actual proper homotopy of compactifications. Absolute K⁰ homotopy
  invariance applies to the compact Hausdorff compactifications. Restrict that
  equality to the basepoint evaluation kernels and use subtype extensionality. -/
  have h := complexKZeroPullback_eq_of_homotopy
    (properOnePointMap f hf) (properOnePointMap g hg) (properOnePointHomotopy hf hg H hH)
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  exact DFunLike.congr_fun h a.val

omit hYL hYT in
/-- Identity proper pullback is identity. -/
theorem compactSupportKZeroPullback_id :
    compactSupportKZeroPullback (ContinuousMap.id X) isProperMap_id =
      AddMonoidHom.id (CompactSupportKZero X) := by
  /- The one-point extension of the identity is identity at finite points and
  infinity. Its precomposition on functions and induced reduced K₀ map are identity. -/
  have hid : properOnePointMap (ContinuousMap.id X) isProperMap_id =
      ContinuousMap.id (OnePoint X) := by
    ext x
    cases x using OnePoint.rec <;> rfl
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  change complexKZeroPullback (properOnePointMap (ContinuousMap.id X) isProperMap_id) a.val =
    a.val
  rw [hid]
  change kZeroMap (RingHom.id C(OnePoint X, ℂ)) a.val = a.val
  rw [kZeroMap_id]
  rfl

variable [LocallyCompactSpace Z] [T2Space Z]

/-- Proper pullbacks compose contravariantly. -/
theorem compactSupportKZeroPullback_comp (f : C(X, Y)) (g : C(Y, Z))
    (hf : IsProperMap f) (hg : IsProperMap g) :
    compactSupportKZeroPullback (g.comp f) (hg.comp hf) =
      (compactSupportKZeroPullback f hf).comp (compactSupportKZeroPullback g hg) := by
  /- Extensions by infinity commute with composition on every point. Apply
  contravariance of the absolute K₀ map and restrict the equality to reduced classes.
  Properness of the composite follows by composition of proper maps. -/
  have hcomp : properOnePointMap (g.comp f) (hg.comp hf) =
      (properOnePointMap g hg).comp (properOnePointMap f hf) := by
    ext x
    cases x using OnePoint.rec <;> rfl
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  change complexKZeroPullback (properOnePointMap (g.comp f) (hg.comp hf)) a.val =
    complexKZeroPullback (properOnePointMap f hf)
      (complexKZeroPullback (properOnePointMap g hg) a.val)
  rw [hcomp, complexKZeroPullback_comp]
  rfl

end AtiyahSinger
