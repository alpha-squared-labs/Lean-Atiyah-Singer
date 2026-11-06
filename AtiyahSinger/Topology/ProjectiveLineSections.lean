/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ProjectiveLineCoordinates

/-!
# Sections of the original projective bundle from line projections

Public module ID: M2016.

A continuous family of rank-one orthogonal projections defines a section
of the original Hermitian projective bundle. If a specified bundle map
identifies its range with a given line bundle, the tautological first Chern
class restricts to that line's normalized first Chern class.

Source: the tautological line and the projectivization of a line subbundle,
Hatcher, Vector Bundles and K-Theory, Sections 1.1 and 3.1. The comparison
retains the original total topologies and the actual projection and map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianProjectiveTopology hermitianProjectiveLineTopology
  isFiniteRank_hermitianProjectiveLine isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Jointly continuous native linear endomorphisms form a continuous section of the Hom bundle.
This implementation comparison is used to place actual line projections in projective space. -/
theorem continuous_nativeEndomorphismSection (a : ∀ x, E x →L[ℂ] E x)
    (ha : Continuous (fun z : TotalSpace (EuclideanSpace ℂ (Fin r)) E ↦
      (⟨z.proj, a z.proj z.snd⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))) :
    Continuous (fun x ↦ (⟨x, a x⟩ :
      TotalSpace (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
        (fun x ↦ E x →L[ℂ] E x))) := by
  let V := EuclideanSpace ℂ (Fin r)
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
  refine ⟨continuous_id.continuousAt, ?_⟩
  apply continuousAt_clm_apply.mpr
  intro v
  let e := trivializationAt V E x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt V E x
  -- A fixed local model vector gives an actual continuous local section.
  have hv : ContinuousOn (fun y ↦ (⟨y, e.symmL ℂ y v⟩ : TotalSpace V E)) e.baseSet := by
    have hraw := e.continuousOn_symm.comp
      (continuous_id.prodMk (continuous_const (y := v))).continuousOn
      (fun y hy ↦ ⟨hy, Set.mem_univ v⟩)
    apply hraw.congr
    intro y hy
    change (⟨y, e.symmL ℂ y v⟩ : TotalSpace V E) = ⟨y, e.symm y v⟩
    rw [e.symmL_apply hy]
  have hav : ContinuousOn (fun y ↦ (⟨y, a y (e.symmL ℂ y v)⟩ : TotalSpace V E))
      e.baseSet := ha.comp_continuousOn hv
  have hcoord : ContinuousOn (fun y ↦ (e ⟨y, a y (e.symmL ℂ y v)⟩).2) e.baseSet :=
    (e.continuousOn.comp hav (fun y hy ↦ e.mem_source.mpr hy)).snd
  -- These are precisely the matrix coordinates defining the native Hom topology.
  apply (hcoord.continuousAt (e.open_baseSet.mem_nhds hx)).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  change e.continuousLinearMapAt ℂ y (a y (e.symmL ℂ y v)) =
    (e ⟨y, a y (e.symmL ℂ y v)⟩).2
  exact e.continuousLinearMapAt_apply_of_mem ℂ hy _

/-- A continuous family of actual orthogonal line projections gives its projective section. -/
def hermitianProjectiveSection
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ x : X, HermitianProjectiveSpace (E x) (h.toCore x))
    (ha : Continuous (fun x ↦ (⟨x, (a x).val⟩ :
      TotalSpace (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
        (fun x ↦ E x →L[ℂ] E x)))) : C(X, HermitianProjectiveBundle r E h) where
  toFun x := ⟨x, a x⟩
  continuous_toFun := continuous_induced_rng.mpr (continuous_id.prodMk ha)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The tautological line over a projected section is the line identified by its coordinate. -/
def hermitianProjectiveSectionLineIso
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ x : X, HermitianProjectiveSpace (E x) (h.toCore x))
    (ha : Continuous (fun x ↦ (⟨x, (a x).val⟩ :
      TotalSpace (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
        (fun x ↦ E x →L[ℂ] E x))))
    {F : X → Type u} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (b : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      Hom E F)
    (hb : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ x, Function.Bijective
      ((b.linearMap x).comp (LinearMap.range (a x).val.toLinearMap).subtype)) :
    Iso ((hermitianProjectiveSection r E h a ha : X → _) *ᵖ
      (HermitianProjectiveLine r E h)) F := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let Q := HermitianProjectiveBundle r E h
  let L := HermitianProjectiveLine r E h
  let p := hermitianProjectiveProjection r E h
  let s := hermitianProjectiveSection r E h a ha
  let U := (s : X → Q) *ᵖ L
  let : ∀ x, NormedAddCommGroup (U x) :=
    fun x ↦ Submodule.normedAddCommGroup (LinearMap.range (a x).val.toLinearMap)
  let : ∀ x, NormedSpace ℂ (U x) :=
    fun x ↦ SubmoduleClass.toNormedSpace (LinearMap.range (a x).val.toLinearMap)
  -- The original coordinate acts on the actual range of the section's projector.
  let e : Hom U F :=
    { linearMap x := (b.linearMap x).comp (LinearMap.range (a x).val.toLinearMap).subtype
      continuous_total := by
        let inc : TotalSpace Unit L → TotalSpace Unit ((p : Q → X) *ᵖ E) :=
          fun z ↦ ⟨z.proj, z.snd.val⟩
        have hinc : Continuous inc := continuous_induced_dom
        have htotal := b.continuous_total.comp
          ((Pullback.continuous_lift Unit E p).comp
            (hinc.comp (Pullback.continuous_lift Unit L s)))
        exact htotal }
  exact e.toIso hb

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The tautological class restricts to the original line identified by the specified coordinate. -/
theorem hermitianProjectiveChernRoot_pullback_section
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ x : X, HermitianProjectiveSpace (E x) (h.toCore x))
    (ha : Continuous (fun x ↦ (⟨x, (a x).val⟩ :
      TotalSpace (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
        (fun x ↦ E x →L[ℂ] E x))))
    {F : X → Type u} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (hF : ∀ x, Module.finrank ℂ (F x) = 1)
    (b : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      Hom E F)
    (hb : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ x, Function.Bijective
      ((b.linearMap x).comp (LinearMap.range (a x).val.toLinearMap).subtype)) :
    singularCohomologyPullback ℤ (hermitianProjectiveSection r E h a ha) 2
        (hermitianProjectiveChernRoot r E h) = firstChernClass F hF := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let L := HermitianProjectiveLine r E h
  let s := hermitianProjectiveSection r E h a ha
  let U := (s : X → _) *ᵖ L
  let : ∀ x, NormedAddCommGroup (U x) :=
    fun x ↦ Submodule.normedAddCommGroup (LinearMap.range (a x).val.toLinearMap)
  let : ∀ x, NormedSpace ℂ (U x) :=
    fun x ↦ SubmoduleClass.toNormedSpace (LinearMap.range (a x).val.toLinearMap)
  have hline : ∀ x, Module.finrank ℂ (U x) = 1 := fun x ↦ (a x).property.2.1
  -- Naturality and the actual line isomorphism preserve the normalized first Chern class.
  rw [hermitianProjectiveChernRoot]
  exact (firstChernClass_pullback L (fun q ↦ q.2.property.2.1) s).symm.trans
    (firstChernClass_eq_of_iso U hline hF
      (hermitianProjectiveSectionLineIso r E h a ha b hb))

end AtiyahSinger.ComplexBundle
