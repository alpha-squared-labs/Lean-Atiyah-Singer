/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectivePullback

/-!
# Tautological line comparisons for the original projective maps

Public module ID: M2027.

The tautological line pulled back along an original flag-line projection is
exactly that original flag range line. The isomorphism keeps each vector;
continuity is checked in both directions in the given induced total topologies.
Consequently the normalized projective first Chern class pulls back to the
normalized class of this same flag line. Native base pullback likewise retains
the original projector range and normalized tautological class.

Source: naturality of the tautological bundle, Hatcher, Vector Bundles and
K-Theory, Sections 1.1 and 3.1. These comparisons do not assert a projective
cohomology computation or a Leray--Hirsch theorem.
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
  hermitianFlagTopology hermitianFlagLineTopology isFiniteRank_hermitianProjectiveLine
  isFiniteRank_hermitianFlagLine isFiniteRank_pullback

/-- An original flag range line is the pullback of the same projective tautological range. -/
def hermitianProjectiveFlagLineIso (i : Fin r) :
    Iso (HermitianFlagLine r E h i)
      ((hermitianFlagLineProjection r E h i :
        HermitianFlagBundle r E h → HermitianProjectiveBundle r E h) *ᵖ
          (HermitianProjectiveLine r E h)) := by
  let V := EuclideanSpace ℂ (Fin r)
  let := modelTopology V E
  let := isFiniteRank_model V E
  let p := hermitianFlagProjection r E h
  let q := hermitianProjectiveProjection r E h
  let f := hermitianFlagLineProjection r E h i
  let L := HermitianProjectiveLine r E h
  have hflag : Continuous (fun z : TotalSpace Unit (HermitianFlagLine r E h i) ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace Unit ((p : _ → X) *ᵖ E))) :=
    continuous_induced_dom
  have hprojective : Continuous (fun z : TotalSpace Unit L ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace Unit ((q : _ → X) *ᵖ E))) :=
    continuous_induced_dom
  refine
    { linearEquiv := fun _ ↦ LinearEquiv.refl ℂ _
      continuous_total := ?_
      continuous_symm := ?_ }
  · -- The flag point and its actual vector give the two coordinates of the pullback topology.
    have hb := (Pullback.continuous_proj Unit E p).comp hflag
    rw [(inducing_pullbackTotalSpaceEmbedding Unit L f).continuous_iff]
    refine hb.prodMk ?_
    apply continuous_induced_rng.mpr
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E q).continuous_iff]
    exact (f.continuous.comp hb).prodMk ((Pullback.continuous_lift Unit E p).comp hflag)
  · -- Conversely forget the projective pullback in the same order, without changing the vector.
    have hb := Pullback.continuous_proj Unit L f
    have hv := (Pullback.continuous_lift Unit E q).comp
      (hprojective.comp (Pullback.continuous_lift Unit L f))
    apply continuous_induced_rng.mpr
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    exact hb.prodMk hv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A flag-line projection pulls the normalized projective root back to its actual flag line. -/
theorem hermitianProjectiveChernRoot_pullback_flagLineProjection (i : Fin r) :
    singularCohomologyPullback ℤ (hermitianFlagLineProjection r E h i) 2
        (hermitianProjectiveChernRoot r E h) =
      firstChernClass (HermitianFlagLine r E h i) (fun p ↦ p.2.property.2.1 i) := by
  let f := hermitianFlagLineProjection r E h i
  let L := HermitianProjectiveLine r E h
  let G := (f : HermitianFlagBundle r E h → HermitianProjectiveBundle r E h) *ᵖ L
  let : ∀ p, NormedAddCommGroup (G p) :=
    fun p ↦ (inferInstance : NormedAddCommGroup (L (f p)))
  let : ∀ p, NormedSpace ℂ (G p) :=
    fun p ↦ (inferInstance : NormedSpace ℂ (L (f p)))
  let hL (q : HermitianProjectiveBundle r E h) : Module.finrank ℂ (L q) = 1 :=
    q.2.property.2.1
  -- Both classes use the same positive complex Thom normalization on the same line vectors.
  have hiso := firstChernClass_eq_of_iso (F := G) (HermitianFlagLine r E h i)
    (fun p ↦ p.2.property.2.1 i) (fun p ↦ hL (f p)) (hermitianProjectiveFlagLineIso r E h i)
  exact ((firstChernClass_pullback L hL f).symm.trans hiso.symm)

section Pullback

variable {Y : Type u} [TopologicalSpace Y] (f : C(Y, X))

local instance : ∀ y : Y, NormedAddCommGroup (((f : Y → X) *ᵖ E) y) :=
  fun y ↦ inferInstanceAs (NormedAddCommGroup (E (f y)))

local instance : ∀ y : Y, NormedSpace ℂ (((f : Y → X) *ᵖ E) y) :=
  fun y ↦ inferInstanceAs (NormedSpace ℂ (E (f y)))

local instance : FiberBundle (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E) :=
  FiberBundle.pullback (F := EuclideanSpace ℂ (Fin r)) (E := E) f

local instance : VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E) :=
  VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin r)) (E := E) f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Native projective pullback preserves the actual tautological line by the identity on vectors. -/
def hermitianProjectivePullbackLineIso :
    Iso (HermitianProjectiveLine r ((f : Y → X) *ᵖ E)
        (hermitianProjectivePullbackMetric r E h f))
      ((hermitianProjectivePullback r E h f :
        HermitianProjectiveBundle r ((f : Y → X) *ᵖ E)
          (hermitianProjectivePullbackMetric r E h f) → HermitianProjectiveBundle r E h) *ᵖ
        (HermitianProjectiveLine r E h)) := by
  let V := EuclideanSpace ℂ (Fin r)
  let G := (f : Y → X) *ᵖ E
  let hG := hermitianProjectivePullbackMetric r E h f
  let p := hermitianProjectiveProjection r G hG
  let q := hermitianProjectiveProjection r E h
  let g := hermitianProjectivePullback r E h f
  let L := HermitianProjectiveLine r E h
  let L' := HermitianProjectiveLine r G hG
  letI := modelTopology V E
  letI := modelTopology V G
  letI := isFiniteRank_model V E
  letI := isFiniteRank_model V G
  have hsource : Continuous (fun z : TotalSpace Unit L' ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace Unit ((p : _ → Y) *ᵖ G))) :=
    continuous_induced_dom
  have htarget : Continuous (fun z : TotalSpace Unit L ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace Unit ((q : _ → X) *ᵖ E))) :=
    continuous_induced_dom
  have hlift : Continuous (fun z : TotalSpace Unit G ↦
      (⟨f z.proj, z.snd⟩ : TotalSpace Unit E)) :=
    (continuous_unitTotalEquiv_symm V E).comp
      ((Pullback.continuous_lift V E f).comp (continuous_unitTotalEquiv V G))
  refine
    { linearEquiv := fun _ ↦ LinearEquiv.refl ℂ _
      continuous_total := ?_
      continuous_symm := ?_ }
  · -- The forward map retains the projective point and lifts the same original vector through f.
    have hb := (Pullback.continuous_proj Unit G p).comp hsource
    have hv := hlift.comp ((Pullback.continuous_lift Unit G p).comp hsource)
    rw [(inducing_pullbackTotalSpaceEmbedding Unit L g).continuous_iff]
    refine hb.prodMk ?_
    apply continuous_induced_rng.mpr
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E q).continuous_iff]
    exact (g.continuous.comp hb).prodMk hv
  · -- The inverse first reconstructs the native pullback vector from its base and original lift.
    have hb := Pullback.continuous_proj Unit L g
    have hvE := (Pullback.continuous_lift Unit E q).comp
      (htarget.comp (Pullback.continuous_lift Unit L g))
    have hvG : Continuous (fun z : TotalSpace Unit ((g : _ → _) *ᵖ L) ↦
        (⟨p z.proj, z.snd.val⟩ : TotalSpace V G)) := by
      rw [(inducing_pullbackTotalSpaceEmbedding V E f).continuous_iff]
      exact (p.continuous.comp hb).prodMk ((continuous_unitTotalEquiv V E).comp hvE)
    apply continuous_induced_rng.mpr
    rw [(inducing_pullbackTotalSpaceEmbedding Unit G p).continuous_iff]
    exact hb.prodMk ((continuous_unitTotalEquiv_symm V G).comp hvG)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalized projective root is natural under the same native projective pullback. -/
theorem hermitianProjectiveChernRoot_pullback :
    singularCohomologyPullback ℤ (hermitianProjectivePullback r E h f) 2
        (hermitianProjectiveChernRoot r E h) =
      hermitianProjectiveChernRoot r ((f : Y → X) *ᵖ E)
        (hermitianProjectivePullbackMetric r E h f) := by
  let G := (f : Y → X) *ᵖ E
  let hG := hermitianProjectivePullbackMetric r E h f
  let g := hermitianProjectivePullback r E h f
  let L := HermitianProjectiveLine r E h
  let L' := HermitianProjectiveLine r G hG
  let T := (g : HermitianProjectiveBundle r G hG → HermitianProjectiveBundle r E h) *ᵖ L
  let : ∀ p, NormedAddCommGroup (T p) :=
    fun p ↦ (inferInstance : NormedAddCommGroup (L (g p)))
  let : ∀ p, NormedSpace ℂ (T p) :=
    fun p ↦ (inferInstance : NormedSpace ℂ (L (g p)))
  let hL (p : HermitianProjectiveBundle r E h) : Module.finrank ℂ (L p) = 1 :=
    p.2.property.2.1
  -- The same line isomorphism compares the normalized classes before applying naturality.
  have hiso := firstChernClass_eq_of_iso (F := T) L' (fun p ↦ p.2.property.2.1)
    (fun p ↦ hL (g p)) (hermitianProjectivePullbackLineIso r E h f)
  exact (firstChernClass_pullback L hL g).symm.trans hiso.symm

end Pullback

end AtiyahSinger.ComplexBundle
