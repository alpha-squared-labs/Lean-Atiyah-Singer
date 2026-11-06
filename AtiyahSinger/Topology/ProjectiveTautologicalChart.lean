/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectiveTrivialization
public import AtiyahSinger.Topology.ProjectiveLinearIsometry
public import AtiyahSinger.Topology.ProjectiveTautologicalLine

/-!
# Tautological Chern roots in the same projective chart

Public module ID: M2026.

A projective trivialization obtained by conjugating with a continuous
orthonormal frame identifies the actual tautological range line with the
pullback of the standard projective range line. The line isomorphism applies
that same frame inverse to each vector. Both directions are continuous in the
original total topologies, so the original normalized first Chern classes agree.

This is the local comparison needed for projective Leray--Hirsch. It asserts
neither that theorem nor a cohomology computation for the projective fiber.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open HermitianProjectiveSpace

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianProjectiveTopology hermitianProjectiveLineTopology
  isFiniteRank_hermitianProjectiveLine tautologicalLineTopology isFiniteRank_tautologicalLine
  isFiniteRank_pullback sumTopology sectionModule

variable (t : Trivialization
  (HermitianProjectiveSpace (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore)
  (hermitianProjectiveProjection r E h : HermitianProjectiveBundle r E h → X))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The actual chart fiber coordinate, isometrically lifted to the universe of the original base. -/
def hermitianProjectiveChartFiber :
    C((hermitianProjectiveProjection r E h) ⁻¹' t.baseSet,
      HermitianProjectiveSpace (ULift.{u} (EuclideanSpace ℂ (Fin r)))
        InnerProductSpace.toCore) where
  toFun q := mapLinearIsometryEquiv
    (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ (Fin r))).symm (t q.val).2
  continuous_toFun := by
    have hc : Continuous (fun q : (hermitianProjectiveProjection r E h) ⁻¹' t.baseSet ↦
        t q.val) := t.toOpenPartialHomeomorph.continuousOn.comp_continuous continuous_subtype_val
          (fun q ↦ t.mem_source.mpr q.property)
    exact (mapLinearIsometryEquiv
      (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ (Fin r))).symm).continuous.comp hc.snd

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same orthonormal frame identifies the original local range line with the standard one. -/
def hermitianProjectiveChartLineIso
    (s : ∀ y : X, EuclideanSpace ℂ (Fin r) ≃L[ℂ] E y)
    (hs : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ y u v, (h.toCore y).inner (s y u) (s y v) = inner ℂ u v)
    (hc : ∀ i : Fin r, ContinuousOn
      (fun y ↦ (⟨y, s y (EuclideanSpace.basisFun (Fin r) ℂ i)⟩ :
        TotalSpace (EuclideanSpace ℂ (Fin r)) E)) t.baseSet)
    (ht : ∀ q : HermitianProjectiveBundle r E h,
      (t q).2.val = (s q.1).symm.conjContinuousAlgEquiv q.2.val) :
    Iso ((ContinuousMap.subtypeVal ((hermitianProjectiveProjection r E h) ⁻¹' t.baseSet) :
        ((hermitianProjectiveProjection r E h) ⁻¹' t.baseSet) →
          HermitianProjectiveBundle r E h) *ᵖ (HermitianProjectiveLine r E h))
      ((hermitianProjectiveChartFiber r E h t :
        ((hermitianProjectiveProjection r E h) ⁻¹' t.baseSet) →
          HermitianProjectiveSpace (ULift.{u} (EuclideanSpace ℂ (Fin r)))
            InnerProductSpace.toCore) *ᵖ
        (TautologicalLine (ULift.{u} (EuclideanSpace ℂ (Fin r))))) := by
  classical
  let V := EuclideanSpace ℂ (Fin r)
  let W := ULift.{u} V
  let := modelTopology V E
  let := isFiniteRank_model V E
  let Q := HermitianProjectiveBundle r E h
  let p := hermitianProjectiveProjection r E h
  let D := p ⁻¹' t.baseSet
  let j : C(D, Q) := ContinuousMap.subtypeVal D
  let k := hermitianProjectiveChartFiber r E h t
  let L := HermitianProjectiveLine r E h
  let L₀ := TautologicalLine W
  let G := (j : D → Q) *ᵖ L
  let H := (k : D → HermitianProjectiveSpace W InnerProductSpace.toCore) *ᵖ L₀
  let b₀ := EuclideanSpace.basisFun (Fin r) ℂ
  -- Conjugation, including the explicit universe lift, transports exactly the projector range.
  let a (y : X) : E y ≃L[ℂ] W := (s y).symm.trans ContinuousLinearEquiv.ulift.symm
  have hrange (q : D) :
      (LinearMap.range q.val.2.val.toLinearMap).map (a q.val.1).toLinearEquiv.toLinearMap =
        LinearMap.range (k q).val.toLinearMap := by
    change _ = LinearMap.range
      (ContinuousLinearEquiv.ulift.symm.conjContinuousAlgEquiv (t q.val).2.val).toLinearMap
    rw [ht q.val]
    change _ = LinearMap.range ((a q.val.1).toLinearEquiv.toLinearMap.comp
      (q.val.2.val.toLinearMap.comp (a q.val.1).symm.toLinearEquiv.toLinearMap))
    rw [LinearMap.range_comp, LinearEquiv.range_comp]
  let e (q : D) : G q ≃ₗ[ℂ] H q :=
    (a q.val.1).toLinearEquiv.ofSubmodules _ _ (hrange q)
  have hsource : Continuous (fun z : TotalSpace Unit L ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace Unit ((p : Q → X) *ᵖ E))) :=
    continuous_induced_dom
  have hstandard : Continuous (fun z : TotalSpace Unit L₀ ↦ (z.proj, z.snd.val)) :=
    continuous_induced_dom
  refine { linearEquiv := e, continuous_total := ?_, continuous_symm := ?_ }
  · -- The inverse-frame coordinates are the metric pairings with the same continuous columns.
    let Z := TotalSpace Unit G
    have hb : Continuous (fun z : Z ↦ z.proj) := Pullback.continuous_proj Unit L j
    have hbx : Continuous (fun z : Z ↦ z.proj.val.1) :=
      p.continuous.comp (j.continuous.comp hb)
    have hv : Continuous (fun z : Z ↦ (⟨z.proj.val.1, z.snd.val⟩ : TotalSpace Unit E)) :=
      (Pullback.continuous_lift Unit E p).comp
        (hsource.comp (Pullback.continuous_lift Unit L j))
    have hpair (i : Fin r) : Continuous
        (fun z : Z ↦ (h.toCore z.proj.val.1).inner
          (s z.proj.val.1 (b₀ i)) z.snd.val) := by
      have hcol : Continuous (fun z : Z ↦
          (⟨z.proj.val.1, s z.proj.val.1 (b₀ i)⟩ : TotalSpace Unit E)) :=
        (continuous_unitTotalEquiv_symm V E).comp
          ((hc i).comp_continuous hbx (fun z ↦ z.proj.property))
      have hd : Topology.IsInducing (fun z : TotalSpace Unit (E ×ᵇ E) ↦
          ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit E),
            (⟨z.proj, z.snd.2⟩ : TotalSpace Unit E))) := ⟨rfl⟩
      have hdouble : Continuous (fun z : Z ↦
          (⟨z.proj.val.1, s z.proj.val.1 (b₀ i), z.snd.val⟩ :
            TotalSpace Unit (E ×ᵇ E))) := hd.continuous_iff.mpr (hcol.prodMk hv)
      exact h.continuous_pairing.comp hdouble
    have hcoord (y : X) (v : E y) (i : Fin r) :
        ((s y).symm v) i = (h.toCore y).inner (s y (b₀ i)) v := by
      calc
        ((s y).symm v) i = inner ℂ (b₀ i) ((s y).symm v) :=
          b₀.repr_apply_apply _ _
        _ = (h.toCore y).inner (s y (b₀ i)) v := by
          rw [← hs, ContinuousLinearEquiv.apply_symm_apply]
    have hcoords : Continuous (fun z : Z ↦ (s z.proj.val.1).symm z.snd.val) := by
      apply ((PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℂ)).comp
        (continuous_pi fun i ↦ hpair i)).congr
      intro z
      apply PiLp.ext
      intro i
      exact (hcoord z.proj.val.1 z.snd.val i).symm
    rw [(inducing_pullbackTotalSpaceEmbedding Unit L₀ k).continuous_iff]
    refine hb.prodMk ?_
    apply continuous_induced_rng.mpr
    exact (k.continuous.comp hb).prodMk (continuous_uliftUp.comp hcoords)
  · -- The frame reconstructs each vector as a finite sum of its continuous columns.
    let Z := TotalSpace Unit H
    have hb : Continuous (fun z : Z ↦ z.proj) := Pullback.continuous_proj Unit L₀ k
    let b : C(Z, X) := ⟨fun z ↦ z.proj.val.1,
      p.continuous.comp (j.continuous.comp hb)⟩
    let F := (b : Z → X) *ᵖ E
    have hw : Continuous (fun z : Z ↦ z.snd.val.down) :=
      continuous_uliftDown.comp (hstandard.snd.comp (Pullback.continuous_lift Unit L₀ k))
    have hcol (i : Fin r) : Continuous
        (fun z : Z ↦ (⟨z, s (b z) (b₀ i)⟩ : TotalSpace Unit F)) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E b).continuous_iff]
      exact continuous_id.prodMk ((continuous_unitTotalEquiv_symm V E).comp
        ((hc i).comp_continuous b.continuous (fun z ↦ z.proj.property)))
    let c (i : Fin r) : C(Z, ℂ) := ⟨fun z ↦ z.snd.val.down i,
      (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp hw)⟩
    have hterm (i : Fin r) :
        (fun z : Z ↦ c i z • s (b z) (b₀ i)) ∈ continuousSections F :=
      continuous_smul_section F (c i) (fun z ↦ s (b z) (b₀ i)) (hcol i)
    have hsum (a : Finset (Fin r)) : Continuous (fun z : Z ↦
        (⟨z, ∑ i ∈ a, c i z • s (b z) (b₀ i)⟩ : TotalSpace Unit F)) := by
      induction a using Finset.induction_on with
      | empty =>
        simpa only [Finset.sum_empty] using continuous_zero_section F
      | @insert i a hi ih =>
        simpa only [Finset.sum_insert hi] using continuous_add_section F
          (fun z ↦ c i z • s (b z) (b₀ i))
          (fun z ↦ ∑ j ∈ a, c j z • s (b z) (b₀ j)) (hterm i) ih
    have hsum_eq (z : Z) : ∑ i : Fin r, c i z • s (b z) (b₀ i) =
        s (b z) z.snd.val.down := by
      have h := congrArg (s (b z)) (b₀.sum_repr z.snd.val.down)
      simpa only [map_sum, map_smul, b₀, c, ContinuousMap.coe_mk,
        EuclideanSpace.basisFun_repr] using h
    have hv : Continuous (fun z : Z ↦
        (⟨b z, s (b z) z.snd.val.down⟩ : TotalSpace Unit E)) := by
      have hsum' : Continuous (fun z : Z ↦
          (⟨z, ∑ i : Fin r, c i z • s (b z) (b₀ i)⟩ : TotalSpace Unit F)) := hsum Finset.univ
      have hv := (Pullback.continuous_lift Unit E b).comp hsum'
      exact hv.congr (fun z ↦ congrArg (fun v : E (b z) ↦
        (⟨b z, v⟩ : TotalSpace Unit E)) (hsum_eq z))
    rw [(inducing_pullbackTotalSpaceEmbedding Unit L j).continuous_iff]
    refine hb.prodMk ?_
    apply continuous_induced_rng.mpr
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    exact (j.continuous.comp hb).prodMk hv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalized projective root becomes the standard tautological root in the same chart. -/
theorem hermitianProjectiveChernRoot_restrict_chart
    (s : ∀ y : X, EuclideanSpace ℂ (Fin r) ≃L[ℂ] E y)
    (hs : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ y u v, (h.toCore y).inner (s y u) (s y v) = inner ℂ u v)
    (hc : ∀ i : Fin r, ContinuousOn
      (fun y ↦ (⟨y, s y (EuclideanSpace.basisFun (Fin r) ℂ i)⟩ :
        TotalSpace (EuclideanSpace ℂ (Fin r)) E)) t.baseSet)
    (ht : ∀ q : HermitianProjectiveBundle r E h,
      (t q).2.val = (s q.1).symm.conjContinuousAlgEquiv q.2.val) :
    singularCohomologyPullback ℤ
        (ContinuousMap.subtypeVal ((hermitianProjectiveProjection r E h) ⁻¹' t.baseSet)) 2
        (hermitianProjectiveChernRoot r E h) =
      singularCohomologyPullback ℤ (hermitianProjectiveChartFiber r E h t) 2
        (tautologicalChernRoot (ULift.{u} (EuclideanSpace ℂ (Fin r)))) := by
  let V := EuclideanSpace ℂ (Fin r)
  let W := ULift.{u} V
  let Q := HermitianProjectiveBundle r E h
  let D := (hermitianProjectiveProjection r E h) ⁻¹' t.baseSet
  let j : C(D, Q) := ContinuousMap.subtypeVal D
  let k := hermitianProjectiveChartFiber r E h t
  let L := HermitianProjectiveLine r E h
  let L₀ := TautologicalLine W
  let G := (j : D → Q) *ᵖ L
  let H := (k : D → HermitianProjectiveSpace W InnerProductSpace.toCore) *ᵖ L₀
  let : ∀ q, NormedAddCommGroup (G q) := fun q ↦ (inferInstance : NormedAddCommGroup (L (j q)))
  let : ∀ q, NormedSpace ℂ (G q) := fun q ↦ (inferInstance : NormedSpace ℂ (L (j q)))
  let : ∀ q, NormedAddCommGroup (H q) := fun q ↦ (inferInstance : NormedAddCommGroup (L₀ (k q)))
  let : ∀ q, NormedSpace ℂ (H q) := fun q ↦ (inferInstance : NormedSpace ℂ (L₀ (k q)))
  let hL (q : Q) : Module.finrank ℂ (L q) = 1 := q.2.property.2.1
  let hL₀ (P : HermitianProjectiveSpace W InnerProductSpace.toCore) :
      Module.finrank ℂ (L₀ P) = 1 := P.property.2.1
  -- Naturality and the actual same-frame Iso preserve the original complex Thom sign.
  exact (firstChernClass_pullback L hL j).symm.trans
    ((firstChernClass_eq_of_iso (F := H) G (fun q ↦ hL (j q)) (fun q ↦ hL₀ (k q))
      (hermitianProjectiveChartLineIso r E h t s hs hc ht)).trans
        (firstChernClass_pullback L₀ hL₀ k))

end AtiyahSinger.ComplexBundle
