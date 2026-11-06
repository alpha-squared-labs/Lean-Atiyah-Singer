/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ChernClass
public import AtiyahSinger.Topology.ComplexLineConjugation
public import AtiyahSinger.Topology.HermitianConjugation
public import AtiyahSinger.Topology.HermitianProjectiveBundle
public import AtiyahSinger.Topology.ProjectiveChernSign

/-!
# Conjugation on the actual Hermitian projective bundle

Public module ID: M1894.

An antiunitary involution conjugates the original orthogonal line projectors.
The induced projective map covers the identity of the base and acts by the same
conjugate-linear map on their actual tautological ranges. This supplies the
projective comparison for self-conjugate Chern classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E] [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)
  (J : ∀ x, E x ≃ₗ⋆[ℂ] E x) (hJ : ∀ x, Function.Involutive (J x))
  (hcontinuous : Continuous (fun z : TotalSpace (EuclideanSpace ℂ (Fin r)) E ↦
    (⟨z.proj, J z.proj z.snd⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)))
  (hunitary : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ x (v w : E x),
      (h.toCore x).inner (J x v) (J x w) = star ((h.toCore x).inner v w))

attribute [local instance] hermitianProjectiveTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Conjugating the actual orthogonal line projector by an antiunitary involution is continuous. -/
def hermitianProjectiveConjugationMap :
    C(HermitianProjectiveBundle r E h, HermitianProjectiveBundle r E h) := by
  classical
  let V := EuclideanSpace ℂ (Fin r)
  let := modelTopology V E
  let := isFiniteRank_model V E
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let Q := HermitianProjectiveBundle r E h
  let A (p : Q) : E p.1 →L[ℂ] E p.1 :=
    (show E p.1 →ₗ[ℂ] E p.1 from
      (J p.1).toLinearMap.comp (p.2.val.toLinearMap.comp (J p.1).toLinearMap)).toContinuousLinearMap
  have hprojector (p : Q) : (A p).comp (A p) = A p ∧
      Module.finrank ℂ (LinearMap.range (A p).toLinearMap) = 1 ∧
      ∀ v w, (h.toCore p.1).inner (A p v) w = (h.toCore p.1).inner v (A p w) := by
    refine ⟨?_, ?_, ?_⟩
    · apply ContinuousLinearMap.ext
      intro v
      change J p.1 (p.2.val (J p.1 (J p.1 (p.2.val (J p.1 v))))) =
        J p.1 (p.2.val (J p.1 v))
      rw [hJ p.1]
      exact congrArg (J p.1) (DFunLike.congr_fun p.2.property.1 (J p.1 v))
    · -- Conjugation carries a spanning nonzero range vector to one for the image projector.
      have hmem (v : LinearMap.range p.2.val.toLinearMap) :
          J p.1 v.val ∈ LinearMap.range (A p).toLinearMap := by
        obtain ⟨w, hw⟩ := v.property
        refine ⟨J p.1 w, ?_⟩
        change J p.1 (p.2.val (J p.1 (J p.1 w))) = J p.1 v.val
        rw [hJ p.1]
        exact congrArg (J p.1) hw
      obtain ⟨v, hv, hspan⟩ := finrank_eq_one_iff'.mp p.2.property.2.1
      apply finrank_eq_one_iff'.mpr
      refine ⟨⟨J p.1 v.val, hmem v⟩, ?_, ?_⟩
      · intro hz
        apply hv
        apply Subtype.ext
        exact (J p.1).injective ((congrArg Subtype.val hz).trans (J p.1).map_zero.symm)
      · intro w
        obtain ⟨z, hz⟩ := w.property
        obtain ⟨c, hc⟩ := hspan ⟨p.2.val (J p.1 z), ⟨J p.1 z, rfl⟩⟩
        refine ⟨star c, ?_⟩
        apply Subtype.ext
        have hc' := congrArg (fun v : LinearMap.range p.2.val.toLinearMap ↦ J p.1 v.val) hc
        change J p.1 (c • v.val) = J p.1 (p.2.val (J p.1 z)) at hc'
        rw [map_smulₛₗ, starRingEnd_apply] at hc'
        exact hc'.trans hz
    · -- Antiunitarity converts the original self-adjointness equation into its conjugate.
      intro v w
      change (h.toCore p.1).inner (J p.1 (p.2.val (J p.1 v))) w =
        (h.toCore p.1).inner v (J p.1 (p.2.val (J p.1 w)))
      calc
        _ = star ((h.toCore p.1).inner (p.2.val (J p.1 v)) (J p.1 w)) := by
          rw [← hunitary, hJ p.1]
        _ = star ((h.toCore p.1).inner (J p.1 v) (p.2.val (J p.1 w))) :=
          congrArg star (p.2.property.2.2 (J p.1 v) (J p.1 w))
        _ = _ := by rw [← hunitary, hJ p.1]
  let f : Q → Q := fun p ↦ ⟨p.1, A p, hprojector p⟩
  have hbase : Continuous (fun p : Q ↦ p.1) := (hermitianProjectiveProjection r E h).continuous
  have hraw : Continuous (fun p : Q ↦
      (p.1, (⟨p.1, p.2.val⟩ : TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x)))) :=
    continuous_induced_dom
  have hA : Continuous (fun p : Q ↦
      (⟨p.1, A p⟩ : TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x))) := by
    -- Finite-dimensional native Hom coordinates detect continuity on each fixed vector.
    apply continuous_iff_continuousAt.mpr
    intro p₀
    apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
    refine ⟨hbase.continuousAt, ?_⟩
    apply continuousAt_clm_apply.mpr
    intro v
    let e := trivializationAt V E p₀.1
    have hp₀ : p₀.1 ∈ e.baseSet := mem_baseSet_trivializationAt V E p₀.1
    have hnear : ∀ᶠ p : Q in nhds p₀, p.1 ∈ e.baseSet :=
      hbase.continuousAt.eventually (e.open_baseSet.mem_nhds hp₀)
    have hframe : ContinuousAt (fun p : Q ↦
        (⟨p.1, e.symmL ℂ p.1 v⟩ : TotalSpace V E)) p₀ := by
      have hc := (e.toOpenPartialHomeomorph.continuousAt_symm
        (e.mem_target.mpr hp₀)).comp
          (hbase.continuousAt.prodMk (continuousAt_const (y := v)))
      apply hc.congr_of_eventuallyEq
      filter_upwards [hnear] with p hp
      rw [e.symmL_apply hp, e.mk_symm hp]
      rfl
    have hout := hcontinuous.continuousAt.comp
      (hraw.snd.continuousAt.clm_bundle_apply (hcontinuous.continuousAt.comp hframe))
    have hcoord := (e.continuousAt (e.mem_source.mpr hp₀)).comp hout
    apply hcoord.snd.congr_of_eventuallyEq
    filter_upwards [hnear] with p hp
    change e.continuousLinearMapAt ℂ p.1 (A p (e.symmL ℂ p.1 v)) = _
    exact e.continuousLinearMapAt_apply_of_mem ℂ hp _
  have hi : Topology.IsInducing (fun p : Q ↦
      (p.1, (⟨p.1, p.2.val⟩ : TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x)))) := ⟨rfl⟩
  exact ⟨f, hi.continuous_iff.mpr (hbase.prodMk hA)⟩

attribute [local instance] hermitianProjectiveLineTopology isFiniteRank_hermitianProjectiveLine
  isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual projective conjugation negates the normalized tautological first Chern class. -/
theorem hermitianProjectiveConjugationMap_pullback_root :
    singularCohomologyPullback ℤ
        (hermitianProjectiveConjugationMap r E h J hJ hcontinuous hunitary) 2
        (hermitianProjectiveChernRoot r E h) = -hermitianProjectiveChernRoot r E h := by
  let V := EuclideanSpace ℂ (Fin r)
  let := modelTopology V E
  let := isFiniteRank_model V E
  let Q := HermitianProjectiveBundle r E h
  let base := hermitianProjectiveProjection r E h
  let g := hermitianProjectiveConjugationMap r E h J hJ hcontinuous hunitary
  let L := HermitianProjectiveLine r E h
  let F := (g : Q → Q) *ᵖ L
  let : ∀ p, NormedAddCommGroup (F p) :=
    fun p ↦ (inferInstance : NormedAddCommGroup (L (g p)))
  let : ∀ p, NormedSpace ℂ (F p) := fun p ↦ (inferInstance : NormedSpace ℂ (L (g p)))
  have hL (p : Q) : Module.finrank ℂ (L p) = 1 := p.2.property.2.1
  -- The same J restricts to an actual conjugate-linear equivalence of the two tautological ranges.
  have hmem (p : Q) (v : L p) : J p.1 v.val ∈ LinearMap.range (g p).2.val.toLinearMap := by
    obtain ⟨w, hw⟩ := v.property
    refine ⟨J p.1 w, ?_⟩
    change J p.1 (p.2.val (J p.1 (J p.1 w))) = J p.1 v.val
    rw [hJ p.1]
    exact congrArg (J p.1) hw
  have hinv (p : Q) (v : F p) : J p.1 v.val ∈ LinearMap.range p.2.val.toLinearMap := by
    obtain ⟨w, hw⟩ := v.property
    refine ⟨J p.1 w, ?_⟩
    have hback := congrArg (J p.1) hw
    change J p.1 (J p.1 (p.2.val (J p.1 w))) = J p.1 v.val at hback
    rw [hJ p.1] at hback
    exact hback
  let e (p : Q) : L p ≃ₗ⋆[ℂ] F p :=
    { toFun := fun v ↦ ⟨J p.1 v.val, hmem p v⟩
      invFun := fun v ↦ ⟨J p.1 v.val, hinv p v⟩
      left_inv := fun v ↦ Subtype.ext (hJ p.1 v.val)
      right_inv := fun v ↦ Subtype.ext (hJ p.1 v.val)
      map_add' := fun v w ↦ Subtype.ext ((J p.1).map_add v.val w.val)
      map_smul' := fun c v ↦ Subtype.ext ((J p.1).map_smulₛₗ c v.val) }
  have he : Continuous (fun z : TotalSpace Unit L ↦
      (⟨z.proj, e z.proj z.snd⟩ : TotalSpace Unit F)) := by
    have hsource : Continuous (fun z : TotalSpace Unit L ↦
        (⟨z.proj, z.snd.val⟩ : TotalSpace Unit ((base : Q → X) *ᵖ E))) :=
      continuous_induced_dom
    have hb := (Pullback.continuous_proj Unit E base).comp hsource
    have hv := (Pullback.continuous_lift Unit E base).comp hsource
    have hJUnit : Continuous (fun z : TotalSpace Unit E ↦
        (⟨z.proj, J z.proj z.snd⟩ : TotalSpace Unit E)) :=
      (continuous_unitTotalEquiv_symm V E).comp
        (hcontinuous.comp (continuous_unitTotalEquiv V E))
    rw [(inducing_pullbackTotalSpaceEmbedding Unit L g).continuous_iff]
    refine hb.prodMk ?_
    apply continuous_induced_rng.mpr
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E base).continuous_iff]
    exact (g.continuous.comp hb).prodMk (hJUnit.comp hv)
  have heq := firstChernClass_eq_neg_of_conjugateLinearEquiv L hL
    (F := F) (fun p ↦ hL (g p)) e he
  exact (firstChernClass_pullback L hL g).symm.trans (neg_eq_iff_eq_neg.mp heq.symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include J hJ hcontinuous in
/-- A genuine conjugate-linear involution fixes every signed Chern class of the same bundle. -/
theorem chernClass_eq_neg_one_pow_smul_of_conjugateLinear_involution (k : ℕ) :
    chernClass r E h k = (-1 : ℤ) ^ k • chernClass r E h k := by
  let V := EuclideanSpace ℂ (Fin r)
  let := modelTopology V E
  let := isFiniteRank_model V E
  have hJUnit : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, J z.proj z.snd⟩ : TotalSpace Unit E)) :=
    (continuous_unitTotalEquiv_symm V E).comp
      (hcontinuous.comp (continuous_unitTotalEquiv V E))
  -- Average the supplied metric solely to make the actual projector conjugation orthogonal.
  obtain ⟨h₀, hunitary₀⟩ :=
    exists_hermitianMetric_invariant_of_conjugateLinear_involution E h J hJ hJUnit
  let g := hermitianProjectiveConjugationMap r E h₀ J hJ hcontinuous hunitary₀
  have hb := hermitianProjectivePowerCombination_int_bijective r E h₀ r
    (fun i ↦ Nat.le_of_lt i.isLt)
  have hsign := projectiveChernCoefficient_eq_neg_one_pow_smul_of_pullback_neg
    (hermitianProjectiveProjection r E h₀) r (hermitianProjectiveChernRoot r E h₀) hb g
    (by rfl) (hermitianProjectiveConjugationMap_pullback_root r E h₀ J hJ hcontinuous hunitary₀) k
  rw [← chernClass_eq_projectiveChernCoefficient r E h₀ hb k] at hsign
  -- Original metric independence returns the conclusion for the exact metric in the statement.
  rw [chernClass_metric_independent r E h h₀ k]
  exact hsign

end AtiyahSinger.ComplexBundle
