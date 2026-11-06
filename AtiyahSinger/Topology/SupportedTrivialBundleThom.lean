/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportSplitPair
public import AtiyahSinger.Topology.ThomNaturality
public import AtiyahSinger.Topology.ThomOpenExtension
public import AtiyahSinger.Topology.TrivialBundleThom

/-!
# Supported Thom on a trivial bundle

Public module ID: M2219.

The native total-space trivialization identifies the supported Thom operator
with the exterior Bott product over an arbitrary locally compact Hausdorff base.
The compact-base calculation descends through extension into the one-point
compactification. Its infinity fiber has a proper retraction, so that extension
detects equality. This comparison retains the specified positive exterior Bott
class and is independent of the chosen continuous Hermitian metric.

Sources: Spin Geometry C.13; Karoubi IV.1.10--1.11, II.4.21.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle Topology

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Normalize the compactification extension and the specified exterior Bott product.
/-- The original supported Thom map of a trivial bundle is external exterior Bott product. -/
theorem supportedThomHom_trivial_externalProduct
    (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] :
    let T := Bundle.Trivial X V
    letI := modelTopology V T
    letI := isFiniteRank_model V T
    letI := FiniteDimensional.proper ℂ V
    let e := (unitTotalHomeomorph V T).trans (Bundle.Trivial.homeomorphProd X V)
    ∀ (h : ContinuousHermitianMetric T) (a : CompactSupportKZero X),
      compactSupportKZeroHomeomorph e (h.supportedThomHom a) =
        compactSupportKZeroExternalProduct a (exteriorBottClass V) := by
  classical
  let B := OnePoint X
  let TB := Bundle.Trivial B V
  let TX := Bundle.Trivial X V
  let := modelTopology V TB
  let := modelTopology V TX
  let := isFiniteRank_model V TB
  let := isFiniteRank_model V TX
  let := FiniteDimensional.proper ℂ V
  let eB := (unitTotalHomeomorph V TB).trans (Bundle.Trivial.homeomorphProd B V)
  let eX := (unitTotalHomeomorph V TX).trans (Bundle.Trivial.homeomorphProd X V)
  dsimp only
  intro h a
  -- Extend the fixed inner product to the constant bundle on the compactification.
  have hinner : Continuous (fun z : TotalSpace Unit (TB ×ᵇ TB) ↦
      inner ℂ z.snd.1 z.snd.2) :=
    (eB.continuous.snd.comp (continuous_sum_fst (E := TB) (F := TB))).inner
      (eB.continuous.snd.comp (continuous_sum_snd (E := TB) (F := TB)))
  let hB := ofInnerProduct TB hinner
  let f : C(X, B) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
  have hf : IsOpenEmbedding f := OnePoint.isOpenEmbedding_coe
  let R := f *ᵖ TB
  let := isFiniteRank_pullback (E := TB) f
  let d : Hom R TX :=
    { linearMap _ := LinearMap.id
      continuous_total := eX.symm.continuous.comp
        (continuous_proj.prodMk
          (eB.continuous.snd.comp (Pullback.continuous_lift Unit TB f))) }
  let e := d.toIso (fun _ ↦ Function.bijective_id)
  let q := pullbackTotalMap TB f
  have hq : IsOpenEmbedding q := (pullbackTotalMap_properties TB f).2 hf
  let j : X × V → B × V := Prod.map f id
  have hj : IsOpenEmbedding j := hf.prodMap IsOpenEmbedding.id
  -- The complement is precisely the infinity fiber, with a proper retraction.
  let N : Set (B × V) := (Set.range j)ᶜ
  have hN : IsClosed N := hj.isOpen_range.isClosed_compl
  let := hN.locallyCompactSpace
  have hinfty (v : V) : (OnePoint.infty, v) ∈ N := by
    rintro ⟨z, hz⟩
    have hp := congrArg Prod.fst hz
    cases hp
  have hpoint (z : N) : z.val.1 = OnePoint.infty := by
    rcases z with ⟨⟨b, v⟩, hz⟩
    cases b using OnePoint.rec with
    | infty => rfl
    | coe x => exact (hz ⟨(x, v), rfl⟩).elim
  let r : C(B × V, N) :=
    ⟨fun z ↦ ⟨(OnePoint.infty, z.2), hinfty z.2⟩,
      (continuous_const.prodMk continuous_snd).subtype_mk _⟩
  have hr (z : N) : r z.val = z := by
    apply Subtype.ext
    exact Prod.ext (hpoint z).symm rfl
  have hproper : IsProperMap r :=
    isProperMap_of_comp_of_t2 r.continuous
      (continuous_snd.comp continuous_subtype_val)
      (show IsProperMap ((fun z : N ↦ z.val.2) ∘ r) from
        isProperMap_snd_of_compactSpace)
  have hdetect : Function.Injective (compactSupportKZeroOpenPushforward j hj) :=
    compactSupportKZeroOpenPushforward_injective_of_retraction j hj r hproper hr
  -- All three trivializations carry the same pair (x,v); open extension composes.
  have hsquare (u : CompactSupportKZero (TotalSpace Unit R)) :
      compactSupportKZeroOpenPushforward j hj
          (compactSupportKZeroHomeomorph eX
            (compactSupportKZeroHomeomorph e.totalHomeomorph u)) =
        compactSupportKZeroHomeomorph eB (compactSupportKZeroOpenPushforward q hq u) := by
    rw [← compactSupportKZeroOpenPushforward_homeomorph eX,
      ← compactSupportKZeroOpenPushforward_homeomorph e.totalHomeomorph,
      ← compactSupportKZeroOpenPushforward_homeomorph eB]
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp]
    rfl
  have hmetric := DFunLike.congr_fun
    ((hB.pullback f).supportedThomHom_iso h e) a
  have hextend := DFunLike.congr_fun (hB.supportedThomHom_openPushforward f hf) a
  -- The compact-base formula uses the same positive exterior Bott class.
  have hcompact (b : CompactSupportKZero B) :
      compactSupportKZeroHomeomorph eB (hB.supportedThomHom b) =
        compactSupportKZeroExternalProduct b (exteriorBottClass V) := by
    change compactSupportKZeroHomeomorph eB
      ((ofInnerProduct TB hinner).supportedThomHom b) = _
    rw [supportedThomHom_ofInnerProduct, supportedThomHom_compact]
    simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.symm_apply_apply] using
      exteriorThomHom_trivial (X := B) V hinner ((compactSupportKZeroCompactEquiv B) b)
  apply hdetect
  calc
    compactSupportKZeroOpenPushforward j hj
        (compactSupportKZeroHomeomorph eX (h.supportedThomHom a)) =
        compactSupportKZeroHomeomorph eB
          (compactSupportKZeroOpenPushforward q hq ((hB.pullback f).supportedThomHom a)) := by
      rw [← hmetric]
      exact hsquare _
    _ = compactSupportKZeroHomeomorph eB
        (hB.supportedThomHom (compactSupportKZeroOpenPushforward f hf a)) := by
      exact congrArg (compactSupportKZeroHomeomorph eB) hextend
    _ = compactSupportKZeroExternalProduct
        (compactSupportKZeroOpenPushforward f hf a) (exteriorBottClass V) := hcompact _
    _ = compactSupportKZeroOpenPushforward j hj
        (compactSupportKZeroExternalProduct a (exteriorBottClass V)) := by
      simpa only [compactSupportKZeroOpenPushforward_id, AddMonoidHom.id_apply] using
        (compactSupportKZeroExternalProduct_openPushforward f hf id IsOpenEmbedding.id
          a (exteriorBottClass V)).symm

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
