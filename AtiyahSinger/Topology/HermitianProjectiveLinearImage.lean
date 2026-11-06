/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectiveCoordinates
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Linear images in the original orthogonal-projector model

Public module ID: M1897.

A linear map acts on each projective line that it does not annihilate.
The image is the orthogonal projector onto the actual image subspace.
Local nonzero image vectors prove continuity jointly in the map and projector;
this includes the varying linear maps used in projective deformation retractions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- The actual rank-one image under a linear map which does not annihilate the given line. -/
def linearImage (f : V →L[ℂ] W) (P : HermitianProjectiveSpace V InnerProductSpace.toCore)
    (hf : f.comp P.val ≠ 0) : HermitianProjectiveSpace W InnerProductSpace.toCore := by
  let U := LinearMap.range (f.comp P.val).toLinearMap
  have hle : Module.finrank ℂ U ≤ 1 := by
    change Module.finrank ℂ (LinearMap.range (f.toLinearMap.comp P.val.toLinearMap)) ≤ 1
    rw [LinearMap.range_comp]
    exact (Submodule.finrank_map_le f.toLinearMap _).trans_eq P.property.2.1
  have hpos : 0 < Module.finrank ℂ U := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    by_contra hzero
    push Not at hzero
    apply hf
    apply ContinuousLinearMap.ext
    intro v
    have hz := hzero (⟨f (P.val v), ⟨v, rfl⟩⟩ : U)
    exact congrArg Subtype.val hz
  refine ⟨U.starProjection, U.isIdempotentElem_starProjection, ?_,
    U.inner_starProjection_left_eq_right⟩
  rw [Submodule.range_starProjection]
  omega

/-- Every actual image vector is fixed by its image-line projector. -/
theorem linearImage_apply_image (f : V →L[ℂ] W)
    (P : HermitianProjectiveSpace V InnerProductSpace.toCore) (hf : f.comp P.val ≠ 0)
    (v : V) : (linearImage f P hf).val (f (P.val v)) = f (P.val v) :=
  Submodule.starProjection_eq_self_iff.mpr ⟨v, rfl⟩

/-- Any nonzero projected image vector computes the same actual image projector. -/
theorem linearImage_eq_ofVector (f : V →L[ℂ] W)
    (P : HermitianProjectiveSpace V InnerProductSpace.toCore) (hf : f.comp P.val ≠ 0)
    (v : V) (hv : f (P.val v) ≠ 0) :
    linearImage f P hf = ofVector (f (P.val v)) hv :=
  (ofVector_eq _ _ hv (linearImage_apply_image f P hf v)).symm

/-- Taking a nonvanishing linear image is continuous jointly in the map and original projector. -/
theorem continuous_linearImage :
    Continuous (fun z : {z : (V →L[ℂ] W) ×
        HermitianProjectiveSpace V InnerProductSpace.toCore // z.1.comp z.2.val ≠ 0} ↦
      linearImage z.val.1 z.val.2 z.property) := by
  let D := {z : (V →L[ℂ] W) ×
    HermitianProjectiveSpace V InnerProductSpace.toCore // z.1.comp z.2.val ≠ 0}
  apply continuous_iff_continuousAt.mpr
  intro z₀
  obtain ⟨v, hv⟩ : ∃ v : V, z₀.val.1 (z₀.val.2.val v) ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply z₀.property
    exact ContinuousLinearMap.ext hzero
  -- The same fixed vector remains a nonzero image on a neighborhood of z₀.
  have hx : Continuous (fun z : D ↦ z.val.1 (z.val.2.val v)) :=
    (continuous_fst.comp continuous_subtype_val).clm_apply
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).clm_apply
        continuous_const)
  have hn : ∀ᶠ z : D in nhds z₀, z.val.1 (z.val.2.val v) ≠ 0 :=
    (isOpen_ne_fun hx continuous_const).mem_nhds hv
  have hw : ContinuousAt (fun z : D ↦
      ‖z.val.1 (z.val.2.val v)‖⁻¹ • z.val.1 (z.val.2.val v)) z₀ :=
    (hx.norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hv)).smul hx.continuousAt
  have hformula : ContinuousAt (fun z : D ↦
      (innerSL ℂ (‖z.val.1 (z.val.2.val v)‖⁻¹ • z.val.1 (z.val.2.val v))).smulRight
        (‖z.val.1 (z.val.2.val v)‖⁻¹ • z.val.1 (z.val.2.val v))) z₀ :=
    ((ContinuousLinearMap.smulRightL ℂ W W).continuous.continuousAt.comp
      ((innerSL ℂ).continuous.continuousAt.comp hw)).clm_apply hw
  apply Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hn] with z hz
  exact congrArg Subtype.val (linearImage_eq_ofVector z.val.1 z.val.2 z.property v hz)

/-- An injective continuous linear map acts continuously on every original projective line. -/
def linearImageMap (f : V →L[ℂ] W) (hf : Function.Injective f) :
    C(HermitianProjectiveSpace V InnerProductSpace.toCore,
      HermitianProjectiveSpace W InnerProductSpace.toCore) := by
  have hnonzero (P : HermitianProjectiveSpace V InnerProductSpace.toCore) :
      f.comp P.val ≠ 0 := by
    intro hzero
    have hP : P.val = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      apply hf
      exact (congrArg (fun L : V →L[ℂ] W ↦ L v) hzero).trans f.map_zero.symm
    have hr : Module.finrank ℂ (LinearMap.range P.val.toLinearMap) = 1 := P.property.2.1
    have hlin : P.val.toLinearMap = 0 := congrArg ContinuousLinearMap.toLinearMap hP
    rw [hlin, LinearMap.range_zero] at hr
    simp at hr
  let D := {z : (V →L[ℂ] W) ×
    HermitianProjectiveSpace V InnerProductSpace.toCore // z.1.comp z.2.val ≠ 0}
  let g : HermitianProjectiveSpace V InnerProductSpace.toCore → D :=
    fun P ↦ ⟨(f, P), hnonzero P⟩
  have hg : Continuous g := (continuous_const.prodMk continuous_id).subtype_mk hnonzero
  have hc := (continuous_linearImage (V := V) (W := W)).comp hg
  exact
    { toFun := fun P ↦ linearImage f P (hnonzero P)
      continuous_toFun := hc }

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace
