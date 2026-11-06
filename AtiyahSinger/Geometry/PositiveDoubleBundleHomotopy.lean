/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.PositiveBundleHomotopy
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Positive vertical homotopies on the original doubled bundle

Public module ID: M1345.

An endomorphism of the second vector may depend on the entire first vector.
Regard it as a bundle endomorphism over the original total space, apply the
positive affine homotopy there, and return through the actual reassociation
of the two original vector coordinates. The result retains the doubled
bundle topology and the whole parameter-cylinder homeomorphism.

No compactness of the base, uniform positive bound, or symmetry is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Topology
open scoped unitInterval

variable {X F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (V : X → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A positive vertical map on the original double bundle has a proper affine homotopy. -/
theorem exists_positiveDoubleBundle_properHomotopy
    (A : ∀ z : TotalSpace F V, V z.proj →L[ℝ] V z.proj)
    (hA : let pr : C(TotalSpace F V, X) := ⟨TotalSpace.proj, FiberBundle.continuous_proj F V⟩
      let W := (pr : TotalSpace F V → X) *ᵖ V
      Continuous (fun z : TotalSpace F W ↦ (⟨z.proj, A z.proj z.snd⟩ : TotalSpace F W)))
    (hpos : ∀ (z : TotalSpace F V) (v : V z.proj), v ≠ 0 → 0 < inner ℝ v (A z v)) :
    ∃ e : TotalSpace (F × F) (V ×ᵇ V) ≃ₜ TotalSpace (F × F) (V ×ᵇ V),
      (∀ z, e z = ⟨z.proj, z.snd.1, A ⟨z.proj, z.snd.1⟩ z.snd.2⟩) ∧
      ∃ H : ContinuousMap.Homotopy (ContinuousMap.id (TotalSpace (F × F) (V ×ᵇ V)))
          ⟨e, e.continuous⟩,
        IsProperMap H ∧
        (∀ (t : I) (z : TotalSpace (F × F) (V ×ᵇ V)), H (t, z) =
          ⟨z.proj, z.snd.1,
            (1 - (t : ℝ)) • z.snd.2 + (t : ℝ) • A ⟨z.proj, z.snd.1⟩ z.snd.2⟩) ∧
        ∃ C : (I × TotalSpace (F × F) (V ×ᵇ V)) ≃ₜ
            (I × TotalSpace (F × F) (V ×ᵇ V)),
          ∀ p, C p = (p.1, H p) := by
  classical
  let pr : C(TotalSpace F V, X) := ⟨TotalSpace.proj, FiberBundle.continuous_proj F V⟩
  let W := (pr : TotalSpace F V → X) *ᵖ V
  let D := TotalSpace (F × F) (V ×ᵇ V)
  let (z : TotalSpace F V) : NormedAddCommGroup (W z) := by
    change NormedAddCommGroup (V z.proj)
    infer_instance
  let (z : TotalSpace F V) : InnerProductSpace ℝ (W z) := by
    change InnerProductSpace ℝ (V z.proj)
    infer_instance
  let : FiberBundle F W := FiberBundle.pullback (F := F) (E := V) pr
  let : VectorBundle ℝ F W := VectorBundle.pullback ℝ (F := F) (E := V) pr
  -- Reassociation uses the same two original vector coordinates and native product charts.
  let c : D ≃ₜ TotalSpace F W :=
    { toFun := fun z ↦ ⟨⟨z.proj, z.snd.1⟩, z.snd.2⟩
      invFun := fun z ↦ ⟨z.proj.proj, z.proj.snd, z.snd⟩
      left_inv := by rintro ⟨x, u, v⟩; rfl
      right_inv := by rintro ⟨⟨x, u⟩, v⟩; rfl
      continuous_toFun := by
        apply continuous_iff_continuousAt.mpr
        intro z
        have hb : ContinuousAt (fun w : D ↦ w.proj) z :=
          (FiberBundle.continuous_proj (F × F) (V ×ᵇ V)).continuousAt
        have hc := (FiberBundle.continuousAt_totalSpace (F × F) (E := V ×ᵇ V)
          (x₀ := z) (f := id)).mp continuousAt_id |>.2
        have hfirst : ContinuousAt (fun w : D ↦
            (⟨w.proj, w.snd.1⟩ : TotalSpace F V)) z := by
          apply (FiberBundle.continuousAt_totalSpace F _).mpr
          exact ⟨hb, hc.fst⟩
        apply (FiberBundle.continuousAt_totalSpace F _).mpr
        exact ⟨hfirst, hc.snd⟩
      continuous_invFun := by
        apply continuous_iff_continuousAt.mpr
        intro z
        have hp : ContinuousAt (fun w : TotalSpace F W ↦ w.proj) z :=
          (FiberBundle.continuous_proj F W).continuousAt
        have hfirst := (FiberBundle.continuousAt_totalSpace F (E := V)
          (x₀ := z) (f := fun w : TotalSpace F W ↦ w.proj)).mp hp
        have hsecond := (FiberBundle.continuousAt_totalSpace F (E := W)
          (x₀ := z) (f := id)).mp continuousAt_id |>.2
        apply (FiberBundle.continuousAt_totalSpace (F × F) _).mpr
        exact ⟨hfirst.1, hfirst.2.prodMk hsecond⟩ }
  obtain ⟨H, hHproper, hH, C, hC⟩ := exists_positiveBundle_properHomotopy W A hA hpos
  -- The time-one restriction of the same cylinder supplies the actual endpoint homeomorphism.
  let eW : TotalSpace F W ≃ₜ TotalSpace F W :=
    { toFun := fun z ↦ H (1, z)
      invFun := fun z ↦ (C.symm (1, z)).2
      left_inv := by
        intro z
        have h := C.symm_apply_apply (1, z)
        rw [hC] at h
        exact congrArg Prod.snd h
      right_inv := by
        intro z
        have h := C.apply_symm_apply (1, z)
        rw [hC] at h
        have ht := congrArg Prod.fst h
        have hv := congrArg Prod.snd h
        change (C.symm (1, z)).1 = 1 at ht
        change H ((C.symm (1, z)).1, (C.symm (1, z)).2) = z at hv
        rw [ht] at hv
        exact hv
      continuous_toFun := H.continuous.comp (continuous_const.prodMk continuous_id)
      continuous_invFun := continuous_snd.comp
        (C.symm.continuous.comp (continuous_const.prodMk continuous_id)) }
  let e : D ≃ₜ D := (c.trans eW).trans c.symm
  let J : ContinuousMap.Homotopy (ContinuousMap.id D) ⟨e, e.continuous⟩ :=
    { toFun := fun p ↦ c.symm (H (p.1, c p.2))
      continuous_toFun := c.symm.continuous.comp
        (H.continuous.comp (continuous_fst.prodMk (c.continuous.comp continuous_snd)))
      map_zero_left := by
        intro z
        change c.symm (H (0, c z)) = z
        have hzero : H (0, c z) = c z := H.map_zero_left (c z)
        exact (congrArg c.symm hzero).trans (c.symm_apply_apply z)
      map_one_left := by intro z; rfl }
  let cI := (Homeomorph.refl I).prodCongr c
  let CI : (I × D) ≃ₜ (I × D) := (cI.trans C).trans cI.symm
  refine ⟨e, ?_, J, ?_, ?_, CI, ?_⟩
  · intro z
    change c.symm (H (1, c z)) = _
    have hterminal : H (1, c z) =
        ⟨(c z).proj, A (c z).proj (c z).snd⟩ := H.map_one_left (c z)
    exact congrArg c.symm hterminal
  · exact c.symm.isProperMap.comp (hHproper.comp cI.isProperMap)
  · intro t z
    change c.symm (H (t, c z)) = _
    rw [hH]
    rfl
  · intro p
    change cI.symm (C (p.1, c p.2)) = (p.1, J p)
    rw [hC]
    rfl

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Positive rescaling followed by the same positive vertical map has a proper homotopy. -/
theorem exists_positiveDoubleBundle_scaledProperHomotopy
    (A : ∀ z : TotalSpace F V, V z.proj →L[ℝ] V z.proj)
    (hA : let pr : C(TotalSpace F V, X) := ⟨TotalSpace.proj, FiberBundle.continuous_proj F V⟩
      let W := (pr : TotalSpace F V → X) *ᵖ V
      Continuous (fun z : TotalSpace F W ↦ (⟨z.proj, A z.proj z.snd⟩ : TotalSpace F W)))
    (hpos : ∀ (z : TotalSpace F V) (v : V z.proj), v ≠ 0 → 0 < inner ℝ v (A z v))
    (c : ℝ) (hc : 0 < c) :
    ∃ e : TotalSpace (F × F) (V ×ᵇ V) ≃ₜ TotalSpace (F × F) (V ×ᵇ V),
      (∀ z, e z = ⟨z.proj, c • z.snd.1, c⁻¹ • A ⟨z.proj, c • z.snd.1⟩ z.snd.2⟩) ∧
      ∃ H : ContinuousMap.Homotopy (ContinuousMap.id (TotalSpace (F × F) (V ×ᵇ V)))
          ⟨e, e.continuous⟩,
        IsProperMap H ∧
        ∃ C : (I × TotalSpace (F × F) (V ×ᵇ V)) ≃ₜ
            (I × TotalSpace (F × F) (V ×ᵇ V)),
          ∀ p, C p = (p.1, H p) := by
  classical
  let D := TotalSpace (F × F) (V ×ᵇ V)
  let a (t : I) : ℝ := 1 - (t : ℝ) + (t : ℝ) * c
  have ha (t : I) : 0 < a t := by
    by_cases ht : (t : ℝ) = 0
    · simp [a, ht]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.property.2)
        (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) hc)
  have hca : Continuous a := (continuous_const.sub continuous_subtype_val).add
    (continuous_subtype_val.mul continuous_const)
  have hcia : Continuous (fun t : I ↦ (a t)⁻¹) := hca.inv₀ (fun t ↦ (ha t).ne')
  -- Both scalar factors vary continuously in the same original product frame.
  have hscale (f g : I → ℝ) (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun p : I × D ↦
        (⟨p.2.proj, f p.1 • p.2.snd.1, g p.1 • p.2.snd.2⟩ : D)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hb : ContinuousAt (fun z : I × D ↦ z.2.proj) p :=
      ((FiberBundle.continuous_proj (F × F) (V ×ᵇ V)).comp continuous_snd).continuousAt
    have hcoords := (FiberBundle.continuousAt_totalSpace (F × F) (E := V ×ᵇ V)
      (x₀ := p) (f := fun z : I × D ↦ z.2)).mp continuous_snd.continuousAt |>.2
    let e := trivializationAt F V p.2.proj
    apply (FiberBundle.continuousAt_totalSpace (F × F) _).mpr
    refine ⟨hb, ?_⟩
    have hpair := ((hf.comp continuous_fst).continuousAt.smul hcoords.fst).prodMk
      ((hg.comp continuous_fst).continuousAt.smul hcoords.snd)
    apply hpair.congr_of_eventuallyEq
    filter_upwards [hb (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V p.2.proj))]
      with z hz
    change ((e ⟨z.2.proj, f z.1 • z.2.snd.1⟩).2,
        (e ⟨z.2.proj, g z.1 • z.2.snd.2⟩).2) =
      (f z.1 • (e ⟨z.2.proj, z.2.snd.1⟩).2,
        g z.1 • (e ⟨z.2.proj, z.2.snd.2⟩).2)
    simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hz, map_smul]
  let S : (I × D) ≃ₜ (I × D) :=
    { toFun := fun p ↦ (p.1, ⟨p.2.proj, a p.1 • p.2.snd.1, (a p.1)⁻¹ • p.2.snd.2⟩)
      invFun := fun p ↦ (p.1, ⟨p.2.proj, (a p.1)⁻¹ • p.2.snd.1, a p.1 • p.2.snd.2⟩)
      left_inv := by
        rintro ⟨t, x, u, v⟩
        simp only [smul_smul, inv_mul_cancel₀ (ha t).ne', mul_inv_cancel₀ (ha t).ne', one_smul]
      right_inv := by
        rintro ⟨t, x, u, v⟩
        simp only [smul_smul, inv_mul_cancel₀ (ha t).ne', mul_inv_cancel₀ (ha t).ne', one_smul]
      continuous_toFun := continuous_fst.prodMk (hscale a (fun t ↦ (a t)⁻¹) hca hcia)
      continuous_invFun := continuous_fst.prodMk (hscale (fun t ↦ (a t)⁻¹) a hcia hca) }
  let s : D ≃ₜ D :=
    { toFun := fun z ↦ ⟨z.proj, c • z.snd.1, c⁻¹ • z.snd.2⟩
      invFun := fun z ↦ ⟨z.proj, c⁻¹ • z.snd.1, c • z.snd.2⟩
      left_inv := by
        rintro ⟨x, u, v⟩
        simp only [smul_smul, inv_mul_cancel₀ hc.ne', mul_inv_cancel₀ hc.ne', one_smul]
      right_inv := by
        rintro ⟨x, u, v⟩
        simp only [smul_smul, inv_mul_cancel₀ hc.ne', mul_inv_cancel₀ hc.ne', one_smul]
      continuous_toFun := (hscale (fun _ ↦ c) (fun _ ↦ c⁻¹)
        continuous_const continuous_const).comp (show Continuous (fun z : D ↦ ((0 : I), z)) from
          continuous_const.prodMk continuous_id)
      continuous_invFun := (hscale (fun _ ↦ c⁻¹) (fun _ ↦ c)
        continuous_const continuous_const).comp (show Continuous (fun z : D ↦ ((0 : I), z)) from
          continuous_const.prodMk continuous_id) }
  obtain ⟨e, he, H, hHproper, _hH, C, hC⟩ :=
    exists_positiveDoubleBundle_properHomotopy V A hA hpos
  -- Composition takes the positive vertical map at the actual rescaled first coordinate.
  let J : ContinuousMap.Homotopy (ContinuousMap.id D) ⟨s.trans e, (s.trans e).continuous⟩ :=
    { toFun := fun p ↦ H (S p)
      continuous_toFun := H.continuous.comp S.continuous
      map_zero_left := by
        intro z
        have hS : S (0, z) = (0, z) := by
          rcases z with ⟨x, u, v⟩
          simp [S, a]
        exact (congrArg H hS).trans (H.map_zero_left z)
      map_one_left := by
        intro z
        have hS : S (1, z) = (1, s z) := by simp [S, a, s]
        exact (congrArg H hS).trans (H.map_one_left (s z)) }
  refine ⟨s.trans e, ?_, J, hHproper.comp S.isProperMap, S.trans C, ?_⟩
  · intro z
    have h := he (s z)
    change e (s z) = _
    change e (s z) = ⟨z.proj, c • z.snd.1,
      A ⟨z.proj, c • z.snd.1⟩ (c⁻¹ • z.snd.2)⟩ at h
    simpa only [map_smul] using h
  · intro p
    change C (S p) = (p.1, H (S p))
    exact hC (S p)

end AtiyahSinger
