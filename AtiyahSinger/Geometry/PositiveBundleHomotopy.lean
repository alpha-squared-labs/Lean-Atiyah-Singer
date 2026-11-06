/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Proper affine homotopy of a strictly positive bundle map

Public module ID: M1344.

A continuous endomorphism of a finite-dimensional real vector bundle whose
quadratic form is strictly positive is joined to the identity by its affine
path. Retaining time makes this path a homeomorphism of the parameter cylinder.
Local inversion in the
original bundle charts proves joint inverse continuity, without a compact base,
a uniform positivity bound, or symmetry of the endomorphism.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Topology
open scoped unitInterval

variable {X F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (V : X → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- The affine path from the identity to a strictly positive real bundle map is proper. -/
theorem exists_positiveBundle_properHomotopy
    (A : ∀ x, V x →L[ℝ] V x)
    (hA : Continuous (fun z : TotalSpace F V ↦
      (⟨z.proj, A z.proj z.snd⟩ : TotalSpace F V)))
    (hpos : ∀ x (v : V x), v ≠ 0 → 0 < inner ℝ v (A x v)) :
    ∃ H : ContinuousMap.Homotopy (ContinuousMap.id (TotalSpace F V))
        ⟨fun z ↦ ⟨z.proj, A z.proj z.snd⟩, hA⟩,
      IsProperMap H ∧
      (∀ (t : I) (z : TotalSpace F V), H (t, z) =
        ⟨z.proj, (1 - (t : ℝ)) • z.snd + (t : ℝ) • A z.proj z.snd⟩) ∧
      ∃ C : (I × TotalSpace F V) ≃ₜ (I × TotalSpace F V),
        ∀ p, C p = (p.1, H p) := by
  classical
  let (x : X) : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  let L (t : I) (x : X) : V x →L[ℝ] V x :=
    (1 - (t : ℝ)) • ContinuousLinearMap.id ℝ (V x) + (t : ℝ) • A x
  -- Strict positivity survives the affine path, so every fiber map is bijective.
  have hLpos (t : I) (x : X) (v : V x) (hv : v ≠ 0) :
      0 < inner ℝ v (L t x v) := by
    have hself : 0 < inner ℝ v v := real_inner_self_pos.mpr hv
    have hAv := hpos x v hv
    change 0 < inner ℝ v ((1 - (t : ℝ)) • v + (t : ℝ) • A x v)
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    by_cases ht : (t : ℝ) = 0
    · simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hself
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr t.property.2) hself.le)
        (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) hAv)
  have hLbij (t : I) (x : X) : Bijective (L t x) := by
    have hinj : Injective (L t x) := by
      apply (injective_iff_map_eq_zero (L t x)).mpr
      intro v hv
      by_contra hne
      have hp := hLpos t x v hne
      rw [hv, inner_zero_right] at hp
      exact lt_irrefl 0 hp
    exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let E (t : I) (x : X) : V x ≃L[ℝ] V x :=
    (LinearEquiv.ofBijective (L t x).toLinearMap (hLbij t x)).toContinuousLinearEquiv
  let J (p : I × TotalSpace F V) : TotalSpace F V :=
    ⟨p.2.proj, L p.1 p.2.proj p.2.snd⟩
  have hb : Continuous (fun p : I × TotalSpace F V ↦ p.2.proj) :=
    (FiberBundle.continuous_proj F V).comp continuous_snd
  -- The original linear charts identify the forward path with an affine combination.
  have hJ : Continuous J := by
    rw [continuous_iff_continuousAt]
    intro p
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨hb.continuousAt, ?_⟩
    let e := trivializationAt F V p.2.proj
    have hv := ((FiberBundle.continuousAt_totalSpace F (x₀ := p)
      (f := fun z : I × TotalSpace F V ↦ z.2)).mp continuous_snd.continuousAt).2
    have hw := ((FiberBundle.continuousAt_totalSpace F (x₀ := p)
      (f := fun z : I × TotalSpace F V ↦
        (⟨z.2.proj, A z.2.proj z.2.snd⟩ : TotalSpace F V))).mp
          (hA.comp continuous_snd).continuousAt).2
    have ht : ContinuousAt (fun z : I × TotalSpace F V ↦ (z.1 : ℝ)) p :=
      (continuous_subtype_val.comp continuous_fst).continuousAt
    apply ((((continuousAt_const (y := (1 : ℝ))).sub ht).smul hv).add
      (ht.smul hw)).congr_of_eventuallyEq
    filter_upwards [hb.continuousAt
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V p.2.proj))] with z hz
    change (e ⟨z.2.proj, (1 - (z.1 : ℝ)) • z.2.snd +
      (z.1 : ℝ) • A z.2.proj z.2.snd⟩).2 =
        (1 - (z.1 : ℝ)) • (e z.2).2 +
          (z.1 : ℝ) • (e ⟨z.2.proj, A z.2.proj z.2.snd⟩).2
    simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hz, map_add, map_smul]
  let K (p : I × TotalSpace F V) : TotalSpace F V :=
    ⟨p.2.proj, (E p.1 p.2.proj).symm p.2.snd⟩
  -- In each original finite-dimensional chart, invert the same continuous family.
  have hK : Continuous K := by
    apply continuous_iff_continuousAt.mpr
    intro p₀
    let e := trivializationAt F V p₀.2.proj
    let U : Set X := e.baseSet
    let eLin (x : U) : V x.val ≃L[ℝ] F := e.continuousLinearEquivAt ℝ x.val x.property
    let B (q : I × U) : F ≃L[ℝ] F :=
      ((eLin q.2).symm.trans (E q.1 q.2.val)).trans (eLin q.2)
    have hpoint (x : U) (v : F) :
        (⟨x.val, (eLin x).symm v⟩ : TotalSpace F V) =
          e.toOpenPartialHomeomorph.symm (x.val, v) :=
      (e.symm_apply_eq_mk_continuousLinearEquivAt_symm x.val x.property v).symm
    have hB : Continuous (fun q : I × U ↦ (B q : F →L[ℝ] F)) := by
      apply continuous_clm_apply.mpr
      intro v
      have heinv : Continuous (fun q : I × U ↦
          (⟨q.2.val, (eLin q.2).symm v⟩ : TotalSpace F V)) := by
        have hc := e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
          ((continuous_subtype_val.comp continuous_snd).prodMk (continuous_const (y := v)))
          (fun q : I × U ↦ e.mem_target.mpr q.2.property)
        exact hc.congr (fun q ↦ (hpoint q.2 v).symm)
      have hf := hJ.comp (continuous_fst.prodMk heinv)
      exact continuous_snd.comp
        (e.toOpenPartialHomeomorph.continuousOn.comp_continuous hf
          (fun q : I × U ↦ e.mem_source.mpr q.2.property))
    have hBi : Continuous (fun q : I × U ↦ ((B q).symm : F →L[ℝ] F)) := by
      apply continuous_iff_continuousAt.mpr
      intro q
      have hi := (contDiffAt_map_inverse (n := 0) (B q)).continuousAt.comp_of_eq
        hB.continuousAt rfl
      simpa only [Function.comp_def, ContinuousLinearMap.inverse_equiv] using hi
    let W : Set (I × TotalSpace F V) := {p | p.2.proj ∈ U}
    have hW : IsOpen W := e.open_baseSet.preimage hb
    have hKW : ContinuousOn K W := by
      rw [continuousOn_iff_continuous_domRestrict]
      let base (p : W) : I × U := (p.val.1, ⟨p.val.2.proj, p.property⟩)
      have hbase : Continuous base :=
        (continuous_fst.comp continuous_subtype_val).prodMk
          ((hb.comp continuous_subtype_val).subtype_mk _)
      have hcoords : Continuous (fun p : W ↦ (e p.val.2).2) :=
        continuous_snd.comp (e.toOpenPartialHomeomorph.continuousOn.comp_continuous
          (continuous_snd.comp continuous_subtype_val)
          (fun p : W ↦ e.mem_source.mpr p.property))
      have hvalues : Continuous (fun p : W ↦ (B (base p)).symm (e p.val.2).2) :=
        (hBi.comp hbase).clm_apply hcoords
      have hc := e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
        ((hb.comp continuous_subtype_val).prodMk hvalues)
        (fun p : W ↦ e.mem_target.mpr p.property)
      apply hc.congr
      intro p
      have hinverse : (B (base p)).symm (e p.val.2).2 =
          eLin (base p).2 ((E p.val.1 p.val.2.proj).symm p.val.2.snd) := by
        apply (B (base p)).injective
        rw [ContinuousLinearEquiv.apply_symm_apply]
        change (e p.val.2).2 = eLin (base p).2
          (E p.val.1 p.val.2.proj ((eLin (base p).2).symm
            (eLin (base p).2 ((E p.val.1 p.val.2.proj).symm p.val.2.snd))))
        rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
        rfl
      change e.toOpenPartialHomeomorph.symm
        (p.val.2.proj, (B (base p)).symm (e p.val.2).2) = K p.val
      rw [hinverse, ← hpoint (base p).2, ContinuousLinearEquiv.symm_apply_apply]
    exact hKW.continuousAt
      (hW.mem_nhds (mem_baseSet_trivializationAt F V p₀.2.proj))
  -- The cylinder inverse is fiberwise; properness follows by compact parameter projection.
  let C : (I × TotalSpace F V) ≃ₜ (I × TotalSpace F V) :=
    { toFun := fun p ↦ (p.1, J p)
      invFun := fun p ↦ (p.1, K p)
      left_inv := by
        rintro ⟨t, x, v⟩
        change (t, (⟨x, (E t x).symm (E t x v)⟩ : TotalSpace F V)) = _
        rw [ContinuousLinearEquiv.symm_apply_apply]
      right_inv := by
        rintro ⟨t, x, v⟩
        change (t, (⟨x, E t x ((E t x).symm v)⟩ : TotalSpace F V)) = _
        rw [ContinuousLinearEquiv.apply_symm_apply]
      continuous_toFun := continuous_fst.prodMk hJ
      continuous_invFun := continuous_fst.prodMk hK }
  let H : ContinuousMap.Homotopy (ContinuousMap.id (TotalSpace F V))
      ⟨fun z ↦ ⟨z.proj, A z.proj z.snd⟩, hA⟩ :=
    { toFun := J
      continuous_toFun := hJ
      map_zero_left := by
        intro z
        change (⟨z.proj, (1 - (0 : ℝ)) • z.snd +
          (0 : ℝ) • A z.proj z.snd⟩ : TotalSpace F V) = z
        simp
      map_one_left := by
        intro z
        change (⟨z.proj, (1 - (1 : ℝ)) • z.snd +
          (1 : ℝ) • A z.proj z.snd⟩ : TotalSpace F V) = ⟨z.proj, A z.proj z.snd⟩
        simp }
  refine ⟨H, ?_, fun _ _ ↦ rfl, C, fun _ ↦ rfl⟩
  exact isProperMap_snd_of_compactSpace.comp C.isProperMap

end AtiyahSinger
