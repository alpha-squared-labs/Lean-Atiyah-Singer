/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Radial compression in an original vector bundle

Public module ID: M1111.

A continuous fiberwise quadratic function gives a radial compression and its
explicit inverse on an open cylinder. Taking the squared metric length divided
by a positive varying radius squared identifies the whole bundle with its open
disk bundle at time one. The formula also interpolates from the identity.

This is the standard radial step in the tubular neighborhood theorem. The
construction keeps the original total topology and does not choose a new atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set Topology
open scoped ContDiff Manifold

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

/-- Radial compression associated to the supplied real-valued fiber function. -/
def bundleRadialCompression (q : TotalSpace F V → ℝ)
    (p : ℝ × TotalSpace F V) : TotalSpace F V :=
  ⟨p.2.proj, (Real.sqrt (1 + p.1 * q p.2))⁻¹ • p.2.2⟩

variable [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- The radial formula and its inverse form one parameter-preserving open cylinder. -/
def bundleRadialCompressionCylinder (q : TotalSpace F V → ℝ) (hq : Continuous q)
    (hquad : ∀ (a : ℝ) (z : TotalSpace F V), q ⟨z.proj, a • z.2⟩ = a ^ 2 * q z) :
    OpenPartialHomeomorph (ℝ × TotalSpace F V) (ℝ × TotalSpace F V) := by
  let R := bundleRadialCompression q
  let D (p : ℝ × TotalSpace F V) : ℝ := 1 + p.1 * q p.2
  have hD : Continuous D := continuous_const.add (continuous_fst.mul (hq.comp continuous_snd))
  -- The quadratic scaling identity computes the image domain and the inverse exactly.
  have hinv (p : ℝ × TotalSpace F V) (hp : 0 < D p) :
      1 - p.1 * q (R p) = (D p)⁻¹ ∧ R (-p.1, R p) = p.2 := by
    have hs : 0 < Real.sqrt (D p) := Real.sqrt_pos.mpr hp
    have hqR : q (R p) = (D p)⁻¹ * q p.2 := by
      rw [show R p = ⟨p.2.proj, (Real.sqrt (D p))⁻¹ • p.2.2⟩ from rfl, hquad]
      rw [inv_pow, Real.sq_sqrt hp.le]
    have hden : 1 - p.1 * q (R p) = (D p)⁻¹ := by
      rw [hqR]
      dsimp [D]
      field_simp [show 1 + p.1 * q p.2 ≠ 0 from hp.ne']
      ring
    refine ⟨hden, ?_⟩
    have hden' : 1 + -p.1 * q (R p) = (D p)⁻¹ := by
      simpa only [neg_mul, sub_eq_add_neg] using hden
    change (⟨p.2.proj,
      (Real.sqrt (1 + -p.1 * q (R p)))⁻¹ •
        ((Real.sqrt (D p))⁻¹ • p.2.2)⟩ : TotalSpace F V) = p.2
    rw [hden', Real.sqrt_inv, inv_inv, smul_inv_smul₀ hs.ne']
  -- Continuity is checked in the same bundle frame; scalar multiplication is fiberwise.
  have hR : ContinuousOn R {p | 0 < D p} := by
    intro p hp
    have hc : ContinuousAt (fun z ↦ (Real.sqrt (D z))⁻¹) p :=
      hD.continuousAt.sqrt.inv₀ (Real.sqrt_pos.mpr hp).ne'
    have hb : Continuous (fun z : ℝ × TotalSpace F V ↦ z.2.proj) :=
      (FiberBundle.continuous_proj F V).comp continuous_snd
    rw [FiberBundle.continuousWithinAt_totalSpace]
    refine ⟨hb.continuousAt.continuousWithinAt, ?_⟩
    let e := trivializationAt F V p.2.proj
    have hv := ((FiberBundle.continuousAt_totalSpace F (x₀ := p)
      (f := fun z : ℝ × TotalSpace F V ↦ z.2)).mp continuous_snd.continuousAt).2
    apply (hc.smul hv).continuousWithinAt.congr_of_eventuallyEq
    · apply Filter.Eventually.filter_mono inf_le_left
      filter_upwards [hb.continuousAt
        (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V p.2.proj))] with z hz
      change (e ⟨z.2.proj, (Real.sqrt (D z))⁻¹ • z.2.2⟩).2 =
        (Real.sqrt (D z))⁻¹ • (e z.2).2
      simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hz, map_smul]
    · change (e ⟨p.2.proj, (Real.sqrt (D p))⁻¹ • p.2.2⟩).2 =
        (Real.sqrt (D p))⁻¹ • (e p.2).2
      simp only [← e.continuousLinearMapAt_apply_of_mem ℝ
        (mem_baseSet_trivializationAt F V p.2.proj), map_smul]
  refine
    { toFun := fun p ↦ (p.1, R p)
      invFun := fun p ↦ (p.1, R (-p.1, p.2))
      source := {p | 0 < D p}
      target := {p | 0 < 1 - p.1 * q p.2}
      map_source' := fun p hp ↦ by
        change 0 < 1 - p.1 * q (R p)
        rw [(hinv p hp).1]
        exact inv_pos.mpr hp
      map_target' := ?_
      left_inv' := fun p hp ↦ by
        apply Prod.ext
        · rfl
        · exact (hinv p hp).2
      right_inv' := ?_
      open_source := isOpen_lt continuous_const hD
      open_target := isOpen_lt continuous_const
        (continuous_const.sub (continuous_fst.mul (hq.comp continuous_snd)))
      continuousOn_toFun := continuous_fst.continuousOn.prodMk hR
      continuousOn_invFun := continuous_fst.continuousOn.prodMk
        (hR.comp (continuous_fst.neg.prodMk continuous_snd).continuousOn
          (fun p hp ↦ by simpa only [mem_ofPred_eq, D, neg_mul, sub_eq_add_neg] using hp)) }
  · intro p hp
    have hp' : 0 < D (-p.1, p.2) := by
      simpa only [mem_ofPred_eq, D, neg_mul, sub_eq_add_neg] using hp
    have h := (hinv (-p.1, p.2) hp').1
    change 0 < 1 + p.1 * q (R (-p.1, p.2))
    rw [show 1 + p.1 * q (R (-p.1, p.2)) = (D (-p.1, p.2))⁻¹ by
      simpa only [neg_mul, sub_neg_eq_add] using h]
    exact inv_pos.mpr hp'
  · intro p hp
    apply Prod.ext
    · rfl
    · have hp' : 0 < D (-p.1, p.2) := by
        simpa only [mem_ofPred_eq, D, neg_mul, sub_eq_add_neg] using hp
      simpa only [neg_neg] using (hinv (-p.1, p.2) hp').2

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB} [ChartedSpace HB B]

/-- A smooth fiber function gives a jointly smooth compression on its full open domain. -/
theorem contMDiffOn_bundleRadialCompression (q : TotalSpace F V → ℝ)
    (hq : ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ) ∞ q) :
    ContMDiffOn (𝓘(ℝ).prod (I.prod 𝓘(ℝ, F))) (I.prod 𝓘(ℝ, F)) ∞
      (bundleRadialCompression q) {p | 0 < 1 + p.1 * q p.2} := by
  let D (p : ℝ × TotalSpace F V) : ℝ := 1 + p.1 * q p.2
  have hD : ContMDiff (𝓘(ℝ).prod (I.prod 𝓘(ℝ, F))) 𝓘(ℝ) ∞ D :=
    contMDiff_const.add (contMDiff_fst.mul (hq.comp contMDiff_snd))
  intro p hp
  have hc : ContMDiffAt (𝓘(ℝ).prod (I.prod 𝓘(ℝ, F))) 𝓘(ℝ) ∞
      (fun z ↦ (Real.sqrt (D z))⁻¹) p :=
    ((Real.contDiffAt_sqrt (show D p ≠ 0 from hp.ne')).contMDiffAt.comp p (hD p)).inv₀
      (Real.sqrt_pos.mpr hp).ne'
  have hb : ContMDiff (𝓘(ℝ).prod (I.prod 𝓘(ℝ, F))) I ∞
      (fun z : ℝ × TotalSpace F V ↦ z.2.proj) :=
    (contMDiff_proj V).comp contMDiff_snd
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨(hb p).contMDiffWithinAt, ?_⟩
  let e := trivializationAt F V p.2.proj
  have hv := (Bundle.contMDiffAt_totalSpace (IB := I)
    (IM := 𝓘(ℝ).prod (I.prod 𝓘(ℝ, F))) (n := ∞)
    (f := fun z : ℝ × TotalSpace F V ↦ z.2) (x₀ := p)).mp
      (contMDiff_snd p)
  -- The original linear frame turns fiber multiplication into ordinary scalar multiplication.
  apply (hc.smul hv.2).contMDiffWithinAt.congr_of_eventuallyEq
  · apply Filter.Eventually.filter_mono inf_le_left
    filter_upwards [hb.continuous.continuousAt
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V p.2.proj))] with z hz
    change (e ⟨z.2.proj, (Real.sqrt (D z))⁻¹ • z.2.2⟩).2 =
      (Real.sqrt (D z))⁻¹ • (e z.2).2
    simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hz, map_smul]
  · change (e ⟨p.2.proj, (Real.sqrt (D p))⁻¹ • p.2.2⟩).2 =
      (Real.sqrt (D p))⁻¹ • (e p.2).2
    simp only [← e.continuousLinearMapAt_apply_of_mem ℝ
      (mem_baseSet_trivializationAt F V p.2.proj), map_smul]

end AtiyahSinger
