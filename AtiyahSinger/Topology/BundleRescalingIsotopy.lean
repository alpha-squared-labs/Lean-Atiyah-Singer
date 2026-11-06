/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleRadialCompression
public import AtiyahSinger.Geometry.CoefficientBundleRescaling
public import AtiyahSinger.Topology.OpenEmbeddingHomotopyOperations

/-!
# Extending a rescaled bundle transition to a whole-total open isotopy

Public module ID: M1591.

A zero-fixing overlap transition whose forward and inverse fiber rescalings
are jointly continuous gives an isotopy between the two specified open maps.
A continuous nonnegative fiber quadratic form, with its open unit disk inside the
overlap, compresses all fibers before rescaling. The isotopy has an open
parameter cylinder and retains the zero section at every time.

This is the topological part of tubular uniqueness, also applicable to actual
nested maps with continuous coefficient transport. Existence of the quadratic
form and of the normalized transition remains explicit input, never an assumed
isotopy or an assumed equality of compact-support pushforwards.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Topology
open scoped unitInterval

variable {M N G : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace G V)]
  [FiberBundle G V] [VectorBundle ℝ G V]

local notation "NB" => TotalSpace G V

/-- The actual normalized rescaling extends to an open isotopy on the whole original bundle. -/
theorem exists_openIsotopy_of_rescaling
    (τ₀ τ₁ : C(NB, N)) (h₀ : IsOpenEmbedding τ₀) (h₁ : IsOpenEmbedding τ₁)
    (e : OpenPartialHomeomorph NB NB)
    (hezero : ∀ x : M, (⟨x, 0⟩ : NB) ∈ e.source)
    (hefix : ∀ x : M, e ⟨x, 0⟩ = ⟨x, 0⟩)
    (hemap : ∀ z : NB, z ∈ e.source → τ₀ (e z) = τ₁ z)
    (hR : ContinuousOn (rescaleBundleMap e)
      {p : ℝ × NB | bundleFiberScale p.1 p.2 ∈ e.source})
    (hRi : ContinuousOn (rescaleBundleMap e.symm)
      {p : ℝ × NB | bundleFiberScale p.1 p.2 ∈ e.target})
    (q : NB → ℝ) (hq : Continuous q) (hqnonneg : ∀ z, 0 ≤ q z)
    (hquad : ∀ (a : ℝ) (z : NB), q ⟨z.proj, a • z.snd⟩ = a ^ 2 * q z)
    (hqsub : ∀ z : NB, q z < 1 → z ∈ e.source) :
    ∃ H : ContinuousMap.Homotopy τ₀ τ₁,
      IsOpenEmbedding (fun p : I × NB ↦ (p.1, H p)) ∧
        ∀ (t : I) (x : M), H (t, ⟨x, 0⟩) = τ₀ ⟨x, 0⟩ := by
  have hsame (x : M) : τ₁ ⟨x, 0⟩ = τ₀ ⟨x, 0⟩ := by
    simpa only [hefix] using (hemap ⟨x, 0⟩ (hezero x)).symm
  let R := bundleRadialCompression q
  have hRzero (a : ℝ) (x : M) : R (a, (⟨x, 0⟩ : NB)) = ⟨x, 0⟩ := by
    change (⟨x, _ • (0 : V x)⟩ : NB) = _
    rw [smul_zero]
  have hR0 (z : NB) : R (0, z) = z := by
    simp only [R, bundleRadialCompression, zero_mul, add_zero, Real.sqrt_one, inv_one, one_smul]
  -- Compress at rate t² while rescaling the transition at rate t. The rescaled
  -- input always stays in the chosen disk, even for arbitrarily long fiber vectors.
  have hscaled (t : ℝ) (z : NB) : bundleFiberScale t (R (t ^ 2, z)) ∈ e.source := by
    apply hqsub
    have hden : 0 < 1 + t ^ 2 * q z :=
      add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (sq_nonneg t) (hqnonneg z))
    have hformula : q (bundleFiberScale t (R (t ^ 2, z))) =
        t ^ 2 * (1 + t ^ 2 * q z)⁻¹ * q z := by
      change q ⟨z.proj, t • ((Real.sqrt (1 + t ^ 2 * q z))⁻¹ • z.snd)⟩ = _
      rw [← mul_smul, hquad, mul_pow, inv_pow, Real.sq_sqrt hden.le]
    rw [hformula]
    calc
      t ^ 2 * (1 + t ^ 2 * q z)⁻¹ * q z =
          (t ^ 2 * q z) / (1 + t ^ 2 * q z) := by ring
      _ < 1 := (div_lt_one hden).mpr (by linarith)
  let C := bundleRadialCompressionCylinder q hq hquad
  let D := rescaleBundleOpenPartialHomeomorph (fun t : I ↦ (t : ℝ))
    continuous_subtype_val e hefix hezero hR hRi
  have hRsource (a : ℝ) (ha : 0 ≤ a) (z : NB) : (a, z) ∈ C.source := by
    change 0 < 1 + a * q z
    exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ha (hqnonneg z))
  have hscaleOne (z : NB) : bundleFiberScale (1 : ℝ) z = z := by
    change (⟨z.proj, (1 : ℝ) • z.snd⟩ : NB) = z
    rw [one_smul]
  have hscaleZero (a : ℝ) (x : M) : bundleFiberScale a (⟨x, 0⟩ : NB) = ⟨x, 0⟩ := by
    change (⟨x, a • (0 : V x)⟩ : NB) = _
    rw [smul_zero]
  have hR1source (z : NB) : R (1, z) ∈ e.source := by
    have h := hscaled 1 z
    rw [show (1 : ℝ) ^ 2 = 1 by norm_num] at h
    change (⟨(R (1, z)).proj, (1 : ℝ) • (R (1, z)).snd⟩ : NB) ∈ e.source at h
    rw [one_smul] at h
    rcases hR : R (1, z) with ⟨x, v⟩
    exact hR ▸ h
  have hRopen (a : I → ℝ) (ha : Continuous a) (hapos : ∀ t, 0 ≤ a t) :
      IsOpenEmbedding (fun p : I × NB ↦ (p.1, R (a p.1, p.2))) := by
    exact isOpenEmbedding_parameter_comp C (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) a ha
      (fun p ↦ hRsource (a p.1) (hapos p.1) p.2)
  let U (p : I × NB) : D.source := ⟨(p.1, R ((p.1 : ℝ) ^ 2, p.2)), hscaled p.1 p.2⟩
  have hU : IsOpenEmbedding U :=
    IsOpenEmbedding.of_comp U D.open_source.isOpenEmbedding_subtypeVal
      (hRopen (fun t ↦ (t : ℝ) ^ 2) (continuous_subtype_val.pow 2) (fun t ↦ sq_nonneg _))
  have hK : IsOpenEmbedding (fun p : I × NB ↦
      (p.1, τ₀
        (rescaleBundleMap e (p.1, R ((p.1 : ℝ) ^ 2, p.2))))) :=
    (IsOpenEmbedding.id.prodMap h₀).comp (D.isOpenEmbedding_restrict.comp hU)
  let c : C(NB, N) :=
    ⟨fun z ↦ τ₁ (R (1, z)),
      τ₁.continuous.comp
        ((hRopen (fun _ ↦ 1) continuous_const (fun _ ↦ zero_le_one)).continuous.snd.comp
          ((show Continuous (fun _ : NB ↦ (0 : I)) from continuous_const).prodMk
            continuous_id))⟩
  let H₀ : ContinuousMap.Homotopy τ₀ c :=
    { toFun := fun p ↦ τ₀
        (rescaleBundleMap e (p.1, R ((p.1 : ℝ) ^ 2, p.2)))
      continuous_toFun := hK.continuous.snd
      map_zero_left := fun z ↦ by
        change τ₀
          (rescaleBundleMap e (0, R ((0 : ℝ) ^ 2, z))) = _
        rw [rescaleBundleMap, ite_eq_left rfl, zero_pow (by omega), hR0]
      map_one_left := fun z ↦ by
        change τ₀
          (rescaleBundleMap e (1, R ((1 : ℝ) ^ 2, z))) = _
        rw [rescaleBundleMap, ite_eq_right (by norm_num), one_pow, inv_one]
        rw [hscaleOne, hscaleOne]
        exact hemap _ (hR1source z) }
  -- Reverse the final compression inside the second actual tube. Both segments
  -- have open cylinders, so their standard concatenation also has an open cylinder.
  have hL : IsOpenEmbedding (fun p : I × NB ↦
      (p.1, τ₁ (R (1 - p.1, p.2)))) :=
    (IsOpenEmbedding.id.prodMap h₁).comp
      (hRopen (fun t ↦ 1 - t) (continuous_const.sub continuous_subtype_val)
        (fun t ↦ sub_nonneg.mpr t.property.2))
  let H₁ : ContinuousMap.Homotopy c τ₁ :=
    { toFun := fun p ↦ τ₁ (R (1 - p.1, p.2))
      continuous_toFun := hL.continuous.snd
      map_zero_left := fun z ↦ by
        change τ₁ (R (1 - 0, z)) = _
        rw [sub_zero]
        rfl
      map_one_left := fun z ↦ by
        change τ₁ (R (1 - 1, z)) = _
        rw [sub_self, hR0] }
  have hnormalZero (t : ℝ) (x : M) :
      rescaleBundleMap e (t, (⟨x, 0⟩ : NB)) = ⟨x, 0⟩ := by
    by_cases ht : t = 0
    · simp only [rescaleBundleMap, ht, ↓reduceIte]
    · rw [rescaleBundleMap, ite_eq_right ht, hscaleZero, hefix, hscaleZero]
  have hH₀zero (t : I) (x : M) : H₀ (t, ⟨x, 0⟩) = τ₀ ⟨x, 0⟩ := by
    change τ₀
      (rescaleBundleMap e (t, R ((t : ℝ) ^ 2, ⟨x, 0⟩))) = _
    rw [hRzero, hnormalZero]
  have hH₁zero (t : I) (x : M) : H₁ (t, ⟨x, 0⟩) = τ₀ ⟨x, 0⟩ := by
    change τ₁ (R (1 - t, ⟨x, 0⟩)) = _
    rw [hRzero]
    exact hsame x
  refine ⟨H₀.trans H₁, ?_, ?_⟩
  · exact isOpenEmbedding_homotopy_trans H₀ H₁ hK hL
  · intro t x
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact hH₀zero _ x
    · exact hH₁zero _ x

end AtiyahSinger
