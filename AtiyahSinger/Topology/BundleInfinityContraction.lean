/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Reuse.Poincare.CompactDisk
public import AtiyahSinger.Topology.FiberBundleTopology
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Contraction of the bundle neighborhood of infinity

Public module ID: M1576.

Over a compact Hausdorff base, the complement of a positive-radius closed disk
bundle in the one-point compactification contracts to infinity. The radial
homotopy uses the original fiber norm and scalar multiplication. Continuity at
infinity follows from compactness of the original disks; continuity at its final
time uses the uniform positive lower bound on the norm in this same complement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Set Topology
open scoped OnePoint unitInterval

universe u v w

variable {B : Type u} [TopologicalSpace B]
  (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- Joint scalar multiplication is continuous in the original total-space topology. -/
theorem continuous_bundleFiberScale :
    Continuous (fun p : ℝ × TotalSpace F E ↦ (⟨p.2.proj, p.1 • p.2.snd⟩ : TotalSpace F E)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let e := trivializationAt F E p.2.proj
  have h := (FiberBundle.continuousAt_totalSpace F _).mp
    (continuous_snd.continuousAt (x := p))
  apply (FiberBundle.continuousAt_totalSpace F _).mpr
  refine ⟨h.1, ?_⟩
  apply (continuous_fst.continuousAt.smul h.2).congr_of_eventuallyEq
  filter_upwards [h.1.eventually (e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F E p.2.proj))] with q hq
  exact (e.linear ℝ hq).map_smul q.1 q.2.snd

/-- The actual complement of the closed native metric disk in the one-point compactification. -/
def bundleInfinityNeighborhood (a : ℝ) : Set (OnePoint (TotalSpace F E)) :=
  (((↑) : TotalSpace F E → OnePoint (TotalSpace F E)) '' {v | ‖v.snd‖ ≤ a})ᶜ

variable [CompactSpace B] [T2Space B] [FiniteDimensional ℝ F]
  [IsContinuousRiemannianBundle F E]

attribute [local instance] t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

/-- The complement of every positive-radius native disk bundle contracts to infinity. -/
theorem contractibleSpace_bundleInfinityNeighborhood (a : ℝ) (ha : 0 < a) :
    ContractibleSpace (bundleInfinityNeighborhood F E a) := by
  classical
  let V := TotalSpace F E
  let N := bundleInfinityNeighborhood F E a
  have hnorm : Continuous (fun v : V ↦ ‖v.snd‖) :=
    Poincare.VectorBundle.continuous_fiber_norm
  have hdisk (b : ℝ) : IsCompact {v : V | ‖v.snd‖ ≤ b} := by
    simpa using Poincare.VectorBundle.isCompact_disk_over
      (F := F) (E := E) (K := Set.univ) isCompact_univ b
  have hNopen : IsOpen N := OnePoint.isOpen_compl_image_coe.mpr
    ⟨(hdisk a).isClosed, hdisk a⟩
  have hinf : (∞ : OnePoint V) ∈ N := OnePoint.infty_notMem_image_coe
  have hmem (v : V) : (v : OnePoint V) ∈ N ↔ a < ‖v.snd‖ := by
    simp only [N, bundleInfinityNeighborhood, Set.mem_compl_iff, Set.mem_image,
      OnePoint.coe_eq_coe, exists_eq_right, Set.mem_ofPred_eq, not_le]
  let pinf : N := ⟨∞, hinf⟩
  let H (p : I × N) : OnePoint V :=
    if p.1 = 1 then ∞ else p.2.val.elim ∞
      (fun v ↦ (⟨v.proj, (1 - (p.1 : ℝ))⁻¹ • v.snd⟩ : V))
  have hden (t : I) (ht : t ≠ 1) : 0 < 1 - (t : ℝ) := by
    apply sub_pos.mpr
    exact lt_of_le_of_ne t.property.2 (fun h ↦ ht (Subtype.ext h))
  have hscaleNorm (t : I) (ht : t ≠ 1) (v : V) :
      ‖(1 - (t : ℝ))⁻¹ • v.snd‖ = ‖v.snd‖ / (1 - (t : ℝ)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hden t ht))]
    exact inv_mul_eq_div _ _
  have hscaleLarge (t : I) (ht : t ≠ 1) (v : V) :
      ‖v.snd‖ ≤ ‖(1 - (t : ℝ))⁻¹ • v.snd‖ := by
    rw [hscaleNorm t ht, le_div_iff₀ (hden t ht)]
    nlinarith [norm_nonneg v.snd, t.property.1]
  have hHinf (t : I) (x : N) (hx : x.val = ∞) : H (t, x) = ∞ := by
    simp [H, hx]
  have hHfinite (t : I) (ht : t ≠ 1) (x : N) (v : V) (hx : x.val = (v : OnePoint V)) :
      H (t, x) = (⟨v.proj, (1 - (t : ℝ))⁻¹ • v.snd⟩ : V) := by
    simp [H, ht, hx]
  have hHmem (p : I × N) : H p ∈ N := by
    by_cases ht : p.1 = 1
    · simpa [H, ht] using hinf
    · cases hx : p.2.val using OnePoint.rec with
      | infty => simpa [H, ht, hx] using hinf
      | coe v =>
        rw [hHfinite p.1 ht p.2 v hx, hmem]
        exact ((hmem v).mp (hx ▸ p.2.property)).trans_le (hscaleLarge p.1 ht v)
  -- Every compact target control has an upper norm bound in these same native fibers.
  have hbound (K : Set V) (hK : IsCompact K) : ∃ b : ℝ, 0 ≤ b ∧ ∀ v ∈ K, ‖v.snd‖ ≤ b := by
    obtain ⟨b, hb⟩ := hK.bddAbove_image hnorm.continuousOn
    exact ⟨max b 0, le_max_right _ _, fun v hv ↦
      (hb (Set.mem_image_of_mem _ hv)).trans (le_max_left _ _)⟩
  have hHcontinuous : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    rintro ⟨t, x⟩
    by_cases ht : t = 1
    · -- Near final time, the positive radius bounds every finite input away from zero.
      subst t
      change Tendsto H (𝓝 (1, x)) (𝓝 (H (1, x)))
      rw [show H (1, x) = ∞ by simp [H]]
      apply OnePoint.hasBasis_nhds_infty.tendsto_right_iff.mpr
      intro K hK
      obtain ⟨b, hb, hKb⟩ := hbound K hK.2
      have hδ : 0 < a / (b + 1) := div_pos ha (by linarith)
      have hevent : ∀ᶠ p : I × N in 𝓝 (1, x), 1 - (p.1 : ℝ) < a / (b + 1) :=
        (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).continuousAt
          (isOpen_Iio.mem_nhds (by simpa using hδ))
      filter_upwards [hevent] with p hp
      by_cases hpt : p.1 = 1
      · exact Or.inr (by simp [H, hpt])
      · cases hx : p.2.val using OnePoint.rec with
        | infty => exact Or.inr (hHinf p.1 p.2 hx)
        | coe v =>
          apply Or.inl
          refine ⟨⟨v.proj, (1 - (p.1 : ℝ))⁻¹ • v.snd⟩, ?_, (hHfinite p.1 hpt p.2 v hx).symm⟩
          intro hKmem
          have hv := (hmem v).mp (hx ▸ p.2.property)
          have hsmall : (1 - (p.1 : ℝ)) * (b + 1) < a :=
            (lt_div_iff₀ (by linarith : 0 < b + 1)).mp hp
          have hbig : b < ‖(1 - (p.1 : ℝ))⁻¹ • v.snd‖ := by
            rw [hscaleNorm p.1 hpt, lt_div_iff₀ (hden p.1 hpt)]
            nlinarith [hden p.1 hpt]
          exact (not_le_of_gt hbig) (hKb _ hKmem)
    · cases hx : x.val using OnePoint.rec with
      | infty =>
        -- Norms never decrease, uniformly in time, so escaping a larger disk remains escaping.
        change Tendsto H (𝓝 (t, x)) (𝓝 (H (t, x)))
        rw [hHinf t x hx]
        apply OnePoint.hasBasis_nhds_infty.tendsto_right_iff.mpr
        intro K hK
        obtain ⟨b, hb, hKb⟩ := hbound K hK.2
        have hopen : IsOpen ((((↑) : V → OnePoint V) '' {v : V | ‖v.snd‖ ≤ b})ᶜ) :=
          OnePoint.isOpen_compl_image_coe.mpr ⟨(hdisk b).isClosed, hdisk b⟩
        have hevent : ∀ᶠ p : I × N in 𝓝 (t, x),
            p.2.val ∉ (((↑) : V → OnePoint V) '' {v : V | ‖v.snd‖ ≤ b}) :=
          (continuous_subtype_val.comp continuous_snd).continuousAt
            (hopen.mem_nhds (by
              change x.val ∈ _
              rw [hx]
              exact OnePoint.infty_notMem_image_coe))
        filter_upwards [hevent] with p hp
        by_cases hpt : p.1 = 1
        · exact Or.inr (by simp [H, hpt])
        · cases hy : p.2.val using OnePoint.rec with
          | infty => exact Or.inr (hHinf p.1 p.2 hy)
          | coe v =>
            apply Or.inl
            refine ⟨⟨v.proj, (1 - (p.1 : ℝ))⁻¹ • v.snd⟩, ?_, (hHfinite p.1 hpt p.2 v hy).symm⟩
            intro hKmem
            apply hp
            refine ⟨v, ?_, hy.symm⟩
            exact (hscaleLarge p.1 hpt v).trans (hKb _ hKmem)
      | coe v =>
        -- Away from infinity and final time this is ordinary continuous fiber scaling.
        let U := {v : V | a < ‖v.snd‖}
        have hUopen : IsOpen U := isOpen_lt continuous_const hnorm
        let j : U → N := fun v ↦ ⟨v.val, (hmem v.val).mpr v.property⟩
        have hj : IsOpenEmbedding j :=
          IsOpenEmbedding.of_comp j hNopen.isOpenEmbedding_subtypeVal
            (OnePoint.isOpenEmbedding_coe.comp hUopen.isOpenEmbedding_subtypeVal)
        let vp : U := ⟨v, (hmem v).mp (hx ▸ x.property)⟩
        have hjv : j vp = x := Subtype.ext hx.symm
        have hprod := (IsOpenEmbedding.id (X := I)).prodMap hj
        rw [← hjv]
        apply (hprod.continuousAt_iff (g := H) (x := (t, vp))).mp
        have hscalar : ContinuousAt (fun p : I × U ↦ (1 - (p.1 : ℝ))⁻¹) (t, vp) :=
          (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).continuousAt.inv₀
            (ne_of_gt (hden t ht))
        have hscaled := (continuous_bundleFiberScale F E).continuousAt.comp
          (hscalar.prodMk (continuous_subtype_val.comp continuous_snd).continuousAt)
        apply (OnePoint.continuous_coe.continuousAt.comp hscaled).congr_of_eventuallyEq
        have hne : {s : I | s ≠ 1} ∈ 𝓝 t := isOpen_ne.mem_nhds ht
        have hevent : ∀ᶠ p : I × U in 𝓝 (t, vp), p.1 ≠ 1 :=
          (continuous_fst.continuousAt (x := (t, vp))).eventually hne
        filter_upwards [hevent] with p hp
        exact hHfinite p.1 hp (j p.2) p.2.val rfl
  apply (contractible_iff_id_nullhomotopic N).mpr
  refine ⟨pinf, ⟨{ toFun := fun p ↦ ⟨H p, hHmem p⟩
                   continuous_toFun := hHcontinuous.subtype_mk _
                   map_zero_left := ?_
                   map_one_left := ?_ }⟩⟩
  · intro x
    apply Subtype.ext
    change H (0, x) = x.val
    cases hx : x.val using OnePoint.rec with
    | infty => exact hHinf 0 x hx
    | coe v =>
      calc
        H (0, x) = (⟨v.proj, (1 - (0 : I).val)⁻¹ • v.snd⟩ : V) :=
          hHfinite 0 (by exact zero_ne_one) x v hx
        _ = (v : OnePoint V) := by simp
  · intro x
    apply Subtype.ext
    simp [H, pinf]

end AtiyahSinger
