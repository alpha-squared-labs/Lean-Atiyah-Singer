/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleCompactSupportCharacter

/-!
# One-point comparison on the product of actual real bundle total spaces

Public module ID: M2035.

The maximum of the two original fiber norms has compact sublevel sets in the
original product topology. Simultaneous original fiber scaling contracts each
positive-radius infinity complement, with uniform escape at final time and
uniform control near infinity. The original compact-support comparison is
therefore bijective on this actual product, including rank zero.

This is the product version of the metric-disk argument in BundleInfinityContraction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Set Topology
open scoped OnePoint unitInterval

attribute [local instance] t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

universe u

set_option maxHeartbeats 1000000 in
-- Both original fiber norms and total-space topologies are kept in the simultaneous contraction.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original compact-support one-point comparison is bijective on the product of two
copies of the actual real metric bundle total space. -/
theorem compactSupportCohomologyToOnePoint_realBundleProd_bijective
    (R : Type) [CommRing R] (r : ℕ) {B : Type u} [TopologicalSpace B]
    [CompactSpace B] [T2Space B] (E : B → Type u)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
    [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin r)) E] (n : ℕ) :
    Function.Bijective (compactSupportCohomologyToOnePoint R
      (TotalSpace (EuclideanSpace ℝ (Fin r)) E ×
        TotalSpace (EuclideanSpace ℝ (Fin r)) E) n) := by
  classical
  let F := EuclideanSpace ℝ (Fin r)
  let T := TotalSpace F E
  let V := T × T
  let ρ (v : V) : ℝ := max ‖v.1.snd‖ ‖v.2.snd‖
  let scale (t : ℝ) (v : V) : V :=
    (⟨v.1.proj, t • v.1.snd⟩, ⟨v.2.proj, t • v.2.snd⟩)
  have hsingle : Continuous (fun v : T ↦ ‖v.snd‖) :=
    Poincare.VectorBundle.continuous_fiber_norm
  have hnorm : Continuous ρ := (hsingle.comp continuous_fst).max
    (hsingle.comp continuous_snd)
  have hρnonneg (v : V) : 0 ≤ ρ v := (norm_nonneg _).trans (le_max_left _ _)
  have hdisk (a : ℝ) : IsCompact {v : V | ρ v ≤ a} := by
    have hD : IsCompact {v : T | ‖v.snd‖ ≤ a} := by
      simpa using Poincare.VectorBundle.isCompact_disk_over
        (F := F) (E := E) (K := Set.univ) isCompact_univ a
    have heq : {v : V | ρ v ≤ a} = {v : T | ‖v.snd‖ ≤ a} ×ˢ
        {v : T | ‖v.snd‖ ≤ a} := by
      ext v
      change max ‖v.1.snd‖ ‖v.2.snd‖ ≤ a ↔ ‖v.1.snd‖ ≤ a ∧ ‖v.2.snd‖ ≤ a
      exact max_le_iff
    rw [heq]
    exact hD.prod hD
  have hscale : Continuous (fun p : ℝ × V ↦ scale p.1 p.2) :=
    ((continuous_bundleFiberScale F E).comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      ((continuous_bundleFiberScale F E).comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  have hscaleRadius (t : ℝ) (ht : 0 ≤ t) (v : V) : ρ (scale t v) = t * ρ v := by
    change max ‖t • v.1.snd‖ ‖t • v.2.snd‖ = t * max ‖v.1.snd‖ ‖v.2.snd‖
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    exact (mul_max_of_nonneg _ _ ht).symm
  have hcontract (a : ℝ) (ha : 0 < a) :
      ContractibleSpace ((((↑) : V → OnePoint V) '' {v : V | ρ v ≤ a})ᶜ :
        Set (OnePoint V)) := by
    let N : Set (OnePoint V) := (((↑) : V → OnePoint V) '' {v | ρ v ≤ a})ᶜ
    have hNopen : IsOpen N := OnePoint.isOpen_compl_image_coe.mpr
      ⟨(hdisk a).isClosed, hdisk a⟩
    have hinf : (∞ : OnePoint V) ∈ N := OnePoint.infty_notMem_image_coe
    have hmem (v : V) : (v : OnePoint V) ∈ N ↔ a < ρ v := by
      simp only [N, Set.mem_compl_iff, Set.mem_image,
        OnePoint.coe_eq_coe, exists_eq_right, Set.mem_ofPred_eq, not_le]
    let pinf : N := ⟨∞, hinf⟩
    let H (p : I × N) : OnePoint V :=
      if p.1 = 1 then ∞ else p.2.val.elim ∞
        (fun v ↦ (scale (1 - (p.1 : ℝ))⁻¹ v))
    have hden (t : I) (ht : t ≠ 1) : 0 < 1 - (t : ℝ) := by
      apply sub_pos.mpr
      exact lt_of_le_of_ne t.property.2 (fun h ↦ ht (Subtype.ext h))
    have hscaleNorm (t : I) (ht : t ≠ 1) (v : V) :
        ρ (scale (1 - (t : ℝ))⁻¹ v) = ρ v / (1 - (t : ℝ)) := by
      rw [hscaleRadius _ (le_of_lt (inv_pos.mpr (hden t ht)))]
      exact inv_mul_eq_div _ _
    have hscaleLarge (t : I) (ht : t ≠ 1) (v : V) :
        ρ v ≤ ρ (scale (1 - (t : ℝ))⁻¹ v) := by
      rw [hscaleNorm t ht, le_div_iff₀ (hden t ht)]
      nlinarith [hρnonneg v, t.property.1]
    have hHinf (t : I) (x : N) (hx : x.val = ∞) : H (t, x) = ∞ := by
      simp [H, hx]
    have hHfinite (t : I) (ht : t ≠ 1) (x : N) (v : V) (hx : x.val = (v : OnePoint V)) :
        H (t, x) = (scale (1 - (t : ℝ))⁻¹ v) := by
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
    have hbound (K : Set V) (hK : IsCompact K) : ∃ b : ℝ, 0 ≤ b ∧ ∀ v ∈ K, ρ v ≤ b := by
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
            refine ⟨scale (1 - (p.1 : ℝ))⁻¹ v, ?_, (hHfinite p.1 hpt p.2 v hx).symm⟩
            intro hKmem
            have hv := (hmem v).mp (hx ▸ p.2.property)
            have hsmall : (1 - (p.1 : ℝ)) * (b + 1) < a :=
              (lt_div_iff₀ (by linarith : 0 < b + 1)).mp hp
            have hbig : b < ρ (scale (1 - (p.1 : ℝ))⁻¹ v) := by
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
          have hopen : IsOpen ((((↑) : V → OnePoint V) '' {v : V | ρ v ≤ b})ᶜ) :=
            OnePoint.isOpen_compl_image_coe.mpr ⟨(hdisk b).isClosed, hdisk b⟩
          have hevent : ∀ᶠ p : I × N in 𝓝 (t, x),
              p.2.val ∉ (((↑) : V → OnePoint V) '' {v : V | ρ v ≤ b}) :=
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
              refine ⟨scale (1 - (p.1 : ℝ))⁻¹ v, ?_, (hHfinite p.1 hpt p.2 v hy).symm⟩
              intro hKmem
              apply hp
              refine ⟨v, ?_, hy.symm⟩
              exact (hscaleLarge p.1 hpt v).trans (hKb _ hKmem)
        | coe v =>
          -- Away from infinity and final time this is ordinary continuous fiber scaling.
          let U := {v : V | a < ρ v}
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
          have hscaled := hscale.continuousAt.comp
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
          H (0, x) = (scale (1 - (0 : I).val)⁻¹ v) :=
            hHfinite 0 (by exact zero_ne_one) x v hx
          _ = (v : OnePoint V) := by
            rcases v with ⟨⟨x, u⟩, ⟨y, w⟩⟩
            simp [scale]
    · intro x
      apply Subtype.ext
      simp [H, pinf]
  -- Every original compact support is contained in one of these same product disks.
  apply compactSupportCohomologyToOnePoint_bijective_of_contractible_complements R
  intro K
  obtain ⟨b, hb⟩ := K.isCompact.bddAbove_image hnorm.continuousOn
  let a : ℝ := max b 1
  refine ⟨⟨{v : V | ρ v ≤ a}, hdisk a⟩, ?_, ?_⟩
  · intro v hv
    exact (hb (Set.mem_image_of_mem _ hv)).trans (le_max_left _ _)
  · exact hcontract a (lt_of_lt_of_le zero_lt_one (le_max_right _ _))

end AtiyahSinger
