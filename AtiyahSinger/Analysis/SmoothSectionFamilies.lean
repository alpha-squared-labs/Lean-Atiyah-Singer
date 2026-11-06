/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothSectionTopology

/-!
# Continuity criteria for families of smooth sections

Public module ID: M0979.

Localization into the original compactly supported Schwartz coordinates is
continuous. Joint continuity of every localized derivative, with an arbitrary
topological parameter, implies continuity in the original smooth topology.
Compactness concerns the fixed cutoff supports and imposes no condition on
the parameter space.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter
open scoped Manifold ContDiff Topology

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

namespace SmoothBundlePresentation

variable (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- The original fixed-cutoff Schwartz localization is continuous in the smooth topology. -/
theorem continuous_localize (j : Fin A.size) :
    Continuous (fun u : A.SmoothSectionSpace ↦
      A.localize j (A.smoothSectionEquiv u)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let p := A.smoothSectionSeminorm
  have hp := A.withSeminorms_smoothSectionTopology
  let K := (A.chart j) '' tsupport (A.cutoff j)
  have hK : IsCompact K :=
    (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  let T : A.SmoothSectionSpace →ₗ[ℂ] SchwartzMap X V :=
    (A.localizeLinearMap j).comp A.smoothSectionEquiv.toLinearMap
  apply hp.continuous_of_isBounded (schwartz_withSeminorms ℂ X V) T
  rintro ⟨a, b⟩
  refine ⟨{b}, ⟨R ^ a, pow_nonneg hRpos.le a⟩, ?_⟩
  intro u
  rw [Finset.sup_singleton]
  change SchwartzMap.seminorm ℂ a b (A.localize j (A.smoothSectionEquiv u)) ≤
    R ^ a * A.smoothSectionSeminorm b u
  have hnonneg : 0 ≤ R ^ a * A.smoothSectionSeminorm b u :=
    mul_nonneg (pow_nonneg hRpos.le a) (apply_nonneg _ u)
  apply SchwartzMap.seminorm_le_bound ℂ a b _ hnonneg
  intro x
  by_cases hx : x ∈ K
  · -- The original C^b supremum controls the identical localized derivative.
    have hderiv :
        ‖iteratedFDeriv ℝ b (A.localize j (A.smoothSectionEquiv u)) x‖ ≤ p b u := by
      change ‖iteratedFDeriv ℝ b
        (A.localizedCkFunction b j (A.smoothToCk b (A.smoothSectionEquiv u))) x‖ ≤
          A.ckNorm b (A.smoothToCk b (A.smoothSectionEquiv u))
      exact le_csSup (A.bddAbove_ckNorm_values b _)
        ⟨j, b, le_rfl, x, rfl⟩
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (hR x hx) a)
      hderiv (norm_nonneg _) (pow_nonneg hRpos.le a)
  · -- Derivatives vanish off that same support, including near chart boundaries.
    have hzero : iteratedFDeriv ℝ b (A.localize j (A.smoothSectionEquiv u)) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hx (A.tsupport_localizedFunction_subset j (A.smoothSectionEquiv u)
        (tsupport_iteratedFDeriv_subset b hmem))
    simpa only [hzero, norm_zero, mul_zero] using hnonneg

set_option maxHeartbeats 1000000 in
-- Compare the native Schwartz coordinates with every original Ck norm simultaneously.
/-- Joint continuity of localized jets gives continuity in the full smooth section topology. -/
theorem continuous_of_joint_localized_derivatives
    {Z : Type*} [TopologicalSpace Z] (f : Z → A.SmoothSectionSpace)
    (hf : ∀ (j : Fin A.size) (k : ℕ), Continuous
      (fun p : Z × EuclideanSpace ℝ (Fin n) ↦
        iteratedFDeriv ℝ k (A.localize j (A.smoothSectionEquiv (f p.1))) p.2)) :
    Continuous f := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro z₀
  rw [ContinuousAt, A.tendsto_smoothSectionSpace_iff]
  intro k ε hε
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let D (j : Fin A.size) (i : ℕ) (z : Z) (x : X) :=
    iteratedFDeriv ℝ i (A.localize j (A.smoothSectionEquiv (f z))) x
  have huniform (j : Fin A.size) (i : Fin (k + 1)) :
      ∀ᶠ z in 𝓝 z₀, ∀ x : X, ‖D j i.val z x - D j i.val z₀ x‖ < ε / 2 := by
    -- Each derivative has the same fixed compact support, independent of z.
    let K := (A.chart j) '' tsupport (A.cutoff j)
    have hK : IsCompact K := (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let family : Z → C(K, X [×i.val]→L[ℝ] V) := fun z ↦
      ⟨fun x ↦ D j i.val z x.val,
        (hf j i.val).comp (continuous_const.prodMk continuous_subtype_val)⟩
    have hfamily : Continuous family := ContinuousMap.continuous_of_continuous_uncurry family
      ((hf j i.val).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
      (hfamily.tendsto z₀)) Set.univ isCompact_univ
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) (ε / 2) (half_pos hε)] with z hz x
    by_cases hx : x ∈ K
    · have hb := hz ⟨x, hx⟩ (Set.mem_univ _)
      change dist (D j i.val z₀ x) (D j i.val z x) < ε / 2 at hb
      simpa only [dist_eq_norm, norm_sub_rev] using hb
    · have hzero (z : Z) : D j i.val z x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        exact hx (A.tsupport_localizedFunction_subset j (A.smoothSectionEquiv (f z))
          (tsupport_iteratedFDeriv_subset i.val hmem))
      simpa only [hzero, sub_self, norm_zero] using half_pos hε
  have hall : ∀ᶠ z in 𝓝 z₀, ∀ (j : Fin A.size) (i : Fin (k + 1)) (x : X),
      ‖D j i.val z x - D j i.val z₀ x‖ < ε / 2 :=
    Filter.eventually_all.mpr (fun j ↦ Filter.eventually_all.mpr (huniform j))
  filter_upwards [hall] with z hz
  change A.ckNorm k (A.smoothToCk k (A.smoothSectionEquiv (f z - f z₀))) < ε
  by_cases hsize : A.size = 0
  · have : IsEmpty (Fin A.size) := Fin.isEmpty_iff.mpr hsize
    simpa [ckNorm] using hε
  · apply lt_of_le_of_lt (b := ε / 2) _ (half_lt_self hε)
    unfold ckNorm
    apply csSup_le
    · obtain ⟨j⟩ := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hsize)
      exact ⟨_, j, 0, Nat.zero_le k, 0, rfl⟩
    · rintro a ⟨j, i, hi, x, rfl⟩
      have hlocal : A.localizedCkFunction k j
          (A.smoothToCk k (A.smoothSectionEquiv (f z - f z₀))) =
          (A.localize j (A.smoothSectionEquiv (f z)) : X → V) -
            (A.localize j (A.smoothSectionEquiv (f z₀)) : X → V) := by
        change (A.localizeLinearMap j (A.smoothSectionEquiv (f z - f z₀)) : X → V) = _
        rw [map_sub, map_sub]
        rfl
      rw [hlocal, iteratedFDeriv_sub_apply
        ((A.localize j (A.smoothSectionEquiv (f z))).smooth i).contDiffAt
        ((A.localize j (A.smoothSectionEquiv (f z₀))).smooth i).contDiffAt]
      exact (hz j ⟨i, Nat.lt_succ_of_le hi⟩ x).le

end SmoothBundlePresentation

end AtiyahSinger
