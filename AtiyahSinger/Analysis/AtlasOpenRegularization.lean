/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasOpenSymbols
public import AtiyahSinger.Analysis.CosphereRegularity

/-!
# Restriction of the prescribed radial principal symbol

Public module ID: M0270.

On each compact coordinate set a positive cotangent metric has a uniform
recovery radius. Hence restriction of the ambient radial regularization and
regularization with any metric on the open submanifold differ by a smoothing
symbol locally in the base. Both use the same original homogeneous maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M]

omit [T2Space M] in
/-- A metric radial cutoff is identically one at uniformly large coordinate frequencies. -/
theorem SmoothCotangentMetric.exists_recovery_radius
    (g : SmoothCotangentMetric (n := n) (M := M))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKc : K ⊆ c.target) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ η, R ≤ ‖η‖ →
      1 ≤ g.length (c.symm z) (covectorFromChart c (c.symm z) η) := by
  have hcov_smul (z η : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
      covectorFromChart c (c.symm z) (t • η) = t • covectorFromChart c (c.symm z) η := by
    ext v
    exact real_inner_smul_left η _ t
  have hcov_ne (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
      (η : EuclideanSpace ℝ (Fin n)) (hη : η ≠ 0) :
      covectorFromChart c (c.symm z) η ≠ 0 := by
    intro hzero
    have h := covectorInChart_covectorFromChart c hc (c.symm z) (c.map_target hz) η
    rw [hzero] at h
    have hzero' : covectorInChart c (c.symm z) 0 = 0 := by ext v; rfl
    exact hη (h.symm.trans hzero')
  let L (z η : EuclideanSpace ℝ (Fin n)) :=
    g.length (c.symm z) (covectorFromChart c (c.symm z) η)
  let S := K ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hne (η : EuclideanSpace ℝ (Fin n))
      (hη : η ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : η ≠ 0 := by
    intro hz
    simp [hz] at hη
  have hcont : ContinuousOn (Function.uncurry L) S :=
    (g.contDiffOn_length_covectorFromChart c hc).continuousOn.mono
      (fun z hz ↦ ⟨hKc hz.1, hne z.2 hz.2⟩)
  -- Positivity on the compact coordinate unit sphere gives one common lower bound.
  obtain ⟨d, hd, hlow⟩ := hS.exists_forall_le' hcont (a := 0) (by
    intro z hz
    exact g.length_pos _ _ (hcov_ne z.1 (hKc hz.1) z.2 (hne z.2 hz.2)))
  refine ⟨d⁻¹, inv_pos.mpr hd, ?_⟩
  intro z hz η hη
  have hηpos : 0 < ‖η‖ := lt_of_lt_of_le (inv_pos.mpr hd) hη
  have hηne : η ≠ 0 := norm_pos_iff.mp hηpos
  let v := ‖η‖⁻¹ • η
  have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hηne
  have hscale : ‖η‖ • v = η := by simp [v, smul_smul, norm_ne_zero_iff.mpr hηne]
  have hlen : L z η = ‖η‖ * L z v := by
    dsimp [L]
    conv_lhs => rw [← hscale, hcov_smul, g.length_smul]
    rw [abs_of_nonneg (norm_nonneg η)]
  change 1 ≤ L z η
  rw [hlen]
  have h := mul_le_mul_of_nonneg_left hη hd.le
  rw [mul_inv_cancel₀ hd.ne'] at h
  have hl := mul_le_mul_of_nonneg_left (hlow (z, v) ⟨hz, hv⟩) (norm_nonneg η)
  exact h.trans (by simpa only [Function.uncurry, mul_comm] using hl)

variable {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting the original regularization preserves the principal class for any local metric. -/
theorem atlasRegularizedSymbol_principalClass_restrictOpen
    (U : Opens M) (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := n) (M := U)) (m : ℝ)
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a) :
    atlasGlobalPrincipalSymbolClass (A.restrictOpen U) (B.restrictOpen U) m
      ⟨fun x ξ ↦ (atlasRegularizedSymbol A B g m a hs hh).val x.val ξ,
        (atlasRegularizedSymbol A B g m a hs hh).property.restrictOpen A B U⟩ =
      atlasGlobalPrincipalSymbolClass (A.restrictOpen U) (B.restrictOpen U) m
        (atlasRegularizedSymbol (A.restrictOpen U) (B.restrictOpen U) k m
          (fun x ξ ↦ a x.val ξ) (hs.restrictOpen A B U) (fun x ξ ↦ hh x.val ξ)) := by
  classical
  let p := atlasRegularizedSymbol A B g m a hs hh
  let pU : atlasGlobalSymbolSpace (A.restrictOpen U) (B.restrictOpen U) m :=
    ⟨fun x ξ ↦ p.val x.val ξ, p.property.restrictOpen A B U⟩
  let aU : AtlasSymbolFunction (n := n) (M := U) (ComplexBundle.Restrict E U)
      (ComplexBundle.Restrict F U) :=
    fun x ξ ↦ a x.val ξ
  let q := atlasRegularizedSymbol (A.restrictOpen U) (B.restrictOpen U) k m aU
    (hs.restrictOpen A B U) (fun x ξ ↦ hh x.val ξ)
  apply (atlasGlobalPrincipalSymbolClass_eq_iff _ _ m _ _).mpr
  intro d hd i j
  have hU : Nonempty U := by
    rcases hd with ⟨_, ⟨x, _⟩, _⟩
    exact ⟨x⟩
  obtain ⟨x₀, rfl⟩ := Opens.chart_eq hU hd
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x₀.val
  let d := c.subtypeRestr hU
  have hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M := chart_mem_atlas _ _
  let V := atlasSymbolChartDomain (A.restrictOpen U) (B.restrictOpen U) d i j
  let pg := atlasGlobalSymbolInChart (A.restrictOpen U) (B.restrictOpen U)
    pU.val d i j
  let pk := atlasGlobalSymbolInChart (A.restrictOpen U) (B.restrictOpen U) q.val d i j
  have hopen : IsOpen V := by
    simpa only [V, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      d.continuousOn_symm.isOpen_inter_preimage d.open_target
        (((A.restrictOpen U).chart i).open_baseSet.inter
          ((B.restrictOpen U).chart j).open_baseSet)
  have hsub : atlasGlobalSymbolInChart (A.restrictOpen U) (B.restrictOpen U)
      (pU.val - q.val) d i j = pg - pk := by
    ext z η v
    by_cases hz : d.symm z ∈ ((A.restrictOpen U).chart i).baseSet ∧
      d.symm z ∈ ((B.restrictOpen U).chart j).baseSet
    <;> simp [atlasGlobalSymbolInChart, pg, pk, hz]
  change IsSymbol V (m - 1) (atlasGlobalSymbolInChart _ _
    (pU.val - q.val) d i j)
  rw [hsub]
  have hpg := (p.property.restrictOpen A B U) d hd i j
  have hpk := q.property d hd i j
  have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry (pg - pk)) (V ×ˢ Set.univ) :=
    hpg.1.sub hpk.1
  refine ⟨hsmooth, ?_⟩
  intro K hKV hK α β
  obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hopen hKV
  have hK'd : K' ⊆ d.target := fun z hz ↦ (hK'V hz).1.1
  obtain ⟨Rg, _, hg⟩ := g.exists_recovery_radius c hc K' hK'
    (fun z hz ↦ c.subtypeRestr_target_subset hU (hK'd hz))
  obtain ⟨Rk, _, hk⟩ := k.exists_recovery_radius d hd K' hK' hK'd
  let R := max Rg Rk
  have hint : interior K' ⊆ V := interior_subset.trans hK'V
  -- The two cutoffs recover the same original symbol above one common radius.
  have hzero : ∀ z ∈ interior K', ∀ η, R ≤ ‖η‖ → (pg - pk) z η = 0 := by
    intro z hz η hη
    have hzV := hint hz
    have hpgcoord := atlasGlobalSymbolInChart_restrictOpen A B U hU c hc p.val i j z hzV η
    have hacoord := atlasGlobalSymbolInChart_restrictOpen A B U hU c hc a i j z hzV η
    have hga := (atlasRegularizedSymbolFunction_cutoff g a).2 _ _
      (hg z (interior_subset hz) η ((le_max_left _ _).trans hη))
    have hka := (atlasRegularizedSymbolFunction_cutoff k aU).2 _ _
      (hk z (interior_subset hz) η ((le_max_right _ _).trans hη))
    change pg z η - pk z η = 0
    have hpg' : pg z η = atlasGlobalSymbolInChart A B a c i j z η := by
      rw [show pg z η = atlasGlobalSymbolInChart A B p.val c i j z η from hpgcoord]
      simp only [atlasGlobalSymbolInChart, p, atlasRegularizedSymbol, hga]
    have hpk' : pk z η = atlasGlobalSymbolInChart (A.restrictOpen U)
        (B.restrictOpen U) aU d i j z η := by
      simp only [pk, q, atlasRegularizedSymbol, atlasGlobalSymbolInChart, hka]
    rw [hpg', hpk', hacoord, sub_self]
  exact (isSmoothingSymbol_of_frequency_support isOpen_interior (pg - pk) R
    (hsmooth.mono (Set.prod_mono hint subset_rfl)) hzero (m - 1)).2 K hKK' hK α β

end AtiyahSinger
