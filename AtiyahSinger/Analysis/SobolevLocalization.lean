/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSobolev
public import AtiyahSinger.Geometry.ChartLocalization

import AtiyahSinger.Analysis.SobolevCoordinateChange
import AtiyahSinger.Analysis.SobolevMultiplication

/-!
# Sobolev bounds for actual bundle localizations and extensions

Public module ID: M1000.

Compact overlaps of the original charts and frames give a cutoff coordinate pullback
followed by a compact smooth matrix multiplier. The real-order Euclidean bounds give
uniform estimates for these same maps. Finite partition sums then compare localizations
with the specified global Hilbert norm, without additional fiber metric hypotheses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff SchwartzMap

set_option maxSynthPendingDepth 20

section GeneralFibers

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

omit [T2Space M] [SecondCountableTopology M] in
open Classical in
/-- A compactly supported section transfers between the original chart and frame
coordinates by a bounded operator at every real Sobolev order. -/
private theorem exists_chartTransfer_sobolev
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e f : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (χ ψ : M → ℝ) (hcχ : HasCompactSupport χ)
    (hχ : tsupport χ ⊆ c.source ∩ e.baseSet)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ)
    (hsψ : tsupport ψ ⊆ d.source ∩ f.baseSet) (s : ℝ) :
    ∃ T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ v, ‖schwartzSobolevCoordinate s (T v)‖ ≤
          C * ‖schwartzSobolevCoordinate s v‖) ∧
        ∀ (u : ∀ x, E x) (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))),
          (∀ z, v z = if z ∈ c.target then
            (χ (c.symm z) : ℂ) • (e ⟨c.symm z, u (c.symm z)⟩).2 else 0) →
          ∀ z, T v z = if z ∈ d.target then
            (ψ (d.symm z) : ℂ) • (χ (d.symm z) : ℂ) •
              (f ⟨d.symm z, u (d.symm z)⟩).2 else 0 := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let I := 𝓘(ℝ, X)
  let t := d.symm.trans c
  let U := d.target ∩ d.symm ⁻¹' (c.source ∩ (e.baseSet ∩ f.baseSet))
  have hU : IsOpen U := d.continuousOn_symm.isOpen_inter_preimage d.open_target
    (c.open_source.inter (e.open_baseSet.inter f.open_baseSet))
  have hUt : U ⊆ t.source := fun z hz ↦ ⟨hz.1, hz.2.1⟩
  let K := tsupport χ ∩ tsupport ψ
  have hK : IsCompact K := hcχ.inter_right (isClosed_tsupport ψ)
  have hKd : K ⊆ d.source := fun x hx ↦ (hsψ hx.2).1
  have hKimage : IsCompact (d '' K) := hK.image_of_continuousOn (d.continuousOn.mono hKd)
  have hKU : d '' K ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨d.map_source (hKd hx), ?_⟩
    change d.symm (d x) ∈ c.source ∩ (e.baseSet ∩ f.baseSet)
    rw [d.left_inv (hKd hx)]
    exact ⟨(hχ hx.1).1, (hχ hx.1).2, (hsψ hx.2).2⟩
  -- One compact plateau captures exactly the common support, inside the actual overlap.
  obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
    exists_open_between_and_isCompact_closure hKimage hU hKU
  obtain ⟨η, hη, _, hsη, honeη⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hOo hKimage.isClosed hKO
  have hηsupport : tsupport η = closure O := congrArg closure hsη
  have hcη : HasCompactSupport η := by simpa [HasCompactSupport, hηsupport] using hOc
  have hηU : tsupport η ⊆ U := by rwa [hηsupport]
  have hηone (x : M) (hx : x ∈ K) : η (d x) = 1 :=
    (honeη _).mp ⟨x, hx, rfl⟩
  have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
  have ht : ContDiffOn ℝ ∞ t t.source := by
    intro z hz
    exact (((contMDiffAt_of_mem_maximalAtlas hcM hz.2).comp z
      (contMDiffAt_symm_of_mem_maximalAtlas hdM hz.1)).contDiffAt).contDiffWithinAt
  have hts : ContDiffOn ℝ ∞ t.symm t.target := by
    intro z hz
    exact (((contMDiffAt_of_mem_maximalAtlas hdM hz.2).comp z
      (contMDiffAt_symm_of_mem_maximalAtlas hcM hz.1)).contDiffAt).contDiffWithinAt
  have hdU : ContMDiffOn I I ∞ d.symm U := by
    intro z hz
    exact (contMDiffAt_symm_of_mem_maximalAtlas hdM hz.1).contMDiffWithinAt
  let F : X → V →L[ℂ] V := fun z ↦ (ψ (d.symm z) : ℂ) •
    (e.coordChangeL ℂ f (d.symm z)).toContinuousLinearMap
  have hF : ContDiffOn ℝ ∞ F U := by
    have hcoord := (IsSmoothComplexBundle.contMDiffOn_coordChange e f).comp hdU
      (fun z hz ↦ hz.2.2)
    have hscalar := (Complex.ofRealCLM.contMDiff.comp hψ).comp_contMDiffOn hdU
    exact hscalar.contDiffOn.smul hcoord.contDiffOn
  let G := cutoffMatrix η F
  have hG : ContDiff ℝ ∞ G := contDiff_cutoffMatrix U hU F hF η hη hηU
  have hcG : HasCompactSupport G := hasCompactSupport_cutoffMatrix η F hcη
  let P : 𝓢(X, V) →L[ℂ] 𝓢(X, V) :=
    cutoffPullbackCLM t.source t.open_source t ht η hη hcη (hηU.trans hUt)
  let T := (matrixMultiplierCLM G hG hcG).comp P
  -- The pullback and the actual forward frame matrix preserve the same real order.
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_norm_cutoffPullback_sobolev_le (r := r) t ht hts
    η hη hcη (hηU.trans hUt) s
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_norm_matrixMultiplier_sobolev_le G hG hcG s
  refine ⟨T, C₂ * C₁, mul_nonneg hC₂ hC₁, ?_, ?_⟩
  · intro v
    apply (hb₂ (P v)).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb₁ v) hC₂
  intro u v hv z
  change matrixMultiplierCLM G hG hcG (P v) z = _
  rw [matrixMultiplierCLM_apply]
  by_cases hz : z ∈ tsupport η
  · have hzU := hηU hz
    have hxsource : d.symm z ∈ c.source := hzU.2.1
    have hctarget : t z ∈ c.target := c.map_source hxsource
    have hinv : c.symm (t z) = d.symm z := c.left_inv hxsource
    rw [show P v z = η z • v (t z) from
      cutoffPullbackCLM_apply t.source t.open_source t ht η hη hcη
        (hηU.trans hUt) v z, hv, ite_eq_left hctarget, hinv, ite_eq_left hzU.1]
    change (η z • ((ψ (d.symm z) : ℂ) •
      (e.coordChangeL ℂ f (d.symm z)).toContinuousLinearMap))
      (η z • ((χ (d.symm z) : ℂ) • (e ⟨d.symm z, u (d.symm z)⟩).2)) = _
    by_cases hxχ : χ (d.symm z) = 0
    · simp [hxχ]
    by_cases hxψ : ψ (d.symm z) = 0
    · simp [hxψ]
    have hxK : d.symm z ∈ K := ⟨subset_tsupport _ hxχ, subset_tsupport _ hxψ⟩
    have hηz : η z = 1 := by simpa only [d.right_inv hzU.1] using hηone _ hxK
    rw [hηz, one_smul, one_smul]
    simp only [smul_apply, map_smul, ContinuousLinearEquiv.coe_coe]
    rw [e.coordChangeL_apply f hzU.2.2, e.symm_apply_apply_mk hzU.2.2.1]
    exact smul_comm _ _ _
  · have hzero : η z = 0 := image_eq_zero_of_notMem_tsupport hz
    have hleft : G z = 0 := by simp [G, cutoffMatrix, hzero]
    rw [hleft, zero_apply]
    by_cases hzd : z ∈ d.target
    · rw [ite_eq_left hzd]
      by_cases hxχ : χ (d.symm z) = 0
      · simp [hxχ]
      by_cases hxψ : ψ (d.symm z) = 0
      · simp [hxψ]
      have hxK : d.symm z ∈ K := ⟨subset_tsupport _ hxχ, subset_tsupport _ hxψ⟩
      have hηz : η z = 1 := by simpa only [d.right_inv hzd] using hηone _ hxK
      exact False.elim (zero_ne_one (hzero.symm.trans hηz))
    · simp [hzd]

namespace SmoothBundlePresentation

open Classical in
/-- Any compactly localized chart expression is controlled by the original finite Sobolev norm.
The chosen frame and cutoff are retained, including their actual coordinate convention. -/
theorem exists_norm_chartLocalization_sobolev_le
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e]
    (ψ : M → ℝ) (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ)
    (hsψ : tsupport ψ ⊆ c.source ∩ e.baseSet) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : smoothSections (n := n) (r := r) E)
      (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))),
      (∀ z, v z = if z ∈ c.target then
        (ψ (c.symm z) : ℂ) • (e ⟨c.symm z, u.val (c.symm z)⟩).2 else 0) →
      ‖schwartzSobolevCoordinate s v‖ ≤ C * ‖A.smoothToSobolev s u‖ := by
  classical
  have hlocal (j : Fin A.size) := by
    let := A.frame_mem_atlas j
    exact exists_chartTransfer_sobolev (A.chart j) c (A.chart_mem_atlas j) hc
      (A.frame j) e (A.cutoff j) ψ (A.compact_support j) (A.support_subset j) hψ hsψ s
  choose T C hC hb hT using hlocal
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ ↦ hC j), ?_⟩
  intro u v hv
  -- The original partition identity reconstructs the same output Schwartz function.
  have hsum : (∑ j, T j (A.localize j u)) = v := by
    apply SchwartzMap.ext
    intro z
    simp only [sum_apply]
    simp_rw [hT _ u.val (A.localize _ u) (fun _ ↦ rfl), hv]
    by_cases hz : z ∈ c.target
    · simp only [ite_eq_left hz]
      rw [← Finset.smul_sum, ← Finset.sum_smul]
      have hcut : ∑ j, (A.cutoff j (c.symm z) : ℂ) = 1 := by
        exact_mod_cast A.sum_cutoff (c.symm z)
      rw [hcut, one_smul]
    · simp [hz]
  let L := schwartzSobolevCoordinateLinearMap n r s
  change ‖L v‖ ≤ _
  rw [← hsum, map_sum]
  calc
    ‖∑ j, L (T j (A.localize j u))‖ ≤ ∑ j, ‖L (T j (A.localize j u))‖ := norm_sum_le _ _
    _ ≤ ∑ j, C j * ‖A.smoothToSobolev s u‖ := by
      apply Finset.sum_le_sum
      intro j _
      have hinput : ‖schwartzSobolevCoordinate s (A.localize j u)‖ ≤
          ‖A.smoothToSobolev s u‖ := PiLp.norm_apply_le (A.sobolevCoordinates s u) j
      exact (hb j (A.localize j u)).trans (mul_le_mul_of_nonneg_left hinput (hC j))
    _ = (∑ j, C j) * ‖A.smoothToSobolev s u‖ := (Finset.sum_mul _ _ _).symm

end SmoothBundlePresentation

end GeneralFibers

section NormedFibers

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

namespace BundleChartCutoff

variable {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
  (A : BundleChartCutoff (r := r) E c)
  (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)

omit [SecondCountableTopology M] [∀ x, NormedSpace ℂ (E x)]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E] in
include hc in
open Classical in
/-- Pull the specified coordinate cutoff back to the base and extend it by zero. -/
private theorem exists_baseCutoff :
    ∃ χ : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ c.source ∩ A.frame.baseSet ∧
        ∀ x, χ x = if x ∈ c.source then A.cutoff (c x) else 0 := by
  classical
  let K := c.symm '' tsupport A.cutoff
  have hK : IsCompact K := A.compact_support.image_of_continuousOn
    (c.continuousOn_symm.mono (fun z hz ↦ (A.support_subset hz).1))
  have hKsub : K ⊆ c.source ∩ A.frame.baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨c.map_target (A.support_subset hz).1, (A.support_subset hz).2⟩
  let χ : M → ℝ := fun x ↦ if x ∈ c.source then A.cutoff (c x) else 0
  have hχK : tsupport χ ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    have hxs : x ∈ c.source := by
      by_contra h
      exact hx (by simp [χ, h])
    have hcxs : c x ∈ tsupport A.cutoff := by
      apply subset_tsupport
      intro hzero
      exact hx (by simp [χ, hxs, hzero])
    exact ⟨c x, hcxs, c.left_inv hxs⟩
  refine ⟨χ, ?_, hK.of_isClosed_subset (isClosed_tsupport _) hχK,
    hχK.trans hKsub, fun _ ↦ rfl⟩
  intro x
  by_cases hx : x ∈ K
  · have hxs := (hKsub hx).1
    have hcM := IsManifold.subset_maximalAtlas
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) hc
    have hlocal := A.smooth_cutoff.comp_contMDiffAt
      (contMDiffAt_of_mem_maximalAtlas hcM hxs)
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds hxs] with y hy
    simp [χ, hy]
  · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hχK h))

/-- Compact cutoff localization is bounded from the specified global Sobolev space. -/
theorem exists_norm_localize_sobolev_le
    (B : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : smoothSections (n := n) (r := r) E,
      ‖schwartzSobolevCoordinate s (A.localize hc u)‖ ≤
        C * ‖B.smoothToSobolev s u‖ := by
  classical
  let := A.frame_mem_atlas
  obtain ⟨χ, hχ, _, hsχ, hχval⟩ := A.exists_baseCutoff hc
  obtain ⟨C, hC, hb⟩ := B.exists_norm_chartLocalization_sobolev_le c hc A.frame χ hχ hsχ s
  refine ⟨C, hC, fun u ↦ hb u (A.localize hc u) ?_⟩
  intro z
  change A.localizedFunction u z = _
  by_cases hz : z ∈ c.target
  · rw [hχval, ite_eq_left (c.map_target hz), c.right_inv hz]
    simp only [localizedFunction, ite_eq_left hz, sectionInChart]
  · simp [localizedFunction, hz]

/-- Compact cutoff extension is bounded into the specified global Sobolev space. -/
theorem exists_norm_extend_sobolev_le
    (B : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ‖B.smoothToSobolev s (A.extend hc v)‖ ≤ C * ‖schwartzSobolevCoordinate s v‖ := by
  classical
  let := A.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  obtain ⟨χ, _, hcχ, hsχ, hχval⟩ := A.exists_baseCutoff hc
  let G : X → V →L[ℂ] V := fun z ↦ A.cutoff z • ContinuousLinearMap.id ℂ V
  have hG : ContDiff ℝ ∞ G := A.smooth_cutoff.smul contDiff_const
  have hcG : HasCompactSupport G := A.compact_support.smul_right
  let P := matrixMultiplierCLM G hG hcG
  obtain ⟨D, hD, hbP⟩ := exists_norm_matrixMultiplier_sobolev_le G hG hcG s
  -- The original input cutoff is applied exactly once before transferring frames.
  let raw (v : 𝓢(X, V)) (x : M) : E x := A.frame.symmL ℂ x (v (c x))
  have hinput (v : 𝓢(X, V)) (z : X) : P v z = if z ∈ c.target then
      (χ (c.symm z) : ℂ) • (A.frame ⟨c.symm z, raw v (c.symm z)⟩).2 else 0 := by
    rw [matrixMultiplierCLM_apply]
    change A.cutoff z • v z = _
    by_cases hz : z ∈ tsupport A.cutoff
    · have hzt := (A.support_subset hz).1
      have hzf := (A.support_subset hz).2
      rw [ite_eq_left hzt, hχval, ite_eq_left (c.map_target hzt), c.right_inv hzt]
      simp only [raw, c.right_inv hzt]
      rw [A.frame.symmL_apply hzf, A.frame.apply_mk_symm hzf]
      simp only [Complex.coe_smul]
    · have hzero : A.cutoff z = 0 := image_eq_zero_of_notMem_tsupport hz
      rw [hzero, zero_smul]
      by_cases hzt : z ∈ c.target
      · rw [ite_eq_left hzt, hχval, ite_eq_left (c.map_target hzt), c.right_inv hzt, hzero]
        simp
      · simp [hzt]
  have hextend (v : 𝓢(X, V)) (x : M) :
      (A.extend hc v).val x = (χ x : ℂ) • raw v x := by
    rw [hχval]
    change (if x ∈ c.source then
      (A.cutoff (c x) : ℂ) • A.frame.symmL ℂ x (v (c x)) else 0) = _
    by_cases hx : x ∈ c.source <;> simp [hx, raw]
  have hlocal (i : Fin B.size) := by
    let := B.frame_mem_atlas i
    exact exists_chartTransfer_sobolev c (B.chart i) hc (B.chart_mem_atlas i)
      A.frame (B.frame i) χ (B.cutoff i) hcχ hsχ (B.smooth_cutoff i) (B.support_subset i) s
  choose T C hC hb hT using hlocal
  refine ⟨(∑ i, C i) * D, mul_nonneg (Finset.sum_nonneg (fun i _ ↦ hC i)) hD, ?_⟩
  intro v
  -- Every output localization uses its specified forward frame, on the same section.
  have houtput (i : Fin B.size) : T i (P v) = B.localize i (A.extend hc v) := by
    let := B.frame_mem_atlas i
    apply SchwartzMap.ext
    intro z
    rw [hT i (raw v) (P v) (hinput v)]
    change _ = B.localizedFunction i (A.extend hc v) z
    by_cases hz : z ∈ (B.chart i).target
    · simp only [SmoothBundlePresentation.localizedFunction, ite_eq_left hz, sectionInChart]
      by_cases hb : B.cutoff i ((B.chart i).symm z) = 0
      · simp [hb]
      have hframe := (B.support_subset i (subset_tsupport _ hb)).2
      rw [hextend]
      have hlin := ((B.frame i).linearEquivAt ℂ _ hframe).map_smul
        (χ ((B.chart i).symm z) : ℂ) (raw v ((B.chart i).symm z))
      simp only [Trivialization.linearEquivAt_apply] at hlin
      rw [hlin]
    · simp [SmoothBundlePresentation.localizedFunction, hz]
  have hbound (i : Fin B.size) :
      ‖schwartzSobolevCoordinate s (B.localize i (A.extend hc v))‖ ≤
        C i * D * ‖schwartzSobolevCoordinate s v‖ := by
    rw [← houtput]
    apply (hb i (P v)).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbP v) (hC i)
  -- Sum the coordinate bounds in the original finite Hilbert norm.
  have hnorm : ‖B.smoothToSobolev s (A.extend hc v)‖ ≤
      ∑ i, ‖schwartzSobolevCoordinate s (B.localize i (A.extend hc v))‖ := by
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (fun (i : Fin B.size) _ ↦
        norm_nonneg (schwartzSobolevCoordinate s (B.localize i (A.extend hc v))))
    rw [← B.norm_smoothToSobolev_sq] at hsq
    have hnonneg : 0 ≤ ∑ i, ‖schwartzSobolevCoordinate s (B.localize i (A.extend hc v))‖ :=
      Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
    nlinarith [norm_nonneg (B.smoothToSobolev s (A.extend hc v))]
  calc
    ‖B.smoothToSobolev s (A.extend hc v)‖ ≤
        ∑ i, ‖schwartzSobolevCoordinate s (B.localize i (A.extend hc v))‖ := hnorm
    _ ≤ ∑ i, C i * D * ‖schwartzSobolevCoordinate s v‖ :=
      Finset.sum_le_sum (fun i _ ↦ hbound i)
    _ = (∑ i, C i) * D * ‖schwartzSobolevCoordinate s v‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]

end BundleChartCutoff

end NormedFibers

end AtiyahSinger
