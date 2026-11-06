/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSobolevLocalization

import AtiyahSinger.Analysis.SobolevCoordinateChange
import AtiyahSinger.Analysis.SobolevMultiplication
import AtiyahSinger.Geometry.AtlasFrame

/-!
# Sobolev localization in any compatible smooth chart

Public module ID: M0301.

The original finite atlas need not contain a newly constructed smooth chart.
Transfer its compact cutoff coordinates through the maximal smooth atlas and
reconstruct them from the unchanged original partition. The resulting actual
Schwartz function has the specified cutoff and original bundle frame, and its
real-order norm is bounded by the original finite-atlas Sobolev norm.

The compact coordinate-transfer proof extends the argument of
`AtlasSobolevLocalization` to maximal-atlas members. Raw-atlas membership is not
assumed and the original smooth sections, finite presentation and Hilbert norm
are unchanged. This is the coordinate input needed for associated-sphere
product charts whose chosen atlas certificate only exposes smooth compatibility.
Sources: SG III.3.15--3.17 and real-order compact coordinate invariance.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff SchwartzMap Topology

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {A : SmoothComplexBundleAtlas (n := n) E}

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] in
open Classical in
/-- A compactly supported section transfers between compatible smooth chart and original frame
coordinates by a bounded operator at every real Sobolev order. -/
private theorem exists_smoothChartTransfer_sobolev
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (e f : A.Index)
    (χ ψ : M → ℝ) (hcχ : HasCompactSupport χ)
    (hχ : tsupport χ ⊆ c.source ∩ (A.chart e).baseSet)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ)
    (hsψ : tsupport ψ ⊆ d.source ∩ (A.chart f).baseSet) (s : ℝ) :
    ∃ T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank e))) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank f))),
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ v, ‖schwartzSobolevCoordinate s (T v)‖ ≤
          C * ‖schwartzSobolevCoordinate s v‖) ∧
        ∀ (u : ∀ x, E x) (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank e)))),
          (∀ z, v z = if z ∈ c.target then
            (χ (c.symm z) : ℂ) • (EuclideanSpace.equiv (Fin (A.rank e)) ℂ).symm
              ((A.chart e ⟨c.symm z, u (c.symm z)⟩).2) else 0) →
          ∀ z, T v z = if z ∈ d.target then
            (ψ (d.symm z) : ℂ) • (χ (d.symm z) : ℂ) •
              (EuclideanSpace.equiv (Fin (A.rank f)) ℂ).symm
                ((A.chart f ⟨d.symm z, u (d.symm z)⟩).2) else 0 := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin (A.rank e))
  let W := EuclideanSpace ℂ (Fin (A.rank f))
  let ev := EuclideanSpace.equiv (Fin (A.rank e)) ℂ
  let ew := EuclideanSpace.equiv (Fin (A.rank f)) ℂ
  let I := 𝓘(ℝ, X)
  let t := d.symm.trans c
  let U := d.target ∩ d.symm ⁻¹' (c.source ∩ ((A.chart e).baseSet ∩ (A.chart f).baseSet))
  have hU : IsOpen U := d.continuousOn_symm.isOpen_inter_preimage d.open_target
    (c.open_source.inter ((A.chart e).open_baseSet.inter (A.chart f).open_baseSet))
  have hUt : U ⊆ t.source := fun z hz ↦ ⟨hz.1, hz.2.1⟩
  let K := tsupport χ ∩ tsupport ψ
  have hK : IsCompact K := hcχ.inter_right (isClosed_tsupport ψ)
  have hKd : K ⊆ d.source := fun x hx ↦ (hsψ hx.2).1
  have hKimage : IsCompact (d '' K) := hK.image_of_continuousOn (d.continuousOn.mono hKd)
  have hKU : d '' K ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨d.map_source (hKd hx), ?_⟩
    change d.symm (d x) ∈ c.source ∩ ((A.chart e).baseSet ∩ (A.chart f).baseSet)
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
  have hcM := hc
  have hdM := hd
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
  -- The rectangular frame matrix is the finite sum of its original transition columns.
  let p (a : Fin (A.rank e)) : V →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj a).comp ev.toContinuousLinearMap
  let H (x : M) : V →L[ℂ] W := ∑ a : Fin (A.rank e),
    ContinuousLinearMap.smulRightL ℂ V W (p a)
      (ew.symm ((A.chart f ((A.chart e).toPartialEquiv.symm (x, Pi.single a 1))).2))
  have hH : ContDiffOn ℝ ∞ (fun z ↦ H (d.symm z)) U := by
    apply ContDiffOn.sum
    intro a _
    have hcol := (A.contMDiffOn_coordChange e f a).comp hdU (fun z hz ↦ hz.2.2)
    have hvec := (ew.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn
      hcol.contDiffOn
    exact ((ContinuousLinearMap.smulRightL ℂ V W (p a)).restrictScalars ℝ).contDiff
      |>.comp_contDiffOn hvec
  have hHapply (x : M) (he : x ∈ (A.chart e).baseSet)
      (hf : x ∈ (A.chart f).baseSet) (v : E x) :
      H x (ev.symm ((A.chart e ⟨x, v⟩).2)) = ew.symm ((A.chart f ⟨x, v⟩).2) := by
    let R := (A.frameLinearEquiv f x hf).toLinearMap.comp
      (A.frameLinearEquiv e x he).symm.toLinearMap
    have hexpand := congrArg R ((Pi.basisFun ℂ (Fin (A.rank e))).sum_repr
      ((A.frameLinearEquiv e x he) v))
    simp [R, map_sum, map_smul] at hexpand
    have hcolumn (a : Fin (A.rank e)) :
        (A.frameLinearEquiv f x hf) ((A.frameLinearEquiv e x he).symm (Pi.single a 1)) =
          (A.chart f ((A.chart e).toPartialEquiv.symm (x, Pi.single a 1))).2 := by
      change (A.chart f ⟨x, cast (congrArg E ((A.chart e).proj_symm_apply' he))
        ((A.chart e).toOpenPartialHomeomorph.symm (x, Pi.single a 1)).2⟩).2 = _
      have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
        ((A.chart e).proj_symm_apply' (x := Pi.single a 1) he)
        ((A.chart e).toOpenPartialHomeomorph.symm (x, Pi.single a 1)).2
      exact congrArg (fun z : TotalSpace Unit E ↦ (A.chart f z).2) hpoint
    simp only [hcolumn] at hexpand
    apply ew.injective
    simpa [H, p, map_sum, map_smul, ContinuousLinearMap.smulRightL_apply_apply,
      SmoothComplexBundleAtlas.frameLinearEquiv] using hexpand
  let F : X → V →L[ℂ] W := fun z ↦ (ψ (d.symm z) : ℂ) • H (d.symm z)
  have hF : ContDiffOn ℝ ∞ F U := by
    have hscalar := (Complex.ofRealCLM.contMDiff.comp hψ).comp_contMDiffOn hdU
    exact hscalar.contDiffOn.smul hH
  let G := cutoffMatrix η F
  have hG : ContDiff ℝ ∞ G := contDiff_cutoffMatrix U hU F hF η hη hηU
  have hcG : HasCompactSupport G := hasCompactSupport_cutoffMatrix η F hcη
  let P : 𝓢(X, V) →L[ℂ] 𝓢(X, V) :=
    cutoffPullbackCLM t.source t.open_source t ht η hη hcη (hηU.trans hUt)
  let T := (matrixMultiplierCLM G hG hcG).comp P
  -- The pullback and the actual forward frame matrix preserve the same real order.
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_norm_cutoffPullback_sobolev_le (r := A.rank e) t ht hts
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
      H (d.symm z)))
      (η z • ((χ (d.symm z) : ℂ) • ev.symm ((A.chart e ⟨d.symm z, u (d.symm z)⟩).2))) = _
    by_cases hxχ : χ (d.symm z) = 0
    · simp [hxχ]
    by_cases hxψ : ψ (d.symm z) = 0
    · simp [hxψ]
    have hxK : d.symm z ∈ K := ⟨subset_tsupport _ hxχ, subset_tsupport _ hxψ⟩
    have hηz : η z = 1 := by simpa only [d.right_inv hzU.1] using hηone _ hxK
    rw [hηz, one_smul, one_smul]
    simp only [smul_apply, map_smul]
    rw [hHapply _ hzU.2.2.1 hzU.2.2.2]
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

namespace AtlasChartCutoff

variable {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
  (D : AtlasChartCutoff A c)
  (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [SecondCountableTopology M] in
include hc in
open Classical in
/-- Transfer the specified coordinate cutoff to the base without changing its support or values. -/
private theorem exists_smoothBaseCutoff :
    ∃ χ : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ c.source ∩ (A.chart D.frameIndex).baseSet ∧
        ∀ x, χ x = if x ∈ c.source then D.cutoff (c x) else 0 := by
  classical
  let K := c.symm '' tsupport D.cutoff
  have hK : IsCompact K := D.compact_support.image_of_continuousOn
    (c.continuousOn_symm.mono (fun z hz ↦ (D.support_subset hz).1))
  have hKsub : K ⊆ c.source ∩ (A.chart D.frameIndex).baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨c.map_target (D.support_subset hz).1, (D.support_subset hz).2⟩
  let χ : M → ℝ := fun x ↦ if x ∈ c.source then D.cutoff (c x) else 0
  have hχK : tsupport χ ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    have hxs : x ∈ c.source := by
      by_contra h
      exact hx (by simp [χ, h])
    have hcxs : c x ∈ tsupport D.cutoff := by
      apply subset_tsupport
      intro hzero
      exact hx (by simp [χ, hxs, hzero])
    exact ⟨c x, hcxs, c.left_inv hxs⟩
  refine ⟨χ, ?_, hK.of_isClosed_subset (isClosed_tsupport _) hχK,
    hχK.trans hKsub, fun _ ↦ rfl⟩
  intro x
  by_cases hx : x ∈ K
  · have hxs := (hKsub hx).1
    have hcM := hc
    have hlocal := D.smooth_cutoff.comp_contMDiffAt
      (contMDiffAt_of_mem_maximalAtlas hcM hxs)
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds hxs] with y hy
    simp [χ, hy]
  · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hχK h))

include hc in
/-- A compact cutoff in any compatible smooth chart gives the actual bounded localization
of the unchanged original smooth sections. -/
theorem exists_localize_sobolev_of_mem_maximalAtlas
    (L : AtlasBundlePresentation A) (s : ℝ) :
    ∃ R : A.smoothSections →ₗ[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D.frameIndex))),
      (∀ u z, R u z = D.localizedFunction u z) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.smoothSections,
          ‖schwartzSobolevCoordinate s (R u)‖ ≤ C * ‖L.smoothToSobolev s u‖ := by
  classical
  obtain ⟨ψ, hψ, _, hsψ, hψval⟩ := D.exists_smoothBaseCutoff hc
  have hlocal (j : Fin L.size) :=
    exists_smoothChartTransfer_sobolev (L.chart j) c
      (IsManifold.subset_maximalAtlas (L.chart_mem_atlas j)) hc
      (L.frameIndex j) D.frameIndex (L.cutoff j) ψ (L.compact_support j)
      (L.support_subset j) hψ hsψ s
  choose T C hC hb hT using hlocal
  let R := ∑ j, (T j).toLinearMap.comp (L.localizeLinearMap j)
  refine ⟨R, ?_, ∑ j, C j, Finset.sum_nonneg (fun j _ ↦ hC j), ?_⟩
  · -- The same original partition reconstructs the exact new-chart cutoff coordinates.
    intro u z
    change (∑ j, (T j).toLinearMap.comp (L.localizeLinearMap j)) u z = _
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    change (∑ j, T j (L.localize j u)) z = _
    simp only [sum_apply]
    simp_rw [hT _ u.val (L.localize _ u) (fun _ ↦ rfl)]
    by_cases hz : z ∈ c.target
    · simp only [ite_eq_left hz, localizedFunction, atlasSectionInChart]
      rw [← Finset.smul_sum, ← Finset.sum_smul]
      have hcut : ∑ j, (L.cutoff j (c.symm z) : ℂ) = 1 := by
        exact_mod_cast L.sum_cutoff (c.symm z)
      rw [hcut, one_smul, hψval, ite_eq_left (c.map_target hz), c.right_inv hz]
    · simp [localizedFunction, hz]
  · -- Sum the transferred estimates in the original finite Hilbert norm.
    intro u
    let Q := schwartzSobolevCoordinateLinearMap n (A.rank D.frameIndex) s
    change ‖Q ((∑ j, (T j).toLinearMap.comp (L.localizeLinearMap j)) u)‖ ≤ _
    rw [LinearMap.sum_apply, map_sum]
    calc
      ‖∑ j, Q (T j (L.localize j u))‖ ≤ ∑ j, ‖Q (T j (L.localize j u))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j, C j * ‖L.smoothToSobolev s u‖ := by
        apply Finset.sum_le_sum
        intro j _
        have hinput : ‖schwartzSobolevCoordinate s (L.localize j u)‖ ≤
            ‖L.smoothToSobolev s u‖ := PiLp.norm_apply_le (L.sobolevCoordinates s u) j
        exact (hb j (L.localize j u)).trans (mul_le_mul_of_nonneg_left hinput (hC j))
      _ = (∑ j, C j) * ‖L.smoothToSobolev s u‖ := (Finset.sum_mul _ _ _).symm

include hc in
/-- Compact inverse-frame extension from any compatible smooth chart is bounded into the
same original finite-atlas Sobolev space. -/
theorem exists_extend_sobolev_of_mem_maximalAtlas
    (L : AtlasBundlePresentation A) (s : ℝ) :
    ∃ O : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D.frameIndex)))
        →ₗ[ℂ] A.smoothSections,
      (∀ v x, (O v).val x = D.extendedFunction v x) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D.frameIndex))),
            ‖L.smoothToSobolev s (O v)‖ ≤ C * ‖schwartzSobolevCoordinate s v‖ := by
  classical
  -- The same inverse original frame extends smoothly across the compact cutoff boundary.
  have hextsmooth
      (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D.frameIndex)))) :
      A.IsSmoothSection (D.extendedFunction v) := by
    classical
    have hvanish (x : M) (hx : x ∉ c.symm '' tsupport D.cutoff) :
        D.extendedFunction v x = 0 := by
      by_cases hvalid : x ∈ c.source ∩ (A.chart D.frameIndex).baseSet
      · have hcut : c x ∉ tsupport D.cutoff := by
          intro hcut
          exact hx ⟨c x, hcut, c.left_inv hvalid.1⟩
        simp [extendedFunction, hvalid, image_eq_zero_of_notMem_tsupport hcut]
      · simp [extendedFunction, hvalid]
    have hcompact : IsCompact (c.symm '' tsupport D.cutoff) :=
      D.compact_support.image_of_continuousOn
        (c.continuousOn_symm.mono (fun z hz ↦ (D.support_subset hz).1))
    intro j x hxj
    by_cases hx : x ∈ c.symm '' tsupport D.cutoff
    · obtain ⟨z, hz, rfl⟩ := hx
      have hzchart := (D.support_subset hz).1
      have hxsource := c.map_target hzchart
      have hxframe := (D.support_subset hz).2
      have hchart := contMDiffAt_of_mem_maximalAtlas
        hc hxsource
      -- Recover every output coordinate by the original smooth transition columns.
      let e := EuclideanSpace.equiv (Fin (A.rank D.frameIndex)) ℂ
      have hvector := (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contMDiffAt
        ((v.smooth ⊤).comp_contMDiffAt hchart)
      have hcutoff :=
        (Complex.ofRealCLM.contDiff.comp D.smooth_cutoff).comp_contMDiffAt hchart
      have hsum : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
          (fun y ↦ ∑ k : Fin (A.rank D.frameIndex),
            ((EuclideanSpace.equiv (Fin (A.rank D.frameIndex)) ℂ) (v (c y))) k •
              (A.chart j ((A.chart D.frameIndex).toPartialEquiv.symm
                (y, Pi.single k 1))).2) (c.symm z) := by
        apply contMDiffAt_finsetSum
        intro k _
        have hcoeff := contMDiffAt_pi_space.mp hvector k
        have hcolumn := (A.contMDiffOn_coordChange D.frameIndex j k).contMDiffAt
          (((A.chart D.frameIndex).open_baseSet.inter
            (A.chart j).open_baseSet).mem_nhds ⟨hxframe, hxj⟩)
        have hmul : ContDiff ℝ ∞
            (fun p : ℂ × (Fin (A.rank j) → ℂ) ↦ p.1 • p.2) := contDiff_smul
        exact hmul.comp_contMDiffAt (hcoeff.prodMk_space hcolumn)
      have hmul : ContDiff ℝ ∞
          (fun p : ℂ × (Fin (A.rank j) → ℂ) ↦ p.1 • p.2) := contDiff_smul
      have hlocal := hmul.comp_contMDiffAt (hcutoff.prodMk_space hsum)
      apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [c.open_source.mem_nhds hxsource,
        (A.chart D.frameIndex).open_baseSet.mem_nhds hxframe,
        (A.chart j).open_baseSet.mem_nhds hxj] with y hyc hyi hyj
      simp only [extendedFunction,
        dite_eq_left (show y ∈ c.source ∩ (A.chart D.frameIndex).baseSet from ⟨hyc, hyi⟩)]
      rw [(A.linear j y hyj).map_smul]
      congr 1
      let T := (A.frameLinearEquiv j y hyj).toLinearMap.comp
        (A.frameLinearEquiv D.frameIndex y hyi).symm.toLinearMap
      have hexpand := congrArg T ((Pi.basisFun ℂ (Fin (A.rank D.frameIndex))).sum_repr
        ((EuclideanSpace.equiv (Fin (A.rank D.frameIndex)) ℂ) (v (c y))))
      simp [T, map_sum, map_smul] at hexpand
      have hcolumn (k : Fin (A.rank D.frameIndex)) :
          (A.frameLinearEquiv j y hyj)
              ((A.frameLinearEquiv D.frameIndex y hyi).symm (Pi.single k 1)) =
            (A.chart j ((A.chart D.frameIndex).toPartialEquiv.symm (y, Pi.single k 1))).2 := by
        change (A.chart j ⟨y, cast (congrArg E
          ((A.chart D.frameIndex).proj_symm_apply' hyi))
            ((A.chart D.frameIndex).toOpenPartialHomeomorph.symm (y, Pi.single k 1)).2⟩).2 = _
        have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
          ((A.chart D.frameIndex).proj_symm_apply' (x := Pi.single k 1) hyi)
          ((A.chart D.frameIndex).toOpenPartialHomeomorph.symm (y, Pi.single k 1)).2
        exact congrArg (fun p : TotalSpace Unit E ↦ (A.chart j p).2) hpoint
      simp only [hcolumn] at hexpand
      change (A.frameLinearEquiv j y hyj)
        ((A.frameLinearEquiv D.frameIndex y hyi).symm
          ((EuclideanSpace.equiv (Fin (A.rank D.frameIndex)) ℂ) (v (c y)))) = _
      exact hexpand.symm
    · -- The compact inverse-chart image is closed, so extension is locally zero off it.
      have hzero : ∀ᶠ y in 𝓝 x, (A.chart j ⟨y, D.extendedFunction v y⟩).2 = 0 := by
        filter_upwards [hcompact.isClosed.isOpen_compl.mem_nhds hx,
          (A.chart j).open_baseSet.mem_nhds hxj] with y hy hyj
        rw [hvanish y hy]
        exact (A.linear j y hyj).map_zero
      exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt
  let O : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D.frameIndex)))
      →ₗ[ℂ] A.smoothSections := {
    toFun v := ⟨D.extendedFunction v, hextsmooth v⟩
    map_add' u v := by
      apply Subtype.ext
      funext x
      change D.extendedFunction (u + v) x = D.extendedFunction u x + D.extendedFunction v x
      by_cases hx : x ∈ c.source ∩ (A.chart D.frameIndex).baseSet
      · simp [extendedFunction, hx, map_add, smul_add]
      · simp [extendedFunction, hx]
    map_smul' a v := by
      apply Subtype.ext
      funext x
      change D.extendedFunction (a • v) x = a • D.extendedFunction v x
      by_cases hx : x ∈ c.source ∩ (A.chart D.frameIndex).baseSet
      · simp [extendedFunction, hx, map_smul, smul_comm (D.cutoff (c x) : ℂ) a]
      · simp [extendedFunction, hx] }
  refine ⟨O, fun _ _ ↦ rfl, ?_⟩
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin (A.rank D.frameIndex))
  let ev := EuclideanSpace.equiv (Fin (A.rank D.frameIndex)) ℂ
  obtain ⟨χ, _, hcχ, hsχ, hχval⟩ := D.exists_smoothBaseCutoff hc
  let G : X → V →L[ℂ] V := fun z ↦ D.cutoff z • ContinuousLinearMap.id ℂ V
  have hG : ContDiff ℝ ∞ G := D.smooth_cutoff.smul contDiff_const
  have hcG : HasCompactSupport G := D.compact_support.smul_right
  let P := matrixMultiplierCLM G hG hcG
  obtain ⟨C₀, hC₀, hbP⟩ := exists_norm_matrixMultiplier_sobolev_le G hG hcG s
  -- The uncut inverse frame is used only on its own original base set.
  let raw (v : 𝓢(X, V)) (x : M) : E x :=
    if hx : x ∈ (A.chart D.frameIndex).baseSet then
      (A.frameLinearEquiv D.frameIndex x hx).symm (ev (v (c x))) else 0
  have hinput (v : 𝓢(X, V)) (z : X) : P v z = if z ∈ c.target then
      (χ (c.symm z) : ℂ) • ev.symm
        ((A.chart D.frameIndex ⟨c.symm z, raw v (c.symm z)⟩).2) else 0 := by
    rw [matrixMultiplierCLM_apply]
    change D.cutoff z • v z = _
    by_cases hz : z ∈ tsupport D.cutoff
    · have hzt := (D.support_subset hz).1
      have hzf : c.symm z ∈ (A.chart D.frameIndex).baseSet := (D.support_subset hz).2
      rw [ite_eq_left hzt, hχval, ite_eq_left (c.map_target hzt), c.right_inv hzt]
      have hframe : (A.chart D.frameIndex ⟨c.symm z, raw v (c.symm z)⟩).2 = ev (v z) := by
        change (A.frameLinearEquiv D.frameIndex (c.symm z) hzf) (raw v (c.symm z)) = _
        simp only [raw, dite_eq_left hzf, c.right_inv hzt, LinearEquiv.apply_symm_apply]
      rw [hframe, ev.symm_apply_apply]
      simp only [Complex.coe_smul]
    · have hzero : D.cutoff z = 0 := image_eq_zero_of_notMem_tsupport hz
      rw [hzero, zero_smul]
      by_cases hzt : z ∈ c.target
      · rw [ite_eq_left hzt, hχval, ite_eq_left (c.map_target hzt), c.right_inv hzt, hzero]
        simp
      · simp [hzt]
  have hextend (v : 𝓢(X, V)) (x : M) :
      (O v).val x = (χ x : ℂ) • raw v x := by
    rw [hχval]
    change D.extendedFunction v x = _
    by_cases hx : x ∈ c.source
    · by_cases hf : x ∈ (A.chart D.frameIndex).baseSet
      · simp [extendedFunction, raw, hx, hf, ev]
      · have hz : D.cutoff (c x) = 0 := by
          by_contra h
          have hf' : c.symm (c x) ∈ (A.chart D.frameIndex).baseSet :=
            (D.support_subset (subset_tsupport _ h)).2
          exact hf (by simpa only [c.left_inv hx] using hf')
        simp [extendedFunction, raw, hx, hf, hz]
    · simp [extendedFunction, raw, hx]
  have hlocal (i : Fin L.size) :=
    exists_smoothChartTransfer_sobolev c (L.chart i) hc
      (IsManifold.subset_maximalAtlas (L.chart_mem_atlas i))
      D.frameIndex (L.frameIndex i) χ (L.cutoff i) hcχ hsχ
      (L.smooth_cutoff i) (L.support_subset i) s
  choose T C hC hb hT using hlocal
  refine ⟨(∑ i, C i) * C₀, mul_nonneg (Finset.sum_nonneg (fun i _ ↦ hC i)) hC₀, ?_⟩
  intro v
  -- Each output localization uses its specified rectangular transition on the same section.
  have houtput (i : Fin L.size) : T i (P v) = L.localize i (O v) := by
    apply SchwartzMap.ext
    intro z
    rw [hT i (raw v) (P v) (hinput v)]
    change _ = L.localizedFunction i (O v) z
    by_cases hz : z ∈ (L.chart i).target
    · simp only [AtlasBundlePresentation.localizedFunction, ite_eq_left hz, atlasSectionInChart]
      by_cases hb : L.cutoff i ((L.chart i).symm z) = 0
      · simp [hb]
      have hframe := (L.support_subset i (subset_tsupport _ hb)).2
      rw [hextend]
      have hlin := (A.frameLinearEquiv (L.frameIndex i) _ hframe).map_smul
        (χ ((L.chart i).symm z) : ℂ) (raw v ((L.chart i).symm z))
      change (A.chart (L.frameIndex i) ⟨_, _⟩).2 = _ at hlin
      rw [hlin, map_smul]
      rfl
    · simp [AtlasBundlePresentation.localizedFunction, hz]
  have hbound (i : Fin L.size) :
      ‖schwartzSobolevCoordinate s (L.localize i (O v))‖ ≤
        C i * C₀ * ‖schwartzSobolevCoordinate s v‖ := by
    rw [← houtput]
    apply (hb i (P v)).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbP v) (hC i)
  -- Sum the coordinate bounds in the original finite Hilbert norm.
  have hnorm : ‖L.smoothToSobolev s (O v)‖ ≤
      ∑ i, ‖schwartzSobolevCoordinate s (L.localize i (O v))‖ := by
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (fun (i : Fin L.size) _ ↦
        norm_nonneg (schwartzSobolevCoordinate s (L.localize i (O v))))
    rw [← L.norm_smoothToSobolev_sq] at hsq
    have hn : 0 ≤ ∑ i, ‖schwartzSobolevCoordinate s (L.localize i (O v))‖ :=
      Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
    nlinarith [norm_nonneg (L.smoothToSobolev s (O v))]
  calc
    ‖L.smoothToSobolev s (O v)‖ ≤
        ∑ i, ‖schwartzSobolevCoordinate s (L.localize i (O v))‖ := hnorm
    _ ≤ ∑ i, C i * C₀ * ‖schwartzSobolevCoordinate s v‖ :=
      Finset.sum_le_sum (fun i _ ↦ hbound i)
    _ = (∑ i, C i) * C₀ * ‖schwartzSobolevCoordinate s v‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]

end AtlasChartCutoff

end AtiyahSinger
