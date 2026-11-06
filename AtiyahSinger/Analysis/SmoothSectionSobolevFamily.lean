/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothCompositionFamilies
public import AtiyahSinger.Analysis.SmoothSectionFamilies

/-!
# Sobolev continuity of smooth families in the original native bundle

Public module ID: M0983.

Joint smoothness in the original finite presentation frames implies continuity
of the same section family in every real-order Sobolev completion. The proof
localizes with the original fixed compact supports, including the chart-boundary
zero extensions, then applies the existing localized-jet continuity criterion.
The parameter need not be compact and no separated expansion is used.

This is the continuity input for integrating compactly localized whole-fiber
families in the associated horizontal/vertical graph estimates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Topology

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  {V H Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] (I : ModelWithCorners ℝ V H)
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]

namespace SmoothBundlePresentation

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 800000 in
-- Native frame smoothness and fixed compact supports control all localized derivatives together.
/-- A jointly smooth family is continuous in each original real-order Sobolev completion. -/
theorem continuous_sobolev_family
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (u : Z → smoothSections (n := n) (r := r) E)
    (hu : ∀ j : Fin A.size,
      ContMDiffOn (I.prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) 𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
        (fun p : Z × M ↦ (A.frame j ⟨p.2, (u p.1).val p.2⟩).2)
        (Set.univ ×ˢ (A.frame j).baseSet)) (s : ℝ) :
    Continuous (fun z ↦ A.smoothToSobolev s (u z)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let W := EuclideanSpace ℂ (Fin r)
  have hlocal (j : Fin A.size) : ContMDiff (I.prod 𝓘(ℝ, X)) 𝓘(ℝ, W) ∞
      (fun p : Z × X ↦ A.localize j (u p.1) p.2) := by
    let c := A.chart j
    let K := c '' tsupport (A.cutoff j)
    have hK : IsCompact K := (A.compact_support j).image_of_continuousOn
      (c.continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
    intro p
    by_cases hp : p.2 ∈ K
    · obtain ⟨x, hx, hxp⟩ := hp
      have hsource := (A.support_subset j hx).1
      have hframe := (A.support_subset j hx).2
      have htarget : p.2 ∈ c.target := hxp ▸ c.map_source hsource
      have hinv : c.symm p.2 = x := by rw [← hxp, c.left_inv hsource]
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) (A.chart_mem_atlas j)) htarget
      have hparam : ContMDiffAt (I.prod 𝓘(ℝ, X)) (I.prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) ∞
          (fun q : Z × X ↦ (q.1, c.symm q.2)) p :=
        contMDiffAt_fst.prodMk (hchart.comp p contMDiffAt_snd)
      have hdom : (p.1, c.symm p.2) ∈ Set.univ ×ˢ (A.frame j).baseSet :=
        ⟨Set.mem_univ _, hinv.symm ▸ hframe⟩
      have hcoords := ((hu j).contMDiffAt
        ((isOpen_univ.prod (A.frame j).open_baseSet).mem_nhds hdom)).comp p hparam
      have hcutoff : ContMDiffAt (I.prod 𝓘(ℝ, X)) 𝓘(ℝ, ℂ) ∞
          (fun q : Z × X ↦ (A.cutoff j (c.symm q.2) : ℂ)) p :=
        Complex.ofRealCLM.contMDiffAt.comp p
          ((A.smooth_cutoff j).contMDiffAt.comp p (hchart.comp p contMDiffAt_snd))
      have hmul : ContDiff ℝ ∞ (fun q : ℂ × W ↦ q.1 • q.2) := contDiff_smul
      apply (hmul.comp_contMDiffAt (hcutoff.prodMk_space hcoords)).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt (c.open_target.mem_nhds htarget)] with q hq
      change q.2 ∈ (A.chart j).target at hq
      change A.localizedFunction j (u q.1) q.2 = _
      simp only [localizedFunction, ite_eq_left hq, sectionInChart]
      rfl
    · -- The entire localized family vanishes near every point outside its fixed compact support.
      apply (contMDiffAt_const (c := (0 : W))).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt (hK.isClosed.isOpen_compl.mem_nhds hp)]
        with q hq
      exact image_eq_zero_of_notMem_tsupport
        (fun h ↦ hq (A.tsupport_localizedFunction_subset j (u q.1) h))
  let f : Z → A.SmoothSectionSpace := fun z ↦ A.smoothSectionEquiv.symm (u z)
  have hf : Continuous f := by
    apply A.continuous_of_joint_localized_derivatives f
    intro j k
    have hj := contMDiffOn_iteratedFDeriv_parameter I isOpen_univ (hlocal j).contMDiffOn k
    have hc := continuousOn_univ.mp hj.continuousOn
    simpa only [f, LinearEquiv.apply_symm_apply] using hc
  -- The existing smooth-to-Sobolev map keeps the original presentation and original section.
  have h := (A.continuous_smoothToSobolev s).comp hf
  simpa only [Function.comp_def, f, LinearEquiv.apply_symm_apply] using h

end SmoothBundlePresentation

end AtiyahSinger
