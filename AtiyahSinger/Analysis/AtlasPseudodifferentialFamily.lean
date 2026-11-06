/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialLocalSchwartzAction
public import AtiyahSinger.Analysis.AtlasPseudodifferentialParameter
public import AtiyahSinger.Analysis.CompactLocalSymbolCalculus

/-!
# Joint parameter regularity of the full original atlas PDO

Public module ID: M0283.

A finite original input presentation reconstructs every actual section using
plateau extensions. Each resulting whole-PDO local Schwartz action preserves
joint smoothness. A nonzero original output partition weight recovers the
original output coordinates locally. The smoothing remainder is retained as
part of that same operator throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Set
open scoped Manifold ContDiff SchwartzMap Topology

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

local notation "Y" => EuclideanSpace ℝ (Fin k)
local notation "X" => EuclideanSpace ℝ (Fin n)

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

variable [SecondCountableTopology M] [CompactSpace M]

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The entire original atlas PDO preserves joint smoothness in an untruncated parameter. -/
theorem AtlasPseudodifferentialOperator.contMDiffOn_apply_parameter {m : ℝ}
    (P : AtlasPseudodifferentialOperator A B m) (u : Y → A.smoothSections)
    (hu : ∀ i : A.Index,
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun p : Y × M ↦ (A.chart i ⟨p.2, (u p.1).val p.2⟩).2)
        (Set.univ ×ˢ (A.chart i).baseSet)) (i : B.Index) :
    ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (B.rank i) → ℂ) ∞
      (fun p : Y × M ↦ (B.chart i ⟨p.2, (P.toLinearMap (u p.1)).val p.2⟩).2)
      (Set.univ ×ˢ (B.chart i).baseSet) := by
  classical
  obtain ⟨L⟩ := nonempty_atlasBundlePresentation A
  obtain ⟨K⟩ := nonempty_atlasBundlePresentation B
  let U (j : Fin L.size) :=
    (L.chart j).target ∩ (L.chart j).symm ⁻¹' (A.chart (L.frameIndex j)).baseSet
  let H (j : Fin L.size) := (L.chart j) '' tsupport (L.cutoff j)
  have hU (j : Fin L.size) : IsOpen (U j) :=
    (L.chart j).isOpen_inter_preimage_symm (A.chart (L.frameIndex j)).open_baseSet
  have hH (j : Fin L.size) : IsCompact (H j) :=
    (L.compact_support j).image_of_continuousOn
      ((L.chart j).continuousOn.mono (fun x hx ↦ (L.support_subset j hx).1))
  have hHU (j : Fin L.size) : H j ⊆ U j := by
    rintro _ ⟨x, hx, rfl⟩
    have hs := (L.support_subset j hx).1
    refine ⟨(L.chart j).map_source hs, ?_⟩
    change (L.chart j).symm ((L.chart j) x) ∈ (A.chart (L.frameIndex j)).baseSet
    rw [(L.chart j).left_inv hs]
    exact (L.support_subset j hx).2
  -- Original compact input supports receive plateaus only for exact reconstruction.
  have hplateau (j : Fin L.size) : ∃ η : X → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U j ∧
        ∀ z ∈ H j, η z = 1 := by
    obtain ⟨η, hη, hcη, hsη, honeη⟩ := exists_compact_cutoff_one_near
      (H j) (U j) (hH j) (hU j) (hHU j)
    refine ⟨η, hη, hcη, hsη, fun z hz ↦ ?_⟩
    exact (show z ∈ {x | η x = 1} from interior_subset (honeη hz))
  choose η hη hcη hsη honeη using hplateau
  let D (j : Fin L.size) : AtlasChartCutoff A (L.chart j) :=
    { frameIndex := L.frameIndex j
      cutoff := η j
      smooth_cutoff := hη j
      compact_support := hcη j
      support_subset := hsη j }
  have hpiece (j : Fin L.size) (s : A.smoothSections) (x : M) :
      ((D j).extend (L.chart_mem_atlas j) (L.localize j s)).val x =
        (L.cutoff j x : ℂ) • s.val x := by
    change (D j).extendedFunction (L.localize j s) x = _
    by_cases hx : x ∈ (L.chart j).source ∩ (A.chart (L.frameIndex j)).baseSet
    · simp only [AtlasChartCutoff.extendedFunction, D, dite_eq_left hx]
      change (η j ((L.chart j) x) : ℂ) • (A.frameLinearEquiv (L.frameIndex j) x hx.2).symm
        ((EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ)
          (L.localizedFunction j s ((L.chart j) x))) = _
      simp only [AtlasBundlePresentation.localizedFunction,
        ite_eq_left ((L.chart j).map_source hx.1), atlasSectionInChart]
      rw [(L.chart j).left_inv hx.1, map_smul,
        ContinuousLinearEquiv.apply_symm_apply, map_smul]
      change _ • ((L.cutoff j x : ℂ) •
        (A.frameLinearEquiv (L.frameIndex j) x hx.2).symm
          ((A.frameLinearEquiv (L.frameIndex j) x hx.2) (s.val x))) = _
      rw [LinearEquiv.symm_apply_apply]
      by_cases hχ : L.cutoff j x = 0
      · simp [hχ]
      · rw [honeη j _ ⟨x, subset_tsupport _ hχ, rfl⟩, Complex.ofReal_one, one_smul]
    · have hχ : L.cutoff j x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hx (L.support_subset j h))
      simp [AtlasChartCutoff.extendedFunction, D, hx, hχ]
  have hreconstruct (s : A.smoothSections) :
      (∑ j, (D j).extend (L.chart_mem_atlas j) (L.localize j s)) = s := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_sum, Finset.sum_apply, hpiece]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, L.sum_cutoff, Complex.ofReal_one, one_smul]
  -- Each actual localized input is jointly smooth with its original fixed compact support.
  let f (j : Fin L.size) (y : Y) := L.localize j (u y)
  have hf (j : Fin L.size) : ContDiff ℝ ∞ (fun p : Y × X ↦ f j p.1 p.2) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p.2 ∈ H j
    · have hpt := (hHU j hp).1
      have hpf := (hHU j hp).2
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) (L.chart_mem_atlas j)) hpt
      have hpair : ContMDiffAt 𝓘(ℝ, Y × X) ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) ∞
          (fun z : Y × X ↦ (z.1, (L.chart j).symm z.2)) p :=
        contDiffAt_fst.contMDiffAt.prodMk (hchart.comp p contDiffAt_snd.contMDiffAt)
      have hsection : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X))
          𝓘(ℝ, Fin (A.rank (L.frameIndex j)) → ℂ) ∞
          (fun z : Y × M ↦ (A.chart (L.frameIndex j) ⟨z.2, (u z.1).val z.2⟩).2)
          (p.1, (L.chart j).symm p.2) := (hu (L.frameIndex j)).contMDiffAt
        ((isOpen_univ.prod (A.chart (L.frameIndex j)).open_baseSet).mem_nhds
          ⟨Set.mem_univ _, hpf⟩)
      let e := EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ
      have hcoords := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiffAt.comp p
        (hsection.comp p hpair)
      have hcutoff := Complex.ofRealCLM.contMDiffAt.comp p
        ((L.smooth_cutoff j).contMDiffAt.comp p (hchart.comp p contDiffAt_snd.contMDiffAt))
      apply (hcutoff.contDiffAt.smul hcoords.contDiffAt).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt ((L.chart j).open_target.mem_nhds hpt)]
        with z hz
      change L.localizedFunction j (u z.1) z.2 = _
      have hz' : z.2 ∈ (L.chart j).target := hz
      simp [AtlasBundlePresentation.localizedFunction, atlasSectionInChart, hz', e]
    · apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ
        (Fin (A.rank (L.frameIndex j)))))).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt ((hH j).isClosed.isOpen_compl.mem_nhds hp)]
        with z hz
      exact image_eq_zero_of_notMem_tsupport
        (fun h ↦ hz ((L.localizedFunction_properties j (u z.1)).2.1 h))
  -- The whole original P, including its smoothing remainder, acts through these same CLMs.
  have hlocalized (j : Fin K.size) : ContDiff ℝ ∞
      (fun p : Y × X ↦ K.localize j (P.toLinearMap (u p.1)) p.2) := by
    choose T hT using fun l : Fin L.size ↦
      P.exists_localActionSchwartz L K (D l) (L.chart_mem_atlas l) j
    have hreg (l : Fin L.size) : ContDiff ℝ ∞ (fun p : Y × X ↦ T l (f l p.1) p.2) :=
      contDiff_schwartzOperator_euclidean_of_common_compact_support (f l) (hf l) (H l)
        (hH l) (fun y ↦ (L.localizedFunction_properties l (u y)).2.1) (T l)
    have hsum : ContDiff ℝ ∞ (fun p : Y × X ↦ ∑ l, T l (f l p.1) p.2) := by
      apply ContDiff.sum
      intro l _
      exact hreg l
    have hequal : (fun p : Y × X ↦ K.localize j (P.toLinearMap (u p.1)) p.2) =
        (fun p : Y × X ↦ ∑ l, T l (f l p.1) p.2) := by
      funext p
      have heq := congrArg (fun s : A.smoothSections ↦
        K.localizeLinearMap j (P.toLinearMap s)) (hreconstruct (u p.1))
      simp only [map_sum] at heq
      have heval := congrArg (fun v ↦ v p.2) heq.symm
      change K.localize j (P.toLinearMap (u p.1)) p.2 =
        (∑ l, K.localize j (P.toLinearMap ((D l).extend
          (L.chart_mem_atlas l) (L.localize l (u p.1))))) p.2 at heval
      simpa only [sum_apply, hT, f] using heval
    rw [hequal]
    exact hsum
  -- A nonzero original partition weight recovers the output in one covering frame locally.
  intro p hp
  obtain ⟨j, hj⟩ : ∃ j : Fin K.size, K.cutoff j p.2 ≠ 0 := by
    by_contra! h
    have hsum := K.sum_cutoff p.2
    simp only [h, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  have hx := K.support_subset j (subset_tsupport _ hj)
  have hchart := (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) (K.chart_mem_atlas j)) hx.1).comp p
      (contMDiffAt_snd : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, X) ∞ Prod.snd p)
  let e := EuclideanSpace.equiv (Fin (B.rank (K.frameIndex j))) ℂ
  have hv := (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contMDiffAt
    ((hlocalized j).comp_contMDiffAt (contMDiffAt_fst.prodMk_space hchart))
  have hscalar : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, ℂ) ∞
      (fun w : Y × M ↦ (K.cutoff j w.2 : ℂ)) p :=
    Complex.ofRealCLM.contMDiffAt.comp p ((K.smooth_cutoff j).contMDiffAt.comp p contMDiffAt_snd)
  have hinv := (contDiffAt_inv ℝ
    (show (K.cutoff j p.2 : ℂ) ≠ 0 by exact_mod_cast hj)).comp_contMDiffAt
      (f := fun w : Y × M ↦ (K.cutoff j w.2 : ℂ)) hscalar
  have hsum : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (B.rank i) → ℂ) ∞
      (fun w : Y × M ↦ ∑ a : Fin (B.rank (K.frameIndex j)),
        (e (K.localize j (P.toLinearMap (u w.1)) (K.chart j w.2))) a •
          (B.chart i ((B.chart (K.frameIndex j)).toPartialEquiv.symm
            (w.2, Pi.single a 1))).2) p := by
    apply contMDiffAt_finsetSum
    intro a _
    have hcoeff := contMDiffAt_pi_space.mp hv a
    have hcolumn := ((B.contMDiffOn_coordChange (K.frameIndex j) i a).contMDiffAt
      (((B.chart (K.frameIndex j)).open_baseSet.inter (B.chart i).open_baseSet).mem_nhds
        ⟨hx.2, hp.2⟩)).comp p
          (contMDiffAt_snd : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X))
            𝓘(ℝ, X) ∞ Prod.snd p)
    exact (contDiff_smul (𝕜 := ℝ)).comp_contMDiffAt (hcoeff.prodMk_space hcolumn)
  have hlocal := (contDiff_smul (𝕜 := ℝ)).comp_contMDiffAt (hinv.prodMk_space hsum)
  apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
  have hopen : IsOpen {x : M | K.cutoff j x ≠ 0} :=
    isOpen_ne_fun (K.smooth_cutoff j).continuous continuous_const
  filter_upwards [continuous_snd.continuousAt ((K.chart j).open_source.mem_nhds hx.1),
    continuous_snd.continuousAt ((B.chart (K.frameIndex j)).open_baseSet.mem_nhds hx.2),
    continuous_snd.continuousAt ((B.chart i).open_baseSet.mem_nhds hp.2),
    continuous_snd.continuousAt (hopen.mem_nhds hj)] with w hwc hwj hwi hwχ
  let s := P.toLinearMap (u w.1)
  have hrecover : (K.cutoff j w.2 : ℂ)⁻¹ •
      e (K.localize j s (K.chart j w.2)) =
        (B.frameLinearEquiv (K.frameIndex j) w.2 hwj) (s.val w.2) := by
    change _ • e (K.localizedFunction j s (K.chart j w.2)) = _
    simp only [AtlasBundlePresentation.localizedFunction,
      ite_eq_left ((K.chart j).map_source hwc), atlasSectionInChart]
    rw [(K.chart j).left_inv hwc, map_smul, ContinuousLinearEquiv.apply_symm_apply,
      smul_smul, inv_mul_cancel₀ (show (K.cutoff j w.2 : ℂ) ≠ 0 by exact_mod_cast hwχ), one_smul]
    rfl
  let T := (B.frameLinearEquiv i w.2 hwi).toLinearMap.comp
    (B.frameLinearEquiv (K.frameIndex j) w.2 hwj).symm.toLinearMap
  have hexpand :
      (∑ a : Fin (B.rank (K.frameIndex j)), e (K.localize j s (K.chart j w.2)) a •
        (B.frameLinearEquiv i w.2 hwi)
          ((B.frameLinearEquiv (K.frameIndex j) w.2 hwj).symm (Pi.single a 1))) =
      (B.frameLinearEquiv i w.2 hwi)
        ((B.frameLinearEquiv (K.frameIndex j) w.2 hwj).symm
          (e (K.localize j s (K.chart j w.2)))) := by
    simpa [T, map_sum, map_smul] using congrArg T
      ((Pi.basisFun ℂ (Fin (B.rank (K.frameIndex j)))).sum_repr
        (e (K.localize j s (K.chart j w.2))))
  have hcolumn (a : Fin (B.rank (K.frameIndex j))) :
      (B.frameLinearEquiv i w.2 hwi)
          ((B.frameLinearEquiv (K.frameIndex j) w.2 hwj).symm (Pi.single a 1)) =
        (B.chart i ((B.chart (K.frameIndex j)).toPartialEquiv.symm (w.2, Pi.single a 1))).2 := by
    change (B.chart i ⟨w.2, cast (congrArg F ((B.chart (K.frameIndex j)).proj_symm_apply' hwj))
      ((B.chart (K.frameIndex j)).toOpenPartialHomeomorph.symm (w.2, Pi.single a 1)).2⟩).2 = _
    exact congrArg (fun z : TotalSpace Unit F ↦ (B.chart i z).2)
      (TotalSpace.mk_cast (F := Unit) (E := F)
        ((B.chart (K.frameIndex j)).proj_symm_apply' (x := Pi.single a 1) hwj)
        ((B.chart (K.frameIndex j)).toOpenPartialHomeomorph.symm (w.2, Pi.single a 1)).2)
  simp only [hcolumn] at hexpand
  change (B.frameLinearEquiv i w.2 hwi) (s.val w.2) =
    (K.cutoff j w.2 : ℂ)⁻¹ • ∑ a : Fin (B.rank (K.frameIndex j)),
      e (K.localize j s (K.chart j w.2)) a •
        (B.chart i ((B.chart (K.frameIndex j)).toPartialEquiv.symm
          (w.2, Pi.single a 1))).2
  rw [hexpand, ← map_smul, ← map_smul, hrecover, LinearEquiv.symm_apply_apply]

set_option maxSynthPendingDepth 20 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Joint smoothness is local in an unchanged parameter chart for the same original atlas PDO. -/
theorem AtlasPseudodifferentialOperator.contMDiffOn_apply_parameter_of_isOpen {m : ℝ}
    (L : AtlasPseudodifferentialOperator A B m) (U : Set Y) (hU : IsOpen U)
    (u : Y → A.smoothSections)
    (hu : ∀ i : A.Index,
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun p : Y × M ↦ (A.chart i ⟨p.2, (u p.1).val p.2⟩).2)
        (U ×ˢ (A.chart i).baseSet)) (j : B.Index) :
    ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (B.rank j) → ℂ) ∞
      (fun p : Y × M ↦ (B.chart j ⟨p.2, (L.toLinearMap (u p.1)).val p.2⟩).2)
      (U ×ˢ (B.chart j).baseSet) := by
  classical
  intro p hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp.1)
  let β : ContDiffBump p.1 :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hβsupport : tsupport β ⊆ U := by
    rw [β.tsupport_eq]
    intro y hy
    apply hball
    exact lt_of_le_of_lt hy (half_lt_self hε)
  let v (y : Y) : A.smoothSections := (β y : ℂ) • u y
  -- A proof-local plateau supplies a global family equal to the original one near the point.
  have hv (i : A.Index) :
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun z : Y × M ↦ (A.chart i ⟨z.2, (v z.1).val z.2⟩).2)
        (Set.univ ×ˢ (A.chart i).baseSet) := by
    intro z hz
    by_cases hb : z.1 ∈ tsupport β
    · have huAt := (hu i).contMDiffAt
        ((hU.prod (A.chart i).open_baseSet).mem_nhds ⟨hβsupport hb, hz.2⟩)
      have hβ : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, ℂ) ∞
          (fun w : Y × M ↦ (β w.1 : ℂ)) z :=
        (Complex.ofRealCLM.contDiff.comp β.contDiff).comp_contMDiffAt contMDiffAt_fst
      have hmul : ContDiff ℝ ∞
          (fun q : ℂ × (Fin (A.rank i) → ℂ) ↦ q.1 • q.2) := contDiff_smul
      have hlocal := hmul.comp_contMDiffAt (hβ.prodMk_space huAt)
      apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [continuous_snd.continuousAt ((A.chart i).open_baseSet.mem_nhds hz.2)]
        with w hw
      exact (A.linear i w.2 hw).map_smul (β w.1 : ℂ) ((u w.1).val w.2)
    · have hzero : ∀ᶠ w : Y × M in nhds z,
          (A.chart i ⟨w.2, (v w.1).val w.2⟩).2 = 0 := by
        filter_upwards [continuous_fst.continuousAt
          ((isClosed_tsupport β).isOpen_compl.mem_nhds hb),
          continuous_snd.continuousAt ((A.chart i).open_baseSet.mem_nhds hz.2)] with w hw hwi
        have hbzero : β w.1 = 0 := image_eq_zero_of_notMem_tsupport hw
        have hvzero : v w.1 = 0 := by simp only [v, hbzero, Complex.ofReal_zero, zero_smul]
        rw [hvzero]
        exact (A.linear i w.2 hwi).map_zero
      exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt
  have hresult := (L.contMDiffOn_apply_parameter A B v hv j).contMDiffAt
    ((isOpen_univ.prod (B.chart j).open_baseSet).mem_nhds ⟨Set.mem_univ _, hp.2⟩)
  -- Linearity removes the proof-local plateau exactly; the actual operator never truncates it.
  apply (hresult.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [continuous_fst.continuousAt β.eventuallyEq_one] with w hw
  have hw' : β w.1 = 1 := hw
  have hvu : v w.1 = u w.1 := by
    change (β w.1 : ℂ) • u w.1 = u w.1
    rw [hw', Complex.ofReal_one, one_smul]
  exact congrArg (fun s : A.smoothSections ↦
    (B.chart j ⟨w.2, (L.toLinearMap s).val w.2⟩).2) hvu.symm


end AtiyahSinger
