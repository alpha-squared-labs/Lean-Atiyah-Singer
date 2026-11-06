/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSectionTopology

import AtiyahSinger.Analysis.EquivariantSectionSupport
import AtiyahSinger.Analysis.SmoothCompositionFamilies
import AtiyahSinger.Analysis.SmoothSectionFamilies
import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Smooth section action under the original averaging hypotheses

Public module ID: M0571.

The group parameter is only a topological group with a manifold structure and
smooth actions on the original base and fibers. Smoothness of group inversion
is not assumed. Use two independent manifold parameters for the forward fiber
action and the inverse-moving base point, take derivatives only in the base,
and then restrict all continuous jets along the continuous map `g ↦ (g, g⁻¹)`.
This supplies the weaker continuity interface required by original PDO averaging.
The existing smooth section topology and geometric representation are unchanged.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothBundlePresentation

open Bundle ComplexBundle
open scoped Manifold ContDiff Topology

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  (A : SmoothBundlePresentation (n := n) (r := r) E)

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (hσ : σ.IsSmooth (n := n) (r := r) IG)

set_option maxHeartbeats 3000000 in
-- Track finite jets, moving bundle frames, and the original seminorm topology together.
include hM hT hSC hE hG hAction in
/-- The original geometric action is jointly continuous in the full smooth section topology. -/
theorem continuous_smoothSectionAction_of_isManifold :
    Continuous (fun p : G × A.SmoothSectionSpace ↦
      A.smoothSectionEquiv.symm
        ((σ.smoothSectionRepresentation IG hσ p.1) (A.smoothSectionEquiv p.2))) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let X := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℂ (Fin r)
  let I := 𝓘(ℝ, X)
  let ρ := σ.smoothSectionRepresentation IG hσ
  let action (p : G × A.SmoothSectionSpace) : A.SmoothSectionSpace :=
    A.smoothSectionEquiv.symm (ρ p.1 (A.smoothSectionEquiv p.2))
  -- The topology is tested on the original finite family of compactly supported localizations.
  apply A.continuous_of_joint_localized_derivatives action
  intro j k
  apply continuous_iff_continuousAt.mpr
  intro p₀
  let c := A.chart j
  let e := A.frame j
  let K := c '' tsupport (A.cutoff j)
  have hK : IsCompact K := (A.compact_support j).image_of_continuousOn
    (c.continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  by_cases hzK : p₀.2 ∈ K
  · -- Around a support point choose one source localization whose partition weight is nonzero.
    have hz : p₀.2 ∈ c.target := by
      obtain ⟨x, hx, heq⟩ := hzK
      rw [← heq]
      exact c.map_source (A.support_subset j hx).1
    have hxe : c.symm p₀.2 ∈ e.baseSet := by
      obtain ⟨x, hx, heq⟩ := hzK
      rw [← heq, c.left_inv (A.support_subset j hx).1]
      exact (A.support_subset j hx).2
    let x (p : (G × G) × X) : M := c.symm p.2
    let y (p : (G × G) × X) : M := p.1.2 • x p
    let moved (p : (G × G) × X) : M := p.1.1 • y p
    let C : Set ((G × G) × X) := Set.univ ×ˢ c.target
    have hC : IsOpen C := isOpen_univ.prod c.open_target
    have hx : ContMDiffOn ((IG.prod IG).prod I) I ∞ x C :=
      (contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) (A.chart_mem_atlas j))).comp
        contMDiffOn_snd (fun _ hp ↦ hp.2)
    have hy : ContMDiffOn ((IG.prod IG).prod I) I ∞ y C :=
      contMDiff_fst.snd.contMDiffOn.smul hx
    have hmovedSmooth : ContMDiffOn ((IG.prod IG).prod I) I ∞ moved C :=
      contMDiff_fst.fst.contMDiffOn.smul hy
    let y₀ := y ((p₀.1.1, p₀.1.1⁻¹), p₀.2)
    obtain ⟨i, hi⟩ : ∃ i : Fin A.size, A.cutoff i y₀ ≠ 0 := by
      by_contra! hall
      have hsum := A.sum_cutoff y₀
      simp only [hall, Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    let d := A.chart i
    let f := A.frame i
    let := A.frame_mem_atlas j
    let := A.frame_mem_atlas i
    have hy₀ := A.support_subset i (subset_tsupport _ hi)
    let U : Set M := d.source ∩ f.baseSet ∩ {z | A.cutoff i z ≠ 0}
    have hU : IsOpen U := (d.open_source.inter f.open_baseSet).inter
      (isOpen_ne.preimage (A.smooth_cutoff i).continuous)
    let W : Set ((G × G) × X) := (C ∩ moved ⁻¹' e.baseSet) ∩ y ⁻¹' U
    have hW : IsOpen W := (hy.continuousOn.mono (Set.inter_subset_left)).isOpen_inter_preimage
      (hmovedSmooth.continuousOn.isOpen_inter_preimage hC e.open_baseSet) hU
    have hp₀ : ((p₀.1.1, p₀.1.1⁻¹), p₀.2) ∈ W :=
      ⟨⟨⟨Set.mem_univ _, hz⟩, by simpa [moved, y, x] using hxe⟩, ⟨hy₀, hi⟩⟩
    have hxW : ContMDiffOn ((IG.prod IG).prod I) I ∞ x W :=
      hx.mono (fun _ hp ↦ hp.1.1)
    have hyW : ContMDiffOn ((IG.prod IG).prod I) I ∞ y W :=
      hy.mono (fun _ hp ↦ hp.1.1)
    let φ (p : (G × G) × X) : X := d (y p)
    have hφ : ContMDiffOn ((IG.prod IG).prod I) I ∞ φ W :=
      (contMDiffOn_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) (A.chart_mem_atlas i))).comp
        hyW (fun _ hp ↦ hp.2.1.1)
    -- Assemble the original smooth action columns, retaining every moving-fiber transport.
    let L (p : (G × G) × X) : F →L[ℂ] F :=
      (e.continuousLinearMapAt ℂ (p.1.1 • y p)).comp
        ((σ.linearMap p.1.1 (y p)).toContinuousLinearMap.comp (f.symmL ℂ (y p)))
    have hmoved (p : (G × G) × X) (hp : p ∈ W) : p.1.1 • y p ∈ e.baseSet := by
      exact hp.1.2
    have hcol (l : Fin r) : ContMDiffOn ((IG.prod IG).prod I) 𝓘(ℝ, F) ∞
        (fun p ↦ L p (EuclideanSpace.single l 1)) W := by
      have h := (hσ f e l).comp
        (contMDiff_fst.fst.contMDiffOn.prodMk hyW)
        (fun p hp ↦ ⟨hp.2.1.2, hmoved p hp⟩)
      apply h.congr
      intro p hp
      exact e.continuousLinearMapAt_apply_of_mem ℂ (hmoved p hp) _
    have hL : ContMDiffOn ((IG.prod IG).prod I) 𝓘(ℝ, F →L[ℂ] F) ∞ L W := by
      have hsum : ContMDiffOn ((IG.prod IG).prod I) 𝓘(ℝ, F →L[ℂ] F) ∞
          (fun p ↦ ∑ l : Fin r, ContinuousLinearMap.smulRightL ℂ F F
            (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) l)
            (L p (EuclideanSpace.single l 1))) W := by
        apply contMDiffOn_finsetSum
        intro l _
        exact ((ContinuousLinearMap.smulRightL ℂ F F
          (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) l)).restrictScalars ℝ).contMDiff
          |>.comp_contMDiffOn (hcol l)
      apply hsum.congr
      intro p _
      apply ContinuousLinearMap.ext
      intro v
      simp only [sum_apply, ContinuousLinearMap.smulRightL_apply_apply]
      change L p v = ∑ l : Fin r, v l • L p (EuclideanSpace.single l 1)
      have hv := congrArg (L p) ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr v)
      simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.basisFun_repr] using hv.symm
    let b (p : (G × G) × X) : ℂ := (A.cutoff j (x p) : ℂ) / (A.cutoff i (y p) : ℂ)
    have hb : ContMDiffOn ((IG.prod IG).prod I) 𝓘(ℝ, ℂ) ∞ b W := by
      have hj := (A.smooth_cutoff j).comp_contMDiffOn hxW
      have hi := (A.smooth_cutoff i).comp_contMDiffOn hyW
      have hInv := hi.inv₀ (fun p hp ↦ hp.2.2)
      have hmul : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.1 * p.2) := contDiff_mul
      have hreal : ContMDiffOn ((IG.prod IG).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p ↦ A.cutoff j (x p) / A.cutoff i (y p)) W := by
        simpa only [div_eq_mul_inv, Function.comp_def] using hmul.contMDiff.comp_contMDiffOn
          (hj.prodMk_space hInv)
      apply (Complex.ofRealCLM.contMDiff.comp_contMDiffOn hreal).congr
      intro p _
      exact (Complex.ofReal_div _ _).symm
    let B (p : (G × G) × X) : F →L[ℂ] F := b p • L p
    have hB : ContMDiffOn ((IG.prod IG).prod I) 𝓘(ℝ, F →L[ℂ] F) ∞ B W := by
      have hs : ContDiff ℝ ∞ (fun z : ℂ × (F →L[ℂ] F) ↦ z.1 • z.2) := contDiff_smul
      exact hs.contMDiff.comp_contMDiffOn (hb.prodMk_space hL)
    -- On this one neighborhood the acted localization is a smooth matrix times a Schwartz pullback.
    let Z := G × A.SmoothSectionSpace
    let t (p : Z × X) : (G × G) × X := ((p.1.1, p.1.1⁻¹), p.2)
    have ht : Continuous t :=
      (continuous_fst.fst.prodMk continuous_fst.fst.inv).prodMk continuous_snd
    let S : Set (Z × X) := t ⁻¹' W
    have hS : IsOpen S := hW.preimage ht
    let w (z : Z) : SchwartzMap X F := A.localize i (A.smoothSectionEquiv z.2)
    have hw : Continuous w := (A.continuous_localize i).comp continuous_snd
    let ψ (z : Z) (a : X) : X := φ ((z.1, z.1⁻¹), a)
    let D (z : Z) (a : X) : F →L[ℂ] F := B ((z.1, z.1⁻¹), a)
    let H (z : Z) (a : X) : F := D z a (w z (ψ z a))
    have hψ (p : Z × X) (hp : p ∈ S) : ContDiffAt ℝ ∞ (ψ p.1) p.2 :=
      ((hφ (t p) hp).contMDiffAt (hW.mem_nhds hp)).comp_of_eq
        (contMDiffAt_const.prodMk contMDiffAt_id) rfl |>.contDiffAt
    have hD (p : Z × X) (hp : p ∈ S) : ContDiffAt ℝ ∞ (D p.1) p.2 :=
      ((hB (t p) hp).contMDiffAt (hW.mem_nhds hp)).comp_of_eq
        (contMDiffAt_const.prodMk contMDiffAt_id) rfl |>.contDiffAt
    have hdψ (l : ℕ) : ContinuousOn
        (fun p : Z × X ↦ iteratedFDeriv ℝ l (ψ p.1) p.2) S :=
      (contMDiffOn_iteratedFDeriv_parameter (IG.prod IG) hW hφ l).continuousOn.comp
        ht.continuousOn (fun _ hp ↦ hp)
    have hdD (l : ℕ) : ContinuousOn
        (fun p : Z × X ↦ iteratedFDeriv ℝ l (D p.1) p.2) S := by
      have hj := (contMDiffOn_iteratedFDeriv_parameter (Y := G × G) (X := X)
        (F := F →L[ℂ] F) (f := B) (IG.prod IG) hW hB l).continuousOn
      convert hj.comp ht.continuousOn (fun p (hp : p ∈ S) ↦ hp) using 1
      rfl
    have hψc : ContinuousOn (fun p : Z × X ↦ ψ p.1 p.2) S :=
      hφ.continuousOn.comp ht.continuousOn (fun _ hp ↦ hp)
    have hdw (l : ℕ) : ContinuousOn (fun p : Z × X ↦
        iteratedFDeriv ℝ l (w p.1) (ψ p.1 p.2)) S :=
      (continuous_iteratedFDeriv_schwartz l).continuousOn.comp
        (((hw.comp continuous_fst).continuousOn).prodMk hψc) (fun _ _ ↦ Set.mem_univ _)
    have hdc (l : ℕ) := continuousOn_iteratedFDeriv_comp_family
      (fun z : Z ↦ (w z : X → F)) ψ S
      (fun p _ ↦ (w p.1).smooth ⊤ |>.contDiffAt) hψ hdw hdψ l
    let Q (z : Z) (a : X) : (F →L[ℂ] F) × F := (D z a, w z (ψ z a))
    have hQ (p : Z × X) (hp : p ∈ S) : ContDiffAt ℝ ∞ (Q p.1) p.2 :=
      (hD p hp).prodMk (((w p.1).smooth ⊤ |>.contDiffAt).comp p.2 (hψ p hp))
    have hdQ (l : ℕ) : ContinuousOn
        (fun p : Z × X ↦ iteratedFDeriv ℝ l (Q p.1) p.2) S := by
      have hc := (ContinuousMultilinearMap.prodL (𝕜 := ℝ)
        (E := fun _ : Fin l ↦ X) (G := F →L[ℂ] F) (G' := F)).continuous.comp_continuousOn
          ((hdD l).prodMk (hdc l))
      apply hc.congr
      intro p hp
      exact iteratedFDeriv_prodMk (hD p hp)
        (((w p.1).smooth ⊤ |>.contDiffAt).comp p.2 (hψ p hp)) (by simp)
    have hwc : Continuous (fun p : SchwartzMap X F × X ↦ p.1 p.2) := by
      have hev : Continuous (fun p : BoundedContinuousFunction X F × X ↦ p.1 p.2) :=
        continuous_eval
      exact hev.comp
        (((SchwartzMap.toBoundedContinuousFunctionCLM ℝ X F).continuous.comp
          continuous_fst).prodMk continuous_snd)
    have hQc : ContinuousOn (fun p : Z × X ↦ Q p.1 p.2) S :=
      (hB.continuousOn.comp ht.continuousOn (fun _ hp ↦ hp)).prodMk
        (hwc.comp_continuousOn (((hw.comp continuous_fst).continuousOn).prodMk hψc))
    have heval : ContDiff ℝ ∞ (fun z : (F →L[ℂ] F) × F ↦ z.1 z.2) :=
      (show ContDiff ℂ ∞ (fun z : (F →L[ℂ] F) × F ↦ z.1 z.2) from
        contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
    have hdH : ContinuousOn
        (fun p : Z × X ↦ iteratedFDeriv ℝ k (H p.1) p.2) S :=
      continuousOn_iteratedFDeriv_comp_family
        (fun _ : Z ↦ fun z : (F →L[ℂ] F) × F ↦ z.1 z.2) Q S
        (fun _ _ ↦ heval.contDiffAt) hQ
        (fun l ↦ (heval.continuous_iteratedFDeriv (by simp)).continuousOn.comp
          hQc (fun _ _ ↦ Set.mem_univ _)) hdQ k
    have heq (p : Z × X) (hp : p ∈ S) :
        A.localize j (A.smoothSectionEquiv (action p.1)) p.2 = H p.1 p.2 := by
      let a := t p
      have hxT : p.2 ∈ c.target := hp.1.1.2
      have hyD : y a ∈ d.source := hp.2.1.1
      have hyF : y a ∈ f.baseSet := hp.2.1.2
      have hsource : w p.1 (ψ p.1 p.2) =
          (A.cutoff i (y a) : ℂ) • (f ⟨y a, (A.smoothSectionEquiv p.1.2).val (y a)⟩).2 := by
        change (if d (y a) ∈ d.target then
          (A.cutoff i (d.symm (d (y a))) : ℂ) •
            (f ⟨d.symm (d (y a)),
              (A.smoothSectionEquiv p.1.2).val (d.symm (d (y a)))⟩).2 else 0) = _
        simp only [ite_eq_left (d.map_source hyD), d.left_inv hyD]
        apply congrArg (fun z : TotalSpace F E ↦ (A.cutoff i (y a) : ℂ) • (f z).2)
        exact congrArg (fun z : M ↦ (⟨z, (A.smoothSectionEquiv p.1.2).val z⟩ : TotalSpace F E))
          (d.left_inv hyD)
      have htarget : A.localize j (A.smoothSectionEquiv (action p.1)) p.2 =
          (A.cutoff j (x a) : ℂ) •
            (e ⟨a.1.1 • y a, σ.linearMap a.1.1 (y a)
              ((A.smoothSectionEquiv p.1.2).val (y a))⟩).2 := by
        change A.localizedFunction j (ρ p.1.1 (A.smoothSectionEquiv p.1.2)) p.2 = _
        rw [localizedFunction, ite_eq_left hxT]
        apply congrArg (fun v : F ↦ (A.cutoff j (x a) : ℂ) • v)
        exact congrArg (fun z : TotalSpace Unit E ↦ (e ⟨z.proj, z.snd⟩).2)
          (σ.mk_sectionLinearMap a.1.1 (A.smoothSectionEquiv p.1.2).val (x a))
      rw [htarget]
      dsimp only [H, D, B]
      rw [smul_apply, hsource, map_smul]
      rw [smul_smul (b a) (A.cutoff i (y a) : ℂ)]
      have hcancel : b a * (A.cutoff i (y a) : ℂ) = (A.cutoff j (x a) : ℂ) :=
        div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hp.2.2)
      rw [hcancel]
      apply congrArg (fun v : F ↦ (A.cutoff j (x a) : ℂ) • v)
      dsimp only [L, ContinuousLinearMap.comp_apply]
      rw [f.symmL_apply hyF, f.symm_apply_apply_mk hyF]
      exact (e.continuousLinearMapAt_apply_of_mem ℂ (hmoved a hp) _).symm
    -- Equality on a neighborhood identifies the actual derivative family, including all cutoffs.
    have hjet (p : Z × X) (hp : p ∈ S) :
        iteratedFDeriv ℝ k (A.localize j (A.smoothSectionEquiv (action p.1))) p.2 =
          iteratedFDeriv ℝ k (H p.1) p.2 := by
      have hnear : (A.localize j (A.smoothSectionEquiv (action p.1)) : X → F) =ᶠ[𝓝 p.2]
          H p.1 := by
        filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
          (hS.mem_nhds hp)] with a ha
        exact heq (p.1, a) ha
      exact (hnear.iteratedFDeriv ℝ k).eq_of_nhds
    exact (hdH.continuousAt (hS.mem_nhds hp₀)).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hS.mem_nhds hp₀) (fun p hp ↦ hjet p hp))
  · -- Outside the fixed support all derivatives vanish, uniformly in the group action.
    apply (continuousAt_const (y := (0 : X [×k]→L[ℝ] F))).congr_of_eventuallyEq
    filter_upwards [(hK.isClosed.isOpen_compl.preimage continuous_snd).mem_nhds hzK] with p hp
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hp (A.tsupport_localizedFunction_subset j (A.smoothSectionEquiv (action p.1))
      (tsupport_iteratedFDeriv_subset k hmem))

end AtiyahSinger.SmoothBundlePresentation
