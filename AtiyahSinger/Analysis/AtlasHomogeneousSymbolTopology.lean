/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbol
public import AtiyahSinger.Analysis.AtlasGlobalSymbolTopology

import AtiyahSinger.Analysis.HomogeneousSymbolTopology
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# The punctured smooth topology on original atlas homogeneous fields

Public module ID: M0251.

A03: the standard compact-open C-infinity topology on punctured homogeneous
Hom data, using actual coordinate mixed derivatives. Compact frequency sets avoid
zero; they need not lie on a chosen cosphere. Local ranks remain independent.
No cotangent metric is used.
The carrier retains arbitrary zero-section values, which the seminorms ignore.
Consequently this total-function presentation is not asserted to be Hausdorff.

This supplies the derivative control for the homogeneous extension behind SG III.7.10,
Remark 7.11 and III.13 (13.5). The topology and its estimates are explicit project
bridges, not additional numbered statements from SG. All original topology and
parameter-continuity statements below are proved.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter
open scoped Manifold ContDiff Topology NNReal

set_option maxSynthPendingDepth 15

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- Closure of smooth degree-m homogeneous fields under the original fiberwise module operations. -/
theorem homogeneousAtlasSymbol_closure (m : ℝ) :
    (IsSmoothOffZeroAtlasSymbol A B 0 ∧
      IsHomogeneousAtlasSymbol m (0 : AtlasSymbolFunction (n := n) E F)) ∧
      (∀ a b : AtlasSymbolFunction (n := n) E F,
        IsSmoothOffZeroAtlasSymbol A B a → IsHomogeneousAtlasSymbol m a →
        IsSmoothOffZeroAtlasSymbol A B b → IsHomogeneousAtlasSymbol m b →
          IsSmoothOffZeroAtlasSymbol A B (a + b) ∧ IsHomogeneousAtlasSymbol m (a + b)) ∧
      (∀ (z : ℂ) (a : AtlasSymbolFunction (n := n) E F),
        IsSmoothOffZeroAtlasSymbol A B a → IsHomogeneousAtlasSymbol m a →
          IsSmoothOffZeroAtlasSymbol A B (z • a) ∧ IsHomogeneousAtlasSymbol m (z • a)) := by
  /- Coordinate frame maps preserve zero, addition and scalar multiplication.
  Apply smooth-function closure on the open punctured domains and
  distribute the positive real scaling factor to prove homogeneity. -/
  classical
  -- Each original frame map is linear, including the common zero-extension branch.
  have hzero (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (i : A.Index) (j : B.Index) : atlasGlobalSymbolInChart A B 0 c i j = 0 := by
    ext z η v
    simp [atlasGlobalSymbolInChart]
  have hadd (a b : AtlasSymbolFunction (n := n) E F)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (i : A.Index) (j : B.Index) :
      atlasGlobalSymbolInChart A B (a + b) c i j =
        atlasGlobalSymbolInChart A B a c i j + atlasGlobalSymbolInChart A B b c i j := by
    ext z η v
    by_cases h : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet
    · simp [atlasGlobalSymbolInChart, h]
    · simp [atlasGlobalSymbolInChart, h]
  have hsmul (z : ℂ) (a : AtlasSymbolFunction (n := n) E F)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (i : A.Index) (j : B.Index) :
      atlasGlobalSymbolInChart A B (z • a) c i j =
        z • atlasGlobalSymbolInChart A B a c i j := by
    ext x η v
    by_cases h : c.symm x ∈ (A.chart i).baseSet ∧ c.symm x ∈ (B.chart j).baseSet
    · simp [atlasGlobalSymbolInChart, h]
    · simp [atlasGlobalSymbolInChart, h]
  -- Smoothness is tested off zero, whereas homogeneity uses the same actual fiber.
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro c hc i j
    rw [hzero]
    exact contDiffOn_const
  · intro x ξ hξ t ht
    simp
  · intro a b ha hha hb hhb
    constructor
    · intro c hc i j
      rw [hadd]
      exact (ha c hc i j).add (hb c hc i j)
    · intro x ξ hξ t ht
      change a x (t • ξ) + b x (t • ξ) = _
      rw [hha x ξ hξ t ht, hhb x ξ hξ t ht]
      exact (smul_add _ _ _).symm
  · intro z a ha hha
    constructor
    · intro c hc i j
      rw [hsmul]
      exact (ha c hc i j).const_smul z
    · intro x ξ hξ t ht
      change z • a x (t • ξ) = _
      rw [hha x ξ hξ t ht]
      exact smul_comm z _ _

/-- The standard vector space of smooth homogeneous fields, retaining arbitrary values at zero. -/
def homogeneousAtlasSymbolSpace (m : ℝ) :
    Submodule ℂ (AtlasSymbolFunction (n := n) E F) where
  carrier := {a | IsSmoothOffZeroAtlasSymbol A B a ∧ IsHomogeneousAtlasSymbol m a}
  zero_mem' := (homogeneousAtlasSymbol_closure A B m).1
  add_mem' := fun ha hb ↦ (homogeneousAtlasSymbol_closure A B m).2.1
    _ _ ha.1 ha.2 hb.1 hb.2
  smul_mem' := fun z a ha ↦ (homogeneousAtlasSymbol_closure A B m).2.2 z a ha.1 ha.2

/-- One compact coordinate test for the standard punctured smooth-function topology. -/
structure AtlasHomogeneousSymbolSeminormIndex extends
    AtlasGlobalSymbolSeminormIndex A B where
  /-- The compact frequency set on which derivatives are measured. -/
  frequencySet : Set (EuclideanSpace ℝ (Fin n))
  /-- The frequency set is compact, including the permitted empty set. -/
  isCompact_frequencySet : IsCompact frequencySet
  /-- No zero frequency is measured. -/
  frequency_ne_zero : ∀ ξ ∈ frequencySet, ξ ≠ 0

variable (m : ℝ)

/-- The supremum of coordinate mixed derivative norms on a compact punctured product. -/
def atlasHomogeneousSymbolSeminormValue
    (J : AtlasHomogeneousSymbolSeminormIndex A B)
    (a : homogeneousAtlasSymbolSpace A B m) : ℝ :=
  sSup {t : ℝ | ∃ x ∈ J.localIndex.compactSet, ∃ ξ ∈ J.frequencySet,
    t = ‖symbolDerivative (atlasGlobalSymbolInChart A B a.val J.chart J.inputIndex J.outputIndex)
      J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖}

/-- The derivative norms defining a homogeneous seminorm are bounded above. -/
theorem bddAbove_atlasHomogeneousSymbolSeminormValue_set
    (J : AtlasHomogeneousSymbolSeminormIndex A B)
    (a : homogeneousAtlasSymbolSpace A B m) :
    BddAbove {t : ℝ | ∃ x ∈ J.localIndex.compactSet, ∃ ξ ∈ J.frequencySet,
      t = ‖symbolDerivative (atlasGlobalSymbolInChart A B a.val J.chart J.inputIndex J.outputIndex)
        J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖} := by
  /- The common base domain and the punctured frequency domain are open. Smoothness
  gives continuous mixed derivatives there. Their norms are bounded on the displayed
  compact product. The empty product has an empty, hence bounded, image as well. -/
  -- Smooth parameter differentiation makes each mixed derivative continuous off zero.
  let f := atlasGlobalSymbolInChart A B a.val J.chart J.inputIndex J.outputIndex
  let U := atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
  have hU : IsOpen U := isOpen_atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
  have hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ {ξ | ξ ≠ 0}) :=
    a.property.1 J.chart J.mem_atlas J.inputIndex J.outputIndex
  have hcont : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        ‖symbolDerivative f J.localIndex.spatialOrder J.localIndex.frequencyOrder p.1 p.2‖)
      (J.localIndex.compactSet ×ˢ J.frequencySet) := by
    intro p hp
    have hfp : ContDiffAt ℝ ∞ (Function.uncurry f) p :=
      hf.contDiffAt ((hU.prod isOpen_ne).mem_nhds
        ⟨J.localIndex.subset_domain hp.1, J.frequency_ne_zero p.2 hp.2⟩)
    have hξ := contDiffAt_iteratedFDeriv_uncurry f p.1 p.2 hfp
      J.localIndex.frequencyOrder
    have hswap : ContDiffAt ℝ ∞
        (Function.uncurry (fun ξ x ↦ iteratedFDeriv ℝ J.localIndex.frequencyOrder (f x) ξ))
        (p.2, p.1) := hξ.comp (p.2, p.1) (contDiffAt_snd.prodMk contDiffAt_fst)
    have hx := contDiffAt_iteratedFDeriv_uncurry _ p.2 p.1 hswap
      J.localIndex.spatialOrder
    exact ((hx.comp p (contDiffAt_snd.prodMk contDiffAt_fst)).continuousAt.norm).continuousWithinAt
  -- The defining set lies in the continuous image of the original compact product.
  have hb := ((J.localIndex.isCompact.prod J.isCompact_frequencySet).image_of_continuousOn
    hcont).bddAbove
  apply hb.mono
  rintro t ⟨x, hx, ξ, hξ, rfl⟩
  exact ⟨(x, ξ), ⟨hx, hξ⟩, rfl⟩

/-- Compact derivative suprema are subadditive. -/
theorem atlasHomogeneousSymbolSeminormValue_add_le
    (J : AtlasHomogeneousSymbolSeminormIndex A B)
    (a b : homogeneousAtlasSymbolSpace A B m) :
    atlasHomogeneousSymbolSeminormValue A B m J (a + b) ≤
      atlasHomogeneousSymbolSeminormValue A B m J a +
        atlasHomogeneousSymbolSeminormValue A B m J b := by
  /- Differentiate the exact coordinate sum on the open punctured domain, apply
  the norm triangle inequality, and take bounded suprema. Empty suprema in the
  real numbers are zero and must be handled separately. -/
  classical
  -- Empty compact products have the stipulated real supremum zero.
  by_cases hK : J.localIndex.compactSet.Nonempty
  swap
  · simp [atlasHomogeneousSymbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hK]
  by_cases hV : J.frequencySet.Nonempty
  swap
  · simp [atlasHomogeneousSymbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hV]
  obtain ⟨x₀, hx₀⟩ := hK
  obtain ⟨ξ₀, hξ₀⟩ := hV
  let U := atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
  let f := atlasGlobalSymbolInChart A B a.val J.chart J.inputIndex J.outputIndex
  let g := atlasGlobalSymbolInChart A B b.val J.chart J.inputIndex J.outputIndex
  have hU : IsOpen U := isOpen_atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
  have hfg (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) :
      ContDiffAt ℝ ∞ (Function.uncurry f) (x, ξ) ∧
        ContDiffAt ℝ ∞ (Function.uncurry g) (x, ξ) := by
    exact ⟨(a.property.1 J.chart J.mem_atlas J.inputIndex J.outputIndex).contDiffAt
        ((hU.prod isOpen_ne).mem_nhds ⟨hx, hξ⟩),
      (b.property.1 J.chart J.mem_atlas J.inputIndex J.outputIndex).contDiffAt
        ((hU.prod isOpen_ne).mem_nhds ⟨hx, hξ⟩)⟩
  -- Both rounds of differentiation commute with addition on the open punctured domain.
  have hder (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) :
      symbolDerivative (f + g) J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ =
        symbolDerivative f J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ +
          symbolDerivative g J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ := by
    have hnear : (fun y ↦ iteratedFDeriv ℝ J.localIndex.frequencyOrder ((f + g) y) ξ) =ᶠ[𝓝 x]
        (fun y ↦ iteratedFDeriv ℝ J.localIndex.frequencyOrder (f y) ξ +
          iteratedFDeriv ℝ J.localIndex.frequencyOrder (g y) ξ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact iteratedFDeriv_add_apply
        (((hfg y hy ξ hξ).1.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
        (((hfg y hy ξ hξ).2.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
    have hf := (contDiffAt_iteratedFDeriv_uncurry f x ξ (hfg x hx ξ hξ).1
      J.localIndex.frequencyOrder).comp x (contDiffAt_id.prodMk contDiffAt_const)
    have hg := (contDiffAt_iteratedFDeriv_uncurry g x ξ (hfg x hx ξ hξ).2
      J.localIndex.frequencyOrder).comp x (contDiffAt_id.prodMk contDiffAt_const)
    exact ((hnear.iteratedFDeriv ℝ J.localIndex.spatialOrder).eq_of_nhds).trans
      (iteratedFDeriv_add_apply (hf.of_le (by simp)) (hg.of_le (by simp)))
  -- Compare each derivative norm to the two bounded defining suprema.
  unfold atlasHomogeneousSymbolSeminormValue
  refine csSup_le ⟨_, x₀, hx₀, ξ₀, hξ₀, rfl⟩ ?_
  rintro t ⟨x, hx, ξ, hξ, rfl⟩
  change ‖symbolDerivative
      (atlasGlobalSymbolInChart A B (a.val + b.val) J.chart J.inputIndex J.outputIndex)
      J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖ ≤ _
  have hcoord : atlasGlobalSymbolInChart A B (a.val + b.val)
      J.chart J.inputIndex J.outputIndex = f + g := by
    ext z η v
    by_cases h : J.chart.symm z ∈ (A.chart J.inputIndex).baseSet ∧
        J.chart.symm z ∈ (B.chart J.outputIndex).baseSet
    · simp [atlasGlobalSymbolInChart, f, g, h]
    · simp [atlasGlobalSymbolInChart, f, g, h]
  rw [hcoord]
  calc
    ‖symbolDerivative (f + g) J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖ =
        ‖symbolDerivative f J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ +
          symbolDerivative g J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖ :=
      congrArg norm (hder x (J.localIndex.subset_domain hx) ξ (J.frequency_ne_zero ξ hξ))
    _ ≤ ‖symbolDerivative f J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖ +
        ‖symbolDerivative g J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖ :=
      norm_add_le _ _
    _ ≤ atlasHomogeneousSymbolSeminormValue A B m J a +
        atlasHomogeneousSymbolSeminormValue A B m J b :=
      add_le_add (le_csSup (bddAbove_atlasHomogeneousSymbolSeminormValue_set A B m J a)
        ⟨x, hx, ξ, hξ, rfl⟩)
        (le_csSup (bddAbove_atlasHomogeneousSymbolSeminormValue_set A B m J b)
          ⟨x, hx, ξ, hξ, rfl⟩)

/-- Compact derivative suprema scale by the norm of a complex scalar. -/
theorem atlasHomogeneousSymbolSeminormValue_smul
    (J : AtlasHomogeneousSymbolSeminormIndex A B)
    (z : ℂ) (a : homogeneousAtlasSymbolSpace A B m) :
    atlasHomogeneousSymbolSeminormValue A B m J (z • a) =
      ‖z‖ * atlasHomogeneousSymbolSeminormValue A B m J a := by
  /- Constant complex multiplication commutes with the real derivatives. Norms
  scale by norm(z); move this factor through the bounded supremum. Treat z=0
  and an empty compact product explicitly. -/
  classical
  -- Empty compact products contribute zero before and after scalar multiplication.
  by_cases hK : J.localIndex.compactSet.Nonempty
  swap
  · simp [atlasHomogeneousSymbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hK]
  by_cases hV : J.frequencySet.Nonempty
  swap
  · simp [atlasHomogeneousSymbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hV]
  obtain ⟨x₀, hx₀⟩ := hK
  obtain ⟨ξ₀, hξ₀⟩ := hV
  let U := atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
  let f := atlasGlobalSymbolInChart A B a.val J.chart J.inputIndex J.outputIndex
  have hU : IsOpen U := isOpen_atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
  have hf (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) :
      ContDiffAt ℝ ∞ (Function.uncurry f) (x, ξ) :=
    (a.property.1 J.chart J.mem_atlas J.inputIndex J.outputIndex).contDiffAt
      ((hU.prod isOpen_ne).mem_nhds ⟨hx, hξ⟩)
  -- The constant complex scalar commutes with both real derivative operations.
  have hder (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) :
      symbolDerivative (z • f) J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ =
        z • symbolDerivative f J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ := by
    have hnear : (fun y ↦ iteratedFDeriv ℝ J.localIndex.frequencyOrder ((z • f) y) ξ) =ᶠ[𝓝 x]
        (fun y ↦ z • iteratedFDeriv ℝ J.localIndex.frequencyOrder (f y) ξ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact iteratedFDeriv_const_smul_apply (a := z)
        (((hf y hy ξ hξ).comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
    have hparam := (contDiffAt_iteratedFDeriv_uncurry f x ξ (hf x hx ξ hξ)
      J.localIndex.frequencyOrder).comp x (contDiffAt_id.prodMk contDiffAt_const)
    exact ((hnear.iteratedFDeriv ℝ J.localIndex.spatialOrder).eq_of_nhds).trans
      (iteratedFDeriv_const_smul_apply (a := z) (hparam.of_le (by simp)))
  -- Multiplication by the nonnegative norm carries the old least upper bound to the new one.
  let S : Set ℝ := {t | ∃ x ∈ J.localIndex.compactSet, ∃ ξ ∈ J.frequencySet,
    t = ‖symbolDerivative f J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖}
  have hS : S.Nonempty := ⟨_, x₀, hx₀, ξ₀, hξ₀, rfl⟩
  have hbound : BddAbove S := bddAbove_atlasHomogeneousSymbolSeminormValue_set A B m J a
  have himage : {t : ℝ | ∃ x ∈ J.localIndex.compactSet, ∃ ξ ∈ J.frequencySet,
      t = ‖symbolDerivative (z • f) J.localIndex.spatialOrder
        J.localIndex.frequencyOrder x ξ‖} = (fun t : ℝ ↦ ‖z‖ * t) '' S := by
    ext t
    constructor
    · rintro ⟨x, hx, ξ, hξ, rfl⟩
      refine ⟨_, ⟨x, hx, ξ, hξ, rfl⟩, ?_⟩
      rw [hder x (J.localIndex.subset_domain hx) ξ (J.frequency_ne_zero ξ hξ), norm_smul]
    · rintro ⟨t, ⟨x, hx, ξ, hξ, rfl⟩, rfl⟩
      refine ⟨x, hx, ξ, hξ, ?_⟩
      rw [hder x (J.localIndex.subset_domain hx) ξ (J.frequency_ne_zero ξ hξ), norm_smul]
  change sSup {t : ℝ | ∃ x ∈ J.localIndex.compactSet, ∃ ξ ∈ J.frequencySet,
      t = ‖symbolDerivative
        (atlasGlobalSymbolInChart A B (z • a.val) J.chart J.inputIndex J.outputIndex)
        J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖} = ‖z‖ * sSup S
  have hcoord : atlasGlobalSymbolInChart A B (z • a.val)
      J.chart J.inputIndex J.outputIndex = z • f := by
    ext x η v
    by_cases h : J.chart.symm x ∈ (A.chart J.inputIndex).baseSet ∧
        J.chart.symm x ∈ (B.chart J.outputIndex).baseSet
    · simp [atlasGlobalSymbolInChart, f, h]
    · simp [atlasGlobalSymbolInChart, f, h]
  rw [hcoord, himage]
  exact ((isLUB_csSup hS hbound).mul_left (norm_nonneg z)).csSup_eq (hS.image _)

/-- The standard C-infinity seminorm on a compact punctured coordinate product. -/
def atlasHomogeneousSymbolSeminorm
    (J : AtlasHomogeneousSymbolSeminormIndex A B) :
    Seminorm ℂ (homogeneousAtlasSymbolSpace A B m) :=
  Seminorm.of (atlasHomogeneousSymbolSeminormValue A B m J)
    (atlasHomogeneousSymbolSeminormValue_add_le A B m J)
    (atlasHomogeneousSymbolSeminormValue_smul A B m J)

/-- These seminorms detect precisely the data away from the zero section. -/
theorem forall_atlasHomogeneousSymbolSeminorm_eq_zero_iff
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (a : homogeneousAtlasSymbolSpace A B m) :
    (∀ J : AtlasHomogeneousSymbolSeminormIndex A B,
      atlasHomogeneousSymbolSeminorm A B m J a = 0) ↔
      ∀ x ξ, ξ ≠ 0 → a.val x ξ = 0 := by
  /- Forward: choose valid charts and frames at x and singleton compact sets for
  its coordinates and for the nonzero covector, with both derivative orders zero.
  The chart/frame isomorphisms recover a(x,ξ) from the zero norm. Reverse: all mixed
  derivatives vanish on the open punctured domains, so every supremum is zero.
  Values at zero remain arbitrary, including when n=0; do not conclude a=0. -/
  classical
  constructor
  · intro ha x ξ hξ
    -- Choose covering frames at this actual fiber, with no common-rank assumption.
    obtain ⟨i, hi⟩ := A.covers x
    obtain ⟨j, hj⟩ := B.covers x
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hc := chart_mem_atlas (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    let η := covectorInChart c x ξ
    have hη : η ≠ 0 := by
      intro hz
      apply hξ
      rw [← covectorFromChart_covectorInChart c hc x hx ξ,
        show covectorInChart c x ξ = 0 from hz]
      ext v
      change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) ((mfderiv _ _ c x) v) = 0
      exact inner_zero_left _
    have hz : c x ∈ atlasSymbolChartDomain A B c i j :=
      ⟨⟨c.map_source hx, by simpa only [Set.mem_preimage, c.left_inv hx] using hi⟩,
        by simpa only [Set.mem_preimage, c.left_inv hx] using hj⟩
    let J : AtlasHomogeneousSymbolSeminormIndex A B :=
      { chart := c
        mem_atlas := hc
        inputIndex := i
        outputIndex := j
        localIndex :=
          { compactSet := {c x}
            subset_domain := Set.singleton_subset_iff.mpr hz
            isCompact := isCompact_singleton
            spatialOrder := 0
            frequencyOrder := 0 }
        frequencySet := {η}
        isCompact_frequencySet := isCompact_singleton
        frequency_ne_zero := by
          intro ζ hζ
          simpa only [Set.mem_singleton_iff.mp hζ] using hη }
    -- The zero-order singleton seminorm detects the coordinate Hom value.
    have hJ : atlasHomogeneousSymbolSeminormValue A B m J a = 0 := ha J
    have hle := le_csSup (bddAbove_atlasHomogeneousSymbolSeminormValue_set A B m J a)
      (show ‖symbolDerivative (atlasGlobalSymbolInChart A B a.val c i j) 0 0 (c x) η‖ ∈
        {t : ℝ | ∃ y ∈ J.localIndex.compactSet, ∃ ζ ∈ J.frequencySet,
          t = ‖symbolDerivative (atlasGlobalSymbolInChart A B a.val J.chart
            J.inputIndex J.outputIndex) J.localIndex.spatialOrder
              J.localIndex.frequencyOrder y ζ‖} from
        ⟨c x, Set.mem_singleton _, η, Set.mem_singleton _, rfl⟩)
    change ‖symbolDerivative (atlasGlobalSymbolInChart A B a.val c i j) 0 0 (c x) η‖ ≤
      atlasHomogeneousSymbolSeminormValue A B m J a at hle
    rw [hJ] at hle
    simp only [symbolDerivative, norm_iteratedFDeriv_zero] at hle
    have hmap : atlasGlobalSymbolInChart A B a.val c i j (c x) η = 0 :=
      norm_le_zero_iff.mp hle
    -- Undo the same frame maps before transporting the returned dependent fiber to x.
    let y := c.symm (c x)
    have hiy : y ∈ (A.chart i).baseSet := by simpa only [y, c.left_inv hx] using hi
    have hjy : y ∈ (B.chart j).baseSet := by simpa only [y, c.left_inv hx] using hj
    let input := (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).toLinearEquiv.trans
      (A.frameLinearEquiv i y hiy).symm
    let output := (B.frameLinearEquiv j y hjy).trans
      (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm.toLinearEquiv
    have hval : a.val y (covectorFromChart c y η) = 0 := by
      unfold atlasGlobalSymbolInChart at hmap
      rw [dite_eq_left (show c.symm (c x) ∈ (A.chart i).baseSet ∧
        c.symm (c x) ∈ (B.chart j).baseSet from ⟨hiy, hjy⟩)] at hmap
      ext v
      have htest := congrArg
        (fun L : EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ]
            EuclideanSpace ℂ (Fin (B.rank j)) ↦ output.symm (L (input.symm v))) hmap
      change output.symm (output ((a.val y (covectorFromChart c y η))
        (input (input.symm v)))) = output.symm 0 at htest
      simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, map_zero,
        LinearMap.zero_apply] using htest
    have hxval : a.val x (covectorFromChart c x η) = 0 :=
      (congrArg (fun z : M ↦ a.val z (covectorFromChart c z η) = 0) (c.left_inv hx)).mp hval
    rw [covectorFromChart_covectorInChart c hc x hx ξ] at hxval
    exact hxval
  · intro ha J
    -- Off-zero vanishing is a local zero identity on the open punctured chart domain.
    let U := atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
    let f := atlasGlobalSymbolInChart A B a.val J.chart J.inputIndex J.outputIndex
    have hU : IsOpen U :=
      isOpen_atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
    have hfzero (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
        (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) : f x ξ = 0 := by
      have hcov : covectorFromChart J.chart (J.chart.symm x) ξ ≠ 0 := by
        intro hz
        have hinv := covectorInChart_covectorFromChart J.chart J.mem_atlas
          (J.chart.symm x) (J.chart.map_target hx.1.1) ξ
        rw [hz] at hinv
        apply hξ
        rw [← hinv]
        ext i
        change (0 : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (J.chart.symm x)
          →L[ℝ] ℝ) _ = 0
        rfl
      dsimp [f]
      unfold atlasGlobalSymbolInChart
      rw [dite_eq_left (show J.chart.symm x ∈ (A.chart J.inputIndex).baseSet ∧
        J.chart.symm x ∈ (B.chart J.outputIndex).baseSet from ⟨hx.1.2, hx.2⟩)]
      rw [ha _ _ hcov]
      ext v
      simp
    -- Locality of iterated derivatives leaves the unmeasured zero-section values free.
    have hderzero (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
        (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) :
        symbolDerivative f J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ = 0 := by
      have hinner (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U) :
          iteratedFDeriv ℝ J.localIndex.frequencyOrder (f y) ξ = 0 := by
        have hnear : f y =ᶠ[𝓝 ξ] 0 := by
          filter_upwards [(isOpen_ne : IsOpen {ζ : EuclideanSpace ℝ (Fin n) | ζ ≠ 0}).mem_nhds hξ]
            with ζ hζ
          exact hfzero y hy ζ hζ
        simpa only [iteratedFDeriv_zero, Pi.zero_apply] using
          (hnear.iteratedFDeriv ℝ J.localIndex.frequencyOrder).eq_of_nhds
      have hnear : (fun y ↦ iteratedFDeriv ℝ J.localIndex.frequencyOrder (f y) ξ) =ᶠ[𝓝 x] 0 := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact hinner y hy
      simpa only [symbolDerivative, iteratedFDeriv_zero, Pi.zero_apply] using
        (hnear.iteratedFDeriv ℝ J.localIndex.spatialOrder).eq_of_nhds
    -- Empty products have zero real supremum; otherwise the norm set is exactly {0}.
    change atlasHomogeneousSymbolSeminormValue A B m J a = 0
    by_cases hK : J.localIndex.compactSet.Nonempty
    swap
    · simp [atlasHomogeneousSymbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hK]
    by_cases hV : J.frequencySet.Nonempty
    swap
    · simp [atlasHomogeneousSymbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hV]
    obtain ⟨x₀, hx₀⟩ := hK
    obtain ⟨ξ₀, hξ₀⟩ := hV
    have hset : {t : ℝ | ∃ x ∈ J.localIndex.compactSet, ∃ ξ ∈ J.frequencySet,
        t = ‖symbolDerivative f J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖} =
        {0} := by
      ext t
      constructor
      · rintro ⟨x, hx, ξ, hξ, rfl⟩
        rw [hderzero x (J.localIndex.subset_domain hx) ξ (J.frequency_ne_zero ξ hξ)]
        simp
      · intro ht
        refine ⟨x₀, hx₀, ξ₀, hξ₀, ?_⟩
        rw [hderzero x₀ (J.localIndex.subset_domain hx₀) ξ₀ (J.frequency_ne_zero ξ₀ hξ₀)]
        simpa only [norm_zero] using (Set.mem_singleton_iff.mp ht : t = 0)
    change sSup {t : ℝ | ∃ x ∈ J.localIndex.compactSet, ∃ ξ ∈ J.frequencySet,
      t = ‖symbolDerivative f J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖} = 0
    rw [hset, csSup_singleton]

/-- Compact-open smooth convergence on the punctured cotangent bundle, at fixed degree. -/
@[instance_reducible]
def atlasHomogeneousSymbolTopology :
    TopologicalSpace (homogeneousAtlasSymbolSpace A B m) :=
  (SeminormFamily.moduleFilterBasis
    (atlasHomogeneousSymbolSeminorm A B m)).topology

attribute [local instance] atlasHomogeneousSymbolTopology

/-- The selected topology is generated by the actual punctured derivative seminorms. -/
theorem withSeminorms_atlasHomogeneousSymbolTopology :
    WithSeminorms (atlasHomogeneousSymbolSeminorm A B m) := by
  /- Unfold the chosen topology: it is exactly the module filter basis of this
  family of seminorms. This does not assert separation of zero-section values. -/

  exact ⟨rfl⟩

/-- Convergence tests uniform derivatives of differences on every compact punctured product. -/
theorem tendsto_atlasHomogeneousSymbolTopology_iff {Z : Type*} (l : Filter Z)
    (a : Z → homogeneousAtlasSymbolSpace A B m)
    (b : homogeneousAtlasSymbolSpace A B m) :
    Tendsto a l (𝓝 b) ↔
      ∀ J : AtlasHomogeneousSymbolSeminormIndex A B,
        ∀ ε : ℝ, 0 < ε → ∀ᶠ z in l, atlasHomogeneousSymbolSeminorm A B m J (a z - b) < ε := by
  /- Apply WithSeminorms.tendsto_nhds to the displayed topology. Every derivative
  order is tested. Continuity of values alone does not imply this condition. -/

  exact (withSeminorms_atlasHomogeneousSymbolTopology A B m).tendsto_nhds a b

set_option maxHeartbeats 800000 in

/-- Joint continuity of every coordinate derivative implies continuity of a homogeneous family. -/
theorem continuous_atlasHomogeneousSymbol_of_joint_derivatives
    {Z : Type*} [TopologicalSpace Z] (a : Z → homogeneousAtlasSymbolSpace A B m)
    (ha : ∀ (J : AtlasHomogeneousSymbolSeminormIndex A B),
      ContinuousOn (fun z : Z × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        symbolDerivative
          (atlasGlobalSymbolInChart A B (a z.1).val J.chart J.inputIndex J.outputIndex)
          J.localIndex.spatialOrder J.localIndex.frequencyOrder z.2.1 z.2.2)
        (Set.univ ×ˢ (J.localIndex.compactSet ×ˢ J.frequencySet))) :
    Continuous a := by
  /- Fix a parameter and one compact derivative test. Joint continuity on
  that parameter space times the compact spatial-frequency product gives
  uniform convergence in this derivative norm, by a finite neighborhood cover.
  Apply this to every index and the seminorm convergence criterion. The
  parameter need not be compact or metrizable. A jointly smooth family satisfies
  this hypothesis for all coordinate derivatives. This conclusion uses compact
  punctured tests; it is false for unrestricted full-symbol frequency suprema. -/
  classical
  apply continuous_iff_continuousAt.mpr
  intro z₀
  change Tendsto a (𝓝 z₀) (𝓝 (a z₀))
  rw [tendsto_atlasHomogeneousSymbolTopology_iff A B m]
  intro J ε hε
  let U := atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
  let f (z : Z) : SymbolFunction n (A.rank J.inputIndex) (B.rank J.outputIndex) :=
    atlasGlobalSymbolInChart A B (a z).val J.chart J.inputIndex J.outputIndex
  let V := ContinuousMultilinearMap ℝ
    (fun _ : Fin J.localIndex.spatialOrder ↦ EuclideanSpace ℝ (Fin n))
    (ContinuousMultilinearMap ℝ
      (fun _ : Fin J.localIndex.frequencyOrder ↦ EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℂ (Fin (A.rank J.inputIndex)) →L[ℂ]
        EuclideanSpace ℂ (Fin (B.rank J.outputIndex))))
  let D (z : Z) (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : V :=
    symbolDerivative (f z) J.localIndex.spatialOrder J.localIndex.frequencyOrder p.1 p.2
  have hU : IsOpen U :=
    isOpen_atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
  -- On the open punctured domain, mixed derivatives commute with this actual difference.
  have hsmooth (z : Z) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) :
      ContDiffAt ℝ ∞ (Function.uncurry (f z)) (x, ξ) :=
    ((a z).property.1 J.chart J.mem_atlas J.inputIndex J.outputIndex).contDiffAt
      ((hU.prod isOpen_ne).mem_nhds ⟨hx, hξ⟩)
  have hcoord (z : Z) :
      atlasGlobalSymbolInChart A B ((a z).val - (a z₀).val)
        J.chart J.inputIndex J.outputIndex = f z - f z₀ := by
    ext x ξ v
    by_cases h : J.chart.symm x ∈ (A.chart J.inputIndex).baseSet ∧
        J.chart.symm x ∈ (B.chart J.outputIndex).baseSet
    · simp [atlasGlobalSymbolInChart, f, h]
    · simp [atlasGlobalSymbolInChart, f, h]
  have hder (z : Z) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) :
      symbolDerivative
        (atlasGlobalSymbolInChart A B (a z - a z₀).val J.chart J.inputIndex J.outputIndex)
        J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ = D z (x, ξ) - D z₀ (x, ξ) := by
    change symbolDerivative
      (atlasGlobalSymbolInChart A B ((a z).val - (a z₀).val)
        J.chart J.inputIndex J.outputIndex) _ _ _ _ = _
    rw [hcoord]
    have hnear :
        (fun y ↦ iteratedFDeriv ℝ J.localIndex.frequencyOrder ((f z - f z₀) y) ξ) =ᶠ[𝓝 x]
        (fun y ↦ iteratedFDeriv ℝ J.localIndex.frequencyOrder (f z y) ξ -
          iteratedFDeriv ℝ J.localIndex.frequencyOrder (f z₀ y) ξ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact iteratedFDeriv_sub_apply
        (((hsmooth z y hy ξ hξ).comp ξ
          (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
        (((hsmooth z₀ y hy ξ hξ).comp ξ
          (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
    have hf := (contDiffAt_iteratedFDeriv_uncurry (f z) x ξ (hsmooth z x hx ξ hξ)
      J.localIndex.frequencyOrder).comp x (contDiffAt_id.prodMk contDiffAt_const)
    have hg := (contDiffAt_iteratedFDeriv_uncurry (f z₀) x ξ (hsmooth z₀ x hx ξ hξ)
      J.localIndex.frequencyOrder).comp x (contDiffAt_id.prodMk contDiffAt_const)
    exact ((hnear.iteratedFDeriv ℝ J.localIndex.spatialOrder).eq_of_nhds).trans
      (iteratedFDeriv_sub_apply (hf.of_le (by simp)) (hg.of_le (by simp)))
  -- Restrict the derivative to its compact test product, then curry the joint map.
  let K := J.localIndex.compactSet ×ˢ J.frequencySet
  have hKcompact : IsCompact K := J.localIndex.isCompact.prod J.isCompact_frequencySet
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  have hin : Continuous (fun p : Z × K ↦ (p.1, p.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hD : Continuous (fun p : Z × K ↦ D p.1 p.2.val) :=
    (ha J).comp_continuous (f := fun p : Z × K ↦ (p.1, p.2.val)) hin
      (fun p ↦ ⟨Set.mem_univ _, p.2.property⟩)
  let family : Z → C(K, V) := fun z ↦
    ⟨fun p ↦ D z p.val, hD.comp (continuous_const.prodMk continuous_id)⟩
  have hfamily : Continuous family :=
    ContinuousMap.continuous_of_continuous_uncurry family hD
  have huniform :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
      (hfamily.tendsto z₀)) Set.univ isCompact_univ
  -- Uniform convergence gives one parameter neighborhood for the whole compact set.
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp huniform) (ε / 2) (half_pos hε)]
    with z hz
  change atlasHomogeneousSymbolSeminormValue A B m J (a z - a z₀) < ε
  by_cases hK : K.Nonempty
  · obtain ⟨⟨x₀, ξ₀⟩, hx₀, hξ₀⟩ := hK
    apply lt_of_le_of_lt (b := ε / 2) _ (half_lt_self hε)
    unfold atlasHomogeneousSymbolSeminormValue
    refine csSup_le ⟨_, x₀, hx₀, ξ₀, hξ₀, rfl⟩ ?_
    rintro t ⟨x, hx, ξ, hξ, rfl⟩
    rw [hder z x (J.localIndex.subset_domain hx) ξ (J.frequency_ne_zero ξ hξ)]
    have hbound := hz ⟨(x, ξ), ⟨hx, hξ⟩⟩ (Set.mem_univ _)
    change dist (D z₀ (x, ξ)) (D z (x, ξ)) < ε / 2 at hbound
    rw [dist_eq_norm] at hbound
    exact le_of_lt (by simpa only [norm_sub_rev] using hbound)
  · have hset : {t : ℝ | ∃ x ∈ J.localIndex.compactSet, ∃ ξ ∈ J.frequencySet,
        t = ‖symbolDerivative
          (atlasGlobalSymbolInChart A B (a z - a z₀).val J.chart J.inputIndex J.outputIndex)
          J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro t ⟨x, hx, ξ, hξ, ht⟩
      exact hK ⟨(x, ξ), hx, hξ⟩
    simpa only [atlasHomogeneousSymbolSeminormValue, hset, Real.sSup_empty] using hε

end AtiyahSinger
