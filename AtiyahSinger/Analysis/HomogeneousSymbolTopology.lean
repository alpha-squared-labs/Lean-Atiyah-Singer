/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalHomogeneousSymbol
public import AtiyahSinger.Analysis.GlobalSymbolTopology

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The smooth topology of homogeneous cotangent symbols

Public module ID: M0750.

D05/A03/A08: the standard compact-open C-infinity topology on punctured homogeneous
Hom data, using actual coordinate mixed derivatives. Compact frequency sets avoid
zero; they are not required to lie on a chosen cosphere. No cotangent metric is used.
The carrier retains arbitrary zero-section values, which the seminorms ignore.
Consequently this total-function presentation is not asserted to be Hausdorff.

This supplies the derivative control for the homogeneous extension behind SG III.7.10,
Remark 7.11 and III.13 (13.5). The topology and its estimates are explicit project
bridges, not additional numbered statements from SG. The original seminorms measure
all mixed derivatives on compact punctured coordinate products.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter
open scoped Manifold ContDiff Topology NNReal

set_option maxSynthPendingDepth 15

section ParametricDerivatives

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Iterated derivatives in the second variable remain smooth in both variables.
This standard parameter-calculus fact supplies regularity of the mixed derivatives
used by the compact homogeneous-symbol seminorms. -/
theorem contDiffAt_iteratedFDeriv_uncurry (f : E → F → G) (x : E) (y : F)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, y)) (j : ℕ) :
    ContDiffAt ℝ ∞ (fun p : E × F ↦ iteratedFDeriv ℝ j (f p.1) p.2) (x, y) := by
  -- Differentiate the previous smooth parameter family and uncurry its derivative.
  induction j with
  | zero =>
    exact hf.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ F G).symm : _ →L[ℝ] F [×0]→L[ℝ] G)
  | succ j ih =>
    have h : ContDiffAt ℝ ∞
        (Function.uncurry (fun p : E × F ↦ fun z : F ↦ iteratedFDeriv ℝ j (f p.1) z))
        ((x, y), y) := ih.comp ((x, y), y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞
        (fun p : E × F ↦ fderiv ℝ (iteratedFDeriv ℝ j (f p.1)) p.2) (x, y) :=
      h.fderiv contDiffAt_snd (by simp)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ F) G).symm :
        _ →L[ℝ] F [×(j + 1)]→L[ℝ] G)

end ParametricDerivatives

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- The zero cotangent Hom function is smooth away from zero. -/
theorem isSmoothOffZeroGlobalSymbol_zero :
    IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F 0 := by
  /- In every chart the zero Hom function is the zero matrix function. Its
  restriction to the open punctured coordinate domain is smooth. -/

  intro c hc e f _ _
  have hzero : Function.uncurry (globalSymbolInChart E F 0 c e f) =
      fun _ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        (0 : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) := by
    funext p
    change (f.continuousLinearMapAt ℂ (c.symm p.1)).comp
      ((0 : E (c.symm p.1) →L[ℂ] F (c.symm p.1)).comp (e.symmL ℂ (c.symm p.1))) = 0
    simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  rw [hzero]
  exact contDiffOn_const

/-- The zero Hom function has every real homogeneous degree. -/
theorem isHomogeneousGlobalSymbol_zero (m : ℝ) :
    IsHomogeneousGlobalSymbol (n := n) E F m 0 := by
  /- Both sides of the positive scaling identity vanish at each nonzero covector.
  No condition at zero or positive dimension is needed. -/

  intro x ξ hξ t ht
  simp

variable {E F}

/-- Punctured smoothness is preserved by addition. -/
theorem IsSmoothOffZeroGlobalSymbol.add {a b : GlobalSymbolFunction (n := n) E F}
    (ha : IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F a)
    (hb : IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F b) :
    IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F (a + b) := by
  /- Use the exact chartwise addition formula and add the two smooth functions
  on their common punctured domain. No growth estimate is involved. -/

  intro c hc e f _ _
  simp_rw [globalSymbolInChart_add]
  exact (ha c hc e f).add (hb c hc e f)

/-- Punctured smoothness is preserved by constant complex scalar multiplication. -/
theorem IsSmoothOffZeroGlobalSymbol.smul (z : ℂ)
    {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F a) :
    IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F (z • a) := by
  /- Chart expressions commute with complex scalars; multiplication by z is
  continuous real-linear and hence preserves real smoothness on the punctured domain. -/

  intro c hc e f _ _
  simp_rw [globalSymbolInChart_smul]
  exact (ha c hc e f).const_smul z

/-- Addition preserves a fixed real homogeneous degree. -/
theorem IsHomogeneousGlobalSymbol.add {m : ℝ} {a b : GlobalSymbolFunction (n := n) E F}
    (ha : IsHomogeneousGlobalSymbol E F m a) (hb : IsHomogeneousGlobalSymbol E F m b) :
    IsHomogeneousGlobalSymbol E F m (a + b) := by
  /- Apply both scaling identities at the same positive scalar and distribute
  its common real power over the sum of the two Hom values. -/

  intro x ξ hξ t ht
  change a x (t • ξ) + b x (t • ξ) = _
  rw [ha x ξ hξ t ht, hb x ξ hξ t ht]
  exact (smul_add _ _ _).symm

/-- Complex scalar multiplication preserves a fixed real homogeneous degree. -/
theorem IsHomogeneousGlobalSymbol.smul {m : ℝ} (z : ℂ)
    {a : GlobalSymbolFunction (n := n) E F} (ha : IsHomogeneousGlobalSymbol E F m a) :
    IsHomogeneousGlobalSymbol E F m (z • a) := by
  /- The constant complex scalar commutes with the real positive scaling factor.
  Apply ha at each nonzero covector; no conjugation occurs. -/

  intro x ξ hξ t ht
  change z • a x (t • ξ) = _
  rw [ha x ξ hξ t ht]
  exact smul_comm z _ _

variable (E F)

/-- Total cotangent Hom functions that are smooth off zero and homogeneous of real degree m. -/
def homogeneousGlobalSymbolSpace (m : ℝ) :
    Submodule ℂ (GlobalSymbolFunction (n := n) E F) where
  carrier := {a | IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F a ∧
    IsHomogeneousGlobalSymbol E F m a}
  zero_mem' := ⟨isSmoothOffZeroGlobalSymbol_zero E F, isHomogeneousGlobalSymbol_zero E F m⟩
  add_mem' := fun ha hb ↦ ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  smul_mem' := fun z _ ha ↦ ⟨ha.1.smul z, ha.2.smul z⟩

/-- One compact coordinate test for the standard punctured smooth-function topology. -/
structure HomogeneousSymbolSeminormIndex extends
    GlobalSymbolSeminormIndex (n := n) (r := r) (q := q) E F where
  /-- The compact frequency set on which derivatives are measured. -/
  frequencySet : Set (EuclideanSpace ℝ (Fin n))
  /-- The frequency set is compact, including the permitted empty set. -/
  isCompact_frequencySet : IsCompact frequencySet
  /-- No zero frequency is measured. -/
  frequency_ne_zero : ∀ ξ ∈ frequencySet, ξ ≠ 0

attribute [local instance] GlobalSymbolSeminormIndex.input_mem_atlas
  GlobalSymbolSeminormIndex.output_mem_atlas

variable (m : ℝ)

/-- The supremum of coordinate mixed derivative norms on a compact punctured product. -/
def homogeneousSymbolSeminormValue
    (J : HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) : ℝ :=
  sSup {t : ℝ | ∃ x ∈ J.localIndex.compactSet, ∃ ξ ∈ J.frequencySet,
    t = ‖symbolDerivative (globalSymbolInChart E F a.val J.chart J.inputFrame J.outputFrame)
      J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖}

/-- The derivative norms defining a homogeneous seminorm are bounded above. -/
theorem bddAbove_homogeneousSymbolSeminormValue_set
    (J : HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    BddAbove {t : ℝ | ∃ x ∈ J.localIndex.compactSet, ∃ ξ ∈ J.frequencySet,
      t = ‖symbolDerivative (globalSymbolInChart E F a.val J.chart J.inputFrame J.outputFrame)
        J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖} := by
  /- The common base domain and the punctured frequency domain are open. Smoothness
  gives continuous mixed derivatives there. Their norms are bounded on the displayed
  compact product. The empty product has an empty, hence bounded, image as well. -/
  -- Smooth parameter differentiation makes each mixed derivative continuous off zero.
  let f := globalSymbolInChart E F a.val J.chart J.inputFrame J.outputFrame
  let U := symbolChartDomain E F J.chart J.inputFrame J.outputFrame
  have hU : IsOpen U := isOpen_symbolChartDomain E F J.chart J.inputFrame J.outputFrame
  have hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ {ξ | ξ ≠ 0}) :=
    a.property.1 J.chart J.mem_atlas J.inputFrame J.outputFrame
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
theorem homogeneousSymbolSeminormValue_add_le
    (J : HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F)
    (a b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    homogeneousSymbolSeminormValue E F m J (a + b) ≤
      homogeneousSymbolSeminormValue E F m J a + homogeneousSymbolSeminormValue E F m J b := by
  /- Differentiate the exact coordinate sum on the open punctured domain, apply
  the norm triangle inequality, and take bounded suprema. Empty suprema in the
  real numbers are zero and must be handled separately. -/
  classical
  -- Empty compact products have the stipulated real supremum zero.
  by_cases hK : J.localIndex.compactSet.Nonempty
  swap
  · simp [homogeneousSymbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hK]
  by_cases hV : J.frequencySet.Nonempty
  swap
  · simp [homogeneousSymbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hV]
  obtain ⟨x₀, hx₀⟩ := hK
  obtain ⟨ξ₀, hξ₀⟩ := hV
  let U := symbolChartDomain E F J.chart J.inputFrame J.outputFrame
  let f := globalSymbolInChart E F a.val J.chart J.inputFrame J.outputFrame
  let g := globalSymbolInChart E F b.val J.chart J.inputFrame J.outputFrame
  have hU : IsOpen U := isOpen_symbolChartDomain E F J.chart J.inputFrame J.outputFrame
  have hfg (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) :
      ContDiffAt ℝ ∞ (Function.uncurry f) (x, ξ) ∧
        ContDiffAt ℝ ∞ (Function.uncurry g) (x, ξ) := by
    exact ⟨(a.property.1 J.chart J.mem_atlas J.inputFrame J.outputFrame).contDiffAt
        ((hU.prod isOpen_ne).mem_nhds ⟨hx, hξ⟩),
      (b.property.1 J.chart J.mem_atlas J.inputFrame J.outputFrame).contDiffAt
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
  unfold homogeneousSymbolSeminormValue
  refine csSup_le ⟨_, x₀, hx₀, ξ₀, hξ₀, rfl⟩ ?_
  rintro t ⟨x, hx, ξ, hξ, rfl⟩
  change ‖symbolDerivative
      (globalSymbolInChart E F (a.val + b.val) J.chart J.inputFrame J.outputFrame)
      J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖ ≤ _
  rw [globalSymbolInChart_add]
  calc
    ‖symbolDerivative (f + g) J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖ =
        ‖symbolDerivative f J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ +
          symbolDerivative g J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖ :=
      congrArg norm (hder x (J.localIndex.subset_domain hx) ξ (J.frequency_ne_zero ξ hξ))
    _ ≤ ‖symbolDerivative f J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖ +
        ‖symbolDerivative g J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖ :=
      norm_add_le _ _
    _ ≤ homogeneousSymbolSeminormValue E F m J a +
        homogeneousSymbolSeminormValue E F m J b :=
      add_le_add (le_csSup (bddAbove_homogeneousSymbolSeminormValue_set E F m J a)
        ⟨x, hx, ξ, hξ, rfl⟩)
        (le_csSup (bddAbove_homogeneousSymbolSeminormValue_set E F m J b)
          ⟨x, hx, ξ, hξ, rfl⟩)

/-- Compact derivative suprema scale by the norm of a complex scalar. -/
theorem homogeneousSymbolSeminormValue_smul
    (J : HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F)
    (z : ℂ) (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    homogeneousSymbolSeminormValue E F m J (z • a) =
      ‖z‖ * homogeneousSymbolSeminormValue E F m J a := by
  /- Constant complex multiplication commutes with the real derivatives. Norms
  scale by norm(z); move this factor through the bounded supremum. Treat z=0
  and an empty compact product explicitly. -/
  classical
  -- Empty compact products contribute zero before and after scalar multiplication.
  by_cases hK : J.localIndex.compactSet.Nonempty
  swap
  · simp [homogeneousSymbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hK]
  by_cases hV : J.frequencySet.Nonempty
  swap
  · simp [homogeneousSymbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hV]
  obtain ⟨x₀, hx₀⟩ := hK
  obtain ⟨ξ₀, hξ₀⟩ := hV
  let U := symbolChartDomain E F J.chart J.inputFrame J.outputFrame
  let f := globalSymbolInChart E F a.val J.chart J.inputFrame J.outputFrame
  have hU : IsOpen U := isOpen_symbolChartDomain E F J.chart J.inputFrame J.outputFrame
  have hf (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) :
      ContDiffAt ℝ ∞ (Function.uncurry f) (x, ξ) :=
    (a.property.1 J.chart J.mem_atlas J.inputFrame J.outputFrame).contDiffAt
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
  have hbound : BddAbove S := bddAbove_homogeneousSymbolSeminormValue_set E F m J a
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
        (globalSymbolInChart E F (z • a.val) J.chart J.inputFrame J.outputFrame)
        J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ‖} = ‖z‖ * sSup S
  rw [globalSymbolInChart_smul, himage]
  exact ((isLUB_csSup hS hbound).mul_left (norm_nonneg z)).csSup_eq (hS.image _)

/-- The standard C-infinity seminorm on a compact punctured coordinate product. -/
def homogeneousSymbolSeminorm
    (J : HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F) :
    Seminorm ℂ (homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) :=
  Seminorm.of (homogeneousSymbolSeminormValue E F m J)
    (homogeneousSymbolSeminormValue_add_le E F m J)
    (homogeneousSymbolSeminormValue_smul E F m J)

/-- These seminorms detect precisely the data away from the zero section. -/
theorem forall_homogeneousSymbolSeminorm_eq_zero_iff
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    (∀ J : HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F,
      homogeneousSymbolSeminorm E F m J a = 0) ↔
      ∀ x ξ, ξ ≠ 0 → a.val x ξ = 0 := by
  /- Forward: choose valid charts and frames at x and singleton compact sets for
  its coordinates and for the nonzero covector, with both derivative orders zero.
  The chart/frame isomorphisms recover a(x,ξ) from the zero norm. Reverse: all mixed
  derivatives vanish on the open punctured domains, so every supremum is zero.
  Values at zero remain arbitrary, including when n=0; do not conclude a=0. -/
  classical
  constructor
  · intro ha x ξ hξ
    -- A zero-order singleton test detects the value in one valid chart and pair of frames.
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hc := chart_mem_atlas (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    have hf : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
    let η := covectorInChart c x ξ
    have hη : η ≠ 0 := by
      intro hz
      apply hξ
      rw [← covectorFromChart_covectorInChart c hc x hx ξ, show covectorInChart c x ξ = 0 from hz]
      ext v
      change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) ((mfderiv _ _ c x) v) = 0
      exact inner_zero_left _
    let J : HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F :=
      { chart := c
        mem_atlas := hc
        inputFrame := e
        outputFrame := f
        input_mem_atlas := inferInstance
        output_mem_atlas := inferInstance
        localIndex :=
          { compactSet := {c x}
            subset_domain := by
              intro y hy
              obtain rfl := Set.mem_singleton_iff.mp hy
              exact ⟨⟨c.map_source hx, by simpa only [Set.mem_preimage, c.left_inv hx] using he⟩,
                by simpa only [Set.mem_preimage, c.left_inv hx] using hf⟩
            isCompact := isCompact_singleton
            spatialOrder := 0
            frequencyOrder := 0 }
        frequencySet := {η}
        isCompact_frequencySet := isCompact_singleton
        frequency_ne_zero := by intro ζ hζ; simpa only [Set.mem_singleton_iff.mp hζ] using hη }
    have hJ : homogeneousSymbolSeminormValue E F m J a = 0 := ha J
    have hle := le_csSup (bddAbove_homogeneousSymbolSeminormValue_set E F m J a)
      (show ‖symbolDerivative (globalSymbolInChart E F a.val c e f) 0 0 (c x) η‖ ∈
        {t : ℝ | ∃ y ∈ J.localIndex.compactSet, ∃ ζ ∈ J.frequencySet,
          t = ‖symbolDerivative (globalSymbolInChart E F a.val J.chart J.inputFrame J.outputFrame)
            J.localIndex.spatialOrder J.localIndex.frequencyOrder y ζ‖} from
        ⟨c x, Set.mem_singleton _, η, Set.mem_singleton _, rfl⟩)
    change ‖symbolDerivative (globalSymbolInChart E F a.val c e f) 0 0 (c x) η‖ ≤
      homogeneousSymbolSeminormValue E F m J a at hle
    rw [hJ] at hle
    simp only [symbolDerivative, norm_iteratedFDeriv_zero] at hle
    have hmap : globalSymbolInChart E F a.val c e f (c x) η = 0 :=
      norm_le_zero_iff.mp hle
    -- The inverse coordinate and frame maps recover the same actual fiber map.
    rw [globalSymbolInChart_covectorInChart E F a.val c hc e f x hx ξ] at hmap
    ext v
    have htest := congrArg
      (fun L : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) ↦
        f.symmL ℂ x (L (e.continuousLinearMapAt ℂ x v))) hmap
    simpa only [ContinuousLinearMap.comp_apply, e.symmL_continuousLinearMapAt he,
      f.symmL_continuousLinearMapAt hf, zero_apply, map_zero] using htest
  · intro ha J
    -- Vanishing off zero makes every coordinate function locally zero on its measured domain.
    let U := symbolChartDomain E F J.chart J.inputFrame J.outputFrame
    let f := globalSymbolInChart E F a.val J.chart J.inputFrame J.outputFrame
    have hU : IsOpen U := isOpen_symbolChartDomain E F J.chart J.inputFrame J.outputFrame
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
      change (J.outputFrame.continuousLinearMapAt ℂ (J.chart.symm x)).comp
        ((a.val (J.chart.symm x) (covectorFromChart J.chart (J.chart.symm x) ξ)).comp
          (J.inputFrame.symmL ℂ (J.chart.symm x))) = 0
      rw [ha _ _ hcov]
      simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
    -- Locality of each derivative handles arbitrary orders without conditions at zero.
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
    -- The supremum is zero for empty products and for a nonempty set of zero norms.
    change homogeneousSymbolSeminormValue E F m J a = 0
    by_cases hK : J.localIndex.compactSet.Nonempty
    swap
    · simp [homogeneousSymbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hK]
    by_cases hV : J.frequencySet.Nonempty
    swap
    · simp [homogeneousSymbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hV]
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
def homogeneousSymbolTopology :
    TopologicalSpace (homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) :=
  (SeminormFamily.moduleFilterBasis
    (homogeneousSymbolSeminorm (n := n) (r := r) (q := q) E F m)).topology

attribute [local instance] homogeneousSymbolTopology

/-- The selected topology is generated by the actual punctured derivative seminorms. -/
theorem withSeminorms_homogeneousSymbolTopology :
    WithSeminorms (homogeneousSymbolSeminorm (n := n) (r := r) (q := q) E F m) := by
  /- Unfold the chosen topology: it is exactly the module filter basis of this
  family of seminorms. This does not assert separation of zero-section values. -/

  exact ⟨rfl⟩

/-- Convergence tests uniform derivatives of differences on every compact punctured product. -/
theorem tendsto_homogeneousSymbolTopology_iff {Z : Type*} (l : Filter Z)
    (a : Z → homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    Tendsto a l (𝓝 b) ↔
      ∀ J : HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F,
        ∀ ε : ℝ, 0 < ε → ∀ᶠ z in l, homogeneousSymbolSeminorm E F m J (a z - b) < ε := by
  /- Apply WithSeminorms.tendsto_nhds to the displayed topology. Every derivative
  order is tested. Continuity of values alone does not imply this condition. -/

  exact (withSeminorms_homogeneousSymbolTopology E F m).tendsto_nhds a b

end AtiyahSinger
