/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalHomogeneousSymbol
public import AtiyahSinger.Analysis.GlobalSymbolComposition
public import AtiyahSinger.Analysis.HomogeneousSymbolTopology

/-!
# Multiplication of original homogeneous principal classes

Public module ID: M0747.

Independent regularizations of composable homogeneous symbols have the class
of their specified homogeneous product. The actual pointwise error has every
symbol order: on compact neighborhoods with a common intermediate bundle frame,
all three regularizations agree with the original symbols at high frequency.
This supplies the principal-class comparison used by the geometric composition,
bundle-isomorphism and direct-sum index relations.

Sources: SG III.3, Theorems 3.10 and 3.17, and III.13's homogeneous representative
route. The explicit comparison of independent regularizations is a supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff

variable {n r q d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F H : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [∀ x, NormedAddCommGroup (H x)] [∀ x, NormedSpace ℂ (H x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin d)) H)]
  [FiberBundle (EuclideanSpace ℂ (Fin d)) H]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin d)) H]

/-- The actual fiberwise product of two punctured smooth symbols is punctured smooth. -/
theorem IsSmoothOffZeroGlobalSymbol.globalSymbolComp
    {a : GlobalSymbolFunction (n := n) E F} {b : GlobalSymbolFunction (n := n) F H}
    (hb : IsSmoothOffZeroGlobalSymbol (r := q) (q := d) F H b)
    (ha : IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F a) :
    IsSmoothOffZeroGlobalSymbol (r := r) (q := d) E H (AtiyahSinger.globalSymbolComp b a) := by
  intro c hc e g _ _ z hz
  -- A middle frame is chosen on an actual neighborhood of this point, never globally.
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F (c.symm z.1)
  let U := symbolChartDomain E F c e f ∩ symbolChartDomain F H c f g
  have hf : c.symm z.1 ∈ f.baseSet := mem_baseSet_trivializationAt _ _ _
  have hU : IsOpen U := (isOpen_symbolChartDomain E F c e f).inter
    (isOpen_symbolChartDomain F H c f g)
  have hzU : z.1 ∈ U := ⟨⟨⟨hz.1.1.1, hz.1.1.2⟩, hf⟩,
    ⟨⟨hz.1.1.1, hf⟩, hz.1.2⟩⟩
  have hdomain : IsOpen (U ×ˢ {ξ : EuclideanSpace ℝ (Fin n) | ξ ≠ 0}) :=
    hU.prod isClosed_singleton.isOpen_compl
  have ha' : ContDiffOn ℝ ∞ (Function.uncurry (globalSymbolInChart E F a c e f))
      (U ×ˢ {ξ | ξ ≠ 0}) :=
    (ha c hc e f).mono (prod_mono inter_subset_left subset_rfl)
  have hb' : ContDiffOn ℝ ∞ (Function.uncurry (globalSymbolInChart F H b c f g))
      (U ×ˢ {ξ | ξ ≠ 0}) :=
    (hb c hc f g).mono (prod_mono inter_subset_right subset_rfl)
  let B := (ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ (Fin r))
    (EuclideanSpace ℂ (Fin q)) (EuclideanSpace ℂ (Fin d))).bilinearRestrictScalars ℝ
  have hp := B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hb' ha'
  have hproduct : ContDiffOn ℝ ∞
      (Function.uncurry (globalSymbolInChart E H (AtiyahSinger.globalSymbolComp b a) c e g))
      (U ×ˢ {ξ | ξ ≠ 0}) := by
    apply hp.congr
    intro y hy
    exact globalSymbolInChart_globalSymbolComp b a c e f g y.1 y.2 hy.1.1.2
  exact (hproduct.contDiffAt (hdomain.mem_nhds ⟨hzU, hz.2⟩)).contDiffWithinAt

/-- Positive homogeneity degrees add under the actual fiberwise product. -/
theorem IsHomogeneousGlobalSymbol.globalSymbolComp {l m : ℝ}
    {a : GlobalSymbolFunction (n := n) E F} {b : GlobalSymbolFunction (n := n) F H}
    (hb : IsHomogeneousGlobalSymbol F H l b) (ha : IsHomogeneousGlobalSymbol E F m a) :
    IsHomogeneousGlobalSymbol E H (l + m) (AtiyahSinger.globalSymbolComp b a) := by
  intro x ξ hξ t ht
  simp only [AtiyahSinger.globalSymbolComp, hb x ξ hξ t ht, ha x ξ hξ t ht,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add ht, add_comm m l]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsSmoothComplexBundle (n := n) (r := d) H]

/-- Regularizing composable homogeneous symbols changes their pointwise product only by
an error of every symbol order, compared with the same specified homogeneous product. -/
theorem isGlobalSymbol_regularizedSymbol_comp_sub
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (B : QuantizationPresentation (n := n) (r := q) (q := d) F H)
    (C : QuantizationPresentation (n := n) (r := r) (q := d) E H)
    {l m : ℝ} (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := q) (q := d) F H l)
    (c : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := d) E H (l + m))
    (hcomp : ∀ x ξ, ξ ≠ 0 → c.val x ξ = globalSymbolComp b.val a.val x ξ) (k : ℝ) :
    IsGlobalSymbol (n := n) (r := r) (q := d) E H k
      (globalSymbolComp (B.regularizedSymbolFunction b.val)
        (A.regularizedSymbolFunction a.val) - C.regularizedSymbolFunction c.val) := by
  classical
  have hA := A.isGlobalSymbol_regularizedSymbolFunction m a.val a.property.1 a.property.2
  have hB := B.isGlobalSymbol_regularizedSymbolFunction l b.val b.property.1 b.property.2
  have hC := C.isGlobalSymbol_regularizedSymbolFunction (l + m) c.val c.property.1 c.property.2
  intro chart hchart e f _ _
  let U := symbolChartDomain E H chart e f
  let p := globalSymbolInChart E H
    (globalSymbolComp (B.regularizedSymbolFunction b.val)
      (A.regularizedSymbolFunction a.val) - C.regularizedSymbolFunction c.val) chart e f
  have hU : IsOpen U := isOpen_symbolChartDomain E H chart e f
  have hsplit : p = globalSymbolInChart E H
      (globalSymbolComp (B.regularizedSymbolFunction b.val)
        (A.regularizedSymbolFunction a.val)) chart e f -
      globalSymbolInChart E H (C.regularizedSymbolFunction c.val) chart e f := by
    ext z η v
    simp [p, globalSymbolInChart]
  have hp : ContDiffOn ℝ ∞ (Function.uncurry p) (U ×ˢ univ) := by
    rw [hsplit]
    exact ((hB.globalSymbolComp hA) chart hchart e f).1.sub (hC chart hchart e f).1
  change IsSymbol U k p
  refine ⟨hp, ?_⟩
  intro K hKU hK i j
  -- A genuine middle frame is fixed on each compact neighborhood before taking derivatives.
  have hlocal (z : U) : ∃ N : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact N ∧ z.val ∈ interior N ∧ ∃ D : ℝ, 0 ≤ D ∧
        ∀ x ∈ N, ∀ η, ‖symbolDerivative p i j x η‖ ≤
          D * (1 + ‖η‖) ^ (k - (j : ℝ)) := by
    let f₀ := trivializationAt (EuclideanSpace ℂ (Fin q)) F (chart.symm z.val)
    let V := symbolChartDomain E F chart e f₀ ∩ symbolChartDomain F H chart f₀ f
    have hf₀ : chart.symm z.val ∈ f₀.baseSet := mem_baseSet_trivializationAt _ _ _
    have hV : IsOpen V := (isOpen_symbolChartDomain E F chart e f₀).inter
      (isOpen_symbolChartDomain F H chart f₀ f)
    have hzV : z.val ∈ V :=
      ⟨⟨⟨z.property.1.1, z.property.1.2⟩, hf₀⟩,
        ⟨⟨z.property.1.1, hf₀⟩, z.property.2⟩⟩
    have hVU : V ⊆ U := fun y hy ↦ ⟨⟨hy.1.1.1, hy.1.1.2⟩, hy.2.2⟩
    obtain ⟨L, hL, hzL, hLV⟩ := exists_compact_subset hV hzV
    obtain ⟨N, hN, hzN, hNL⟩ := exists_compact_subset isOpen_interior hzL
    obtain ⟨RA, hRA, hrecoverA⟩ :=
      A.regularizedSymbolFunction_eq_inChart_at_high_frequency a.val chart hchart e f₀ L hL
        (hLV.trans inter_subset_left)
    obtain ⟨RB, _, hrecoverB⟩ :=
      B.regularizedSymbolFunction_eq_inChart_at_high_frequency b.val chart hchart f₀ f L hL
        (hLV.trans inter_subset_right)
    obtain ⟨RC, _, hrecoverC⟩ :=
      C.regularizedSymbolFunction_eq_inChart_at_high_frequency c.val chart hchart e f L hL
        (hLV.trans hVU)
    let R := max RA (max RB RC)
    have hsupp : ∀ y ∈ interior L, ∀ η, R ≤ ‖η‖ → p y η = 0 := by
      intro y hy η hη
      have hyV := hLV (interior_subset hy)
      have hAη : RA ≤ ‖η‖ := (le_max_left _ _).trans hη
      have hBη : RB ≤ ‖η‖ := (le_max_left _ _).trans ((le_max_right _ _).trans hη)
      have hCη : RC ≤ ‖η‖ := (le_max_right _ _).trans ((le_max_right _ _).trans hη)
      have hηne : η ≠ 0 := norm_pos_iff.mp (hRA.trans_le hAη)
      have hξne : covectorFromChart chart (chart.symm y) η ≠ 0 := by
        intro hzero
        have hrecover := covectorInChart_covectorFromChart chart hchart (chart.symm y)
          (chart.map_target hyV.1.1.1) η
        rw [hzero] at hrecover
        apply hηne
        apply (WithLp.ext_iff 2).mpr
        funext a
        have ha := congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ v a) hrecover
        change (0 : ℝ) = η a at ha
        exact ha.symm
      rw [hsplit]
      simp only [Pi.sub_apply]
      rw [globalSymbolInChart_globalSymbolComp _ _ chart e f₀ f y η hyV.1.2]
      simp only [symbolComp]
      rw [hrecoverB y (interior_subset hy) η hBη,
        hrecoverA y (interior_subset hy) η hAη,
        hrecoverC y (interior_subset hy) η hCη]
      change symbolComp (globalSymbolInChart F H b.val chart f₀ f)
          (globalSymbolInChart E F a.val chart e f₀) y η -
        globalSymbolInChart E H c.val chart e f y η = 0
      rw [← globalSymbolInChart_globalSymbolComp b.val a.val chart e f₀ f y η hyV.1.2]
      unfold globalSymbolInChart
      rw [hcomp (chart.symm y) (covectorFromChart chart (chart.symm y) η) hξne, sub_self]
    -- Frequency agreement on this neighborhood controls all spatial and frequency derivatives.
    have hint : interior L ⊆ U := (interior_subset.trans hLV).trans hVU
    have hsmoothing := isSmoothingSymbol_of_frequency_support isOpen_interior p R
      (hp.mono (Set.prod_mono hint subset_rfl)) hsupp k
    obtain ⟨D, hD, hbound⟩ := hsmoothing.2 N hNL hN i j
    exact ⟨N, hN, hzN, D, hD, hbound⟩
  choose N hN hzN D hD hbound using hlocal
  -- A finite subcover returns an estimate on the originally requested compact set.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : U ↦ interior (N z))
    (fun _ ↦ isOpen_interior) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hzN ⟨x, hKU hx⟩⟩)
  refine ⟨∑ z ∈ t, D z, Finset.sum_nonneg (fun z _ ↦ hD z), ?_⟩
  intro x hx η
  obtain ⟨z, hzt, hxz⟩ := mem_iUnion₂.mp (ht hx)
  apply (hbound z x (interior_subset hxz) η).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  exact Finset.single_le_sum (fun z _ ↦ hD z) hzt

/-- Composition of independently regularized principal classes is the class of the
specified off-zero homogeneous product. -/
theorem globalPrincipalSymbolComp_regularizedSymbol_eq
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (B : QuantizationPresentation (n := n) (r := q) (q := d) F H)
    (C : QuantizationPresentation (n := n) (r := r) (q := d) E H)
    {l m : ℝ} (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := q) (q := d) F H l)
    (c : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := d) E H (l + m))
    (hcomp : ∀ x ξ, ξ ≠ 0 → c.val x ξ = globalSymbolComp b.val a.val x ξ) :
    globalPrincipalSymbolComp
        (globalPrincipalSymbolClass F H l
          (B.regularizedSymbol l b.val b.property.1 b.property.2))
        (globalPrincipalSymbolClass E F m
          (A.regularizedSymbol m a.val a.property.1 a.property.2)) =
      globalPrincipalSymbolClass E H (l + m)
        (C.regularizedSymbol (l + m) c.val c.property.1 c.property.2) := by
  rw [globalPrincipalSymbolComp_class, globalPrincipalSymbolClass_eq_iff]
  exact isGlobalSymbol_regularizedSymbol_comp_sub A B C a b c hcomp ((l + m) - 1)

end AtiyahSinger
