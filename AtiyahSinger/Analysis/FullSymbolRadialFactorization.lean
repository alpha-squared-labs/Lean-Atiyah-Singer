/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolKClassHomotopy
public import AtiyahSinger.Analysis.FullSymbolRadialFreezing

import all AtiyahSinger.Analysis.FullSymbolRadialFreezing

/-!
# Actual exterior inverse symbols for radial factorization

Public module ID: M2294.

Use the actual inverse of the original full symbol on its proved exterior. A fixed smooth
metric cutoff removes the inner disk, while the existing compact-local inverse estimates
supply its order. No growth bound for the desired inverse is assumed. The transition is
between radii 3R/2 and 2R, wholly inside the region where the radial freezing still agrees
with the original symbol. The same actual target automorphism also transports the
compact-support class to the actual homogeneous radial representative.

Sources: SG III.4.2--4.4 and III.13.3. The explicit metric-cutoff construction is a project
supplement for the actual general-symbol comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Set
open scoped Manifold ContDiff Topology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- The actual exterior inverse, smoothly cut off before radius 3R/2. -/
def fullSymbolExteriorInverseFunction {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) :
    GlobalSymbolFunction (n := n) F E :=
  fun x ξ ↦
    ((Real.smoothTransition ((g.length x ξ - 3 * R / 2) / (R / 2)) : ℝ) : ℂ) •
      (a.val x ξ).inverse

/-- Exterior invertibility gives all-frequency smoothness of the same cutoff inverse. -/
theorem isSmoothFullGlobalSymbol_fullSymbolExteriorInverseFunction {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) (hR : 0 < R)
    (hi : ∀ x (ξ : CotangentFiber (n := n) x), R < g.length x ξ →
      (a.val x ξ).IsInvertible) :
    IsSmoothFullGlobalSymbol (r := q) (q := r) F E
      (fullSymbolExteriorInverseFunction a g R) := by
  /- Near the inner disk the cutoff is identically zero, so no inverse or smoothness
  of the length at the zero section is used. On the exterior, real smooth matrix
  inversion and the smooth off-zero metric length act in the original two frames. -/
  intro c hc f e _ _
  let V := symbolChartDomain E F c e f
  let W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) := V ×ˢ univ
  let w (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    g.length (c.symm p.1) (covectorFromChart c (c.symm p.1) p.2)
  let A := Function.uncurry (globalSymbolInChart E F a.val c e f)
  have hdomain : symbolChartDomain F E c f e = V := by
    ext z
    simp only [V, symbolChartDomain, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hdomain]
  have hV : IsOpen V := isOpen_symbolChartDomain E F c e f
  have hW : IsOpen W := hV.prod isOpen_univ
  have hw : ContinuousOn w W :=
    (g.continuous_length.comp_continuousOn
      (contMDiffOn_covectorFromChart_total c hc).continuousOn).mono
        (fun p hp ↦ ⟨hp.1.1.1, mem_univ _⟩)
  intro p hp
  by_cases hsmall : w p ≤ R
  · -- The transition starts strictly outside this whole inner neighborhood.
    have hwAt : ContinuousAt w p := (hw p hp).continuousAt (hW.mem_nhds hp)
    have hless : w p < 3 * R / 2 := by linarith
    have hnear : ∀ᶠ z in 𝓝 p, w z < 3 * R / 2 := hwAt (isOpen_Iio.mem_nhds hless)
    apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin q) →L[ℂ]
      EuclideanSpace ℂ (Fin r)))).congr_of_eventuallyEq
    filter_upwards [hnear] with z hz
    have hcut : Real.smoothTransition ((w z - 3 * R / 2) / (R / 2)) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hz.le) (by positivity))
    change globalSymbolInChart F E (fullSymbolExteriorInverseFunction a g R)
      c f e z.1 z.2 = 0
    simp only [globalSymbolInChart, fullSymbolExteriorInverseFunction, w, hcut,
      Complex.ofReal_zero, zero_smul, ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero]
  · have hlarge : R < w p := lt_of_not_ge hsmall
    have hpos : 0 < w p := hR.trans hlarge
    have hpne : p.2 ≠ 0 := by
      intro hz
      have hcovzero : covectorFromChart c (c.symm p.1) p.2 = 0 := by
        rw [hz]
        ext v
        change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (mfderiv _ _ c (c.symm p.1) v) = 0
        exact inner_zero_left _
      exact hpos.ne' ((g.length_eq_zero_iff _ _).mpr hcovzero)
    let Q := c.target ×ˢ {η : EuclideanSpace ℝ (Fin n) | η ≠ 0}
    have hQ : IsOpen Q := c.open_target.prod isOpen_ne
    have hwAt : ContDiffAt ℝ ∞ w p :=
      (g.contDiffOn_length_covectorFromChart c hc).contDiffAt
        (hQ.mem_nhds ⟨hp.1.1.1, hpne⟩)
    have hcut : ContDiffAt ℝ ∞ (fun z ↦
        ((Real.smoothTransition ((w z - 3 * R / 2) / (R / 2)) : ℝ) : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p
        (Real.smoothTransition.contDiff.contDiffAt.comp p
          ((hwAt.sub contDiffAt_const).div_const (R / 2)))
    have hInv : (A p).IsInvertible := by
      change ((f.continuousLinearMapAt ℂ (c.symm p.1)).comp
        ((a.val (c.symm p.1) (covectorFromChart c (c.symm p.1) p.2)).comp
          (e.symmL ℂ (c.symm p.1)))).IsInvertible
      rw [← f.coe_continuousLinearEquivAt_eq' (R := ℂ) hp.1.2,
        ← e.symm_continuousLinearEquivAt_eq' (R := ℂ) hp.1.1.2]
      exact ContinuousLinearMap.isInvertible_equiv.comp
        ((hi _ _ hlarge).comp ContinuousLinearMap.isInvertible_equiv)
    have hA : ContDiffAt ℝ ∞ A p :=
      (a.property c hc e f).1.contDiffAt (hW.mem_nhds hp)
    have hInvAt : ContDiffAt ℝ ∞ (fun z ↦ (A z).inverse) p :=
      ((hInv.contDiffAt_map_inverse (n := ∞)).restrict_scalars ℝ).comp p hA
    apply ContDiffAt.contDiffWithinAt
    apply (hcut.smul hInvAt).congr_of_eventuallyEq
    filter_upwards [hW.mem_nhds hp] with z hz
    have hcoord := globalSymbolInChart_globalSymbolInverse a.val c e f z.1 z.2 hz.1
    change globalSymbolInChart F E (fullSymbolExteriorInverseFunction a g R)
      c f e z.1 z.2 = _
    simp only [globalSymbolInChart, fullSymbolExteriorInverseFunction,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    change ((Real.smoothTransition ((w z - 3 * R / 2) / (R / 2)) : ℝ) : ℂ) •
      globalSymbolInChart F E (globalSymbolInverse a.val) c f e z.1 z.2 =
        ((Real.smoothTransition ((w z - 3 * R / 2) / (R / 2)) : ℝ) : ℂ) • (A z).inverse
    rw [hcoord]
    rfl

/-- Quantitative ellipticity supplies the order-minus-m bound for this actual exterior inverse. -/
theorem isGlobalSymbol_fullSymbolExteriorInverseFunction {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (he : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) (hR : 0 < R)
    (hi : ∀ x (ξ : CotangentFiber (n := n) x), R < g.length x ξ →
      (a.val x ξ).IsInvertible) :
    IsGlobalSymbol (r := q) (q := r) F E (-m)
      (fullSymbolExteriorInverseFunction a g R) := by
  /- Compare with the original compact-local inverse on an enlarged compact base
  neighborhood. Both functions are the same actual inverse at high frequency.
  Their smooth bounded-frequency difference is smoothing; adding it back proves
  the desired order without assuming any derivative estimate for the inverse. -/
  have hs := isSmoothFullGlobalSymbol_fullSymbolExteriorInverseFunction a g R hR hi
  intro c hc f e _ _
  let U := symbolChartDomain E F c e f
  let p := globalSymbolInChart E F a.val c e f
  let b := globalSymbolInChart F E (fullSymbolExteriorInverseFunction a g R) c f e
  have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
  have hdomain : symbolChartDomain F E c f e = U := by
    ext z
    simp only [U, symbolChartDomain, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hdomain]
  change IsSymbol U (-m) b
  have hb : ContDiffOn ℝ ∞ (Function.uncurry b) (U ×ˢ univ) := by
    simpa only [b, hdomain] using hs c hc f e
  obtain ⟨v, hv, hrecover⟩ := exists_inverse_symbol_of_isEllipticFullSymbol hU p
    (a.property c hc e f) (he c hc e f)
  refine ⟨hb, ?_⟩
  intro K hKU hK i j
  obtain ⟨K', hK', hKK', hK'U⟩ := exists_compact_between hK hU hKU
  have hint : interior K' ⊆ U := interior_subset.trans hK'U
  obtain ⟨S, _hS, heq⟩ := hrecover K' hK'U hK'
  have hK'c : K' ⊆ c.target := fun z hz ↦ (hK'U hz).1.1
  obtain ⟨d, D, hd, _hD, hlength⟩ := g.exists_length_bounds_on c hc K' hK' hK'c
  let T := max S (2 * R / d)
  have hdiff : ContDiffOn ℝ ∞ (Function.uncurry (b - v)) (interior K' ×ˢ univ) :=
    (hb.sub hv.1).mono (Set.prod_mono hint subset_rfl)
  have hzero : ∀ z ∈ interior K', ∀ η, T ≤ ‖η‖ → (b - v) z η = 0 := by
    intro z hz η hη
    have hmetric : 2 * R ≤ g.length (c.symm z) (covectorFromChart c (c.symm z) η) := by
      have hcoord : 2 * R ≤ d * ‖η‖ := by
        simpa only [mul_comm] using (div_le_iff₀ hd).mp ((le_max_right _ _).trans hη)
      exact hcoord.trans (hlength z (interior_subset hz) η).1
    have hcut : Real.smoothTransition
        ((g.length (c.symm z) (covectorFromChart c (c.symm z) η) - 3 * R / 2) /
          (R / 2)) = 1 := by
      apply Real.smoothTransition.one_of_one_le
      apply (le_div_iff₀ (show 0 < R / 2 by positivity)).mpr
      linarith
    have hactual : b z η = (p z η).inverse := by
      change globalSymbolInChart F E (fullSymbolExteriorInverseFunction a g R) c f e z η = _
      simp only [globalSymbolInChart, fullSymbolExteriorInverseFunction, hcut,
        Complex.ofReal_one, one_smul]
      exact globalSymbolInChart_globalSymbolInverse a.val c e f z η (hint hz)
    exact sub_eq_zero.mpr (hactual.trans
      (heq z (interior_subset hz) η ((le_max_left _ _).trans hη)).symm)
  have hsmall : IsSymbol (interior K') (-m) (b - v) :=
    isSmoothingSymbol_of_frequency_support isOpen_interior (b - v) T hdiff hzero (-m)
  have hsum : IsSymbol (interior K') (-m) b := by
    simpa only [sub_add_cancel] using IsSymbol.add isOpen_interior hsmall (hv.restrict hint)
  exact hsum.2 K hKK' hK i j


/-- The actual target comparison is identity where the original two symbols agree. -/
def fullSymbolRadialComparisonFunction {m : ℝ}
    (a b : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) :
    GlobalSymbolFunction (n := n) F F :=
  globalSymbolId F + globalSymbolComp (a.val - b.val) (fullSymbolExteriorInverseFunction b g R)

variable [IsSmoothComplexBundle (n := n) (r := q) F]

/-- Two elliptic symbols agreeing on the inner disk have an actual order-zero target factor. -/
theorem exists_fullSymbolTargetFactorization {m : ℝ}
    (a b : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val)
    (hb : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m b.val)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) (hR : 0 < R)
    (hi : ∀ x (ξ : CotangentFiber (n := n) x), R < g.length x ξ →
      (a.val x ξ).IsInvertible ∧ (b.val x ξ).IsInvertible)
    (hsame : ∀ x (ξ : CotangentFiber (n := n) x), g.length x ξ ≤ 2 * R →
      a.val x ξ = b.val x ξ) :
    ∃ u v : globalSymbolSpace (n := n) (r := q) (q := q) F F 0,
      u.val = fullSymbolRadialComparisonFunction a b g R ∧
      v.val = fullSymbolRadialComparisonFunction b a g R ∧
      globalSymbolComp u.val v.val = globalSymbolId F ∧
      globalSymbolComp v.val u.val = globalSymbolId F ∧
      globalSymbolComp u.val b.val = a.val ∧
      IsEllipticFullGlobalSymbol (r := q) (q := q) F F 0 u.val := by
  /- Both comparison functions use the actual cutoff inverses, hence have order zero.
  On the inner disk both are identity. Outside it the cutoff is one, so the same
  two functions are a b⁻¹ and b a⁻¹. Their two exact products and a = u b follow.
  The constructed inverse symbol then supplies quantitative ellipticity for u. -/
  have hia : ∀ x (ξ : CotangentFiber (n := n) x), R < g.length x ξ →
      (a.val x ξ).IsInvertible := fun x ξ hξ ↦ (hi x ξ hξ).1
  have hib : ∀ x (ξ : CotangentFiber (n := n) x), R < g.length x ξ →
      (b.val x ξ).IsInvertible := fun x ξ hξ ↦ (hi x ξ hξ).2
  -- The original symbol orders cancel against the proved orders of the cutoff inverses.
  have hca := isGlobalSymbol_fullSymbolExteriorInverseFunction a ha g R hR hia
  have hcb := isGlobalSymbol_fullSymbolExteriorInverseFunction b hb g R hR hib
  have hu : IsGlobalSymbol (r := q) (q := q) F F 0
      (fullSymbolRadialComparisonFunction a b g R) := by
    have hmul : IsGlobalSymbol (r := q) (q := q) F F 0
        (globalSymbolComp (a.val - b.val) (fullSymbolExteriorInverseFunction b g R)) := by
      simpa only [Submodule.coe_sub, add_neg_cancel] using
        (a - b).property.globalSymbolComp hcb
    exact (isGlobalSymbol_globalSymbolId (E := F) (r := q)).add hmul
  have hv : IsGlobalSymbol (r := q) (q := q) F F 0
      (fullSymbolRadialComparisonFunction b a g R) := by
    have hmul : IsGlobalSymbol (r := q) (q := q) F F 0
        (globalSymbolComp (b.val - a.val) (fullSymbolExteriorInverseFunction a g R)) := by
      simpa only [Submodule.coe_sub, add_neg_cancel] using
        (b - a).property.globalSymbolComp hca
    exact (isGlobalSymbol_globalSymbolId (E := F) (r := q)).add hmul
  let u : globalSymbolSpace (n := n) (r := q) (q := q) F F 0 :=
    ⟨fullSymbolRadialComparisonFunction a b g R, hu⟩
  let v : globalSymbolSpace (n := n) (r := q) (q := q) F F 0 :=
    ⟨fullSymbolRadialComparisonFunction b a g R, hv⟩
  -- These local identities concern the same actual matrices and the same metric radii.
  have hinner (a₁ a₂ : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
      (x : M) (ξ : CotangentFiber (n := n) x) (heq : a₁.val x ξ = a₂.val x ξ) :
      fullSymbolRadialComparisonFunction a₁ a₂ g R x ξ = ContinuousLinearMap.id ℂ (F x) := by
    change ContinuousLinearMap.id ℂ (F x) + (a₁.val x ξ - a₂.val x ξ).comp _ = _
    rw [heq, sub_self, ContinuousLinearMap.zero_comp, add_zero]
  have hratio (a₁ a₂ : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
      (x : M) (ξ : CotangentFiber (n := n) x) (hξ : 2 * R ≤ g.length x ξ)
      (hinv : (a₂.val x ξ).IsInvertible) :
      fullSymbolRadialComparisonFunction a₁ a₂ g R x ξ =
        (a₁.val x ξ).comp (a₂.val x ξ).inverse := by
    have hcut : Real.smoothTransition ((g.length x ξ - 3 * R / 2) / (R / 2)) = 1 := by
      apply Real.smoothTransition.one_of_one_le
      apply (le_div_iff₀ (show 0 < R / 2 by positivity)).mpr
      linarith
    change ContinuousLinearMap.id ℂ (F x) + (a₁.val x ξ - a₂.val x ξ).comp
      (((Real.smoothTransition ((g.length x ξ - 3 * R / 2) / (R / 2)) : ℝ) : ℂ) •
        (a₂.val x ξ).inverse) = _
    rw [hcut, Complex.ofReal_one, one_smul, ContinuousLinearMap.sub_comp,
      hinv.self_comp_inverse]
    abel
  have hUV : globalSymbolComp u.val v.val = globalSymbolId F := by
    funext x ξ
    change (fullSymbolRadialComparisonFunction a b g R x ξ).comp
      (fullSymbolRadialComparisonFunction b a g R x ξ) = ContinuousLinearMap.id ℂ (F x)
    by_cases hsmall : g.length x ξ ≤ 2 * R
    · rw [hinner a b x ξ (hsame x ξ hsmall), hinner b a x ξ (hsame x ξ hsmall).symm]
      exact ContinuousLinearMap.id_comp _
    · have hlarge : R < g.length x ξ := by linarith [lt_of_not_ge hsmall]
      obtain ⟨hax, hbx⟩ := hi x ξ hlarge
      rw [hratio a b x ξ (le_of_not_ge hsmall) hbx,
        hratio b a x ξ (le_of_not_ge hsmall) hax]
      ext w
      simp only [ContinuousLinearMap.comp_apply]
      rw [hbx.inverse_apply_self, hax.self_apply_inverse]
      rfl
  have hVU : globalSymbolComp v.val u.val = globalSymbolId F := by
    funext x ξ
    change (fullSymbolRadialComparisonFunction b a g R x ξ).comp
      (fullSymbolRadialComparisonFunction a b g R x ξ) = ContinuousLinearMap.id ℂ (F x)
    by_cases hsmall : g.length x ξ ≤ 2 * R
    · rw [hinner b a x ξ (hsame x ξ hsmall).symm, hinner a b x ξ (hsame x ξ hsmall)]
      exact ContinuousLinearMap.id_comp _
    · have hlarge : R < g.length x ξ := by linarith [lt_of_not_ge hsmall]
      obtain ⟨hax, hbx⟩ := hi x ξ hlarge
      rw [hratio b a x ξ (le_of_not_ge hsmall) hax,
        hratio a b x ξ (le_of_not_ge hsmall) hbx]
      ext w
      simp only [ContinuousLinearMap.comp_apply]
      rw [hax.inverse_apply_self, hbx.self_apply_inverse]
      rfl
  have hfactor : globalSymbolComp u.val b.val = a.val := by
    funext x ξ
    change (fullSymbolRadialComparisonFunction a b g R x ξ).comp (b.val x ξ) = a.val x ξ
    by_cases hsmall : g.length x ξ ≤ 2 * R
    · rw [hinner a b x ξ (hsame x ξ hsmall), ContinuousLinearMap.id_comp]
      exact (hsame x ξ hsmall).symm
    · have hlarge : R < g.length x ξ := by linarith [lt_of_not_ge hsmall]
      have hbx := (hi x ξ hlarge).2
      rw [hratio a b x ξ (le_of_not_ge hsmall) hbx]
      ext w
      simp only [ContinuousLinearMap.comp_apply]
      rw [hbx.inverse_apply_self]
  have hInvU (x : M) (ξ : CotangentFiber (n := n) x) : (u.val x ξ).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := v.val x ξ)
    · exact congrFun (congrFun hUV x) ξ
    · exact congrFun (congrFun hVU x) ξ
  have hactual : globalSymbolInverse u.val = v.val := by
    funext x ξ
    exact ContinuousLinearMap.inverse_eq (congrFun (congrFun hUV x) ξ)
      (congrFun (congrFun hVU x) ξ)
  -- The actual inverse is already a symbol of order zero, so its compact-local norms are bounded.
  have heU : IsEllipticFullGlobalSymbol (r := q) (q := q) F F 0 u.val := by
    intro c hc f e _ _ K hKU hK
    have hdomain : symbolChartDomain F F c e f = symbolChartDomain F F c f e := by
      ext z
      simp only [symbolChartDomain, Set.mem_inter_iff, Set.mem_preimage]
      tauto
    have hlocal : IsSymbol (symbolChartDomain F F c f e) 0
        (globalSymbolInChart F F v.val c e f) := by
      simpa only [hdomain] using v.property c hc e f
    obtain ⟨C, hC, hbound⟩ := hlocal.2 K hKU hK 0 0
    refine ⟨1, C + 1, zero_lt_one, by linarith, ?_⟩
    intro z hz η _hη
    have hzU := hKU hz
    have hmat : (globalSymbolInChart F F u.val c f e z η).IsInvertible := by
      change ((e.continuousLinearMapAt ℂ (c.symm z)).comp
        ((u.val (c.symm z) (covectorFromChart c (c.symm z) η)).comp
          (f.symmL ℂ (c.symm z)))).IsInvertible
      rw [← e.coe_continuousLinearEquivAt_eq' (R := ℂ) hzU.2,
        ← f.symm_continuousLinearEquivAt_eq' (R := ℂ) hzU.1.2]
      exact ContinuousLinearMap.isInvertible_equiv.comp
        ((hInvU _ _).comp ContinuousLinearMap.isInvertible_equiv)
    refine ⟨hmat, ?_⟩
    rw [← globalSymbolInChart_globalSymbolInverse u.val c f e z η hzU, hactual]
    have hbnd : ‖globalSymbolInChart F F v.val c e f z η‖ ≤ C := by
      simpa only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero,
        Real.rpow_zero, mul_one] using hbound z hz η
    simpa only [neg_zero, Real.rpow_zero, mul_one] using
      hbnd.trans (show C ≤ C + 1 by linarith)
  exact ⟨u, v, rfl, rfl, hUV, hVU, hfactor, heU⟩

attribute [local instance] ComplexBundle.isFiniteRank_pullback

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

/-- A general elliptic symbol factors through an actual homogeneous model with the same K class. -/
theorem IsEllipticFullGlobalSymbol.exists_radialFactorization {m : ℝ}
    {a : globalSymbolSpace (n := n) (r := r) (q := q) E F m}
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F) :
    ∃ (p : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
      (hp : IsEllipticGlobalSymbol E F p.val)
      (b : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
      (_hb : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m b.val)
      (u v : globalSymbolSpace (n := n) (r := q) (q := q) F F 0),
      globalSymbolComp u.val v.val = globalSymbolId F ∧
      globalSymbolComp v.val u.val = globalSymbolId F ∧
      globalSymbolComp u.val b.val = a.val ∧
      IsEllipticFullGlobalSymbol (r := q) (q := q) F F 0 u.val ∧
      globalPrincipalSymbolClass E F m b =
        globalPrincipalSymbolClass E F m
          (A.regularizedSymbol m p.val p.property.1 p.property.2) ∧
      fullSymbolKClass a ha = symbolKClass p.val p.property.1.continuous hp := by
  /- Freeze the original symbol outside its ellipticity disk. Its exact order-zero
  target factor is a continuous automorphism of the original cotangent pullback.
  This identifies the two full-symbol K classes, without identifying their
  principal quotient classes. Only the frozen symbol is then compared with the
  regularization of the homogeneous radial model. -/
  obtain ⟨R, hR, b, hbval, hb, hi, hclass⟩ :=
    ha.exists_fullSymbolFrozenEllipticSymbol g A
  -- The inner disk agrees as original fiber maps, so the actual target factors exist.
  have hsame (x : M) (ξ : CotangentFiber (n := n) x)
      (hξ : g.length x ξ ≤ 2 * R) : a.val x ξ = b.val x ξ := by
    rw [hbval]
    exact (fullSymbolFrozenFunction_eq_of_length_le a g R hR x ξ hξ).symm
  obtain ⟨u, v, _hu, _hv, hUV, hVU, hfactor, heU⟩ :=
    exists_fullSymbolTargetFactorization a b ha hb g R hR hi hsame
  let p := fullSymbolRadialPrincipalSymbol a g R
  let c := A.regularizedSymbol m p.val p.property.1 p.property.2
  have hc : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m c.val :=
    (isEllipticFullGlobalSymbol_iff_of_class_eq b c hclass).mp hb
  have hp : IsEllipticGlobalSymbol E F p.val :=
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff A m p.val
      p.property.1 p.property.2).mp hc
  -- Convert the same order-zero target map to an actual pullback-bundle isomorphism.
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := ComplexBundle.isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let U : ComplexBundle.Iso
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) :=
    (fullSymbolBundleHom u).toIso <| by
      intro z
      change Function.Bijective (u.val z.proj z.snd)
      exact (ContinuousLinearMap.IsInvertible.of_inverse
        (congrFun (congrFun hUV z.proj) z.snd)
        (congrFun (congrFun hVU z.proj) z.snd)).bijective
  have hK : fullSymbolKClass a ha = fullSymbolKClass b hb := by
    apply fullSymbolKClass_eq_of_targetIso a b ha hb U
    intro z w
    change a.val z.proj z.snd w = u.val z.proj z.snd (b.val z.proj z.snd w)
    exact (congrArg (fun f : E z.proj →L[ℂ] F z.proj ↦ f w)
      (congrFun (congrFun hfactor z.proj) z.snd)).symm
  -- The accepted lower-order homotopy and regularization preserve this same K class.
  have hrad : fullSymbolKClass a ha = symbolKClass p.val p.property.1.continuous hp :=
    hK.trans ((fullSymbolKClass_eq_of_principalClass_eq b c hb hc hclass).trans
      (fullSymbolKClass_regularizedSymbol A p hp))
  exact ⟨p, hp, b, hb, u, v, hUV, hVU, hfactor, heU, hclass, hrad⟩

end AtiyahSinger
