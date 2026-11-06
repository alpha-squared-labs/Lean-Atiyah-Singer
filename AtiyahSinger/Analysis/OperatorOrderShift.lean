/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OrderReduction

/-!
# Changing an elliptic operator's order without changing its index or symbol class

Public module ID: M0838.

A09: the consumer of the order-reducing isomorphism in SG III.13, p.247.
Precomposition changes the actual PDO order to any prescribed real value.
Its new principal representative is specified off zero, and both the original
smooth index and the compact-support K class are retained. Values at zero and
the empty-cosphere case are not used to discard the source-minus-target class.
The real-order existence construction and its source boundary are recorded in
OrderReduction. Composition and a common high-frequency comparison retain the
specified regularization, while the same cosphere restriction preserves the K class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  [MeasurableSpace M] [hB : BorelSpace M]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

namespace PseudodifferentialOperator

include hM hT hSC hC hE hF hB hμ in
/-- SG order reduction, retaining the original map, index and displayed symbol K class.

The prescribed target order may be any real value, including zero and one.
No equality of source and target ranks or positive dimension is assumed.
-/
theorem exists_orderShift {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2))
    (hi : IsEllipticGlobalSymbol E F a.val) (t : ℝ) :
    ∃ (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ t)
      (b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F t)
      (hj : IsEllipticGlobalSymbol E F b.val)
      (U : smoothSections (n := n) (r := r) E ≃ₗ[ℂ]
        smoothSections (n := n) (r := r) E),
      Q.toLinearMap = P.toLinearMap.comp U.toLinearMap ∧
      Q.principalSymbol = globalPrincipalSymbolClass E F t
        (R.regularizedSymbol t b.val b.property.1 b.property.2) ∧
      (∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        b.val x ξ = (g.length x ξ ^ (t - m) : ℝ) • a.val x ξ) ∧
      Q.IsElliptic ∧ Q.toLinearMap.index = P.toLinearMap.index ∧
      homogeneousSymbolKClass t b hj = homogeneousSymbolKClass m a hi := by
  classical
  -- Keep the actual composite order definitionally equal to the requested target order.
  generalize hd : t - m = d
  have ht : t = m + d := by rw [← hd]; ring
  subst t
  obtain ⟨R₀⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := r) (E := E) (F := E)
  obtain ⟨c, J, U, hc, hJclass, hJU, _, _⟩ := exists_elliptic_orderReduction μ g R₀ d
  let Q := P.comp J
  let a₀ := cosphereRestriction g a.val
  let b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F (m + d) :=
    ⟨cosphereExtension g (m + d) a₀,
      (isSmoothOffZeroGlobalSymbol_cosphereExtension_iff g (m + d) a₀).mpr
        (isSmoothCosphereSymbol_restriction g a.val a.property.1),
      isHomogeneousGlobalSymbol_cosphereExtension g (m + d) a₀⟩
  -- The positive radial factor changes the degree without changing any cosphere value.
  have hb (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      b.val x ξ = (g.length x ξ ^ d : ℝ) • a.val x ξ := by
    change cosphereExtension g (m + d) a₀ x ξ = _
    rw [← cosphereExtension_restriction g m a.val a.property.2 x ξ hξ,
      cosphereExtension_of_ne_zero g (m + d) a₀ x ξ hξ,
      cosphereExtension_of_ne_zero g m a₀ x ξ hξ,
      Real.rpow_add (g.length_pos x ξ hξ), Complex.ofReal_mul,
      mul_comm, mul_smul, Complex.coe_smul]
    rfl
  have hj : IsEllipticGlobalSymbol E F b.val := by
    intro x ξ hξ
    rw [hb x ξ hξ]
    exact (IsUnit.smul_bijective
      (isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos (g.length_pos x ξ hξ) d).ne')).comp
      (hi x ξ hξ)
  have hprod (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      globalSymbolComp a.val c.val x ξ = b.val x ξ := by
    change (a.val x ξ).comp (c.val x ξ) = _
    rw [hc x ξ hξ, hb x ξ hξ, ← Complex.coe_smul, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_id, Complex.coe_smul]
  let pa := R.regularizedSymbol m a.val a.property.1 a.property.2
  let pc := R₀.regularizedSymbol d c.val c.property.1 c.property.2
  let pb := R.regularizedSymbol (m + d) b.val b.property.1 b.property.2
  -- Compare the specified regularizations on enlarged compact coordinate neighborhoods.
  have hlow : IsGlobalSymbol (n := n) (r := r) (q := q) E F (m + d - 1)
      ((globalSymbolSpaceComp pa pc).val - pb.val) := by
    intro chart hchart e f _ _
    let V := symbolChartDomain E F chart e f
    let va := globalSymbolInChart E F (globalSymbolSpaceComp pa pc).val chart e f
    let vb := globalSymbolInChart E F pb.val chart e f
    have hV : IsOpen V := isOpen_symbolChartDomain E F chart e f
    have hsplit : globalSymbolInChart E F
        ((globalSymbolSpaceComp pa pc).val - pb.val) chart e f = va - vb := by
      ext z η v
      simp [globalSymbolInChart, va, vb]
    rw [hsplit]
    have hs : ContDiffOn ℝ ∞ (Function.uncurry (va - vb)) (V ×ˢ Set.univ) :=
      ((globalSymbolSpaceComp pa pc).property chart hchart e f).1.sub
        (pb.property chart hchart e f).1
    refine ⟨hs, ?_⟩
    intro K hKV hK i j
    obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
    have hint : interior K' ⊆ V := interior_subset.trans hK'V
    have hKE : K' ⊆ symbolChartDomain E E chart e e :=
      fun z hz ↦ ⟨(hK'V hz).1, (hK'V hz).1.2⟩
    obtain ⟨Ra, hRa, haRec⟩ := R.regularizedSymbolFunction_eq_inChart_at_high_frequency
      a.val chart hchart e f K' hK' hK'V
    obtain ⟨Rc, _, hcRec⟩ := R₀.regularizedSymbolFunction_eq_inChart_at_high_frequency
      c.val chart hchart e e K' hK' hKE
    obtain ⟨Rb, _, hbRec⟩ := R.regularizedSymbolFunction_eq_inChart_at_high_frequency
      b.val chart hchart e f K' hK' hK'V
    let radius := max Ra (max Rc Rb)
    have hsupport : ∀ z ∈ interior K', ∀ η, radius ≤ ‖η‖ → (va - vb) z η = 0 := by
      intro z hz η hη
      have hza := (le_max_left Ra (max Rc Rb)).trans hη
      have hzc := (le_max_left Rc Rb).trans ((le_max_right Ra (max Rc Rb)).trans hη)
      have hzb := (le_max_right Rc Rb).trans ((le_max_right Ra (max Rc Rb)).trans hη)
      have hξ : covectorFromChart chart (chart.symm z) η ≠ 0 := by
        intro hzero
        have hiCoord := covectorInChart_covectorFromChart chart hchart
          (chart.symm z) (chart.map_target (hint hz).1.1) η
        rw [hzero] at hiCoord
        have hηzero : covectorInChart chart (chart.symm z) 0 = 0 := by ext k; rfl
        exact (norm_pos_iff.mp (hRa.trans_le hza)) (hiCoord.symm.trans hηzero)
      change globalSymbolInChart E F (globalSymbolComp pa.val pc.val) chart e f z η -
        globalSymbolInChart E F pb.val chart e f z η = 0
      rw [globalSymbolInChart_globalSymbolComp pa.val pc.val chart e e f z η (hint hz).1.2]
      dsimp only [symbolComp, pa, pc, pb, QuantizationPresentation.regularizedSymbol]
      rw [haRec z (interior_subset hz) η hza, hcRec z (interior_subset hz) η hzc,
        hbRec z (interior_subset hz) η hzb]
      change symbolComp (globalSymbolInChart E F a.val chart e f)
        (globalSymbolInChart E E c.val chart e e) z η -
          globalSymbolInChart E F b.val chart e f z η = 0
      rw [← globalSymbolInChart_globalSymbolComp a.val c.val chart e e f z η (hint hz).1.2]
      simp only [globalSymbolInChart, hprod _ _ hξ, sub_self]
    have hlocal := isSmoothingSymbol_of_frequency_support isOpen_interior (va - vb) radius
      (hs.mono (Set.prod_mono hint Set.Subset.rfl)) hsupport (m + d - 1)
    exact hlocal.2 K hKK' hK i j
  have hQclass : Q.principalSymbol = globalPrincipalSymbolClass E F (m + d) pb := by
    rw [principalSymbol_comp, hP, hJclass, globalPrincipalSymbolComp_class]
    exact (globalPrincipalSymbolClass_eq_iff E F (m + d) _ _).mpr hlow
  have hQ : Q.IsElliptic :=
    (Q.isElliptic_iff_homogeneous R b hQclass).mpr hj
  refine ⟨Q, b, hj, U, ?_, hQclass, hb, hQ, ?_, ?_⟩
  · change P.toLinearMap.comp J.toLinearMap = _
    rw [hJU]
  · -- Precomposition by the same smooth equivalence preserves kernel and range.
    change (P.toLinearMap.comp J.toLinearMap).index = _
    rw [hJU]
    let K : (P.toLinearMap.comp U.toLinearMap).ker ≃ₗ[ℂ] P.toLinearMap.ker :=
      { toFun := fun u ↦ ⟨U u.val, u.property⟩
        invFun := fun v ↦ ⟨U.symm v.val, by
          change P.toLinearMap (U (U.symm v.val)) = 0
          rw [U.apply_symm_apply]
          exact v.property⟩
        left_inv := fun u ↦ Subtype.ext (U.symm_apply_apply u.val)
        right_inv := fun v ↦ Subtype.ext (U.apply_symm_apply v.val)
        map_add' := fun u v ↦ Subtype.ext (U.map_add u.val v.val)
        map_smul' := fun a u ↦ Subtype.ext (U.map_smul a u.val) }
    have hrange : (P.toLinearMap.comp U.toLinearMap).range = P.toLinearMap.range := by
      rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr U.surjective, Submodule.map_top]
    rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub, hrange, K.finrank_eq]
  · -- The compact-support class keeps both original bundles, including when the cosphere is empty.
    rw [homogeneousSymbolKClass_eq_cosphere g (m + d) b hj,
      homogeneousSymbolKClass_eq_cosphere g m a hi]
    apply cosphereKClass_congr
    change cosphereRestriction g (cosphereExtension g (m + d) a₀) = a₀
    exact cosphereRestriction_extension g (m + d) a₀

end PseudodifferentialOperator

end AtiyahSinger
