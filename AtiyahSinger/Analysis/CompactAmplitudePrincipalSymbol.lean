/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactAmplitudeIntegral
public import AtiyahSinger.Analysis.GlobalPrincipalSymbol

/-!
# Principal symbols of compact amplitude integrals

Public module ID: M0346.

The actual integral piece and its principal representative are constructed together.
The reduced symbol of the integrated amplitude differs from its integrated diagonal
by one symbol order. The comparison retains both original cutoffs and the original
chart and frames, and is made in the actual global symbol space.

This is the compact-parameter form of SG III.3.5 and III.3.18. It supplies the
principal-symbol certificate needed by geometric Haar averaging without selecting
an unrelated representative after constructing the operator integral.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory Set
open scoped ContDiff Manifold SchwartzMap


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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]

open Classical in
set_option maxSynthPendingDepth 25 in
/-- A uniform compact amplitude family integrates to one actual PDO piece whose global
principal representative is the integrated amplitude diagonal in the same original cutoffs. -/
theorem PseudodifferentialPiece.exists_integral_of_uniform_amplitudes_with_principalSymbol {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (a : Y → AmplitudeFunction n r q) (ha : ∀ t, IsAmplitude m (a t))
    (T : Y → (𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))))
    (hT : ∀ t u z, T t u z = amplitudeApply (a t) u z)
    (K : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hsupp : ∀ t, tsupport (Function.uncurry (a t)) ⊆ K)
    (hmixed : ∀ i j k : ℕ, Continuous
      (fun p : Y × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n)) ↦ amplitudeDerivative (a p.1) i j k
          p.2.1.1 p.2.1.2 p.2.2))
    (hjoint : ∀ l : ℕ, Continuous
      (fun p : Y × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n)) ↦ iteratedFDeriv ℝ l
          (fun z : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
            EuclideanSpace ℝ (Fin n) ↦ a p.1 z.1.1 z.1.2 z.2) p.2))
    (hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      IsCompact K → ∀ i j k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t x y, (x, y) ∈ K → ∀ ξ,
        ‖amplitudeDerivative (a t) i j k x y ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - (k : ℝ))) :
    let := L.input.frame_mem_atlas
    let := L.output.frame_mem_atlas
    ∃ Q : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m,
      (∀ (u : smoothSections (n := n) (r := r) E) (x : M),
        (Q.toLinearMap u).val x =
          ∫ t, (L.output.extendLinearMap L.chart_mem_atlas
            (T t (L.input.localize L.chart_mem_atlas u))).val x ∂μ) ∧
      IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1)
        (Q.globalSymbolFunction - fun x ξ ↦
          if x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet then
            ((L.output.cutoff (L.chart x) * L.input.cutoff (L.chart x) : ℝ) : ℂ) •
              (L.output.frame.symmL ℂ x).comp
                ((∫ t, a t (L.chart x) (L.chart x)
                  (covectorInChart L.chart x ξ) ∂μ).comp
                  (L.input.frame.continuousLinearMapAt ℂ x))
          else 0) := by
  classical
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let abar : AmplitudeFunction n r q := fun x y ξ ↦ ∫ t, a t x y ξ ∂μ
  have habar : IsAmplitude m abar :=
    isAmplitude_integral_of_continuous_jets μ a ha hmixed hjoint hbound
  have hcompact : HasCompactSupport (Function.uncurry abar) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ hK.isClosed
    intro z hz
    by_contra hout
    have hzero (t : Y) : Function.uncurry (a t) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hout (hsupp t h))
    apply hz
    funext ξ
    change (∫ t, a t z.1 z.2 ξ ∂μ) = 0
    have hzero' (t : Y) : a t z.1 z.2 ξ = 0 := congrFun (hzero t) ξ
    simp only [hzero', integral_zero]
  -- Reduce only the integrated amplitude, retaining the exact original action.
  let Q : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
    { L with
      symbol := amplitudeSymbol abar
      isSymbol := isSymbol_amplitudeSymbol m abar habar hcompact
      operator := amplitudeOperator m abar habar hcompact
      operator_apply := fun u z ↦ (amplitudeOperator_apply m abar habar hcompact u z).trans
        (congrFun (quantize_amplitudeSymbol m abar habar hcompact u) z).symm }
  -- Reduce the integrated amplitude through degree zero, with its actual diagonal.
  let diagonal : SymbolFunction n r q := fun x ξ ↦ abar x x ξ
  let remainder := amplitudeSymbol abar - diagonal
  have hrem : IsSymbol univ (m - 1) remainder := by
    have h := hasSymbolExpansion_amplitudeSymbol m abar habar hcompact 1
    simpa only [Nat.cast_one, Finset.sum_range_one, amplitudeExpansionTerm_zero] using h
  have hdiagCompact : HasCompactSupport diagonal := by
    have hproj : IsCompact (Prod.fst '' tsupport (Function.uncurry abar)) :=
      hcompact.image continuous_fst
    apply hproj.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ hproj.isClosed
    intro x hx
    by_contra hout
    have hzero : Function.uncurry abar (x, x) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hout ⟨(x, x), h, rfl⟩)
    exact hx hzero
  have hremCompact : HasCompactSupport remainder :=
    (hasCompactSupport_amplitudeSymbol abar hcompact).sub hdiagCompact
  let R : PseudodifferentialPiece (n := n) (r := r) (q := q) E F (m - 1) :=
    { L with
      symbol := remainder
      isSymbol := hrem
      operator := quantizeSchwartz (m - 1) remainder hrem hremCompact
      operator_apply := quantizeSchwartz_apply (m - 1) remainder hrem hremCompact }
  -- The same original chart and both frame maps transport this lower-order remainder.
  have hprincipal : IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1)
      (Q.globalSymbolFunction - fun x ξ ↦
        if x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet then
          ((L.output.cutoff (L.chart x) * L.input.cutoff (L.chart x) : ℝ) : ℂ) •
            (L.output.frame.symmL ℂ x).comp
              ((∫ t, a t (L.chart x) (L.chart x)
                (covectorInChart L.chart x ξ) ∂μ).comp
                (L.input.frame.continuousLinearMapAt ℂ x))
        else 0) := by
    convert R.isGlobalSymbol_globalSymbolFunction using 1
    funext x ξ
    simp only [PseudodifferentialPiece.globalSymbolFunction, Q, R, Pi.sub_apply]
    split_ifs
    · simp only [remainder, diagonal, abar, Pi.sub_apply, ContinuousLinearMap.sub_comp,
        ContinuousLinearMap.comp_sub, smul_sub]
    · simp only [sub_self]
  have hc : Continuous (fun p : Y × ((X × X) × X) ↦ a p.1 p.2.1.1 p.2.1.2 p.2.2) := by
    have h := (continuousMultilinearCurryFin0 ℝ ((X × X) × X) H).continuous.comp (hjoint 0)
    change Continuous (fun p : Y × ((X × X) × X) ↦
      (iteratedFDeriv ℝ 0 (fun z : (X × X) × X ↦ a p.1 z.1.1 z.1.2 z.2) p.2).curry0) at h
    simpa only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.curry0_apply,
      Function.comp_def, id_eq] using h
  have haverage (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) :
      amplitudeApply abar u z = ∫ t, T t u z ∂μ := by
    simp_rw [hT]
    apply amplitudeApply_integral_of_uniform_bound μ a ha K hK hsupp hc
    intro K' hK' j
    simpa only [Nat.cast_zero, sub_zero] using hbound K' hK' 0 j 0
  -- The inverse output frame commutes with the fiber integral wherever its cutoff is nonzero.
  refine ⟨Q, ?_, hprincipal⟩
  intro u x
  change L.output.extendedFunction
    (amplitudeOperator m abar habar hcompact (L.input.localize L.chart_mem_atlas u)) x =
      ∫ t, L.output.extendedFunction (T t (L.input.localize L.chart_mem_atlas u)) x ∂μ
  by_cases hx : x ∈ L.chart.source
  · simp only [BundleChartCutoff.extendedFunction, ite_eq_left hx]
    rw [amplitudeOperator_apply, haverage]
    by_cases hcut : L.output.cutoff (L.chart x) = 0
    · simp only [hcut, Complex.ofReal_zero, zero_smul, integral_zero]
    · have hz : L.chart x ∈ tsupport L.output.cutoff := subset_tsupport _ hcut
      have hf : x ∈ L.output.frame.baseSet := by
        have hf := (L.output.support_subset hz).2
        change L.chart.symm (L.chart x) ∈ L.output.frame.baseSet at hf
        rwa [L.chart.left_inv hx] at hf
      let := L.output.frame_mem_atlas
      let C := (L.output.frame.linearEquivAt ℂ x hf).symm.toContinuousLinearEquiv
      have hmap (v : EuclideanSpace ℂ (Fin q)) : L.output.frame.symmL ℂ x v = C v :=
        L.output.frame.symmL_apply hf v
      simp only [hmap, integral_smul]
      rw [C.integral_comp_comm]
  · simp only [BundleChartCutoff.extendedFunction, ite_eq_right hx, integral_zero]


end AtiyahSinger
