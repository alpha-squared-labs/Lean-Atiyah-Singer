/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.GradedDifferentialFormBundle

/-!
# Differential-operator realizations retaining the exterior derivative

Public module ID: M0698.

The original exterior derivatives and their selected metric codifferentials
are realized together in one family of native smooth form bundles. The actual
first-order principal maps are retained, including the factor `i` required by
`D_j = -i ∂_j`. This supplies the degreewise inputs for the finite parity sum.

Source: Lawson--Michelsohn, Spin Geometry, II.5 and III.5. The proof expands
the existing Hodge realization's local coordinate argument into an interface
that retains its derivative and symbol witnesses for the graded operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold MeasureTheory Module Set
open scoped BigOperators Manifold ContDiff ComplexConjugate Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] (g : SmoothTangentMetric (n := n) (M := M))

set_option maxHeartbeats 800000 in
-- Keep the complete degreewise coordinate realization in one native family.

set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- Actual exterior derivatives and codifferentials have compatible native first-order models. -/
theorem exists_smoothFormDifferential_bundleRealization :
    letI : IsSmoothPositiveMeasure (n := n) g.riemannianVolume :=
      g.isSmoothPositiveMeasure_riemannianVolume
    ∃ (rank : ℕ → ℕ)
      (core : (p : ℕ) → VectorBundleCore ℂ M (EuclideanSpace ℂ (Fin (rank p)))
        (atlas (EuclideanSpace ℝ (Fin n)) M))
      (coordinates : (p : ℕ) → (EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ) ≃L[ℂ]
        EuclideanSpace ℂ (Fin (rank p))),
      letI : (p : ℕ) → ∀ x, NormedAddCommGroup ((core p).Fiber x) := fun p _ ↦
        inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin (rank p))))
      letI : (p : ℕ) → ∀ x, NormedSpace ℂ ((core p).Fiber x) := fun p _ ↦
        inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin (rank p))))
      ∃ hSmooth : ∀ p, IsSmoothComplexBundle (n := n) (r := rank p) (core p).Fiber,
      letI : ∀ p, IsSmoothComplexBundle (n := n) (r := rank p) (core p).Fiber := hSmooth
      (∀ p i, (core p).baseSet i = i.val.source) ∧
      (∀ p (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (x : M) (_ : x ∈ c.source)
        (a : DifferentialFormFiber (n := n) p x),
        ((core p).localTriv ⟨c, hc⟩ ⟨x, coordinates p a⟩).2 =
          coordinates p (a.compContinuousLinearMap
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
              𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm (c x)))) ∧
      ∃ sectionEquiv : (p : ℕ) → SmoothDifferentialForm (n := n) M p ≃ₗ[ℂ]
          smoothSections (n := n) (r := rank p) (core p).Fiber,
        (∀ p u x, (sectionEquiv p u).val x = coordinates p (u.val x)) ∧
      ∃ metric : (p : ℕ) → SmoothHermitianMetric (n := n) (r := rank p) (core p).Fiber,
        (∀ p x a b, (metric p).pairing x a b =
          differentialFormInner g p x ((coordinates p).symm a) ((coordinates p).symm b)) ∧
      ∃ P : (p : ℕ) → DifferentialOperator (n := n) (r := rank p) (q := rank (p + 1))
          (core p).Fiber (core (p + 1)).Fiber 1,
        (∀ p u, (P p).toLinearMap (sectionEquiv p u) =
          sectionEquiv (p + 1) (smoothFormExteriorDerivative p u)) ∧
        (∀ p (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
          (a : DifferentialFormFiber (n := n) p x),
          (P p).principalSymbol x ξ (coordinates p a) = Complex.I •
            coordinates (p + 1) (ContinuousAlternatingMap.alternatizeUncurryFin
              (ξ.smulRight a))) ∧
        (∀ p u, ((P p).metricFormalAdjoint (μ := g.riemannianVolume)
            (metric p) (metric (p + 1))).toLinearMap (sectionEquiv (p + 1) u) =
          sectionEquiv p (smoothFormCodifferential g p u)) := by
  classical
  -- Stage 1: choose all degrees together, retaining the same sections and induced metrics.
  choose rank core coordinates hdata using
    (fun p : ℕ ↦ exists_smoothDifferentialForm_bundleModel g p)
  let normedGroup (p : ℕ) : ∀ x, NormedAddCommGroup ((core p).Fiber x) := fun _ ↦
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin (rank p))))
  let normedSpace (p : ℕ) : ∀ x, NormedSpace ℂ ((core p).Fiber x) := fun _ ↦
    inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin (rank p))))
  choose hSmooth hbase hchart sectionEquiv hsection metric hmetric using hdata
  let smoothBundle (p : ℕ) : IsSmoothComplexBundle (n := n) (r := rank p) (core p).Fiber :=
    hSmooth p
  have hdifferential (p : ℕ) :
      IsDifferentialOperator (n := n) (r := rank p) (q := rank (p + 1))
        (core p).Fiber (core (p + 1)).Fiber 1
        ((sectionEquiv (p + 1)).toLinearMap.comp
          ((smoothFormExteriorDerivative p).comp (sectionEquiv p).symm.toLinearMap)) := by
    let V := EuclideanSpace ℝ (Fin n)
    let I₀ := 𝓘(ℝ, V)
    let W := V [⋀^Fin p]→L[ℝ] ℂ
    let W' := V [⋀^Fin (p + 1)]→L[ℝ] ℂ
    let : FiniteDimensional ℂ W :=
      FiniteDimensional.of_injective (coordinates p).toLinearMap (coordinates p).injective
    let : FiniteDimensional ℂ W' :=
      FiniteDimensional.of_injective (coordinates (p + 1)).toLinearMap
        (coordinates (p + 1)).injective
    let r := rank p
    let q := rank (p + 1)
    let E := core p
    let F := core (p + 1)
    let e := coordinates p
    let f := coordinates (p + 1)
    let Φ := sectionEquiv p
    let Ψ := sectionEquiv (p + 1)
    have hΦ := hsection p
    have hΨ := hsection (p + 1)
    have hEc := hchart p
    have hFc := hchart (p + 1)
    have hEb := hbase p
    have hFb := hbase (p + 1)
    let S := EuclideanSpace ℂ (Fin r)
    let T := EuclideanSpace ℂ (Fin q)
    let D := Ψ.toLinearMap.comp ((smoothFormExteriorDerivative p).comp Φ.symm.toLinearMap)
    -- The exterior derivative is the alternating sum of the real coordinate derivatives.
    let K (j : Fin n) : W →L[ℂ] W' := LinearMap.toContinuousLinearMap
      { toFun := fun a ↦ ContinuousAlternatingMap.alternatizeUncurryFin
          ((EuclideanSpace.proj (𝕜 := ℝ) j).smulRight a)
        map_add' := by
          intro a b
          have heq : (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (a + b) =
              (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight a +
                (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight b := by
            apply ContinuousLinearMap.ext
            intro y
            change (y j : ℝ) • (a + b) = (y j : ℝ) • a + (y j : ℝ) • b
            exact smul_add _ _ _
          rw [heq, ContinuousAlternatingMap.alternatizeUncurryFin_add]
        map_smul' := by
          intro c a
          have heq : (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (c • a) =
              c • (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight a := by
            apply ContinuousLinearMap.ext
            intro y
            change (y j : ℝ) • (c • a) = c • ((y j : ℝ) • a)
            exact smul_comm _ _ _
          rw [heq, ContinuousAlternatingMap.alternatizeUncurryFin_smul]
          rfl }
    have hK (L : V →L[ℝ] W) :
        ContinuousAlternatingMap.alternatizeUncurryFin L =
          ∑ j : Fin n, K j (L (EuclideanSpace.single j 1)) := by
      have hL : L = ∑ j : Fin n,
          (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (L (EuclideanSpace.single j 1)) := by
        apply ContinuousLinearMap.ext
        intro y
        simp only [sum_apply]
        change L y = ∑ j : Fin n, y j • L (EuclideanSpace.single j 1)
        calc
          L y = L (∑ j : Fin n, y j • EuclideanSpace.single j 1) := by
            congr 1
            simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
              EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
              ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr y).symm
          _ = ∑ j : Fin n, y j • L (EuclideanSpace.single j 1) := by
            rw [map_sum]
            simp only [map_smul]
      conv_lhs => rw [hL]
      change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℂ)
        (∑ j, (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (L (EuclideanSpace.single j 1))) = _
      rw [map_sum]
      rfl
    have hEchart (u : SmoothDifferentialForm (n := n) M p)
        (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M) (y : M) (hy : y ∈ c.source) :
        (E.localTriv ⟨c, hc⟩ ⟨y, (Φ u).val y⟩).2 =
          e (differentialFormInChart u.val c (c y)) := by
      rw [hΦ]
      exact (hEc c hc y hy (u.val y)).trans (by
        unfold differentialFormInChart
        congr 2
        let u₀ : M → W := fun z ↦ u.val z
        exact (congrArg u₀ (c.left_inv hy)).symm)
    have hFchart (u : SmoothDifferentialForm (n := n) M (p + 1))
        (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M) (y : M) (hy : y ∈ c.source) :
        (F.localTriv ⟨c, hc⟩ ⟨y, (Ψ u).val y⟩).2 =
          f (differentialFormInChart u.val c (c y)) := by
      rw [hΨ]
      exact (hFc c hc y hy (u.val y)).trans (by
        unfold differentialFormInChart
        congr 2
        let u₀ : M → W' := fun z ↦ u.val z
        exact (congrArg u₀ (c.left_inv hy)).symm)
    have hd : IsDifferentialOperator (n := n) (r := r) (q := q) E.Fiber F.Fiber 1 D := by
      intro c hc i hi j hj x hx
      let := hi
      let := hj
      let ec := E.localTriv ⟨c, hc⟩
      let fc := F.localTriv ⟨c, hc⟩
      let : MemTrivializationAtlas ec := ⟨⟨c, hc⟩, rfl⟩
      let : MemTrivializationAtlas fc := ⟨⟨c, hc⟩, rfl⟩
      have hec : ec.baseSet = c.source := hEb ⟨c, hc⟩
      have hfc : fc.baseSet = c.source := hFb ⟨c, hc⟩
      let U := c.source ∩ i.baseSet ∩ j.baseSet
      let O := c.target ∩ c.symm ⁻¹' i.baseSet ∩ c.symm ⁻¹' j.baseSet
      have hO : IsOpen O := by
        convert (c.isOpen_inter_preimage_symm i.open_baseSet).inter
          (c.isOpen_inter_preimage_symm j.open_baseSet) using 1
        ext z
        simp only [O, Set.mem_inter_iff]
        tauto
      have hUO : c '' U ⊆ O := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨⟨c.map_source hy.1.1, by
          simpa only [Set.mem_preimage, c.left_inv hy.1.1] using hy.1.2⟩,
          by simpa only [Set.mem_preimage, c.left_inv hy.1.1] using hy.2⟩
      let A (z : V) : S →L[ℂ] W := e.symm.toContinuousLinearMap.comp
        (i.coordChangeL ℂ ec (c.symm z)).toContinuousLinearMap
      let B (z : V) : W' →L[ℂ] T :=
        (fc.coordChangeL ℂ j (c.symm z)).toContinuousLinearMap.comp f.toContinuousLinearMap
      have hA : ContDiffOn ℝ ∞ A O := by
        have htrans := IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) i ec
        have hcs := contMDiffOn_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I₀) (n := ∞) hc)
        have hbase := htrans.comp (hcs.mono (show O ⊆ c.target from fun _ hz ↦ hz.1.1)) (by
          intro z hz
          exact ⟨hz.1.2, hec ▸ c.map_target hz.1.1⟩)
        exact ((ContinuousLinearMap.compL ℂ S S W) e.symm.toContinuousLinearMap
          |>.restrictScalars ℝ).contDiff.comp_contDiffOn hbase.contDiffOn
      have hB : ContDiffOn ℝ ∞ B O := by
        have htrans := IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) fc j
        have hcs := contMDiffOn_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I₀) (n := ∞) hc)
        have hbase := htrans.comp (hcs.mono (show O ⊆ c.target from fun _ hz ↦ hz.1.1)) (by
          intro z hz
          exact ⟨hfc ▸ c.map_target hz.1.1, hz.2⟩)
        exact ((ContinuousLinearMap.compL ℂ W' T T).flip f.toContinuousLinearMap
          |>.restrictScalars ℝ).contDiff.comp_contDiffOn hbase.contDiffOn
      let C₀ (z : V) : S →L[ℂ] T :=
        ∑ a : Fin n, (B z).comp ((K a).comp (fderiv ℝ A z (EuclideanSpace.single a 1)))
      let C₁ (a : Fin n) (z : V) : S →L[ℂ] T := (B z).comp ((K a).comp (A z))
      have hC₀ : ContDiffOn ℝ ∞ C₀ O := by
        have hDA : ContDiffOn ℝ ∞ (fderiv ℝ A) O :=
          hA.fderiv_of_isOpen hO (by simp)
        apply ContDiffOn.sum
        intro a _
        have hDa := hDA.clm_apply (contDiffOn_const (c := EuclideanSpace.single a 1))
        have hinner :=
          ((ContinuousLinearMap.compL ℂ S W W' (K a)).restrictScalars ℝ).contDiff
            |>.comp_contDiffOn hDa
        let μ := (ContinuousLinearMap.compL ℂ S W' T).bilinearRestrictScalars ℝ
        exact (μ.contDiff.comp_contDiffOn hB).clm_apply hinner
      have hC₁ (a : Fin n) : ContDiffOn ℝ ∞ (C₁ a) O := by
        have hinner :=
          ((ContinuousLinearMap.compL ℂ S W W' (K a)).restrictScalars ℝ).contDiff
            |>.comp_contDiffOn hA
        let μ := (ContinuousLinearMap.compL ℂ S W' T).bilinearRestrictScalars ℝ
        exact (μ.contDiff.comp_contDiffOn hB).clm_apply hinner
      let Q : CoordinateDifferentialOperator n r q 1 (c '' U) :=
        { coefficient := Fin.cases (fun _ ↦ C₀)
            (fun b α z ↦ Complex.I • C₁ (α ⟨0, Nat.zero_lt_succ b.val⟩) z)
          smooth_coefficient := by
            intro b
            refine Fin.cases (fun _ ↦ hC₀.mono hUO) (fun b α ↦ ?_) b
            exact ((hC₁ (α ⟨0, Nat.zero_lt_succ b.val⟩)).mono hUO).const_smul Complex.I }
      have hQ (w : V → S) (z : V) : Q.apply w z = C₀ z (w z) +
          ∑ a : Fin n, C₁ a z (fderiv ℝ w z (EuclideanSpace.single a 1)) := by
        let reindex : (Fin 1 → Fin n) ≃ Fin n :=
          { toFun α := α 0
            invFun a := fun _ ↦ a
            left_inv α := by funext t; exact congrArg α (Subsingleton.elim (0 : Fin 1) t)
            right_inv _ := rfl }
        unfold CoordinateDifferentialOperator.apply
        rw [Fin.sum_univ_two]
        have hone : (1 : Fin 2) = (0 : Fin 1).succ := rfl
        rw [hone]
        simp only [Q, Fin.cases_zero, Fin.cases_succ, Fin.val_succ, Fin.val_zero, zero_add,
          pow_zero, one_smul, iteratedFDeriv_zero_apply, pow_one, Fintype.sum_unique,
          smul_apply, map_smul, smul_smul, neg_mul, Complex.I_mul_I, neg_neg]
        change C₀ z (w z) + (∑ α : Fin 1 → Fin n,
          C₁ (α 0) z (iteratedFDeriv ℝ 1 w z (fun t ↦ EuclideanSpace.single (α t) 1))) = _
        simp only [iteratedFDeriv_one_apply]
        exact congrArg (C₀ z (w z) + ·) (reindex.sum_comp
          (fun a ↦ C₁ a z (fderiv ℝ w z (EuclideanSpace.single a 1))))
      refine ⟨U, (c.open_source.inter i.open_baseSet).inter j.open_baseSet, hx, Q,
        (fun _ hy ↦ hy), ?_⟩
      intro s y hy
      let w := sectionInChart E.Fiber c i s.val
      have hz : c y ∈ O := hUO ⟨y, hy, rfl⟩
      have hw : ContDiffOn ℝ ∞ w O := by
        have hcs := contMDiffOn_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I₀) (n := ∞) hc)
        exact ((s.property i hi).comp (hcs.mono (show O ⊆ c.target from fun _ hz ↦ hz.1.1))
          (fun _ hz ↦ hz.1.2)).contDiffOn
      have hcoord : differentialFormInChart (Φ.symm s).val c =ᶠ[𝓝 (c y)]
          (fun z ↦ A z (w z)) := by
        filter_upwards [hO.mem_nhds hz] with z hzo
        have hzf : c.symm z ∈ ec.baseSet := hec ▸ c.map_target hzo.1.1
        have htr := coordChangeL_section_coordinates E.Fiber i ec s.val (c.symm z)
          ⟨hzo.1.2, hzf⟩
        have hcform := hEchart (Φ.symm s) c hc (c.symm z) (c.map_target hzo.1.1)
        rw [Φ.apply_symm_apply, c.right_inv hzo.1.1] at hcform
        apply e.injective
        change e (differentialFormInChart (Φ.symm s).val c z) =
          e (e.symm (i.coordChangeL ℂ ec (c.symm z) (w z)))
        rw [e.apply_symm_apply]
        exact hcform.symm.trans htr
      have hderiv : fderiv ℝ (differentialFormInChart (Φ.symm s).val c) (c y) =
          fderiv ℝ (fun z ↦ A z (w z)) (c y) := hcoord.fderiv_eq
      have hvalue : (j ⟨y, (D s).val y⟩).2 =
          B (c y) (ContinuousAlternatingMap.alternatizeUncurryFin
            (fderiv ℝ (fun z ↦ A z (w z)) (c y))) := by
        have htr := coordChangeL_section_coordinates F.Fiber fc j (D s).val y
          ⟨hfc ▸ hy.1.1, hy.2⟩
        have hcform := hFchart (smoothFormExteriorDerivative p (Φ.symm s)) c hc y hy.1.1
        change (fc ⟨y, (D s).val y⟩).2 = _ at hcform
        rw [smoothFormExteriorDerivative_inChart _ c hc (c y) (c.map_source hy.1.1)] at hcform
        change (fc ⟨y, (D s).val y⟩).2 =
          f (ContinuousAlternatingMap.alternatizeUncurryFin
            (fderiv ℝ (differentialFormInChart (Φ.symm s).val c) (c y))) at hcform
        rw [hderiv] at hcform
        rw [htr, hcform]
        change _ = fc.coordChangeL ℂ j (c.symm (c y)) _
        rw [c.left_inv hy.1.1]
        rfl
      rw [hvalue, hQ, hK, map_sum]
      have hAs := (hA.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
      have hws := (hw.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
      let res := ContinuousLinearMap.restrictScalarsL ℂ S W ℝ ℝ
      have hAs' := res.hasFDerivAt.comp (c y) hAs.hasFDerivAt
      have hder := (hAs'.clm_apply hws.hasFDerivAt).fderiv
      have hjets (a : Fin n) :
          fderiv ℝ (fun z ↦ A z (w z)) (c y) (EuclideanSpace.single a 1) =
            A (c y) (fderiv ℝ w (c y) (EuclideanSpace.single a 1)) +
            fderiv ℝ A (c y) (EuclideanSpace.single a 1) (w (c y)) := by
        exact congrArg (fun L : V →L[ℝ] W ↦ L (EuclideanSpace.single a 1)) hder
      simp only [hjets, map_add, Finset.sum_add_distrib, C₀, C₁,
        sum_apply, ContinuousLinearMap.comp_apply]
      abel
    exact hd
  -- Stage 2: identify the actual first-order symbol by its scalar commutator.
  let P (p : ℕ) : DifferentialOperator (n := n) (r := rank p) (q := rank (p + 1))
      (core p).Fiber (core (p + 1)).Fiber 1 :=
    ⟨_, hdifferential p⟩
  let wedge (p : ℕ) (ξ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
      (EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ) →ₗ[ℂ]
        (EuclideanSpace ℝ (Fin n) [⋀^Fin (p + 1)]→L[ℝ] ℂ) :=
    { toFun := fun a ↦ ContinuousAlternatingMap.alternatizeUncurryFin (ξ.smulRight a)
      map_add' := by
        intro a b
        have heq : ξ.smulRight (a + b) = ξ.smulRight a + ξ.smulRight b := by
          ext v w
          exact smul_add _ _ _
        rw [heq, ContinuousAlternatingMap.alternatizeUncurryFin_add]
      map_smul' := by
        intro c a
        have heq : ξ.smulRight (c • a) = c • ξ.smulRight a := by
          ext v w
          exact smul_comm _ _ _
        rw [heq, ContinuousAlternatingMap.alternatizeUncurryFin_smul]
        rfl }
  let A (p : ℕ) (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      (core p).Fiber x →ₗ[ℂ] (core (p + 1)).Fiber x :=
    (coordinates (p + 1)).toLinearMap.comp
      ((wedge p ξ).comp (coordinates p).symm.toLinearMap)
  have hP (p : ℕ) (u : SmoothDifferentialForm (n := n) M p) :
      (P p).toLinearMap (sectionEquiv p u) =
        sectionEquiv (p + 1) (smoothFormExteriorDerivative p u) := by
    change sectionEquiv (p + 1)
      (smoothFormExteriorDerivative p ((sectionEquiv p).symm (sectionEquiv p u))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hsymbol (p : ℕ) (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      (P p).principalSymbol x ξ = Complex.I • A p x ξ := by
    apply (P p).principalSymbol_eq_smul_of_leibniz (A p)
    intro φ hφ s t hst y
    let u := (sectionEquiv p).symm s
    let v := (sectionEquiv p).symm t
    have hu : sectionEquiv p u = s := (sectionEquiv p).apply_symm_apply s
    have hv : sectionEquiv p v = t := (sectionEquiv p).apply_symm_apply t
    have hvu (z : M) : v.val z = φ z • u.val z := by
      apply (coordinates p).injective
      change coordinates p (show EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ from
        v.val z) = coordinates p ((φ z : ℂ) •
          (show EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ from u.val z))
      exact (hsection p v z).symm.trans ((congrArg (fun w ↦ w.val z) hv).trans
        ((hst z).trans ((congrArg ((φ z : ℂ) • ·)
          ((congrArg (fun w ↦ w.val z) hu).symm.trans (hsection p u z))).trans
            ((coordinates p).map_smul (φ z : ℂ) _).symm)))
    have h := smoothFormExteriorDerivative_leibniz p φ hφ u v hvu y
    rw [← hv, ← hu, hP, hP, hsection, hsection, hsection]
    change coordinates (p + 1) ((smoothFormExteriorDerivative p v).val y) =
      coordinates (p + 1) (wedge p (mfderiv _ _ φ y)
        ((coordinates p).symm (coordinates p (u.val y)))) +
        (φ y : ℂ) • coordinates (p + 1) ((smoothFormExteriorDerivative p u).val y)
    rw [ContinuousLinearEquiv.symm_apply_apply]
    have hc := congrArg (coordinates (p + 1)) h
    exact hc.trans (((coordinates (p + 1)).map_add _ _).trans
      (congrArg (coordinates (p + 1) (wedge p (mfderiv _ _ φ y) (u.val y)) + ·)
        ((coordinates (p + 1)).map_smul (φ y : ℂ) _)))
  -- Stage 3: adjunction uses the same metric density and the original selected codifferential.
  have hpair (p : ℕ) (u v : SmoothDifferentialForm (n := n) M p) :
      (metric p).sectionPairing g.riemannianVolume (sectionEquiv p u) (sectionEquiv p v) =
        smoothFormPairing g p u v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      change (metric p).pairing x ((sectionEquiv p u).val x)
        ((sectionEquiv p v).val x) = differentialFormInner g p x (u.val x) (v.val x)
      rw [hmetric, hsection, hsection]
      erw [(coordinates p).symm_apply_apply, (coordinates p).symm_apply_apply]
  let : IsSmoothPositiveMeasure (n := n) g.riemannianVolume :=
    g.isSmoothPositiveMeasure_riemannianVolume
  let Q (p : ℕ) := (P p).metricFormalAdjoint (μ := g.riemannianVolume)
    (metric p) (metric (p + 1))
  have hQ (p : ℕ) (u : SmoothDifferentialForm (n := n) M (p + 1)) :
      (Q p).toLinearMap (sectionEquiv (p + 1) u) =
        sectionEquiv p (smoothFormCodifferential g p u) := by
    let δ : SmoothDifferentialForm (n := n) M (p + 1) →ₗ[ℂ]
        SmoothDifferentialForm (n := n) M p :=
      (sectionEquiv p).symm.toLinearMap.comp
        ((Q p).toLinearMap.comp (sectionEquiv (p + 1)).toLinearMap)
    have hδ (v : SmoothDifferentialForm (n := n) M (p + 1)) :
        (Q p).toLinearMap (sectionEquiv (p + 1) v) = sectionEquiv p (δ v) :=
      ((sectionEquiv p).apply_symm_apply _).symm
    have heq : δ = smoothFormCodifferential g p := by
      apply (existsUnique_smoothFormCodifferential g p).unique
      · intro v w _hv
        have hadj := (P p).isMetricFormalAdjoint_metricFormalAdjoint
          (μ := g.riemannianVolume) (metric p) (metric (p + 1))
          (sectionEquiv p v) (sectionEquiv (p + 1) w)
        change (metric (p + 1)).sectionPairing g.riemannianVolume
          ((P p).toLinearMap (sectionEquiv p v)) (sectionEquiv (p + 1) w) =
            (metric p).sectionPairing g.riemannianVolume (sectionEquiv p v)
              ((Q p).toLinearMap (sectionEquiv (p + 1) w)) at hadj
        rw [hP, hδ, hpair, hpair] at hadj
        exact hadj
      · exact (existsUnique_smoothFormCodifferential g p).exists.choose_spec
    rw [← heq]
    exact hδ u
  refine ⟨rank, core, coordinates, hSmooth, hbase, hchart, sectionEquiv, hsection,
    metric, hmetric, P, hP, ?_, hQ⟩
  intro p x ξ a
  rw [hsymbol]
  change Complex.I • coordinates (p + 1)
    (wedge p ξ ((coordinates p).symm (coordinates p a))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

end AtiyahSinger
