/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantRadialOrderReduction
public import AtiyahSinger.Analysis.EquivariantSymbolHomotopy
public import AtiyahSinger.Analysis.OperatorOrderShift
public import AtiyahSinger.Analysis.SmoothEquivariantIndex

/-!
# Equivariant order shifts preserve the full smooth index and support class

Public module ID: M0549.

Precompose with the actual invertible radial equivariant PDO. The same smooth
kernel and range comparisons preserve their full finite representations.
The invariant radial degree family preserves the original equivariant support
class, with one zero-section control even in dimension zero.

Source: SG III.13, order reduction, with its actual equivariant representatives.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

section

/- The first statement permits arbitrary universes for the base and group action.
Its fibers lie in Type, as required by the support model. The following statement
specializes the base, group and group model to universe zero. -/
variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type}
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

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (γ : G) (x : M) (u v : E x),
      h.pairing (γ • x) (σE.linearMap γ x u) (σE.linearMap γ x v) = h.pairing x u v)
  (hμInvariant : ∀ γ : G, Measure.map (fun x : M ↦ γ • x) μ = μ)

namespace PseudodifferentialOperator

set_option maxHeartbeats 2000000 in
-- All symbol, kernel and range transports retain their specified original models.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
include h hInvariant hμInvariant in
/-- Equivariant order shift preserves the full index and original support class. -/
theorem exists_equivariant_orderShift_universe {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hPg : P.IsEquivariant IG σE σF hσE hσF)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (hg : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x),
      g.length (γ • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ γ) ⟨x, ξ⟩).snd =
        g.length x ξ)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2))
    (hi : IsEllipticGlobalSymbol E F a.val)
    (ha : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF γ a.val x ξ = a.val x ξ)
    (t : ℝ) :
    ∃ (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ t)
      (b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F t)
      (hj : IsEllipticGlobalSymbol E F b.val)
      (hb : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σE σF γ b.val x ξ = b.val x ξ)
      (hQg : Q.IsEquivariant IG σE σF hσE hσF) (hQ : Q.IsElliptic)
      (U : smoothSections (n := n) (r := r) E ≃ₗ[ℂ] smoothSections (n := n) (r := r) E),
      Q.toLinearMap = P.toLinearMap.comp U.toLinearMap ∧
      (∀ γ u, U (σE.smoothSectionRepresentation IG hσE γ u) =
        σE.smoothSectionRepresentation IG hσE γ (U u)) ∧
      Q.principalSymbol = globalPrincipalSymbolClass E F t
        (R.regularizedSymbol t b.val b.property.1 b.property.2) ∧
      (∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        b.val x ξ = (g.length x ξ ^ (t - m) : ℝ) • a.val x ξ) ∧
      Q.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hQg hQ =
        P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg
          ((P.isElliptic_iff_homogeneous R a hP).mpr hi) ∧
      equivariantHomogeneousSymbolKClass IG σE σF t b hj hb =
        equivariantHomogeneousSymbolKClass IG σE σF m a hi ha := by
  classical
  -- Keep the actual composite order definitionally equal to the requested target order.
  generalize hd : t - m = d
  have ht : t = m + d := by rw [← hd]; ring
  subst t
  obtain ⟨R₀⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := r) (E := E) (F := E)
  obtain ⟨c, J, hc, hJclass, hJg, _, hJbij, _⟩ :=
    exists_equivariant_elliptic_orderReduction μ IG σE hσE h hInvariant hμInvariant g hg R₀ d
  let U := LinearEquiv.ofBijective J.toLinearMap hJbij
  have hJU : J.toLinearMap = U.toLinearMap := rfl
  have hUg (γ : G) (u : smoothSections (n := n) (r := r) E) :
      U (σE.smoothSectionRepresentation IG hσE γ u) =
        σE.smoothSectionRepresentation IG hσE γ (U u) :=
    LinearMap.congr_fun (hJg γ) u
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
  -- Invariant radial extension preserves the original moving-fiber symbol square at every degree.
  have hformula (s : ℝ) (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      cosphereExtension g s a₀ x ξ = (g.length x ξ ^ (s - m) : ℝ) • a.val x ξ := by
    rw [← cosphereExtension_restriction g m a.val a.property.2 x ξ hξ,
      cosphereExtension_of_ne_zero g s a₀ x ξ hξ,
      cosphereExtension_of_ne_zero g m a₀ x ξ hξ]
    let L : E x →L[ℂ] F x := a₀ (g.radial ⟨⟨x, ξ⟩, hξ⟩)
    change ((g.length x ξ ^ s : ℝ) : ℂ) • L =
      (g.length x ξ ^ (s - m) : ℝ) • (((g.length x ξ ^ m : ℝ) : ℂ) • L)
    rw [← Complex.coe_smul]
    have hpower : g.length x ξ ^ s = g.length x ξ ^ (s - m) * g.length x ξ ^ m := by
      rw [← Real.rpow_add (g.length_pos x ξ hξ)]
      congr 1
      ring
    rw [hpower, Complex.ofReal_mul, mul_smul]
  have hshift (s : ℝ) : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF γ (cosphereExtension g s a₀) x ξ =
        cosphereExtension g s a₀ x ξ := by
    apply (equivariantGlobalSymbolLinearMap_eq_iff IG σE σF _).mpr
    intro γ x ξ hξ v
    let ξ' : CotangentFiber (n := n) (γ • x) := (cotangentDiffeomorphMap
      (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ γ) ⟨x, ξ⟩).snd
    have hξ' : ξ' ≠ 0 := by
      intro hz
      have hlen : g.length (γ • x) ξ' = g.length x ξ := hg γ x ξ
      have hzlen : g.length (γ • x) ξ' = 0 := (g.length_eq_zero_iff (γ • x) ξ').mpr hz
      exact (g.length_pos x ξ hξ).ne' (hlen.symm.trans hzlen)
    rw [hformula s (γ • x) ξ' hξ', hformula s x ξ hξ, hg γ x ξ]
    simp only [smul_apply, ← Complex.coe_smul, map_smul]
    exact congrArg (fun w : F (γ • x) ↦ ((g.length x ξ ^ (s - m) : ℝ) : ℂ) • w)
      ((equivariantGlobalSymbolLinearMap_eq_iff IG σE σF a.val).mp ha γ x ξ hξ v)
  have hbg := hshift (m + d)
  have hQg : Q.IsEquivariant IG σE σF hσE hσF := by
    intro γ
    apply LinearMap.ext
    intro u
    change P.toLinearMap (J.toLinearMap (σE.smoothSectionRepresentation IG hσE γ u)) =
      σF.smoothSectionRepresentation IG hσF γ (P.toLinearMap (J.toLinearMap u))
    exact (congrArg P.toLinearMap (LinearMap.congr_fun (hJg γ) u)).trans
      (LinearMap.congr_fun (hPg γ) (J.toLinearMap u))
  refine ⟨Q, b, hj, hbg, hQg, hQ, U, ?_, hUg, hQclass, hb, ?_, ?_⟩
  · change P.toLinearMap.comp J.toLinearMap = _
    rw [hJU]
  · -- The actual smooth kernel is transported by U; its original range is unchanged.
    let hPE := (P.isElliptic_iff_homogeneous R a hP).mpr hi
    obtain ⟨ρ, τ, e, f, he, hf⟩ :=
      P.exists_smoothKernelCokernelRepresentations IG σE σF hσE hσF hPg hPE
    let K : Q.toLinearMap.ker ≃ₗ[ℂ] P.toLinearMap.ker :=
      { toFun u := ⟨U u.val, u.property⟩
        invFun v := ⟨U.symm v.val, by
          change P.toLinearMap (U (U.symm v.val)) = 0
          rw [U.apply_symm_apply]
          exact v.property⟩
        left_inv u := Subtype.ext (U.symm_apply_apply u.val)
        right_inv v := Subtype.ext (U.apply_symm_apply v.val)
        map_add' u v := Subtype.ext (U.map_add u.val v.val)
        map_smul' c u := Subtype.ext (U.map_smul c u.val) }
    have hRange : Q.toLinearMap.range = P.toLinearMap.range := by
      change (P.toLinearMap.comp U.toLinearMap).range = _
      rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr U.surjective, Submodule.map_top]
    let C := Submodule.quotEquivOfEq Q.toLinearMap.range P.toLinearMap.range hRange
    let e' := e.trans K.symm
    let f' := f.trans C.symm
    rw [P.smoothEquivariantAnalyticIndex_eq IG σE σF hσE hσF hPg hPE ρ τ e f he hf]
    apply Q.smoothEquivariantAnalyticIndex_eq IG σE σF hσE hσF hQg hQ ρ τ e' f'
    · intro γ v
      apply U.injective
      change U (U.symm (e (ρ.representation γ v)).val) =
        U (σE.smoothSectionRepresentation IG hσE γ (U.symm (e v).val))
      rw [U.apply_symm_apply, hUg, U.apply_symm_apply]
      exact he γ v
    · intro γ v
      apply C.injective
      change C (C.symm (f (τ.representation γ (f.symm (C (Q.toLinearMap.range.mkQ v)))))) =
        C (Q.toLinearMap.range.mkQ (σF.smoothSectionRepresentation IG hσF γ v))
      rw [C.apply_symm_apply]
      have hCv (u : smoothSections (n := n) (r := q) F) :
          C (Q.toLinearMap.range.mkQ u) = P.toLinearMap.range.mkQ u :=
        Submodule.quotEquivOfEq_mk _ _ hRange u
      rw [hCv, hCv]
      exact hf γ v
  · -- The same cosphere data gives a jointly continuous equivariant elliptic degree family.
    have hcs : IsEllipticCosphereSymbol g a₀ :=
      (isEllipticCosphereSymbol_restriction_iff g m a.val a.property.2).mpr hi
    apply equivariantHomogeneousSymbolKClass_eq_of_family IG σE σF (m + d) m
      b a hj hi hbg ha (cosphereDegreeFamily g (m + d) m a₀)
      (isContinuousOffZeroSymbolFamily_degree g (m + d) m a₀
        (isSmoothCosphereSymbol_restriction g a.val a.property.1).continuous)
      (isEllipticGlobalSymbol_degree g (m + d) m a₀ hcs)
    · intro t γ x ξ hξ
      exact hshift _ γ x ξ hξ
    · intro x ξ _
      exact congrArg (fun s : GlobalSymbolFunction (n := n) E F ↦ s x ξ)
        (cosphereDegreeFamily_zero g (m + d) m a₀)
    · intro x ξ hξ
      rw [cosphereDegreeFamily_one]
      exact cosphereExtension_restriction g m a.val a.property.2 x ξ hξ

end PseudodifferentialOperator

end

variable {n r q : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type}
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

variable {V HG G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (γ : G) (x : M) (u v : E x),
      h.pairing (γ • x) (σE.linearMap γ x u) (σE.linearMap γ x v) = h.pairing x u v)
  (hμInvariant : ∀ γ : G, Measure.map (fun x : M ↦ γ • x) μ = μ)

namespace PseudodifferentialOperator

set_option maxHeartbeats 2000000 in
-- All symbol, kernel and range transports retain their specified original models.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
include h hInvariant hμInvariant in
/-- Equivariant order shift preserves the full index and original support class. -/
theorem exists_equivariant_orderShift {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hPg : P.IsEquivariant IG σE σF hσE hσF)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (hg : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x),
      g.length (γ • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ γ) ⟨x, ξ⟩).snd =
        g.length x ξ)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2))
    (hi : IsEllipticGlobalSymbol E F a.val)
    (ha : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF γ a.val x ξ = a.val x ξ)
    (t : ℝ) :
    ∃ (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ t)
      (b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F t)
      (hj : IsEllipticGlobalSymbol E F b.val)
      (hb : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σE σF γ b.val x ξ = b.val x ξ)
      (hQg : Q.IsEquivariant IG σE σF hσE hσF) (hQ : Q.IsElliptic)
      (U : smoothSections (n := n) (r := r) E ≃ₗ[ℂ] smoothSections (n := n) (r := r) E),
      Q.toLinearMap = P.toLinearMap.comp U.toLinearMap ∧
      (∀ γ u, U (σE.smoothSectionRepresentation IG hσE γ u) =
        σE.smoothSectionRepresentation IG hσE γ (U u)) ∧
      Q.principalSymbol = globalPrincipalSymbolClass E F t
        (R.regularizedSymbol t b.val b.property.1 b.property.2) ∧
      (∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        b.val x ξ = (g.length x ξ ^ (t - m) : ℝ) • a.val x ξ) ∧
      Q.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hQg hQ =
        P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg
          ((P.isElliptic_iff_homogeneous R a hP).mpr hi) ∧
      equivariantHomogeneousSymbolKClass IG σE σF t b hj hb =
        equivariantHomogeneousSymbolKClass IG σE σF m a hi ha := by
  -- Specialize the general order-shift result to these universe-zero parameters.
  exact P.exists_equivariant_orderShift_universe IG σE σF hσE hσF h hInvariant
    hμInvariant hPg g hg R a hP hi ha t

end PseudodifferentialOperator

end AtiyahSinger
