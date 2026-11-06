/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianRealPrincipal
public import AtiyahSinger.Analysis.OperatorOrderShift

/-!
# The specified spectral powers as actual elliptic order shifts

Public module ID: M0392.

A09: the original spectral power of 1+Delta, its selected smooth action and
its PDO realization are identified on exactly the same sections. The resulting
operator has homogeneous principal symbol length^l times identity and gives
the existing Sobolev extension an inverse supplied by the opposite power.
The original L2 domain is the actual embedded H^l space for l>0 and the full
L2 space for l<=0. Negative Sobolev spaces are not mistaken for subspaces of L2.

Finally, the original elliptic PDO is precomposed with this specified smooth
spectral equivalence. The resulting order shift retains its analytic index and
its original homogeneous-symbol K class. This supplies concrete spectral
witnesses for the previously declared existence statements in OrderReduction
and OperatorOrderShift, without replacing an arbitrary earlier witness by fiat.

Sources: SG III.13, p.247; TA XII.1.3 and pp.298--299. The vector-bundle
functional-calculus argument, agreement with the project's actual Sobolev
presentations and partial domains, and real-order extension of SG's integer
statement are explicit project supplements. The same g, h, measure and smooth
complex connection are used throughout. A unitary connection is not necessary
for positivity of the operator defined as the formal square nabla* nabla.
The spectral identification is constructed from the same resolvent family.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (g : SmoothCotangentMetric (n := n) (M := M))
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℂ (Fin r)) E)
  (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
  (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E cov)

/-- The original smooth spectral action has a unique PDO realization of its stated real order. -/
theorem existsUnique_connectionLaplacianPseudodifferential (l : ℝ) :
    ∃! J : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ l,
      J.toLinearMap =
        (connectionLaplacianSmoothPower μ g h cov hcov hcomplex l).toLinearMap := by
  obtain ⟨R⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := r) (E := E) (F := E)
  obtain ⟨a, J, _, hJ, _⟩ :=
    exists_connectionLaplacianSmoothPower_principal μ g h cov hcov hcomplex R l
  -- The constructed certificate belongs to the original action; proof irrelevance gives uniqueness.
  refine ⟨J, hJ, ?_⟩
  intro K hK
  have heq : K.toLinearMap = J.toLinearMap := hK.trans hJ.symm
  cases K
  cases J
  cases heq
  rfl

/-- The PDO whose section action is exactly the specified connection-Laplacian spectral power. -/
def connectionLaplacianPseudodifferential (l : ℝ) :
    PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ l :=
  (existsUnique_connectionLaplacianPseudodifferential μ g h cov hcov hcomplex l).exists.choose

/-- The same spectral PDO has the stated principal symbol and mutually inverse Sobolev actions. -/
theorem connectionLaplacianPseudodifferential_properties
    (R : QuantizationPresentation (n := n) (r := r) (q := r) E E) (l : ℝ) :
    let J := connectionLaplacianPseudodifferential μ g h cov hcov hcomplex l
    J.toLinearMap =
        (connectionLaplacianSmoothPower μ g h cov hcov hcomplex l).toLinearMap ∧
      J.IsElliptic ∧
      (∃ a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := r) E E l,
        (∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
          a.val x ξ = (g.length x ξ ^ l : ℝ) • ContinuousLinearMap.id ℂ (E x)) ∧
        J.principalSymbol = globalPrincipalSymbolClass E E l
          (R.regularizedSymbol l a.val a.property.1 a.property.2)) ∧
      ∀ (A : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ),
        ∃ V : A.SobolevSpace s ≃L[ℂ] A.SobolevSpace (s - l),
          V.toContinuousLinearMap = J.sobolevExtension A A s ∧
          V.symm.toContinuousLinearMap =
            Eq.mp (congrArg
              (fun t : ℝ ↦ A.SobolevSpace (s - l) →L[ℂ] A.SobolevSpace t)
              (by ring : s - l - -l = s))
              (PseudodifferentialOperator.sobolevExtension
                (connectionLaplacianPseudodifferential μ g h cov hcov hcomplex (-l))
                A A (s - l)) := by
  classical
  let J := connectionLaplacianPseudodifferential μ g h cov hcov hcomplex l
  let U := connectionLaplacianSmoothPower μ g h cov hcov hcomplex
  have hJU : J.toLinearMap = (U l).toLinearMap :=
    (existsUnique_connectionLaplacianPseudodifferential
      μ g h cov hcov hcomplex l).exists.choose_spec
  -- Transfer the radial symbol of the constructed operator to the same uniquely specified action.
  obtain ⟨a, P, ha, hP, hPa⟩ :=
    exists_connectionLaplacianSmoothPower_principal μ g h cov hcov hcomplex R l
  have hJclass : J.principalSymbol = globalPrincipalSymbolClass E E l
      (R.regularizedSymbol l a.val a.property.1 a.property.2) :=
    (J.principalSymbol_eq_of_toLinearMap_eq μ P (hJU.trans hP.symm)).trans hPa
  have hell : IsEllipticGlobalSymbol E E a.val := by
    intro x ξ hξ
    rw [ha x ξ hξ]
    exact (IsUnit.smul_bijective
      (isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos (g.length_pos x ξ hξ) l).ne')).comp
        Function.bijective_id
  refine ⟨hJU, (J.isElliptic_iff_homogeneous R a hJclass).mpr hell, ⟨a, ha, hJclass⟩, ?_⟩
  intro A s
  let K := connectionLaplacianPseudodifferential μ g h cov hcov hcomplex (-l)
  have hKU : K.toLinearMap = (U (-l)).toLinearMap :=
    (existsUnique_connectionLaplacianPseudodifferential μ g h cov hcov hcomplex
      (-l)).exists.choose_spec
  let T := J.sobolevExtension A A s
  let W := K.sobolevRealization A A (s - l) s (by linarith)
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (A.smoothToSobolev s u) = A.smoothToSobolev (s - l) (U l u) := by
    rw [J.sobolevExtension_smoothToSobolev, hJU]
    rfl
  have hW (u : smoothSections (n := n) (r := r) E) :
      W (A.smoothToSobolev (s - l) u) = A.smoothToSobolev s (U (-l) u) := by
    rw [K.sobolevRealization_smoothToSobolev, hKU]
    rfl
  have hneg : U (-l) = (U l).symm :=
    connectionLaplacianSmoothPower_neg μ g h cov hcov hcomplex l
  -- Density extends the exact inverse identities of the same smooth spectral maps.
  have hWT : W.comp T = ContinuousLinearMap.id ℂ (A.SobolevSpace s) := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev s).equalizer (W.comp T).continuous continuous_id
    funext u
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply, hT, hW, hneg,
      LinearEquiv.symm_apply_apply, id_eq]
  have hTW : T.comp W = ContinuousLinearMap.id ℂ (A.SobolevSpace (s - l)) := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev (s - l)).equalizer (T.comp W).continuous continuous_id
    funext u
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply, hW, hT, hneg,
      LinearEquiv.apply_symm_apply, id_eq]
  let V : A.SobolevSpace s ≃L[ℂ] A.SobolevSpace (s - l) :=
    { toLinearEquiv :=
        { T.toLinearMap with
          invFun := W
          left_inv := fun x ↦ DFunLike.congr_fun hWT x
          right_inv := fun x ↦ DFunLike.congr_fun hTW x }
      continuous_toFun := T.continuous
      continuous_invFun := W.continuous }
  refine ⟨V, rfl, ?_⟩
  -- The inverse uses only the required arithmetic transport, with the original opposite PDO.
  have hcast (t : ℝ) (ht : t = s)
      (L : A.SobolevSpace (s - l) →L[ℂ] A.SobolevSpace t) :
      (A.sobolevInclusion t s ht.ge).comp L =
        Eq.mp (congrArg (fun v : ℝ ↦ A.SobolevSpace (s - l) →L[ℂ] A.SobolevSpace v) ht) L := by
    subst t
    have hid : A.sobolevInclusion s s le_rfl = ContinuousLinearMap.id ℂ (A.SobolevSpace s) := by
      apply DFunLike.coe_injective
      apply (A.denseRange_smoothToSobolev s).equalizer
        (A.sobolevInclusion s s le_rfl).continuous continuous_id
      funext u
      exact A.sobolevInclusion_smoothToSobolev s s le_rfl u
    rw [hid]
    rfl
  change W = _
  exact hcast (s - l - -l) (by ring) (K.sobolevExtension A A (s - l))

/-- The original spectral L2 domain is the embedded positive Sobolev space, or all L2. -/
theorem connectionLaplacianSpectralPower_domain
    (A : SmoothBundlePresentation (n := n) (r := r) E) (l : ℝ) :
    (connectionLaplacianSpectralPower μ g h cov hcov hcomplex l).domain =
      if hl : 0 < l then
        ((h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap.comp
          (A.sobolevInclusion l 0 hl.le)).toLinearMap.range
      else
        ⊤ := by
  classical
  by_cases hl : 0 < l
  · rw [dite_eq_left hl]
    let H := h.L2SectionSpace μ
    let B := connectionLaplacianInverse μ g h cov hcov hcomplex
    let F : H →L[ℂ] H := CFC.rpow B (l / 2)
    let e := h.sobolevZeroEquivL2 (μ := μ) A
    let I : A.SobolevSpace l →L[ℂ] H :=
      e.toContinuousLinearMap.comp (A.sobolevInclusion l 0 hl.le)
    let J := connectionLaplacianPseudodifferential μ g h cov hcov hcomplex (-l)
    let W := connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-l)
    have he (u : smoothSections (n := n) (r := r) E) :
        e (A.smoothToSobolev 0 u) = h.smoothToL2 μ u :=
      h.sobolevZeroEquivL2_smooth (μ := μ) A u
    -- Keep the actual opposite-order Sobolev isomorphism supplied for this same J.
    obtain ⟨R⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := r)
      (E := E) (F := E)
    have hprops := connectionLaplacianPseudodifferential_properties
      μ g h cov hcov hcomplex R (-l)
    have hJmap : J.toLinearMap = W.toLinearMap := hprops.1
    have hVexists : ∃ V : A.SobolevSpace 0 ≃L[ℂ] A.SobolevSpace l,
        ∀ u : smoothSections (n := n) (r := r) E,
          V (A.smoothToSobolev 0 u) = A.smoothToSobolev l (W u) := by
      let Hdom (v : ℝ) : Prop :=
        ∃ V : A.SobolevSpace 0 ≃L[ℂ] A.SobolevSpace v,
          ∀ u : smoothSections (n := n) (r := r) E,
            V (A.smoothToSobolev 0 u) = A.smoothToSobolev v (W u)
      obtain ⟨V, hV, _⟩ := hprops.2.2.2 A 0
      have hact (u : smoothSections (n := n) (r := r) E) :
          V (A.smoothToSobolev 0 u) = A.smoothToSobolev (0 - -l) (W u) := by
        change V.toContinuousLinearMap (A.smoothToSobolev 0 u) = _
        rw [hV, J.sobolevExtension_smoothToSobolev, hJmap]
        rfl
      have hex : Hdom (0 - -l) := ⟨V, hact⟩
      exact (congrArg Hdom (by ring : 0 - -l = l)).mp hex
    obtain ⟨V, hV⟩ := hVexists
    -- The bounded CFC power agrees with the same negative smooth spectral graph.
    have hF (u : smoothSections (n := n) (r := r) E) :
        F (h.smoothToL2 μ u) = h.smoothToL2 μ (W u) := by
      have hg := connectionLaplacianSmoothPower_graph μ g h cov hcov hcomplex (-l) u
      rw [connectionLaplacianSpectralPower, ite_eq_left (by linarith : -l ≤ 0)] at hg
      have hexp : - -l / 2 = l / 2 := by ring
      rw [hexp] at hg
      obtain ⟨z, hz, hvalue⟩ := (LinearPMap.mem_graph_iff _).mp hg
      change (z : H) = h.smoothToL2 μ u at hz
      change F (z : H) = h.smoothToL2 μ (W u) at hvalue
      rw [hz] at hvalue
      exact hvalue
    let G : H →L[ℂ] H := I.comp (V.toContinuousLinearMap.comp e.symm.toContinuousLinearMap)
    have hG (u : smoothSections (n := n) (r := r) E) :
        G (h.smoothToL2 μ u) = h.smoothToL2 μ (W u) := by
      change e (A.sobolevInclusion l 0 hl.le (V (e.symm (h.smoothToL2 μ u)))) = _
      rw [← he u, e.symm_apply_apply, hV u, A.sobolevInclusion_smoothToSobolev, he]
    have hFG : F = G := by
      apply DFunLike.coe_injective
      apply (h.denseRange_smoothToL2 μ).equalizer F.continuous G.continuous
      funext u
      exact (hF u).trans (hG u).symm
    have hFapply (z : H) : F z = I (V (e.symm z)) :=
      congrArg (fun Q : H →L[ℂ] H ↦ Q z) hFG
    -- The positive spectral domain is the range of this original bounded CFC power.
    rw [connectionLaplacianSpectralPower, ite_eq_right (not_le_of_gt hl),
      LinearPMap.inverse_domain]
    change ((F.toLinearMap.toPMap ⊤).toFun.range) = I.toLinearMap.range
    ext z
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨V (e.symm (w : H)), ?_⟩
      change I (V (e.symm (w : H))) = z
      exact (hFapply (w : H)).symm.trans hw
    · rintro ⟨w, hw⟩
      refine ⟨⟨e (V.symm w), Submodule.mem_top⟩, ?_⟩
      change F (e (V.symm w)) = z
      rw [hFapply, e.symm_apply_apply, V.apply_symm_apply]
      exact hw
  · -- Nonpositive powers are the bounded CFC operators on the complete original L2 carrier.
    have hl₀ : l ≤ 0 := le_of_not_gt hl
    rw [dite_eq_right hl, connectionLaplacianSpectralPower, ite_eq_left hl₀,
      LinearMap.toPMap_domain]

variable {q : ℕ} {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]

namespace PseudodifferentialOperator

/-- The specified spectral shift changes order while retaining the original index and K class. -/
theorem exists_connectionLaplacian_orderShift {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2))
    (hi : IsEllipticGlobalSymbol E F a.val) (t : ℝ) :
    ∃ (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ t)
      (b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F t)
      (hj : IsEllipticGlobalSymbol E F b.val),
      Q.toLinearMap = P.toLinearMap.comp
        (connectionLaplacianSmoothPower μ g h cov hcov hcomplex (t - m)).toLinearMap ∧
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
  let J := connectionLaplacianPseudodifferential μ g h cov hcov hcomplex d
  let U := connectionLaplacianSmoothPower μ g h cov hcov hcomplex d
  obtain ⟨hJU, _, ⟨c, hc, hJclass⟩, _⟩ :=
    connectionLaplacianPseudodifferential_properties μ g h cov hcov hcomplex R₀ d
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
  refine ⟨Q, b, hj, ?_, hQclass, hb, hQ, ?_, ?_⟩
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
