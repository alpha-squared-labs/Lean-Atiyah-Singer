/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactTestFormalAdjoint
public import AtiyahSinger.Geometry.DeRhamComplex
public import AtiyahSinger.Geometry.DifferentialFormMetric

/-!
# The metric codifferential and Hodge Laplacian on the original forms

Public module ID: M1276.

D09: the codifferential is the unique formal adjoint of the original exterior
derivative, for the induced form metric and the volume of the same tangent
metric. The defining identity uses a compactly supported first test and an
arbitrary smooth second form, so it also defines the operator on noncompact
manifolds. No arbitrary positive density is substituted for the Riemannian
volume and no orientation is needed.

The degreewise Laplacian is the actual sum dδ + δd. In degree zero only δd
appears. These are operators on the original smooth differential forms, not
unbounded Hilbert-space extensions; no self-adjoint domain is silently chosen.

Sources: Lawson--Michelsohn, Spin Geometry, II.5, pp.123--126, and III.5,
p.195. The explicit complexification and compact-test formulation are standard
supplements. The metric is the existing native smooth tangent metric.
The compact-test construction and locality arguments retain the original forms and volume.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Module Set
open scoped BigOperators Manifold ContDiff ComplexConjugate Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  (g : SmoothTangentMetric (n := n) (M := M))

omit [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
/-- Exterior differentiation is local on the original smooth differential forms. -/
theorem support_smoothFormExteriorDerivative_subset (p : ℕ)
    (u : SmoothDifferentialForm (n := n) M p) :
    {x : M | (smoothFormExteriorDerivative p u).val x ≠ 0} ⊆
      closure {x : M | u.val x ≠ 0} := by
  intro x hx
  by_contra hout
  let V := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, V)
  let c := chartAt V x
  have hcx : c x ∈ c.target := mem_chart_target V x
  have hxsource : x ∈ c.source := mem_chart_source V x
  -- Outside the closed support, the original form vanishes on a whole neighborhood.
  have hz : ∀ᶠ y in 𝓝 x, u.val y = 0 := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hout] with y hy
    exact not_ne_iff.mp (fun h ↦ hy (subset_closure h))
  have hz' : ∀ᶠ y in 𝓝 (c x), u.val (c.symm y) = 0 := by
    have hc : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
      simpa only [ContinuousAt, c.left_inv hxsource] using c.continuousAt_symm hcx
    exact hc.eventually (p := fun y : M ↦ u.val y = 0) hz
  have hcoeff : differentialFormInChart (n := n) u.val c =ᶠ[𝓝 (c x)]
      (fun _ : V ↦ (0 : V [⋀^Fin p]→L[ℝ] ℂ)) := by
    filter_upwards [hz'] with y hy
    unfold differentialFormInChart
    rw [hy]
    rfl
  -- The coordinate derivative of the zero germ vanishes, and so does its pullback.
  apply hx
  have hspec :=
    (existsUnique_smoothFormExteriorDerivative (n := n) (M := M) p).exists.choose_spec
  rw [show (smoothFormExteriorDerivative p u).val x =
    differentialFormExteriorDerivative u.val x from hspec u x]
  change (extDeriv (differentialFormInChart (n := n) u.val c) (c x)).compContinuousLinearMap
    (mfderiv I I c x) = 0
  rw [hcoeff.extDeriv_eq]
  have hext : extDeriv (fun _ : V ↦ (0 : V [⋀^Fin p]→L[ℝ] ℂ)) (c x) = 0 := by
    simp only [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin, fderiv_const_apply,
      map_zero]
  rw [hext]
  rfl

/-- Positive Hermitian data for the original form pairing with its prescribed normalization. -/
@[instance_reducible]
def differentialFormInnerCore (g : SmoothTangentMetric (n := n) (M := M))
    (p : ℕ) (x : M) : InnerProductSpace.Core ℂ (DifferentialFormFiber (n := n) p x) := by
  classical
  -- Install the metric on a temporary copy only, to choose an orthonormal basis.
  let V := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x
  let a : Basis (Fin n) ℝ V := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let : FiniteDimensional ℝ V := Module.Finite.of_basis a
  let W := ULift.{0} V
  let core : InnerProductSpace.Core ℝ W :=
    { inner u v := g.inner x u.down v.down
      conj_inner_symm u v := g.symm x v.down u.down
      re_inner_nonneg v := by
        by_cases hv : v.down = 0
        · simp [hv]
        · exact (g.pos x v.down hv).le
      add_left u v w := by
        change g.inner x (u.down + v.down) w.down = _
        simp
      smul_left u v c := by
        change g.inner x (c • u.down) v.down = c * g.inner x u.down v.down
        simp
      definite v h := by
        have hv : v.down = 0 := by
          by_contra hv
          exact (ne_of_gt (g.pos x v.down hv)) h
        exact ULift.ext hv }
  let : InnerProductSpace.Core ℝ W := core
  let : NormedAddCommGroup W := core.toNormedAddCommGroup
  let : NormedSpace ℝ W := InnerProductSpace.Core.toNormedSpace
  let : InnerProductSpace ℝ W := InnerProductSpace.ofCore core.toCore
  let : FiniteDimensional ℝ W :=
    (ULift.moduleEquiv (R := ℝ) (M := V)).symm.finiteDimensional
  have hdim : Module.finrank ℝ W = n := by
    rw [(ULift.moduleEquiv (R := ℝ) (M := V)).finrank_eq]
    simpa using Module.finrank_eq_card_basis a
  let b : OrthonormalBasis (Fin n) ℝ W :=
    (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  let e : Fin n → V := fun i ↦ (b i).down
  have he (i j : Fin n) : g.inner x (e i) (e j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  let d : Basis (Fin n) ℝ V := b.toBasis.map (ULift.moduleEquiv (R := ℝ) (M := V))
  have hpair (a b : DifferentialFormFiber (n := n) p x) :
      differentialFormInner g p x a b = (p.factorial : ℂ)⁻¹ *
        ∑ i : Fin p → Fin n, conj (a (fun k ↦ e (i k))) * b (fun k ↦ e (i k)) :=
    differentialFormInner_eq_sum_orthonormal g p x e he a b
  have hself (a : DifferentialFormFiber (n := n) p x) :
      (differentialFormInner g p x a a).re = (p.factorial : ℝ)⁻¹ *
        ∑ i : Fin p → Fin n, Complex.normSq (a (fun k ↦ e (i k))) := by
    rw [hpair]
    simp only [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum,
      ← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hfactor : 0 < (p.factorial : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast p.factorial_pos)
  refine
    { inner := differentialFormInner g p x
      conj_inner_symm := ?_
      re_inner_nonneg := ?_
      add_left := ?_
      smul_left := ?_
      definite := ?_ }
  · intro a b
    simp only [hpair, map_mul, map_inv₀, map_natCast, map_sum, Complex.conj_conj]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  · intro a
    change 0 ≤ (differentialFormInner g p x a a).re
    rw [hself]
    exact mul_nonneg hfactor.le (Finset.sum_nonneg (fun _ _ ↦ Complex.normSq_nonneg _))
  · intro a b c
    simp only [hpair, ContinuousAlternatingMap.add_apply, map_add, add_mul,
      Finset.sum_add_distrib, mul_add]
  · intro a b c
    simp only [hpair, ContinuousAlternatingMap.smul_apply, smul_eq_mul, map_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro a ha
    have hz : (differentialFormInner g p x a a).re = 0 := congrArg Complex.re ha
    rw [hself] at hz
    have hsum : (∑ i : Fin p → Fin n, Complex.normSq (a (fun k ↦ e (i k)))) = 0 :=
      (mul_eq_zero.mp hz).resolve_left hfactor.ne'
    have hcoeff (i : Fin p → Fin n) : a (fun k ↦ e (i k)) = 0 := by
      apply Complex.normSq_eq_zero.mp
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ Complex.normSq_nonneg (a (fun k ↦ e (j k))))).mp hsum i (Finset.mem_univ _)
    have hzero : a.toAlternatingMap = 0 := by
      apply d.ext_alternating
      intro i hi
      exact hcoeff i
    ext v
    exact congrArg (fun f : V [⋀^Fin p]→ₗ[ℝ] ℂ ↦ f v) hzero

/-- Compactly supported tests separate all original smooth forms for the same metric volume. -/
theorem eq_zero_of_smoothFormPairing_eq_zero (p : ℕ)
    (v : SmoothDifferentialForm (n := n) M p)
    (hv : ∀ u : SmoothDifferentialForm (n := n) M p,
      IsCompact (closure {x : M | u.val x ≠ 0}) → smoothFormPairing g p u v = 0) :
    v = 0 := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  -- Multiplication uses the original alternating tensors in every original chart.
  let mulForm (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
      (w : SmoothDifferentialForm (n := n) M p) : SmoothDifferentialForm (n := n) M p :=
    ⟨fun x ↦ (f x : ℂ) • w.val x, by
      intro c hc
      have hc' := contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc)
      have hf' : ContDiffOn ℝ ∞ (fun y ↦ (f (c.symm y) : ℂ)) c.target :=
        (Complex.ofRealCLM.contMDiff.comp_contMDiffOn (hf.comp_contMDiffOn hc')).contDiffOn
      convert hf'.smul (w.property c hc) using 1
      ext y a
      rfl⟩
  -- A real bump square turns the assumed pairing into the norm of the once-cut-off form.
  apply Subtype.ext
  funext x
  let b : SmoothBumpFunction I x := Classical.choice inferInstance
  let w := mulForm b b.contMDiff v
  let z := mulForm b b.contMDiff w
  have hsupp (t : SmoothDifferentialForm (n := n) M p) :
      IsCompact (closure {y : M | (mulForm b b.contMDiff t).val y ≠ 0}) := by
    apply b.hasCompactSupport.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro y hy
    change b y ≠ 0
    intro hb
    apply hy
    change (b y : ℂ) • t.val y = 0
    rw [hb, Complex.ofReal_zero, zero_smul]
  have hnorm : smoothFormPairing g p w w = 0 := by
    rw [← hv z (hsupp w)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y ↦ by
      let : InnerProductSpace.Core ℂ (DifferentialFormFiber (n := n) p y) :=
        differentialFormInnerCore g p y
      change (differentialFormInnerCore g p y).inner
          ((b y : ℂ) • v.val y) ((b y : ℂ) • v.val y) =
        (differentialFormInnerCore g p y).inner
          ((b y : ℂ) • ((b y : ℂ) • v.val y)) (v.val y)
      simp only [InnerProductSpace.Core.inner_smul_left,
        InnerProductSpace.Core.inner_smul_right, Complex.conj_ofReal]
  have hw := (smoothFormPairing_self_eq_zero_iff g p w (hsupp v)).mp hnorm
  have hx := congrArg (fun u : SmoothDifferentialForm (n := n) M p ↦ u.val x) hw
  change (b x : ℂ) • v.val x = 0 at hx
  change v.val x = 0
  simpa only [b.eq_one, Complex.ofReal_one, one_smul] using hx

set_option maxHeartbeats 2000000 in
-- Construct the codifferential in local tensor coordinates and prove compact-test uniqueness.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- The exterior derivative has a unique metric formal adjoint on all smooth forms. -/
theorem existsUnique_smoothFormCodifferential (p : ℕ) :
    ∃! δ : SmoothDifferentialForm (n := n) M (p + 1) →ₗ[ℂ]
        SmoothDifferentialForm (n := n) M p,
      ∀ (u : SmoothDifferentialForm (n := n) M p)
        (v : SmoothDifferentialForm (n := n) M (p + 1)),
        IsCompact (closure {x : M | u.val x ≠ 0}) →
        smoothFormPairing g (p + 1) (smoothFormExteriorDerivative p u) v =
          smoothFormPairing g p u (δ v) := by
  classical
  -- Finite alternating-tensor coordinates serve only this construction.
  have hfinite (p : ℕ) : FiniteDimensional ℂ
      (EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ) := by
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let L : (EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ) →ₗ[ℂ]
        ((Fin p → Fin n) → ℂ) :=
      { toFun := fun a i ↦ a (fun k ↦ b (i k))
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    refine FiniteDimensional.of_injective L ?_
    intro a c h
    have heq : a.toAlternatingMap = c.toAlternatingMap := by
      apply b.ext_alternating
      intro i hi
      exact congrFun h i
    ext v
    exact congrArg (fun f : EuclideanSpace ℝ (Fin n) [⋀^Fin p]→ₗ[ℝ] ℂ ↦ f v) heq
  -- Transport the original every-chart smoothness and prescribed metric exactly.
  have hmodel (p : ℕ) :
      ∃ (R : ℕ) (Z : VectorBundleCore ℂ M (EuclideanSpace ℂ (Fin R))
          (atlas (EuclideanSpace ℝ (Fin n)) M))
        (e : (EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ) ≃L[ℂ]
          EuclideanSpace ℂ (Fin R)),
        letI : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
          inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin R)))
        letI : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦
          inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin R)))
        IsSmoothComplexBundle (n := n) (r := R) Z.Fiber ∧
        (∀ i, Z.baseSet i = i.val.source) ∧
        (∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
          (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (x : M) (_ : x ∈ c.source)
          (a : DifferentialFormFiber (n := n) p x),
          (Z.localTriv ⟨c, hc⟩ ⟨x, e a⟩).2 = e (a.compContinuousLinearMap
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
              𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm (c x)))) ∧
        ∃ Φ : SmoothDifferentialForm (n := n) M p ≃ₗ[ℂ]
            smoothSections (n := n) (r := R) Z.Fiber,
          (∀ u x, (Φ u).val x = e (u.val x)) ∧
        ∃ metric : SmoothHermitianMetric (n := n) (r := R) Z.Fiber,
          ∀ x a b, metric.pairing x a b =
            differentialFormInner g p x (e.symm a) (e.symm b) := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    let I₀ := 𝓘(ℝ, V)
    let W := V [⋀^Fin p]→L[ℝ] ℂ
    let : FiniteDimensional ℂ W := hfinite p
    let R := Module.finrank ℂ W
    let e : W ≃L[ℂ] EuclideanSpace ℂ (Fin R) :=
      (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv.trans
        (EuclideanSpace.equiv (Fin R) ℂ).symm
    let T := tangentBundleCore I₀ M
    let C (L : V →L[ℝ] V) : (EuclideanSpace ℂ (Fin R)) →L[ℂ]
        EuclideanSpace ℂ (Fin R) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun a ↦ e ((e.symm a).compContinuousLinearMap L)
          map_add' := by
            intro a b
            rw [e.symm.map_add, ← e.map_add]
            apply congrArg e
            ext v
            rfl
          map_smul' := by
            intro c a
            rw [e.symm.map_smul, RingHom.id_apply, ← e.map_smul]
            apply congrArg e
            ext v
            rfl }
    have hCsmooth : ContDiff ℝ ∞ C := by
      let B (L : V →L[ℝ] V) : W →L[ℝ] W :=
        ContinuousAlternatingMap.compContinuousLinearMapCLM L
      have hB : ContDiff ℝ ∞ B := contDiff_iff_contDiffAt.mpr fun L ↦
        (ContinuousAlternatingMap.analyticAt_compContinuousLinearMapCLM L).contDiffAt
      -- Complex linear maps are smooth exactly when their real coordinate columns are.
      let e₀ := EuclideanSpace.equiv (Fin R) ℂ
      let cols := (e₀.arrowCongr (ContinuousLinearEquiv.refl ℂ
        (EuclideanSpace ℂ (Fin R)))).trans (ContinuousLinearEquiv.piRing (Fin R))
      have hc : ContDiff ℝ ∞ (fun L ↦ cols (C L)) := by
        apply contDiff_pi.mpr
        intro i
        exact (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
          (hB.clm_apply contDiff_const)
      convert (cols.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hc using 1
      funext L
      exact (cols.symm_apply_apply (C L)).symm
    let Z : VectorBundleCore ℂ M (EuclideanSpace ℂ (Fin R)) (atlas V M) :=
      { baseSet := T.baseSet
        isOpen_baseSet := T.isOpen_baseSet
        indexAt := T.indexAt
        mem_baseSet_at := T.mem_baseSet_at
        coordChange := fun i j x ↦ C (T.coordChange j i x)
        coordChange_self := by
          intro i x hx a
          change e ((e.symm a).compContinuousLinearMap (T.coordChange i i x)) = a
          have ht : T.coordChange i i x = ContinuousLinearMap.id ℝ V := by
            apply ContinuousLinearMap.ext
            intro v
            exact T.coordChange_self i x hx v
          rw [ht]
          have hid : (e.symm a).compContinuousLinearMap (ContinuousLinearMap.id ℝ V) =
              e.symm a := by
            ext v
            rfl
          rw [hid, e.apply_symm_apply]
        continuousOn_coordChange := by
          intro i j
          exact hCsmooth.continuous.comp_continuousOn
            ((T.continuousOn_coordChange j i).mono (by
              intro x hx
              exact ⟨hx.2, hx.1⟩))
        coordChange_comp := by
          intro i j k x hx a
          change e (((e.symm (e ((e.symm a).compContinuousLinearMap
            (T.coordChange j i x))))).compContinuousLinearMap (T.coordChange k j x)) =
              e ((e.symm a).compContinuousLinearMap (T.coordChange k i x))
          rw [e.symm_apply_apply]
          apply congrArg e
          ext v
          apply congrArg (e.symm a)
          funext l
          exact T.coordChange_comp k j i x ⟨⟨hx.2, hx.1.2⟩, hx.1.1⟩ (v l) }
    let : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin R)))
    let : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin R)))
    let : IsManifold I₀ (∞ + 1) M := by simpa using
      (inferInstance : IsManifold I₀ ∞ M)
    let : T.IsContMDiff I₀ ∞ := tangentBundleCore.isContMDiff (I := I₀) (M := M)
    let : IsSmoothComplexBundle (n := n) (r := R) Z.Fiber := by
      constructor
      rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
      have hT := (T.contMDiffOn_coordChange I₀ j i (n := ∞))
      have hswap : T.baseSet i ∩ T.baseSet j ⊆ T.baseSet j ∩ T.baseSet i := by
        intro x hx
        exact ⟨hx.2, hx.1⟩
      have hcomp := hCsmooth.contMDiff.comp_contMDiffOn (hT.mono hswap)
      apply hcomp.congr
      intro x hx
      apply ContinuousLinearMap.ext
      intro a
      exact Z.localTriv_coordChange_eq i j hx a
    have hderiv (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M)
        (x : M) (hx : x ∈ c.source) :
        T.coordChange ⟨c, hc⟩ (T.indexAt x) x = mfderiv I₀ I₀ c.symm (c x) := by
      have hd := (mdifferentiable_of_mem_atlas (I := I₀) hc).mdifferentiableAt_symm
        (c.map_source hx)
      simp only [mfderiv, ite_eq_left hd]
      suffices h : fderiv ℝ (chartAt V x ∘ c.symm) (c x) =
          (tangentSpaceCastModel I₀ (c.symm (c x))).symm.toContinuousLinearMap.comp
            ((fderiv ℝ (chartAt V x ∘ c.symm) (c x)).comp
              (tangentSpaceCastModel I₀ (c x)).toContinuousLinearMap) by
        simpa [T, I₀, tangentBundleCore_coordChange, tangentBundleCore_indexAt,
          writtenInExtChartAt, extChartAt, c.left_inv hx, mfld_simps] using h
      apply ContinuousLinearMap.ext
      intro v
      rfl
    -- Identify the temporary core coordinates with the original differential-form coordinates.
    have hchart (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M)
        (x : M) (hx : x ∈ c.source) (a : DifferentialFormFiber (n := n) p x) :
        (Z.localTriv ⟨c, hc⟩ ⟨x, e a⟩).2 =
          e (a.compContinuousLinearMap (mfderiv I₀ I₀ c.symm (c x))) := by
      change e ((e.symm (e a)).compContinuousLinearMap
        (T.coordChange ⟨c, hc⟩ (T.indexAt x) x)) = _
      rw [e.symm_apply_apply, hderiv c hc x hx]
    have hsmooth (u : M → W) :
        IsSmoothDifferentialForm u ↔
          IsSmoothSection (n := n) (r := R) Z.Fiber (fun x ↦ e (u x)) := by
      constructor
      · intro hu
        rintro _ ⟨c, rfl⟩
        have hc := contMDiffOn_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I₀) (n := ∞) c.property)
        have he := (e.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
          ((hu c.val c.property).contMDiffOn.comp hc (fun x hx ↦ c.val.map_source hx))
        apply he.congr
        intro x hx
        change (Z.localTriv c ⟨x, e (u x)⟩).2 =
          e (differentialFormInChart u c.val (c.val x))
        exact (hchart c.val c.property x hx (u x)).trans (by
          unfold differentialFormInChart
          congr 2
          exact (congrArg u (c.val.left_inv hx)).symm)
      · intro hu c hc
        have hc' := contMDiffOn_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I₀) (n := ∞) hc)
        have hlocal := hu (Z.localTriv ⟨c, hc⟩) ⟨⟨c, hc⟩, rfl⟩
        have he := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
          (hlocal.comp hc' (fun y hy ↦ c.map_target hy))
        apply he.contDiffOn.congr
        intro y hy
        change differentialFormInChart u c y =
          e.symm ((Z.localTriv ⟨c, hc⟩ ⟨c.symm y, e (u (c.symm y))⟩).2)
        have heq := congrArg e.symm (hchart c hc (c.symm y)
          (c.map_target hy) (u (c.symm y)))
        simp only [e.symm_apply_apply] at heq
        apply Eq.trans _ heq.symm
        unfold differentialFormInChart
        congr 2
        exact (c.right_inv hy).symm
    let Φ : SmoothDifferentialForm (n := n) M p ≃ₗ[ℂ]
        smoothSections (n := n) (r := R) Z.Fiber :=
      { toFun := fun u ↦ ⟨fun x ↦ e (u.val x), (hsmooth u.val).mp u.property⟩
        invFun := fun s ↦ ⟨fun x ↦ e.symm (s.val x), (hsmooth _).mpr (by
          simpa only [e.apply_symm_apply] using
            (show IsSmoothSection (n := n) (r := R) Z.Fiber s.val from s.property))⟩
        left_inv := by
          intro u
          apply Subtype.ext
          funext x
          exact e.symm_apply_apply (u.val x)
        right_inv := by
          intro s
          apply Subtype.ext
          funext x
          exact e.apply_symm_apply (s.val x)
        map_add' := by
          intro u v
          apply Subtype.ext
          funext x
          exact e.map_add (u.val x) (v.val x)
        map_smul' := by
          intro a u
          apply Subtype.ext
          funext x
          exact e.map_smul a (u.val x) }
    -- Local smooth sections recover constant vectors in each chosen frame near a point.
    have hloc (f : Trivialization (EuclideanSpace ℂ (Fin R))
        (π (EuclideanSpace ℂ (Fin R)) Z.Fiber)) [MemTrivializationAtlas f]
        (x : M) (hx : x ∈ f.baseSet) (a : EuclideanSpace ℂ (Fin R)) :
        ∃ s : smoothSections (n := n) (r := R) Z.Fiber,
          ∀ᶠ y in 𝓝 x, s.val y = f.symmL ℂ y a := by
      obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I₀) x).mem_iff.mp
        (f.open_baseSet.mem_nhds hx)
      let s : ∀ y, Z.Fiber y := fun y ↦ (b y : ℂ) • f.symmL ℂ y a
      have hs : IsSmoothSection (n := n) (r := R) Z.Fiber s := by
        intro q hq y hy
        let := hq
        by_cases hyb : y ∈ tsupport b
        · have hyf : y ∈ f.baseSet := hb hyb
          have ht := (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) f q).contMDiffAt
            ((f.open_baseSet.inter q.open_baseSet).mem_nhds ⟨hyf, hy⟩)
          have ha : ContDiff ℝ ∞
              (fun L : EuclideanSpace ℂ (Fin R) →L[ℂ] EuclideanSpace ℂ (Fin R) ↦ L a) :=
            (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
          have hscalar := Complex.ofRealCLM.contMDiff.comp b.contMDiff
          have hmul : ContDiff ℝ ∞
              (fun z : ℂ × EuclideanSpace ℂ (Fin R) ↦ z.1 • z.2) := contDiff_smul
          have hlocal := hmul.comp_contMDiffAt
            (hscalar.contMDiffAt.prodMk_space (ha.comp_contMDiffAt ht))
          apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
          filter_upwards [f.open_baseSet.mem_nhds hyf, q.open_baseSet.mem_nhds hy]
            with z hzf hzq
          change (q.linearEquivAt ℂ z hzq) ((b z : ℂ) • f.symmL ℂ z a) =
            (b z : ℂ) • f.coordChangeL ℂ q z a
          rw [map_smul, f.coordChangeL_apply q ⟨hzf, hzq⟩, f.symmL_apply hzf]
          rfl
        · apply (contMDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin R)))
            |>.congr_of_eventuallyEq ?_).contMDiffWithinAt
          filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hyb,
            q.open_baseSet.mem_nhds hy] with z hzb hzq
          change (q.linearEquivAt ℂ z hzq) ((b z : ℂ) • f.symmL ℂ z a) = 0
          rw [image_eq_zero_of_notMem_tsupport hzb, Complex.ofReal_zero, zero_smul, map_zero]
      refine ⟨⟨s, hs⟩, ?_⟩
      filter_upwards [b.eventuallyEq_one] with y hy
      change (b y : ℂ) • f.symmL ℂ y a = f.symmL ℂ y a
      change b y = (1 : ℝ) at hy
      rw [hy, Complex.ofReal_one, one_smul]
    -- The transported metric has exactly the original pairing; no fiber norm is replaced.
    let core (x : M) : InnerProductSpace.Core ℂ (Z.Fiber x) :=
      { inner := fun a b ↦ differentialFormInner g p x (e.symm a) (e.symm b)
        conj_inner_symm := fun a b ↦ (differentialFormInnerCore g p x).conj_inner_symm _ _
        re_inner_nonneg := fun a ↦ (differentialFormInnerCore g p x).re_inner_nonneg _
        add_left := by
          intro a b c
          rw [e.symm.map_add]
          exact (differentialFormInnerCore g p x).add_left _ _ _
        smul_left := by
          intro a b c
          rw [e.symm.map_smul]
          exact (differentialFormInnerCore g p x).smul_left _ _ _
        definite := by
          intro a ha
          apply e.symm.injective
          exact ((differentialFormInnerCore g p x).definite _ ha).trans e.symm.map_zero.symm }
    let metric : SmoothHermitianMetric (n := n) (r := R) Z.Fiber :=
      { toCore := core
        isSmoothBundle := inferInstance
        contMDiffOn_gram := by
          intro f hf i j x hx
          let := hf
          obtain ⟨u, hu⟩ := hloc f x hx (EuclideanSpace.single i 1)
          obtain ⟨v, hv⟩ := hloc f x hx (EuclideanSpace.single j 1)
          have hpair := (contMDiff_differentialFormInner g p (Φ.symm u) (Φ.symm v)).contMDiffAt
            (x := x)
          apply (hpair.congr_of_eventuallyEq ?_).contMDiffWithinAt
          filter_upwards [hu, hv] with y hyu hyv
          change differentialFormInner g p y (e.symm (f.symmL ℂ y _))
            (e.symm (f.symmL ℂ y _)) =
            differentialFormInner g p y (e.symm (u.val y)) (e.symm (v.val y))
          rw [hyu, hyv] }
    exact ⟨R, Z, e, inferInstance, (fun _ ↦ rfl), hchart, Φ, (fun _ _ ↦ rfl),
      metric, fun _ _ _ ↦ rfl⟩
  -- Construct the actual exterior derivative as a first-order operator in this model.
  let V := EuclideanSpace ℝ (Fin n)
  let I₀ := 𝓘(ℝ, V)
  let W := V [⋀^Fin p]→L[ℝ] ℂ
  let W' := V [⋀^Fin (p + 1)]→L[ℝ] ℂ
  let : FiniteDimensional ℂ W := hfinite p
  let : FiniteDimensional ℂ W' := hfinite (p + 1)
  obtain ⟨r, E, e, hdata⟩ := hmodel p
  let : ∀ x, NormedAddCommGroup (E.Fiber x) := fun _ ↦
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin r)))
  let : ∀ x, NormedSpace ℂ (E.Fiber x) := fun _ ↦
    inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin r)))
  obtain ⟨hE, hEb, hEc, Φ, hΦ, h, hh⟩ := hdata
  let := hE
  obtain ⟨q, F, f, hdata⟩ := hmodel (p + 1)
  let : ∀ x, NormedAddCommGroup (F.Fiber x) := fun _ ↦
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin q)))
  let : ∀ x, NormedSpace ℂ (F.Fiber x) := fun _ ↦
    inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin q)))
  obtain ⟨hF, hFb, hFc, Ψ, hΨ, k, hk⟩ := hdata
  let := hF
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
  have hD : IsDifferentialOperator (n := n) (r := r) (q := q) E.Fiber F.Fiber 1 D := by
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
  let P : DifferentialOperator (n := n) (r := r) (q := q) E.Fiber F.Fiber 1 := ⟨D, hD⟩
  let : IsSmoothPositiveMeasure (n := n) g.riemannianVolume :=
    g.isSmoothPositiveMeasure_riemannianVolume
  obtain ⟨Q, hQ, _⟩ := P.existsUnique_compactTestMetricFormalAdjoint (μ := g.riemannianVolume) h k
  -- The differential adjoint initially tests two compactly supported sections.
  -- Cut off the second input near the first support and use differential locality.
  let δ := Φ.symm.toLinearMap.comp (Q.toLinearMap.comp Ψ.toLinearMap)
  have hpairE (u v : SmoothDifferentialForm (n := n) M p) :
      h.sectionPairing g.riemannianVolume (Φ u) (Φ v) = smoothFormPairing g p u v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      change h.pairing x ((Φ u).val x) ((Φ v).val x) =
        differentialFormInner g p x (u.val x) (v.val x)
      rw [hh, hΦ, hΦ, e.symm_apply_apply, e.symm_apply_apply]
  have hpairF (u v : SmoothDifferentialForm (n := n) M (p + 1)) :
      k.sectionPairing g.riemannianVolume (Ψ u) (Ψ v) = smoothFormPairing g (p + 1) u v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      change k.pairing x ((Ψ u).val x) ((Ψ v).val x) =
        differentialFormInner g (p + 1) x (u.val x) (v.val x)
      rw [hk, hΨ, hΨ, f.symm_apply_apply, f.symm_apply_apply]
  have hadj (u : SmoothDifferentialForm (n := n) M p)
      (v : SmoothDifferentialForm (n := n) M (p + 1))
      (hu : IsCompact (closure {x : M | u.val x ≠ 0})) :
      smoothFormPairing g (p + 1) (smoothFormExteriorDerivative p u) v =
        smoothFormPairing g p u (δ v) := by
    let K₀ := closure {x : M | u.val x ≠ 0}
    let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace V M
    obtain ⟨L, hL, hKL⟩ := exists_compact_superset hu
    obtain ⟨b, hb, hbL, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      I₀ isClosed_closure hKL (n := (⊤ : ℕ∞))
    let v' := smoothSectionMul F.Fiber (fun x ↦ (b x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp b.contMDiff) (Ψ v)
    have hu0 (x : M) (hx : x ∉ K₀) : u.val x = 0 := by
      by_contra h
      exact hx (subset_closure h)
    let su : supportedSmoothSections (n := n) (r := r) E.Fiber K₀ :=
      ⟨Φ u, by
        intro x hx
        rw [hΦ, hu0 x hx, map_zero]⟩
    let sv : supportedSmoothSections (n := n) (r := q) F.Fiber L :=
      ⟨v', by
        intro x hx
        change (b x : ℂ) • (Ψ v).val x = 0
        rw [hbL x hx, Complex.ofReal_zero, zero_smul]⟩
    have hvnear (x : M) (hx : x ∈ K₀) : ∀ᶠ y in 𝓝 x, v'.val y = (Ψ v).val y := by
      filter_upwards [mem_nhdsSet_iff_forall.mp hb x hx] with y hy
      change (b y : ℂ) • (Ψ v).val y = (Ψ v).val y
      rw [hy, Complex.ofReal_one, one_smul]
    have hP0 (x : M) (hx : x ∉ K₀) : (P.toLinearMap (Φ u)).val x = 0 := by
      have hnear : ∀ᶠ y in 𝓝 x,
          (Φ u).val y = (0 : smoothSections (n := n) (r := r) E.Fiber).val y := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
        rw [hΦ, hu0 y hy, map_zero]
        rfl
      rw [P.apply_eq_of_eventually_eq (Φ u) 0 x hnear, map_zero]
      rfl
    have hleft : k.sectionPairing g.riemannianVolume (P.toLinearMap (Φ u)) (Ψ v) =
        k.sectionPairing g.riemannianVolume (P.toLinearMap su.val) sv.val := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        by_cases hx : x ∈ K₀
        · exact congrArg (k.pairing x ((P.toLinearMap (Φ u)).val x))
            (Filter.Eventually.self_of_nhds (hvnear x hx)).symm
        · let : InnerProductSpace.Core ℂ (F.Fiber x) := k.toCore x
          change (k.toCore x).inner ((P.toLinearMap (Φ u)).val x) ((Ψ v).val x) =
            (k.toCore x).inner ((P.toLinearMap (Φ u)).val x) (v'.val x)
          rw [hP0 x hx, InnerProductSpace.Core.inner_zero_left,
            InnerProductSpace.Core.inner_zero_left]
    have hright : h.sectionPairing g.riemannianVolume su.val (Q.toLinearMap sv.val) =
        h.sectionPairing g.riemannianVolume (Φ u) (Q.toLinearMap (Ψ v)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        by_cases hx : x ∈ K₀
        · exact congrArg (h.pairing x ((Φ u).val x))
            (Q.apply_eq_of_eventually_eq v' (Ψ v) x (hvnear x hx))
        · let : InnerProductSpace.Core ℂ (E.Fiber x) := h.toCore x
          change (h.toCore x).inner ((Φ u).val x) ((Q.toLinearMap v').val x) =
            (h.toCore x).inner ((Φ u).val x) ((Q.toLinearMap (Ψ v)).val x)
          rw [hΦ, hu0 x hx, map_zero, InnerProductSpace.Core.inner_zero_left,
            InnerProductSpace.Core.inner_zero_left]
    have htest := hleft.trans ((hQ K₀ L hu hL su sv).trans hright)
    have hPd : P.toLinearMap (Φ u) = Ψ (smoothFormExteriorDerivative p u) := by
      change Ψ (smoothFormExteriorDerivative p (Φ.symm (Φ u))) = _
      rw [Φ.symm_apply_apply]
    have hQδ : Q.toLinearMap (Ψ v) = Φ (δ v) := (Φ.apply_symm_apply _).symm
    rw [hPd, hQδ, hpairE, hpairF] at htest
    exact htest
  refine ⟨δ, hadj, ?_⟩
  intro ε hε
  apply LinearMap.ext
  intro v
  apply sub_eq_zero.mp
  apply eq_zero_of_smoothFormPairing_eq_zero g p
  intro u hu
  have hsub : smoothFormPairing g p u (ε v - δ v) =
      smoothFormPairing g p u (ε v) - smoothFormPairing g p u (δ v) := by
    change (∫ x, differentialFormInner g p x (u.val x) ((ε v - δ v).val x)
      ∂g.riemannianVolume) = _
    have heq (x : M) : differentialFormInner g p x (u.val x) ((ε v - δ v).val x) =
        differentialFormInner g p x (u.val x) ((ε v).val x) -
          differentialFormInner g p x (u.val x) ((δ v).val x) := by
      let : InnerProductSpace.Core ℂ (DifferentialFormFiber (n := n) p x) :=
        differentialFormInnerCore g p x
      exact InnerProductSpace.Core.inner_sub_right (u.val x) ((ε v).val x) ((δ v).val x)
    simp_rw [heq]
    exact integral_sub (integrable_differentialFormInner g p u (ε v) hu)
      (integrable_differentialFormInner g p u (δ v) hu)
  rw [hsub, ← hε u v hu, ← hadj u v hu, sub_self]

/-- The metric codifferential, selected from its formal-adjoint characterization. -/
def smoothFormCodifferential (p : ℕ) :
    SmoothDifferentialForm (n := n) M (p + 1) →ₗ[ℂ]
      SmoothDifferentialForm (n := n) M p :=
  (existsUnique_smoothFormCodifferential g p).exists.choose

/-- The codifferential satisfies integration by parts for the actual metric volume. -/
theorem smoothFormCodifferential_formalAdjoint (p : ℕ)
    (u : SmoothDifferentialForm (n := n) M p)
    (v : SmoothDifferentialForm (n := n) M (p + 1))
    (hu : IsCompact (closure {x : M | u.val x ≠ 0})) :
    smoothFormPairing g (p + 1) (smoothFormExteriorDerivative p u) v =
      smoothFormPairing g p u (smoothFormCodifferential g p v) := by
  -- Use the exact witness selected by the original compact-test characterization.
  exact (existsUnique_smoothFormCodifferential g p).exists.choose_spec u v hu

/-- The metric codifferential is local on the original differential forms. -/
theorem support_smoothFormCodifferential_subset (p : ℕ)
    (v : SmoothDifferentialForm (n := n) M (p + 1)) :
    {x : M | (smoothFormCodifferential g p v).val x ≠ 0} ⊆
      closure {x : M | v.val x ≠ 0} := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let mulForm (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
      (w : SmoothDifferentialForm (n := n) M p) : SmoothDifferentialForm (n := n) M p :=
    ⟨fun x ↦ (f x : ℂ) • w.val x, by
      intro c hc
      have hc' := contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc)
      have hf' : ContDiffOn ℝ ∞ (fun y ↦ (f (c.symm y) : ℂ)) c.target :=
        (Complex.ofRealCLM.contMDiff.comp_contMDiffOn (hf.comp_contMDiffOn hc')).contDiffOn
      convert hf'.smul (w.property c hc) using 1
      ext y a
      rfl⟩
  intro x hx
  by_contra hxK
  obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    (isClosed_closure.isOpen_compl.mem_nhds hxK)
  let w := mulForm b b.contMDiff (smoothFormCodifferential g p v)
  let z := mulForm b b.contMDiff w
  have hsupp (t : SmoothDifferentialForm (n := n) M p) :
      closure {y : M | (mulForm b b.contMDiff t).val y ≠ 0} ⊆ tsupport b := by
    apply closure_minimal _ (isClosed_tsupport b)
    intro y hy
    apply subset_closure
    change b y ≠ 0
    intro hby
    apply hy
    change (b y : ℂ) • t.val y = 0
    rw [hby, Complex.ofReal_zero, zero_smul]
  have hcompact (t : SmoothDifferentialForm (n := n) M p) :
      IsCompact (closure {y : M | (mulForm b b.contMDiff t).val y ≠ 0}) :=
    b.hasCompactSupport.of_isClosed_subset isClosed_closure (hsupp t)
  have hnorm : smoothFormPairing g p w w = 0 := by
    calc
      smoothFormPairing g p w w =
          smoothFormPairing g p z (smoothFormCodifferential g p v) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y ↦ by
          let : InnerProductSpace.Core ℂ (DifferentialFormFiber (n := n) p y) :=
            differentialFormInnerCore g p y
          change (differentialFormInnerCore g p y).inner
              ((b y : ℂ) • (smoothFormCodifferential g p v).val y)
              ((b y : ℂ) • (smoothFormCodifferential g p v).val y) =
            (differentialFormInnerCore g p y).inner
              ((b y : ℂ) • ((b y : ℂ) • (smoothFormCodifferential g p v).val y))
              ((smoothFormCodifferential g p v).val y)
          simp only [InnerProductSpace.Core.inner_smul_left,
            InnerProductSpace.Core.inner_smul_right, Complex.conj_ofReal]
      _ = smoothFormPairing g (p + 1) (smoothFormExteriorDerivative p z) v :=
        (smoothFormCodifferential_formalAdjoint g p z v (hcompact w)).symm
      _ = 0 := by
        apply integral_eq_zero_of_ae
        exact Filter.Eventually.of_forall fun y ↦ by
          let : InnerProductSpace.Core ℂ (DifferentialFormFiber (n := n) (p + 1) y) :=
            differentialFormInnerCore g (p + 1) y
          by_cases hvy : v.val y = 0
          · change (differentialFormInnerCore g (p + 1) y).inner _ (v.val y) = 0
            rw [hvy, InnerProductSpace.Core.inner_zero_right]
          · have hdy : (smoothFormExteriorDerivative p z).val y = 0 := by
              by_contra hd
              exact hb (hsupp w (support_smoothFormExteriorDerivative_subset p z hd))
                (subset_closure hvy)
            change (differentialFormInnerCore g (p + 1) y).inner
              ((smoothFormExteriorDerivative p z).val y) _ = 0
            rw [hdy, InnerProductSpace.Core.inner_zero_left]
  have hw := (smoothFormPairing_self_eq_zero_iff g p w
    (hcompact (smoothFormCodifferential g p v))).mp hnorm
  have hx0 := congrArg (fun u : SmoothDifferentialForm (n := n) M p ↦ u.val x) hw
  change (b x : ℂ) • (smoothFormCodifferential g p v).val x = 0 at hx0
  apply hx
  simpa only [b.eq_one, Complex.ofReal_one, one_smul] using hx0

/-- Two successive metric codifferentials have zero composite. -/
theorem smoothFormCodifferential_comp (p : ℕ) :
    (smoothFormCodifferential g p).comp (smoothFormCodifferential g (p + 1)) = 0 := by
  apply LinearMap.ext
  intro v
  change smoothFormCodifferential g p (smoothFormCodifferential g (p + 1) v) = 0
  apply eq_zero_of_smoothFormPairing_eq_zero g p
  intro u hu
  -- Locality keeps the first derivative of a compact test compactly supported.
  have hdu : IsCompact (closure {x : M | (smoothFormExteriorDerivative p u).val x ≠ 0}) := by
    apply hu.of_isClosed_subset isClosed_closure
    exact closure_minimal (support_smoothFormExteriorDerivative_subset p u) isClosed_closure
  -- Two integrations by parts expose the original square-zero exterior derivative.
  rw [← smoothFormCodifferential_formalAdjoint g p u _ hu,
    ← smoothFormCodifferential_formalAdjoint g (p + 1) _ v hdu]
  have hd := LinearMap.congr_fun
    (smoothFormExteriorDerivative_comp (n := n) (M := M) p) u
  change smoothFormExteriorDerivative (p + 1) (smoothFormExteriorDerivative p u) = 0 at hd
  rw [hd]
  unfold smoothFormPairing
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    let : InnerProductSpace.Core ℂ (DifferentialFormFiber (n := n) (p + 2) x) :=
      differentialFormInnerCore g (p + 2) x
    exact InnerProductSpace.Core.inner_zero_left (𝕜 := ℂ) (v.val x)

/-- The Hodge Laplacian dδ + δd, with the incoming differential absent in degree zero. -/
def smoothFormHodgeLaplacian : (p : ℕ) →
    SmoothDifferentialForm (n := n) M p →ₗ[ℂ] SmoothDifferentialForm (n := n) M p
  | 0 => (smoothFormCodifferential g 0).comp (smoothFormExteriorDerivative 0)
  | p + 1 =>
      (smoothFormExteriorDerivative p).comp (smoothFormCodifferential g p) +
        (smoothFormCodifferential g (p + 1)).comp (smoothFormExteriorDerivative (p + 1))

end AtiyahSinger
