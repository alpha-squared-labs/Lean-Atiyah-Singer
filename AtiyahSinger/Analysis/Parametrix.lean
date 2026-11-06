/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalComposition
public import AtiyahSinger.Analysis.GlobalEllipticSymbol
public import AtiyahSinger.Analysis.PseudodifferentialAsymptotics

import AtiyahSinger.Analysis.DifferentialPrincipalSymbol
import AtiyahSinger.Analysis.ZeroOrderBundleMap
import Mathlib.Algebra.Ring.GeomSum

/-!
# Two-sided parametrices modulo smooth kernels

Public module ID: M0849.

A04: the geometric correction step in SG III.4.3--4.7, expressed for actual global
section maps. The finite sums below are explicit formulas. Asymptotic summation,
rather than norm convergence of a Neumann series, improves order-minus-one errors
to smooth kernels. This is a project-derived global version of SG's recursive
symbol correction. No Fredholm conclusion or distributional regularity is built in.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hμ in
/-- The actual identity on smooth sections is an order-zero global PDO. -/
theorem isPseudodifferentialOperator_id :
    IsPseudodifferentialOperator (n := n) (r := r) (q := r) E E μ 0
      (LinearMap.id : smoothSections (n := n) (r := r) E →ₗ[ℂ]
        smoothSections (n := n) (r := r) E) := by
  /- The identity fiber map is smooth because its matrix in two original frames
  is their given smooth transition matrix. Regard its exact section action as an
  order-zero differential operator, then apply the established differential-to-PDO
  construction. That construction provides the finite local representation with
  zero smoothing remainder and retains the original identity section map. -/
  -- The identity's columns are evaluations of the same smooth transition operator.
  have hid : IsSmoothBundleMap (n := n) (r := r) (q := r)
      (fun x ↦ (LinearMap.id : E x →ₗ[ℂ] E x)) := by
    intro e he f hf j
    let := he
    let := hf
    have hcolumn := ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin r))
      (EuclideanSpace.single j 1)).restrictScalars ℝ).contMDiff.comp_contMDiffOn
        (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e f)
    apply hcolumn.congr
    intro x hx
    change (f ⟨x, e.symmL ℂ x (EuclideanSpace.single j 1)⟩).2 =
      e.coordChangeL ℂ f x (EuclideanSpace.single j 1)
    rw [e.coordChangeL_apply f hx, e.symmL_apply hx.1]
  -- The zero-order realization acts by the original fiber identity on every section.
  let D : DifferentialOperator (n := n) (r := r) (q := r) E E 0 :=
    { toLinearMap := smoothSectionMap (fun x ↦ LinearMap.id) hid
      isDifferentialOperator :=
        isDifferentialOperator_smoothSectionMap (fun x ↦ LinearMap.id) hid }
  have hD : D.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    rfl
  simpa only [Nat.cast_zero, hD] using D.isPseudodifferentialOperator (μ := μ)

/-- The identity section map with its derived PDO certificate. -/
def PseudodifferentialOperator.id :
    PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ 0 where
  toLinearMap := LinearMap.id
  isPseudodifferentialOperator := isPseudodifferentialOperator_id μ

/-- The principal class of the identity operator is the actual fiber identity class. -/
theorem PseudodifferentialOperator.principalSymbol_id :
    (PseudodifferentialOperator.id (n := n) (r := r) (E := E) μ).principalSymbol =
      globalPrincipalSymbolClass E E 0 (globalIdentitySymbol (n := n) (r := r) (E := E)) := by
  /- Realize the exact identity section map as an order-zero differential operator.
  In a single common local frame its coordinate expression has constant coefficient I.
  The existing characterization therefore gives the fiber identity at every covector.
  Transfer that same section action through the differential-to-PDO principal comparison. -/
  classical
  have hid : IsSmoothBundleMap (n := n) (r := r) (q := r)
      (fun x ↦ (LinearMap.id : E x →ₗ[ℂ] E x)) := by
    intro e he f hf j
    let := he
    let := hf
    have hcolumn := ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin r))
      (EuclideanSpace.single j 1)).restrictScalars ℝ).contMDiff.comp_contMDiffOn
        (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e f)
    apply hcolumn.congr
    intro x hx
    change (f ⟨x, e.symmL ℂ x (EuclideanSpace.single j 1)⟩).2 =
      e.coordChangeL ℂ f x (EuclideanSpace.single j 1)
    rw [e.coordChangeL_apply f hx, e.symmL_apply hx.1]
  -- Realize exactly the identity map as an order-zero differential operator.
  let D : DifferentialOperator (n := n) (r := r) (q := r) E E 0 :=
    { toLinearMap := LinearMap.id
      isDifferentialOperator := by
        have h := isDifferentialOperator_smoothSectionMap (fun x ↦ LinearMap.id) hid
        have heq : smoothSectionMap (fun x ↦ LinearMap.id) hid = LinearMap.id := by
          apply LinearMap.ext
          intro s
          apply Subtype.ext
          rfl
        rwa [heq] at h }
  have hsymbol : D.principalSymbolFunction =
      (globalIdentitySymbol (n := n) (r := r) (E := E)).val := by
    funext x ξ
    apply ContinuousLinearMap.ext
    intro v
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have hxC : x ∈ c.source := mem_chart_source _ x
    have hxE : x ∈ e.baseSet := mem_baseSet_trivializationAt _ E x
    let U := c.source ∩ e.baseSet ∩ e.baseSet
    have hU : IsOpen U := (c.open_source.inter e.open_baseSet).inter e.open_baseSet
    -- In one and the same frame the identity expression has the constant coefficient I.
    let Q : CoordinateDifferentialOperator n r r 0 (c '' U) :=
      { coefficient := fun _ _ _ ↦ ContinuousLinearMap.id ℂ _
        smooth_coefficient := fun _ _ ↦ contDiffOn_const }
    have hQ : HasCoordinateExpression E E 0 D.toLinearMap c e e U Q := by
      refine ⟨Set.Subset.rfl, ?_⟩
      intro s y hy
      change (e ⟨y, s.val y⟩).2 = Q.apply (sectionInChart E c e s.val) (c y)
      have hsection : sectionInChart E c e s.val (c y) = (e ⟨y, s.val y⟩).2 := by
        unfold sectionInChart
        rw [c.left_inv hy.1.1]
      simp [CoordinateDifferentialOperator.apply, Q, hsection]
    have h := LinearMap.congr_fun
      (D.hasPrincipalSymbol c (chart_mem_atlas _ x) e e U hU Q hQ x
        ⟨⟨hxC, hxE⟩, hxE⟩ ξ) v
    have hlocal : e.linearMapAt ℂ x (D.principalSymbol x ξ v) = e.linearMapAt ℂ x v := by
      simpa [CoordinateDifferentialOperator.principalSymbol, Q] using h
    have hcancel := congrArg (e.symmL ℂ x) hlocal
    change D.principalSymbol x ξ v = v
    simpa only [e.coe_linearMapAt_of_mem hxE, e.symmL_apply hxE,
      e.symm_apply_apply_mk hxE] using hcancel
  -- The established differential-to-PDO comparison preserves this exact section action.
  have htransfer (l : ℝ) (hl : l = 0)
      (Q : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ l)
      (p : globalSymbolSpace (n := n) (r := r) (q := r) E E l)
      (hQ : Q.toLinearMap = LinearMap.id) (hp : p.val = globalSymbolId E)
      (hσ : Q.principalSymbol = globalPrincipalSymbolClass E E l p) :
      (PseudodifferentialOperator.id (n := n) (r := r) (E := E) μ).principalSymbol =
        globalPrincipalSymbolClass E E 0
          (globalIdentitySymbol (n := n) (r := r) (E := E)) := by
    subst l
    have hpi : p = globalIdentitySymbol (n := n) (r := r) (E := E) := Subtype.ext hp
    rw [← hpi]
    let I := PseudodifferentialOperator.id (n := n) (r := r) (E := E) μ
    have heq := I.principalSymbol_eq_of_toLinearMap_eq μ Q hQ.symm
    exact heq.trans hσ
  exact htransfer _ (Nat.cast_zero) (D.toPseudodifferentialOperator μ)
    D.principalGlobalSymbol rfl hsymbol (D.principalSymbol_toPseudodifferentialOperator μ)

/-- A two-sided parametrix means that both actual composition errors have smooth kernels. -/
def IsParametrix
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (Q : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E) :
    Prop :=
  IsSmoothingOperator μ (Q.comp P - LinearMap.id) ∧
    IsSmoothingOperator μ (P.comp Q - LinearMap.id)

/-- The finite geometric correction, with the left residual acting on the input bundle. -/
def parametrixPartialSum
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (Q : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E)
    (N : ℕ) : smoothSections (n := n) (r := q) F →ₗ[ℂ]
      smoothSections (n := n) (r := r) E :=
  (∑ j ∈ Finset.range N, (LinearMap.id - Q.comp P) ^ j).comp Q


set_option linter.unusedSectionVars false in
/-- The left geometric remainder is an exact identity, including the empty partial sum. -/
theorem parametrixPartialSum_comp
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (Q : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E)
    (N : ℕ) :
    (parametrixPartialSum P Q N).comp P - LinearMap.id =
      -(LinearMap.id - Q.comp P) ^ N := by
  /- Set R=I-QP. Associativity rewrites the left composite as the finite sum
  of R^j(I-R). Consecutive powers telescope to I-R^N. This is an identity in
  the endomorphism ring of smooth E sections; it needs no analytic hypothesis. -/
  -- The geometric sum is taken in the actual endomorphism ring of the source sections.
  let R := LinearMap.id - Q.comp P
  have hQP : Q.comp P = 1 - R := by
    dsimp only [R]
    change Q.comp P = LinearMap.id - (LinearMap.id - Q.comp P)
    abel
  change (∑ j ∈ Finset.range N, R ^ j) * (Q.comp P) - 1 = -(R ^ N)
  rw [hQP, geom_sum_mul_neg]
  abel

set_option linter.unusedSectionVars false in
/-- The same finite correction has the matching right geometric remainder. -/
theorem comp_parametrixPartialSum
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (Q : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E)
    (N : ℕ) :
    P.comp (parametrixPartialSum P Q N) - LinearMap.id =
      -(LinearMap.id - P.comp Q) ^ N := by
  /- First prove P(I-QP)^j=(I-PQ)^jP by induction and associativity.
  This moves P across the finite sum without identifying the E and F fibers.
  Telescope with PQ=I-(I-PQ) in the endomorphism ring of smooth F sections.
  The empty sum gives -I on both sides as well. -/
  let R := LinearMap.id - Q.comp P
  let S := LinearMap.id - P.comp Q
  -- Moving P through one residual exchanges the source and target endomorphisms.
  have hstep : P.comp R = S.comp P := by
    ext u
    simp [R, S]
  have hmove (j : ℕ) : P.comp (R ^ j) = (S ^ j).comp P := by
    induction j with
    | zero =>
      simp only [pow_zero]
      rfl
    | succ j hj =>
      rw [pow_succ, pow_succ]
      change P.comp ((R ^ j).comp R) = ((S ^ j).comp S).comp P
      rw [← LinearMap.comp_assoc, hj, LinearMap.comp_assoc, hstep,
        ← LinearMap.comp_assoc]
  -- Evaluate the finite sum after this exact exchange, then telescope on target sections.
  have hsum : P.comp (parametrixPartialSum P Q N) =
      (∑ j ∈ Finset.range N, S ^ j) * (P.comp Q) := by
    unfold parametrixPartialSum
    apply LinearMap.ext
    intro u
    change P ((∑ j ∈ Finset.range N, R ^ j) (Q u)) =
      (∑ j ∈ Finset.range N, S ^ j) (P (Q u))
    simp only [LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact LinearMap.congr_fun (hmove j) (Q u)
  have hPQ : P.comp Q = 1 - S := by
    dsimp only [S]
    change P.comp Q = LinearMap.id - (LinearMap.id - P.comp Q)
    abel
  change P.comp (parametrixPartialSum P Q N) - 1 = -(S ^ N)
  rw [hsum, hPQ, geom_sum_mul_neg]
  abel

include hM hT2 hSC hC hE hμ in
/-- Powers of an actual PDO endomorphism have the corresponding multiple order. -/
theorem IsPseudodifferentialOperator.pow {l : ℝ}
    (R : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := r) E)
    (hR : IsPseudodifferentialOperator E E μ l R) (N : ℕ) :
    IsPseudodifferentialOperator E E μ ((N : ℝ) * l) (R ^ N) := by
  /- Induct in the original endomorphism ring. Global composition multiplies
  the actual section maps, and the successor arithmetic gives the stated order. -/
  induction N with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul, pow_zero, Module.End.one_eq_id] using
      (isPseudodifferentialOperator_id (n := n) (r := r) (E := E) μ)
  | succ N hN =>
    have hcomp := IsPseudodifferentialOperator.comp (R ^ N) R hN hR
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, pow_succ,
      Module.End.mul_eq_comp] using hcomp

include hM hT2 hSC hC hE hF hμ in
/-- Two order-minus-one composition errors can be improved to genuine smoothing errors. -/
theorem exists_parametrix_of_order_neg_one {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (Q₀ : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))
    (hleft : IsPseudodifferentialOperator E E μ (-1)
      (Q₀.toLinearMap.comp P.toLinearMap - LinearMap.id))
    (hright : IsPseudodifferentialOperator F F μ (-1)
      (P.toLinearMap.comp Q₀.toLinearMap - LinearMap.id)) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m),
      IsParametrix μ P.toLinearMap Q.toLinearMap := by
  /- Stage 1: put R=I-Q₀P and S=I-PQ₀. Both have order -1. The jth
  correction R^j Q₀ has order -m-j by the power and composition theorems.
  Stage 2: asymptotically sum these actual maps. The resulting Q has order -m,
  and Q minus its N-term partial sum has order -m-N for every N. This step
  does not require small operator norm or convergence of the formal series.
  Stage 3: the two finite geometric identities give residuals -R^N and -S^N.
  Multiplying the summation remainder by P leaves order -N in both directions.
  Thus QP-I and PQ-I have every real order, by cofinality of negative integers.
  Choose smooth bundle presentations and use the all-order/kernel criterion
  to obtain genuine smooth kernels for both errors of this same Q. -/
  classical
  let R := LinearMap.id - Q₀.toLinearMap.comp P.toLinearMap
  let S := LinearMap.id - P.toLinearMap.comp Q₀.toLinearMap
  have hR : IsPseudodifferentialOperator E E μ (-1) R := by
    simpa only [neg_one_smul, neg_sub] using
      (IsPseudodifferentialOperator.smul (-1) (-1) _ hleft)
  have hS : IsPseudodifferentialOperator F F μ (-1) S := by
    simpa only [neg_one_smul, neg_sub] using
      (IsPseudodifferentialOperator.smul (-1) (-1) _ hright)
  let orders : ℕ → ℝ := fun j ↦ -m - j
  let terms : ℕ → smoothSections (n := n) (r := q) F →ₗ[ℂ]
      smoothSections (n := n) (r := r) E := fun j ↦ (R ^ j).comp Q₀.toLinearMap
  have horders : StrictAnti orders := by
    intro i j hij
    dsimp [orders]
    exact sub_lt_sub_left (Nat.cast_lt.mpr hij) _
  have hlim : Filter.Tendsto orders Filter.atTop Filter.atBot := by
    apply Filter.tendsto_atBot.mpr
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge (-m - b)
    filter_upwards [Filter.eventually_ge_atTop N] with j hj
    have hNj : (N : ℝ) ≤ j := Nat.cast_le.mpr hj
    dsimp [orders]
    linarith
  have hterms (j : ℕ) : IsPseudodifferentialOperator F E μ (orders j) (terms j) := by
    have h := IsPseudodifferentialOperator.comp (R ^ j) Q₀.toLinearMap
      (IsPseudodifferentialOperator.pow μ R hR j) Q₀.isPseudodifferentialOperator
    convert h using 1
    dsimp [orders]
    ring
  obtain ⟨Q, hQ⟩ := exists_pseudodifferential_expansion μ orders horders hlim terms hterms
  have hsum (N : ℕ) : (∑ j ∈ Finset.range N, terms j) =
      parametrixPartialSum P.toLinearMap Q₀.toLinearMap N := by
    ext u
    simp [parametrixPartialSum, terms, R]
  let Q' : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m) :=
    ⟨Q.toLinearMap, by simpa only [orders, Nat.cast_zero, sub_zero] using
      Q.isPseudodifferentialOperator⟩
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  refine ⟨Q', ?_, ?_⟩
  · apply (isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ _ A A).mpr
    intro l
    obtain ⟨N, hN⟩ := exists_nat_ge (-l)
    have hNl : -(N : ℝ) ≤ l := by linarith
    have hrem := IsPseudodifferentialOperator.comp
      (Q.toLinearMap - ∑ j ∈ Finset.range N, terms j) P.toLinearMap (hQ N)
      P.isPseudodifferentialOperator
    have hrem' : IsPseudodifferentialOperator E E μ (-(N : ℝ))
        ((Q.toLinearMap - parametrixPartialSum P.toLinearMap Q₀.toLinearMap N).comp
          P.toLinearMap) := by
      rw [← hsum]
      convert hrem using 1
      dsimp [orders]
      ring
    have hpower := IsPseudodifferentialOperator.smul (-(N : ℝ)) (-1) (R ^ N)
      (by simpa only [mul_neg_one] using IsPseudodifferentialOperator.pow μ R hR N)
    have h := IsPseudodifferentialOperator.add (-(N : ℝ)) _ _ hrem' hpower
    have heq :
        (Q.toLinearMap - parametrixPartialSum P.toLinearMap Q₀.toLinearMap N).comp
          P.toLinearMap + (-1 : ℂ) • R ^ N = Q'.toLinearMap.comp P.toLinearMap -
            LinearMap.id := by
      rw [neg_one_smul, ← parametrixPartialSum_comp P.toLinearMap Q₀.toLinearMap N]
      simp only [LinearMap.sub_comp, Q']
      abel
    rw [heq] at h
    exact h.mono hNl _
  · apply (isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ _ B B).mpr
    intro l
    obtain ⟨N, hN⟩ := exists_nat_ge (-l)
    have hNl : -(N : ℝ) ≤ l := by linarith
    have hrem := IsPseudodifferentialOperator.comp P.toLinearMap
      (Q.toLinearMap - ∑ j ∈ Finset.range N, terms j) P.isPseudodifferentialOperator (hQ N)
    have hrem' : IsPseudodifferentialOperator F F μ (-(N : ℝ))
        (P.toLinearMap.comp
          (Q.toLinearMap - parametrixPartialSum P.toLinearMap Q₀.toLinearMap N)) := by
      rw [← hsum]
      convert hrem using 1
      dsimp [orders]
      ring
    have hpower := IsPseudodifferentialOperator.smul (-(N : ℝ)) (-1) (S ^ N)
      (by simpa only [mul_neg_one] using IsPseudodifferentialOperator.pow μ S hS N)
    have h := IsPseudodifferentialOperator.add (-(N : ℝ)) _ _ hrem' hpower
    have heq : P.toLinearMap.comp
        (Q.toLinearMap - parametrixPartialSum P.toLinearMap Q₀.toLinearMap N) +
          (-1 : ℂ) • S ^ N = P.toLinearMap.comp Q'.toLinearMap - LinearMap.id := by
      rw [neg_one_smul, ← comp_parametrixPartialSum P.toLinearMap Q₀.toLinearMap N]
      simp only [LinearMap.comp_sub, Q']
      abel
    rw [heq] at h
    exact h.mono hNl _

include hM hT2 hSC hC hE hF hμ in
/-- PDO parametrices of the same map differ by a genuine smooth-kernel operator. -/
theorem isSmoothingOperator_sub_of_isParametrix {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (Q Q' : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap)
    (hQ' : IsParametrix μ P.toLinearMap Q'.toLinearMap) :
    IsSmoothingOperator μ (Q.toLinearMap - Q'.toLinearMap) := by
  /- Both given errors compose with the original PDOs by the smoothing ideals.
  Their difference is exactly Q-Q' as a section map. The all-order criterion
  then recovers its smooth kernel; no construction of a new parametrix is used. -/
  have hleft := IsSmoothingOperator.comp_isPseudodifferentialOperator
    (Q.toLinearMap.comp P.toLinearMap - LinearMap.id) Q'.toLinearMap
    hQ.1 Q'.isPseudodifferentialOperator
  have hright := IsPseudodifferentialOperator.comp_isSmoothingOperator
    Q.toLinearMap (P.toLinearMap.comp Q'.toLinearMap - LinearMap.id)
    Q.isPseudodifferentialOperator hQ'.2
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  apply (isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ
    (Q.toLinearMap - Q'.toLinearMap) A B).mpr
  intro l
  have hsub := IsPseudodifferentialOperator.add l _ _
    (hleft.isPseudodifferentialOperator l _)
    (IsPseudodifferentialOperator.smul l (-1) _ (hright.isPseudodifferentialOperator l _))
  simp only [neg_one_smul, ← sub_eq_add_neg] at hsub
  have hid :
      (Q.toLinearMap.comp P.toLinearMap - LinearMap.id).comp Q'.toLinearMap -
        Q.toLinearMap.comp (P.toLinearMap.comp Q'.toLinearMap - LinearMap.id) =
          Q.toLinearMap - Q'.toLinearMap := by
    ext u
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub]
    abel
  rwa [hid] at hsub

end AtiyahSinger
