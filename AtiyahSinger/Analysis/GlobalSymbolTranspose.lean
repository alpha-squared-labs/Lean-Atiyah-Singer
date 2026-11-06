/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSymbol
public import AtiyahSinger.Analysis.LocalTranspose
public import AtiyahSinger.Geometry.DualBundle

/-!
# Bilinear transposition in the global principal symbol quotient

Public module ID: M0683.

The symbol operation underlying SG III.3.11, (3.18), and 3.19.
At a genuine cotangent vector, reflect that vector and precompose a covector with
its actual fiber map. In induced dual frames this is the ordinary matrix transpose
of p(x,-ξ). The operation preserves each real order and descends to S^m/S^(m-1).
No homogeneous representative, compact base, density, or Hermitian metric is used.
The comparison with the actual operator transpose is in PrincipalSymbolTranspose.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

/-- Ordinary matrix transposition with reflected frequency preserves any local real symbol order. -/
theorem isSymbol_symbolTranspose {n r q : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (m : ℝ)
    (p : SymbolFunction n r q) (hp : IsSymbol U m p) :
    IsSymbol U m (symbolTranspose p) := by
  /- On U times the whole frequency space, reflection is a real linear isometry.
  Its frequency derivatives contribute only signs. Ordinary matrix transposition
  is a fixed continuous complex-linear map between finite-dimensional matrix spaces.
  Apply the chain rule to the mixed derivatives and bound this map's operator norm;
  the reflected frequency has the same norm. Smoothness and the order m follow. -/
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let A := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let B := EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)
  let : FiniteDimensional ℝ A := Module.Finite.trans ℂ A
  let : FiniteDimensional ℝ B := Module.Finite.trans ℂ B
  -- Ordinary matrix transpose is an invertible linear map of the actual operator spaces.
  let T : A ≃L[ℝ] B :=
    (((((LinearMap.toContinuousLinearMap :
      (EuclideanSpace ℂ (Fin r) →ₗ[ℂ] EuclideanSpace ℂ (Fin q)) ≃ₗ[ℂ] A).symm.trans
        Matrix.toEuclideanLin.symm).trans
        (Matrix.transposeLinearEquiv (Fin q) (Fin r) ℂ ℂ)).trans
        Matrix.toEuclideanLin).trans LinearMap.toContinuousLinearMap).restrictScalars ℝ
          |>.toContinuousLinearEquiv
  let e : V ≃L[ℝ] V := ContinuousLinearEquiv.neg ℝ
  have hT (x ξ : V) : symbolTranspose p x ξ = T (p x (e ξ)) := rfl
  -- Reflection preserves the coordinate domain, and the output conversion is smooth.
  refine ⟨?_, ?_⟩
  · intro z hz
    have hpz := hp.1.contDiffAt
      ((hU.prod isOpen_univ).mem_nhds (show (z.1, -z.2) ∈ U ×ˢ Set.univ from
        ⟨hz.1, Set.mem_univ _⟩))
    have hcomp := T.contDiff.contDiffAt.comp z
      (hpz.comp z (contDiffAt_fst.prodMk contDiffAt_snd.neg))
    exact hcomp.contDiffWithinAt
  · intro K hKU hK i j
    obtain ⟨C, hC, hbound⟩ := hp.2 K hKU hK i j
    -- At each frequency order, reflection and transpose induce one fixed linear equivalence.
    let L : (V [×j]→L[ℝ] A) ≃L[ℝ] (V [×j]→L[ℝ] B) :=
      (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft A
        (fun _ : Fin j ↦ e)).trans
        (T.continuousMultilinearMapCongrRight (fun _ : Fin j ↦ V))
    have hfreq (x ξ : V) : iteratedFDeriv ℝ j (symbolTranspose p x) ξ =
        L (iteratedFDeriv ℝ j (p x) (e ξ)) := by
      change iteratedFDeriv ℝ j (T ∘ (p x ∘ e)) ξ = _
      rw [T.iteratedFDeriv_comp_left]
      have hreflect := e.iteratedFDerivWithin_comp_right (p x)
        uniqueDiffOn_univ (x := ξ) (Set.mem_univ _) j
      simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hreflect
      rw [hreflect]
      rfl
    have hmixed (x ξ : V) : symbolDerivative (symbolTranspose p) i j x ξ =
        L.toContinuousLinearMap.compContinuousMultilinearMap
          (symbolDerivative p i j x (e ξ)) := by
      unfold symbolDerivative
      simp_rw [hfreq]
      exact L.iteratedFDeriv_comp_left
    refine ⟨‖L.toContinuousLinearMap‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
    intro x hx ξ
    rw [hmixed]
    calc
      _ ≤ ‖L.toContinuousLinearMap‖ * ‖symbolDerivative p i j x (e ξ)‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ ‖L.toContinuousLinearMap‖ * (C * (1 + ‖e ξ‖) ^ (m - (j : ℝ))) :=
        mul_le_mul_of_nonneg_left (hbound x hx (e ξ)) (norm_nonneg _)
      _ = (‖L.toContinuousLinearMap‖ * C) * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
        simp [e, mul_assoc]

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

/-- The reflected symbol acts on actual complex-linear covectors by precomposition. -/
def globalSymbolTranspose (p : GlobalSymbolFunction (n := n) E F) :
    GlobalSymbolFunction (n := n) (DualBundle F) (DualBundle E) :=
  fun x ξ ↦ (ContinuousLinearMap.compL ℂ (E x) (F x) ℂ).flip (p x (-ξ))

/-- The dual fiber formula uses reflection and ordinary evaluation, with no conjugation. -/
theorem globalSymbolTranspose_apply (p : GlobalSymbolFunction (n := n) E F)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
    (α : DualBundle F x) (v : E x) :
    globalSymbolTranspose p x ξ α v = α (p x (-ξ) v) := by
  /- The flipped composition map fixes p(x,-ξ) and sends α to α composed with it.
  Evaluating that actual functional at v gives the right-hand side. This formula
  works at every covector, including zero, and for unequal fiber ranks. -/
  rfl

/-- Bilinear transposition preserves sums of actual symbol families. -/
theorem globalSymbolTranspose_add (p p' : GlobalSymbolFunction (n := n) E F) :
    globalSymbolTranspose (p + p') = globalSymbolTranspose p + globalSymbolTranspose p' := by
  /- Evaluate at x,ξ,α,v. The covector α sends the sum of p(x,-ξ)v and p'(x,-ξ)v
  to the sum of their evaluations. Extensionality for the two continuous linear
  maps and the dependent symbol family gives the asserted equality. -/
  -- Evaluation in the genuine dual fiber is complex-linear.
  ext x ξ α v
  exact α.map_add _ _

/-- Complex scalars are unchanged by bilinear transposition. -/
theorem globalSymbolTranspose_smul (z : ℂ) (p : GlobalSymbolFunction (n := n) E F) :
    globalSymbolTranspose (z • p) = z • globalSymbolTranspose p := by
  /- At each x,ξ,α,v the left side is α(z p(x,-ξ)v). Complex linearity of α
  moves z outside, without conjugation. Apply extensionality to the actual maps;
  no Hermitian identification of a fiber with its dual occurs. -/
  ext x ξ α v
  exact α.map_smul z _


set_option linter.unusedSectionVars false in
/-- The two induced dual frames have exactly the same common coordinate region. -/
theorem symbolChartDomain_dualFrame
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    symbolChartDomain (DualBundle F) (DualBundle E) c (dualFrame F f) (dualFrame E e) =
      symbolChartDomain E F c e f := by
  /- Each dual frame has its primal frame's base set. Unfold the common domain:
  both sides intersect the chart target with the inverse images of e.baseSet and
  f.baseSet, only in opposite orders. Commutativity of intersection identifies them. -/
  simp only [symbolChartDomain, dualFrame_baseSet, Set.inter_right_comm]

/-- In valid induced dual frames, genuine cotangent transposition is reflected matrix transpose. -/
theorem globalSymbolInChart_globalSymbolTranspose
    (p : GlobalSymbolFunction (n := n) E F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (z η : EuclideanSpace ℝ (Fin n))
    (he : c.symm z ∈ e.baseSet) (hf : c.symm z ∈ f.baseSet) :
    globalSymbolInChart (DualBundle F) (DualBundle E) (globalSymbolTranspose p)
        c (dualFrame F f) (dualFrame E e) z η =
      symbolTranspose (globalSymbolInChart E F p c e f) z η := by
  /- Stage 1: covectorFromChart is real-linear in η, so its value at -η is the
  negative of its value at η. This requires no chart-derivative inverse.
  Stage 2: dual coordinates evaluate covectors on the inverse primal basis.
  At the valid point he,hf the primal frame and its inverse cancel. Expanding
  the resulting coefficients gives the ordinary transpose of the original matrix.
  Both valid-frame assumptions are retained; no equality off their bases is used. -/
  classical
  let x := c.symm z
  -- Dual-frame coefficients evaluate the actual covector on the inverse primal basis.
  have hcoeffF (α : DualBundle F x) (i : Fin q) :
      (dualFrame F f).continuousLinearMapAt ℂ x α i =
        α (f.symmL ℂ x (EuclideanSpace.single i 1)) := by
    rw [(dualFrame F f).continuousLinearMapAt_apply_of_mem ℂ
      (by simpa only [dualFrame_baseSet] using hf)]
    change dualModelEquiv q
      (((Bundle.Trivial.trivialization M ℂ).continuousLinearMapAt ℂ x).comp
        (α.comp (f.symmL ℂ x))) i = _
    rw [dualModelEquiv_apply, ContinuousLinearMap.comp_apply,
      (Bundle.Trivial.trivialization M ℂ).continuousLinearMapAt_apply_of_mem ℂ
        (Set.mem_univ x)]
    rfl
  have hcoeffE (α : DualBundle E x) (i : Fin r) :
      (dualFrame E e).continuousLinearMapAt ℂ x α i =
        α (e.symmL ℂ x (EuclideanSpace.single i 1)) := by
    rw [(dualFrame E e).continuousLinearMapAt_apply_of_mem ℂ
      (by simpa only [dualFrame_baseSet] using he)]
    change dualModelEquiv r
      (((Bundle.Trivial.trivialization M ℂ).continuousLinearMapAt ℂ x).comp
        (α.comp (e.symmL ℂ x))) i = _
    rw [dualModelEquiv_apply, ContinuousLinearMap.comp_apply,
      (Bundle.Trivial.trivialization M ℂ).continuousLinearMapAt_apply_of_mem ℂ
        (Set.mem_univ x)]
    rfl
  have hreflect : covectorFromChart c x (-η) = -covectorFromChart c x η := by
    ext v
    change inner ℝ (-η) ((mfderiv _ _ c x) v) =
      -inner ℝ η ((mfderiv _ _ c x) v)
    exact inner_neg_left _ _
  ext a i
  -- The input dual inverse frame has exactly the prescribed coefficient vector a.
  let α : DualBundle F x := (dualFrame F f).symmL ℂ x a
  have hα (j : Fin q) : α (f.symmL ℂ x (EuclideanSpace.single j 1)) = a j := by
    rw [← hcoeffF α j]
    exact congrArg (fun v : EuclideanSpace ℂ (Fin q) ↦ v j)
      ((dualFrame F f).continuousLinearMapAt_symmL
        (by simpa only [dualFrame_baseSet] using hf) a)
  let v : F x := p x (-covectorFromChart c x η)
    (e.symmL ℂ x (EuclideanSpace.single i 1))
  have hexpand : α v = ∑ j, (f.continuousLinearMapAt ℂ x v) j * a j := by
    have hv : (∑ j, (f.continuousLinearMapAt ℂ x v) j • EuclideanSpace.single j 1) =
        f.continuousLinearMapAt ℂ x v := by
      ext j
      simp [Pi.single_apply]
    calc
      α v = α (f.symmL ℂ x
          (∑ j, (f.continuousLinearMapAt ℂ x v) j • EuclideanSpace.single j 1)) := by
        rw [hv, f.symmL_continuousLinearMapAt hf v]
      _ = _ := by simp only [map_sum, map_smul, hα, smul_eq_mul]
  change (dualFrame E e).continuousLinearMapAt ℂ x
    (globalSymbolTranspose p x (covectorFromChart c x η) α) i = _
  rw [hcoeffE]
  change α v = _
  rw [symbolTranspose_apply]
  convert hexpand using 1
  congr 1
  funext j
  simp only [globalSymbolInChart, ContinuousLinearMap.comp_apply]
  rw [hreflect]

/-- Transposition preserves global order estimates without extra geometric hypotheses. -/
theorem IsGlobalSymbol.globalSymbolTranspose {m : ℝ}
    {p : GlobalSymbolFunction (n := n) E F}
    (hp : IsGlobalSymbol (n := n) (r := r) (q := q) E F m p) :
    IsGlobalSymbol (n := n) (r := q) (q := r)
      (DualBundle F) (DualBundle E) m (globalSymbolTranspose p) := by
  /- Fix any chart and two frames in the dual atlases. By the definition of these
  atlases both are induced from primal frames. The preceding domain equality and
  coordinate formula identify their symbol on the common open region with the
  reflected ordinary transpose. Apply isSymbol_symbolTranspose and the original
  order estimate. Local equality on this open region also identifies derivatives.
  No compactness or density of the whole base, or smooth frame change, is needed. -/
  -- Every frame in the designated dual atlas is induced from a primal frame.
  rintro c hc _ _ ⟨f, hf, rfl⟩ ⟨e, he, rfl⟩
  let := hf
  let := he
  rw [symbolChartDomain_dualFrame]
  let U := symbolChartDomain E F c e f
  let a := globalSymbolInChart E F p c e f
  let b := globalSymbolInChart (DualBundle F) (DualBundle E) (AtiyahSinger.globalSymbolTranspose p)
    c (dualFrame F f) (dualFrame E e)
  have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
  have ha : IsSymbol U m (symbolTranspose a) :=
    isSymbol_symbolTranspose U hU m a (hp c hc e f)
  have heq (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) : b x ξ = symbolTranspose a x ξ :=
    globalSymbolInChart_globalSymbolTranspose p c e f x ξ hx.1.2 hx.2
  refine ⟨ha.1.congr (fun z hz ↦ heq z.1 hz.1 z.2), ?_⟩
  intro K hKU hK i j
  obtain ⟨C, hC, hbound⟩ := ha.2 K hKU hK i j
  refine ⟨C, hC, ?_⟩
  intro x hx ξ
  -- Equality on the open coordinate region identifies the total mixed derivatives locally.
  have hnear : (fun y ↦ iteratedFDeriv ℝ j (b y) ξ) =ᶠ[nhds x]
      (fun y ↦ iteratedFDeriv ℝ j (symbolTranspose a y) ξ) := by
    filter_upwards [hU.mem_nhds (hKU hx)] with y hy
    rw [show b y = symbolTranspose a y from funext (heq y hy)]
  have hderiv := (hnear.iteratedFDeriv ℝ i).eq_of_nhds
  change ‖iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (b y) ξ) x‖ ≤ _
  rw [hderiv]
  exact hbound x hx ξ

/-- The actual reflected dual symbol packaged with its same-order estimate. -/
def globalSymbolSpaceTranspose {m : ℝ}
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalSymbolSpace (n := n) (r := q) (q := r) (DualBundle F) (DualBundle E) m :=
  ⟨globalSymbolTranspose p.val, p.property.globalSymbolTranspose⟩

/-- A lower-order change of representative remains lower order after transposition. -/
theorem globalPrincipalSymbolClass_transpose_congr {m : ℝ}
    (p p' : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (h : globalPrincipalSymbolClass E F m p = globalPrincipalSymbolClass E F m p') :
    globalPrincipalSymbolClass (DualBundle F) (DualBundle E) m (globalSymbolSpaceTranspose p) =
      globalPrincipalSymbolClass (DualBundle F) (DualBundle E) m
        (globalSymbolSpaceTranspose p') := by
  /- The quotient equality criterion puts p-p' in global order m-1. Transpose
  that actual difference, using additivity and scalar linearity to identify it
  with the difference of the transposes. Order preservation at m-1 and the target
  quotient criterion give equality of classes. Full smoothing is not required. -/
  -- The denominator consists of the same actual difference at one lower order.
  apply (globalPrincipalSymbolClass_eq_iff (DualBundle F) (DualBundle E) m _ _).mpr
  have hlow := ((globalPrincipalSymbolClass_eq_iff E F m p p').mp h).globalSymbolTranspose
  have hsub : globalSymbolTranspose (p.val - p'.val) =
      globalSymbolTranspose p.val - globalSymbolTranspose p'.val := by
    ext x ξ α v
    exact α.map_sub _ _
  rw [hsub] at hlow
  exact hlow

/-- Reflected dualization descended to the actual global principal-symbol quotient. -/
def globalPrincipalSymbolTranspose {m : ℝ} :
    GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m →
      GlobalPrincipalSymbolSpace (n := n) (r := q) (q := r) (DualBundle F) (DualBundle E) m :=
  Quotient.lift
    (fun p ↦ globalPrincipalSymbolClass (DualBundle F) (DualBundle E) m
      (globalSymbolSpaceTranspose p))
    (fun p p' h ↦ globalPrincipalSymbolClass_transpose_congr p p' (Quotient.sound h))

/-- Any actual representative computes the quotient transpose by reflected fiber dualization. -/
theorem globalPrincipalSymbolTranspose_class {m : ℝ}
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolTranspose (globalPrincipalSymbolClass E F m p) =
      globalPrincipalSymbolClass (DualBundle F) (DualBundle E) m
        (globalSymbolSpaceTranspose p) := by
  /- Evaluate the quotient lift on the representative p. Its prescribed value is
  precisely the class of the actual reflected dual symbol. The congruence proof
  ensures independence of p; no representative selection or homogeneity is imposed. -/
  rfl

/-- The zero principal class has zero transpose. -/
theorem globalPrincipalSymbolTranspose_zero (m : ℝ) :
    globalPrincipalSymbolTranspose
        (0 : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) = 0 := by
  /- Represent zero by the actual zero symbol. Precomposition with the zero
  fiber map is zero, even after reflection. Its class is the zero class in the
  dual-bundle quotient, as follows from linearity of the quotient projection. -/
  -- Represent zero by zero before applying the same quotient lift.
  change globalPrincipalSymbolTranspose (globalPrincipalSymbolClass E F m 0) = 0
  rw [globalPrincipalSymbolTranspose_class]
  have hz : globalSymbolSpaceTranspose
      (0 : globalSymbolSpace (n := n) (r := r) (q := q) E F m) = 0 := by
    apply Subtype.ext
    ext x ξ α v
    exact α.map_zero
  rw [hz, map_zero]

/-- Transposition is additive on the principal-symbol quotient. -/
theorem globalPrincipalSymbolTranspose_add {m : ℝ}
    (p p' : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolTranspose (p + p') =
      globalPrincipalSymbolTranspose p + globalPrincipalSymbolTranspose p' := by
  /- Choose actual representatives for both quotient elements. The class map
  preserves their sum. Apply globalSymbolTranspose_add, then the target class
  map's additivity. Quotient surjectivity removes the representative choices. -/
  obtain ⟨a, rfl⟩ := globalPrincipalSymbolClass_surjective E F m p
  obtain ⟨b, rfl⟩ := globalPrincipalSymbolClass_surjective E F m p'
  -- Addition is calculated on the original representatives and then projected.
  rw [← map_add, globalPrincipalSymbolTranspose_class,
    globalPrincipalSymbolTranspose_class, globalPrincipalSymbolTranspose_class, ← map_add]
  congr 1
  apply Subtype.ext
  exact globalSymbolTranspose_add a.val b.val

/-- The quotient transpose is complex-linear rather than conjugate-linear. -/
theorem globalPrincipalSymbolTranspose_smul {m : ℝ} (z : ℂ)
    (p : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolTranspose (z • p) = z • globalPrincipalSymbolTranspose p := by
  /- On an arbitrary representative apply globalSymbolTranspose_smul, where
  the covector's complex linearity leaves z unchanged. Both class projections
  preserve scalar multiplication, giving the formula on the quotient. -/
  obtain ⟨a, rfl⟩ := globalPrincipalSymbolClass_surjective E F m p
  -- The original bilinear dual action leaves the complex scalar unchanged.
  rw [← map_smul, globalPrincipalSymbolTranspose_class,
    globalPrincipalSymbolTranspose_class, ← map_smul]
  congr 1
  apply Subtype.ext
  exact globalSymbolTranspose_smul z a.val

end AtiyahSinger
