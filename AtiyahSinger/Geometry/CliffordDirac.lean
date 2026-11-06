/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalDifferentialOperator
public import AtiyahSinger.Analysis.SmoothSectionMultiplication
public import AtiyahSinger.Geometry.AtlasConnectionContraction
public import AtiyahSinger.Geometry.ConnectionExistence
public import AtiyahSinger.Geometry.NativeAtlasConnection
public import AtiyahSinger.Geometry.SmoothCliffordModule

/-!
# The actual Clifford contraction of a smooth complex connection

Public module ID: M1124.

S02: construct the first-order operator on the original smooth sections by
contracting their given covariant derivative with the given smooth Clifford
action. SG II.5, formula (5.0) and Lemma 5.1, pp.112--113, use the same formula
for a metric Clifford-module bundle with a Riemannian connection. Here the action is on the
actual cotangent fibers, so its value at a covector already incorporates
the musical identification used in the tangent description.

The present generalized Clifford contraction needs only a smooth complex
connection. Compatibility with a Hermitian metric or the Clifford action
is not needed for its first-order property or principal symbol. These
weaker hypotheses are a project supplement, not the full Dirac-bundle
conditions of SG Definition 5.2, p.114. Formal symmetry, a canonical spin
connection, tensor twisting and the spin-symbol K class are not asserted.

The actual finite-sum contraction is defined in SmoothCliffordModule.
The existence theorem supplies a differential operator with exactly that
action, and this unique operator is retained in every later statement.
With the project's D_j = -i partial_j convention its principal symbol is
+i times Clifford multiplication; the constant is not silently removed.
No compactness is assumed. Empty bases, zero dimension and zero bundle
rank are allowed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  {g : SmoothCotangentMetric (n := n) (M := M)}

namespace SmoothCliffordModule

variable (C : SmoothCliffordModule (n := n) (r := r) E g)
  (cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℂ (Fin r)) E)
  (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
  (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E cov)

include hM hE hT hSC hcov hcomplex

/-- Clifford contraction determines one actual first-order differential operator on sections. -/
theorem existsUnique_diracOperator :
    ∃! D : DifferentialOperator (n := n) (r := r) (q := r) E E 1,
      ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
        (D.toLinearMap u).val x = C.contract x (cov u.val x) := by
  /- Stage 1: express the original Clifford action in the native smooth atlas.
  Its finitely many smooth input-frame columns reconstruct the whole
  coordinate operator. An original frame transition changes the output
  frame and gives the required off-zero atlas smoothness certificate.
  Stage 2: express the same supplied covariant derivative as an atlas
  connection. Reuse the intrinsic atlas connection-contraction theorem,
  which supplies its first-order operator and basis-independent action.
  Stage 3: the native section equivalence identifies the two actual section
  carriers. Their coordinate conversions cancel, so the same local
  expressions certify the native operator. The connection comparison
  identifies each summand of its action with C.contract x (cov u.val x).
  Stage 4: any other operator with that pointwise action has the same
  section map. Extensionality and proof irrelevance give uniqueness
  of the full differential operator. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let H := EuclideanSpace ℝ (Fin n)
    let F := EuclideanSpace ℂ (Fin r)
    let := ComplexBundle.modelTopology F E
    let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
    let e := nativeSmoothSectionLinearEquiv (n := n) (r := r) E
    let c : AtlasSymbolFunction (n := n) E E := fun x ξ ↦ C.clifford x ξ
    have hc (x : M) : IsLinearMap ℝ (c x) := (C.clifford x).isLinear
    -- Recover the whole smooth coordinate operator from its finitely many native columns.
    have hs : IsSmoothOffZeroAtlasSymbol A A c := by
      intro d hd i j
      let := i.property
      let := j.property
      let b (a : Fin r) : F := EuclideanSpace.single a 1
      let column (a : Fin r) (z : H × H) : F :=
        i.val.linearMapAt ℂ (d.symm z.1)
          (C.clifford (d.symm z.1) (covectorFromChart d (d.symm z.1) z.2)
            (i.val.symmL ℂ (d.symm z.1) (b a)))
      let S (z : H × H) : F →L[ℂ] F :=
        ∑ a : Fin r, (EuclideanSpace.proj a).smulRight (column a z)
      have hcolumn (a : Fin r) : ContDiffOn ℝ ∞ (column a)
          ((d.target ∩ d.symm ⁻¹' i.val.baseSet) ×ˢ Set.univ) :=
        C.contDiffOn_clifford d hd i.val (b a)
      have hS : ContDiffOn ℝ ∞ S
          ((d.target ∩ d.symm ⁻¹' i.val.baseSet) ×ˢ Set.univ) := by
        apply ContDiffOn.sum
        intro a _
        exact ((ContinuousLinearMap.smulRightL ℂ F F (EuclideanSpace.proj a)).restrictScalars
          ℝ).contDiff.comp_contDiffOn (hcolumn a)
      have hsum (v : F) : ∑ a : Fin r, v a • b a = v := by
        simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
          EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, b] using
          (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.sum_repr v
      have hSapply (z : H × H) (v : F) :
          S z v = i.val.linearMapAt ℂ (d.symm z.1)
            (C.clifford (d.symm z.1) (covectorFromChart d (d.symm z.1) z.2)
              (i.val.symmL ℂ (d.symm z.1) v)) := by
        conv_rhs => rw [← hsum v, map_sum, map_sum, map_sum]
        simp only [S, column, sum_apply, ContinuousLinearMap.smulRight_apply,
          map_smul, EuclideanSpace.proj]
        rfl
      -- Changing the output frame uses the original smooth transition on the actual overlap.
      let T (z : H × H) : F →L[ℂ] F :=
        (i.val.coordChangeL ℂ j.val (d.symm z.1)).toContinuousLinearMap
      let U := atlasSymbolChartDomain A A d i j ×ˢ {ξ : H | ξ ≠ 0}
      have hT : ContDiffOn ℝ ∞ T U := by
        have hbase := IsSmoothComplexBundle.contMDiffOn_coordChange
          (n := n) (E := E) i.val j.val
        have hsymm := contMDiffOn_symm_of_mem_maximalAtlas
          (I := 𝓘(ℝ, H)) (n := ∞) (IsManifold.subset_maximalAtlas hd)
        have htrans := hbase.comp
          (hsymm.mono (show atlasSymbolChartDomain A A d i j ⊆ d.target from
            fun _ hz ↦ hz.1.1)) (fun z hz ↦ ⟨hz.1.2, hz.2⟩)
        have htrans' : ContDiffOn ℝ ∞
            (fun z : H ↦ (i.val.coordChangeL ℂ j.val (d.symm z)).toContinuousLinearMap)
            (atlasSymbolChartDomain A A d i j) := by
          exact contMDiffOn_iff_contDiffOn.mp htrans
        exact htrans'.comp contDiffOn_fst (fun z hz ↦ hz.1)
      let μ := (ContinuousLinearMap.compL ℂ F F F).bilinearRestrictScalars ℝ
      have hprod : ContDiffOn ℝ ∞ (fun z ↦ (T z).comp (S z)) U :=
        (μ.contDiff.comp_contDiffOn hT).clm_apply
          (hS.mono (fun z hz ↦ ⟨hz.1.1, Set.mem_univ _⟩))
      apply hprod.congr
      intro z hz
      have hi : d.symm z.1 ∈ (A.chart i).baseSet := hz.1.1.2
      have hj : d.symm z.1 ∈ (A.chart j).baseSet := hz.1.2
      let e₀ := EuclideanSpace.equiv (Fin r) ℂ
      let P (k : A.Index) (x : M) (hx : x ∈ (A.chart k).baseSet) : E x ≃ₗ[ℂ] F :=
        (A.frameLinearEquiv k x hx).trans e₀.symm.toLinearEquiv
      let (k : A.Index) : MemTrivializationAtlas k.val := k.property
      have hP (k : A.Index) (x : M) (hx : x ∈ (A.chart k).baseSet) :
          P k x hx = k.val.linearEquivAt ℂ x hx := by
        apply LinearEquiv.ext
        intro v
        exact e₀.symm_apply_apply (k.val ⟨x, v⟩).2
      apply ContinuousLinearMap.ext
      intro v
      dsimp only [Function.uncurry, atlasGlobalSymbolInChart]
      rw [dite_eq_left ⟨hi, hj⟩]
      change P j (d.symm z.1) hj
        (C.clifford (d.symm z.1) (covectorFromChart d (d.symm z.1) z.2)
          ((P i (d.symm z.1) hi).symm v)) = (T z) (S z v)
      rw [hP, hP]
      erw [hSapply z v]
      erw [i.val.symmL_apply (R := ℂ) hi]
      change (j.val ⟨d.symm z.1,
        C.clifford (d.symm z.1) (covectorFromChart d (d.symm z.1) z.2)
          (i.val.symm (d.symm z.1) v)⟩).2 =
        i.val.coordChangeL ℂ j.val (d.symm z.1)
          (i.val.linearMapAt ℂ (d.symm z.1)
            (C.clifford (d.symm z.1) (covectorFromChart d (d.symm z.1) z.2)
              (i.val.symm (d.symm z.1) v)))
      rw [i.val.coordChangeL_apply (R := ℂ) j.val ⟨hi, hj⟩,
        i.val.symm_linearMapAt (R := ℂ) hi]
    obtain ⟨covA, hcovA⟩ := exists_atlasComplexConnection_native cov hcov hcomplex
    let P := atlasConnectionContraction covA c hc hs
    let L := e.toLinearMap.comp (P.toLinearMap.comp e.symm.toLinearMap)
    -- The atlas/native coordinate conversions cancel; reuse exactly the same local expression.
    have hL : IsDifferentialOperator E E 1 L := by
      intro d hd i hi j hj x hx
      let ia : A.Index := ⟨i, hi⟩
      let ja : A.Index := ⟨j, hj⟩
      obtain ⟨U, hU, hxU, Q, hQ⟩ := P.isAtlasDifferentialOperator d hd ia ja x hx
      refine ⟨U, hU, hxU, Q, hQ.1, ?_⟩
      intro u y hy
      have hlocal := hQ.2 (e.symm u) y hy
      have hcoord : atlasSectionInChart A d ia (e.symm u).val =
          sectionInChart E d i u.val := by
        funext z
        exact (EuclideanSpace.equiv (Fin r) ℂ).symm_apply_apply _
      rw [hcoord] at hlocal
      exact ((EuclideanSpace.equiv (Fin r) ℂ).symm_apply_apply _).symm.trans hlocal
    let D : DifferentialOperator (n := n) (r := r) (q := r) E E 1 := ⟨L, hL⟩
    have hD (u : smoothSections (n := n) (r := r) E) (x : M) :
        (D.toLinearMap u).val x = C.contract x (cov u.val x) := by
      change (P.toLinearMap (e.symm u)).val x = _
      rw [atlasConnectionContraction_apply]
      change (∑ a : Fin n, C.clifford x (EuclideanSpace.proj a)
        (covA.covariantDerivative (e.symm u) x (EuclideanSpace.single a 1))) = _
      apply Finset.sum_congr rfl
      intro a _
      rw [show covA.covariantDerivative (e.symm u) x (EuclideanSpace.single a 1) =
        cov u.val x (EuclideanSpace.single a 1) from hcovA u x (EuclideanSpace.single a 1)]
    refine ⟨D, hD, ?_⟩
    intro D' hD'
    have hmaps : D'.toLinearMap = D.toLinearMap := by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext x
      exact (hD' u x).trans (hD u x).symm
    cases D' with
    | mk L' hL' =>
      change L' = L at hmaps
      subst L'
      rfl

/-- The original Clifford contraction, selected by its unique section-action specification. -/
def diracOperator : DifferentialOperator (n := n) (r := r) (q := r) E E 1 :=
  (C.existsUnique_diracOperator cov hcov hcomplex).exists.choose

/-- The chosen operator retains the same Clifford action and the same covariant derivative. -/
theorem diracOperator_apply (u : smoothSections (n := n) (r := r) E) (x : M) :
    ((C.diracOperator cov hcov hcomplex).toLinearMap u).val x =
      C.contract x (cov u.val x) := by
  /- Apply the specification of precisely the witness chosen by
  diracOperator. Both supplied geometric maps, the original smooth
  section and its base point remain unchanged. The right side is the
  explicit finite contraction, not a chosen operator with this symbol. -/
  exact (C.existsUnique_diracOperator cov hcov hcomplex).exists.choose_spec u x

/-- SG Lemma 5.5: the commutator with a real smooth scalar is actual Clifford multiplication. -/
theorem diracOperator_smoothSectionMul (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ f)
    (u : smoothSections (n := n) (r := r) E) (x : M) :
    ((C.diracOperator cov hcov hcomplex).toLinearMap
      (smoothSectionMul E (fun y ↦ (f y : ℂ)) (Complex.ofRealCLM.contMDiff.comp hf) u)).val x =
      C.clifford x (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) f x) (u.val x) +
        (f x : ℂ) • ((C.diracOperator cov hcov hcomplex).toLinearMap u).val x := by
  /- Stage 1: apply diracOperator_apply to the same pointwise scalar
  multiple of u. It is exactly the original smoothSectionMul section;
  real scalar multiplication and its complex cast agree on each fiber.
  The native connection Leibniz identity gives f(x) times cov u at x
  plus the E-valued covector v -> df_x(v) u(x).
  Stage 2: distribute the actual finite contraction over these terms.
  Complex linearity extracts f(x). In the remaining sum, real linearity
  of C.clifford and the dual basis expansion of df_x give precisely
  C.clifford x (mfderiv f x) (u(x)). There is no factor i in this
  commutator: that factor belongs only to the principal-symbol convention.
  Stage 3: the original smooth-action specification identifies the first
  contraction with the same D u. This is SG II.5 Lemma 5.5, equation
  (5.8), p.116, with cotangent df in place of its metric-dual gradient;
  its calculation needs no Hermitian or Clifford-connection compatibility. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let H := EuclideanSpace ℝ (Fin n)
    let t := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have ht : x ∈ t.baseSet := mem_baseSet_trivializationAt _ E x
    have hu : ContMDiffAt I (I.prod 𝓘(ℝ, EuclideanSpace ℂ (Fin r))) ∞
        (fun y ↦ (⟨y, u.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)) x :=
      (t.contMDiffAt_section_iff ht).mpr
        ((u.property t inferInstance).contMDiffAt (t.open_baseSet.mem_nhds ht))
    have hmul : (smoothSectionMul E (fun y ↦ (f y : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hf) u).val = f • u.val := by
      funext y
      rfl
    have hleibniz := cov.isCovariantDerivativeOnUniv.leibniz
      (hu.mdifferentiableAt (by simp)) ((hf x).mdifferentiableAt (by simp))
    -- The ordinary real Leibniz rule applies to the same original section and function.
    rw [C.diracOperator_apply cov hcov hcomplex, C.diracOperator_apply cov hcov hcomplex,
      hmul, hleibniz]
    have hsum (v : H) : ∑ a : Fin n,
        EuclideanSpace.proj a v • EuclideanSpace.single a 1 = v := by
      simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr,
        EuclideanSpace.proj, PiLp.proj_apply] using
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    have hdual (a : H →L[ℝ] ℝ) :
        a = ∑ j : Fin n, a (EuclideanSpace.single j 1) • EuclideanSpace.proj j := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [sum_apply, smul_apply, smul_eq_mul]
      conv_lhs => rw [← hsum v]
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    -- Dual-basis reconstruction turns contraction of df tensor u into c(df)u.
    let df : CotangentFiber (n := n) x := mfderiv I 𝓘(ℝ, ℝ) f x
    have hdf : C.contract x (df.smulRight (u.val x)) = C.clifford x df (u.val x) := by
      conv_rhs => rw [hdual df, map_sum]
      simp only [contract, ContinuousLinearMap.smulRight_apply, LinearMap.sum_apply,
        map_smul, LinearMap.smul_apply, LinearMap.map_smul_of_tower]
      rfl
    have hreal (v : E x) : f x • v = (f x : ℂ) • v := rfl
    calc
      C.contract x (f x • cov u.val x + df.smulRight (u.val x)) =
          f x • C.contract x (cov u.val x) +
            C.contract x (df.smulRight (u.val x)) := by
        simp only [contract, add_apply, smul_apply,
          map_add, LinearMap.map_smul_of_tower, Finset.sum_add_distrib, Finset.smul_sum]
      _ = C.clifford x (mfderiv I 𝓘(ℝ, ℝ) f x) (u.val x) +
          (f x : ℂ) • C.contract x (cov u.val x) := by
        rw [hdf, hreal, add_comm]

/-- In the D_j = -i partial_j convention the principal symbol is +i Clifford multiplication. -/
theorem diracOperator_principalSymbol (x : M) (ξ : CotangentFiber (n := n) x) :
    (C.diracOperator cov hcov hcomplex).principalSymbol x ξ =
      Complex.I • C.clifford x ξ := by
  /- Stage 1: identify the given pointwise real-scalar multiple with the
  original smoothSectionMul section. The proved Dirac Leibniz identity
  then supplies its scalar-derivative term c(df)u on the same fibers.
  Stage 2: the principal-symbol characterization by that Leibniz identity
  gives +i c(ξ), using the fixed D_j = -i partial_j convention. This
  identifies the symbol of the selected actual operator. -/
  -- The original real-function commutator determines the same local principal symbol.
  refine (C.diracOperator cov hcov hcomplex).principalSymbol_eq_smul_of_leibniz
    (fun y η ↦ C.clifford y η) ?_ x ξ
  intro φ hφ u v hv y
  have heq : v = smoothSectionMul E (fun z ↦ (φ z : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hφ) u := by
    apply Subtype.ext
    funext z
    exact hv z
  rw [heq]
  exact C.diracOperator_smoothSectionMul cov hcov hcomplex φ hφ u y

/-- The Clifford square identity makes the same first-order operator elliptic. -/
theorem diracOperator_isElliptic :
    (C.diracOperator cov hcov hcomplex).IsElliptic := by
  /- Stage 1: fix a nonzero original covector ξ at x. Positive
  definiteness gives a=g.inner x ξ ξ>0. The Clifford relation states
  c(ξ)^2=-a Id, and complex linearity gives (i c(ξ))^2=a Id.
  Stage 2: a is nonzero, so a⁻¹ times the same i c(ξ) is a two-sided
  inverse of the principal map computed above. Hence that map is
  bijective on the original fiber, which is the existing ellipticity
  predicate. This includes rank-zero fibers. In base dimension zero
  there are no nonzero covectors, so the condition is vacuous; neither
  compactness nor a positive dimension assumption is needed. -/
  intro x ξ hξ
  rw [C.diracOperator_principalSymbol cov hcov hcomplex]
  let a : ℂ := g.inner x ξ ξ
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (g.pos x ξ hξ))
  let A : Module.End ℂ (E x) := Complex.I • C.clifford x ξ
  -- The factor +i changes the negative Clifford square into the positive metric square.
  have hsquare (v : E x) : A (A v) = a • v := by
    dsimp only [A, a]
    simp only [LinearMap.smul_apply, map_smul, C.clifford_sq, smul_smul,
      ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, neg_neg]
  let B : E x → E x := fun v ↦ a⁻¹ • A v
  have hleft : Function.LeftInverse B A := by
    intro v
    change a⁻¹ • A (A v) = v
    rw [hsquare, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hright : Function.RightInverse B A := by
    intro v
    change A (a⁻¹ • A v) = v
    rw [map_smul, hsquare, smul_smul, inv_mul_cancel₀ ha, one_smul]
  -- Both inverse identities act on the original fiber, including a zero-dimensional fiber.
  exact ⟨hleft.injective, hright.surjective⟩

end SmoothCliffordModule

end AtiyahSinger
