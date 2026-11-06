/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianRealization
public import AtiyahSinger.Analysis.PseudodifferentialLocalRegularity
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Actual spectral powers of one plus the specified connection Laplacian

Public module ID: M0394.

Write B for the bounded positive inverse of the original closed realization of
1+Delta. At nonpositive order l, the spectral power is B^(-l/2) on the full metric
L2 space. At positive order it is the partial inverse of B^(l/2), with the actual
range of that bounded map as its domain. Only nonnegative powers of B enter CFC.

B is injective and densely ranged, although zero may belong to its spectrum.
Nonnegative bounded powers of B are proved positive, injective and densely ranged;
their genuine partial inverses give densely defined self-adjoint spectral operators.
Integer elliptic regularity and spectral commutation identify the smooth-section
image and prove its invariance. The same spectral graph then determines a unique
smooth linear equivalence, whose inverse is the opposite smooth power.

Sources: SG III.13, p.247, for positive connection-Laplacian powers; TA XII.1.3
and pp.298--299 for positive square-root and functional-calculus arguments. The
bounded-inverse construction and comparisons with the project's Sobolev spaces
are supplements. Real-order PDO recognition is given by subsequent results.
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

local notation "H" => h.L2SectionSpace μ
local notation "B" => connectionLaplacianInverse μ g h cov hcov hcomplex

/-- The actual spectral power, defined by nonnegative bounded powers and their partial inverses. -/
def connectionLaplacianSpectralPower (l : ℝ) : H →ₗ.[ℂ] H :=
  if l ≤ 0 then
    (CFC.rpow B (-l / 2)).toLinearMap.toPMap ⊤
  else
    ((CFC.rpow B (l / 2)).toLinearMap.toPMap ⊤).inverse

/-- Nonnegative bounded powers of the same resolvent stay positive, injective and densely ranged. -/
theorem connectionLaplacianInverse_rpow_properties (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ CFC.rpow B t ∧
      Function.Injective ((CFC.rpow B t : H →L[ℂ] H) : H → H) ∧
        DenseRange ((CFC.rpow B t : H →L[ℂ] H) : H → H) := by
  obtain ⟨hB, hBinj, _, _, _, _⟩ :=
    connectionLaplacianInverse_properties μ g h cov hcov hcomplex
  have hpositive : 0 ≤ CFC.rpow B t := CFC.rpow_nonneg
  have hinj : Function.Injective ((CFC.rpow B t : H →L[ℂ] H) : H → H) := by
    rcases eq_or_lt_of_le ht with ht0 | htpos
    · have hz : CFC.rpow B 0 = (1 : H →L[ℂ] H) := CFC.rpow_zero B hB
      rw [← ht0, hz]
      exact Function.injective_id
    · obtain ⟨N, hN⟩ := exists_nat_gt t
      let a : NNReal := ⟨t, ht⟩
      let b : NNReal := ⟨(N : ℝ) - t, by linarith⟩
      have ha : 0 < a := htpos
      have hb : 0 < b := sub_pos.mpr hN
      have hab : ((b + a : NNReal) : ℝ) = (N : ℝ) := by
        change (N : ℝ) - t + t = N
        ring
      -- Positive exponent addition is valid at zero; no bounded inverse for B is used.
      have hpow : CFC.rpow B (N : ℝ) = CFC.rpow B ((N : ℝ) - t) * CFC.rpow B t := by
        have hba : CFC.nnrpow B (b + a) = CFC.nnrpow B b * CFC.nnrpow B a :=
          CFC.nnrpow_add hb ha
        have hb' : CFC.nnrpow B b = CFC.rpow B (b : ℝ) := CFC.nnrpow_eq_rpow hb
        have ha' : CFC.nnrpow B a = CFC.rpow B (a : ℝ) := CFC.nnrpow_eq_rpow ha
        have hab' : CFC.nnrpow B (b + a) = CFC.rpow B ((b + a : NNReal) : ℝ) :=
          CFC.nnrpow_eq_rpow (add_pos hb ha)
        rw [hab', hab, hb', ha'] at hba
        exact hba
      have hNinj (k : ℕ) : Function.Injective ((B ^ k : H →L[ℂ] H) : H → H) := by
        induction k with
        | zero => exact Function.injective_id
        | succ k hk =>
          intro x y hxy
          rw [pow_succ'] at hxy
          change B ((B ^ k) x) = B ((B ^ k) y) at hxy
          exact hk (hBinj hxy)
      intro x y hxy
      apply hNinj N
      have hnat : CFC.rpow B (N : ℝ) = B ^ N := CFC.rpow_natCast B N hB
      rw [← hnat, hpow]
      change CFC.rpow B ((N : ℝ) - t) (CFC.rpow B t x) =
        CFC.rpow B ((N : ℝ) - t) (CFC.rpow B t y)
      rw [hxy]
  -- For a bounded self-adjoint map, the orthogonal range complement is its zero kernel.
  have hself : IsSelfAdjoint (CFC.rpow B t) :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hpositive).isSelfAdjoint
  refine ⟨hpositive, hinj, ?_⟩
  change Dense ((CFC.rpow B t).range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [Submodule.topologicalClosure_eq_top_iff, ContinuousLinearMap.orthogonal_range]
  rw [← ContinuousLinearMap.star_eq_adjoint, hself]
  exact LinearMap.ker_eq_bot.mpr hinj

/-- Each actual spectral power is a densely defined self-adjoint operator on the original L2. -/
theorem connectionLaplacianSpectralPower_isSelfAdjoint (l : ℝ) :
    IsSelfAdjoint (connectionLaplacianSpectralPower μ g h cov hcov hcomplex l) := by
  unfold connectionLaplacianSpectralPower
  split_ifs with hl
  · have hpos := (connectionLaplacianInverse_rpow_properties
      μ g h cov hcov hcomplex (-l / 2) (by linarith)).1
    have hself : IsSelfAdjoint (CFC.rpow B (-l / 2)) :=
      (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).isSelfAdjoint
    apply LinearPMap.isSelfAdjoint_def.mpr
    have hadj := ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense
      (CFC.rpow B (-l / 2)) (p := ⊤) (by exact dense_univ)
    have heq : (CFC.rpow B (-l / 2)).adjoint = CFC.rpow B (-l / 2) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, hself]
    exact hadj.trans (congrArg (fun Q : H →L[ℂ] H ↦ Q.toLinearMap.toPMap ⊤) heq)
  · obtain ⟨hpos, hinj, hdenseQ⟩ := connectionLaplacianInverse_rpow_properties
      μ g h cov hcov hcomplex (l / 2) (by linarith)
    let Q := CFC.rpow B (l / 2)
    let A := Q.toLinearMap.toPMap ⊤
    let T := A.inverse
    have hker : A.ker = ⊥ := by
      apply LinearPMap.ker_eq_bot'.mpr
      intro x hx
      apply Subtype.ext
      apply hinj
      change Q x.val = Q (0 : H)
      rw [map_zero]
      exact hx
    -- The flipped graph retains the actual range as its domain.
    have hgraph (x y : H) : (x, y) ∈ T.graph ↔ Q y = x := by
      rw [A.inverse_graph hker, Submodule.map_equiv_eq_comap_symm]
      change (y, x) ∈ A.graph ↔ Q y = x
      simp only [LinearPMap.mem_graph_iff]
      constructor
      · rintro ⟨z, hz, hQz⟩
        change Q z.val = x at hQz
        rwa [hz] at hQz
      · intro hxy
        exact ⟨⟨y, Submodule.mem_top⟩, rfl, hxy⟩
    have hrange : A.toFun.range = Q.range := by
      ext y
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x.val, hx⟩
      · rintro ⟨x, hx⟩
        exact ⟨⟨x, Submodule.mem_top⟩, hx⟩
    have hdense : Dense (T.domain : Set H) := by
      change Dense (A.inverse.domain : Set H)
      rw [A.inverse_domain, hrange]
      exact hdenseQ
    have hformal : T.IsFormalAdjoint T := by
      intro x y
      have hx := (hgraph x.val (T x)).mp (T.mem_graph x)
      have hy := (hgraph y.val (T y)).mp (T.mem_graph y)
      rw [← hx, ← hy]
      exact ((ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).isSymmetric (T x) (T y)).symm
    have honto : Function.Surjective T := by
      intro y
      obtain ⟨x, _, hx⟩ := T.mem_graph_iff.mp ((hgraph (Q y) y).mpr rfl)
      exact ⟨x, hx⟩
    -- A densely defined symmetric onto operator coincides with its Hilbert adjoint.
    apply LinearPMap.isSelfAdjoint_def.mpr
    apply le_antisymm
    · apply LinearPMap.le_of_le_graph
      intro z hz
      obtain ⟨y, rfl⟩ := T.adjoint.mem_graph_iff'.mp hz
      obtain ⟨x, hx⟩ := honto (T.adjoint y)
      have hxy : (y : H) = x := by
        apply ext_inner_right ℂ
        intro w
        obtain ⟨u, rfl⟩ := honto w
        calc
          inner ℂ (y : H) (T u) = inner ℂ (T.adjoint y) (u : H) :=
            (LinearPMap.adjoint_isFormalAdjoint hdense y u).symm
          _ = inner ℂ (T x) (u : H) := by rw [hx]
          _ = inner ℂ (x : H) (T u) := hformal x u
      exact T.mem_graph_iff.mpr ⟨x, hxy.symm, hx⟩
    · exact hformal.le_adjoint hdense

/-- The exact positive smooth action has the same elliptic principal class as the Laplacian. -/
theorem exists_connectionLaplacianPositivePDO :
    ∃ P : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ (2 : ℝ),
      P.toLinearMap = LinearMap.id +
        (connectionLaplacian μ g h cov hcov hcomplex).toLinearMap ∧ P.IsElliptic := by
  let D := connectionLaplacian μ g h cov hcov hcomplex
  let P := D.toPseudodifferentialOperator μ
  let I : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ (2 : ℝ) :=
    { toLinearMap := LinearMap.id
      isPseudodifferentialOperator :=
        IsPseudodifferentialOperator.mono (by norm_num : (0 : ℝ) ≤ 2)
          LinearMap.id (isPseudodifferentialOperator_id μ) }
  -- The identity contributes only order zero and therefore vanishes in the order-two class.
  have hI : I.principalSymbol = 0 := by
    apply I.principalSymbol_eq_zero_iff.mpr
    exact IsPseudodifferentialOperator.mono (by norm_num : (0 : ℝ) ≤ 2 - 1)
      LinearMap.id (isPseudodifferentialOperator_id μ)
  have hclass : (I.add P).principalSymbol = P.principalSymbol := by
    rw [I.principalSymbol_add, hI, zero_add]
  obtain ⟨R⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := r) (E := E) (F := E)
  let a := R.regularizedSymbol (2 : ℝ) D.principalSymbolFunction
    D.isSmoothOffZeroGlobalSymbol_principalSymbolFunction
    D.isHomogeneousGlobalSymbol_principalSymbolFunction
  have hPa : P.principalSymbol = globalPrincipalSymbolClass E E (2 : ℝ) a :=
    D.principalSymbol_eq_regularizedSymbol μ R
  have hD := connectionLaplacian_isElliptic μ g h cov hcov hcomplex
  have hPel : P.IsElliptic := by
    apply (P.isElliptic_iff_of_principalSymbol_eq a hPa).mpr
    exact (isEllipticFullGlobalSymbol_regularizedSymbol_iff R (2 : ℝ)
      D.principalSymbolFunction D.isSmoothOffZeroGlobalSymbol_principalSymbolFunction
      D.isHomogeneousGlobalSymbol_principalSymbolFunction).mpr
        (D.isElliptic_iff_isEllipticGlobalSymbol.mp hD)
  exact ⟨I.add P, rfl, ((I.add P).isElliptic_iff_of_principalSymbol_eq_operator P hclass).mpr hPel⟩

/-- The exact resolvent sends each smooth input to a unique actual smooth section. -/
theorem existsUnique_smooth_lift_connectionLaplacianInverse
    (u : smoothSections (n := n) (r := r) E) :
    ∃! v : smoothSections (n := n) (r := r) E,
      h.smoothToL2 μ v = B (h.smoothToL2 μ u) := by
  obtain ⟨P, hP, hPel⟩ := exists_connectionLaplacianPositivePDO μ g h cov hcov hcomplex
  obtain ⟨S⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨V, hV, _⟩ := existsUnique_connectionLaplacianSobolevEquiv μ g h cov hcov hcomplex S
  have he : ∃ e : S.SobolevSpace ((2 : ℝ) - 2) ≃L[ℂ] H,
      ∀ w : smoothSections (n := n) (r := r) E,
        e (S.smoothToSobolev ((2 : ℝ) - 2) w) = h.smoothToL2 μ w := by
    rw [sub_self]
    exact ⟨h.sobolevZeroEquivL2 (μ := μ) S, h.sobolevZeroEquivL2_smooth S⟩
  obtain ⟨e, he⟩ := he
  have hPV : e.toContinuousLinearMap.comp (P.sobolevExtension S S 2) =
      V.toContinuousLinearMap := by
    apply DFunLike.coe_injective
    apply (S.denseRange_smoothToSobolev 2).equalizer (by fun_prop) V.continuous
    funext w
    change e (P.sobolevExtension S S 2 (S.smoothToSobolev 2 w)) = V (S.smoothToSobolev 2 w)
    rw [P.sobolevExtension_smoothToSobolev, he, hV, hP]
    rfl
  have hu : P.sobolevExtension S S 2 (V.symm (h.smoothToL2 μ u)) =
      S.smoothToSobolev ((2 : ℝ) - 2) u := by
    apply e.injective
    rw [he]
    change (e.toContinuousLinearMap.comp (P.sobolevExtension S S 2))
      (V.symm (h.smoothToL2 μ u)) = _
    rw [hPV]
    exact V.apply_symm_apply _
  -- Smooth elliptic regularity applies to this same already-existing H² solution.
  obtain ⟨v, ⟨hv, _⟩, _⟩ := P.existsUnique_smooth_lift_of_isElliptic S S hPel 2
    (V.symm (h.smoothToL2 μ u)) u hu
  have hgraph := connectionLaplacianRealization_graph_equiv μ g h cov hcov hcomplex S V hV
  have hvB : h.smoothToL2 μ v = B (h.smoothToL2 μ u) := by
    apply Eq.symm
    apply (connectionLaplacianInverse_graph μ g h cov hcov hcomplex _ _).mp
    rw [hgraph]
    refine ⟨S.smoothToSobolev 2 v, ?_⟩
    apply Prod.ext
    · change h.sobolevZeroEquivL2 (μ := μ) S
        (S.sobolevInclusion 2 0 (by norm_num) (S.smoothToSobolev 2 v)) = _
      rw [S.sobolevInclusion_smoothToSobolev, h.sobolevZeroEquivL2_smooth]
    · change V (S.smoothToSobolev 2 v) = h.smoothToL2 μ u
      rw [hv, V.apply_symm_apply]
  refine ⟨v, hvB, ?_⟩
  intro w hw
  exact h.smoothToL2_injective μ (hw.trans hvB.symm)

set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the smooth-section resolvent ranges and actual spectral graph.
/-- Smooth sections are exactly the vectors in every integer resolvent range. -/
theorem mem_range_smoothToL2_iff_forall_mem_range_pow_connectionLaplacianInverse (x : H) :
    x ∈ Set.range (h.smoothToL2 μ) ↔ ∀ k : ℕ, x ∈ Set.range (B ^ k : H →L[ℂ] H) := by
  obtain ⟨P, hP, hPel⟩ := exists_connectionLaplacianPositivePDO μ g h cov hcov hcomplex
  obtain ⟨S⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨V, hV, _⟩ := existsUnique_connectionLaplacianSobolevEquiv μ g h cov hcov hcomplex S
  let e := h.sobolevZeroEquivL2 (μ := μ) S
  let J := e.toContinuousLinearMap.comp (S.sobolevInclusion 2 0 (by norm_num))
  have hgraph := connectionLaplacianRealization_graph_equiv μ g h cov hcov hcomplex S V hV
  have hsol (u : smoothSections (n := n) (r := r) E) :
      B (h.smoothToL2 μ (P.toLinearMap u)) = h.smoothToL2 μ u := by
    apply (connectionLaplacianInverse_graph μ g h cov hcov hcomplex _ _).mp
    rw [hgraph]
    refine ⟨S.smoothToSobolev 2 u, ?_⟩
    apply Prod.ext
    · change e (S.sobolevInclusion 2 0 (by norm_num) (S.smoothToSobolev 2 u)) = _
      rw [S.sobolevInclusion_smoothToSobolev, h.sobolevZeroEquivL2_smooth]
    · change V (S.smoothToSobolev 2 u) = h.smoothToL2 μ (P.toLinearMap u)
      rw [hV, hP]
      rfl
  constructor
  · rintro ⟨u, rfl⟩ k
    -- Repeated application of the same smooth positive operator supplies each preimage.
    induction k generalizing u with
    | zero => exact ⟨h.smoothToL2 μ u, rfl⟩
    | succ k hk =>
      obtain ⟨y, hy⟩ := hk (P.toLinearMap u)
      refine ⟨y, ?_⟩
      rw [pow_succ']
      change B ((B ^ k) y) = h.smoothToL2 μ u
      rw [hy, hsol]
  · intro hx
    let L := e.symm.toContinuousLinearMap.comp ((B).comp e.toContinuousLinearMap)
    have hLe (z : S.SobolevSpace 0) : e (L z) = B (e z) := e.apply_symm_apply _
    have hLpow (k : ℕ) (z : S.SobolevSpace 0) : e ((L ^ k) z) = (B ^ k) (e z) := by
      induction k with
      | zero => rfl
      | succ k hk =>
        rw [pow_succ', pow_succ']
        change e (L ((L ^ k) z)) = B ((B ^ k) (e z))
        rw [hLe, hk]
    -- The inverse equation holds as a bounded map H⁰ → H⁻², by smooth density.
    have hPL : (P.sobolevExtension S S 0).comp L =
        S.sobolevInclusion 0 (0 - 2) (by norm_num) := by
      apply DFunLike.coe_injective
      apply (S.denseRange_smoothToSobolev 0).equalizer (by fun_prop) (by fun_prop)
      funext u
      obtain ⟨v, hv, _⟩ := existsUnique_smooth_lift_connectionLaplacianInverse
        μ g h cov hcov hcomplex u
      have hLv : L (S.smoothToSobolev 0 u) = S.smoothToSobolev 0 v := by
        apply e.injective
        rw [hLe, h.sobolevZeroEquivL2_smooth, h.sobolevZeroEquivL2_smooth]
        exact hv.symm
      have hPv : P.toLinearMap v = u := by
        apply h.smoothToL2_injective μ
        apply (connectionLaplacianInverse_properties μ g h cov hcov hcomplex).2.1
        exact (hsol v).trans hv
      change P.sobolevExtension S S 0 (L (S.smoothToSobolev 0 u)) =
        S.sobolevInclusion 0 (0 - 2) (by norm_num) (S.smoothToSobolev 0 u)
      rw [hLv, P.sobolevExtension_smoothToSobolev, hPv,
        S.sobolevInclusion_smoothToSobolev]
    -- Each inverse step gains two local Sobolev orders on the unchanged H⁰ vector.
    have hregular (k : ℕ) (z : S.SobolevSpace 0) :
        S.MemSobolevOn 0 ((L ^ k) z) (2 * (k : ℝ)) Set.univ := by
      induction k with
      | zero => simpa using S.memSobolevOn_self 0 z Set.univ
      | succ k hk =>
        have hright : S.MemSobolevOn (0 - 2)
            (P.sobolevExtension S S 0 ((L ^ (k + 1)) z)) (2 * (k : ℝ)) Set.univ := by
          have heq := DFunLike.congr_fun hPL ((L ^ k) z)
          change P.sobolevExtension S S 0 (L ((L ^ k) z)) = _ at heq
          rw [pow_succ']
          change S.MemSobolevOn (0 - 2)
            (P.sobolevExtension S S 0 (L ((L ^ k) z))) (2 * (k : ℝ)) Set.univ
          rw [heq]
          exact (S.memSobolevOn_sobolevInclusion_iff 0 (0 - 2) (2 * (k : ℝ))
            (by norm_num) ((L ^ k) z) Set.univ).mpr hk
        have hout := P.memSobolevOn_of_isElliptic S S hPel 0 (2 * (k : ℝ))
          ((L ^ (k + 1)) z) Set.univ isOpen_univ hright
        simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_one] using hout
    have hall : S.IsSmoothOn 0 (e.symm x) Set.univ := by
      apply (S.isSmoothOn_iff_forall_memSobolevOn 0 (e.symm x) Set.univ isOpen_univ).mpr
      intro t
      obtain ⟨k, hk⟩ := exists_nat_gt t
      obtain ⟨y, hy⟩ := hx k
      have heq : (L ^ k) (e.symm y) = e.symm x := by
        apply e.injective
        rw [hLpow, e.apply_symm_apply, e.apply_symm_apply]
        exact hy
      have hr := hregular k (e.symm y)
      rw [heq] at hr
      exact S.memSobolevOn_of_le 0 (2 * (k : ℝ)) t (e.symm x) Set.univ hr
        (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
    obtain ⟨u, hu, _⟩ := (S.isSmoothOn_univ_iff_exists_smooth_lift 0 (e.symm x)).mp hall
    refine ⟨u, ?_⟩
    rw [← h.sobolevZeroEquivL2_smooth S u, hu]
    exact e.apply_symm_apply x

set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the smooth-section resolvent ranges and actual spectral graph.
/-- The spectral graph has a unique invertible action on the original smooth sections. -/
theorem existsUnique_connectionLaplacianSmoothPower (l : ℝ) :
    ∃! U : smoothSections (n := n) (r := r) E ≃ₗ[ℂ]
        smoothSections (n := n) (r := r) E,
      ∀ u : smoothSections (n := n) (r := r) E,
        (h.smoothToL2 μ u, h.smoothToL2 μ (U u)) ∈
          (connectionLaplacianSpectralPower μ g h cov hcov hcomplex l).graph := by
  let f := h.smoothToL2 μ
  have hf : Function.Injective f := h.smoothToL2_injective μ
  have hB := (connectionLaplacianInverse_properties μ g h cov hcov hcomplex).1
  have hW (x : H) : x ∈ Set.range f ↔
      ∀ k : ℕ, x ∈ Set.range (B ^ k : H →L[ℂ] H) :=
    mem_range_smoothToL2_iff_forall_mem_range_pow_connectionLaplacianInverse
      μ g h cov hcov hcomplex x
  -- All bounded nonnegative powers preserve every integer resolvent range.
  have hinvariant (t : ℝ) (x : H) (hx : x ∈ Set.range f) :
      CFC.rpow B t x ∈ Set.range f := by
    apply (hW _).mpr
    intro k
    obtain ⟨y, hy⟩ := (hW x).mp hx k
    refine ⟨CFC.rpow B t y, ?_⟩
    have hcomm : Commute (CFC.rpow B t) B := by
      conv_rhs => rw [← CFC.rpow_one B hB]
      exact cfc_commute_cfc (fun x : NNReal ↦ x ^ t) (fun x : NNReal ↦ x ^ (1 : ℝ)) B
    have hcommk := congrArg (fun T : H →L[ℂ] H ↦ T y) (hcomm.pow_right k).eq
    change CFC.rpow B t ((B ^ k) y) = (B ^ k) (CFC.rpow B t y) at hcommk
    rw [← hy]
    exact hcommk.symm
  -- A preimage under an integer power is smooth: use all higher ranges and injectivity.
  have hpreimage (N : ℕ) (x z : H) (hx : x ∈ Set.range f) (hz : (B ^ N) z = x) :
      z ∈ Set.range f := by
    have hNinj : Function.Injective ((B ^ N : H →L[ℂ] H) : H → H) := by
      rw [← CFC.rpow_natCast B N hB]
      exact (connectionLaplacianInverse_rpow_properties μ g h cov hcov hcomplex
        N (Nat.cast_nonneg N)).2.1
    apply (hW z).mpr
    intro k
    obtain ⟨w, hw⟩ := (hW x).mp hx (N + k)
    refine ⟨w, hNinj ?_⟩
    rw [hz]
    change ((B ^ N * B ^ k : H →L[ℂ] H) w) = x
    rw [← pow_add]
    exact hw
  have hbounded (t : ℝ) (ht : 0 ≤ t) :
      ∃ U : smoothSections (n := n) (r := r) E ≃ₗ[ℂ]
          smoothSections (n := n) (r := r) E,
        ∀ u, f (U u) = CFC.rpow B t (f u) := by
    let Q := CFC.rpow B t
    let e := LinearEquiv.ofInjective f hf
    let R := Q.toLinearMap.comp f
    have hR (u : smoothSections (n := n) (r := r) E) : R u ∈ f.range :=
      hinvariant t (f u) ⟨u, rfl⟩
    let U := e.symm.toLinearMap.comp (R.codRestrict f.range hR)
    have hU (u : smoothSections (n := n) (r := r) E) : f (U u) = Q (f u) :=
      congrArg Subtype.val (e.apply_symm_apply ⟨R u, hR u⟩)
    have hUinj : Function.Injective U := by
      intro u v huv
      apply hf
      apply (connectionLaplacianInverse_rpow_properties μ g h cov hcov hcomplex t ht).2.1
      rw [← hU, ← hU, huv]
    have hUsurj : Function.Surjective U := by
      intro u
      rcases eq_or_lt_of_le ht with ht0 | htpos
      · refine ⟨u, hf ?_⟩
        rw [hU]
        change CFC.rpow B t (f u) = f u
        have hz : CFC.rpow B 0 = (1 : H →L[ℂ] H) := CFC.rpow_zero B hB
        rw [← ht0, hz]
        rfl
      · obtain ⟨N, hN⟩ := exists_nat_gt t
        obtain ⟨z, hz⟩ := (hW (f u)).mp ⟨u, rfl⟩ N
        have hzsmooth := hpreimage N (f u) z ⟨u, rfl⟩ hz
        obtain ⟨v, hv⟩ := hinvariant ((N : ℝ) - t) z hzsmooth
        refine ⟨v, hf ?_⟩
        rw [hU, hv]
        let a : NNReal := ⟨t, ht⟩
        let b : NNReal := ⟨(N : ℝ) - t, (sub_pos.mpr hN).le⟩
        have ha : 0 < a := htpos
        have hb : 0 < b := sub_pos.mpr hN
        have hab : ((a + b : NNReal) : ℝ) = (N : ℝ) := by
          change t + ((N : ℝ) - t) = N
          ring
        have hpow : CFC.rpow B t * CFC.rpow B ((N : ℝ) - t) = B ^ N := by
          have heq : CFC.nnrpow B (a + b) = CFC.nnrpow B a * CFC.nnrpow B b :=
            CFC.nnrpow_add ha hb
          have ha' : CFC.nnrpow B a = CFC.rpow B (a : ℝ) := CFC.nnrpow_eq_rpow ha
          have hb' : CFC.nnrpow B b = CFC.rpow B (b : ℝ) := CFC.nnrpow_eq_rpow hb
          have hab' : CFC.nnrpow B (a + b) = CFC.rpow B ((a + b : NNReal) : ℝ) :=
            CFC.nnrpow_eq_rpow (add_pos ha hb)
          have hnat : CFC.rpow B (N : ℝ) = B ^ N := CFC.rpow_natCast B N hB
          rw [hab', hab, ha', hb', hnat] at heq
          exact heq.symm
        change (CFC.rpow B t * CFC.rpow B ((N : ℝ) - t)) z = f u
        rw [hpow]
        exact hz
    exact ⟨LinearEquiv.ofBijective U ⟨hUinj, hUsurj⟩, hU⟩
  -- Nonpositive order is the bounded power; positive order uses its genuine inverse graph.
  have hex : ∃ U : smoothSections (n := n) (r := r) E ≃ₗ[ℂ]
        smoothSections (n := n) (r := r) E,
      ∀ u, (f u, f (U u)) ∈
        (connectionLaplacianSpectralPower μ g h cov hcov hcomplex l).graph := by
    by_cases hl : l ≤ 0
    · obtain ⟨U, hU⟩ := hbounded (-l / 2) (by linarith)
      refine ⟨U, ?_⟩
      intro u
      rw [connectionLaplacianSpectralPower, ite_eq_left hl]
      apply (LinearPMap.mem_graph_iff _).mpr
      exact ⟨⟨f u, Submodule.mem_top⟩, rfl, (hU u).symm⟩
    · obtain ⟨U, hU⟩ := hbounded (l / 2) (by linarith)
      let Q := CFC.rpow B (l / 2)
      let A := Q.toLinearMap.toPMap ⊤
      have hker : A.ker = ⊥ := by
        apply LinearPMap.ker_eq_bot'.mpr
        intro x hx
        apply Subtype.ext
        apply (connectionLaplacianInverse_rpow_properties
          μ g h cov hcov hcomplex (l / 2) (by linarith)).2.1
        change Q x.val = Q (0 : H)
        rw [map_zero]
        exact hx
      refine ⟨U.symm, ?_⟩
      intro u
      rw [connectionLaplacianSpectralPower, ite_eq_right hl]
      have hgu := A.mem_inverse_graph hker ⟨f (U.symm u), Submodule.mem_top⟩
      have heq : Q (f (U.symm u)) = f u := by
        rw [← hU, U.apply_symm_apply]
      change (Q (f (U.symm u)), f (U.symm u)) ∈ A.inverse.graph at hgu
      rwa [heq] at hgu
  obtain ⟨U, hU⟩ := hex
  refine ⟨U, hU, ?_⟩
  intro V hV
  apply DFunLike.coe_injective
  funext u
  apply hf
  exact (connectionLaplacianSpectralPower μ g h cov hcov hcomplex l).mem_graph_snd_inj
    (hV u) (hU u) rfl

/-- The smooth action selected from the unique graph of the actual spectral power. -/
def connectionLaplacianSmoothPower (l : ℝ) :
    smoothSections (n := n) (r := r) E ≃ₗ[ℂ] smoothSections (n := n) (r := r) E :=
  (existsUnique_connectionLaplacianSmoothPower μ g h cov hcov hcomplex l).exists.choose

/-- The selected smooth equivalence acts by the same partially defined spectral operator. -/
theorem connectionLaplacianSmoothPower_graph (l : ℝ)
    (u : smoothSections (n := n) (r := r) E) :
    (h.smoothToL2 μ u,
      h.smoothToL2 μ (connectionLaplacianSmoothPower μ g h cov hcov hcomplex l u)) ∈
      (connectionLaplacianSpectralPower μ g h cov hcov hcomplex l).graph := by
  -- The chosen equivalence retains the actual graph, including domain membership.
  exact (existsUnique_connectionLaplacianSmoothPower
    μ g h cov hcov hcomplex l).exists.choose_spec u

/-- The opposite spectral power is exactly the inverse of the same smooth equivalence. -/
theorem connectionLaplacianSmoothPower_neg (l : ℝ) :
    connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-l) =
      (connectionLaplacianSmoothPower μ g h cov hcov hcomplex l).symm := by
  let f := h.smoothToL2 μ
  -- Nonnegative powers are injective, so their partial inverses have the flipped graph.
  have hflip (t : ℝ) (ht : 0 ≤ t) (x y : H) :
      (x, y) ∈ ((CFC.rpow B t).toLinearMap.toPMap ⊤).inverse.graph ↔
        (y, x) ∈ ((CFC.rpow B t).toLinearMap.toPMap ⊤).graph := by
    let Q := CFC.rpow B t
    let A := Q.toLinearMap.toPMap ⊤
    have hker : A.ker = ⊥ := by
      apply LinearPMap.ker_eq_bot'.mpr
      intro z hz
      apply Subtype.ext
      apply (connectionLaplacianInverse_rpow_properties μ g h cov hcov hcomplex t ht).2.1
      change Q z.val = Q (0 : H)
      rw [map_zero]
      exact hz
    rw [A.inverse_graph hker, Submodule.map_equiv_eq_comap_symm]
    rfl
  have hreciprocal (x y : H) :
      (x, y) ∈ (connectionLaplacianSpectralPower μ g h cov hcov hcomplex (-l)).graph ↔
        (y, x) ∈ (connectionLaplacianSpectralPower μ g h cov hcov hcomplex l).graph := by
    rcases lt_trichotomy l 0 with hl | rfl | hl
    · rw [connectionLaplacianSpectralPower, connectionLaplacianSpectralPower,
        ite_eq_right (by linarith : ¬ -l ≤ 0), ite_eq_left hl.le]
      exact hflip (-l / 2) (by linarith) x y
    · have hB := (connectionLaplacianInverse_properties μ g h cov hcov hcomplex).1
      have hzero : CFC.rpow B 0 = (1 : H →L[ℂ] H) := CFC.rpow_zero B hB
      simp only [connectionLaplacianSpectralPower, neg_zero, zero_div, le_refl,
        hzero]
      simp [LinearPMap.mem_graph_iff, eq_comm]
    · rw [connectionLaplacianSpectralPower, connectionLaplacianSpectralPower,
        ite_eq_left (by linarith : -l ≤ 0), ite_eq_right (not_le.mpr hl), neg_neg]
      exact (hflip (l / 2) (by linarith) y x).symm
  -- The inverse of the selected l action lies in precisely the opposite spectral graph.
  let U := connectionLaplacianSmoothPower μ g h cov hcov hcomplex l
  have hU (u : smoothSections (n := n) (r := r) E) :
      (f u, f (U.symm u)) ∈
        (connectionLaplacianSpectralPower μ g h cov hcov hcomplex (-l)).graph := by
    apply (hreciprocal _ _).mpr
    have hgu := connectionLaplacianSmoothPower_graph μ g h cov hcov hcomplex l (U.symm u)
    change (f (U.symm u), f (U (U.symm u))) ∈ _ at hgu
    simpa only [U.apply_symm_apply] using hgu
  exact (existsUnique_connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-l)).unique
    (connectionLaplacianSmoothPower_graph μ g h cov hcov hcomplex (-l)) hU

end AtiyahSinger
