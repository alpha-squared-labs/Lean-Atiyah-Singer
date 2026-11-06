/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EllipticIndex
public import AtiyahSinger.Analysis.HermitianMetricL2Realization
public import AtiyahSinger.Analysis.SobolevInclusionTransport
public import AtiyahSinger.Geometry.ConnectionLaplacian
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The positive closed connection Laplacian and its bounded inverse

Public module ID: M0396.

A09: start with the actual smooth action of `1 + connectionLaplacian`, on the
original integral L² completion. Its graph closure is self-adjoint, has precisely
the H² graph, and has a unique bounded positive inverse on that same L² space.
The inverse is compact and injective with dense range; no bounded invertibility
or positive spectral lower bound is asserted for the inverse itself.

Sources: SG III.5.2, III.5.5 and III.5.7 for elliptic regularity and the
self-adjoint elliptic inverse, and III.13, p.247, for positive Laplacian powers.
SG's self-adjointness there is formal adjunction on smooth sections; the
unbounded closed-graph self-adjointness, exact H² graph and completion
comparisons are project supplements. SG chooses a unitary connection and
Riemannian volume; the same energy argument works for any smooth complex
connection and smooth positive density, since the formal adjoint is taken
for those exact data.
The actual smooth core is closable; its closure is self-adjoint and its bounded
inverse is positive and compact. Its graph is identified both through the positive
H² equivalence and through the original transported Sobolev extension.
Each data definition retains the given connection, Hermitian metric, cotangent
metric, density and section map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

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
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  (g : SmoothCotangentMetric (n := n) (M := M))
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℂ (Fin r)) E)
  (hcov : cov.ContMDiffCovariantDerivative ∞)
  (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E cov)

include hM hT2 hSC hC hBorel hE hμ

/-- The actual smooth `1 + ∇*∇`, defined on its original smooth image in integral L². -/
def connectionLaplacianSmoothCore : h.L2SectionSpace μ →ₗ.[ℂ] h.L2SectionSpace μ where
  domain := (h.smoothToL2 μ).range
  toFun := (h.smoothToL2 μ).comp
    ((LinearMap.id + (connectionLaplacian μ g h cov hcov hcomplex).toLinearMap).comp
      (LinearEquiv.ofInjective (h.smoothToL2 μ)
        (h.smoothToL2_injective μ)).symm.toLinearMap)

/-- Integral symmetry makes the given connection Laplacian smooth core closable. -/
theorem isClosable_connectionLaplacianSmoothCore :
    (connectionLaplacianSmoothCore μ g h cov hcov hcomplex).IsClosable := by
  /- The connection energy identity and Hermitian symmetry give self-adjunction
  of 1 + ∇*∇ on the actual dense smooth L² image. Density makes its Hilbert adjoint
  closed, and formal symmetry includes the original smooth graph in that adjoint
  graph. Restriction to this graph is therefore closable. Self-adjointness of the
  closure is established by the later positive Sobolev graph comparison. -/
  let A := connectionLaplacianSmoothCore μ g h cov hcov hcomplex
  have hA : Dense (A.domain : Set (h.L2SectionSpace μ)) := h.denseRange_smoothToL2 μ
  have hformal : A.IsFormalAdjoint A := by
    intro x y
    let e := LinearEquiv.ofInjective (h.smoothToL2 μ) (h.smoothToL2_injective μ)
    let u := e.symm x
    let v := e.symm y
    have hx : h.smoothToL2 μ u = x.val := congrArg Subtype.val (e.apply_symm_apply x)
    have hy : h.smoothToL2 μ v = y.val := congrArg Subtype.val (e.apply_symm_apply y)
    let P := connectionLaplacian μ g h cov hcov hcomplex
    change inner ℂ (h.smoothToL2 μ (u + P.toLinearMap u)) y.val =
      inner ℂ x.val (h.smoothToL2 μ (v + P.toLinearMap v))
    rw [← hx, ← hy, map_add, map_add, inner_add_left, inner_add_right,
      h.inner_smoothToL2, h.inner_smoothToL2, h.inner_smoothToL2]
    exact congrArg (fun z : ℂ ↦ h.sectionPairing μ u v + z)
      (connectionLaplacian_symmetric μ g h cov hcov hcomplex u v)
  -- The dense symmetric operator is a restriction of its closed Hilbert adjoint.
  exact (LinearPMap.adjoint_isClosed hA).isClosable.leIsClosable
    (hformal.le_adjoint hA)

/-- The unbounded positive operator is the graph closure of the original smooth action. -/
def connectionLaplacianRealization : h.L2SectionSpace μ →ₗ.[ℂ] h.L2SectionSpace μ :=
  (connectionLaplacianSmoothCore μ g h cov hcov hcomplex).closure


set_option linter.auxLemma false in
omit hM hT2 hSC hC hBorel hE hμ in
/-- The original closed inequality used by the H²-to-L² inclusion. -/
theorem connectionLaplacianRealization_graph_sobolev._proof_1 : (0 : ℝ) ≤ 2 := by
  norm_num

set_option linter.auxLemma false in
omit hM hT2 hSC hC hBorel hE hμ in
/-- The original closed equality used by the order-two target transport. -/
theorem connectionLaplacianRealization_graph_sobolev._proof_2 :
    (2 : ℝ) - (2 : ℕ) = 0 := by
  norm_num

set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the elliptic Sobolev isomorphism and actual closed Laplacian
-- graph.
/-- The positive elliptic operator is an isomorphism from the specified H² onto metric L². -/
theorem existsUnique_connectionLaplacianSobolevEquiv
    (S : SmoothBundlePresentation (n := n) (r := r) E) :
    ∃! V : S.SobolevSpace 2 ≃L[ℂ] h.L2SectionSpace μ,
      ∀ u : smoothSections (n := n) (r := r) E,
        V (S.smoothToSobolev 2 u) = h.smoothToL2 μ
          (u + (connectionLaplacian μ g h cov hcov hcomplex).toLinearMap u) := by
  let D := connectionLaplacian μ g h cov hcov hcomplex
  have hD : D.IsElliptic := connectionLaplacian_isElliptic μ g h cov hcov hcomplex
  have he : ∃ e : S.SobolevSpace ((2 : ℝ) - (2 : ℕ)) ≃L[ℂ] h.L2SectionSpace μ,
      ∀ u : smoothSections (n := n) (r := r) E,
        e (S.smoothToSobolev ((2 : ℝ) - (2 : ℕ)) u) = h.smoothToL2 μ u := by
    rw [show (2 : ℝ) - (2 : ℕ) = 0 by norm_num]
    exact ⟨h.sobolevZeroEquivL2 (μ := μ) S, h.sobolevZeroEquivL2_smooth S⟩
  obtain ⟨e, he⟩ := he
  let I := S.sobolevInclusion 2 ((2 : ℝ) - (2 : ℕ)) (by norm_num)
  let J := e.toContinuousLinearMap.comp I
  let T := e.toContinuousLinearMap.comp (D.sobolevExtension S S 2)
  let R := T + J
  have hJ (u : smoothSections (n := n) (r := r) E) :
      J (S.smoothToSobolev 2 u) = h.smoothToL2 μ u := by
    change e (I (S.smoothToSobolev 2 u)) = _
    rw [S.sobolevInclusion_smoothToSobolev, he]
  have hR (u : smoothSections (n := n) (r := r) E) :
      R (S.smoothToSobolev 2 u) = h.smoothToL2 μ (u + D.toLinearMap u) := by
    change e (D.sobolevExtension S S 2 (S.smoothToSobolev 2 u)) +
      J (S.smoothToSobolev 2 u) = _
    rw [D.sobolevExtension_smoothToSobolev, he, hJ, map_add, add_comm]
  -- Compact perturbation preserves the actual critical Fredholm index.
  have hT : T.IsFredholm := e.isFredholm.comp (D.isFredholm_sobolevExtension μ S S hD 2)
  have hJcompact : IsCompactOperator J :=
    (S.isCompactOperator_sobolevInclusion 2 ((2 : ℝ) - (2 : ℕ))
      (by norm_num)).clm_comp e.toContinuousLinearMap
  have hRfred : R.IsFredholm := isFredholm_add_compact T J hT hJcompact
  have hDad : D.metricFormalAdjoint (μ := μ) h h = D :=
    D.metricFormalAdjoint_eq h h D (connectionLaplacian_symmetric μ g h cov hcov hcomplex)
  have hDindex : D.analyticIndex hD = 0 := by
    rw [D.analyticIndex_eq_finrank_ker_sub_finrank_ker_metricFormalAdjoint (μ := μ) h h hD, hDad]
    exact sub_self _
  have heindex : e.toContinuousLinearMap.index = 0 :=
    LinearMap.index_of_bijective e.bijective
  have hRindex : R.index = 0 := by
    rw [index_add_compact T J hT hJcompact,
      e.isFredholm.index_comp (D.isFredholm_sobolevExtension μ S S hD 2),
      heindex,
      D.index_sobolevExtension_eq_analyticIndex μ S S hD 2, hDindex, add_zero]
  -- The original connection energy inequality extends by H² density.
  have henergy (x : S.SobolevSpace 2) :
      ‖J x‖ ^ 2 ≤ (inner ℂ (J x) (R x)).re := by
    have hc : IsClosed {z : S.SobolevSpace 2 |
        ‖J z‖ ^ 2 ≤ (inner ℂ (J z) (R z)).re} :=
      isClosed_le (by fun_prop) (by fun_prop)
    apply hc.closure_subset_iff.mpr ?_ (S.denseRange_smoothToSobolev 2 x)
    rintro _ ⟨u, rfl⟩
    change ‖J (S.smoothToSobolev 2 u)‖ ^ 2 ≤
      (inner ℂ (J (S.smoothToSobolev 2 u)) (R (S.smoothToSobolev 2 u))).re
    rw [hJ, hR, map_add, inner_add_right, Complex.add_re]
    have hself : (inner ℂ (h.smoothToL2 μ u) (h.smoothToL2 μ u)).re =
        ‖h.smoothToL2 μ u‖ ^ 2 := by
      simpa only [RCLike.re_eq_complex_re] using
        (inner_self_eq_norm_sq (𝕜 := ℂ) (h.smoothToL2 μ u))
    rw [hself]
    have hn := connectionLaplacian_nonneg μ g h cov hcov hcomplex u
    rw [← h.inner_smoothToL2] at hn
    exact le_add_of_nonneg_right hn
  have hRinj : Function.Injective R := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hxR : R x = 0 := hx
    have hxbound := henergy x
    rw [hxR, inner_zero_right, Complex.zero_re] at hxbound
    have hxJ : J x = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (J x)])
    have hxi : I x = 0 := e.injective (by
      change J x = e 0
      simpa only [map_zero] using hxJ)
    apply S.sobolevInclusion_injective 2 ((2 : ℝ) - (2 : ℕ)) (by norm_num)
    change I x = I 0
    simpa only [map_zero] using hxi
  -- Finite-dimensional cokernel and index zero upgrade injectivity to surjectivity.
  have hcoker := (isFredholm_iff_closed_range_finite R).mp hRfred
  let : FiniteDimensional ℂ (h.L2SectionSpace μ ⧸ R.range) := hcoker.2.2
  have hdim : Module.finrank ℂ (h.L2SectionSpace μ ⧸ R.range) = 0 := by
    have heq := LinearMap.index_of_injective (f := R.toLinearMap) hRinj
    rw [hRindex] at heq
    omega
  have hRrange : R.range = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp ((Module.finrank_zero_iff).mp hdim)
  let V := ContinuousLinearEquiv.ofBijective R (LinearMap.ker_eq_bot.mpr hRinj) hRrange
  refine ⟨V, hR, ?_⟩
  intro W hW
  apply DFunLike.coe_injective
  apply (S.denseRange_smoothToSobolev 2).equalizer W.continuous V.continuous
  funext u
  exact (hW u).trans (hR u).symm


set_option linter.auxLemma false in
set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the elliptic Sobolev isomorphism and actual closed Laplacian
-- graph.
/-- The closed Laplacian graph is parametrized by its actual positive Sobolev equivalence. -/
theorem connectionLaplacianRealization_graph_equiv
    (S : SmoothBundlePresentation (n := n) (r := r) E)
    (V : S.SobolevSpace 2 ≃L[ℂ] h.L2SectionSpace μ)
    (hV : ∀ u : smoothSections (n := n) (r := r) E,
      V (S.smoothToSobolev 2 u) = h.smoothToL2 μ
        (u + (connectionLaplacian μ g h cov hcov hcomplex).toLinearMap u)) :
    let J := (h.sobolevZeroEquivL2 (μ := μ) S).toContinuousLinearMap.comp
      (S.sobolevInclusion 2 0 connectionLaplacianRealization_graph_sobolev._proof_1)
    (connectionLaplacianRealization μ g h cov hcov hcomplex).graph =
      (J.prod V.toContinuousLinearMap).range := by
  let D := connectionLaplacian μ g h cov hcov hcomplex
  let e := h.sobolevZeroEquivL2 (μ := μ) S
  let I := S.sobolevInclusion 2 0 (by norm_num)
  let J := e.toContinuousLinearMap.comp I
  let G := J.prod V.toContinuousLinearMap
  change (connectionLaplacianRealization μ g h cov hcov hcomplex).graph = G.range
  have hJ (v : smoothSections (n := n) (r := r) E) :
      J (S.smoothToSobolev 2 v) = h.smoothToL2 μ v := by
    change e (I (S.smoothToSobolev 2 v)) = _
    rw [S.sobolevInclusion_smoothToSobolev, h.sobolevZeroEquivL2_smooth]
  -- Its inverse bounds the entire graph map and therefore gives a closed range.
  let K : NNReal := ⟨‖V.symm.toContinuousLinearMap‖, norm_nonneg _⟩
  have hGbound (u : S.SobolevSpace 2) : ‖u‖ ≤ K * ‖G u‖ := by
    have hinv := V.symm.toContinuousLinearMap.le_opNorm (V u)
    change ‖V.symm (V u)‖ ≤
      ‖V.symm.toContinuousLinearMap‖ * ‖V u‖ at hinv
    rw [V.symm_apply_apply] at hinv
    have hRu : ‖V u‖ ≤ ‖G u‖ := norm_snd_le (G u)
    exact hinv.trans (mul_le_mul_of_nonneg_left hRu (norm_nonneg _))
  have hclosed : IsClosed (G.range : Set (h.L2SectionSpace μ × h.L2SectionSpace μ)) :=
    (G.antilipschitz_of_bound hGbound).isClosed_range G.uniformContinuous
  -- Both smooth graph coordinates use the original section and its 1 + Laplacian image.
  let core := connectionLaplacianSmoothCore μ g h cov hcov hcomplex
  let smoothEquiv := LinearEquiv.ofInjective (h.smoothToL2 μ) (h.smoothToL2_injective μ)
  have hcore : core.graph ≤ G.range := by
    intro z hz
    obtain ⟨x, rfl⟩ := core.mem_graph_iff'.mp hz
    let v := smoothEquiv.symm x
    refine ⟨S.smoothToSobolev 2 v, ?_⟩
    apply Prod.ext
    · exact (hJ v).trans (congrArg Subtype.val (smoothEquiv.apply_symm_apply x))
    · exact hV v
  have hsmooth (v : smoothSections (n := n) (r := r) E) :
      G (S.smoothToSobolev 2 v) ∈ core.graph := by
    apply core.mem_graph_iff.mpr
    refine ⟨smoothEquiv v, (hJ v).symm, ?_⟩
    change h.smoothToL2 μ
      (smoothEquiv.symm (smoothEquiv v) + D.toLinearMap (smoothEquiv.symm (smoothEquiv v))) =
        V (S.smoothToSobolev 2 v)
    rw [smoothEquiv.symm_apply_apply, hV]
  change core.closure.graph = G.range
  have hclos := isClosable_connectionLaplacianSmoothCore μ g h cov hcov hcomplex
  rw [hclos.graph_closure_eq_closure_graph.symm]
  apply le_antisymm
  · exact core.graph.topologicalClosure_minimal hcore hclosed
  · rintro z ⟨u, rfl⟩
    -- H² density approximates both graph coordinates simultaneously.
    apply map_mem_closure G.continuous (S.denseRange_smoothToSobolev 2 u)
    rintro _ ⟨v, rfl⟩
    exact hsmooth v


set_option linter.auxLemma false in
/-- Its exact closed graph is the H² realization of the same differential operator. -/
theorem connectionLaplacianRealization_graph_sobolev
    (S : SmoothBundlePresentation (n := n) (r := r) E) :
    let J : S.SobolevSpace 2 →L[ℂ] h.L2SectionSpace μ :=
      (h.sobolevZeroEquivL2 (μ := μ) S).toContinuousLinearMap.comp
        (S.sobolevInclusion 2 0 connectionLaplacianRealization_graph_sobolev._proof_1)
    let T : S.SobolevSpace 2 →L[ℂ] S.SobolevSpace 0 := by
      exact Eq.mp (congrArg (fun s : ℝ ↦ S.SobolevSpace 2 →L[ℂ] S.SobolevSpace s)
        connectionLaplacianRealization_graph_sobolev._proof_2)
        ((connectionLaplacian μ g h cov hcov hcomplex).sobolevExtension S S 2)
    let R : S.SobolevSpace 2 →L[ℂ] h.L2SectionSpace μ :=
      J + (h.sobolevZeroEquivL2 (μ := μ) S).toContinuousLinearMap.comp T
    (connectionLaplacianRealization μ g h cov hcov hcomplex).graph =
      (J.toLinearMap.prod R.toLinearMap).range := by
  /- First identify the fixed-target extension on dense smooth sections with the
  positive elliptic H² equivalence. Its already established graph is closed.
  Finally compare whole bounded maps to the original dependent cast. -/
  let D := connectionLaplacian μ g h cov hcov hcomplex
  let e := h.sobolevZeroEquivL2 (μ := μ) S
  let J : S.SobolevSpace 2 →L[ℂ] h.L2SectionSpace μ :=
    e.toContinuousLinearMap.comp (S.sobolevInclusion 2 0 (by norm_num))
  let T : S.SobolevSpace 2 →L[ℂ] S.SobolevSpace 0 :=
    (S.sobolevInclusion ((2 : ℝ) - (2 : ℕ)) 0 (by norm_num)).comp
      (D.sobolevExtension S S 2)
  let R : S.SobolevSpace 2 →L[ℂ] h.L2SectionSpace μ := J + e.toContinuousLinearMap.comp T
  have hfixed : (connectionLaplacianRealization μ g h cov hcov hcomplex).graph =
      (J.toLinearMap.prod R.toLinearMap).range := by
    obtain ⟨V, hV, _⟩ := existsUnique_connectionLaplacianSobolevEquiv μ g h cov hcov hcomplex S
    have hRV : R = V.toContinuousLinearMap := by
      apply DFunLike.coe_injective
      apply (S.denseRange_smoothToSobolev 2).equalizer R.continuous V.continuous
      funext u
      change e (S.sobolevInclusion 2 0 _ (S.smoothToSobolev 2 u)) +
        e (S.sobolevInclusion ((2 : ℝ) - (2 : ℕ)) 0 _
          (D.sobolevExtension S S 2 (S.smoothToSobolev 2 u))) = V (S.smoothToSobolev 2 u)
      rw [D.sobolevExtension_smoothToSobolev, S.sobolevInclusion_smoothToSobolev,
        S.sobolevInclusion_smoothToSobolev, h.sobolevZeroEquivL2_smooth,
        h.sobolevZeroEquivL2_smooth, hV, map_add]
    rw [hRV]
    exact connectionLaplacianRealization_graph_equiv μ g h cov hcov hcomplex S V hV
  -- Transport the entire bounded map before evaluating its graph coordinates.
  have hTcast : T =
      Eq.mp (congrArg (fun t : ℝ ↦ S.SobolevSpace 2 →L[ℂ] S.SobolevSpace t)
        (by norm_num : (2 : ℝ) - (2 : ℕ) = 0)) (D.sobolevExtension S S 2) :=
    S.sobolevInclusion_comp_eq_cast ((2 : ℝ) - (2 : ℕ)) 0 (by norm_num)
      (D.sobolevExtension S S 2)
  exact hfixed.trans (congrArg (fun U : S.SobolevSpace 2 →L[ℂ] S.SobolevSpace 0 ↦
    (J.toLinearMap.prod (J + e.toContinuousLinearMap.comp U).toLinearMap).range) hTcast)

/-- The closure is densely defined and self-adjoint, with lower bound one. -/
theorem connectionLaplacianRealization_properties :
    let A := connectionLaplacianRealization μ g h cov hcov hcomplex
    A.graph =
        ((connectionLaplacianSmoothCore μ g h cov hcov hcomplex).graph).topologicalClosure ∧
      A.IsClosed ∧ Dense (A.domain : Set (h.L2SectionSpace μ)) ∧
        IsSelfAdjoint A ∧
          ∀ u : A.domain, ‖(u : h.L2SectionSpace μ)‖ ^ 2 ≤
            (inner ℂ (u : h.L2SectionSpace μ) (A u)).re := by
  let A := connectionLaplacianRealization μ g h cov hcov hcomplex
  let core := connectionLaplacianSmoothCore μ g h cov hcov hcomplex
  have hclos := isClosable_connectionLaplacianSmoothCore μ g h cov hcov hcomplex
  have hgraphClosure : A.graph = core.graph.topologicalClosure :=
    hclos.graph_closure_eq_closure_graph.symm
  have hdense : Dense (A.domain : Set (h.L2SectionSpace μ)) :=
    (h.denseRange_smoothToL2 μ).mono core.le_closure.1
  obtain ⟨S⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨V, hV, _⟩ := existsUnique_connectionLaplacianSobolevEquiv μ g h cov hcov hcomplex S
  let J := (h.sobolevZeroEquivL2 (μ := μ) S).toContinuousLinearMap.comp
    (S.sobolevInclusion 2 0 (by norm_num))
  have hJ (v : smoothSections (n := n) (r := r) E) :
      J (S.smoothToSobolev 2 v) = h.smoothToL2 μ v := by
    change h.sobolevZeroEquivL2 (μ := μ) S
      (S.sobolevInclusion 2 0 (by norm_num) (S.smoothToSobolev 2 v)) = _
    rw [S.sobolevInclusion_smoothToSobolev, h.sobolevZeroEquivL2_smooth]
  have hgraph : A.graph = (J.prod V.toContinuousLinearMap).range :=
    connectionLaplacianRealization_graph_equiv μ g h cov hcov hcomplex S V hV
  -- H² density extends the original symmetry identity on pairs of smooth sections.
  have hpair : (fun z : S.SobolevSpace 2 × S.SobolevSpace 2 ↦
      inner ℂ (V z.1) (J z.2)) = fun z ↦ inner ℂ (J z.1) (V z.2) := by
    apply ((S.denseRange_smoothToSobolev 2).prodMap
      (S.denseRange_smoothToSobolev 2)).equalizer (by fun_prop) (by fun_prop)
    funext z
    rcases z with ⟨u, v⟩
    change inner ℂ (V (S.smoothToSobolev 2 u)) (J (S.smoothToSobolev 2 v)) =
      inner ℂ (J (S.smoothToSobolev 2 u)) (V (S.smoothToSobolev 2 v))
    rw [hV, hV, hJ, hJ, map_add, map_add, inner_add_left, inner_add_right,
      h.inner_smoothToL2, h.inner_smoothToL2, h.inner_smoothToL2]
    exact congrArg (fun z : ℂ ↦ h.sectionPairing μ u v + z)
      (connectionLaplacian_symmetric μ g h cov hcov hcomplex u v)
  have hformal : A.IsFormalAdjoint A := by
    intro x y
    obtain ⟨u, hu⟩ := hgraph ▸ A.mem_graph x
    obtain ⟨v, hv⟩ := hgraph ▸ A.mem_graph y
    have hx₁ : J u = x.val := congrArg Prod.fst hu
    have hx₂ : V u = A x := congrArg Prod.snd hu
    have hy₁ : J v = y.val := congrArg Prod.fst hv
    have hy₂ : V v = A y := congrArg Prod.snd hv
    rw [← hx₁, ← hx₂, ← hy₁, ← hy₂]
    exact congrFun hpair (u, v)
  have honto : Function.Surjective A := by
    intro y
    have hz : (J (V.symm y), y) ∈ A.graph := by
      rw [hgraph]
      refine ⟨V.symm y, ?_⟩
      exact Prod.ext rfl (V.apply_symm_apply y)
    obtain ⟨x, _, hx⟩ := A.mem_graph_iff.mp hz
    exact ⟨x, hx⟩
  -- Symmetry and surjectivity force the maximal Hilbert adjoint to have the same graph.
  have hself : IsSelfAdjoint A := by
    apply LinearPMap.isSelfAdjoint_def.mpr
    apply le_antisymm
    · apply LinearPMap.le_of_le_graph
      intro z hz
      obtain ⟨y, rfl⟩ := A.adjoint.mem_graph_iff'.mp hz
      obtain ⟨x, hx⟩ := honto (A.adjoint y)
      have hxy : (y : h.L2SectionSpace μ) = x := by
        apply ext_inner_right ℂ
        intro w
        obtain ⟨u, rfl⟩ := honto w
        calc
          inner ℂ (y : h.L2SectionSpace μ) (A u) =
              inner ℂ (A.adjoint y) (u : h.L2SectionSpace μ) :=
            (LinearPMap.adjoint_isFormalAdjoint hdense y u).symm
          _ = inner ℂ (A x) (u : h.L2SectionSpace μ) := by rw [hx]
          _ = inner ℂ (x : h.L2SectionSpace μ) (A u) := hformal x u
      exact A.mem_graph_iff.mpr ⟨x, hxy.symm, hx⟩
    · exact hformal.le_adjoint hdense
  -- The smooth connection energy inequality is closed in the two graph coordinates.
  have henergy (u : S.SobolevSpace 2) :
      ‖J u‖ ^ 2 ≤ (inner ℂ (J u) (V u)).re := by
    have hc : IsClosed {z : S.SobolevSpace 2 |
        ‖J z‖ ^ 2 ≤ (inner ℂ (J z) (V z)).re} :=
      isClosed_le (by fun_prop) (by fun_prop)
    apply hc.closure_subset_iff.mpr ?_ (S.denseRange_smoothToSobolev 2 u)
    rintro _ ⟨v, rfl⟩
    change ‖J (S.smoothToSobolev 2 v)‖ ^ 2 ≤
      (inner ℂ (J (S.smoothToSobolev 2 v)) (V (S.smoothToSobolev 2 v))).re
    rw [hJ, hV, map_add, inner_add_right, Complex.add_re]
    have hself : (inner ℂ (h.smoothToL2 μ v) (h.smoothToL2 μ v)).re =
        ‖h.smoothToL2 μ v‖ ^ 2 := by
      simpa only [RCLike.re_eq_complex_re] using
        (inner_self_eq_norm_sq (𝕜 := ℂ) (h.smoothToL2 μ v))
    rw [hself]
    have hn := connectionLaplacian_nonneg μ g h cov hcov hcomplex v
    rw [← h.inner_smoothToL2] at hn
    exact le_add_of_nonneg_right hn
  refine ⟨hgraphClosure, hclos.closure_isClosed, hdense, hself, ?_⟩
  intro x
  obtain ⟨u, hu⟩ := hgraph ▸ A.mem_graph x
  have hx₁ : J u = x.val := congrArg Prod.fst hu
  have hx₂ : V u = A x := congrArg Prod.snd hu
  rw [← hx₁, ← hx₂]
  exact henergy u

/-- The positive closed operator has a unique bounded inverse on the whole original L². -/
theorem existsUnique_connectionLaplacianInverse :
    ∃! B : h.L2SectionSpace μ →L[ℂ] h.L2SectionSpace μ,
      ∀ x y : h.L2SectionSpace μ,
        (x, y) ∈ (connectionLaplacianRealization μ g h cov hcov hcomplex).graph ↔
          B y = x := by
  obtain ⟨S⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨V, hV, _⟩ := existsUnique_connectionLaplacianSobolevEquiv μ g h cov hcov hcomplex S
  let J := (h.sobolevZeroEquivL2 (μ := μ) S).toContinuousLinearMap.comp
    (S.sobolevInclusion 2 0 (by norm_num))
  let B := J.comp V.symm.toContinuousLinearMap
  have hgraph := connectionLaplacianRealization_graph_equiv μ g h cov hcov hcomplex S V hV
  -- Invert the onto second graph coordinate while retaining the specified first coordinate.
  have hB (x y : h.L2SectionSpace μ) :
      (x, y) ∈ (connectionLaplacianRealization μ g h cov hcov hcomplex).graph ↔
        B y = x := by
    rw [hgraph]
    constructor
    · rintro ⟨u, hu⟩
      have hx : J u = x := congrArg Prod.fst hu
      have hy : V u = y := congrArg Prod.snd hu
      change J (V.symm y) = x
      rw [← hy, V.symm_apply_apply]
      exact hx
    · intro hx
      refine ⟨V.symm y, ?_⟩
      exact Prod.ext hx (V.apply_symm_apply y)
  refine ⟨B, hB, ?_⟩
  intro C hC
  ext y
  exact (hC (B y) y).mp ((hB (B y) y).mpr rfl)

/-- The bounded inverse chosen by the unique exact graph characterization. -/
def connectionLaplacianInverse : h.L2SectionSpace μ →L[ℂ] h.L2SectionSpace μ :=
  Classical.choose (existsUnique_connectionLaplacianInverse μ g h cov hcov hcomplex).exists

/-- Both inverse equations, including exact domain membership, are encoded by this graph. -/
theorem connectionLaplacianInverse_graph (x y : h.L2SectionSpace μ) :
    (x, y) ∈ (connectionLaplacianRealization μ g h cov hcov hcomplex).graph ↔
      connectionLaplacianInverse μ g h cov hcov hcomplex y = x := by
  exact (Classical.choose_spec
    (existsUnique_connectionLaplacianInverse μ g h cov hcov hcomplex).exists) x y

/-- The bounded inverse is positive, compact and injective with dense range and norm at most one. -/
theorem connectionLaplacianInverse_properties :
    let B := connectionLaplacianInverse μ g h cov hcov hcomplex
    let A := connectionLaplacianRealization μ g h cov hcov hcomplex
    0 ≤ B ∧ Function.Injective B ∧ DenseRange B ∧ IsCompactOperator B ∧
      ‖B‖ ≤ 1 ∧ B.toLinearMap.toPMap ⊤ = A.inverse := by
  let B := connectionLaplacianInverse μ g h cov hcov hcomplex
  let A := connectionLaplacianRealization μ g h cov hcov hcomplex
  have hBi (x y : h.L2SectionSpace μ) : (x, y) ∈ A.graph ↔ B y = x :=
    connectionLaplacianInverse_graph μ g h cov hcov hcomplex x y
  have hBA (y : h.L2SectionSpace μ) : (B y, y) ∈ A.graph := (hBi (B y) y).mpr rfl
  obtain ⟨_, _, hdense, hself, hlower⟩ :=
    connectionLaplacianRealization_properties μ g h cov hcov hcomplex
  have hformal : A.IsFormalAdjoint A := by
    have hf := LinearPMap.adjoint_isFormalAdjoint hdense
    rwa [LinearPMap.isSelfAdjoint_def.mp hself] at hf
  -- Exact inverse graph equations transfer symmetry and the quadratic lower bound.
  have hsym : B.IsSymmetric := by
    intro x y
    obtain ⟨u, hu, hAu⟩ := A.mem_graph_iff.mp (hBA x)
    obtain ⟨v, hv, hAv⟩ := A.mem_graph_iff.mp (hBA y)
    change u.val = B x at hu
    change v.val = B y at hv
    change A u = x at hAu
    change A v = y at hAv
    change inner ℂ (B x) y = inner ℂ x (B y)
    rw [← hu, ← hv, ← hAu, ← hAv]
    exact (hformal u v).symm
  have henergy (y : h.L2SectionSpace μ) :
      ‖B y‖ ^ 2 ≤ (inner ℂ (B y) y).re := by
    obtain ⟨u, hu, hAu⟩ := A.mem_graph_iff.mp (hBA y)
    change u.val = B y at hu
    change A u = y at hAu
    rw [← hu, ← hAu]
    exact hlower u
  have hpositive : 0 ≤ B := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    refine ⟨hsym, fun y ↦ ?_⟩
    change 0 ≤ (inner ℂ (B y) y).re
    exact (sq_nonneg ‖B y‖).trans (henergy y)
  have hinj : Function.Injective B := by
    intro x y hxy
    exact A.mem_graph_snd_inj (hBA x) (hBA y) hxy
  have hdenseB : DenseRange B := by
    apply hdense.mono
    intro x hx
    exact ⟨A ⟨x, hx⟩, (hBi x (A ⟨x, hx⟩)).mp (A.mem_graph ⟨x, hx⟩)⟩
  have hnorm : ‖B‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    have hc : (inner ℂ (B y) y).re ≤ ‖B y‖ * ‖y‖ := by
      simpa only [RCLike.re_eq_complex_re] using (re_inner_le_norm (𝕜 := ℂ) (B y) y)
    have hb := (henergy y).trans hc
    nlinarith [norm_nonneg (B y), norm_nonneg y]
  -- The explicit inverse factors through H² and the compact strict Sobolev inclusion.
  obtain ⟨S⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨V, hV, _⟩ := existsUnique_connectionLaplacianSobolevEquiv μ g h cov hcov hcomplex S
  let e := h.sobolevZeroEquivL2 (μ := μ) S
  let I := S.sobolevInclusion 2 0 (by norm_num)
  let J := e.toContinuousLinearMap.comp I
  have hgraph : A.graph = (J.prod V.toContinuousLinearMap).range :=
    connectionLaplacianRealization_graph_equiv μ g h cov hcov hcomplex S V hV
  have hBV : B = J.comp V.symm.toContinuousLinearMap := by
    ext y
    apply (hBi (J (V.symm y)) y).mp
    rw [hgraph]
    exact ⟨V.symm y, Prod.ext rfl (V.apply_symm_apply y)⟩
  have hcompact : IsCompactOperator B := by
    rw [hBV]
    exact ((S.isCompactOperator_sobolevInclusion 2 0 (by norm_num)).clm_comp
      e.toContinuousLinearMap).comp_clm V.symm.toContinuousLinearMap
  -- Zero kernel excludes the fallback branch of the partial inverse definition.
  have hker : A.ker = ⊥ := by
    apply LinearPMap.ker_eq_bot'.mpr
    intro x hx
    apply Subtype.ext
    have he := (hBi x.val (A x)).mp (A.mem_graph x)
    rw [hx, map_zero] at he
    exact he.symm
  refine ⟨hpositive, hinj, hdenseB, hcompact, hnorm, ?_⟩
  apply LinearPMap.eq_of_eq_graph
  rw [A.inverse_graph hker]
  ext z
  rcases z with ⟨x, y⟩
  rw [Submodule.map_equiv_eq_comap_symm]
  change (x, y) ∈ (B.toLinearMap.toPMap ⊤).graph ↔ (y, x) ∈ A.graph
  rw [hBi]
  simp only [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨z, hz, hBz⟩
    change B z.val = y at hBz
    rwa [hz] at hBz
  · intro hxy
    exact ⟨⟨x, Submodule.mem_top⟩, rfl, hxy⟩

end AtiyahSinger
