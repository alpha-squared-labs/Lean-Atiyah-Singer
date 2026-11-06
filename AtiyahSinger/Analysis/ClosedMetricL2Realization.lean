/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricL2Realization
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Closed L² realizations of first-order elliptic operators

Public module ID: M0341.

UL01: the original smooth PDO gives an actual partially defined operator on the
metric integral Hilbert spaces. Its graph closure is identified with the H¹ graph,
and its unbounded adjoint with the closure of the original formal adjoint.

Sources: SG III.2.15, III.5.2–5.3 and the closed-operator argument in III.13.5,
pp. 249–250. The exact comparison with the project's Sobolev presentations is a
project deduction. No bounded H¹-to-L² Hilbert adjoint replaces the L² adjoint.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

namespace PseudodifferentialOperator

variable (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1)

/-- The original smooth PDO, with domain the actual smooth image in metric L². -/
def metricL2SmoothCore : h.L2SectionSpace μ →ₗ.[ℂ] k.L2SectionSpace μ where
  domain := (h.smoothToL2 μ).range
  toFun := (k.smoothToL2 μ).comp (P.toLinearMap.comp
    (LinearEquiv.ofInjective (h.smoothToL2 μ) (h.smoothToL2_injective μ)).symm.toLinearMap)

/-- The smooth operator is closable in the two integral L² spaces. -/
theorem isClosable_metricL2SmoothCore : (P.metricL2SmoothCore h k).IsClosable := by
  /- Integral adjunction on the two dense smooth images gives a formal-adjoint
  pair in their actual integral Hilbert spaces. The original smooth operator is
  therefore a restriction of the closed Hilbert adjoint of the target smooth
  core, and a restriction of a closed operator is closable. -/
  -- The geometric integral adjoint gives a densely defined Hilbert-space adjoint pair.
  let Q := P.metricFormalAdjoint h k
  let S := Q.metricL2SmoothCore k h
  have hS : Dense (S.domain : Set (k.L2SectionSpace μ)) :=
    k.denseRange_smoothToL2 μ
  have hformal : (P.metricL2SmoothCore h k).IsFormalAdjoint S := by
    intro x y
    let e := LinearEquiv.ofInjective (h.smoothToL2 μ) (h.smoothToL2_injective μ)
    let f := LinearEquiv.ofInjective (k.smoothToL2 μ) (k.smoothToL2_injective μ)
    let u := e.symm x
    let v := f.symm y
    have hx : h.smoothToL2 μ u = x.val := congrArg Subtype.val (e.apply_symm_apply x)
    have hy : k.smoothToL2 μ v = y.val := congrArg Subtype.val (f.apply_symm_apply y)
    change inner ℂ (k.smoothToL2 μ (P.toLinearMap u)) y.val =
      inner ℂ x.val (h.smoothToL2 μ (Q.toLinearMap v))
    rw [← hx, ← hy, k.inner_smoothToL2, h.inner_smoothToL2]
    exact P.isMetricFormalAdjoint_metricFormalAdjoint h k u v
  -- A restriction of the closed Hilbert adjoint is closable in the same L² spaces.
  exact (LinearPMap.adjoint_isClosed hS).isClosable.leIsClosable
    (hformal.symm.le_adjoint hS)

/-- The closed realization is the graph closure of that same smooth-section operator. -/
def metricL2ClosedRealization : h.L2SectionSpace μ →ₗ.[ℂ] k.L2SectionSpace μ :=
  (P.metricL2SmoothCore h k).closure

/-- The graph closure is a densely defined closed operator, with its exact graph. -/
theorem metricL2ClosedRealization_realization :
    (P.metricL2ClosedRealization h k).graph =
        (P.metricL2SmoothCore h k).graph.topologicalClosure ∧
      (P.metricL2ClosedRealization h k).IsClosed ∧
      Dense ((P.metricL2ClosedRealization h k).domain : Set (h.L2SectionSpace μ)) := by
  /- Stage 1: apply closability to exclude the fallback branch of LinearPMap.closure;
  its graph is the actual topological closure and is closed.
  Stage 2: the closure extends the smooth core. Its domain therefore contains the
  original dense smooth image, so it is dense in the same integral L² space. -/
  -- Closability identifies the chosen closure with the actual closed graph.
  have hclosed := P.isClosable_metricL2SmoothCore h k
  refine ⟨hclosed.graph_closure_eq_closure_graph.symm, hclosed.closure_isClosed, ?_⟩
  -- The original dense smooth domain remains inside the closed realization.
  exact (h.denseRange_smoothToL2 μ).mono (P.metricL2SmoothCore h k).le_closure.1

/-- Elliptic regularity identifies the exact closed graph with the original H¹ graph. -/
theorem metricL2ClosedRealization_graph_sobolev (hP : P.IsElliptic)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) :
    let J : A.SobolevSpace 1 →L[ℂ] h.L2SectionSpace μ :=
      (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap.comp
        (A.sobolevInclusion 1 0 (by norm_num))
    let T : A.SobolevSpace 1 →L[ℂ] B.SobolevSpace 0 := by
      exact Eq.mp (congrArg (fun s : ℝ ↦ A.SobolevSpace 1 →L[ℂ] B.SobolevSpace s)
        (sub_self (1 : ℝ))) (P.sobolevExtension A B 1)
    let R : A.SobolevSpace 1 →L[ℂ] k.L2SectionSpace μ :=
      (k.sobolevZeroEquivL2 (μ := μ) B).toContinuousLinearMap.comp T
    (P.metricL2ClosedRealization h k).graph = (J.toLinearMap.prod R.toLinearMap).range := by
  /- Compare the H¹ input and output maps with the same original smooth section
  and its P output. The elliptic estimate and the inverse H⁰-to-L² norm bounds
  make the paired graph map bounded below, so its range is closed and contains
  the closure of the smooth graph. Conversely, density of the same smooth
  sections in H¹ puts every paired H¹ value in that graph closure. This identifies
  the actual H¹ graph without choosing a replacement completion. -/
  let e := h.sobolevZeroEquivL2 (μ := μ) A
  let f := k.sobolevZeroEquivL2 (μ := μ) B
  let I : A.SobolevSpace 1 →L[ℂ] A.SobolevSpace 0 := A.sobolevInclusion 1 0 (by norm_num)
  let J := e.toContinuousLinearMap.comp I
  let T := P.sobolevRealization A B 1 0 (by norm_num)
  have hTcast : T =
      Eq.mp (congrArg (fun s : ℝ ↦ A.SobolevSpace 1 →L[ℂ] B.SobolevSpace s)
        (sub_self (1 : ℝ))) (P.sobolevExtension A B 1) := by
    -- Compare whole maps after equality induction, before applying any completed vector.
    have hext (t : ℝ) (ht : t = 0) (U : A.SobolevSpace 1 →L[ℂ] B.SobolevSpace t)
        (hU : ∀ v : smoothSections (n := n) (r := r) E,
          U (A.smoothToSobolev 1 v) = B.smoothToSobolev t (P.toLinearMap v)) :
        T = Eq.mp (congrArg (fun s : ℝ ↦ A.SobolevSpace 1 →L[ℂ] B.SobolevSpace s) ht) U := by
      subst t
      apply DFunLike.coe_injective
      apply (A.denseRange_smoothToSobolev 1).equalizer T.continuous U.continuous
      funext v
      exact (P.sobolevRealization_smoothToSobolev A B 1 0 (by norm_num) v).trans (hU v).symm
    exact hext (1 - 1) (sub_self 1) (P.sobolevExtension A B 1)
      (P.sobolevExtension_smoothToSobolev A B 1)
  let R := f.toContinuousLinearMap.comp T
  let G := J.prod R
  rw [← hTcast]
  change (P.metricL2ClosedRealization h k).graph = G.range
  have hJ (v : smoothSections (n := n) (r := r) E) :
      J (A.smoothToSobolev 1 v) = h.smoothToL2 μ v := by
    change e (I (A.smoothToSobolev 1 v)) = _
    rw [A.sobolevInclusion_smoothToSobolev, h.sobolevZeroEquivL2_smooth]
  have hT (v : smoothSections (n := n) (r := r) E) :
      T (A.smoothToSobolev 1 v) = B.smoothToSobolev 0 (P.toLinearMap v) :=
    P.sobolevRealization_smoothToSobolev A B 1 0 (by norm_num) v
  have hR (v : smoothSections (n := n) (r := r) E) :
      R (A.smoothToSobolev 1 v) = k.smoothToL2 μ (P.toLinearMap v) := by
    change f (T (A.smoothToSobolev 1 v)) = _
    rw [hT, k.sobolevZeroEquivL2_smooth]
  have hgExists : ∃ g : B.SobolevSpace (1 - 1) ≃L[ℂ] k.L2SectionSpace μ,
      ∀ v : smoothSections (n := n) (r := q) F,
        g (B.smoothToSobolev (1 - 1) v) = k.smoothToL2 μ v := by
    rw [sub_self]
    exact ⟨k.sobolevZeroEquivL2 (μ := μ) B, k.sobolevZeroEquivL2_smooth B⟩
  obtain ⟨g, hg⟩ := hgExists
  have hRcompare : R = g.toContinuousLinearMap.comp (P.sobolevExtension A B 1) := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev 1).equalizer R.continuous
      (g.toContinuousLinearMap.comp (P.sobolevExtension A B 1)).continuous
    funext v
    change R (A.smoothToSobolev 1 v) = g (P.sobolevExtension A B 1 (A.smoothToSobolev 1 v))
    rw [P.sobolevExtension_smoothToSobolev, hg]
    exact hR v
  -- The elliptic estimate and both inverse norm bounds make the graph map bounded below.
  obtain ⟨C, hC, hbound⟩ := P.exists_estimate_of_isElliptic A B hP 1 0 (by norm_num)
  let D : NNReal := ⟨C * (‖g.symm.toContinuousLinearMap‖ + ‖e.symm.toContinuousLinearMap‖),
    mul_nonneg hC (add_nonneg (norm_nonneg _) (norm_nonneg _))⟩
  have hGbound (u : A.SobolevSpace 1) : ‖u‖ ≤ D * ‖G u‖ := by
    have hI : ‖I u‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖J u‖ := by
      have hinv : e.symm (J u) = I u := e.symm_apply_apply _
      exact hinv ▸ e.symm.toContinuousLinearMap.le_opNorm (J u)
    have hRinv : ‖P.sobolevExtension A B 1 u‖ ≤
        ‖g.symm.toContinuousLinearMap‖ * ‖R u‖ := by
      have hinv : g.symm (R u) = P.sobolevExtension A B 1 u := by
        rw [hRcompare]
        exact g.symm_apply_apply _
      exact hinv ▸ g.symm.toContinuousLinearMap.le_opNorm (R u)
    have hJu : ‖J u‖ ≤ ‖G u‖ := norm_fst_le (G u)
    have hRu : ‖R u‖ ≤ ‖G u‖ := norm_snd_le (G u)
    calc
      ‖u‖ ≤ C * (‖P.sobolevExtension A B 1 u‖ + ‖I u‖) := hbound u
      _ ≤ C * (‖g.symm.toContinuousLinearMap‖ * ‖G u‖ +
          ‖e.symm.toContinuousLinearMap‖ * ‖G u‖) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (hRinv.trans (mul_le_mul_of_nonneg_left hRu (norm_nonneg _)))
          (hI.trans (mul_le_mul_of_nonneg_left hJu (norm_nonneg _)))) hC
      _ = D * ‖G u‖ := by
        change C * (‖g.symm.toContinuousLinearMap‖ * ‖G u‖ +
          ‖e.symm.toContinuousLinearMap‖ * ‖G u‖) =
            (C * (‖g.symm.toContinuousLinearMap‖ + ‖e.symm.toContinuousLinearMap‖)) * ‖G u‖
        ring
  have hclosed : IsClosed (G.range : Set (h.L2SectionSpace μ × k.L2SectionSpace μ)) :=
    (G.antilipschitz_of_bound hGbound).isClosed_range G.uniformContinuous
  let smoothEquiv := LinearEquiv.ofInjective (h.smoothToL2 μ) (h.smoothToL2_injective μ)
  have hcore : (P.metricL2SmoothCore h k).graph ≤ G.range := by
    intro z hz
    obtain ⟨x, rfl⟩ := (P.metricL2SmoothCore h k).mem_graph_iff'.mp hz
    let v := smoothEquiv.symm x
    refine ⟨A.smoothToSobolev 1 v, ?_⟩
    apply Prod.ext
    · exact (hJ v).trans (congrArg Subtype.val (smoothEquiv.apply_symm_apply x))
    · exact hR v
  have hsmooth (v : smoothSections (n := n) (r := r) E) :
      G (A.smoothToSobolev 1 v) ∈ (P.metricL2SmoothCore h k).graph := by
    apply (P.metricL2SmoothCore h k).mem_graph_iff.mpr
    refine ⟨smoothEquiv v, (hJ v).symm, ?_⟩
    change k.smoothToL2 μ (P.toLinearMap (smoothEquiv.symm (smoothEquiv v))) =
      R (A.smoothToSobolev 1 v)
    rw [smoothEquiv.symm_apply_apply, hR]
  rw [(P.metricL2ClosedRealization_realization h k).1]
  apply le_antisymm
  · exact (P.metricL2SmoothCore h k).graph.topologicalClosure_minimal hcore hclosed
  · rintro z ⟨u, rfl⟩
    -- Every H¹ vector is a limit of the same smooth sections, in both graph coordinates.
    apply map_mem_closure G.continuous (A.denseRange_smoothToSobolev 1 u)
    rintro _ ⟨v, rfl⟩
    exact hsmooth v

set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the unbounded metric adjoint and original closed operator graph.
/-- The unbounded L² adjoint is the closed realization of the geometric formal adjoint. -/
theorem metricL2ClosedRealization_metricFormalAdjoint (hP : P.IsElliptic) :
    (P.metricFormalAdjoint h k).metricL2ClosedRealization k h =
      (P.metricL2ClosedRealization h k).adjoint := by
  /- Stage 1: integral adjunction on smooth sections, then graph approximation,
  gives inclusion of the formal-adjoint closure in the unbounded adjoint.
  Stage 2: a vector in the adjoint domain solves P* v = w distributionally with
  v,w in L². Elliptic regularity puts v in H¹. The preceding graph identification
  for P* gives the opposite inclusion, including equality of operator actions.
  The adjoint here is LinearPMap.adjoint on L²; it is not the bounded adjoint
  of the H¹-to-L² extension, whose target and scalar product would be different. -/
  let Q := P.metricFormalAdjoint h k
  let L := P.metricL2ClosedRealization h k
  let S := Q.metricL2SmoothCore k h
  have hdense : Dense (L.domain : Set (h.L2SectionSpace μ)) :=
    (P.metricL2ClosedRealization_realization h k).2.2
  have hformal : L.IsFormalAdjoint S := by
    intro x y
    let e := LinearEquiv.ofInjective (h.smoothToL2 μ) (h.smoothToL2_injective μ)
    let f := LinearEquiv.ofInjective (k.smoothToL2 μ) (k.smoothToL2_injective μ)
    let v := f.symm y
    have hy : k.smoothToL2 μ v = y.val := congrArg Subtype.val (f.apply_symm_apply y)
    have hclosed : IsClosed {z : h.L2SectionSpace μ × k.L2SectionSpace μ |
        inner ℂ z.2 y.val = inner ℂ z.1 (S y)} :=
      isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
    have hcore : ((P.metricL2SmoothCore h k).graph :
        Set (h.L2SectionSpace μ × k.L2SectionSpace μ)) ⊆
        {z | inner ℂ z.2 y.val = inner ℂ z.1 (S y)} := by
      intro z hz
      obtain ⟨a, rfl⟩ := (P.metricL2SmoothCore h k).mem_graph_iff'.mp hz
      let u := e.symm a
      have ha : h.smoothToL2 μ u = a.val := congrArg Subtype.val (e.apply_symm_apply a)
      change inner ℂ (k.smoothToL2 μ (P.toLinearMap u)) y.val =
        inner ℂ a.val (h.smoothToL2 μ (Q.toLinearMap v))
      rw [← ha, ← hy, k.inner_smoothToL2, h.inner_smoothToL2]
      exact P.isMetricFormalAdjoint_metricFormalAdjoint h k u v
    have hx := L.mem_graph x
    rw [(P.metricL2ClosedRealization_realization h k).1] at hx
    exact hclosed.closure_subset_iff.mpr hcore hx
  -- Integral adjunction extends across the graph closure in the original two L² spaces.
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    rw [(Q.metricL2ClosedRealization_realization k h).1]
    exact S.graph.topologicalClosure_minimal
      (LinearPMap.le_graph_of_le (hformal.le_adjoint hdense))
      (LinearPMap.adjoint_isClosed hdense)
  · apply LinearPMap.le_of_le_graph
    intro pair hpair
    obtain ⟨y, rfl⟩ := L.adjoint.mem_graph_iff'.mp hpair
    obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
    obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
    let e := k.sobolevZeroEquivL2 (μ := μ) B
    have hfExists : ∃ f : A.SobolevSpace (1 - 1) ≃L[ℂ] h.L2SectionSpace μ,
        ∀ u : smoothSections (n := n) (r := r) E,
          f (A.smoothToSobolev (1 - 1) u) = h.smoothToL2 μ u := by
      rw [sub_self]
      exact ⟨h.sobolevZeroEquivL2 (μ := μ) A, h.sobolevZeroEquivL2_smooth A⟩
    obtain ⟨f, hf⟩ := hfExists
    have hdExists : ∃ d : A.SobolevSpace (0 - 1) ≃L⋆[ℂ]
        StrongDual ℂ (A.SobolevSpace 1),
        ∀ u v : smoothSections (n := n) (r := r) E,
          d (A.smoothToSobolev (0 - 1) u) (A.smoothToSobolev 1 v) =
            h.sectionPairing μ u v := by
      rw [zero_sub]
      exact ⟨h.sobolevDuality A μ 1, h.sobolevPairing_smooth A μ 1⟩
    obtain ⟨d, hd⟩ := hdExists
    let v₀ := e.symm y.val
    let w₀ := f.symm (L.adjoint y)
    let I := A.sobolevInclusion (1 - 1) (0 - 1) (by norm_num)
    -- The L² adjoint relation is a weak equation for the original adjoint PDO at order zero.
    have hpairQ (v : B.SobolevSpace 0) (u : smoothSections (n := n) (r := r) E) :
        d (Q.sobolevExtension B A 0 v) (A.smoothToSobolev 1 u) =
          inner ℂ (e v) (k.smoothToL2 μ (P.toLinearMap u)) := by
      refine (B.denseRange_smoothToSobolev 0).induction_on v
        (isClosed_eq
          ((d.continuous.comp (Q.sobolevExtension B A 0).continuous).clm_apply continuous_const)
          (e.continuous.inner continuous_const)) ?_
      intro z
      rw [Q.sobolevExtension_smoothToSobolev, hd, k.sobolevZeroEquivL2_smooth,
        k.inner_smoothToL2]
      exact (P.isMetricFormalAdjoint_metricFormalAdjoint h k).symm z u
    have hpairI (w : A.SobolevSpace (1 - 1)) (u : smoothSections (n := n) (r := r) E) :
        d (I w) (A.smoothToSobolev 1 u) = inner ℂ (f w) (h.smoothToL2 μ u) := by
      refine (A.denseRange_smoothToSobolev (1 - 1)).induction_on w
        (isClosed_eq ((d.continuous.comp I.continuous).clm_apply continuous_const)
          (f.continuous.inner continuous_const)) ?_
      intro z
      rw [A.sobolevInclusion_smoothToSobolev, hd, hf, h.inner_smoothToL2]
    have hweak : Q.sobolevExtension B A 0 v₀ = I w₀ := by
      apply d.injective
      apply DFunLike.coe_injective
      apply (A.denseRange_smoothToSobolev 1).equalizer
        (d (Q.sobolevExtension B A 0 v₀)).continuous (d (I w₀)).continuous
      funext u
      change d (Q.sobolevExtension B A 0 v₀) (A.smoothToSobolev 1 u) =
        d (I w₀) (A.smoothToSobolev 1 u)
      rw [hpairQ, hpairI]
      change inner ℂ (e (e.symm y.val)) (k.smoothToL2 μ (P.toLinearMap u)) =
        inner ℂ (f (f.symm (L.adjoint y))) (h.smoothToL2 μ u)
      rw [e.apply_symm_apply, f.apply_symm_apply]
      let eSmooth := LinearEquiv.ofInjective (h.smoothToL2 μ) (h.smoothToL2_injective μ)
      let x : L.domain := ⟨h.smoothToL2 μ u,
        (P.metricL2SmoothCore h k).le_closure.1 (eSmooth u).property⟩
      have hact : L x = k.smoothToL2 μ (P.toLinearMap u) := by
        have heq := (P.metricL2SmoothCore h k).le_closure.2 (x := eSmooth u) (y := x) rfl
        change k.smoothToL2 μ (P.toLinearMap (eSmooth.symm (eSmooth u))) = L x at heq
        rw [eSmooth.symm_apply_apply] at heq
        exact heq.symm
      have hdual := LinearPMap.adjoint_isFormalAdjoint hdense y x
      rw [hact] at hdual
      exact hdual.symm
    have hQ : Q.IsElliptic := (P.isElliptic_metricFormalAdjoint_iff h k).mpr hP
    obtain ⟨parametrix, hparametrix⟩ := Q.exists_parametrix_of_isElliptic hQ
    obtain ⟨z, ⟨hz, hQz⟩, _⟩ :=
      Q.existsUnique_sobolev_lift_of_isSmoothingOperator parametrix B A hparametrix.1
        0 1 (by norm_num) v₀ w₀ hweak
    -- Regularity identifies the same vector and output with the actual H¹ graph.
    let U := Q.sobolevRealization B A 1 0 (by norm_num)
    let f₀ := h.sobolevZeroEquivL2 (μ := μ) A
    have hUcast : U =
        Eq.mp (congrArg (fun s : ℝ ↦ B.SobolevSpace 1 →L[ℂ] A.SobolevSpace s)
          (sub_self (1 : ℝ))) (Q.sobolevExtension B A 1) := by
      have hext (t : ℝ) (ht : t = 0) (V : B.SobolevSpace 1 →L[ℂ] A.SobolevSpace t)
          (hV : ∀ v : smoothSections (n := n) (r := q) F,
            V (B.smoothToSobolev 1 v) = A.smoothToSobolev t (Q.toLinearMap v)) :
          U = Eq.mp (congrArg (fun s : ℝ ↦ B.SobolevSpace 1 →L[ℂ] A.SobolevSpace s) ht) V := by
        subst t
        apply DFunLike.coe_injective
        apply (B.denseRange_smoothToSobolev 1).equalizer U.continuous V.continuous
        funext v
        exact (Q.sobolevRealization_smoothToSobolev B A 1 0 (by norm_num) v).trans (hV v).symm
      exact hext (1 - 1) (sub_self 1) (Q.sobolevExtension B A 1)
        (Q.sobolevExtension_smoothToSobolev B A 1)
    have houtput (u : B.SobolevSpace 1) : f₀ (U u) = f (Q.sobolevExtension B A 1 u) := by
      have heq : f₀.toContinuousLinearMap.comp U =
          f.toContinuousLinearMap.comp (Q.sobolevExtension B A 1) := by
        apply DFunLike.coe_injective
        apply (B.denseRange_smoothToSobolev 1).equalizer
          (f₀.toContinuousLinearMap.comp U).continuous
          (f.toContinuousLinearMap.comp (Q.sobolevExtension B A 1)).continuous
        funext v
        change f₀ (U (B.smoothToSobolev 1 v)) =
          f (Q.sobolevExtension B A 1 (B.smoothToSobolev 1 v))
        rw [Q.sobolevRealization_smoothToSobolev, h.sobolevZeroEquivL2_smooth,
          Q.sobolevExtension_smoothToSobolev, hf]
      exact DFunLike.congr_fun heq u
    rw [Q.metricL2ClosedRealization_graph_sobolev k h hQ B A, ← hUcast]
    refine ⟨z, ?_⟩
    apply Prod.ext
    · change e (B.sobolevInclusion 1 0 (by norm_num) z) = y.val
      rw [hz]
      exact e.apply_symm_apply y.val
    · change f₀ (U z) = L.adjoint y
      rw [houtput, hQz]
      exact f.apply_symm_apply (L.adjoint y)

/-- The closed elliptic realization has closed range and finite kernel and actual cokernel. -/
theorem closed_range_finite_metricL2ClosedRealization (hP : P.IsElliptic) :
    IsClosed ((P.metricL2ClosedRealization h k).toFun.range : Set (k.L2SectionSpace μ)) ∧
      FiniteDimensional ℂ (P.metricL2ClosedRealization h k).ker ∧
      FiniteDimensional ℂ
        (k.L2SectionSpace μ ⧸ (P.metricL2ClosedRealization h k).toFun.range) := by
  /- Stage 1: the full-symbol parametrix makes the original H¹-to-H⁰ extension
  Fredholm. Transport its output through the same H⁰-to-integral-L² equivalence.
  Stage 2: the exact graph identity identifies both its range and its kernel
  with those of the closed realization. The input inclusion is injective, so
  the kernel dimensions agree. Use the quotient by the actual common range;
  closedness is a conclusion, and no closure of the range is substituted. -/
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  let J : A.SobolevSpace 1 →L[ℂ] h.L2SectionSpace μ :=
    (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap.comp
      (A.sobolevInclusion 1 0 (by norm_num))
  let T := P.sobolevRealization A B 1 0 (by norm_num)
  have hTcast : T =
      Eq.mp (congrArg (fun s : ℝ ↦ A.SobolevSpace 1 →L[ℂ] B.SobolevSpace s)
        (sub_self (1 : ℝ))) (P.sobolevExtension A B 1) := by
    -- Compare whole maps after equality induction, before applying any completed vector.
    have hext (t : ℝ) (ht : t = 0) (U : A.SobolevSpace 1 →L[ℂ] B.SobolevSpace t)
        (hU : ∀ v : smoothSections (n := n) (r := r) E,
          U (A.smoothToSobolev 1 v) = B.smoothToSobolev t (P.toLinearMap v)) :
        T = Eq.mp (congrArg (fun s : ℝ ↦ A.SobolevSpace 1 →L[ℂ] B.SobolevSpace s) ht) U := by
      subst t
      apply DFunLike.coe_injective
      apply (A.denseRange_smoothToSobolev 1).equalizer T.continuous U.continuous
      funext v
      exact (P.sobolevRealization_smoothToSobolev A B 1 0 (by norm_num) v).trans (hU v).symm
    exact hext (1 - 1) (sub_self 1) (P.sobolevExtension A B 1)
      (P.sobolevExtension_smoothToSobolev A B 1)
  let R := (k.sobolevZeroEquivL2 (μ := μ) B).toContinuousLinearMap.comp T
  let L := P.metricL2ClosedRealization h k
  have hgraph : L.graph = (J.toLinearMap.prod R.toLinearMap).range := by
    simpa only [← hTcast] using P.metricL2ClosedRealization_graph_sobolev h k hP A B
  have hR (v : smoothSections (n := n) (r := r) E) :
      R (A.smoothToSobolev 1 v) = k.smoothToL2 μ (P.toLinearMap v) := by
    change k.sobolevZeroEquivL2 (μ := μ) B (T (A.smoothToSobolev 1 v)) = _
    rw [P.sobolevRealization_smoothToSobolev, k.sobolevZeroEquivL2_smooth]
  have hgExists : ∃ g : B.SobolevSpace (1 - 1) ≃L[ℂ] k.L2SectionSpace μ,
      ∀ v : smoothSections (n := n) (r := q) F,
        g (B.smoothToSobolev (1 - 1) v) = k.smoothToL2 μ v := by
    rw [sub_self]
    exact ⟨k.sobolevZeroEquivL2 (μ := μ) B, k.sobolevZeroEquivL2_smooth B⟩
  obtain ⟨g, hg⟩ := hgExists
  have hRcompare : R = g.toContinuousLinearMap.comp (P.sobolevExtension A B 1) := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev 1).equalizer R.continuous
      (g.toContinuousLinearMap.comp (P.sobolevExtension A B 1)).continuous
    funext v
    change R (A.smoothToSobolev 1 v) = g (P.sobolevExtension A B 1 (A.smoothToSobolev 1 v))
    rw [P.sobolevExtension_smoothToSobolev, hg]
    exact hR v
  have hFred : R.IsFredholm := by
    rw [hRcompare]
    exact g.isFredholm.comp (P.isFredholm_sobolevExtension_of_isElliptic A B hP 1)
  -- Equality of the exact graphs identifies the actual ranges in integral L².
  have hrange : L.toFun.range = R.range := by
    ext y
    rw [LinearPMap.mem_range_iff, hgraph]
    constructor
    · rintro ⟨x, u, hu⟩
      exact ⟨u, congrArg Prod.snd hu⟩
    · rintro ⟨u, rfl⟩
      exact ⟨J u, u, rfl⟩
  have hker : L.ker = R.ker.map J.toLinearMap := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, hzero⟩ := LinearPMap.mem_ker_iff.mp hx
      have hg : (x, 0) ∈ L.graph := L.mem_graph_iff.mpr ⟨v, hv.symm, hzero⟩
      rw [hgraph] at hg
      obtain ⟨u, hu⟩ := hg
      exact ⟨u, congrArg Prod.snd hu, congrArg Prod.fst hu⟩
    · rintro ⟨u, hu, rfl⟩
      have hg : (J u, 0) ∈ L.graph := by
        rw [hgraph]
        exact ⟨u, Prod.ext rfl hu⟩
      obtain ⟨v, hv, hzero⟩ := L.mem_graph_iff.mp hg
      exact LinearPMap.mem_ker_iff.mpr ⟨v, hv.symm, hzero⟩
  -- Finiteness transfers along the same domain map; the quotient uses the common actual range.
  refine ⟨?_, ?_, ?_⟩
  · change IsClosed (L.toFun.range : Set (k.L2SectionSpace μ))
    rw [hrange]
    exact hFred.isClosed_range
  · change FiniteDimensional ℂ L.ker
    let : FiniteDimensional ℂ R.ker := hFred.finite_ker
    rw [hker]
    infer_instance
  · change FiniteDimensional ℂ (k.L2SectionSpace μ ⧸ L.toFun.range)
    rw [hrange]
    exact hFred.finite_coker

end PseudodifferentialOperator

end AtiyahSinger
