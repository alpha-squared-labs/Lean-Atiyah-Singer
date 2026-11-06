/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedMetricL2Realization

/-!
# Natural kernel and cokernel comparisons for the closed integral realization

Public module ID: M0340.

The original smooth inclusion identifies the kernel and actual range quotient
of an elliptic order-one PDO with those of its closed integral L² realization.
The same-section formulas make these comparisons usable with the original
geometric group actions. The cokernel is the quotient by the actual range.

Sources: SG III.5.2--5.3 and the closed-operator argument in III.13.5.
The explicit comparison through the project's H¹ graph is a project deduction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

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

set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the original smooth inclusions and closed kernel-cokernel
-- equivalences.
/-- The actual smooth inclusion induces kernel and cokernel equivalences for the closed PDO. -/
theorem exists_metricL2ClosedRealization_kernel_cokernel_equiv (hP : P.IsElliptic) :
    ∃ e : P.toLinearMap.ker ≃ₗ[ℂ] (P.metricL2ClosedRealization h k).ker,
      ∃ f : (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) ≃ₗ[ℂ]
          (k.L2SectionSpace μ ⧸ (P.metricL2ClosedRealization h k).toFun.range),
        (∀ u : P.toLinearMap.ker, (e u).val = h.smoothToL2 μ u.val) ∧
        (∀ v : smoothSections (n := n) (r := q) F,
          f (P.toLinearMap.range.mkQ v) =
            (P.metricL2ClosedRealization h k).toFun.range.mkQ (k.smoothToL2 μ v)) := by
  classical
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  let L := P.metricL2ClosedRealization h k
  let J : A.SobolevSpace 1 →L[ℂ] h.L2SectionSpace μ :=
    (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap.comp
      (A.sobolevInclusion 1 0 (by norm_num))
  let T := P.sobolevRealization A B 1 0 (by norm_num)
  have hTcast : T =
      Eq.mp (congrArg (fun s : ℝ ↦ A.SobolevSpace 1 →L[ℂ] B.SobolevSpace s)
        (sub_self (1 : ℝ))) (P.sobolevExtension A B 1) := by
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
  have hgraph : L.graph = (J.toLinearMap.prod R.toLinearMap).range := by
    simpa only [← hTcast] using P.metricL2ClosedRealization_graph_sobolev h k hP A B
  have hJ (v : smoothSections (n := n) (r := r) E) :
      J (A.smoothToSobolev 1 v) = h.smoothToL2 μ v := by
    change h.sobolevZeroEquivL2 (μ := μ) A
      (A.sobolevInclusion 1 0 (by norm_num) (A.smoothToSobolev 1 v)) = _
    rw [A.sobolevInclusion_smoothToSobolev, h.sobolevZeroEquivL2_smooth]
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
  -- Smooth right-hand sides in the exact closed graph have actual smooth preimages.
  have hlift (x : h.L2SectionSpace μ) (v : smoothSections (n := n) (r := q) F)
      (hx : (x, k.smoothToL2 μ v) ∈ L.graph) :
      ∃ w : smoothSections (n := n) (r := r) E,
        h.smoothToL2 μ w = x ∧ P.toLinearMap w = v := by
    rw [hgraph] at hx
    obtain ⟨u, hu⟩ := hx
    have hsolve : P.sobolevExtension A B 1 u = B.smoothToSobolev (1 - 1) v := by
      apply g.injective
      rw [hg]
      have hh := congrArg Prod.snd hu
      change R u = k.smoothToL2 μ v at hh
      rw [hRcompare] at hh
      exact hh
    obtain ⟨w, ⟨hw, hPw⟩, _⟩ :=
      P.existsUnique_smooth_lift_of_isElliptic A B hP 1 u v hsolve
    refine ⟨w, ?_, hPw⟩
    rw [← hJ, hw]
    exact congrArg Prod.fst hu
  have hsmooth (w : smoothSections (n := n) (r := r) E) :
      (h.smoothToL2 μ w, k.smoothToL2 μ (P.toLinearMap w)) ∈ L.graph := by
    rw [hgraph]
    exact ⟨A.smoothToSobolev 1 w, Prod.ext (hJ w) (hR w)⟩
  -- The restricted smooth inclusion is injective, and regularity makes it onto the full kernel.
  have hker (u : P.toLinearMap.ker) : h.smoothToL2 μ u.val ∈ L.ker := by
    have hh := hsmooth u.val
    rw [show P.toLinearMap u.val = 0 from u.property, map_zero] at hh
    obtain ⟨v, hv, hzero⟩ := L.mem_graph_iff.mp hh
    exact LinearPMap.mem_ker_iff.mpr ⟨v, hv.symm, hzero⟩
  let e₀ : P.toLinearMap.ker →ₗ[ℂ] L.ker :=
    ((h.smoothToL2 μ).comp P.toLinearMap.ker.subtype).codRestrict L.ker hker
  have he₀ : Function.Bijective e₀ := by
    constructor
    · intro u v huv
      apply Subtype.ext
      exact h.smoothToL2_injective μ (congrArg Subtype.val huv)
    · intro x
      obtain ⟨u, hu, hzero⟩ := LinearPMap.mem_ker_iff.mp x.property
      have hx : (x.val, k.smoothToL2 μ 0) ∈ L.graph := by
        rw [map_zero]
        exact L.mem_graph_iff.mpr ⟨u, hu.symm, hzero⟩
      obtain ⟨w, hw, hPw⟩ := hlift x.val 0 hx
      exact ⟨⟨w, hPw⟩, Subtype.ext hw⟩
  -- Smooth outputs lie in the actual closed range, so the same inclusion descends to its quotient.
  have hrange : P.toLinearMap.range ≤
      (L.toFun.range.mkQ.comp (k.smoothToL2 μ)).ker := by
    rintro _ ⟨w, rfl⟩
    change L.toFun.range.mkQ (k.smoothToL2 μ (P.toLinearMap w)) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact LinearPMap.mem_range_iff.mpr ⟨h.smoothToL2 μ w, hsmooth w⟩
  let f₀ : (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) →ₗ[ℂ]
      (k.L2SectionSpace μ ⧸ L.toFun.range) :=
    P.toLinearMap.range.liftQ (L.toFun.range.mkQ.comp (k.smoothToL2 μ)) hrange
  have hf₀ : Function.Bijective f₀ := by
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro z hz
      obtain ⟨v, rfl⟩ := P.toLinearMap.range.mkQ_surjective z
      have hv : k.smoothToL2 μ v ∈ L.toFun.range :=
        (Submodule.Quotient.mk_eq_zero _).mp hz
      obtain ⟨x, hx⟩ := LinearPMap.mem_range_iff.mp hv
      obtain ⟨w, _, hPw⟩ := hlift x v hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, hPw⟩
    · let H := k.L2SectionSpace μ
      let C := H ⧸ L.toFun.range
      have hFred := P.closed_range_finite_metricL2ClosedRealization h k hP
      let : IsClosed (L.toFun.range : Set H) := hFred.1
      let : FiniteDimensional ℂ C := hFred.2.2
      let proj : H →L[ℂ] C := ⟨L.toFun.range.mkQ, L.toFun.range.continuous_mkQ⟩
      have hdense : DenseRange (fun v ↦ proj (k.smoothToL2 μ v)) :=
        L.toFun.range.mkQ_surjective.denseRange.comp (k.denseRange_smoothToL2 μ) proj.continuous
      have hclosed : IsClosed (Set.range f₀) := f₀.range.closed_of_finiteDimensional
      have hsubset : Set.range (fun v ↦ proj (k.smoothToL2 μ v)) ⊆ Set.range f₀ := by
        rintro _ ⟨v, rfl⟩
        exact ⟨P.toLinearMap.range.mkQ v, rfl⟩
      intro z
      exact hclosed.closure_subset_iff.mpr hsubset (hdense z)
  exact ⟨LinearEquiv.ofBijective e₀ he₀, LinearEquiv.ofBijective f₀ hf₀,
    fun _ ↦ rfl, fun _ ↦ rfl⟩

end PseudodifferentialOperator

end AtiyahSinger
