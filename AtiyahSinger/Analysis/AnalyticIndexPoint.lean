/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AnalyticIndex
public import AtiyahSinger.Analysis.PointIndex
public import AtiyahSinger.Geometry.SmoothSectionEvaluation

/-!
# Point normalization of the actual analytic-index homomorphism

Public module ID: M0080.

P09: SG III.13, Property 1 and its proof, pp.247--248. The comparison is fixed
by the actual zero-dimensional cotangent projection, a homeomorphism of the
base with a point, restriction from compact support to absolute K theory, and
the existing rank isomorphism. Equality of additive maps includes every class
and fixes the positive rank-one generator. The normalization uses elliptic
representatives and evaluates their smooth section operators at the unique base point.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [hT : T2Space M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- The point rank isomorphism using the actual cotangent projection and specified base map. -/
def cotangentKZeroPointEquivInt (hn : n = 0) (e : M ≃ₜ PUnit) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) ≃+ ℤ :=
  ((compactSupportKZeroHomeomorphEquiv
    ((cotangentProjectionHomeomorphOfDimZero hn).trans e)).trans
      (AddEquiv.ofBijective (compactSupportKZeroToAbsolute (X := PUnit))
        compactSupportKZeroToAbsolute_bijective)).trans complexKZeroPointEquivInt

variable [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hP : PreconnectedSpace M] [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT hSC hC hP hB hμ in
/-- SG Property 1: the analytic-index homomorphism on a point is the specified rank map. -/
theorem analyticIndex_eq_pointRank (hn : n = 0) (e : M ≃ₜ PUnit) :
    analyticIndex (n := n) μ = (cotangentKZeroPointEquivInt hn e).toAddMonoidHom := by
  classical
  let : Subsingleton M := e.injective.subsingleton
  let x₀ : M := e.symm PUnit.unit
  -- At this same base point, evaluation identifies the original smooth sections with the fiber.
  let sectionEquiv (E : SmoothFiniteComplexBundle (n := n) M) :
      smoothSections (n := n) (r := E.rank) E.Fiber ≃ₗ[ℂ] E.Fiber x₀ := by
    let ev : smoothSections (n := n) (r := E.rank) E.Fiber →ₗ[ℂ] E.Fiber x₀ :=
      { toFun := fun s ↦ s.val x₀
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    apply LinearEquiv.ofBijective ev
    constructor
    · intro s t hst
      apply Subtype.ext
      funext x
      have hx : x = x₀ := Subsingleton.elim _ _
      subst x
      exact hst
    · intro v
      exact exists_smoothSection_apply_eq x₀ v
  apply AddMonoidHom.ext
  intro u
  -- Evaluate the analytic map on a representative of the given original K class.
  obtain ⟨E, F, R, a, P, hp, hi, hclass⟩ :=
    exists_elliptic_pseudodifferential_representative_of_preconnected μ u 0
  rw [← hclass, PseudodifferentialOperator.analyticIndex_symbolKClassOfHomogeneous μ P R a hp hi]
  let p := cotangentProjectionHomeomorphOfDimZero (n := n) (M := M) hn
  let G := modelFiniteBundle (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let H := modelFiniteBundle (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let j : C(PUnit, M) := ⟨e.symm, e.symm.continuous⟩
  have hdim : compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback ⟨p.symm, p.symm.continuous⟩ p.symm.isProperMap
        (P.symbolKClassOfHomogeneous R a hp hi)) = G.kZeroClass - H.kZeroClass := by
    exact symbolKClass_of_dim_zero a.val
      a.property.1.continuous
      ((P.isElliptic_iff_homogeneous R a hp).mp hi) hn
  -- The specified cotangent projection and specified point map form the actual pullback square.
  have htransport (v : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
      compactSupportKZeroToAbsolute (compactSupportKZeroHomeomorphEquiv (p.trans e) v) =
        complexKZeroPullback j (compactSupportKZeroToAbsolute
          (compactSupportKZeroPullback ⟨p.symm, p.symm.continuous⟩ p.symm.isProperMap v)) := by
    change complexKZeroPullback ⟨((↑) : PUnit → OnePoint PUnit), OnePoint.continuous_coe⟩
      (complexKZeroPullback
        (properOnePointMap ⟨(p.trans e).symm, (p.trans e).symm.continuous⟩
          (p.trans e).symm.isProperMap) v.val) =
      complexKZeroPullback j
        (complexKZeroPullback ⟨((↑) : M → OnePoint M), OnePoint.continuous_coe⟩
          (complexKZeroPullback (properOnePointMap ⟨p.symm, p.symm.continuous⟩
            p.symm.isProperMap) v.val))
    simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := (G.pullback j).isFiniteRank
  let := (H.pullback j).isFiniteRank
  have hrank : (cotangentKZeroPointEquivInt hn e)
      (P.symbolKClassOfHomogeneous R a hp hi) =
        (Module.finrank ℂ (E.Fiber x₀) : ℤ) - Module.finrank ℂ (F.Fiber x₀) := by
    change complexKZeroPointEquivInt
      (compactSupportKZeroToAbsolute
        (compactSupportKZeroHomeomorphEquiv (p.trans e)
          (P.symbolKClassOfHomogeneous R a hp hi))) = _
    rw [htransport, hdim, map_sub, ← G.kZeroClass_pullback j, ← H.kZeroClass_pullback j]
    change complexKZeroRankAt PUnit.unit ((G.pullback j).kZeroClass -
      (H.pullback j).kZeroClass) = _
    rw [map_sub, FiniteBundle.kZeroClass, FiniteBundle.kZeroClass,
      ComplexBundle.rankAt_kZeroClass, ComplexBundle.rankAt_kZeroClass]
    have hG := ((modelFiniteBundleIso (EuclideanSpace ℂ (Fin E.rank))
      E.Fiber).linearEquiv x₀).finrank_eq
    have hH := ((modelFiniteBundleIso (EuclideanSpace ℂ (Fin F.rank))
      F.Fiber).linearEquiv x₀).finrank_eq
    change (Module.finrank ℂ (G.Fiber x₀) : ℤ) - Module.finrank ℂ (H.Fiber x₀) = _
    rw [← hG, ← hH]
  -- Finite-dimensional rank-nullity computes the index of this very section operator.
  let : FiniteDimensional ℂ (E.Fiber x₀) :=
    (trivializationAt (EuclideanSpace ℂ (Fin E.rank)) E.Fiber x₀).linearEquivAt
      ℂ x₀ (mem_baseSet_trivializationAt _ _ _)|>.symm.finiteDimensional
  let : FiniteDimensional ℂ (F.Fiber x₀) :=
    (trivializationAt (EuclideanSpace ℂ (Fin F.rank)) F.Fiber x₀).linearEquivAt
      ℂ x₀ (mem_baseSet_trivializationAt _ _ _)|>.symm.finiteDimensional
  let : FiniteDimensional ℂ (smoothSections (n := n) (r := E.rank) E.Fiber) :=
    (sectionEquiv E).symm.finiteDimensional
  let : FiniteDimensional ℂ (smoothSections (n := n) (r := F.rank) F.Fiber) :=
    (sectionEquiv F).symm.finiteDimensional
  rw [LinearMap.index_eq_of_finiteDimensional, (sectionEquiv E).finrank_eq,
    (sectionEquiv F).finrank_eq]
  exact hrank.symm

end AtiyahSinger
