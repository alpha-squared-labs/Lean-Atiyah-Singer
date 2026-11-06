/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasFullSymbolParametrix
public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential

/-!
# Full ellipticity and smoothing in the original native and atlas models

Public module ID: M0802.

A04: the native fixed-rank model embeds into the locally varying-rank atlas
model by identity transport on original fiber values.
Quantitative ellipticity keeps the same real cotangent coordinates and the
same finite-dimensional coordinate norms. Smoothing retains the original
operator, all Sobolev presentations, and the native smooth positive density.

These comparisons let the full-symbol parametrix theorem consume the existing
native operators without changing their ellipticity hypothesis or replacing
their residuals. No homogeneous representative or additional norm is assumed.
Sources: SG III.3.15, III.3.18--3.19 and III.4.7, and the compact-local inverse
estimate in Taylor III.1.1. The comparisons are project model identifications,
not additional numbered textbook lemmas. Neither the full-symbol nor the smoothing
comparison assumes parametrix existence.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  {F : M → Type*} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]

/-- Full-symbol inverse bounds are identical in the original native and atlas frames. -/
theorem isEllipticFullAtlasSymbol_native_iff (m : ℝ)
    (p : GlobalSymbolFunction (n := n) E F) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    IsEllipticFullAtlasSymbol
      (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
      (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) m
      (nativeAtlasSymbolFunction p) ↔
        IsEllipticFullGlobalSymbol (r := r) (q := q) E F m p := by
  /- Stage 1: a native atlas index is exactly an original designated
  trivialization. Its actual frame map followed by the Euclidean coordinate
  conversion cancels the inverse conversion used by nativeAtlasSymbolFunction.
  The common chart domains and the coordinate symbol matrices agree.
  Stage 2: both conditions quantify the same compact subsets, radii,
  frequencies, inverse maps and coordinate operator norms. Hence their
  inverse estimates are literally the same estimates. No comparison of
  raw tangent norms or extra global metric is needed. In dimension zero
  both high-frequency conditions are vacuous, with no rank restriction. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  -- Each original frame retains its own base set after finite-coordinate conversion.
  have hcoord (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
      atlasGlobalSymbolInChart A B (nativeAtlasSymbolFunction p) c
          ⟨e, inferInstance⟩ ⟨f, inferInstance⟩ = globalSymbolInChart E F p c e f := by
    funext z η
    apply ContinuousLinearMap.ext
    intro v
    change EuclideanSpace ℂ (Fin r) at v
    have heBase : (A.chart ⟨e, inferInstance⟩).baseSet = e.baseSet := rfl
    have hfBase : (B.chart ⟨f, inferInstance⟩).baseSet = f.baseSet := rfl
    by_cases he : c.symm z ∈ e.baseSet
    · by_cases hf : c.symm z ∈ f.baseSet
      · have heFrame : A.frameLinearEquiv ⟨e, inferInstance⟩ (c.symm z) he =
            (e.continuousLinearEquivAt ℂ (c.symm z) he).toLinearEquiv.trans
              (EuclideanSpace.equiv (Fin r) ℂ).toLinearEquiv := by
          apply LinearEquiv.ext
          intro w
          rfl
        have hfFrame : B.frameLinearEquiv ⟨f, inferInstance⟩ (c.symm z) hf =
            (f.continuousLinearEquivAt ℂ (c.symm z) hf).toLinearEquiv.trans
              (EuclideanSpace.equiv (Fin q) ℂ).toLinearEquiv := by
          apply LinearEquiv.ext
          intro w
          rfl
        simp only [atlasGlobalSymbolInChart, heBase, hfBase, he, hf, and_self, dite_true]
        change (EuclideanSpace.equiv (Fin q) ℂ).symm
          ((B.frameLinearEquiv ⟨f, inferInstance⟩ (c.symm z) hf)
            (p (c.symm z) (covectorFromChart c (c.symm z) η)
              ((A.frameLinearEquiv ⟨e, inferInstance⟩ (c.symm z) he).symm
                ((EuclideanSpace.equiv (Fin r) ℂ) v)))) = _
        rw [heFrame, hfFrame]
        change (EuclideanSpace.equiv (Fin q) ℂ).symm
          ((EuclideanSpace.equiv (Fin q) ℂ)
            ((f.continuousLinearEquivAt ℂ (c.symm z) hf)
              (p (c.symm z) (covectorFromChart c (c.symm z) η)
                ((e.continuousLinearEquivAt ℂ (c.symm z) he).symm
                  ((EuclideanSpace.equiv (Fin r) ℂ).symm
                    ((EuclideanSpace.equiv (Fin r) ℂ) v)))))) =
          f.continuousLinearMapAt ℂ (c.symm z)
            (p (c.symm z) (covectorFromChart c (c.symm z) η)
              (e.symmL ℂ (c.symm z) v))
        rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
        change (f ⟨c.symm z, p (c.symm z) (covectorFromChart c (c.symm z) η)
          (e.symm (c.symm z) v)⟩).2 = _
        rw [e.symmL_apply he]
        exact (Trivialization.continuousLinearMapAt_apply_of_mem ℂ f hf _).symm
      · simp only [atlasGlobalSymbolInChart, heBase, hfBase, hf, and_false, dite_false]
        change (0 : EuclideanSpace ℂ (Fin q)) = f.continuousLinearMapAt ℂ (c.symm z)
          (p (c.symm z) (covectorFromChart c (c.symm z) η) (e.symmL ℂ (c.symm z) v))
        simp [Trivialization.continuousLinearMapAt, Trivialization.coe_linearMapAt, hf]
    · simp only [atlasGlobalSymbolInChart, heBase, hfBase, he, false_and, dite_false]
      change (0 : EuclideanSpace ℂ (Fin q)) = f.continuousLinearMapAt ℂ (c.symm z)
        (p (c.symm z) (covectorFromChart c (c.symm z) η) (e.symmL ℂ (c.symm z) v))
      rw [e.symmL_apply_of_notMem he, map_zero, map_zero]
  -- The native atlas indices are exactly the designated original frame pairs.
  constructor
  · intro hp c hc e f he hf
    have h := hp c hc ⟨e, he⟩ ⟨f, hf⟩
    rw [hcoord] at h
    exact h
  · intro hp c hc i j
    let := i.property
    let := j.property
    rcases i with ⟨e, he⟩
    rcases j with ⟨f, hf⟩
    change IsEllipticFullSymbol (atlasSymbolChartDomain A B c ⟨e, he⟩ ⟨f, hf⟩) m _
    rw [hcoord]
    exact hp c hc e f

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

set_option maxHeartbeats 1000000 in
-- The extended limit accommodates the atlas all-order and native smooth-kernel comparisons.
/-- The all-order atlas smoothing condition is the native smooth-kernel condition. -/
theorem isAtlasSmoothingOperator_native_iff
    (R : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    IsAtlasSmoothingOperator
      (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
      (nativeSmoothComplexBundleAtlas (n := n) (r := q) F)
      ((nativeSmoothSectionLinearEquiv (n := n) (r := q) F).symm.toLinearMap.comp
        (R.comp (nativeSmoothSectionLinearEquiv (n := n) (r := r) E).toLinearMap)) ↔
      IsSmoothingOperator (E := E) (F := F) μ R := by
  /- Stage 1: choose native presentations and their exact atlas isometries.
  For an arbitrary atlas presentation, use the already proved presentation
  equivalence on the same smooth sections. Thus the bounded extensions
  cover every presentation quantified by the smoothing predicate.
  Stage 2: transport the exact bounded extensions of the same section
  map R across those coordinate isometries. The native all-order smoothing
  characterization identifies the result with its smooth kernel for μ.
  The density is used only in this kernel characterization. Neither
  ellipticity nor diagonal action on connected components is required. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  obtain ⟨L₀⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨K₀⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  let e := nativeSmoothSectionLinearEquiv (n := n) (r := r) E
  let f := nativeSmoothSectionLinearEquiv (n := n) (r := q) F
  -- Test the forward implication on the same native presentations and exact isometries.
  constructor
  · intro hR
    apply (isSmoothingOperator_iff_sobolevExtensions μ R L₀ K₀).mpr
    intro s t
    obtain ⟨T, hT⟩ := hR L₀.toAtlasBundlePresentation K₀.toAtlasBundlePresentation s t
    let a := L₀.nativeAtlasSobolevEquiv s
    let b := K₀.nativeAtlasSobolevEquiv t
    refine ⟨b.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp a.toContinuousLinearEquiv.toContinuousLinearMap), ?_⟩
    intro u
    apply b.injective
    change b (b.symm (T (a (L₀.smoothToSobolev s u)))) = b (K₀.smoothToSobolev t (R u))
    rw [LinearIsometryEquiv.apply_symm_apply]
    change T (L₀.nativeAtlasSobolevEquiv s (L₀.smoothToSobolev s u)) =
      K₀.nativeAtlasSobolevEquiv t (K₀.smoothToSobolev t (R u))
    rw [L₀.nativeAtlasSobolevEquiv_smoothToSobolev,
      K₀.nativeAtlasSobolevEquiv_smoothToSobolev, hT]
    rfl
  · intro hR L K s t
    obtain ⟨T, hT⟩ := (isSmoothingOperator_iff_sobolevExtensions μ R L₀ K₀).mp hR s t
    let a := L₀.nativeAtlasSobolevEquiv s
    let b := K₀.nativeAtlasSobolevEquiv t
    -- Compare every requested atlas presentation with the same converted native ones.
    let J := a.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (L.sobolevEquiv L₀.toAtlasBundlePresentation s).toContinuousLinearMap
    let H := (K₀.toAtlasBundlePresentation.sobolevEquiv K t).toContinuousLinearMap.comp
      b.toContinuousLinearEquiv.toContinuousLinearMap
    refine ⟨H.comp (T.comp J), ?_⟩
    intro u
    have hJ : J (L.smoothToSobolev s u) = L₀.smoothToSobolev s (e u) := by
      change a.symm ((L.sobolevEquiv L₀.toAtlasBundlePresentation s)
        (L.smoothToSobolev s u)) = _
      rw [L.sobolevEquiv_smoothToSobolev]
      apply a.injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact (L₀.nativeAtlasSobolevEquiv_smoothToSobolev s (e u)).symm
    change H (T (J (L.smoothToSobolev s u))) = _
    rw [hJ, hT]
    change (K₀.toAtlasBundlePresentation.sobolevEquiv K t)
      (K₀.nativeAtlasSobolevEquiv t (K₀.smoothToSobolev t (R (e u)))) = _
    rw [K₀.nativeAtlasSobolevEquiv_smoothToSobolev,
      K₀.toAtlasBundlePresentation.sobolevEquiv_smoothToSobolev]
    rfl

namespace PseudodifferentialOperator

variable {μ} {m : ℝ}
  (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

/-- Transport of the original section operator preserves its full-symbol ellipticity. -/
theorem isElliptic_toAtlas_iff :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    P.toAtlasPseudodifferentialOperator.IsElliptic ↔ P.IsElliptic := by
  /- Stage 1: choose any representative of the original native principal
  quotient. Its nativeAtlasGlobalSymbol represents the principal class of
  the same transported operator by principalSymbol_toAtlasPseudodifferentialOperator.
  Stage 2: test both ellipticity predicates on these specified representatives.
  Lower-order invariance permits this fixed representative in both directions,
  even if the atlas existential originally selected another representative.
  Apply the exact coordinate comparison above. This does not assume that
  either representative is homogeneous or that the operator is invertible. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  -- Fix one actual representative before testing both existential ellipticity predicates.
  obtain ⟨p, hp⟩ := globalPrincipalSymbolClass_surjective E F m P.principalSymbol
  rw [P.toAtlasPseudodifferentialOperator.isElliptic_iff_of_principalSymbol_eq
    (nativeAtlasGlobalSymbol m p)
    (P.principalSymbol_toAtlasPseudodifferentialOperator p hp.symm)]
  rw [P.isElliptic_iff_of_principalSymbol_eq p hp.symm]
  exact isEllipticFullAtlasSymbol_native_iff m p.val

end PseudodifferentialOperator

end AtiyahSinger
