/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialSymbol
public import AtiyahSinger.Analysis.GlobalPrincipalSymbol
public import AtiyahSinger.Analysis.NativeAtlasDifferentialOperator
public import AtiyahSinger.Analysis.NativeAtlasSobolev

import AtiyahSinger.Analysis.AtlasPseudodifferentialFiltration

/-!
# The original pseudodifferential operators in the atlas presentation

Public module ID: M0805.

D05: compare the native fixed-rank PDO and symbol constructions with the
locally finite-rank atlas construction. The section map is transported by
the identity on the original fiber values. A symbol keeps the original real
cotangent vector and complex-linear fiber action; only its continuity proof
is forgotten when passing to the algebraic Hom carrier.

The smoothing comparison uses all original finite presentations, not just
one chosen completion. Every frame in a native atlas is indexed by its
original designated frame, so any atlas presentation unwraps to a native
presentation with the same charts, cutoffs and Bessel coordinates. The
native smooth-kernel and all-order Sobolev characterization then applies.

Sources: Spin Geometry III.3, p.186 and Definition 3.15, for the smoothing
and PDO descriptions; III.3.18--3.19 for the quotient principal symbol.
The comparison retains the native compactness and positive-density
hypotheses; it makes no claim about a full homogeneous expansion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

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

/-- Forget only the fiberwise continuity certificate of the original symbol values. -/
def nativeAtlasSymbolFunction (p : GlobalSymbolFunction (n := n) E F) :
    AtlasSymbolFunction (n := n) E F :=
  fun x ξ ↦ (p x ξ).toLinearMap

/-- The original symbol estimates are exactly those tested by the native smooth atlases. -/
theorem isAtlasGlobalSymbol_native_iff (m : ℝ) (p : GlobalSymbolFunction (n := n) E F) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    IsAtlasGlobalSymbol
      (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
      (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) m
      (nativeAtlasSymbolFunction p) ↔
        IsGlobalSymbol (n := n) (r := r) (q := q) E F m p := by
  /- Stage 1: every index of a native atlas is exactly an original designated
  native frame. The frame domains agree, and the finite-product conversion
  cancels its Euclidean inverse in the atlas symbol coordinate formula.
  The new fiber map has exactly the original action on each vector and
  uses the same actual real cotangent vector covectorFromChart c x ξ.
  Stage 2: the two coordinate symbol functions therefore agree on the
  same open domain, so all their mixed derivatives and local symbol
  estimates agree. Quantifying all native frame pairs is the same as
  quantifying all atlas index pairs. No ellipticity or leading-term
  representative is involved, including at zero covectors and rank zero. -/
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
    change IsSymbol (atlasSymbolChartDomain A B c ⟨e, he⟩ ⟨f, hf⟩) m _
    rw [hcoord]
    exact hp c hc e f

/-- An original global symbol in the atlas symbol space, with its actual action unchanged. -/
def nativeAtlasGlobalSymbol (m : ℝ)
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    atlasGlobalSymbolSpace
      (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
      (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) m :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
  ⟨nativeAtlasSymbolFunction p.val, (isAtlasGlobalSymbol_native_iff m p.val).mpr p.property⟩

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

namespace BundleChartCutoff

variable {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
  (D : BundleChartCutoff (r := r) E c)

/-- Regard the specified native frame and cutoff as an atlas cutoff, with identical support. -/
def toAtlasChartCutoff :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    AtlasChartCutoff (nativeSmoothComplexBundleAtlas (n := n) (r := r) E) c :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  { frameIndex := ⟨D.frame, D.frame_mem_atlas⟩
    cutoff := D.cutoff
    smooth_cutoff := D.smooth_cutoff
    compact_support := D.compact_support
    support_subset := D.support_subset }

omit [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Native and atlas localization have the same Schwartz function in the original coordinates. -/
theorem localize_toAtlasChartCutoff (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (u : smoothSections (n := n) (r := r) E) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    D.toAtlasChartCutoff.localize hc
      ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u) = D.localize hc u := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  -- The finite-coordinate conversion cancels its inverse before the original cutoff acts.
  apply SchwartzMap.ext
  intro z
  change (if z ∈ c.target then (D.cutoff z : ℂ) •
    (EuclideanSpace.equiv (Fin r) ℂ).symm
      ((EuclideanSpace.equiv (Fin r) ℂ) (D.frame ⟨c.symm z, u.val (c.symm z)⟩).2)
    else 0) = _
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rfl

omit [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The two inverse-frame extensions retain every original fiber vector. -/
theorem extend_toAtlasChartCutoff (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    (nativeSmoothSectionLinearEquiv (n := n) (r := r) E)
      (D.toAtlasChartCutoff.extend hc v) = D.extend hc v := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := D.frame_mem_atlas
  apply Subtype.ext
  funext x
  -- Outside the original frame, support subordination forces the scalar cutoff to vanish.
  by_cases hx : x ∈ c.source
  · by_cases he : x ∈ D.frame.baseSet
    · have hframe : (nativeSmoothComplexBundleAtlas (n := n) (r := r) E).frameLinearEquiv
          ⟨D.frame, D.frame_mem_atlas⟩ x he =
          (D.frame.continuousLinearEquivAt ℂ x he).toLinearEquiv.trans
            (EuclideanSpace.equiv (Fin r) ℂ).toLinearEquiv := by
        apply LinearEquiv.ext
        intro w
        rfl
      change (if h : x ∈ c.source ∩ D.frame.baseSet then
        (D.cutoff (c x) : ℂ) •
          ((nativeSmoothComplexBundleAtlas (n := n) (r := r) E).frameLinearEquiv
            ⟨D.frame, D.frame_mem_atlas⟩ x h.2).symm
              ((EuclideanSpace.equiv (Fin r) ℂ) (v (c x))) else 0) =
        (if x ∈ c.source then (D.cutoff (c x) : ℂ) •
          D.frame.symmL ℂ x (v (c x)) else 0)
      simp only [Set.mem_inter_iff, hx, he, and_self, dite_true, ite_true, hframe]
      congr 1
      change (D.frame.continuousLinearEquivAt ℂ x he).symm
        ((EuclideanSpace.equiv (Fin r) ℂ).symm
          ((EuclideanSpace.equiv (Fin r) ℂ) (v (c x)))) = _
      rw [ContinuousLinearEquiv.symm_apply_apply,
        D.frame.symm_continuousLinearEquivAt_eq he]
    · have hz : D.cutoff (c x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        exact he (by simpa only [Set.mem_preimage, c.left_inv hx]
          using (D.support_subset hmem).2)
      change (if h : x ∈ c.source ∩ D.frame.baseSet then _ else 0) =
        (if x ∈ c.source then (D.cutoff (c x) : ℂ) • _ else 0)
      simp [hx, he, hz]
  · change (if h : x ∈ c.source ∩ D.frame.baseSet then _ else 0) =
      (if x ∈ c.source then _ else 0)
    simp [hx]

end BundleChartCutoff

namespace PseudodifferentialPiece

variable {m : ℝ} (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)

/-- Retain the actual native local Fourier operator in the native atlas model. -/
def toAtlasPseudodifferentialPiece :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    AtlasPseudodifferentialPiece
      (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
      (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) m :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
  { chart := L.chart
    chart_mem_atlas := L.chart_mem_atlas
    input := L.input.toAtlasChartCutoff
    output := L.output.toAtlasChartCutoff
    input_support_in_output_frame := L.input_support_in_output_frame
    output_support_in_input_frame := L.output_support_in_input_frame
    operator := L.operator
    symbol := L.symbol
    isSymbol := L.isSymbol
    operator_apply := L.operator_apply }

omit [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The converted piece acts on exactly the same original smooth section. -/
theorem toLinearMap_toAtlasPseudodifferentialPiece
    (u : smoothSections (n := n) (r := r) E) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    (nativeSmoothSectionLinearEquiv (n := n) (r := q) F)
      (L.toAtlasPseudodifferentialPiece.toLinearMap
        ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u)) =
          L.toLinearMap u := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  -- First cancel localization, then the identical inverse frame in extension.
  change (nativeSmoothSectionLinearEquiv (n := n) (r := q) F)
    (L.output.toAtlasChartCutoff.extend L.chart_mem_atlas
      (L.operator (L.input.toAtlasChartCutoff.localize L.chart_mem_atlas
        ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u)))) = _
  rw [L.input.localize_toAtlasChartCutoff, L.output.extend_toAtlasChartCutoff]
  rfl

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The converted piece symbol retains its original cotangent vector and fiber action. -/
theorem globalSymbolFunction_toAtlasPseudodifferentialPiece :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    L.toAtlasPseudodifferentialPiece.globalSymbolFunction =
      nativeAtlasSymbolFunction L.globalSymbolFunction := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  funext x ξ
  apply LinearMap.ext
  intro v
  by_cases hx : x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
  · have hA : A.frameLinearEquiv ⟨L.input.frame, L.input.frame_mem_atlas⟩ x hx.1.2 =
        (L.input.frame.continuousLinearEquivAt ℂ x hx.1.2).toLinearEquiv.trans
          (EuclideanSpace.equiv (Fin r) ℂ).toLinearEquiv := by
      apply LinearEquiv.ext
      intro w
      rfl
    have hB : B.frameLinearEquiv ⟨L.output.frame, L.output.frame_mem_atlas⟩ x hx.2 =
        (L.output.frame.continuousLinearEquivAt ℂ x hx.2).toLinearEquiv.trans
          (EuclideanSpace.equiv (Fin q) ℂ).toLinearEquiv := by
      apply LinearEquiv.ext
      intro w
      rfl
    -- Both descriptions keep the same two scalar cutoffs before the frame conversions cancel.
    change ((if h : x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet then
      ((L.output.cutoff (L.chart x) * L.input.cutoff (L.chart x) : ℝ) : ℂ) •
        ((B.frameLinearEquiv ⟨L.output.frame, L.output.frame_mem_atlas⟩ x h.2).symm.toLinearMap.comp
          (EuclideanSpace.equiv (Fin q) ℂ).toLinearMap).comp
            ((L.symbol (L.chart x) (covectorInChart L.chart x ξ)).toLinearMap.comp
              ((EuclideanSpace.equiv (Fin r) ℂ).symm.toLinearMap.comp
                (A.frameLinearEquiv ⟨L.input.frame, L.input.frame_mem_atlas⟩ x h.1.2).toLinearMap))
      else 0) v) = ((if x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet then
        ((L.output.cutoff (L.chart x) * L.input.cutoff (L.chart x) : ℝ) : ℂ) •
          (L.output.frame.symmL ℂ x).comp
            ((L.symbol (L.chart x) (covectorInChart L.chart x ξ)).comp
              (L.input.frame.continuousLinearMapAt ℂ x)) else 0) v)
    simp only [dite_eq_left hx, ite_eq_left hx, hA, hB]
    change ((L.output.cutoff (L.chart x) * L.input.cutoff (L.chart x) : ℝ) : ℂ) •
      (L.output.frame.continuousLinearEquivAt ℂ x hx.2).symm
        ((EuclideanSpace.equiv (Fin q) ℂ).symm
          ((EuclideanSpace.equiv (Fin q) ℂ)
            (L.symbol (L.chart x) (covectorInChart L.chart x ξ)
              ((EuclideanSpace.equiv (Fin r) ℂ).symm
                ((EuclideanSpace.equiv (Fin r) ℂ)
                  (L.input.frame.continuousLinearEquivAt ℂ x hx.1.2 v)))))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply,
      L.output.frame.symm_continuousLinearEquivAt_eq hx.2,
      L.input.frame.coe_continuousLinearEquivAt_eq hx.1.2]
    rfl
  · change ((if h : x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
      then _ else (0 : E x →ₗ[ℂ] F x)) v) =
        ((if x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
          then _ else (0 : E x →L[ℂ] F x)) v)
    simp [hx]

end PseudodifferentialPiece

set_option maxHeartbeats 1400000 in
-- The extended limit accommodates the native bundle conjugation and original smooth-section
-- transport.
/-- The original PDO class is unchanged by the identity transport of actual smooth sections. -/
theorem isAtlasPseudodifferentialOperator_native_iff (m : ℝ)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    IsAtlasPseudodifferentialOperator
      (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
      (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) m
      ((nativeSmoothSectionLinearEquiv (n := n) (r := q) F).symm.toLinearMap.comp
        (P.comp (nativeSmoothSectionLinearEquiv (n := n) (r := r) E).toLinearMap)) ↔
      IsPseudodifferentialOperator E F μ m P := by
  /- Stage 1: convert each finite local piece in either direction by keeping
  its original manifold chart, two native frames, two cutoffs, Schwartz
  operator and full symbol. Frame indices package exactly those original
  frames. The canonical coordinate equivalences cancel, and the shared
  inverse-frame map retains each original fiber vector. Thus both pieces
  have exactly the same section action after the stated transport.
  Stage 2: for an arbitrary atlas finite presentation, unwrap every frame
  index to its original native frame. Retain every chart, cutoff and
  partition certificate. The same coordinate cancellation identifies
  the Bessel maps and hence their closed Hilbert ranges isometrically.
  This covers all presentations quantified by IsAtlasSmoothingOperator;
  a single chosen native-to-atlas isometry alone would not suffice.
  Stage 3: apply isSmoothingOperator_iff_sobolevExtensions on the native
  side and transport the exact extensions through those isometries.
  Conversely, choose native presentations and use their converted ones
  in the atlas predicate. The original positive density supplies the
  native kernel characterization. Apply this to the same remainder after
  the finite sum. No support restriction is imposed on that remainder,
  so it may couple distinct connected components and may be nonzero
  in dimension zero. Both directions retain the original map P. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  let e := nativeSmoothSectionLinearEquiv (n := n) (r := r) E
  let f := nativeSmoothSectionLinearEquiv (n := n) (r := q) F
  -- All-order smoothing is transported on every original Sobolev presentation.
  have hsmooth (R : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F) :
      IsAtlasSmoothingOperator A B
        (f.symm.toLinearMap.comp (R.comp e.toLinearMap)) ↔ IsSmoothingOperator μ R := by
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
  -- Every atlas index here is an original frame; no replacement chart or symbol is chosen.
  have hsurj : Function.Surjective
      (fun L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m ↦
        L.toAtlasPseudodifferentialPiece) := by
    intro L
    let D : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
      { chart := L.chart
        chart_mem_atlas := L.chart_mem_atlas
        input :=
          { frame := L.input.frameIndex.val
            frame_mem_atlas := L.input.frameIndex.property
            cutoff := L.input.cutoff
            smooth_cutoff := L.input.smooth_cutoff
            compact_support := L.input.compact_support
            support_subset := L.input.support_subset }
        output :=
          { frame := L.output.frameIndex.val
            frame_mem_atlas := L.output.frameIndex.property
            cutoff := L.output.cutoff
            smooth_cutoff := L.output.smooth_cutoff
            compact_support := L.output.compact_support
            support_subset := L.output.support_subset }
        input_support_in_output_frame := L.input_support_in_output_frame
        output_support_in_input_frame := L.output_support_in_input_frame
        operator := L.operator
        symbol := L.symbol
        isSymbol := L.isSymbol
        operator_apply := L.operator_apply }
    exact ⟨D, rfl⟩
  have hmap (N : ℕ) (L : Fin N → PseudodifferentialPiece E F m) :
      f.symm.toLinearMap.comp ((P - ∑ j, (L j).toLinearMap).comp e.toLinearMap) =
        f.symm.toLinearMap.comp (P.comp e.toLinearMap) -
          ∑ j, (L j).toAtlasPseudodifferentialPiece.toLinearMap := by
    apply LinearMap.ext
    intro u
    apply f.injective
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, map_sub, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact ((L j).toLinearMap_toAtlasPseudodifferentialPiece (e u)).symm
  -- Convert the same finite family and exactly the same remainder in each direction.
  constructor
  · rintro ⟨N, L, hL⟩
    choose D hD using fun j ↦ hsurj (L j)
    refine ⟨N, D, (hsmooth _).mp ?_⟩
    rw [hmap]
    simpa only [hD] using hL
  · rintro ⟨N, L, hL⟩
    refine ⟨N, fun j ↦ (L j).toAtlasPseudodifferentialPiece, ?_⟩
    rw [← hmap]
    exact (hsmooth _).mpr hL


namespace PseudodifferentialOperator

variable {μ} {m : ℝ}
  (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

/-- The original PDO transported by the literal identity on each original section value. -/
def toAtlasPseudodifferentialOperator :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    AtlasPseudodifferentialOperator
      (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
      (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) m :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
  { toLinearMap :=
      (nativeSmoothSectionLinearEquiv (n := n) (r := q) F).symm.toLinearMap.comp
        (P.toLinearMap.comp (nativeSmoothSectionLinearEquiv (n := n) (r := r) E).toLinearMap)
    isPseudodifferentialOperator :=
      (isAtlasPseudodifferentialOperator_native_iff μ m P.toLinearMap).mpr
        P.isPseudodifferentialOperator }

/-- Every specified native principal representative gives the same atlas principal class. -/
theorem principalSymbol_toAtlasPseudodifferentialOperator
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (h : P.principalSymbol = globalPrincipalSymbolClass E F m p) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    P.toAtlasPseudodifferentialOperator.principalSymbol =
      atlasGlobalPrincipalSymbolClass
        (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
        (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) m
        (nativeAtlasGlobalSymbol m p) := by
  /- Stage 1: take one native finite representation of P modulo its actual
  smooth remainder. Convert that same family and remainder as in the
  membership equivalence. The atlas principal-symbol representation
  theorem gives the sum of its actual transported local global symbols.
  Stage 2: each converted piece symbol acts on the same original real
  cotangent vectors and original complex fiber vectors. Hence this
  sum is the image of the native representative sum under the explicit
  pointwise map nativeAtlasSymbolFunction.
  Stage 3: h says that the native sum minus p has order m-1. Apply the
  native symbol-membership equivalence at this lower order; linearity
  of forgetting the continuity proof preserves that same difference.
  The atlas quotient therefore identifies the sum with the displayed
  class. This works for any p satisfying h, without selecting a second
  representative or claiming pointwise equality of quotient elements. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  let e := nativeSmoothSectionLinearEquiv (n := n) (r := r) E
  let f := nativeSmoothSectionLinearEquiv (n := n) (r := q) F
  obtain ⟨N, L, hL⟩ := P.isPseudodifferentialOperator
  -- Use exactly the original finite representation and its same transported remainder.
  have hmap :
      f.symm.toLinearMap.comp
        ((P.toLinearMap - ∑ j, (L j).toLinearMap).comp e.toLinearMap) =
      P.toAtlasPseudodifferentialOperator.toLinearMap -
        ∑ j, (L j).toAtlasPseudodifferentialPiece.toLinearMap := by
    apply LinearMap.ext
    intro u
    apply f.injective
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, map_sub, map_sum]
    change P.toLinearMap (e u) - ∑ j, (L j).toLinearMap (e u) =
      P.toLinearMap (e u) - ∑ j, f ((L j).toAtlasPseudodifferentialPiece.toLinearMap u)
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [e, f, LinearEquiv.symm_apply_apply] using
      ((L j).toLinearMap_toAtlasPseudodifferentialPiece (e u)).symm
  have hR : IsAtlasSmoothingOperator A B
      (P.toAtlasPseudodifferentialOperator.toLinearMap -
        ∑ j, (L j).toAtlasPseudodifferentialPiece.toLinearMap) := by
    rw [← hmap]
    apply (isAtlasSmoothingOperator_iff_forall_isAtlasPseudodifferentialOperator A B _).mpr
    intro l
    exact (isAtlasPseudodifferentialOperator_native_iff μ l _).mpr
      (hL.isPseudodifferentialOperator l _)
  rw [P.toAtlasPseudodifferentialOperator.principalSymbol_eq_of_representation N
    (fun j ↦ (L j).toAtlasPseudodifferentialPiece) hR]
  apply (atlasGlobalPrincipalSymbolClass_eq_iff A B m _ _).mpr
  -- Equality in the native quotient gives the precise lower-order difference.
  have hnative := (globalPrincipalSymbolClass_eq_iff E F m _ p).mp
    ((P.principalSymbol_eq_of_representation N L hL).symm.trans h)
  have hatlas := (isAtlasGlobalSymbol_native_iff (m - 1) _).mpr hnative
  convert hatlas using 1
  funext x ξ
  apply LinearMap.ext
  intro v
  simp only [Submodule.coe_sum, Pi.sub_apply, Finset.sum_apply,
    nativeAtlasGlobalSymbol, nativeAtlasSymbolFunction, LinearMap.sub_apply,
    LinearMap.sum_apply, ContinuousLinearMap.coe_coe, sub_apply, sum_apply]
  change (∑ j, (L j).toAtlasPseudodifferentialPiece.globalSymbolFunction x ξ v) -
      (p.val x ξ) v = (∑ j, (L j).globalSymbolFunction x ξ v) - (p.val x ξ) v
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [(L j).globalSymbolFunction_toAtlasPseudodifferentialPiece]
  rfl

end PseudodifferentialOperator

end AtiyahSinger
