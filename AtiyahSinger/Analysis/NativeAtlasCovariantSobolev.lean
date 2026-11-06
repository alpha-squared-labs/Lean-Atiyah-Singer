/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasCovariantSobolev
public import AtiyahSinger.Analysis.CovariantSobolev
public import AtiyahSinger.Analysis.NativeAtlasSobolev
public import AtiyahSinger.Analysis.NativeAtlasTensorCoordinates
public import AtiyahSinger.Geometry.NativeAtlasConnection
public import AtiyahSinger.Geometry.SmoothInvariantMetric

/-!
# Comparing native and atlas integer geometric norms

Public module ID: M0800.

A01: retain the same original bundle, section, metric, measure and tangent
connection. A native connection is represented in the existing atlas by its
actual first-derivative action; the two standard tensor recursions then agree.
This bridge compares constructions, not independently chosen Sobolev norms.
Sources: SG III.2 (2.1), with the standard coordinate expansion of the tensor
connection. These implementation comparisons are not additional book lemmas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped BigOperators Manifold ContDiff

set_option maxSynthPendingDepth 40

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
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [MeasurableSpace M]
  (μ : Measure M) (g : SmoothCotangentMetric (n := n) (M := M))
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (covT : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin n)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M)))
  (covE : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℂ (Fin r)) E)

variable [hT : T2Space M] [hSC : SecondCountableTopology M]
  (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)
  (hcovE : CovariantDerivative.ContMDiffCovariantDerivative covE ∞)
  (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E covE)

/-- The original metric has smooth Gram entries in the native atlas. -/
theorem SmoothHermitianMetric.isSmoothHermitianMetric_nativeAtlas :
    letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    (nativeSmoothComplexBundleAtlas (n := n) (r := r) E).IsSmoothHermitianMetric
      h.toContinuousHermitianMetric := by
  /- The retyped atlas frames are the same native frames followed by the
  standard finite-coordinate equivalence. Their inverse standard vectors
  therefore equal the original inverse-frame vectors. The continuous metric
  adapter retains exactly h.toCore, so its Gram entries are those already
  certified smooth by h. No norm, topology, pairing or chart is replaced. -/
  classical
  have _manifold := (inferInstance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
  have _measurable := (inferInstance : MeasurableSpace M)
  have _hausdorff := hT
  have _secondCountable := hSC
  let : TopologicalSpace (TotalSpace Unit E) :=
    ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  intro i a b
  let := i.property
  change Fin r at a b
  apply (h.contMDiffOn_gram i.val a b).congr
  intro x hx
  change (if hx' : x ∈ i.val.baseSet then
    (h.toCore x).inner
      (cast (congrArg E ((nativeFiniteBundleChart E i.val).proj_symm_apply' hx'))
        ((nativeFiniteBundleChart E i.val).toPartialEquiv.symm (x, Pi.single a 1)).snd)
      (cast (congrArg E ((nativeFiniteBundleChart E i.val).proj_symm_apply' hx'))
        ((nativeFiniteBundleChart E i.val).toPartialEquiv.symm (x, Pi.single b 1)).snd)
    else 0) = _
  rw [dite_eq_left hx]
  congr 1 <;> rw [i.val.symmL_apply hx, i.val.symm_apply hx] <;> rfl

include hT hSC hcovT hcovE hcomplex in
/-- The two tensor constructions give the same geometric norm for the same connection. -/
theorem nativeAtlas_covariantSobolevNorm_eq
    (L : SmoothBundlePresentation (n := n) (r := r) E)
    (k : ℕ) (u : smoothSections (n := n) (r := r) E) :
    letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ covA : AtlasComplexConnection (nativeSmoothComplexBundleAtlas (n := n) (r := r) E),
      (∀ (w : smoothSections (n := n) (r := r) E) (x : M)
        (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
        covA.covariantDerivative
          ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm w) x v =
          covE w.val x v) →
      L.toAtlasBundlePresentation.covariantSobolevNorm μ g h.toContinuousHermitianMetric
          covA covT k ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u) =
        covariantSobolevNorm μ g h covT covE k u := by
  classical
  have _secondCountable := hSC
  have _complex := hcomplex
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  intro covA hA
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let K : AtlasBundlePresentation A := L.toAtlasBundlePresentation
  change K.covariantSobolevNorm μ g h.toContinuousHermitianMetric covA covT k
      ((nativeSmoothSectionLinearEquiv E).symm u) = _
  unfold AtlasBundlePresentation.covariantSobolevNorm covariantSobolevNorm
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [] with x
  -- Every active partition weight uses a valid chart, whose tensor contraction is the native one.
  let value : ℝ := (iteratedCovariantPairing g h j.val x
    (iteratedCovariantDerivative covT covE j.val u.val x)
    (iteratedCovariantDerivative covT covE j.val u.val x)).re
  have hterm (a : Fin K.size) :
      K.cutoff a x * covA.localCovariantDerivativeNormSq covT (K.chart a)
        (K.chart_mem_atlas a) (K.frameIndex a) g h.toContinuousHermitianMetric j.val
          ((nativeSmoothSectionLinearEquiv E).symm u) x = K.cutoff a x * value := by
    by_cases hz : K.cutoff a x = 0
    · rw [hz, zero_mul, zero_mul]
    · have hx := K.support_subset a (subset_tsupport (K.cutoff a) hz)
      rw [nativeAtlas_localCovariantDerivativeNormSq_eq g h covT covE hcovT hcovE
        covA hA (K.chart a) (K.chart_mem_atlas a) (K.frameIndex a) u j.val x hx]
  -- The original partition sums to one; integrate this pointwise equality at every order.
  rw [Finset.sum_congr rfl (fun a _ ↦ hterm a), ← Finset.sum_mul, K.sum_cutoff x, one_mul]

end AtiyahSinger
