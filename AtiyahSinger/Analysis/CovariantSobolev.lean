/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSobolev
public import AtiyahSinger.Analysis.NativeAtlasSobolev
public import AtiyahSinger.Analysis.NativeAtlasTensorCoordinates
public import AtiyahSinger.Geometry.IteratedCovariantDerivative
public import AtiyahSinger.Geometry.HermitianPairing
public import AtiyahSinger.Geometry.NativeAtlasConnection

/-!
# Integer Sobolev norms from the original iterated covariant derivative

Public module ID: M0427.

A01, SG III.2 (2.1) and Proposition 2.14. The geometric norm sums integrals
of the squared lengths of the actual tensors nabla^j u for j = 0 through k.
It retains the specified tangent and bundle connections, cotangent metric,
Hermitian metric and positive measure. Full covariant tensors have no
alternating-form factorial normalization.

For smooth connections with a complex-linear value connection, the norm is
equivalent to the Fourier norm from the specified finite presentation. The
comparison is a two-sided estimate: Fourier convention, frames, cutoffs, density,
metrics and connections affect its constants. This norm comparison requires
no torsion-free, unitary or metric-compatible connection hypothesis.
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

/-- The integer geometric Sobolev norm, using every actual derivative through order k. -/
def covariantSobolevNorm (k : ℕ) (u : smoothSections (n := n) (r := r) E) : ℝ :=
  Real.sqrt (∑ j : Fin (k + 1), ∫ x,
    (iteratedCovariantPairing (n := n) (r := r) (E := E) g h j.val x
      (iteratedCovariantDerivative covT covE j.val u.val x)
      (iteratedCovariantDerivative covT covE j.val u.val x)).re ∂μ)

variable [hT : T2Space M] [hSC : SecondCountableTopology M] [hB : BorelSpace M]
  [hμ : IsSmoothPositiveMeasure (n := n) μ]
  (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)
  (hcovE : CovariantDerivative.ContMDiffCovariantDerivative covE ∞)
  (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E covE)
  (L : SmoothBundlePresentation (n := n) (r := r) E)

include hT hSC hB hμ hcovT hcovE hcomplex

set_option maxHeartbeats 1000000 in
-- Compare the original tensor integrals and Fourier coordinates through the same native atlas.
/-- SG III.2.14: the integer Fourier norm and the actual geometric norm are equivalent. -/
theorem exists_covariantSobolevNorm_comparison (k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ u : smoothSections (n := n) (r := r) E,
        c * ‖L.smoothToSobolev (k : ℝ) u‖ ≤
          covariantSobolevNorm μ g h covT covE k u ∧
        covariantSobolevNorm μ g h covT covE k u ≤
          C * ‖L.smoothToSobolev (k : ℝ) u‖ := by
  /- The finite original partition first proves compactness. Apply the atlas
  comparison with the native connection having the same section action, then
  transfer both actual norms: coordinate contraction identifies the geometric
  integral, and the native-atlas isometry preserves the original Fourier norm.
  The triangular derivative estimates and Fourier normalization are supplied
  by that atlas comparison, rather than reproved in this transport argument. -/
  classical
  -- The given finite compactly supported partition makes the original base compact.
  have hcompact : IsCompact (Set.univ : Set M) := by
    have hcover : (Set.univ : Set M) = ⋃ a : Fin L.size, tsupport (L.cutoff a) := by
      apply Set.Subset.antisymm
      · intro x _
        have hex : ∃ a : Fin L.size, L.cutoff a x ≠ 0 := by
          by_contra hn
          push Not at hn
          have hs := L.sum_cutoff x
          simp only [hn, Finset.sum_const_zero] at hs
          exact zero_ne_one hs
        obtain ⟨a, ha⟩ := hex
        exact Set.mem_iUnion.mpr ⟨a, subset_tsupport (L.cutoff a) ha⟩
      · exact Set.subset_univ _
    rw [hcover]
    exact isCompact_iUnion (fun a ↦ L.compact_support a)
  let : CompactSpace M := ⟨hcompact⟩
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let K : AtlasBundlePresentation A := L.toAtlasBundlePresentation
  obtain ⟨covA, hA⟩ := exists_atlasComplexConnection_native covE hcovE hcomplex
  -- The converted metric has the same Gram entries in the same original native frames.
  have hh : A.IsSmoothHermitianMetric h.toContinuousHermitianMetric := by
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
  obtain ⟨c, C, hc, hC, hbound⟩ := K.exists_covariantSobolevNorm_comparison
    μ g h.toContinuousHermitianMetric covA covT hcovT hh k
  refine ⟨c, C, hc, hC, ?_⟩
  intro u
  let v := (nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u
  -- Pointwise tensor coordinates identify the geometric integral with the original recursion.
  have hnorm : K.covariantSobolevNorm μ g h.toContinuousHermitianMetric covA covT k v =
      covariantSobolevNorm μ g h covT covE k u := by
    unfold AtlasBundlePresentation.covariantSobolevNorm covariantSobolevNorm
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [] with x
    let value : ℝ := (iteratedCovariantPairing g h j.val x
      (iteratedCovariantDerivative covT covE j.val u.val x)
      (iteratedCovariantDerivative covT covE j.val u.val x)).re
    have hterm (a : Fin K.size) :
        K.cutoff a x * covA.localCovariantDerivativeNormSq covT (K.chart a)
          (K.chart_mem_atlas a) (K.frameIndex a) g h.toContinuousHermitianMetric j.val v x =
          K.cutoff a x * value := by
      by_cases hz : K.cutoff a x = 0
      · rw [hz, zero_mul, zero_mul]
      · have hx := K.support_subset a (subset_tsupport (K.cutoff a) hz)
        rw [nativeAtlas_localCovariantDerivativeNormSq_eq g h covT covE hcovT hcovE
          covA hA (K.chart a) (K.chart_mem_atlas a) (K.frameIndex a) u j.val x hx]
    rw [Finset.sum_congr rfl (fun a _ ↦ hterm a), ← Finset.sum_mul, K.sum_cutoff x, one_mul]
  -- The native-atlas isometry keeps the exact Fourier coordinates, hence their norms.
  have hfourier : ‖K.smoothToSobolev (k : ℝ) v‖ = ‖L.smoothToSobolev (k : ℝ) u‖ := by
    rw [← L.nativeAtlasSobolevEquiv_smoothToSobolev (k : ℝ) u]
    exact (L.nativeAtlasSobolevEquiv (k : ℝ)).norm_map _
  simpa only [hnorm, hfourier] using hbound v

end AtiyahSinger
