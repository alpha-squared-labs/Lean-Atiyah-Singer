/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianPowers

/-!
# Addition of the specified connection-Laplacian spectral powers

Public module ID: M0393.

The selected smooth powers form one additive family of linear equivalences.
The proof uses the actual partially defined spectral graphs and only bounded
nonnegative powers of the same inverse. A sufficiently large positive power
can be cancelled by injectivity even when zero belongs to its spectrum.

This is the group law needed to assemble real-order PDO identifications from
integer powers and powers in one fractional interval. No PDO realization or
bounded inverse for the compact inverse is assumed.
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

set_option maxHeartbeats 800000 in
-- The extended limit accommodates the original smooth spectral powers and addition of their real
-- orders.
/-- The specified smooth spectral powers compose by addition of their real orders. -/
theorem connectionLaplacianSmoothPower_add (a b : ℝ) :
    connectionLaplacianSmoothPower μ g h cov hcov hcomplex (a + b) =
      (connectionLaplacianSmoothPower μ g h cov hcov hcomplex b).trans
        (connectionLaplacianSmoothPower μ g h cov hcov hcomplex a) := by
  classical
  let H := h.L2SectionSpace μ
  let B := connectionLaplacianInverse μ g h cov hcov hcomplex
  let f := h.smoothToL2 μ
  let U := connectionLaplacianSmoothPower μ g h cov hcov hcomplex
  have hB := (connectionLaplacianInverse_properties μ g h cov hcov hcomplex).1
  have hzero : CFC.rpow B 0 = (1 : H →L[ℂ] H) := CFC.rpow_zero B hB
  -- Nonnegative powers obey the addition law at zero without a spectral gap for B.
  have hmul (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
      CFC.rpow B (s + t) = CFC.rpow B s * CFC.rpow B t := by
    rcases eq_or_lt_of_le hs with hs | hs
    · rw [← hs, zero_add, hzero, one_mul]
    rcases eq_or_lt_of_le ht with ht | ht
    · rw [← ht, add_zero, hzero, mul_one]
    let s' : NNReal := ⟨s, hs.le⟩
    let t' : NNReal := ⟨t, ht.le⟩
    have hs' : 0 < s' := hs
    have ht' : 0 < t' := ht
    have hsum := CFC.nnrpow_add (a := B) hs' ht'
    rw [CFC.nnrpow_eq_rpow (add_pos hs' ht'),
      CFC.nnrpow_eq_rpow hs', CFC.nnrpow_eq_rpow ht'] at hsum
    exact hsum
  -- The negative graph is the bounded CFC action on the same embedded section.
  have hnegative (l : ℝ) (hl : l ≤ 0)
      (u : smoothSections (n := n) (r := r) E) :
      f (U l u) = CFC.rpow B (-l / 2) (f u) := by
    have hg := connectionLaplacianSmoothPower_graph μ g h cov hcov hcomplex l u
    rw [connectionLaplacianSpectralPower, ite_eq_left hl] at hg
    obtain ⟨v, hv, hw⟩ := (LinearPMap.mem_graph_iff _).mp hg
    change (v : H) = f u at hv
    change CFC.rpow B (-l / 2) (v : H) = f (U l u) at hw
    rw [hv] at hw
    exact hw.symm
  -- Multiplying by a large bounded power converts every signed order to a bounded identity.
  have hshift (l k : ℝ) (hk : 0 ≤ k) (hkl : 0 ≤ k - l / 2)
      (u : smoothSections (n := n) (r := r) E) :
      CFC.rpow B k (f (U l u)) = CFC.rpow B (k - l / 2) (f u) := by
    by_cases hl : l ≤ 0
    · rw [hnegative l hl u]
      have hexp : k - l / 2 = k + (-l / 2) := by ring
      rw [hexp, hmul k (-l / 2) hk (by linarith)]
      rfl
    · have hlpos : 0 < l := lt_of_not_ge hl
      have hreciprocal : U (-l) = (U l).symm :=
        connectionLaplacianSmoothPower_neg μ g h cov hcov hcomplex l
      have hright := hnegative (-l) (by linarith) (U l u)
      rw [hreciprocal, LinearEquiv.symm_apply_apply, neg_neg] at hright
      have hexp : k = (k - l / 2) + l / 2 := by ring
      conv_lhs => rw [hexp, hmul (k - l / 2) (l / 2) hkl (by linarith)]
      change CFC.rpow B (k - l / 2) (CFC.rpow B (l / 2) (f (U l u))) = _
      rw [← hright]
  -- One common injective power compares the two graphs, including all choices of signs.
  let k : ℝ := |a| + |b| + 1
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hka : 0 ≤ k - a / 2 := by
    dsimp [k]
    linarith [le_abs_self a, abs_nonneg a, abs_nonneg b]
  have hkab : 0 ≤ (k - a / 2) - b / 2 := by
    dsimp [k]
    linarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  have he : (k - a / 2) - b / 2 = k - (a + b) / 2 := by ring
  have hks : 0 ≤ k - (a + b) / 2 := by rwa [← he]
  apply LinearEquiv.ext
  intro u
  apply h.smoothToL2_injective μ
  apply (connectionLaplacianInverse_rpow_properties μ g h cov hcov hcomplex k hk).2.1
  change CFC.rpow B k (f (U (a + b) u)) = CFC.rpow B k (f (U a (U b u)))
  rw [hshift (a + b) k hk hks, hshift a k hk hka,
    hshift b (k - a / 2) hka hkab, he]

end AtiyahSinger
