/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.BoundedEllipticInverse
public import AtiyahSinger.Analysis.ConnectionLaplacianPowers

/-!
# Integer powers of the specified connection Laplacian are PDOs

Public module ID: M0388.

The original smooth spectral action of `(1 + ∇*∇)^z` is a pseudodifferential
operator of order `2*z` for every integer `z`. Negative integer powers are
identified with powers of the same bounded inverse on the original metric L²
completion. Bounded-inverse recognition gives a PDO of order minus two for its
actual smooth action. Positive integer powers are identified through the original
reciprocal spectral graphs, and composition gives the prescribed order bounds.

Sources: SG III.13, p.247, for the connection-Laplacian power construction;
the inverse recognition and explicit spectral-graph comparison are project
supplements. This integer argument does not use a fractional PDO theorem.
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

set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the spectral integer powers and their original PDO orders.
/-- Every original smooth integer spectral power has its expected PDO order. -/
theorem isPseudodifferentialOperator_connectionLaplacianSmoothPower_int (z : ℤ) :
    IsPseudodifferentialOperator E E μ (2 * (z : ℝ))
      (connectionLaplacianSmoothPower μ g h cov hcov hcomplex (2 * (z : ℝ))).toLinearMap := by
  classical
  let H := h.L2SectionSpace μ
  let B := connectionLaplacianInverse μ g h cov hcov hcomplex
  let f := h.smoothToL2 μ
  let U := connectionLaplacianSmoothPower μ g h cov hcov hcomplex
  have hB := (connectionLaplacianInverse_properties μ g h cov hcov hcomplex).1
  have hBinj := (connectionLaplacianInverse_properties μ g h cov hcov hcomplex).2.1
  -- The actual negative spectral graph is exactly the bounded integer power of B.
  have hnegative (k : ℕ) (u : smoothSections (n := n) (r := r) E) :
      f (U (-(2 * (k : ℝ))) u) = (B ^ k) (f u) := by
    have hg := connectionLaplacianSmoothPower_graph μ g h cov hcov hcomplex
      (-(2 * (k : ℝ))) u
    have hsign : -(2 * (k : ℝ)) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg k))
    have hexp : -(-(2 * (k : ℝ))) / 2 = (k : ℝ) := by ring
    rw [connectionLaplacianSpectralPower, ite_eq_left hsign, hexp] at hg
    change (f u, f (U (-(2 * (k : ℝ))) u)) ∈
      ((CFC.rpow B (k : ℝ)).toLinearMap.toPMap ⊤).graph at hg
    have hnat : CFC.rpow B (k : ℝ) = B ^ k := CFC.rpow_natCast B k hB
    rw [hnat] at hg
    obtain ⟨x, hx, hy⟩ := (LinearPMap.mem_graph_iff _).mp hg
    change (x : H) = f u at hx
    change (B ^ k) (x : H) = f (U (-(2 * (k : ℝ))) u) at hy
    rw [hx] at hy
    exact hy.symm
  have hpowinj (k : ℕ) : Function.Injective ((B ^ k : H →L[ℂ] H) : H → H) := by
    induction k with
    | zero => exact Function.injective_id
    | succ k hk =>
      intro x y hxy
      rw [pow_succ'] at hxy
      change B ((B ^ k) x) = B ((B ^ k) y) at hxy
      exact hk (hBinj hxy)
  obtain ⟨P, hP, hPel⟩ := exists_connectionLaplacianPositivePDO μ g h cov hcov hcomplex
  -- The original smooth graph sits in its closure, so B inverts this very positive PDO.
  have hBP (u : smoothSections (n := n) (r := r) E) :
      B (f (P.toLinearMap u)) = f u := by
    apply (connectionLaplacianInverse_graph μ g h cov hcov hcomplex _ _).mp
    let A := connectionLaplacianSmoothCore μ g h cov hcov hcomplex
    apply LinearPMap.le_graph_of_le A.le_closure
    let e := LinearEquiv.ofInjective f (h.smoothToL2_injective μ)
    refine A.mem_graph_iff.mpr ⟨e u, rfl, ?_⟩
    change f (e.symm (e u) + (connectionLaplacian μ g h cov hcov hcomplex).toLinearMap
      (e.symm (e u))) = f (P.toLinearMap u)
    rw [e.symm_apply_apply, hP]
    rfl
  let L : h.SmoothL2Section μ →ₗ[ℂ] h.SmoothL2Section μ := (U (-2)).toLinearMap
  have hLaction (u : h.SmoothL2Section μ) : f (L u) = B (f u) := by
    change f (U (-2) u) = B (f u)
    have hneg := hnegative 1 u
    norm_num only [Nat.cast_one, mul_one, pow_one] at hneg
    exact hneg
  have hnorm (u : h.SmoothL2Section μ) : ‖f u‖ = ‖u‖ :=
    UniformSpace.Completion.norm_coe u
  have hLbound (u : h.SmoothL2Section μ) : ‖L u‖ ≤ ‖B‖ * ‖u‖ := by
    rw [← hnorm (L u), hLaction, ← hnorm u]
    exact B.le_opNorm (f u)
  let G : h.SmoothL2Section μ →L[ℂ] h.SmoothL2Section μ :=
    L.mkContinuous ‖B‖ hLbound
  have hGP (u : h.SmoothL2Section μ) : G (P.toLinearMap u) = u := by
    apply h.smoothToL2_injective μ
    change f (L (P.toLinearMap u)) = f u
    exact (hLaction (P.toLinearMap u)).trans (hBP u)
  have hPG (u : h.SmoothL2Section μ) : P.toLinearMap (G u) = u := by
    apply h.smoothToL2_injective μ
    apply hBinj
    change B (f (P.toLinearMap (L u))) = B (f u)
    exact (hBP (L u)).trans (hLaction u)
  obtain ⟨S⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  have hLpdo : IsPseudodifferentialOperator E E μ (-2) L :=
    P.isPseudodifferentialOperator_of_bounded_inverse h h S S hPel G hGP hPG
  -- Compare both integer iterates through the same injective completion and inverse B.
  have hLpow (k : ℕ) (u : h.SmoothL2Section μ) :
      f ((L ^ k) u) = (B ^ k) (f u) := by
    induction k with
    | zero => rfl
    | succ k hk =>
      rw [pow_succ' L k, pow_succ' B k]
      change f (L ((L ^ k) u)) = B ((B ^ k) (f u))
      rw [hLaction, hk]
  have hPpow (k : ℕ) (u : smoothSections (n := n) (r := r) E) :
      (B ^ k) (f ((P.toLinearMap ^ k) u)) = f u := by
    induction k with
    | zero => rfl
    | succ k hk =>
      rw [pow_succ B k, pow_succ' P.toLinearMap k]
      change (B ^ k) (B (f (P.toLinearMap ((P.toLinearMap ^ k) u)))) = f u
      rw [hBP, hk]
  have hnegativeMap (k : ℕ) : (U (-(2 * (k : ℝ)))).toLinearMap = L ^ k := by
    apply LinearMap.ext
    intro u
    apply h.smoothToL2_injective μ
    exact (hnegative k u).trans (hLpow k u).symm
  have hpositive (k : ℕ) (u : smoothSections (n := n) (r := r) E) :
      (B ^ k) (f (U (2 * (k : ℝ)) u)) = f u := by
    have hneg := hnegative k (U (2 * (k : ℝ)) u)
    have hreciprocal : U (-(2 * (k : ℝ))) = (U (2 * (k : ℝ))).symm :=
      connectionLaplacianSmoothPower_neg μ g h cov hcov hcomplex (2 * (k : ℝ))
    rw [hreciprocal, LinearEquiv.symm_apply_apply] at hneg
    exact hneg.symm
  have hpositiveMap (k : ℕ) :
      (U (2 * (k : ℝ))).toLinearMap = P.toLinearMap ^ k := by
    apply LinearMap.ext
    intro u
    apply h.smoothToL2_injective μ
    apply hpowinj k
    exact (hpositive k u).trans (hPpow k u).symm
  -- Composition gives each integer order; no fractional PDO assertion is used.
  have hPDO_pow (m : ℝ)
      (Q : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := r) E)
      (hQ : IsPseudodifferentialOperator E E μ m Q) (k : ℕ) :
      IsPseudodifferentialOperator E E μ (m * (k : ℝ)) (Q ^ k) := by
    induction k with
    | zero =>
      rw [Nat.cast_zero, mul_zero, pow_zero]
      change IsPseudodifferentialOperator E E μ 0 LinearMap.id
      exact isPseudodifferentialOperator_id μ
    | succ k hk =>
      have hord : m * ((k + 1 : ℕ) : ℝ) = m + m * (k : ℝ) := by push_cast; ring
      rw [hord, pow_succ']
      exact IsPseudodifferentialOperator.comp Q (Q ^ k) hQ hk
  change IsPseudodifferentialOperator E E μ (2 * (z : ℝ)) (U (2 * (z : ℝ))).toLinearMap
  cases z with
  | ofNat k =>
    change IsPseudodifferentialOperator E E μ (2 * (k : ℝ))
      (U (2 * (k : ℝ))).toLinearMap
    rw [hpositiveMap]
    exact hPDO_pow 2 P.toLinearMap P.isPseudodifferentialOperator k
  | negSucc k =>
    have hord : 2 * ((Int.negSucc k : ℤ) : ℝ) = -(2 * ((k + 1 : ℕ) : ℝ)) := by
      rw [Int.cast_negSucc]
      ring
    rw [hord, hnegativeMap]
    have horder : -(2 * ((k + 1 : ℕ) : ℝ)) = (-2 : ℝ) * ((k + 1 : ℕ) : ℝ) := by ring
    rw [horder]
    exact hPDO_pow (-2) L hLpdo (k + 1)

end AtiyahSinger
