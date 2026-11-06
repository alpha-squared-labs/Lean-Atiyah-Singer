/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FiniteParameterParametrix
public import AtiyahSinger.Analysis.GlobalSymbol
public import AtiyahSinger.Geometry.ConnectionLaplacian

/-!
# Finite parameter symbols for the specified connection Laplacian

Public module ID: M0381.

Every actual coordinate expression of the same connection Laplacian, in one
source and target frame, has the scalar metric principal symbol. The finite parameter
symbols are constructed from these original coefficients. The
coordinate expression is not replaced by an unrelated elliptic operator.
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

/-- Actual coordinate Laplacian expressions admit supported finite parameter symbol expansions. -/
theorem exists_connectionLaplacian_coordinate_finite_parametrix
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e]
    (U : Set M) (hU : IsOpen U)
    (P : CoordinateDifferentialOperator n r r 2 (c '' U))
    (hP : HasCoordinateExpression E E 2
      (connectionLaplacian μ g h cov hcov hcomplex).toLinearMap c e e U P)
    (f : SymbolFunction (n + 1) r r)
    (hf : IsSymbol ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹' (c '' U))
        0 f) :
    let W := (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹' (c '' U)
    ∃ a₀ : SymbolFunction (n + 1) r r, ∃ a : ℕ → SymbolFunction (n + 1) r r,
      IsSymbol W (-2) a₀ ∧
      (∀ j : ℕ, IsSymbol W (-2 - (j : ℝ)) (a j)) ∧
      (∀ j : ℕ, tsupport (a j) ⊆ tsupport f) ∧
      (∀ K : Set (EuclideanSpace ℝ (Fin (n + 1))), K ⊆ W → IsCompact K →
        ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ ζ, R ≤ ‖ζ‖ →
          a₀ z ζ = (P.parameterLift.principalSymbol z ζ).inverse) ∧
      a 0 = symbolComp a₀ f ∧
      (∀ j : ℕ, a (j + 1) = (-1 : ℂ) •
        symbolComp a₀ (P.parameterCorrectionSymbol (a j))) ∧
      ∀ N : ℕ, IsSymbol W (-(N : ℝ))
        ((∑ j ∈ Finset.range N,
          (symbolComp P.parameterLift.principalSymbol (a j) +
            P.parameterCorrectionSymbol (a j))) - f) := by
  classical
  let b (z ξ : EuclideanSpace ℝ (Fin n)) : ℝ :=
    g.length (c.symm z) (covectorFromChart c (c.symm z) ξ) ^ 2
  have hUs : U ⊆ c.source := fun x hx ↦ (hP.1 hx).1.1
  have hV : IsOpen (c '' U) := c.isOpen_image_of_subset_source hU hUs
  -- Evaluate the original global symbol identity on the same inverse-frame vector.
  have hprincipal (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c '' U)
      (ξ : EuclideanSpace ℝ (Fin n)) :
      P.principalSymbol z ξ = b z ξ • ContinuousLinearMap.id ℂ _ := by
    obtain ⟨x, hx, rfl⟩ := hz
    have hxc : x ∈ c.source := hUs hx
    have hxe : x ∈ e.baseSet := (hP.1 hx).1.2
    have hcoordinate := covectorInChart_covectorFromChart c hc x hxc ξ
    apply ContinuousLinearMap.ext
    intro v
    have hspec := LinearMap.congr_fun
      ((connectionLaplacian μ g h cov hcov hcomplex).hasPrincipalSymbol
        c hc e e U hU P hP x hx (covectorFromChart c x ξ)) (e.symmL ℂ x v)
    change e.linearMapAt ℂ x
      ((connectionLaplacian μ g h cov hcov hcomplex).principalSymbol x
        (covectorFromChart c x ξ) (e.symmL ℂ x v)) =
      P.principalSymbol (c x) (covectorInChart c x (covectorFromChart c x ξ))
        (e.linearMapAt ℂ x (e.symmL ℂ x v)) at hspec
    rw [hcoordinate, connectionLaplacian_principalSymbol μ g h cov hcov hcomplex] at hspec
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul,
      e.symmL_apply hxe, e.linearMapAt_symm hxe] at hspec
    change P.principalSymbol (c x) ξ v = b (c x) ξ • v
    dsimp only [b]
    rw [c.left_inv hxc]
    simpa only [← Complex.coe_smul, Complex.ofReal_pow] using hspec.symm
  have hnonneg (z : EuclideanSpace ℝ (Fin n)) (_ : z ∈ c '' U)
      (ξ : EuclideanSpace ℝ (Fin n)) : 0 ≤ b z ξ := sq_nonneg _
  -- The original coordinate covector map is injective on its chart domain.
  have hpos (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c '' U)
      (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) : 0 < b z ξ := by
    obtain ⟨x, hx, rfl⟩ := hz
    have hxc : x ∈ c.source := hUs hx
    have hne : covectorFromChart c x ξ ≠ 0 := by
      intro heq
      have h := covectorInChart_covectorFromChart c hc x hxc ξ
      rw [heq] at h
      have hz : covectorInChart c x 0 = 0 := by ext j; rfl
      exact hξ (h.symm.trans hz)
    dsimp only [b]
    rw [c.left_inv hxc]
    exact pow_pos (g.length_pos x _ hne) 2
  exact P.exists_finite_parameter_symbol_sequence hV f hf b hprincipal hnonneg hpos

end AtiyahSinger
