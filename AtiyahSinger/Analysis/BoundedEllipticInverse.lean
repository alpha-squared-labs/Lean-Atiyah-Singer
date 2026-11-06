/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothGreenPseudodifferential

/-!
# A bounded inverse of an elliptic operator is pseudodifferential

Public module ID: M0321.

The same smooth inverse of an elliptic operator of order `m` has order `-m`
whenever its action is bounded for the specified source and target L² metrics.
Both inverse identities are retained. A parametrix and its two smoothing
remainders enclose the bounded inverse, giving a smoothing correction to that
parametrix. No symbol estimate for the inverse is an input.

This standard parametrix argument supplies the actual connection-Laplacian
inverse and integer powers before fractional spectral powers are considered.
It generalizes the smoothing-remainder argument used for the smooth Green map
to any real order and to an actual two-sided inverse.
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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ

namespace PseudodifferentialOperator

/-- The given bounded smooth inverse of an elliptic PDO has the opposite order. -/
theorem isPseudodifferentialOperator_of_bounded_inverse {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) (hP : P.IsElliptic)
    (G : k.SmoothL2Section μ →L[ℂ] h.SmoothL2Section μ)
    (hGP : ∀ u : h.SmoothL2Section μ, G (P.toLinearMap u) = u)
    (hPG : ∀ v : k.SmoothL2Section μ, P.toLinearMap (G v) = v) :
    IsPseudodifferentialOperator F E μ (-m) G.toLinearMap := by
  classical
  let g : smoothSections (n := n) (r := q) F →ₗ[ℂ]
      smoothSections (n := n) (r := r) E := G.toLinearMap
  have hgp (u : smoothSections (n := n) (r := r) E) : g (P.toLinearMap u) = u :=
    hGP u
  have hpg (v : smoothSections (n := n) (r := q) F) : P.toLinearMap (g v) = v :=
    hPG v
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  let R := Q.toLinearMap.comp P.toLinearMap - LinearMap.id
  let T := P.toLinearMap.comp Q.toLinearMap - LinearMap.id
  have hR : IsSmoothingOperator μ R := hQ.1
  have hT : IsSmoothingOperator μ T := hQ.2
  -- The smoothing remainders absorb all Sobolev orders on either side of the same L² map.
  have hsandwich : IsSmoothingOperator μ (R.comp (g.comp T)) := by
    apply (isSmoothingOperator_iff_sobolevExtensions μ _ B A).mpr
    intro s t
    obtain ⟨R₀, hR₀⟩ := (isSmoothingOperator_iff_sobolevExtensions μ R A A).mp hR 0 t
    obtain ⟨T₀, hT₀⟩ := (isSmoothingOperator_iff_sobolevExtensions μ T B B).mp hT s 0
    let e := h.sobolevZeroEquivL2 (μ := μ) A
    let f := k.sobolevZeroEquivL2 (μ := μ) B
    let U := R₀.comp (e.symm.toContinuousLinearMap.comp
      (G.completion.comp (f.toContinuousLinearMap.comp T₀)))
    refine ⟨U, ?_⟩
    intro v
    change R₀ (e.symm (G.completion (f (T₀ (B.smoothToSobolev s v))))) = _
    rw [hT₀]
    have hf (w : smoothSections (n := n) (r := q) F) :
        f (B.smoothToSobolev 0 w) = k.smoothToL2 μ w :=
      k.sobolevZeroEquivL2_smooth B w
    have hcompletion (w : smoothSections (n := n) (r := q) F) :
        G.completion (k.smoothToL2 μ w) = h.smoothToL2 μ (g w) :=
      G.completion_apply_coe (show k.SmoothL2Section μ from w)
    have he (w : smoothSections (n := n) (r := r) E) :
        e.symm (h.smoothToL2 μ w) = A.smoothToSobolev 0 w := by
      rw [← h.sobolevZeroEquivL2_smooth A w]
      exact e.symm_apply_apply _
    rw [hf, hcompletion, he, hR₀]
    rfl
  -- Both inverse identities identify the inverse with this parametrix plus smoothing terms.
  have hQT := IsPseudodifferentialOperator.comp_isSmoothingOperator
    Q.toLinearMap T Q.isPseudodifferentialOperator hT
  have hidentity : g = Q.toLinearMap + (-1 : ℂ) • (Q.toLinearMap.comp T) +
      R.comp (g.comp T) := by
    apply LinearMap.ext
    intro v
    have h₁ : g (T v) = Q.toLinearMap v - g v := by
      change g (P.toLinearMap (Q.toLinearMap v) - v) = _
      rw [map_sub, hgp]
    have h₂ : R (g (T v)) = Q.toLinearMap (T v) - g (T v) := by
      change Q.toLinearMap (P.toLinearMap (g (T v))) - g (T v) = _
      rw [hpg]
    simp only [neg_one_smul, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply]
    rw [h₂, h₁]
    abel
  have hresult := IsPseudodifferentialOperator.add (-m) _ _
    (IsPseudodifferentialOperator.add (-m) _ _ Q.isPseudodifferentialOperator
      (IsPseudodifferentialOperator.smul (-m) (-1) _
        (hQT.isPseudodifferentialOperator (-m) _)))
    (hsandwich.isPseudodifferentialOperator (-m) _)
  change IsPseudodifferentialOperator F E μ (-m) g
  rwa [← hidentity] at hresult

end PseudodifferentialOperator

end AtiyahSinger
