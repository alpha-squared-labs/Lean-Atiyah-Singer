/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothGreenOperator
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Pseudodifferential regularity of the same smooth Green map

Public module ID: M0970.

A bounded smooth Green map differs from an actual elliptic parametrix by
smoothing terms. The only term containing the Green map is enclosed by the
two actual smoothing errors, so its original L² continuity gives extensions
between every pair of Sobolev orders. Both exact Green identities are used;
no parameter-family regularity is assumed.
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

/-- The same bounded smooth Green map is an order-minus-one PDO. -/
theorem isPseudodifferentialOperator_smoothGreenOperator
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) (hP : P.IsElliptic) :
    let W : Submodule ℂ (h.SmoothL2Section μ) := P.toLinearMap.ker
    let W' : Submodule ℂ (k.SmoothL2Section μ) := (P.metricFormalAdjoint h k).toLinearMap.ker
    letI : FiniteDimensional ℂ W := P.finiteDimensional_ker_of_isElliptic A B hP
    letI : FiniteDimensional ℂ W' :=
      (P.metricFormalAdjoint h k).finiteDimensional_ker_of_isElliptic B A
        ((P.isElliptic_metricFormalAdjoint_iff h k).mpr hP)
    ∀ (G : k.SmoothL2Section μ →L[ℂ] h.SmoothL2Section μ),
      (∀ u : h.SmoothL2Section μ, G (P.toLinearMap u) = u - W.starProjection u) →
      (∀ v : k.SmoothL2Section μ, P.toLinearMap (G v) = v - W'.starProjection v) →
      IsPseudodifferentialOperator F E μ (-1) G.toLinearMap := by
  classical
  intro W W'
  let : FiniteDimensional ℂ W := P.finiteDimensional_ker_of_isElliptic A B hP
  let : FiniteDimensional ℂ W' :=
    (P.metricFormalAdjoint h k).finiteDimensional_ker_of_isElliptic B A
      ((P.isElliptic_metricFormalAdjoint_iff h k).mpr hP)
  intro G hGP hPG
  let g : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E :=
    G.toLinearMap
  let K := smoothOrthogonalProjection μ h W
  let K' := smoothOrthogonalProjection μ k W'
  have hK : IsSmoothingOperator μ K := isSmoothingOperator_smoothOrthogonalProjection μ h W
  have hK' : IsSmoothingOperator μ K' := isSmoothingOperator_smoothOrthogonalProjection μ k W'
  have hgp (u : smoothSections (n := n) (r := r) E) :
      g (P.toLinearMap u) = u - K u := hGP u
  have hpg (v : smoothSections (n := n) (r := q) F) :
      P.toLinearMap (g v) = v - K' v := hPG v
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  let R := Q.toLinearMap.comp P.toLinearMap - LinearMap.id
  let T := P.toLinearMap.comp Q.toLinearMap - LinearMap.id
  have hR : IsSmoothingOperator μ R := hQ.1
  have hT : IsSmoothingOperator μ T := hQ.2
  -- The two genuine smoothing errors absorb all Sobolev orders around the bounded L² map.
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
  -- Every other correction is a smoothing ideal term for the original parametrix.
  have hKQ := IsSmoothingOperator.comp_isPseudodifferentialOperator
    K Q.toLinearMap hK Q.isPseudodifferentialOperator
  have hQT := IsPseudodifferentialOperator.comp_isSmoothingOperator
    Q.toLinearMap T Q.isPseudodifferentialOperator hT
  have hQK := IsPseudodifferentialOperator.comp_isSmoothingOperator
    Q.toLinearMap K' Q.isPseudodifferentialOperator hK'
  have hQKT := IsSmoothingOperator.comp_isPseudodifferentialOperator
    (Q.toLinearMap.comp K') T hQK (hT.isPseudodifferentialOperator 0 T)
  have hidentity : g = Q.toLinearMap + (-1 : ℂ) • (K.comp Q.toLinearMap) +
      (-1 : ℂ) • (Q.toLinearMap.comp T) + (Q.toLinearMap.comp K').comp T +
        R.comp (g.comp T) := by
    apply LinearMap.ext
    intro v
    have h₁ : g (T v) = Q.toLinearMap v - K (Q.toLinearMap v) - g v := by
      change g (P.toLinearMap (Q.toLinearMap v) - v) = _
      rw [map_sub, hgp]
    have h₂ : R (g (T v)) = Q.toLinearMap (T v) - Q.toLinearMap (K' (T v)) - g (T v) := by
      change Q.toLinearMap (P.toLinearMap (g (T v))) - g (T v) = _
      rw [hpg, map_sub]
    simp only [neg_one_smul, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply]
    rw [h₂, h₁]
    abel
  have hresult := IsPseudodifferentialOperator.add (-1) _ _
    (IsPseudodifferentialOperator.add (-1) _ _
      (IsPseudodifferentialOperator.add (-1) _ _
        (IsPseudodifferentialOperator.add (-1) _ _ Q.isPseudodifferentialOperator
          (IsPseudodifferentialOperator.smul (-1) (-1) _
            (hKQ.isPseudodifferentialOperator (-1) _)))
        (IsPseudodifferentialOperator.smul (-1) (-1) _
          (hQT.isPseudodifferentialOperator (-1) _)))
      (hQKT.isPseudodifferentialOperator (-1) _))
    (hsandwich.isPseudodifferentialOperator (-1) _)
  change IsPseudodifferentialOperator F E μ (-1) g
  rwa [← hidentity] at hresult

end PseudodifferentialOperator

end AtiyahSinger
