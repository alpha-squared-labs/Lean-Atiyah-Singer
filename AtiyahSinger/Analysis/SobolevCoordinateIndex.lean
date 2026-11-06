/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.IndexIntertwining

/-!
# Elliptic indices in specified Sobolev coordinates

Public module ID: M0992.

A map identified with the actual elliptic PDO on the original dense smooth
core is Fredholm in the supplied completed coordinates and retains the PDO's
smooth index. The specified source and target equivalences are retained;
this allows the actual cutoff family to use fixed component domains.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

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

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- Specified Sobolev coordinates preserve elliptic Fredholmness and the smooth index. -/
theorem isFredholm_and_index_eq_of_sobolev_coordinates
    (hP : P.IsElliptic) (s : ℝ)
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (Φ : A.SobolevSpace s ≃L[ℂ] X) (Ψ : B.SobolevSpace (s - m) ≃L[ℂ] Y)
    (T : X →L[ℂ] Y)
    (hT : ∀ u, T (Φ (A.smoothToSobolev s u)) =
      Ψ (B.smoothToSobolev (s - m) (P.toLinearMap u))) :
    T.IsFredholm ∧ T.index = P.toLinearMap.index := by
  let R := P.sobolevExtension A B s
  -- Continuity extends the exact smooth square to the same Sobolev completion.
  have hcomm : T.comp Φ.toContinuousLinearMap = Ψ.toContinuousLinearMap.comp R := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev s).equalizer
      (T.comp Φ.toContinuousLinearMap).continuous
      (Ψ.toContinuousLinearMap.comp R).continuous
    funext u
    change T (Φ (A.smoothToSobolev s u)) = Ψ (R (A.smoothToSobolev s u))
    rw [P.sobolevExtension_smoothToSobolev]
    exact hT u
  have heq : T = Ψ.toContinuousLinearMap.comp (R.comp Φ.symm.toContinuousLinearMap) := by
    ext x
    have hx := DFunLike.congr_fun hcomm (Φ.symm x)
    change T (Φ (Φ.symm x)) = Ψ (R (Φ.symm x)) at hx
    change T x = Ψ (R (Φ.symm x))
    simpa only [Φ.apply_symm_apply] using hx
  -- Fredholmness and both quotient dimensions follow from these same equivalences.
  have hFred : T.IsFredholm := by
    rw [heq]
    exact Ψ.isFredholm.comp
      ((P.isFredholm_sobolevExtension_of_isElliptic A B hP s).comp Φ.symm.isFredholm)
  have hindex : R.index = T.index :=
    index_eq_of_linearEquiv R.toLinearMap T.toLinearMap Φ.toLinearEquiv Ψ.toLinearEquiv
      (fun u ↦ DFunLike.congr_fun hcomm u)
  exact ⟨hFred, hindex.symm.trans (P.index_sobolevExtension_eq_of_isElliptic A B hP s)⟩

end PseudodifferentialOperator

end AtiyahSinger
