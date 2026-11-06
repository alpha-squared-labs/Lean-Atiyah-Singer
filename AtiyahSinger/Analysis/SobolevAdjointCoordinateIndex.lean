/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricAdjointIndex
public import AtiyahSinger.Analysis.SobolevCoordinateIndex

/-!
# An elliptic operator and its metric adjoint in specified Sobolev coordinates

Public module ID: M0988.

For one order-one elliptic operator, retain the two given bundle metrics and
the four given coordinate equivalences at Sobolev orders one and zero. The
two actual conjugated realizations are Fredholm, retain their smooth indices,
and have opposite indices.

The coordinate-index and metric-adjoint index theorems combine through scalar
order transport and the two smooth coordinate squares. No Green, tensor or cutoff data are used.
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

/-- The specified Sobolev conjugates of one elliptic operator and its literal
metric adjoint are Fredholm, retain their smooth indices, and have index sum zero. -/
theorem isFredholm_and_index_eq_of_sobolev_coordinates_with_metricFormalAdjoint
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (hP : P.IsElliptic)
    {X Y Xa Ya : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Xa] [NormedSpace ℂ Xa] [CompleteSpace Xa]
    [NormedAddCommGroup Ya] [NormedSpace ℂ Ya] [CompleteSpace Ya]
    (Φ : A.SobolevSpace 1 ≃L[ℂ] X) (Ψ : B.SobolevSpace 0 ≃L[ℂ] Y)
    (Φa : B.SobolevSpace 1 ≃L[ℂ] Xa) (Ψa : A.SobolevSpace 0 ≃L[ℂ] Ya) :
    let T : X →L[ℂ] Y := Ψ.toContinuousLinearMap.comp
      ((P.sobolevRealization A B 1 0 (by norm_num)).comp Φ.symm.toContinuousLinearMap)
    let Ta : Xa →L[ℂ] Ya := Ψa.toContinuousLinearMap.comp
      (((P.metricFormalAdjoint h k).sobolevRealization B A 1 0 (by norm_num)).comp
        Φa.symm.toContinuousLinearMap)
    (T.IsFredholm ∧ T.index = P.toLinearMap.index) ∧
    (Ta.IsFredholm ∧ Ta.index = (P.metricFormalAdjoint h k).toLinearMap.index) ∧
    T.index + Ta.index = 0 := by
  intro T Ta
  -- Transport only the scalar target order, keeping both original forward coordinates.
  have hT : T.IsFredholm ∧ T.index = P.toLinearMap.index := by
    let CoordinateIndexAt (t : ℝ) : Prop :=
      ∀ (psi : B.SobolevSpace t ≃L[ℂ] Y) (R : X →L[ℂ] Y),
        (∀ u, R (Φ (A.smoothToSobolev 1 u)) =
          psi (B.smoothToSobolev t (P.toLinearMap u))) →
        R.IsFredholm ∧ R.index = P.toLinearMap.index
    have hcoord : CoordinateIndexAt (1 - 1) :=
      P.isFredholm_and_index_eq_of_sobolev_coordinates A B hP 1 Φ
    have hcoordZero : CoordinateIndexAt 0 :=
      Eq.mp (congrArg CoordinateIndexAt (sub_self (1 : ℝ))) hcoord
    apply hcoordZero Ψ T
    intro u
    -- The source round trip identifies this conjugate with P on its dense smooth core.
    have hroundtrip := Φ.symm_apply_apply (A.smoothToSobolev 1 u)
    have hcancel := congrArg (fun w : A.SobolevSpace 1 ↦
      Ψ (P.sobolevRealization A B 1 0 (by norm_num) w)) hroundtrip
    exact hcancel.trans (congrArg Ψ
      (P.sobolevRealization_smoothToSobolev A B 1 0 (by norm_num) u))
  -- Apply the same coordinate theorem to the literal adjoint for the specified metrics.
  have hTa : Ta.IsFredholm ∧
      Ta.index = (P.metricFormalAdjoint h k).toLinearMap.index := by
    have hPa := (P.isElliptic_metricFormalAdjoint_iff h k).mpr hP
    let CoordinateIndexAt (t : ℝ) : Prop :=
      ∀ (psi : A.SobolevSpace t ≃L[ℂ] Ya) (R : Xa →L[ℂ] Ya),
        (∀ u, R (Φa (B.smoothToSobolev 1 u)) =
          psi (A.smoothToSobolev t ((P.metricFormalAdjoint h k).toLinearMap u))) →
        R.IsFredholm ∧ R.index = (P.metricFormalAdjoint h k).toLinearMap.index
    have hcoord : CoordinateIndexAt (1 - 1) :=
      (P.metricFormalAdjoint h k).isFredholm_and_index_eq_of_sobolev_coordinates
        B A hPa 1 Φa
    have hcoordZero : CoordinateIndexAt 0 :=
      Eq.mp (congrArg CoordinateIndexAt (sub_self (1 : ℝ))) hcoord
    apply hcoordZero Ψa Ta
    intro u
    have hroundtrip := Φa.symm_apply_apply (B.smoothToSobolev 1 u)
    have hcancel := congrArg (fun w : B.SobolevSpace 1 ↦
      Ψa ((P.metricFormalAdjoint h k).sobolevRealization B A 1 0 (by norm_num) w))
      hroundtrip
    exact hcancel.trans (congrArg Ψa
      ((P.metricFormalAdjoint h k).sobolevRealization_smoothToSobolev
        B A 1 0 (by norm_num) u))
  refine ⟨hT, hTa, ?_⟩
  -- Smooth adjoint-index cancellation now applies to these same two conjugates.
  have hsum := congrArg₂ (fun a b : ℤ ↦ a + b) hT.2 hTa.2
  have hadjoint := index_metricFormalAdjoint_eq_neg (P := P) h k hP
  calc
    T.index + Ta.index =
        P.toLinearMap.index + (P.metricFormalAdjoint h k).toLinearMap.index := hsum
    _ = P.toLinearMap.index + -P.toLinearMap.index :=
      congrArg (fun a : ℤ ↦ P.toLinearMap.index + a) hadjoint
    _ = 0 := add_neg_cancel _

end PseudodifferentialOperator

end AtiyahSinger
