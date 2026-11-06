/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ExternalTensorH1Inner
public import AtiyahSinger.Geometry.ExternalTensorPresentation

/-!
# Mixed Sobolev energy in the original product presentation

Public module ID: M0610.

The two factor presentations induce the same native product bundle frames and
partition used by exterior tensor sections. Their first Sobolev pairing is the
sum of the two mixed factor pairings, with their common zeroth-order pairing
subtracted once. This retains all cross terms needed for estimates on arbitrary
finite sums, rather than estimates only on an individual pure tensor.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff TensorProduct SchwartzMap

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

variable {n m r s : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  {E : M → Type*} {F : N → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := m) (r := s) F]

variable [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]

/-- The exact product presentation has the two mixed first-Sobolev energies. -/
theorem inner_smoothToSobolev_one_externalTensor
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := m) (r := s) F)
    (u u' : smoothSections (n := n) (r := r) E)
    (v v' : smoothSections (n := m) (r := s) F) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
    let C := externalTensorPresentation A B
    inner ℂ (C.smoothToSobolev 1 (externalTensorSection E F u v))
        (C.smoothToSobolev 1 (externalTensorSection E F u' v')) =
      inner ℂ (A.smoothToSobolev 1 u) (A.smoothToSobolev 1 u') *
          inner ℂ (B.smoothToSobolev 0 v) (B.smoothToSobolev 0 v') +
        inner ℂ (A.smoothToSobolev 0 u) (A.smoothToSobolev 0 u') *
          inner ℂ (B.smoothToSobolev 1 v) (B.smoothToSobolev 1 v') -
        inner ℂ (A.smoothToSobolev 0 u) (A.smoothToSobolev 0 u') *
          inner ℂ (B.smoothToSobolev 0 v) (B.smoothToSobolev 0 v') := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
  let C := externalTensorPresentation A B
  change inner ℂ (C.smoothToSobolev 1 (externalTensorSection E F u v))
    (C.smoothToSobolev 1 (externalTensorSection E F u' v')) = _
  -- The original Sobolev inner product is the finite sum of its actual Bessel coordinates.
  have hA (t : ℝ) :
      inner ℂ (A.smoothToSobolev t u) (A.smoothToSobolev t u') =
        ∑ i : Fin A.size, inner ℂ (schwartzSobolevCoordinate t (A.localize i u))
          (schwartzSobolevCoordinate t (A.localize i u')) :=
    PiLp.inner_apply (A.sobolevCoordinates t u) (A.sobolevCoordinates t u')
  have hB (t : ℝ) :
      inner ℂ (B.smoothToSobolev t v) (B.smoothToSobolev t v') =
        ∑ j : Fin B.size, inner ℂ (schwartzSobolevCoordinate t (B.localize j v))
          (schwartzSobolevCoordinate t (B.localize j v')) :=
    PiLp.inner_apply (B.sobolevCoordinates t v) (B.sobolevCoordinates t v')
  have hC :
      inner ℂ (C.smoothToSobolev 1 (externalTensorSection E F u v))
          (C.smoothToSobolev 1 (externalTensorSection E F u' v')) =
        ∑ k : Fin C.size,
          inner ℂ (schwartzSobolevCoordinate 1 (C.localize k (externalTensorSection E F u v)))
            (schwartzSobolevCoordinate 1 (C.localize k (externalTensorSection E F u' v'))) :=
    PiLp.inner_apply (C.sobolevCoordinates 1 (externalTensorSection E F u v))
      (C.sobolevCoordinates 1 (externalTensorSection E F u' v'))
  have hzero {d k : ℕ}
      (f : 𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin k))) :
      schwartzSobolevCoordinate 0 f = f.toLp 2 := by
    unfold schwartzSobolevCoordinate
    congr 1
    rw [SchwartzMap.fourierMultiplierCLM_apply]
    have heq : SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin k))
        (fun ξ : EuclideanSpace ℝ (Fin d) ↦ ((1 + ‖ξ‖ ^ 2) ^ ((0 : ℝ) / 2) : ℝ))
          (FourierTransform.fourier f) = FourierTransform.fourier f := by
      ext x
      rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
      simp
    rw [heq, FourierTransform.fourierInv_fourier_eq]
  -- Each product chart uses exactly the two localized factor coordinates.
  have hlocal (i : Fin A.size) (j : Fin B.size) :
      inner ℂ
        (schwartzSobolevCoordinate 1
          (C.localize (finProdFinEquiv (i, j)) (externalTensorSection E F u v)))
        (schwartzSobolevCoordinate 1
          (C.localize (finProdFinEquiv (i, j)) (externalTensorSection E F u' v'))) =
      inner ℂ (schwartzSobolevCoordinate 1 (A.localize i u))
          (schwartzSobolevCoordinate 1 (A.localize i u')) *
          inner ℂ ((B.localize j v).toLp 2) ((B.localize j v').toLp 2) +
        inner ℂ ((A.localize i u).toLp 2) ((A.localize i u').toLp 2) *
          inner ℂ (schwartzSobolevCoordinate 1 (B.localize j v))
            (schwartzSobolevCoordinate 1 (B.localize j v')) -
        inner ℂ ((A.localize i u).toLp 2) ((A.localize i u').toLp 2) *
          inner ℂ ((B.localize j v).toLp 2) ((B.localize j v').toLp 2) := by
    apply inner_schwartzSobolevCoordinate_one_tensor
    · intro x y a b
      exact externalTensorPresentation_localizedFunction A B i j u v (x, y) a b
    · intro x y a b
      exact externalTensorPresentation_localizedFunction A B i j u' v' (x, y) a b
  -- The finite product partition factors each of the three pairing sums.
  rw [hC, hA, hA, hB, hB]
  simp_rw [hzero]
  have hsum := (finProdFinEquiv : Fin A.size × Fin B.size ≃ Fin C.size).sum_comp
    (fun k : Fin C.size ↦ inner ℂ
      (schwartzSobolevCoordinate 1 (C.localize k (externalTensorSection E F u v)))
      (schwartzSobolevCoordinate 1 (C.localize k (externalTensorSection E F u' v'))))
  refine hsum.symm.trans ?_
  simp only [Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl (fun i _ ↦
    Finset.sum_congr rfl (fun j _ ↦ hlocal i j))).trans ?_
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]

end AtiyahSinger
