/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzPairingFubini

/-!
# Finite matrix distribution pairings in independent variables

The original vector-valued functionals are evaluated on the same finite
matrix of scalar Schwartz inputs, localized by one cutoff in each variable.
Whenever the two partial applications have their specified Schwartz values,
their iterated pairings agree. Coordinate injections reduce the assertion to
scalar distributional Fubini, and exact finite reconstruction recovers the
whole vector-valued inputs, including zero-dimensional fibers.

Composing an actual Schwartz operator with any output coordinate evaluation
gives these functionals. Thus the statement allows independent input and
output ranks and applies directly to the local horizontal/vertical comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped SchwartzMap

variable {n m a b : ℕ}

local notation "X" => Fin n → ℝ
local notation "Y" => Fin m → ℝ
local notation "V" => EuclideanSpace ℂ (Fin a)
local notation "W" => EuclideanSpace ℂ (Fin b)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Independent finite matrix pairings commute on their original localized Schwartz values. -/
theorem schwartzLocalizedMatrixPairings_commute
    (φ : 𝓢(X, ℂ)) (hφ : HasCompactSupport φ)
    (ψ : 𝓢(Y, ℂ)) (hψ : HasCompactSupport ψ)
    (L : 𝓢(X, V) →L[ℂ] ℂ) (R : 𝓢(Y, W) →L[ℂ] ℂ)
    (f : Fin a → Fin b → 𝓢(X × Y, ℂ)) :
    let J (i : Fin a) : 𝓢(X, ℂ) →L[ℂ] 𝓢(X, V) :=
      SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight
        (EuclideanSpace.single i 1))
    let K (j : Fin b) : 𝓢(Y, ℂ) →L[ℂ] 𝓢(Y, W) :=
      SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight
        (EuclideanSpace.single j 1))
    let C := SchwartzMap.smulLeftCLM ℂ (fun z : X × Y ↦ φ z.1 * ψ z.2)
    let S : 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(Y × X, ℂ) :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (ContinuousLinearEquiv.prodComm ℝ Y X)
    ∀ (u : 𝓢(X, V)) (v : 𝓢(Y, W)),
      (∀ x i, u x i = R (∑ j, K j (schwartzSliceCLM x (C (f i j))))) →
      (∀ y j, v y j = L (∑ i, J i (schwartzSliceCLM y (S (C (f i j)))))) →
      L u = R v := by
  classical
  intro J K C S u v hu hv
  -- Scalar Fubini uses the very same coordinate injections into the original functionals.
  have hpair (i : Fin a) (j : Fin b) :=
    exists_schwartzLocalizedPairings_commute φ hφ ψ hψ (L.comp (J i)) (R.comp (K j))
  choose A B hA hB hAB using hpair
  have hleft : u = ∑ i : Fin a, J i (∑ j : Fin b, A i j (f i j)) := by
    apply SchwartzMap.ext
    intro x
    have hcoords (i : Fin a) : u x i = ∑ j : Fin b, A i j (f i j) x := by
      rw [hu, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact (hA i j (f i j) x).symm
    calc
      u x = ∑ i : Fin a, u x i • EuclideanSpace.single i 1 := by
        symm
        simpa only [OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply] using
          (EuclideanSpace.basisFun (Fin a) ℂ).toBasis.sum_repr (u x)
      _ = ∑ i : Fin a, (∑ j : Fin b, A i j (f i j) x) •
          EuclideanSpace.single i 1 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hcoords]
      _ = (∑ i : Fin a, J i (∑ j : Fin b, A i j (f i j))) x := by
        simp only [sum_apply, J, SchwartzMap.postcompCLM_apply,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
  have hright : v = ∑ j : Fin b, K j (∑ i : Fin a, B i j (f i j)) := by
    apply SchwartzMap.ext
    intro y
    have hcoords (j : Fin b) : v y j = ∑ i : Fin a, B i j (f i j) y := by
      rw [hv, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (hB i j (f i j) y).symm
    calc
      v y = ∑ j : Fin b, v y j • EuclideanSpace.single j 1 := by
        symm
        simpa only [OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply] using
          (EuclideanSpace.basisFun (Fin b) ℂ).toBasis.sum_repr (v y)
      _ = ∑ j : Fin b, (∑ i : Fin a, B i j (f i j) y) •
          EuclideanSpace.single j 1 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hcoords]
      _ = (∑ j : Fin b, K j (∑ i : Fin a, B i j (f i j))) y := by
        simp only [sum_apply, K, SchwartzMap.postcompCLM_apply,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
  -- Reconstruct before changing the order of the two finite sums.
  rw [hleft, hright, map_sum, map_sum]
  simp only [map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun T : 𝓢(X × Y, ℂ) →L[ℂ] ℂ ↦ T (f i j)) (hAB i j)

end AtiyahSinger
