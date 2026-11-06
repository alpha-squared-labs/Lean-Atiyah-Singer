/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzJointParameter

import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Joint smoothness for the native vector-valued coordinate operator

Public module ID: M0941.

The actual Euclidean parameter and output coordinates are compared by their
canonical continuous linear equivalences. Expanding the original finite input
vector in its standard basis applies the scalar parameter theorem to each
matrix entry of the same operator. Reconstruction proves joint smoothness of
its original vector output, including zero input or output rank.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n m r q : ℕ}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original finite-vector Schwartz operator preserves joint Euclidean smoothness. -/
theorem contDiff_schwartzOperator_euclidean_of_common_compact_support
    (F : EuclideanSpace ℝ (Fin n) → 𝓢(E, EuclideanSpace ℂ (Fin r)))
    (hF : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin n) × E ↦ F p.1 p.2))
    (K : Set E) (hK : IsCompact K) (hsupport : ∀ x, tsupport (F x) ⊆ K)
    (T : 𝓢(E, EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin m), EuclideanSpace ℂ (Fin q))) :
    ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
      T (F p.1) p.2) := by
  classical
  let eD : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)
  let eH : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)
  let f (i : Fin r) (x : Fin n → ℝ) : 𝓢(E, ℂ) :=
    SchwartzMap.postcompCLM (EuclideanSpace.proj (𝕜 := ℂ) i) (F (eD.symm x))
  let lift (i : Fin r) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, EuclideanSpace ℂ (Fin r)) :=
    SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight
      (EuclideanSpace.single i 1))
  have hproj {s : ℕ} (i : Fin s) (v : EuclideanSpace ℂ (Fin s)) :
      (EuclideanSpace.proj (𝕜 := ℂ) i) v = v i := rfl
  have hf (i : Fin r) : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × E ↦ f i p.1 p.2) :=
    ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).contDiff.comp
      (hF.comp ((eD.symm.contDiff.comp contDiff_fst).prodMk contDiff_snd))
  have hfsupp (i : Fin r) (x : Fin n → ℝ) : tsupport (f i x) ⊆ K :=
    (tsupport_comp_subset (g := EuclideanSpace.proj (𝕜 := ℂ) i)
      (map_zero _) (F (eD.symm x))).trans (hsupport (eD.symm x))
  -- The original vector-valued input is exactly the sum of its standard coordinate injections.
  have hsum (x : EuclideanSpace ℝ (Fin n)) :
      F x = ∑ i : Fin r, lift i (f i (eD x)) := by
    apply SchwartzMap.ext
    intro z
    simp only [sum_apply, lift, f, SchwartzMap.postcompCLM_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.symm_apply_apply]
    symm
    simpa only [hproj, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.sum_repr (F x z)
  apply (contDiff_piLp (𝕜 := ℝ) (p := 2)).mpr
  intro j
  let output : 𝓢(EuclideanSpace ℝ (Fin m), EuclideanSpace ℂ (Fin q)) →L[ℂ]
      𝓢((Fin m → ℝ), ℂ) :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eH.symm).comp
      (SchwartzMap.postcompCLM (EuclideanSpace.proj (𝕜 := ℂ) j))
  have hi (i : Fin r) :
      ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        T (lift i (f i (eD p.1))) p.2 j) := by
    have h := contDiff_schwartzOperator_of_common_compact_support (f i) (hf i) K hK
      (hfsupp i) (output.comp (T.comp (lift i)))
    have hcomp := h.comp ((eD.contDiff.comp contDiff_fst).prodMk
      (eH.contDiff.comp contDiff_snd))
    change ContDiff ℝ ∞
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        T (lift i (f i (eD p.1))) (eH.symm (eH p.2)) j) at hcomp
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hcomp
  have hresult := ContDiff.sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) ↦ hi i)
  have heq : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
      T (F p.1) p.2 j) = (fun p ↦ ∑ i : Fin r, T (lift i (f i (eD p.1))) p.2 j) := by
    funext p
    rw [hsum p.1, map_sum]
    simp only [sum_apply]
    change (EuclideanSpace.proj (𝕜 := ℂ) j)
      (∑ i : Fin r, T (lift i (f i (eD p.1))) p.2) = _
    rw [map_sum]
    rfl
  rw [heq]
  exact hresult

end AtiyahSinger
