/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LocalAdjoint

import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Bilinear transposes of compact local pseudodifferential operators

Public module ID: M0790.

The local input for SG III.(3.18) and Theorem 3.17(iv).
Dual coefficients are ordinary complex-linear covectors. Thus the right amplitude
uses the matrix transpose at the reflected frequency, not the Hermitian adjoint.
The existence proof conjugates the established Hermitian adjoint in standard coordinates.
The exact symbol formula follows from the adjoint amplitude by conjugation and frequency reflection.
All orders are real, the two ranks may differ, and both operator supports are retained.
Only the leading symbol comparison is stated here, not a full transpose expansion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 15

variable {n r q : ℕ}

/-- Ordinary matrix transpose at the reflected real frequency, in standard dual coordinates. -/
def symbolTranspose (p : SymbolFunction n r q) : SymbolFunction n q r :=
  fun x ξ ↦ (Matrix.toEuclideanLin
    (Matrix.transpose (Matrix.toEuclideanLin.symm (p x (-ξ)).toLinearMap))).toContinuousLinearMap

/-- The reflected transpose acts on covector coefficients without complex conjugation. -/
theorem symbolTranspose_apply (p : SymbolFunction n r q)
    (x ξ : EuclideanSpace ℝ (Fin n)) (a : EuclideanSpace ℂ (Fin q)) (i : Fin r) :
    symbolTranspose p x ξ a i =
      ∑ j, (p x (-ξ) (EuclideanSpace.single i 1)) j * a j := by
  /- Express p at -ξ in the standard bases, transpose its rectangular matrix,
  and apply the resulting matrix to a. The entry in row i is the displayed sum.
  The operation is complex-linear in a and in p; there is no conjugation. -/
  -- The standard-basis matrix coefficient is the original map on that basis vector.
  simp [symbolTranspose, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.toLin_apply, Matrix.toLin_symm, LinearMap.toMatrix_apply,
    EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The cutoff right amplitude obtained by swapping kernel variables and reflecting frequency. -/
def transposeAmplitude (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n r q) : AmplitudeFunction n q r :=
  fun x y ξ ↦ χ x • symbolTranspose p y ξ

/-- The exact left symbol of the bilinear transpose amplitude. -/
def transposeSymbol (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n r q) : SymbolFunction n q r :=
  amplitudeSymbol (transposeAmplitude χ p)

/-- Formal transposition uses the actual bilinear dot pairing on all Schwartz tests. -/
def IsSchwartzFormalTranspose
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) : Prop :=
  ∀ u a, (∫ x, ∑ i, T a x i * u x i) = ∫ x, ∑ j, a x j * P u x j

set_option maxHeartbeats 800000 in

/-- Reflection and ordinary transpose preserve the mixed symbol estimates. -/
theorem isAmplitude_transposeAmplitude (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) : IsAmplitude m (transposeAmplitude χ p) := by
  /- The matrix transpose is continuous complex-linear in finite dimensions.
  Frequency reflection is a linear isometry; each frequency derivative changes
  only a sign. Apply the mixed product rule to χ(x) and the reflected symbol at y,
  taking bounds on compact spatial pairs. The frequency order remains m. -/
  let P := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let H' := EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)
  -- Transposition is a continuous linear equivalence between the original rectangular Hom spaces.
  let L : H ≃ₗ[ℂ] H' :=
    ((((LinearMap.toContinuousLinearMap (𝕜 := ℂ)).symm.trans Matrix.toEuclideanLin.symm).trans
      (Matrix.transposeLinearEquiv (Fin q) (Fin r) ℂ ℂ)).trans
      (Matrix.toEuclideanLin.trans (LinearMap.toContinuousLinearMap (𝕜 := ℂ))))
  let J : H ≃L[ℝ] H' := {
    toLinearEquiv := L.restrictScalars ℝ
    continuous_toFun := L.toContinuousLinearEquiv.continuous
    continuous_invFun := L.toContinuousLinearEquiv.symm.continuous }
  let R : P ≃L[ℝ] P := ContinuousLinearEquiv.neg ℝ
  have hps : ContDiff ℝ ∞ (Function.uncurry p) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
  have hs : ContDiff ℝ ∞ (Function.uncurry (symbolTranspose p)) :=
    J.contDiff.comp (hps.comp (contDiff_fst.prodMk contDiff_snd.neg))
  have hsp : IsSymbol Set.univ m (symbolTranspose p) := by
    refine ⟨by simpa only [Set.univ_prod_univ] using hs.contDiffOn, ?_⟩
    intro K hK hcompact i j
    obtain ⟨C, hC, hbound⟩ := hp.2 K hK hcompact i j
    let T : (P [×j]→L[ℝ] H) ≃L[ℝ] (P [×j]→L[ℝ] H') :=
      (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft H
        (fun _ : Fin j ↦ R)).trans (J.continuousMultilinearMapCongrRight (fun _ : Fin j ↦ P))
    refine ⟨‖T.toContinuousLinearMap‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
    intro x hx ξ
    have heq : (fun y ↦ iteratedFDeriv ℝ j (symbolTranspose p y) ξ) =
        T ∘ (fun y ↦ iteratedFDeriv ℝ j (p y) (-ξ)) := by
      funext y
      change iteratedFDeriv ℝ j (J ∘ (p y ∘ R)) ξ = _
      have hy : ContDiff ℝ ∞ (p y) := hps.comp (contDiff_const.prodMk contDiff_id)
      have hr := R.toContinuousLinearMap.iteratedFDeriv_comp_right (i := j) hy ξ (by simp)
      simp only [ContinuousLinearEquiv.coe_coe] at hr
      rw [J.iteratedFDeriv_comp_left, hr]
      rfl
    change ‖iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (symbolTranspose p y) ξ) x‖ ≤ _
    rw [heq, T.iteratedFDeriv_comp_left]
    calc
      _ ≤ ‖T.toContinuousLinearMap‖ * ‖symbolDerivative p i j x (-ξ)‖ :=
        T.toContinuousLinearMap.norm_compContinuousMultilinearMap_le _
      _ ≤ ‖T.toContinuousLinearMap‖ * (C * (1 + ‖-ξ‖) ^ (m - (j : ℝ))) :=
        mul_le_mul_of_nonneg_left (hbound x hx (-ξ)) (norm_nonneg _)
      _ = _ := by rw [norm_neg]; ring
  have rightAmplitude (a : SymbolFunction n q r) (ha : IsSymbol Set.univ m a) :
      IsAmplitude m (fun x y ξ ↦ χ x • a y ξ) := by
    have hsa : ContDiff ℝ ∞ (Function.uncurry a) := by
      simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
    have parametric {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
        (f : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
        ContDiff ℝ ∞ (fun z : P × P ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
      induction k with
      | zero =>
        exact hf.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ P V).symm : _ →L[ℝ] P [×0]→L[ℝ] V)
      | succ k ih =>
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun z : P × P ↦ fun η : P ↦ iteratedFDeriv ℝ k (f z.1) η)) :=
          ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
        have hd : ContDiff ℝ ∞
            (fun z : P × P ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
          h.fderiv contDiff_snd (by simp)
        exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ P) V).symm :
            _ →L[ℝ] P [×(k + 1)]→L[ℝ] V)
    refine ⟨(hχ.comp (contDiff_fst.fst)).smul
      (hsa.comp (contDiff_fst.snd.prodMk contDiff_snd)), ?_⟩
    intro K hK i j k
    obtain ⟨C, hC⟩ := ((hK.image continuous_fst).image
      (hχ.continuous_iteratedFDeriv (m := i) (by simp)).norm).bddAbove
    obtain ⟨D, hD, hd⟩ := ha.2 (Prod.snd '' K) (Set.subset_univ _)
      (hK.image continuous_snd) j k
    refine ⟨max C 0 * D, mul_nonneg (le_max_right _ _) hD, ?_⟩
    intro x y hxy ξ
    -- The three derivatives separate: frequency and input position hit p, output position hits χ.
    let d (w : P) := iteratedFDeriv ℝ k (a w) ξ
    have hfreq (z w : P) :
        iteratedFDeriv ℝ k ((fun x y ξ ↦ χ x • a y ξ) z w) ξ = χ z • d w := by
      exact iteratedFDeriv_const_smul_apply'
        ((hsa.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
    have hdSmooth : ContDiff ℝ ∞ d :=
      (parametric a hsa k).comp (contDiff_id.prodMk contDiff_const)
    have heq : amplitudeDerivative ((fun x y ξ ↦ χ x • a y ξ)) i j k x y ξ =
        (iteratedFDeriv ℝ i χ x).smulRight (symbolDerivative (a) j k y ξ) := by
      dsimp only [amplitudeDerivative]
      simp only [hfreq]
      have hy (z : P) : iteratedFDeriv ℝ j (fun w ↦ χ z • d w) y =
          χ z • iteratedFDeriv ℝ j d y :=
        iteratedFDeriv_const_smul_apply' (hdSmooth.contDiffAt.of_le (by simp))
      rw [show (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ χ z • d w) y) =
        (fun z ↦ χ z • iteratedFDeriv ℝ j d y) from funext hy]
      exact iteratedFDeriv_smul_const_apply (hχ.contDiffAt.of_le (by simp))
    rw [heq]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i χ x‖ * ‖symbolDerivative (a) j k y ξ‖ :=
        (ContinuousMultilinearMap.norm_smulRight _ _).le
      _ ≤ max C 0 * (D * (1 + ‖ξ‖) ^ (m - (k : ℝ))) := by
        exact mul_le_mul ((hC ⟨x, ⟨(x, y), hxy, rfl⟩, rfl⟩).trans (le_max_left _ _))
          (hd y ⟨(x, y), hxy, rfl⟩ ξ) (norm_nonneg _) (le_max_right _ _)
      _ = _ := by ring
  exact rightAmplitude (symbolTranspose p) hsp

/-- Compact symbol and cutoff supports give uniform compact support in both spatial variables. -/
theorem hasCompactSupport_transposeAmplitude (p : SymbolFunction n r q)
    (hp : HasCompactSupport p) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : HasCompactSupport χ) :
    HasCompactSupport (Function.uncurry (transposeAmplitude χ p)) := by
  /- The amplitude vanishes outside tsupport χ times tsupport p. Reflection
  changes only frequency, and transpose sends zero to zero. This compact product
  therefore contains the closed support, uniformly over all frequencies. -/
  -- Each nonzero amplitude needs both a nonzero cutoff and a nonzero original symbol.
  apply (hχ.prod hp).of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ ((isClosed_tsupport χ).prod (isClosed_tsupport p))
  intro z hz
  constructor
  · by_contra hχz
    apply hz
    funext ξ
    simp [Function.uncurry, transposeAmplitude, image_eq_zero_of_notMem_tsupport hχz]
  · by_contra hpz
    have hpzero : p z.2 = 0 := image_eq_zero_of_notMem_tsupport hpz
    apply hz
    funext ξ
    simp [Function.uncurry, transposeAmplitude, symbolTranspose, hpzero]

/-- The exact reduced transpose symbol has the original real order. -/
theorem isSymbol_transposeSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hsupp : HasCompactSupport p)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupp : HasCompactSupport χ) : IsSymbol Set.univ m (transposeSymbol χ p) := by
  /- The preceding two results place the actual amplitude in the compact spatial
  case of SG 3.5. Its exact reduction has order m in every compact spatial set.
  The cutoff is arbitrary here; identifying the transpose requires it to be one
  near the operator support, as imposed in the later action formula. -/
  exact isSymbol_amplitudeSymbol m _ (isAmplitude_transposeAmplitude m p hp χ hχ)
    (hasCompactSupport_transposeAmplitude p hsupp χ hχsupp)

/-- The transpose's principal representative is the ordinary transpose at negative frequency. -/
theorem isSymbol_transposeSymbol_sub (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hsupp : HasCompactSupport p)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupp : HasCompactSupport χ) (hone : ∀ x ∈ tsupport p, χ x = 1) :
    IsSymbol Set.univ (m - 1) (transposeSymbol χ p - symbolTranspose p) := by
  /- Take the N=1 amplitude expansion. Its leading diagonal value is
  χ(x) p(x,-ξ)^t. On tsupport p the cutoff is one, and off that support p is zero.
  The remaining symbol is of order m-1. No real power of -1 or homogeneous-symbol
  hypothesis is involved: reflection makes sense for every real order m. -/
  -- The zero-th Taylor term is the same reflected transpose on the diagonal.
  have hterm : amplitudeExpansionTerm (transposeAmplitude χ p) 0 = symbolTranspose p := by
    funext x ξ
    by_cases hx : x ∈ tsupport p
    · simp [amplitudeExpansionTerm, transposeAmplitude, hone x hx,
        iteratedFDeriv_zero_apply]
    · have hpzero : p x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [amplitudeExpansionTerm, transposeAmplitude, symbolTranspose, hpzero,
        iteratedFDeriv_zero_apply]
  -- Only the first remainder is used; its original order is m - 1.
  have h := hasSymbolExpansion_amplitudeSymbol m (transposeAmplitude χ p)
    (isAmplitude_transposeAmplitude m p hp χ hχ)
    (hasCompactSupport_transposeAmplitude p hsupp χ hχsupp) 1
  simpa only [transposeSymbol, Finset.sum_range_one, Nat.cast_one, hterm] using h

variable (m : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
  (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
  (hP : ∀ u x, P u x = quantize p u x)
  (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
  (hPK : HasOperatorSupport K P)

include hp hP hK hPK in
set_option maxSynthPendingDepth 20 in
set_option maxHeartbeats 800000 in

/-- A compact local PDO has a unique continuous bilinear transpose on all Schwartz inputs. -/
theorem existsUnique_localFormalTranspose :
    ∃! T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
      IsSchwartzFormalTranspose P T := by
  /- Coordinatewise complex conjugation is a continuous real-linear involution on
  each Schwartz space. Conjugating a map on both sides gives a continuous
  complex-linear map, and this operation is also involutive.
  The Hermitian pairing identity becomes the bilinear transpose identity under
  this conjugation. The equivalence and involution transfer existence and
  uniqueness from the established adjoint theorem. No Hilbert structure on
  Schwartz space is required. -/
  classical
  -- Conjugation on both Schwartz spaces converts Hermitian adjunction to transposition.
  have hExists := existsUnique_localFormalAdjoint m p hp P hP K hK hPK
  let V := EuclideanSpace ℝ (Fin n)
  let H (s : ℕ) := EuclideanSpace ℂ (Fin s)
  -- Coordinatewise conjugation is a continuous real-linear operation on each Schwartz space.
  let c (s : ℕ) : H s →L[ℝ] H s :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin s ↦ ℂ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i ↦ Complex.conjCLE.toContinuousLinearMap.comp
        ((EuclideanSpace.proj i).restrictScalars ℝ)))
  let C (s : ℕ) : 𝓢(V, H s) →L[ℝ] 𝓢(V, H s) := SchwartzMap.postcompCLM (c s)
  have hC (s : ℕ) (u : 𝓢(V, H s)) (x : V) (i : Fin s) :
      C s u x i = (starRingEnd ℂ) (u x i) := rfl
  have hCC (s : ℕ) (u : 𝓢(V, H s)) : C s (C s u) = u := by
    ext x i
    simp only [hC, starRingEnd_self_apply]
  have hCsmul (s : ℕ) (z : ℂ) (u : 𝓢(V, H s)) : C s (z • u) = (starRingEnd ℂ) z • C s u := by
    ext x i
    change (starRingEnd ℂ) (z * u x i) = (starRingEnd ℂ) z * (starRingEnd ℂ) (u x i)
    exact map_mul _ _ _
  let J (T : 𝓢(V, H q) →L[ℂ] 𝓢(V, H r)) : 𝓢(V, H q) →L[ℂ] 𝓢(V, H r) :=
    { toFun := fun v ↦ C r (T (C q v))
      map_add' := by
        intro v w
        simp only [map_add]
      map_smul' := by
        intro z v
        simp only [hCsmul, map_smul, RingHom.id_apply, starRingEnd_self_apply]
      cont := (C r).continuous.comp (T.continuous.comp (C q).continuous) }
  have hJJ (T : 𝓢(V, H q) →L[ℂ] 𝓢(V, H r)) : J (J T) = T := by
    ext v : 1
    change C r (C r (T (C q (C q v)))) = T v
    rw [hCC, hCC]
  -- The same pointwise Hermitian identity becomes the bilinear identity after conjugation.
  have hbridge (T : 𝓢(V, H q) →L[ℂ] 𝓢(V, H r)) :
      IsSchwartzFormalTranspose P (J T) ↔ IsSchwartzFormalAdjoint P T := by
    constructor
    · intro hT u v
      have h := congrArg (starRingEnd ℂ) (hT u (C q v))
      rw [← integral_conj, ← integral_conj] at h
      have hleft (x : V) : (starRingEnd ℂ) (∑ i, J T (C q v) x i * u x i) =
          inner ℂ (u x) (T v x) := by
        have hJ : J T (C q v) = C r (T v) := by
          change C r (T (C q (C q v))) = _
          rw [hCC]
        simp only [hJ, hC, map_sum, map_mul, starRingEnd_self_apply,
          PiLp.inner_apply, RCLike.inner_apply]
      have hright (x : V) : (starRingEnd ℂ) (∑ j, C q v x j * P u x j) =
          inner ℂ (P u x) (v x) := by
        simp only [hC, map_sum, map_mul, starRingEnd_self_apply,
          PiLp.inner_apply, RCLike.inner_apply]
      simpa only [hleft, hright] using h.symm
    · intro hT u a
      have h := congrArg (starRingEnd ℂ) (hT u (C q a))
      rw [← integral_conj, ← integral_conj] at h
      have hleft (x : V) : (starRingEnd ℂ) (inner ℂ (P u x) (C q a x)) =
          ∑ j, a x j * P u x j := by
        simp only [PiLp.inner_apply, RCLike.inner_apply, hC, map_sum, map_mul,
          starRingEnd_self_apply]
      have hright (x : V) : (starRingEnd ℂ) (inner ℂ (u x) (T (C q a) x)) =
          ∑ i, J T a x i * u x i := by
        change (starRingEnd ℂ) (inner ℂ (u x) (T (C q a) x)) =
          ∑ i, C r (T (C q a)) x i * u x i
        simp only [PiLp.inner_apply, RCLike.inner_apply, hC, map_sum, map_mul,
          starRingEnd_self_apply]
      simpa only [hleft, hright] using h.symm
  obtain ⟨Q, hQ, huniq⟩ := hExists
  refine ⟨J Q, (hbridge Q).mpr hQ, ?_⟩
  intro T hT
  have hJT : IsSchwartzFormalAdjoint P (J T) :=
    (hbridge (J T)).mp (by simpa only [hJJ] using hT)
  have heq : J T = Q := huniq (J T) hJT
  exact (hJJ T).symm.trans (congrArg J heq)

/-- The local transpose selected by its unique bilinear integral identity. -/
def localFormalTranspose :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
  (existsUnique_localFormalTranspose m p hp P hP K hK hPK).exists.choose

/-- The chosen local map satisfies the bilinear transpose identity on all tests. -/
theorem isSchwartzFormalTranspose_localFormalTranspose :
    IsSchwartzFormalTranspose P (localFormalTranspose m p hp P hP K hK hPK) := by
  /- Apply the specification of the unique witness in localFormalTranspose.
  Both sides are integrals of Schwartz products and use ordinary multiplication,
  hence correspond to complex-linear covector evaluation rather than an inner product. -/
  exact (existsUnique_localFormalTranspose m p hp P hP K hK hPK).exists.choose_spec

/-- Every cutoff equal to one near the operator support computes the same exact transpose. -/
theorem localFormalTranspose_apply
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupp : HasCompactSupport χ) (hone : K ⊆ interior {x | χ x = 1})
    (a : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (x : EuclideanSpace ℝ (Fin n)) :
    localFormalTranspose m p hp P hP K hK hPK a x = quantize (transposeSymbol χ p) a x := by
  /- Conjugate the established Hermitian adjoint on both Schwartz spaces. Its pairing
  identity becomes the bilinear one, so uniqueness identifies the chosen transpose.
  In the exact adjoint amplitude, conjugation followed by frequency reflection gives
  the transpose amplitude. Continuous real-linear equivalences commute with the
  Bochner integrals without changing the Fourier normalization or lower-order terms. -/
  -- Double conjugation converts the Hermitian adjoint into the bilinear transpose.
  let V := EuclideanSpace ℝ (Fin n)
  let H (s : ℕ) := EuclideanSpace ℂ (Fin s)
  let c (s : ℕ) : H s ≃L[ℝ] H s :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin s ↦ ℂ)).trans
      (ContinuousLinearEquiv.piCongrRight (fun _ : Fin s ↦ Complex.conjCLE))).trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin s ↦ ℂ)).symm
  let C (s : ℕ) : 𝓢(V, H s) →L[ℝ] 𝓢(V, H s) :=
    SchwartzMap.postcompCLM (c s).toContinuousLinearMap
  have hc (s : ℕ) (v : H s) (i : Fin s) :
      c s v i = (starRingEnd ℂ) (v i) := rfl
  have hC (s : ℕ) (v : 𝓢(V, H s)) (y : V) (i : Fin s) :
      C s v y i = (starRingEnd ℂ) (v y i) := rfl
  have hsmul (s : ℕ) (z : ℂ) (v : H s) :
      c s (z • v) = (starRingEnd ℂ) z • c s v := by
    ext i
    change (starRingEnd ℂ) (z * v i) = (starRingEnd ℂ) z * (starRingEnd ℂ) (v i)
    exact map_mul _ _ _
  -- On the original finite fibers, conjugate adjunction is ordinary matrix transpose.
  have hmatrix (y ξ : V) (v : H q) :
      c r ((p y ξ).adjoint (c q v)) = symbolTranspose p y (-ξ) v := by
    ext i
    rw [hc, symbolTranspose_apply, neg_neg]
    have hi := (p y ξ).adjoint_inner_right (EuclideanSpace.single i 1) (c q v)
    rw [EuclideanSpace.inner_single_left] at hi
    simp only [map_one, one_mul] at hi
    rw [hi]
    simp only [PiLp.inner_apply, RCLike.inner_apply, hc, map_sum, map_mul,
      starRingEnd_self_apply, mul_comm]
  have hphase (y ξ : V) :
      (starRingEnd ℂ) (Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ))) =
        Complex.exp (Complex.I * (inner ℝ (x - y) (-ξ) : ℂ)) := by
    rw [← Complex.exp_conj, inner_neg_right]
    congr 1
    simp
  -- Conjugation commutes with both integrals; reflection restores the original phase.
  have hamp : c r (amplitudeApply (adjointAmplitude χ p) (C q a) x) =
      amplitudeApply (transposeAmplitude χ p) a x := by
    unfold amplitudeApply
    rw [map_smul]
    congr 1
    rw [← (c r).integral_comp_comm]
    calc
      _ = ∫ ξ : V, ∫ y : V,
          Complex.exp (Complex.I * (inner ℝ (x - y) (-ξ) : ℂ)) •
            transposeAmplitude χ p x y (-ξ) (a y) := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [← (c r).integral_comp_comm]
        apply integral_congr_ae
        filter_upwards with y
        change c r (Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
          (χ x • (p y ξ).adjoint) (c q (a y))) = _
        rw [hsmul, hphase]
        congr 1
        simp only [smul_apply, map_smul, hmatrix,
          transposeAmplitude]
      _ = _ := integral_neg_eq_self (fun ξ : V ↦ ∫ y : V,
        Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
          transposeAmplitude χ p x y ξ (a y)) volume
  -- The paired conjugations give a complex-linear Schwartz map with the exact identity.
  have hCsmul (s : ℕ) (z : ℂ) (v : 𝓢(V, H s)) :
      C s (z • v) = (starRingEnd ℂ) z • C s v := by
    ext y i
    exact congrArg (fun v : H s ↦ v i) (hsmul s z (v y))
  let Q := localFormalAdjoint m p hp P hP K hK hPK
  let T : 𝓢(V, H q) →L[ℂ] 𝓢(V, H r) :=
    { toFun := fun v ↦ C r (Q (C q v))
      map_add' := by
        intro v w
        simp only [map_add]
      map_smul' := by
        intro z v
        simp only [hCsmul, map_smul, RingHom.id_apply, starRingEnd_self_apply]
      cont := (C r).continuous.comp (Q.continuous.comp (C q).continuous) }
  have hT : IsSchwartzFormalTranspose P T := by
    intro u a
    have h := congrArg (starRingEnd ℂ)
      (isSchwartzFormalAdjoint_localFormalAdjoint m p hp P hP K hK hPK u (C q a))
    rw [← integral_conj, ← integral_conj] at h
    change (∫ y, (starRingEnd ℂ) (inner ℂ (P u y) (C q a y))) =
      ∫ y, (starRingEnd ℂ) (inner ℂ (u y) (Q (C q a) y)) at h
    have hleft (y : V) : (starRingEnd ℂ) (inner ℂ (P u y) (C q a y)) =
        ∑ j, a y j * P u y j := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, hC, map_sum, map_mul,
        starRingEnd_self_apply]
    have hright (y : V) : (starRingEnd ℂ) (inner ℂ (u y) (Q (C q a) y)) =
        ∑ i, T a y i * u y i := by
      change (starRingEnd ℂ) (inner ℂ (u y) (Q (C q a) y)) =
        ∑ i, C r (Q (C q a)) y i * u y i
      simp only [PiLp.inner_apply, RCLike.inner_apply, hC, map_sum, map_mul,
        starRingEnd_self_apply]
    simpa only [hleft, hright] using h.symm
  -- Uniqueness identifies the actual transpose, then exact amplitude reduction gives its symbol.
  have heq : localFormalTranspose m p hp P hP K hK hPK = T :=
    (existsUnique_localFormalTranspose m p hp P hP K hK hPK).unique
      (isSchwartzFormalTranspose_localFormalTranspose m p hp P hP K hK hPK) hT
  have hpSupp : HasCompactSupport p :=
    hK.of_isClosed_subset (isClosed_tsupport p)
      (tsupport_symbol_subset_of_hasOperatorSupport m p hp P hP K hK.isClosed hPK)
  rw [heq]
  change c r (Q (C q a) x) = _
  rw [show Q (C q a) x = quantize (adjointSymbol χ p) (C q a) x from
    localFormalAdjoint_apply m p hp P hP K hK hPK χ hχ hχsupp hone (C q a) x]
  rw [show quantize (adjointSymbol χ p) (C q a) x =
      amplitudeApply (adjointAmplitude χ p) (C q a) x from
    congrFun (quantize_amplitudeSymbol m _ (isAmplitude_adjointAmplitude m p hp χ hχ)
      (hasCompactSupport_adjointAmplitude p hpSupp χ hχsupp) (C q a)) x, hamp]
  exact (congrFun (quantize_amplitudeSymbol m _ (isAmplitude_transposeAmplitude m p hp χ hχ)
    (hasCompactSupport_transposeAmplitude p hpSupp χ hχsupp) a) x).symm

/-- Bilinear transposition exchanges input and output support conditions. -/
theorem HasOperatorSupport.formalTranspose
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (hPK : HasOperatorSupport K P) (hT : IsSchwartzFormalTranspose P T) :
    HasOperatorSupport K T := by
  /- Test Ta against compact smooth vectors in the open complement of K.
  P annihilates them, so nondegeneracy gives zero output there. Conversely, a
  supported away from K annihilates every Pu; the pairing identity gives Ta=0.
  Closedness of K turns pointwise vanishing off K into the output support inclusion. -/
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  -- Compact scalar tests in each fiber coordinate separate continuous outputs on an open set.
  have hseparate (w : 𝓢(V, E)) (U : Set V) (hU : IsOpen U)
      (hw : ∀ u : 𝓢(V, E), tsupport u ⊆ U →
        (∫ x, ∑ i, w x i * u x i) = 0) : ∀ x ∈ U, w x = 0 := by
    intro x hx
    ext i
    have hcont : Continuous (fun y ↦ w y i) := (EuclideanSpace.proj i).continuous.comp w.continuous
    have hae : ∀ᵐ y ∂volume, y ∈ U → w y i = 0 := by
      apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hcont.continuousOn.locallyIntegrableOn hU.measurableSet)
      intro φ hφ hcφ hφU
      let u : 𝓢(V, E) := (hcφ.smul_right).toSchwartzMap
        (hφ.smul (contDiff_const (c := EuclideanSpace.single i (1 : ℂ))))
      have hu : tsupport u ⊆ U := (tsupport_smul_subset_left _ _).trans hφU
      have hi := hw u hu
      change (∫ x, ∑ j, w x j * (φ x • EuclideanSpace.single i 1) j) = 0 at hi
      simpa [Pi.single_apply, ← Complex.coe_smul, mul_comm] using hi
    have hae' : (fun y ↦ w y i) =ᵐ[volume.restrict U] (fun _ ↦ 0) := by
      exact (ae_restrict_iff' hU.measurableSet).mpr hae
    exact Measure.eqOn_open_of_ae_eq hae' hU hcont.continuousOn continuousOn_const hx
  constructor
  · intro v
    apply closure_minimal ?_ hK
    intro x hx
    by_contra hxK
    apply hx
    apply hseparate (T v) Kᶜ hK.isOpen_compl ?_ x hxK
    intro u hu
    have huK : Disjoint (tsupport u) K := Set.disjoint_left.mpr (fun _ hz hKz ↦ hu hz hKz)
    rw [hT u v, hPK.2 u huK]
    simp
  · intro v hv
    have hz : ∀ x ∈ (Set.univ : Set V), T v x = 0 := by
      apply hseparate (T v) Set.univ isOpen_univ
      intro u _
      rw [hT u v]
      apply integral_eq_zero_of_ae
      filter_upwards with x
      by_cases hx : x ∈ K
      · have hvx : v x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hvx ↦ Set.disjoint_left.mp hv hvx hx)
        simp [hvx]
      · have hux : P u x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hux ↦ hx (hPK.1 u hux))
        simp [hux]
    ext x : 1
    exact hz x (Set.mem_univ x)

end AtiyahSinger
