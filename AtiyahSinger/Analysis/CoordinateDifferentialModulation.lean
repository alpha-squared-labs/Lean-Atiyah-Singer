/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialSymbol
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exact modulation of a second-order coordinate differential expression

Public module ID: M0407.

The original ordered coefficients determine the complete finite product rule. This is an
exact identity for the actual differential expression, including its lower-order terms;
it does not infer exact composition from an asymptotic symbol expansion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.CoordinateDifferentialOperator

open scoped ContDiff Topology

variable {n r q : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

/-- Modulating a smooth section gives its full polynomial symbol and the two finite
derivative corrections, with the original ordered coefficients and the convention
`Dⱼ = -i ∂ⱼ`. Smoothness is only required on the original open coordinate domain. -/
theorem apply_cexp_smul_order_two (hU : IsOpen U)
    (P : CoordinateDifferentialOperator n r q 2 U)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
    (hv : ContDiffOn ℝ ∞ v U) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    P.apply (fun y ↦ Complex.exp (Complex.I * (inner ℝ y ξ : ℂ)) • v y) x =
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        (P.totalSymbol x ξ (v x) +
          (∑ α : Fin 1 → Fin n,
            P.coefficient 1 α x ((-Complex.I) •
              fderiv ℝ v x (EuclideanSpace.single (α 0) 1))) +
          ∑ α : Fin 2 → Fin n,
            P.coefficient 2 α x
              ((-Complex.I) •
                  ((ξ (α 0) : ℂ) • fderiv ℝ v x (EuclideanSpace.single (α 1) 1) +
                    (ξ (α 1) : ℂ) • fderiv ℝ v x (EuclideanSpace.single (α 0) 1)) -
                iteratedFDeriv ℝ 2 v x
                  (fun j ↦ EuclideanSpace.single (α j) 1))) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let L : X →L[ℝ] ℂ :=
    (Complex.I • Complex.ofRealCLM).comp (innerSL ℝ ξ)
  let phase : X → ℂ := fun y ↦ Complex.exp (L y)
  have hL (y : X) : L y = Complex.I * (inner ℝ y ξ : ℂ) := by
    simp [L, real_inner_comm]
  have hLc (i : Fin n) : L (EuclideanSpace.single i 1) = Complex.I * (ξ i : ℂ) := by
    have hi : inner ℝ ξ (EuclideanSpace.single i 1) = ξ i := by
      simpa only [one_mul, conj_trivial] using
        EuclideanSpace.inner_single_right i (1 : ℝ) ξ
    change Complex.I * (inner ℝ ξ (EuclideanSpace.single i 1) : ℂ) = _
    rw [hi]
  have hphase : ContDiff ℝ ∞ phase := L.contDiff.cexp
  have hmod : ContDiffOn ℝ ∞ (fun y ↦ phase y • v y) U :=
    hphase.contDiffOn.smul hv
  -- Differentiate the product locally. No global smooth extension of v is chosen.
  have hfirst (w : X → V) (hw : ContDiffOn ℝ ∞ w U) (z : X) (hz : z ∈ U)
      (d : X) :
      fderiv ℝ (fun y ↦ phase y • w y) z d =
        phase z • (L d • w z + fderiv ℝ w z d) := by
    have hwd := (hw.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    have he := ((L.hasFDerivAt (x := z)).cexp.smul hwd.hasFDerivAt).fderiv
    change (fderiv ℝ ((fun y ↦ Complex.exp (L y)) • w) z) d = _
    rw [he]
    change phase z • fderiv ℝ w z d + (phase z * L d) • w z = _
    simp only [smul_add, smul_smul]
    exact add_comm _ _
  have heval (w : X → V) (hw : ContDiffOn ℝ ∞ w U) (z : X) (hz : z ∈ U)
      (d₁ d₂ : X) :
      fderiv ℝ (fun y ↦ fderiv ℝ w y d₂) z d₁ =
        fderiv ℝ (fderiv ℝ w) z d₁ d₂ := by
    have hd : DifferentiableAt ℝ (fderiv ℝ w) z :=
      ((hw.fderiv_of_isOpen (m := ∞) hU (by simp)).contDiffAt
        (hU.mem_nhds hz)).differentiableAt (by simp)
    let ev : (X →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V d₂
    exact congrArg (fun A : X →L[ℝ] V ↦ A d₁)
      (ev.hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  -- Applying the first product rule twice retains both ordered mixed terms.
  have hsecond (d : Fin 2 → X) :
      iteratedFDeriv ℝ 2 (fun y ↦ phase y • v y) x d =
        phase x • ((L (d 0) * L (d 1)) • v x +
          L (d 0) • fderiv ℝ v x (d 1) +
          L (d 1) • fderiv ℝ v x (d 0) + iteratedFDeriv ℝ 2 v x d) := by
    let w : X → V := fun y ↦ L (d 1) • v y + fderiv ℝ v y (d 1)
    have hvd : ContDiffOn ℝ ∞ (fun y ↦ fderiv ℝ v y (d 1)) U :=
      (hv.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    have hw : ContDiffOn ℝ ∞ w U := (hv.const_smul _).add hvd
    have hnear : (fun y ↦ fderiv ℝ (fun z ↦ phase z • v z) y (d 1)) =ᶠ[𝓝 x]
        (fun y ↦ phase y • w y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hfirst v hv y hy (d 1)
    have hdv : DifferentiableAt ℝ v x :=
      (hv.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hdvd : DifferentiableAt ℝ (fun y ↦ fderiv ℝ v y (d 1)) x :=
      (hvd.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hdw : fderiv ℝ w x (d 0) =
        L (d 1) • fderiv ℝ v x (d 0) + iteratedFDeriv ℝ 2 v x d := by
      change fderiv ℝ (fun y ↦ L (d 1) • v y + fderiv ℝ v y (d 1)) x (d 0) = _
      have hconst : DifferentiableAt ℝ (fun y ↦ L (d 1) • v y) x :=
        hdv.const_smul (L (d 1))
      rw [fderiv_fun_add hconst hdvd, fderiv_fun_const_smul hdv]
      change L (d 1) • fderiv ℝ v x (d 0) +
        fderiv ℝ (fun y ↦ fderiv ℝ v y (d 1)) x (d 0) = _
      rw [heval v hv x hx, iteratedFDeriv_two_apply]
    rw [iteratedFDeriv_two_apply, ← heval _ hmod x hx]
    rw [hnear.fderiv_eq, hfirst w hw x hx, hdw]
    dsimp only [w]
    simp only [smul_add, smul_smul]
    module
  -- The phase derivative supplies exactly the frequency factors for degrees 0, 1, 2.
  have hj₀ (α : Fin 0 → Fin n) :
      ((-Complex.I) ^ (0 : ℕ)) •
          iteratedFDeriv ℝ 0 (fun y ↦ phase y • v y) x
            (fun j ↦ EuclideanSpace.single (α j) 1) = phase x • v x := by
    simp
  have hj₁ (α : Fin 1 → Fin n) :
      (-Complex.I) ^ (1 : ℕ) •
          iteratedFDeriv ℝ 1 (fun y ↦ phase y • v y) x
            (fun j ↦ EuclideanSpace.single (α j) 1) =
        phase x • ((ξ (α 0) : ℂ) • v x +
          (-Complex.I) • fderiv ℝ v x (EuclideanSpace.single (α 0) 1)) := by
    rw [pow_one, iteratedFDeriv_one_apply, hfirst v hv x hx, smul_comm (-Complex.I)]
    congr 1
    rw [smul_add, hLc, smul_smul]
    have hscalar : (-Complex.I) * (Complex.I * (ξ (α 0) : ℂ)) = (ξ (α 0) : ℂ) := by
      rw [← mul_assoc]
      simp
    rw [hscalar]
  have hj₂ (α : Fin 2 → Fin n) :
      (-Complex.I) ^ (2 : ℕ) •
          iteratedFDeriv ℝ 2 (fun y ↦ phase y • v y) x
            (fun j ↦ EuclideanSpace.single (α j) 1) =
        phase x • (((ξ (α 0) : ℂ) * (ξ (α 1) : ℂ)) • v x +
          ((-Complex.I) •
              ((ξ (α 0) : ℂ) • fderiv ℝ v x (EuclideanSpace.single (α 1) 1) +
                (ξ (α 1) : ℂ) • fderiv ℝ v x (EuclideanSpace.single (α 0) 1)) -
            iteratedFDeriv ℝ 2 v x (fun j ↦ EuclideanSpace.single (α j) 1))) := by
    rw [hsecond, smul_comm ((-Complex.I) ^ 2)]
    congr 1
    have hprod : L (EuclideanSpace.single (α 0) 1) *
        L (EuclideanSpace.single (α 1) 1) =
          -((ξ (α 0) : ℂ) * (ξ (α 1) : ℂ)) := by
      rw [hLc, hLc]
      calc
        _ = (Complex.I * Complex.I) * ((ξ (α 0) : ℂ) * (ξ (α 1) : ℂ)) := by ring
        _ = _ := by simp
    rw [hprod, hLc, hLc]
    norm_num only [neg_sq, Complex.I_sq]
    simp only [smul_add, smul_smul]
    module
  -- Sum the exact finite identities using the original coefficients of P.
  let T (k : Fin 3) : EuclideanSpace ℂ (Fin q) :=
    ∑ α : Fin k.val → Fin n,
      P.coefficient k α x (((-Complex.I) ^ k.val) •
        iteratedFDeriv ℝ k.val (fun y ↦ phase y • v y) x
          (fun j ↦ EuclideanSpace.single (α j) 1))
  let B (k : Fin 3) : EuclideanSpace ℂ (Fin q) :=
    ∑ α : Fin k.val → Fin n,
      ((∏ j, ξ (α j) : ℝ) : ℂ) • P.coefficient k α x (v x)
  let R₁ : EuclideanSpace ℂ (Fin q) :=
    ∑ α : Fin 1 → Fin n,
      P.coefficient 1 α x
        ((-Complex.I) • fderiv ℝ v x (EuclideanSpace.single (α 0) 1))
  let R₂ : EuclideanSpace ℂ (Fin q) :=
    ∑ α : Fin 2 → Fin n,
      P.coefficient 2 α x
        ((-Complex.I) •
            ((ξ (α 0) : ℂ) • fderiv ℝ v x (EuclideanSpace.single (α 1) 1) +
              (ξ (α 1) : ℂ) • fderiv ℝ v x (EuclideanSpace.single (α 0) 1)) -
          iteratedFDeriv ℝ 2 v x (fun j ↦ EuclideanSpace.single (α j) 1))
  have hT₀ : T 0 = phase x • B 0 := by
    change (∑ α : Fin 0 → Fin n,
      P.coefficient 0 α x (((-Complex.I) ^ (0 : ℕ)) •
        iteratedFDeriv ℝ 0 (fun y ↦ phase y • v y) x
          (fun j ↦ EuclideanSpace.single (α j) 1))) =
      phase x • ∑ α : Fin 0 → Fin n,
        ((∏ j : Fin 0, ξ (α j) : ℝ) : ℂ) • P.coefficient 0 α x (v x)
    simp only [hj₀, Fin.prod_univ_zero, Complex.ofReal_one, one_smul, map_smul,
      Finset.smul_sum]
  have hT₁ : T 1 = phase x • (B 1 + R₁) := by
    change (∑ α : Fin 1 → Fin n,
      P.coefficient 1 α x (((-Complex.I) ^ (1 : ℕ)) •
        iteratedFDeriv ℝ 1 (fun y ↦ phase y • v y) x
          (fun j ↦ EuclideanSpace.single (α j) 1))) =
      phase x • ((∑ α : Fin 1 → Fin n,
        ((∏ j : Fin 1, ξ (α j) : ℝ) : ℂ) • P.coefficient 1 α x (v x)) + R₁)
    simp only [hj₁, Fin.prod_univ_one, R₁, map_smul, map_add, smul_add,
      Finset.sum_add_distrib, Finset.smul_sum]
  have hT₂ : T 2 = phase x • (B 2 + R₂) := by
    change (∑ α : Fin 2 → Fin n,
      P.coefficient 2 α x (((-Complex.I) ^ (2 : ℕ)) •
        iteratedFDeriv ℝ 2 (fun y ↦ phase y • v y) x
          (fun j ↦ EuclideanSpace.single (α j) 1))) =
      phase x • ((∑ α : Fin 2 → Fin n,
        ((∏ j : Fin 2, ξ (α j) : ℝ) : ℂ) • P.coefficient 2 α x (v x)) + R₂)
    simp only [hj₂, Fin.prod_univ_two, Complex.ofReal_mul, R₂, map_smul, map_add,
      smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  have htotal : P.totalSymbol x ξ (v x) = B 0 + B 1 + B 2 := by
    calc
      _ = ∑ k : Fin 3, B k := by
        simp only [totalSymbol, sum_apply, smul_apply]
        simp only [B, Complex.coe_smul]
      _ = _ := Fin.sum_univ_three B
  simp only [← hL]
  change (∑ k : Fin 3, T k) = phase x • (P.totalSymbol x ξ (v x) + R₁ + R₂)
  rw [Fin.sum_univ_three, hT₀, hT₁, hT₂, htotal]
  simp only [smul_add]
  abel

end AtiyahSinger.CoordinateDifferentialOperator
