/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateOperator
public import AtiyahSinger.Analysis.EuclideanSobolev

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Formal adjoints in a coordinate chart

Public module ID: M0636.

The local form uses a positive smooth density and the standard Hermitian fiber metric.
Both test sections have compact support in the open chart. This is an integration identity
for differential expressions and is deliberately separate from the bounded Hilbert adjoint.
The global metric/density pairing and adjoint statements are in `GlobalFormalAdjoint`.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Filter
open scoped SchwartzMap ContDiff LineDeriv

variable {n r q m : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

/-- A local smooth differential expression preserves smooth compactly supported tests,
with support contained in that of the original input. Coefficients need only be smooth
on the stated open domain. -/
theorem CoordinateDifferentialOperator.apply_testFunction_properties
    (hU : IsOpen U) (P : CoordinateDifferentialOperator n r q m U)
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
    (hu : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u) (hs : tsupport u ⊆ U) :
    ContDiff ℝ ∞ (P.apply u) ∧ HasCompactSupport (P.apply u) ∧
      tsupport (P.apply u) ⊆ tsupport u := by
  -- Derivatives vanish off the original closed support, regardless of exterior coefficients.
  have hsupp : Function.support (P.apply u) ⊆ tsupport u := by
    intro x hx
    by_contra hx'
    have hz (k : ℕ) : iteratedFDeriv ℝ k u x = 0 := by
      by_contra h
      exact hx' (support_iteratedFDeriv_subset k h)
    exact hx (by simp [CoordinateDifferentialOperator.apply, hz])
  have hclosed : tsupport (P.apply u) ⊆ tsupport u :=
    closure_minimal hsupp isClosed_closure
  refine ⟨contDiff_iff_contDiffAt.mpr (fun x ↦ ?_),
    hcompact.of_isClosed_subset isClosed_closure hclosed, hclosed⟩
  -- On the support use the local smooth coefficients; elsewhere the entire expression is zero.
  by_cases hx : x ∈ tsupport u
  · have hc (k : Fin (m + 1)) (α : Fin k.val → Fin n) :
        ContDiffAt ℝ ∞ (P.coefficient k α) x :=
      (P.smooth_coefficient k α).contDiffAt (hU.mem_nhds (hs hx))
    unfold CoordinateDifferentialOperator.apply
    apply ContDiffAt.sum
    intro k hk
    apply ContDiffAt.sum
    intro α hα
    apply ((ContinuousLinearMap.restrictScalarsL ℂ _ _ ℝ ℝ).contDiff.contDiffAt.comp x
      (hc k α)).clm_apply
    apply ContDiffAt.const_smul
    exact (ContinuousMultilinearMap.apply ℝ _ _
      (fun j ↦ EuclideanSpace.single (α j) 1)).contDiff.contDiffAt.comp x
      (hu.iteratedFDeriv_right (m := ∞) (i := k.val) (by simp)).contDiffAt
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hclosed h)))

/-- The usual defining compact-test identity for the formal adjoint with density w dx. -/
def IsFormalAdjoint (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : CoordinateDifferentialOperator n r q m U)
    (Q : CoordinateDifferentialOperator n q r m U) : Prop :=
  ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
    ∀ v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
      HasCompactSupport u → tsupport u ⊆ U →
      HasCompactSupport v → tsupport v ⊆ U →
      (∫ x, w x • inner ℂ (P.apply u x) (v x)) =
        ∫ x, w x • inner ℂ (u x) (Q.apply v x)

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
/-- every local differential expression has a formal adjoint of order at most m. -/
theorem exists_formalAdjoint (hU : IsOpen U)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiffOn ℝ ∞ w U)
    (hpos : ∀ x ∈ U, 0 < w x) (P : CoordinateDifferentialOperator n r q m U) :
    ∃ Q : CoordinateDifferentialOperator n q r m U, IsFormalAdjoint w P Q := by
  /- For each coefficient aα, move D^α by integration by parts, with no boundary
  contribution because both tests are compactly supported inside U. The resulting
  expression is w⁻¹ Σ D^α(w aα* v). Expand by the Leibniz rule to obtain a differential
  expression of order at most m. Positivity makes w⁻¹ smooth on U.
  With D_j=-i∂_j each D_j is formally self-adjoint for constant density. -/
  classical
  -- Compact tests remain supported in the same closed set after scalar multiplication.
  have hsmulSupport {s : ℕ} (a : ℂ)
      (f : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s))) :
      tsupport (a • f) ⊆ tsupport f := by
    exact tsupport_smul_subset_right (fun _ ↦ a) (fun x ↦ f x)
  -- Stage 1: differentiate a local differential expression without extending its coefficients.
  have hderiv {r q m : ℕ} (P : CoordinateDifferentialOperator n r q m U) (j : Fin n) :
      ∃ Q : CoordinateDifferentialOperator n r q (m + 1) U,
        ∀ (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r)),
          ContDiff ℝ ∞ v → ∀ x ∈ U,
            Q.apply v x = (-Complex.I) • fderiv ℝ (P.apply v) x
              (EuclideanSpace.single j 1) := by
    classical
    let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
    -- The product rule separates differentiated coefficients from the next ordered jet.
    let A : CoordinateDifferentialOperator n r q (m + 1) U := {
      coefficient := fun k α x ↦ if hk : k.val < m + 1 then
        (-Complex.I) • fderivWithin ℝ (P.coefficient ⟨k.val, hk⟩ α) U x e else 0
      smooth_coefficient := by
        intro k α
        by_cases hk : k.val < m + 1
        · simp only [dite_eq_left hk]
          exact ((P.smooth_coefficient ⟨k.val, hk⟩ α).fderivWithin hU.uniqueDiffOn
            (by simp)).clm_apply contDiffOn_const |>.const_smul _
        · simpa only [dite_eq_right hk] using (contDiffOn_const (c := (0 :
            EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))) }
    let B : CoordinateDifferentialOperator n r q (m + 1) U := {
      coefficient := Fin.cases (fun _ _ ↦ 0)
        (fun k α x ↦ if α ⟨0, Nat.zero_lt_succ k.val⟩ = j then
          P.coefficient k (Fin.tail α) x else 0)
      smooth_coefficient := by
        intro k
        refine Fin.cases (fun α ↦ contDiffOn_const) (fun k α ↦ ?_) k
        by_cases hα : α ⟨0, Nat.zero_lt_succ k.val⟩ = j
        · simpa only [Fin.cases_succ, ite_eq_left hα] using P.smooth_coefficient k (Fin.tail α)
        · simpa only [Fin.cases_succ, ite_eq_right hα] using (contDiffOn_const (c := (0 :
            EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))) }
    let Q : CoordinateDifferentialOperator n r q (m + 1) U := {
      coefficient := fun k α x ↦ A.coefficient k α x + B.coefficient k α x
      smooth_coefficient := fun k α ↦ (A.smooth_coefficient k α).add (B.smooth_coefficient k α) }
    refine ⟨Q, ?_⟩
    intro v hv x hx
    -- Padding and reindexing retain the original redundant ordered-coefficient convention.
    have hA : A.apply v x = ∑ k : Fin (m + 1), ∑ α : Fin k.val → Fin n,
        (-Complex.I) • (fderivWithin ℝ (P.coefficient k α) U x e)
          (((-Complex.I) ^ k.val) • iteratedFDeriv ℝ k.val v x
            (fun t ↦ EuclideanSpace.single (α t) 1)) := by
      unfold CoordinateDifferentialOperator.apply
      rw [Fin.sum_univ_castSucc]
      simp only [A, Fin.val_castSucc, Fin.is_lt, dite_eq_left, Fin.eta,
        Fin.val_last, Nat.lt_irrefl, dite_false, zero_apply, Finset.sum_const_zero, add_zero,
        smul_apply]
    have hB : B.apply v x = ∑ k : Fin (m + 1), ∑ α : Fin k.val → Fin n,
        P.coefficient k α x (((-Complex.I) ^ (k.val + 1)) •
          iteratedFDeriv ℝ (k.val + 1) v x
            (Fin.cons e (fun t ↦ EuclideanSpace.single (α t) 1))) := by
      unfold CoordinateDifferentialOperator.apply
      rw [Fin.sum_univ_succ]
      simp only [B, Fin.cases_zero, zero_apply, Finset.sum_const_zero,
        zero_add, Fin.cases_succ, Fin.val_succ]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← (Fin.consEquiv (fun _ : Fin (k.val + 1) ↦ Fin n)).sum_comp,
        Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.tail_cons]
      rw [Finset.sum_eq_single j]
      · apply Finset.sum_congr rfl
        intro α hα
        have hhead : Fin.cons (α := fun _ : Fin (k.val + 1) ↦ Fin n) j α
            ⟨0, Nat.zero_lt_succ k.val⟩ = j := by simp [Fin.cons]
        rw [ite_eq_left hhead]
        congr 2
      · intro i hi hij
        simp [hij]
      · simp
    have hsplit : Q.apply v x = A.apply v x + B.apply v x := by
      simp only [CoordinateDifferentialOperator.apply, Q,
        add_apply, Finset.sum_add_distrib]
    -- Apply the real bilinear product rule to every coefficient and jet, then sum.
    let J (k : Fin (m + 1)) (α : Fin k.val → Fin n) := fun y ↦
      ((-Complex.I) ^ k.val) • iteratedFDeriv ℝ k.val v y
        (fun t ↦ EuclideanSpace.single (α t) 1)
    have hJ (k : Fin (m + 1)) (α : Fin k.val → Fin n) : ContDiff ℝ ∞ (J k α) :=
      ((ContinuousMultilinearMap.apply ℝ _ _
        (fun t ↦ EuclideanSpace.single (α t) 1)).contDiff.comp
        (hv.iteratedFDeriv_right (m := ∞) (i := k.val) (by simp))).const_smul _
    have hc (k : Fin (m + 1)) (α : Fin k.val → Fin n) :
        DifferentiableAt ℝ (P.coefficient k α) x :=
      ((P.smooth_coefficient k α).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    let B₀ := (ContinuousLinearMap.id ℂ
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))).bilinearRestrictScalars ℝ
    have ht (k : Fin (m + 1)) (α : Fin k.val → Fin n) :=
      B₀.hasFDerivAt_of_bilinear (hc k α).hasFDerivAt
        ((hJ k α).differentiable (by simp) x).hasFDerivAt
    have hsum := HasFDerivAt.sum (u := Finset.univ) (fun k hk ↦
      HasFDerivAt.sum (u := Finset.univ) (fun α hα ↦ ht k α))
    have heq : P.apply v = ∑ k : Fin (m + 1), ∑ α : Fin k.val → Fin n,
        (fun y ↦ B₀ (P.coefficient k α y) (J k α y)) := by
      funext y
      simp only [Finset.sum_apply]
      rfl
    rw [hsplit, hA, hB, heq]
    rw [hsum.fderiv]
    simp only [sum_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro α hα
    have hdJ : fderiv ℝ (J k α) x e = ((-Complex.I) ^ k.val) •
        iteratedFDeriv ℝ (k.val + 1) v x
          (Fin.cons e (fun t ↦ EuclideanSpace.single (α t) 1)) := by
      let L := ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin k.val ↦ EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℂ (Fin r))
        (fun t ↦ EuclideanSpace.single (α t) 1)
      have hD := (hv.iteratedFDeriv_right (m := ∞) (i := k.val) (by simp)).differentiable
        (by simp) x
      have hL := L.hasFDerivAt.comp x hD.hasFDerivAt
      change (fderiv ℝ (((-Complex.I) ^ k.val) • (L ∘ iteratedFDeriv ℝ k.val v)) x) e = _
      rw [fderiv_const_smul hL.differentiableAt, hL.fderiv]
      rfl
    rw [fderivWithin_of_isOpen hU hx]
    change (-Complex.I) • (fderiv ℝ (P.coefficient k α) x e) (J k α x) +
        P.coefficient k α x (((-Complex.I) ^ (k.val + 1)) •
          iteratedFDeriv ℝ (k.val + 1) v x
            (Fin.cons e (fun t ↦ EuclideanSpace.single (α t) 1))) =
      (-Complex.I) • (P.coefficient k α x (fderiv ℝ (J k α) x e) +
        (fderiv ℝ (P.coefficient k α) x e) (J k α x))
    rw [hdJ]
    simp only [map_smul, smul_add, pow_succ, mul_smul]
    module
  -- Stage 2: D_j = -i ∂_j is self-adjoint for unweighted Schwartz tests.
  have hIBP {r : ℕ} (u v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (e : EuclideanSpace ℝ (Fin n)) :
      (∫ x, inner ℂ ((-Complex.I) • (∂_{e} u) x) (v x)) =
        ∫ x, inner ℂ (u x) ((-Complex.I) • (∂_{e} v) x) := by
    let B := (isBoundedBilinearMap_inner (𝕜 := ℂ)
      (E := EuclideanSpace ℂ (Fin r))).toContinuousLinearMap
    have h := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left (μ := volume) u v B e
    change (∫ x, inner ℂ (u x) ((∂_{e} v) x)) =
      -(∫ x, inner ℂ ((∂_{e} u) x) (v x)) at h
    simp only [inner_smul_left, inner_smul_right, map_neg, Complex.conj_I, neg_neg]
    rw [integral_const_mul, integral_const_mul, h]
    ring
  
  -- The Hermitian adjoint is real linear, although it is conjugate linear over ℂ.
  have hadj {r q : ℕ} : ContDiff ℝ ∞ (fun c : EuclideanSpace ℂ (Fin r) →L[ℂ]
      EuclideanSpace ℂ (Fin q) ↦ c.adjoint) := by
    let adj : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) →L[ℝ]
        (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)) := {
      toFun := fun c ↦ c.adjoint
      map_add' := fun c d ↦ map_add _ c d
      map_smul' := by
        intro a c
        simp only [RingHom.id_apply, ← Complex.coe_smul, map_smulₛₗ,
          Complex.conj_ofReal]
      cont := ContinuousLinearMap.adjoint.continuous }
    exact adj.contDiff
  -- Stage 3: move one ordered derivative at a time, with compact support removing boundaries.
  have hterm (k : ℕ) (α : Fin k → Fin n)
      (c : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
      (hc : ContDiffOn ℝ ∞ c U) :
      ∃ Q : CoordinateDifferentialOperator n q r k U,
        ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
          (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))),
          HasCompactSupport u → tsupport u ⊆ U →
          HasCompactSupport v → tsupport v ⊆ U →
          (∫ x, inner ℂ (c x (((-Complex.I) ^ k) •
            (∂^{fun t ↦ EuclideanSpace.single (α t) (1 : ℝ)} u) x)) (v x)) =
          ∫ x, inner ℂ (u x) (Q.apply v x) := by
    induction k generalizing c with
    | zero =>
      -- Multiplication by a matrix has its pointwise Hermitian adjoint.
      let Q : CoordinateDifferentialOperator n q r 0 U := {
        coefficient := fun _ _ x ↦ (c x).adjoint
        smooth_coefficient := fun _ _ ↦ hadj.comp_contDiffOn hc }
      refine ⟨Q, ?_⟩
      intro u v hu huU hv hvU
      apply integral_congr_ae
      filter_upwards [] with x
      simp [CoordinateDifferentialOperator.apply, Q,
        ContinuousLinearMap.adjoint_inner_right]
    | succ k ih =>
      -- Peel off the last derivative and differentiate the already constructed adjoint.
      obtain ⟨Q₀, hQ₀⟩ := ih (Fin.init α) c hc
      let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (α (Fin.last k)) (1 : ℝ)
      obtain ⟨Q, hQ⟩ := hderiv Q₀ (α (Fin.last k))
      refine ⟨Q, ?_⟩
      intro u v hu huU hv hvU
      let uD : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
        (-Complex.I) • ∂_{e} u
      have huDs : tsupport uD ⊆ tsupport u :=
        (hsmulSupport (-Complex.I) (∂_{e} u)).trans
          (SchwartzMap.tsupport_lineDerivOp_subset e u)
      have huDc : HasCompactSupport uD := hu.of_isClosed_subset isClosed_closure huDs
      obtain ⟨hQv, hQvc, hQvs⟩ := Q₀.apply_testFunction_properties hU v (v.smooth ⊤) hv hvU
      let vQ : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
        hQvc.toSchwartzMap hQv
      have hleft : (fun x ↦ c x (((-Complex.I) ^ (k + 1)) •
          (∂^{fun t ↦ EuclideanSpace.single (α t) (1 : ℝ)} u) x)) =
          fun x ↦ c x (((-Complex.I) ^ k) •
            (∂^{fun t ↦ EuclideanSpace.single (Fin.init α t) (1 : ℝ)} uD) x) := by
        funext x
        simp only [LineDeriv.iteratedLineDerivOp_succ_right, uD,
          LineDeriv.iteratedLineDerivOp_smul, smul_apply, pow_succ, mul_smul]
        rfl
      calc
        _ = ∫ x, inner ℂ (uD x) (Q₀.apply v x) := by
          simp_rw [congrFun hleft]
          exact hQ₀ uD v huDc (huDs.trans huU) hv hvU
        _ = ∫ x, inner ℂ (u x) ((-Complex.I) • (∂_{e} vQ) x) := by
          have h := hIBP u vQ e
          change (∫ x, inner ℂ (uD x) (vQ x)) = _ at h
          exact h
        _ = ∫ x, inner ℂ (u x) (Q.apply v x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          by_cases hx : x ∈ U
          · rw [hQ v (v.smooth ⊤) x hx]
            rfl
          · have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport
              (fun hs ↦ hx (huU hs))
            simp [hu0]
  -- Stage 4: pad every lower-order expression to the original common order.
  have hlift {k m : ℕ} (hkm : k ≤ m) (Q : CoordinateDifferentialOperator n q r k U) :
      ∃ R : CoordinateDifferentialOperator n q r m U, ∀ v x, R.apply v x = Q.apply v x := by
    induction m, hkm using Nat.le_induction with
    | base => exact ⟨Q, fun _ _ ↦ rfl⟩
    | succ m hkm ih =>
      obtain ⟨R, hR⟩ := ih
      let S : CoordinateDifferentialOperator n q r (m + 1) U := {
        coefficient := fun j α x ↦ if hj : j.val < m + 1 then R.coefficient ⟨j.val, hj⟩ α x else 0
        smooth_coefficient := by
          intro j α
          by_cases hj : j.val < m + 1
          · simpa only [dite_eq_left hj] using R.smooth_coefficient ⟨j.val, hj⟩ α
          · simpa only [dite_eq_right hj] using (contDiffOn_const (c := (0 :
              EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)))) }
      refine ⟨S, fun v x ↦ ?_⟩
      rw [← hR v x]
      unfold CoordinateDifferentialOperator.apply
      rw [Fin.sum_univ_castSucc]
      simp only [S, Fin.val_castSucc, Fin.is_lt, dite_eq_left, Fin.eta,
        Fin.val_last, Nat.lt_irrefl, dite_false, zero_apply, Finset.sum_const_zero, add_zero]
  -- Stage 5: absorb the density into the original coefficients before integration by parts.
  let ι := Σ k : Fin (m + 1), Fin k.val → Fin n
  let c (i : ι) := fun x ↦ w x • P.coefficient i.1 i.2 x
  have hc (i : ι) : ContDiffOn ℝ ∞ (c i) U := hw.smul (P.smooth_coefficient i.1 i.2)
  have hex (i : ι) : ∃ Q : CoordinateDifferentialOperator n q r m U,
      ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
        (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))),
        HasCompactSupport u → tsupport u ⊆ U → HasCompactSupport v → tsupport v ⊆ U →
        (∫ x, inner ℂ (c i x (((-Complex.I) ^ i.1.val) •
          (∂^{fun t ↦ EuclideanSpace.single (i.2 t) (1 : ℝ)} u) x)) (v x)) =
        ∫ x, inner ℂ (u x) (Q.apply v x) := by
    obtain ⟨Q, hQ⟩ := hterm i.1.val i.2 (c i) (hc i)
    obtain ⟨R, hR⟩ := hlift (Nat.le_of_lt_succ i.1.is_lt) Q
    refine ⟨R, ?_⟩
    intro u v hu huU hv hvU
    simp_rw [hR]
    exact hQ u v hu huU hv hvU
  choose Qs hQs using hex
  -- Divide the finite sum of adjoints by the same positive density, only using smoothness on U.
  let Q : CoordinateDifferentialOperator n q r m U := {
    coefficient := fun j β x ↦ (w x)⁻¹ • ∑ i : ι, (Qs i).coefficient j β x
    smooth_coefficient := by
      intro j β
      apply (hw.inv (fun x hx ↦ ne_of_gt (hpos x hx))).smul
      exact ContDiffOn.sum (fun i _ ↦ (Qs i).smooth_coefficient j β) }
  have hQa (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin q)) (x) :
      Q.apply v x = (w x)⁻¹ • ∑ i : ι, (Qs i).apply v x := by
    simp only [CoordinateDifferentialOperator.apply, Q, smul_apply, sum_apply,
      Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
  refine ⟨Q, ?_⟩
  intro u v hu huU hv hvU
  -- Stage 6: compact support makes all finite-sum integral exchanges legitimate.
  have htest (i : ι) : HasCompactSupport
      ((-Complex.I) ^ i.1.val • ∂^{fun t ↦ EuclideanSpace.single (i.2 t) (1 : ℝ)} u) := by
    apply hu.of_isClosed_subset isClosed_closure
    exact (hsmulSupport ((-Complex.I) ^ i.1.val)
      (∂^{fun t ↦ EuclideanSpace.single (i.2 t) (1 : ℝ)} u)).trans
      (SchwartzMap.tsupport_iteratedLineDerivOp_subset _ u)
  have htestU (i : ι) : tsupport
      ((-Complex.I) ^ i.1.val • ∂^{fun t ↦ EuclideanSpace.single (i.2 t) (1 : ℝ)} u) ⊆ U :=
    (hsmulSupport ((-Complex.I) ^ i.1.val)
      (∂^{fun t ↦ EuclideanSpace.single (i.2 t) (1 : ℝ)} u)).trans
      ((SchwartzMap.tsupport_iteratedLineDerivOp_subset _ u).trans huU)
  have hleftInt (i : ι) : Integrable (fun x ↦ inner ℂ
      (c i x (((-Complex.I) ^ i.1.val) •
        (∂^{fun t ↦ EuclideanSpace.single (i.2 t) (1 : ℝ)} u) x)) (v x)) := by
    let C : CoordinateDifferentialOperator n r q 0 U := {
      coefficient := fun _ _ ↦ c i
      smooth_coefficient := fun _ _ ↦ hc i }
    let ui : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
      (-Complex.I) ^ i.1.val • ∂^{fun t ↦ EuclideanSpace.single (i.2 t) (1 : ℝ)} u
    obtain ⟨hs, hcpt, _⟩ := C.apply_testFunction_properties hU ui (ui.smooth ⊤)
      (htest i) (htestU i)
    have h := (hs.continuous.inner (𝕜 := ℂ) v.continuous).integrable_of_hasCompactSupport
      (μ := volume) (hcpt.comp₂_left hv (by simp))
    simpa [CoordinateDifferentialOperator.apply, C, ui] using h
  have hrightInt (i : ι) : Integrable (fun x ↦ inner ℂ (u x) ((Qs i).apply v x)) := by
    obtain ⟨hs, hcpt, _⟩ := (Qs i).apply_testFunction_properties hU v (v.smooth ⊤) hv hvU
    exact (u.continuous.inner (𝕜 := ℂ) hs.continuous).integrable_of_hasCompactSupport
      (μ := volume) (hu.comp₂_left hcpt (by simp))
  -- Stage 7: assemble the identity and cancel the density on U; the test is zero outside U.
  calc
    _ = ∫ x, ∑ i : ι, inner ℂ (c i x (((-Complex.I) ^ i.1.val) •
        (∂^{fun t ↦ EuclideanSpace.single (i.2 t) (1 : ℝ)} u) x)) (v x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [ι]
      simp only [c, smul_apply, inner_smul_left_eq_smul,
        SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, Fintype.sum_sigma,
        CoordinateDifferentialOperator.apply, sum_inner, Finset.smul_sum]
    _ = ∑ i : ι, ∫ x, inner ℂ (c i x (((-Complex.I) ^ i.1.val) •
        (∂^{fun t ↦ EuclideanSpace.single (i.2 t) (1 : ℝ)} u) x)) (v x) :=
      integral_finsetSum _ (fun i _ ↦ hleftInt i)
    _ = ∑ i : ι, ∫ x, inner ℂ (u x) ((Qs i).apply v x) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hQs i u v hu huU hv hvU
    _ = ∫ x, ∑ i : ι, inner ℂ (u x) ((Qs i).apply v x) :=
      (integral_finsetSum _ (fun i _ ↦ hrightInt i)).symm
    _ = ∫ x, w x • inner ℂ (u x) (Q.apply v x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ U
      · rw [hQa]
        simp only [inner_smul_right_eq_smul, smul_smul,
          mul_inv_cancel₀ (ne_of_gt (hpos x hx)), one_smul, inner_sum]
      · have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hs ↦ hx (huU hs))
        simp [hu0]

/-- uniqueness concerns the operator on tests, not a redundant coefficient presentation. -/
theorem formalAdjoint_apply_eq (hU : IsOpen U)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiffOn ℝ ∞ w U)
    (hpos : ∀ x ∈ U, 0 < w x)
    (P : CoordinateDifferentialOperator n r q m U)
    (Q R : CoordinateDifferentialOperator n q r m U)
    (hQ : IsFormalAdjoint w P Q) (hR : IsFormalAdjoint w P R) :
    ∀ v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
      HasCompactSupport v → tsupport v ⊆ U → ∀ x ∈ U, Q.apply v x = R.apply v x := by
  /- Subtract the two test identities. For fixed v, the smooth function (Q-R)v
  is itself an admissible compactly supported smooth test. Its weighted squared norm
  has integral zero. Positivity on U and continuity imply pointwise equality. -/
  classical
  intro v hv hvU
  obtain ⟨hQv, hQvc, hQvs⟩ := Q.apply_testFunction_properties hU v (v.smooth ⊤) hv hvU
  obtain ⟨hRv, hRvc, hRvs⟩ := R.apply_testFunction_properties hU v (v.smooth ⊤) hv hvU
  let f := fun x ↦ Q.apply v x - R.apply v x
  have hf : ContDiff ℝ ∞ f := hQv.sub hRv
  have hfc : HasCompactSupport f := hQvc.sub hRvc
  have hfs : tsupport f ⊆ U :=
    (tsupport_sub _ _).trans (Set.union_subset (hQvs.trans hvU) (hRvs.trans hvU))
  let u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) := hfc.toSchwartzMap hf
  -- The density is needed only near the compact support of the test.
  have hwf : Continuous (fun x ↦ w x • f x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport f
    · exact ((hw.continuousOn.continuousAt (hU.mem_nhds (hfs hx))).smul hf.continuous.continuousAt)
    · apply (continuousAt_const (y := (0 : EuclideanSpace ℂ (Fin r)))).congr
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
  have hwfc : HasCompactSupport (fun x ↦ w x • f x) := hfc.smul_left (f := w)
  have hiQ : MeasureTheory.Integrable (fun x ↦ w x • inner ℂ (f x) (Q.apply v x)) := by
    have hi := (hwf.inner (𝕜 := ℂ) hQv.continuous).integrable_of_hasCompactSupport (μ := volume)
      (hwfc.comp₂_left hQvc (by simp))
    simpa only [inner_smul_left_eq_smul] using hi
  have hiR : MeasureTheory.Integrable (fun x ↦ w x • inner ℂ (f x) (R.apply v x)) := by
    have hi := (hwf.inner (𝕜 := ℂ) hRv.continuous).integrable_of_hasCompactSupport (μ := volume)
      (hwfc.comp₂_left hRvc (by simp))
    simpa only [inner_smul_left_eq_smul] using hi
  have heq := (hQ u v hfc hfs hv hvU).symm.trans (hR u v hfc hfs hv hvU)
  have hz : (∫ x, w x • inner ℂ (f x) (f x)) = 0 := by
    change (∫ x, w x • inner ℂ (f x) (Q.apply v x - R.apply v x)) = 0
    simp only [inner_sub_right, smul_sub]
    rw [MeasureTheory.integral_sub hiQ hiR, sub_eq_zero]
    exact heq
  have hif : MeasureTheory.Integrable (fun x ↦ w x • inner ℂ (f x) (f x)) := by
    apply (hiQ.sub hiR).congr
    filter_upwards [] with x
    change w x • inner ℂ (f x) (Q.apply v x) -
      w x • inner ℂ (f x) (R.apply v x) = w x • inner ℂ (f x) (Q.apply v x - R.apply v x)
    rw [inner_sub_right, smul_sub]
  have hreal : (∫ x, w x * ‖f x‖ ^ 2) = 0 := by
    have h := congrArg (RCLike.re : ℂ → ℝ) hz
    rw [← integral_re hif] at h
    simpa only [← RCLike.re_eq_complex_re, RCLike.smul_re,
      inner_self_eq_norm_sq, map_zero] using h
  have hnonneg : ∀ x, 0 ≤ w x * ‖f x‖ ^ 2 := by
    intro x
    by_cases hx : x ∈ U
    · exact mul_nonneg (hpos x hx).le (sq_nonneg _)
    · have hz' : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hs ↦ hx (hfs hs))
      simp [hz']
  have hic : MeasureTheory.Integrable (fun x ↦ w x * ‖f x‖ ^ 2) := by
    simpa only [← RCLike.re_eq_complex_re, RCLike.smul_re, inner_self_eq_norm_sq] using hif.re
  have hae := (MeasureTheory.integral_eq_zero_iff_of_nonneg hnonneg hic).mp hreal
  have hcont : Continuous (fun x ↦ w x * ‖f x‖ ^ 2) := by
    have h' : Continuous (fun x ↦ RCLike.re (inner ℂ (w x • f x) (f x))) :=
      Complex.continuous_re.comp (hwf.inner (𝕜 := ℂ) hf.continuous)
    simpa only [inner_smul_left_eq_smul, RCLike.smul_re, inner_self_eq_norm_sq] using h'
  have hall := MeasureTheory.Measure.eq_of_ae_eq hae hcont continuous_const
  intro x hx
  have hx0 : w x * ‖f x‖ ^ 2 = 0 := congrFun hall x
  have hfn : ‖f x‖ ^ 2 = 0 := (mul_eq_zero.mp hx0).resolve_left (ne_of_gt (hpos x hx))
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hfn))

end AtiyahSinger
