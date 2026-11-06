/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LocalAdjoint

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Composition of compactly supported local pseudodifferential operators

Public module ID: M0784.

SG Theorem 3.10, (3.10), and its proof on pp.184-185. Following the book,
the exact symbol is obtained by reducing p(x,ξ)r(y,ξ), where r is the pointwise
Hermitian adjoint of the left symbol of Q*. The full Schwartz pairing justifies
the Fourier formula globally, rather than Fourier transforming an equality only on K.
The product order is P after Q: rectangular matrices are composed in that order.
The ordinary-derivative coefficient is (-i)^j/j!, summed over ordered coordinate lists.
The comparison with `principalSymbolComp` is for the actual S^m/S^(m-1) quotient.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 15

variable {n r s t : ℕ}

/-- The forward Fourier expression associated to a right symbol, with no inverse factor. -/
def rightSymbolFourierApply (b : SymbolFunction n r s)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (ξ : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin s) :=
  ∫ y, Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • b y ξ (u y)

/-- The composition amplitude of a left symbol p and a right symbol b. -/
def leftRightAmplitude (p : SymbolFunction n s t) (b : SymbolFunction n r s) :
    AmplitudeFunction n r t := fun x y ξ ↦ (p x ξ).comp (b y ξ)

/-- SG's actual reduced symbol for P after Q, using the previously constructed adjoint symbol. -/
def compositionSymbol (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n s t) (q : SymbolFunction n r s) : SymbolFunction n r t :=
  amplitudeSymbol (leftRightAmplitude p (symbolAdjoint (adjointSymbol χ q)))

/-- Degree-j term of SG (3.10): frequency derivatives of p precede spatial derivatives of q. -/
def compositionExpansionTerm (p : SymbolFunction n s t) (q : SymbolFunction n r s)
    (j : ℕ) : SymbolFunction n r t :=
  fun x ξ ↦ ((-Complex.I) ^ j / (j.factorial : ℂ)) •
    ∑ α : Fin j → Fin n,
      (iteratedFDeriv ℝ j (p x) ξ (fun a ↦ EuclideanSpace.single (α a) 1)).comp
        (iteratedFDeriv ℝ j (fun y ↦ q y ξ) x
          (fun a ↦ EuclideanSpace.single (α a) 1))

/-- Pointwise Hermitian adjoint preserves the symbol order on every open domain. -/
theorem IsSymbol.symbolAdjoint {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {m : ℝ} {a : SymbolFunction n r s} (ha : IsSymbol U m a) :
    IsSymbol U m (symbolAdjoint a) := by
  /- The finite-dimensional matrix adjoint is a continuous real-linear isometry.
  On the open domain it commutes with all real derivatives. Thus smoothness is
  preserved and each mixed derivative has the same norm as before taking adjoints.
  This operation is conjugate-linear over the complex numbers, not complex-linear. -/
  -- Adjoint is an isometry over the real scalars used by every symbol derivative.
  let P := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)
  let W := EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin r)
  let J : V ≃ₗᵢ[ℝ] W := {
    toEquiv := (ContinuousLinearMap.adjoint : V ≃ₗᵢ⋆[ℂ] W).toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by
      intro c A
      change (c • A).adjoint = c • A.adjoint
      rw [← Complex.coe_smul c A, map_smulₛₗ]
      simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry (AtiyahSinger.symbolAdjoint a))
      (U ×ˢ Set.univ) := by
    intro z hz
    exact ((J.contDiff.comp_contDiffOn ha.1).contDiffAt
      ((hU.prod isOpen_univ).mem_nhds hz)).contDiffWithinAt
  refine ⟨hsmooth, ?_⟩
  intro K hK hcompact i j
  obtain ⟨C, hC, hbound⟩ := ha.2 K hK hcompact i j
  refine ⟨C, hC, ?_⟩
  intro x hx ξ
  -- The same isometry on derivative targets preserves the full mixed derivative norm.
  let Jj : (P [×j]→L[ℝ] V) ≃ₗᵢ[ℝ] (P [×j]→L[ℝ] W) := {
    toLinearEquiv := (J.toContinuousLinearEquiv.continuousMultilinearMapCongrRight
      (fun _ : Fin j ↦ P)).toLinearEquiv
    norm_map' := fun f ↦ J.toLinearIsometry.norm_compContinuousMultilinearMap f }
  have heq : (fun y ↦ iteratedFDeriv ℝ j (AtiyahSinger.symbolAdjoint a y) ξ) =
      Jj ∘ (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) := by
    funext y
    exact J.toContinuousLinearEquiv.iteratedFDeriv_comp_left
  change ‖iteratedFDeriv ℝ i
    (fun y ↦ iteratedFDeriv ℝ j (AtiyahSinger.symbolAdjoint a y) ξ) x‖ ≤ _
  rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  exact hbound x hx ξ

/-- Taking pointwise adjoints preserves the uniform spatial support exactly. -/
theorem tsupport_symbolAdjoint (a : SymbolFunction n r s) :
    tsupport (symbolAdjoint a) = tsupport a := by
  /- A matrix is zero exactly when its Hermitian adjoint is zero, by involutivity.
  Apply this for every frequency to the function of x valued in frequency functions.
  The ordinary supports coincide, hence their closures coincide as well. -/
  -- Involution identifies the nonzero loci before taking their closures.
  have hsupp : Function.support (symbolAdjoint a) = Function.support a := by
    ext x
    simp only [Function.mem_support, ne_eq]
    have hzero : symbolAdjoint a x = 0 ↔ a x = 0 := by
      constructor
      · intro hx
        funext ξ
        have hξ := congrFun hx ξ
        have h := congrArg ContinuousLinearMap.adjoint hξ
        simpa only [symbolAdjoint, ContinuousLinearMap.adjoint_adjoint, map_zero,
          Pi.zero_apply] using h
      · intro hx
        funext ξ
        simp [symbolAdjoint, hx]
    exact not_congr hzero
  exact congrArg closure hsupp

/-- The reduced adjoint symbol is supported in the output cutoff even for raw input functions. -/
theorem tsupport_adjointSymbol_subset (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : SymbolFunction n r s) : tsupport (adjointSymbol χ a) ⊆ tsupport χ := by
  /- Off the closed support of χ the amplitude χ(x)a(y,ξ)† is zero for all y,ξ.
  Its two iterated integrals are therefore zero at every output frequency.
  Taking the closure of the nonzero set gives the stated support inclusion;
  this support-only fact does not assert convergence for arbitrary raw a. -/
  -- Vanishing of the cutoff makes both raw integrals zero at every frequency.
  apply closure_minimal ?_ (isClosed_tsupport χ)
  intro x hx
  by_contra hχx
  have hzero : χ x = 0 := image_eq_zero_of_notMem_tsupport hχx
  apply hx
  funext ξ
  simp [adjointSymbol, amplitudeSymbol, adjointAmplitude, hzero]

set_option maxHeartbeats 1200000 in

/-- The left-right composition amplitude has the sum of the two symbol orders. -/
theorem isAmplitude_leftRightAmplitude (l m : ℝ)
    (p : SymbolFunction n s t) (b : SymbolFunction n r s)
    (hp : IsSymbol Set.univ l p) (hb : IsSymbol Set.univ m b) :
    IsAmplitude (l + m) (leftRightAmplitude p b) := by
  /- Composition of matrices is a continuous bilinear map. Apply the mixed product
  rule, keeping each derivative of p on the left of the derivative of b. On each
  compact spatial pair set use its two compact projections. If k frequency
  derivatives split as k₁+k₂, the order is l-k₁+m-k₂=l+m-k. -/
  classical
  let P := EuclideanSpace ℝ (Fin n)
  let mixed {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :=
    iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) x
  let triple {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (a : P → P → P → V) (i j k : ℕ) (x y ξ : P) :=
    iteratedFDeriv ℝ i
      (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ iteratedFDeriv ℝ k (a z w) ξ) y) x
  -- Smooth parameter differentiation is used at every derivative target.
  have parametric {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
      ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
    induction k with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Y V).symm : _ →L[ℝ] Y [×0]→L[ℝ] V)
    | succ k ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : X × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ k (f z.1) η)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : X × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) V).symm :
          _ →L[ℝ] Y [×(k + 1)]→L[ℝ] V)
  have nested_isometry {V W : Type}
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (J : V ≃ₗᵢ[ℝ] W) (f : P → P → V) (i j : ℕ) (x y : P) :
      ‖iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (J ∘ f z) y) x‖ =
        ‖iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f z) y) x‖ := by
    let Jj : (P [×j]→L[ℝ] V) ≃ₗᵢ[ℝ] (P [×j]→L[ℝ] W) := {
      toLinearEquiv := (J.toContinuousLinearEquiv.continuousMultilinearMapCongrRight
        (fun _ : Fin j ↦ P)).toLinearEquiv
      norm_map' := fun f ↦ J.toLinearIsometry.norm_compContinuousMultilinearMap f }
    have heq : (fun z ↦ iteratedFDeriv ℝ j (J ∘ f z) y) =
        Jj ∘ (fun z ↦ iteratedFDeriv ℝ j (f z) y) := by
      funext z
      exact J.toContinuousLinearEquiv.iteratedFDeriv_comp_left
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  have mixed_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ fderiv ℝ (f y) η) i j x ξ‖ = ‖mixed f i (j + 1) x ξ‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ (j + 1) (f y) ξ) =
        (continuousMultilinearCurryRightEquiv' ℝ j P V).symm ∘
          (fun y ↦ iteratedFDeriv ℝ j (fderiv ℝ (f y)) ξ) := by
      funext y
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  have mixed_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i : ℕ) (x ξ : P) :
      ‖mixed f i 0 x ξ‖ = ‖iteratedFDeriv ℝ i (fun y ↦ f y ξ) x‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ 0 (f y) ξ) =
        (continuousMultilinearCurryFin0 ℝ P V).symm ∘ (fun y ↦ f y ξ) := rfl
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  have triple_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (a : P → P → P → V) (i j : ℕ) (x y ξ : P) :
      ‖triple a i j 0 x y ξ‖ =
        ‖iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ a z w ξ) y) x‖ := by
    exact nested_isometry (continuousMultilinearCurryFin0 ℝ P V).symm
      (fun z w ↦ a z w ξ) i j x y
  have triple_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (a : P → P → P → V) (i j k : ℕ) (x y ξ : P) :
      ‖triple (fun z w η ↦ fderiv ℝ (a z w) η) i j k x y ξ‖ =
        ‖triple a i j (k + 1) x y ξ‖ := by
    unfold triple
    simp_rw [iteratedFDeriv_succ_eq_comp_right]
    exact (nested_isometry (continuousMultilinearCurryRightEquiv' ℝ k P V).symm
      (fun z w ↦ iteratedFDeriv ℝ k (fderiv ℝ (a z w)) ξ) i j x y).symm
  have nested_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f g : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (hg : ContDiff ℝ ∞ (Function.uncurry g)) (i j : ℕ) (x y : P) :
      iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ f z w + g z w) y) x =
        iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f z) y) x +
          iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (g z) y) x := by
    have heq (z : P) : iteratedFDeriv ℝ j (fun w ↦ f z w + g z w) y =
        iteratedFDeriv ℝ j (f z) y + iteratedFDeriv ℝ j (g z) y :=
      iteratedFDeriv_add_apply
        (((hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt).of_le (by simp))
        (((hg.comp (contDiff_const.prodMk contDiff_id)).contDiffAt).of_le (by simp))
    simp_rw [heq]
    exact iteratedFDeriv_add_apply
      ((((parametric f hf j).comp (contDiff_id.prodMk contDiff_const)).contDiffAt).of_le
        (by simp))
      ((((parametric g hg j).comp (contDiff_id.prodMk contDiff_const)).contDiffAt).of_le
        (by simp))
  have triple_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f g : P → P → P → V)
      (hf : ContDiff ℝ ∞ (fun z : (P × P) × P ↦ f z.1.1 z.1.2 z.2))
      (hg : ContDiff ℝ ∞ (fun z : (P × P) × P ↦ g z.1.1 z.1.2 z.2))
      (i j k : ℕ) (x y ξ : P) :
      triple (fun z w η ↦ f z w η + g z w η) i j k x y ξ =
        triple f i j k x y ξ + triple g i j k x y ξ := by
    have heq (z w : P) : iteratedFDeriv ℝ k (fun η ↦ f z w η + g z w η) ξ =
        iteratedFDeriv ℝ k (f z w) ξ + iteratedFDeriv ℝ k (g z w) ξ := by
      have hff : ContDiff ℝ ∞ (f z w) :=
        hf.comp ((contDiff_const (c := (z, w))).prodMk contDiff_id)
      have hgg : ContDiff ℝ ∞ (g z w) :=
        hg.comp ((contDiff_const (c := (z, w))).prodMk contDiff_id)
      exact iteratedFDeriv_add_apply (hff.contDiffAt.of_le (by simp))
        (hgg.contDiffAt.of_le (by simp))
    unfold triple
    simp_rw [heq]
    apply nested_add
    · exact (parametric (Function.uncurry f) hf k).comp (contDiff_id.prodMk contDiff_const)
    · exact (parametric (Function.uncurry g) hg k).comp (contDiff_id.prodMk contDiff_const)
  -- Spatial derivatives separate between the two original factors. Frequency derivatives
  -- split by Leibniz; inducting on their number records the exact loss of symbol order.
  have estimate (k : ℕ) (K L : Set P) :
      ∀ {V W Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
        [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
        (B : V →L[ℝ] W →L[ℝ] Z) (f : P → P → V) (g : P → P → W) (l m : ℝ),
        ContDiff ℝ ∞ (Function.uncurry f) → ContDiff ℝ ∞ (Function.uncurry g) →
        (∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
          ‖mixed f i j x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (l - (j : ℝ))) →
        (∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ L, ∀ ξ,
          ‖mixed g i j y ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - (j : ℝ))) →
        ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ y ∈ L, ∀ ξ,
          ‖triple (fun z w η ↦ B (f z η) (g w η)) i j k x y ξ‖ ≤
            C * (1 + ‖ξ‖) ^ (l + m - (k : ℝ)) := by
    induction k with
    | zero =>
      intro V W Z _ _ _ _ _ _ B f g l m hf hg hfb hgb i j
      obtain ⟨C, hC, hfc⟩ := hfb i 0
      obtain ⟨D, hD, hgd⟩ := hgb j 0
      refine ⟨‖B‖ * C * D, mul_nonneg (mul_nonneg (norm_nonneg _) hC) hD, ?_⟩
      intro x hx y hy ξ
      rw [triple_zero]
      let d := iteratedFDeriv ℝ j (fun w ↦ g w ξ) y
      let T : V →L[ℝ] P [×j]→L[ℝ] Z :=
        ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
          (fun _ : Fin j ↦ P) W Z).flip d).comp B
      have hgf : ContDiff ℝ ∞ (fun w ↦ g w ξ) :=
        hg.comp (contDiff_id.prodMk contDiff_const)
      have hff : ContDiff ℝ ∞ (fun z ↦ f z ξ) :=
        hf.comp (contDiff_id.prodMk contDiff_const)
      have heq : (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ B (f z ξ) (g w ξ)) y) =
          T ∘ (fun z ↦ f z ξ) := by
        funext z
        exact (B (f z ξ)).iteratedFDeriv_comp_left hgf.contDiffAt (by simp)
      have hT : ‖T‖ ≤ ‖B‖ * ‖d‖ := by
        apply T.opNorm_le_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        intro v
        calc
          ‖T v‖ ≤ ‖B v‖ * ‖d‖ := (B v).norm_compContinuousMultilinearMap_le d
          _ ≤ (‖B‖ * ‖v‖) * ‖d‖ :=
            mul_le_mul_of_nonneg_right (B.le_opNorm v) (norm_nonneg _)
          _ = _ := by ring
      rw [heq]
      have hbound := T.norm_iteratedFDeriv_comp_left hff.contDiffAt (x := x) (n := i) (by simp)
      have hc := hfc x hx ξ
      have hd := hgd y hy ξ
      simp only [mixed_zero, Nat.cast_zero, sub_zero] at hc hd
      simp only [Nat.cast_zero, sub_zero]
      apply hbound.trans
      calc
        ‖T‖ * ‖iteratedFDeriv ℝ i (fun z ↦ f z ξ) x‖ ≤
            (‖B‖ * ‖d‖) * (C * (1 + ‖ξ‖) ^ l) :=
          mul_le_mul hT hc (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ (‖B‖ * (D * (1 + ‖ξ‖) ^ m)) * (C * (1 + ‖ξ‖) ^ l) := by
          gcongr
        _ = _ := by
          rw [Real.rpow_add (by positivity : 0 < 1 + ‖ξ‖)]
          ring
    | succ k ih =>
      intro V W Z _ _ _ _ _ _ B f g l m hf hg hfb hgb i j
      let df : P → P → P →L[ℝ] V := fun x ξ ↦ fderiv ℝ (f x) ξ
      let dg : P → P → P →L[ℝ] W := fun y ξ ↦ fderiv ℝ (g y) ξ
      have hdf : ContDiff ℝ ∞ (Function.uncurry df) := by
        have h : ContDiff ℝ ∞
            (fun z : (P × P) × P ↦ f z.1.1 z.2) :=
          hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
        exact h.fderiv contDiff_snd (by simp)
      have hdg : ContDiff ℝ ∞ (Function.uncurry dg) := by
        have h : ContDiff ℝ ∞
            (fun z : (P × P) × P ↦ g z.1.1 z.2) :=
          hg.comp (contDiff_fst.fst.prodMk contDiff_snd)
        exact h.fderiv contDiff_snd (by simp)
      have hdfb : ∀ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
          ‖mixed df a b x ξ‖ ≤ C * (1 + ‖ξ‖) ^ ((l - 1) - (b : ℝ)) := by
        intro a b
        obtain ⟨C, hC, hbound⟩ := hfb a (b + 1)
        refine ⟨C, hC, ?_⟩
        intro x hx ξ
        have h := hbound x hx ξ
        rw [← mixed_shift] at h
        have hexp : l - ((b + 1 : ℕ) : ℝ) = l - 1 - (b : ℝ) := by
          push_cast
          ring
        rw [hexp] at h
        exact h
      have hdgb : ∀ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ L, ∀ ξ,
          ‖mixed dg a b y ξ‖ ≤ C * (1 + ‖ξ‖) ^ ((m - 1) - (b : ℝ)) := by
        intro a b
        obtain ⟨C, hC, hbound⟩ := hgb a (b + 1)
        refine ⟨C, hC, ?_⟩
        intro y hy ξ
        have h := hbound y hy ξ
        rw [← mixed_shift] at h
        have hexp : m - ((b + 1 : ℕ) : ℝ) = m - 1 - (b : ℝ) := by
          push_cast
          ring
        rw [hexp] at h
        exact h
      let p₁ : P → P → P → P →L[ℝ] Z := fun x y ξ ↦ B.precompR P (f x ξ) (dg y ξ)
      let p₂ : P → P → P → P →L[ℝ] Z := fun x y ξ ↦ B.precompL P (df x ξ) (g y ξ)
      obtain ⟨C, hC, h₁⟩ := ih (B.precompR P) f dg l (m - 1) hf hdg hfb hdgb i j
      obtain ⟨D, hD, h₂⟩ := ih (B.precompL P) df g (l - 1) m hdf hg hdfb hgb i j
      refine ⟨C + D, add_nonneg hC hD, ?_⟩
      intro x hx y hy ξ
      have hp₁ : ContDiff ℝ ∞ (fun z : (P × P) × P ↦ p₁ z.1.1 z.1.2 z.2) :=
        (B.precompR P).isBoundedBilinearMap.contDiff.comp₂
          (hf.comp (contDiff_fst.fst.prodMk contDiff_snd))
          (hdg.comp (contDiff_fst.snd.prodMk contDiff_snd))
      have hp₂ : ContDiff ℝ ∞ (fun z : (P × P) × P ↦ p₂ z.1.1 z.1.2 z.2) :=
        (B.precompL P).isBoundedBilinearMap.contDiff.comp₂
          (hdf.comp (contDiff_fst.fst.prodMk contDiff_snd))
          (hg.comp (contDiff_fst.snd.prodMk contDiff_snd))
      have heq : (fun z w η ↦ fderiv ℝ (fun η ↦ B (f z η) (g w η)) η) =
          (fun z w η ↦ p₁ z w η + p₂ z w η) := by
        funext z w η
        exact B.fderiv_of_bilinear
          (((hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt).differentiableAt (by simp))
          (((hg.comp (contDiff_const.prodMk contDiff_id)).contDiffAt).differentiableAt (by simp))
      rw [← triple_shift, heq, triple_add p₁ p₂ hp₁ hp₂]
      have h := (norm_add_le _ _).trans (add_le_add (h₁ x hx y hy ξ) (h₂ x hx y hy ξ))
      have he₁ : l + (m - 1) - (k : ℝ) = l + m - ((k + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      have he₂ : (l - 1) + m - (k : ℝ) = l + m - ((k + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [he₁, he₂, ← add_mul] at h
      exact h
  -- The two compact projections provide the estimates for the same original symbols.
  have hps : ContDiff ℝ ∞ (Function.uncurry p) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
  have hbs : ContDiff ℝ ∞ (Function.uncurry b) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using hb.1
  let B := (ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ (Fin r))
    (EuclideanSpace ℂ (Fin s)) (EuclideanSpace ℂ (Fin t))).bilinearRestrictScalars ℝ
  refine ⟨B.isBoundedBilinearMap.contDiff.comp₂
    (hps.comp (contDiff_fst.fst.prodMk contDiff_snd))
    (hbs.comp (contDiff_fst.snd.prodMk contDiff_snd)), ?_⟩
  intro K hK i j k
  obtain ⟨C, hC, hbound⟩ := estimate k (Prod.fst '' K) (Prod.snd '' K) B p b l m hps hbs
    (hp.2 _ (Set.subset_univ _) (hK.image continuous_fst))
    (hb.2 _ (Set.subset_univ _) (hK.image continuous_snd)) i j
  exact ⟨C, hC, fun x y hxy ξ ↦
    hbound x ⟨(x, y), hxy, rfl⟩ y ⟨(x, y), hxy, rfl⟩ ξ⟩

/-- Compact spatial supports of the two symbols give compact support in (x,y). -/
theorem hasCompactSupport_leftRightAmplitude
    (p : SymbolFunction n s t) (b : SymbolFunction n r s)
    (hp : HasCompactSupport p) (hb : HasCompactSupport b) :
    HasCompactSupport (Function.uncurry (leftRightAmplitude p b)) := by
  /- The full amplitude vanishes outside tsupport p times tsupport b, uniformly
  in frequency. This product is compact. Composition with a zero matrix on either
  side is zero, so the closed spatial support lies inside this product. -/
  -- Each nonzero composite needs both original spatial symbol supports.
  apply (hp.prod hb).of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ ((isClosed_tsupport p).prod (isClosed_tsupport b))
  intro z hz
  constructor
  · by_contra hpz
    have hzero : p z.1 = 0 := image_eq_zero_of_notMem_tsupport hpz
    apply hz
    funext ξ
    simp [Function.uncurry, leftRightAmplitude, hzero]
  · by_contra hbz
    have hzero : b z.2 = 0 := image_eq_zero_of_notMem_tsupport hbz
    apply hz
    funext ξ
    simp [Function.uncurry, leftRightAmplitude, hzero]

/-- The right-symbol Fourier expression is an ordinary integrable spatial function. -/
theorem integrable_rightSymbolFourierApply (m : ℝ) (b : SymbolFunction n r s)
    (hb : IsSymbol Set.univ m b) (hsupp : HasCompactSupport b)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (ξ : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • b y ξ (u y)) := by
  /- With ξ fixed, joint smoothness makes the integrand continuous in y. Its
  support is contained in the compact spatial support of b. Continuous compactly
  supported functions with this complete finite-dimensional target are integrable. -/
  -- Fixing frequency leaves a continuous spatial matrix function on the original model.
  have hbcont : Continuous (fun y ↦ b y ξ) := by
    have h : Continuous (Function.uncurry b) := by
      simpa only [Set.univ_prod_univ, continuousOn_univ] using hb.1.continuousOn
    exact h.comp (continuous_id.prodMk continuous_const)
  have hphase : Continuous
      (fun y : EuclideanSpace ℝ (Fin n) ↦ Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ))) := by
    fun_prop
  have hcont : Continuous
      (fun y ↦ Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • b y ξ (u y)) := by
    exact hphase.smul (hbcont.clm_apply u.continuous)
  -- The symbol supplies compact support uniformly in frequency; no decay estimate is needed here.
  have hcompact : HasCompactSupport
      (fun y ↦ Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • b y ξ (u y)) := by
    apply hsupp.of_isClosed_subset isClosed_closure
    apply closure_minimal ?_ (isClosed_tsupport b)
    intro y hy
    by_contra hby
    have hzero : b y = 0 := image_eq_zero_of_notMem_tsupport hby
    apply hy
    simp [hzero]
  exact hcont.integrable_of_hasCompactSupport hcompact

set_option maxHeartbeats 1000000 in

/-- The full adjoint pairing gives SG's right-symbol Fourier formula at every frequency. -/
theorem fourierSG_eq_rightSymbolFourierApply (m : ℝ) (a : SymbolFunction n s r)
    (ha : IsSymbol Set.univ m a) (hsupp : HasCompactSupport a)
    (Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (A : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (hA : ∀ v x, A v x = quantize a v x) (hQA : IsSchwartzFormalAdjoint Q A)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (ξ : EuclideanSpace ℝ (Fin n)) :
    fourierSG (Q u) ξ = rightSymbolFourierApply (symbolAdjoint a) u ξ := by
  /- Choose a compact smooth frequency test and a fixed fiber vector; Fourier
  bijectivity supplies the corresponding Schwartz input. Compact spatial support
  of the symbol and frequency support of the test make the pairing integrand
  compact in both variables. Quantization, formal adjunction, Plancherel and Fubini
  identify the two frequency pairings. Compact tests separate their continuous
  components, giving equality everywhere. No plane wave or Fourier transform of
  an equality restricted only to K is used. -/
  let V := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin s)
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  let phase (y η : V) := Complex.exp (-Complex.I * (inner ℝ y (c • η) : ℂ))
  let kernel (η y : V) := phase y η • (a y (c • η)).adjoint (u y)
  let R (η : V) := ∫ y, kernel η y
  have haCont : Continuous (Function.uncurry a) := by
    simpa only [Set.univ_prod_univ, continuousOn_univ] using ha.1.continuousOn
  have hconj (y η : V) : (starRingEnd ℂ) (phase y η) =
      Complex.exp (Complex.I * (inner ℝ y (c • η) : ℂ)) := by
    dsimp [phase]
    rw [← Complex.exp_conj]
    congr 1
    simp
  -- The same scalar substitution cancels the SG inverse normalization exactly.
  have hnormalize (v : 𝓢(V, E)) (y : V) : quantize a v y =
      ∫ η, (starRingEnd ℂ) (phase y η) • a y (c • η) (FourierTransform.fourier v η) := by
    let g (ζ : V) := Complex.exp (Complex.I * (inner ℝ y ζ : ℂ)) •
      a y ζ (fourierSG v ζ)
    have hscale := Measure.integral_comp_smul_of_nonneg (volume : Measure V) g c (hR := hc.le)
    calc
      _ = ∫ η : V, g (c • η) := by
        simpa only [V, finrank_euclideanSpace_fin, quantize, g, c] using hscale.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with η
        have hv : fourierSG v (c • η) = FourierTransform.fourier v η := by
          change FourierTransform.fourier v (c⁻¹ • (c • η)) = _
          rw [inv_smul_smul₀ hc.ne']
        dsimp only [g]
        rw [hv, hconj]
  -- Compact spatial support makes the right-symbol integral continuous in frequency.
  have hkernel : Continuous (Function.uncurry kernel) := by
    have ha' : Continuous (fun z : V × V ↦ a z.2 (c • z.1)) :=
      haCont.comp (continuous_snd.prodMk (continuous_fst.const_smul c))
    have hphase' : Continuous (fun z : V × V ↦ phase z.2 z.1) := by
      dsimp [phase]
      fun_prop
    exact hphase'.smul
      ((ContinuousLinearMap.adjoint.continuous.comp ha').clm_apply
        (u.continuous.comp continuous_snd))
  have hkerzero (η y : V) (hy : y ∉ tsupport a) : kernel η y = 0 := by
    have ha0 : a y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [kernel, ha0]
  have hR : Continuous R := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support hsupp hkernel.continuousOn
    exact fun η y _ hy ↦ hkerzero η y hy
  have hkerint (η : V) : Integrable (kernel η) := by
    apply (hkernel.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    apply hsupp.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ (isClosed_tsupport a)
    exact fun y hy ↦ by_contra (fun h ↦ hy (hkerzero η y h))
  have hFourier : Continuous (fun η ↦ FourierTransform.fourier (Q u) η) :=
    (FourierTransform.fourier (Q u)).continuous
  -- Compact frequency tests give a pairing integrand with compact support in both variables.
  have htest (z : E) (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
      (∫ η, φ η • inner ℂ (FourierTransform.fourier (Q u) η) z) =
        ∫ η, φ η • inner ℂ (R η) z := by
    let w : 𝓢(V, E) := hcφ.smul_right.toSchwartzMap (hφ.smul (contDiff_const (c := z)))
    let v : 𝓢(V, E) := FourierTransform.fourierInv w
    have hv : FourierTransform.fourier v = w := FourierTransform.fourier_fourierInv_eq w
    let H (y η : V) := φ η • inner ℂ (kernel η y) z
    have hH : Continuous (Function.uncurry H) :=
      (hφ.continuous.comp continuous_snd).smul
        ((hkernel.comp continuous_swap).inner continuous_const)
    have hcH : HasCompactSupport (Function.uncurry H) := by
      apply (hsupp.prod hcφ).of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal ?_ ((isClosed_tsupport a).prod (isClosed_tsupport φ))
      intro p hp
      constructor
      · by_contra hy
        exact hp (by simp [Function.uncurry, H, hkerzero p.2 p.1 hy])
      · by_contra hη
        have hz : φ p.2 = 0 := image_eq_zero_of_notMem_tsupport hη
        exact hp (by simp [Function.uncurry, H, hz])
    have hpoint (y : V) : inner ℂ (u y) (A v y) = ∫ η, H y η := by
      rw [hA v y, hnormalize v y, hv]
      have hi : Integrable (fun η ↦ (starRingEnd ℂ) (phase y η) • a y (c • η) (w η)) := by
        have hcont : Continuous (fun η ↦ (starRingEnd ℂ) (phase y η) • a y (c • η) (w η)) := by
          have hay : Continuous (fun η ↦ a y (c • η)) :=
            haCont.comp ((continuous_const (y := y)).prodMk (continuous_id.const_smul c))
          have hpy : Continuous (fun η ↦ (starRingEnd ℂ) (phase y η)) := by
            dsimp [phase]
            fun_prop
          exact hpy.smul (hay.clm_apply w.continuous)
        apply hcont.integrable_of_hasCompactSupport
        apply hcφ.of_isClosed_subset (isClosed_tsupport _)
        apply closure_minimal ?_ (isClosed_tsupport φ)
        intro η hη
        by_contra h
        have hzero : φ η = 0 := image_eq_zero_of_notMem_tsupport h
        apply hη
        change (starRingEnd ℂ) (phase y η) • a y (c • η) (φ η • z) = 0
        simp [hzero]
      rw [← integral_inner hi]
      apply integral_congr_ae
      filter_upwards with η
      change inner ℂ (u y) ((starRingEnd ℂ) (phase y η) • a y (c • η) (φ η • z)) =
        φ η • inner ℂ (phase y η • (a y (c • η)).adjoint (u y)) z
      rw [(a y (c • η)).map_smul_of_tower, inner_smul_right, inner_smul_left,
        inner_smul_right_eq_smul, ContinuousLinearMap.adjoint_inner_left]
      exact smul_comm ((starRingEnd ℂ) (phase y η)) (φ η) (inner ℂ (u y) (a y (c • η) z))
    calc
      _ = ∫ η, inner ℂ (FourierTransform.fourier (Q u) η)
          (FourierTransform.fourier v η) := by
        rw [hv]
        apply integral_congr_ae
        filter_upwards with η
        change φ η • inner ℂ _ z = inner ℂ _ (φ η • z)
        exact (inner_smul_right_eq_smul _ _ _).symm
      _ = ∫ y, inner ℂ (Q u y) (v y) :=
        SchwartzMap.integral_inner_fourier_fourier (Q u) v
      _ = ∫ y, inner ℂ (u y) (A v y) := hQA u v
      _ = ∫ y, ∫ η, H y η := integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = ∫ η, ∫ y, H y η := integral_integral_swap_of_hasCompactSupport hH hcH
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with η
        dsimp only [H, R]
        rw [integral_smul]
        congr 1
        simpa only [← integral_conj, inner_conj_symm] using
          congrArg (starRingEnd ℂ) (integral_inner (𝕜 := ℂ) (hkerint η) z)
  -- Equality on the test space identifies each continuous matrix component everywhere.
  have heq (η : V) : FourierTransform.fourier (Q u) η = R η := by
    apply ext_inner_right ℂ
    intro z
    have hf : Continuous (fun η ↦ inner ℂ (FourierTransform.fourier (Q u) η) z) :=
      hFourier.inner continuous_const
    have hg : Continuous (fun η ↦ inner ℂ (R η) z) := hR.inner continuous_const
    have hae := ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable
      (htest z)
    exact congrFun (Measure.eq_of_ae_eq hae hf hg) η
  have hscale : c • (c⁻¹ • ξ) = ξ := smul_inv_smul₀ hc.ne' ξ
  change FourierTransform.fourier (Q u) (c⁻¹ • ξ) = _
  rw [heq]
  simp only [R, kernel, phase, hscale, rightSymbolFourierApply, symbolAdjoint]
  rfl

/-- Exact quantization on all Schwartz tests determines the full left symbol uniquely. -/
theorem symbol_eq_of_quantize_eq (l m : ℝ) (a b : SymbolFunction n r s)
    (ha : IsSymbol Set.univ l a) (hb : IsSymbol Set.univ m b)
    (hab : ∀ u x, quantize a u x = quantize b u x) : a = b := by
  /- Fix x and use Fourier bijectivity to test the difference against arbitrary
  compactly supported smooth frequency functions in each vector component.
  The continuous polynomially bounded matrix function exp(i<x,ξ>)(a-b)(x,ξ)
  then defines the zero distribution, hence vanishes pointwise. The exponential
  is nonzero, giving equality of the full symbols, not just of their principal classes. -/
  let V := EuclideanSpace ℝ (Fin n)
  have hπ : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  -- The SG frequency scaling is invertible on the same Schwartz space.
  have hfourier (v : 𝓢(V, EuclideanSpace ℂ (Fin r))) :
      ∃ u : 𝓢(V, EuclideanSpace ℂ (Fin r)), fourierSG u = v := by
    let e : V ≃L[ℝ] V :=
      (LinearEquiv.smulOfNeZero ℝ V (2 * Real.pi) hπ).toContinuousLinearEquiv
    let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e v
    refine ⟨FourierTransform.fourierInv w, ?_⟩
    funext ξ
    simp only [fourierSG, FourierTransform.fourier_fourierInv_eq]
    change v ((2 * Real.pi) • ((2 * Real.pi)⁻¹ • ξ)) = v ξ
    rw [smul_smul, mul_inv_cancel₀ hπ, one_smul]
  funext x ξ
  apply ContinuousLinearMap.ext
  intro v
  -- Compact frequency tests identify the continuous columns without any improper interchange.
  let phase (η : V) := Complex.exp (Complex.I * (inner ℝ x η : ℂ))
  let f (η : V) := phase η • a x η v
  let g (η : V) := phase η • b x η v
  have hphase : Continuous phase := by fun_prop
  have hacont : Continuous (fun η : V ↦ a x η) := by
    have h := ha.1.continuousOn
    rw [Set.univ_prod_univ] at h
    exact (continuousOn_univ.mp h).comp (continuous_const.prodMk continuous_id)
  have hbcont : Continuous (fun η : V ↦ b x η) := by
    have h := hb.1.continuousOn
    rw [Set.univ_prod_univ] at h
    exact (continuousOn_univ.mp h).comp (continuous_const.prodMk continuous_id)
  have hf : Continuous f := hphase.smul (hacont.clm_apply continuous_const)
  have hg : Continuous g := hphase.smul (hbcont.clm_apply continuous_const)
  have hae : f =ᵐ[volume] g := by
    apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable
    intro φ hφ hcφ
    have hc : HasCompactSupport (fun η : V ↦ φ η • v) := hcφ.smul_right
    let ψ := hc.toSchwartzMap (hφ.smul contDiff_const)
    obtain ⟨u, hu⟩ := hfourier ψ
    have h := hab u x
    change ((2 * Real.pi) ^ n)⁻¹ • (∫ η, phase η • a x η (fourierSG u η)) =
      ((2 * Real.pi) ^ n)⁻¹ • (∫ η, phase η • b x η (fourierSG u η)) at h
    have hi := smul_right_injective _ (inv_ne_zero (pow_ne_zero n hπ)) h
    rw [hu] at hi
    have htest (p : SymbolFunction n r s) :
        (∫ η, φ η • (phase η • p x η v)) = (∫ η, phase η • p x η (ψ η)) := by
      congr 1
      funext η
      change φ η • (phase η • p x η v) = phase η • p x η (φ η • v)
      rw [(p x η).map_smul_of_tower, smul_comm]
    change (∫ η, φ η • (phase η • a x η v)) = (∫ η, φ η • (phase η • b x η v))
    rw [htest a, htest b]
    exact hi
  have heq : f = g := Measure.eq_of_ae_eq hae hf hg
  exact smul_right_injective _ (Complex.exp_ne_zero _) (congrFun heq ξ)

/-- The explicit reduced composition symbol has order l+m under compact spatial support. -/
theorem isSymbol_compositionSymbol (l m : ℝ)
    (p : SymbolFunction n s t) (q : SymbolFunction n r s)
    (hp : IsSymbol Set.univ l p) (hq : IsSymbol Set.univ m q)
    (hpSupp : HasCompactSupport p) (hqSupp : HasCompactSupport q)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχSupp : HasCompactSupport χ) :
    IsSymbol Set.univ (l + m) (compositionSymbol χ p q) := by
  /- Stage 1: the reduced adjoint symbol has order m and is supported in tsupport χ.
  Taking its pointwise adjoint preserves both estimates and support. Stage 2: the
  left-right amplitude has order l+m and compact (x,y) support, so SG 3.5 applies.
  No cutoff-equals-one condition is needed for this estimate; that condition is
  used separately to identify this particular symbol with the composition of P and Q. -/
  -- Use the same reduced adjoint as in the prescribed composition symbol.
  have ha : IsSymbol Set.univ m (adjointSymbol χ q) :=
    isSymbol_adjointSymbol m q hq hqSupp χ hχ hχSupp
  have haSupp : HasCompactSupport (adjointSymbol χ q) :=
    hχSupp.of_isClosed_subset (isClosed_tsupport _) (tsupport_adjointSymbol_subset χ q)
  have hbSupp : HasCompactSupport (symbolAdjoint (adjointSymbol χ q)) := by
    simpa only [HasCompactSupport, tsupport_symbolAdjoint] using haSupp
  -- The two actual factors supply precisely the order and compact support of the amplitude.
  exact isSymbol_amplitudeSymbol (l + m) _
    (isAmplitude_leftRightAmplitude l m p _ hp (ha.symbolAdjoint isOpen_univ))
    (hasCompactSupport_leftRightAmplitude p _ hpSupp hbSupp)

/-- The exact composition symbol retains the output spatial support of the left symbol. -/
theorem tsupport_compositionSymbol_subset (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n s t) (q : SymbolFunction n r s) :
    tsupport (compositionSymbol χ p q) ⊆ tsupport p := by
  /- Outside tsupport p, p(x,ξ) is zero for every ξ. Thus the entire left-right
  amplitude and its reduced-symbol integrals vanish there at every frequency.
  The closed support of the reduced symbol is contained in the closed support of p. -/
  -- If the original left factor vanishes, the full reduction integrand vanishes.
  apply closure_minimal ?_ (isClosed_tsupport p)
  intro x hx
  by_contra hpx
  have hzero : p x = 0 := image_eq_zero_of_notMem_tsupport hpx
  apply hx
  funext ξ
  simp [compositionSymbol, amplitudeSymbol, leftRightAmplitude, hzero]

/-- The zeroth composition term is the ordered pointwise product of the symbol matrices. -/
theorem compositionExpansionTerm_zero (p : SymbolFunction n s t)
    (q : SymbolFunction n r s) : compositionExpansionTerm p q 0 = symbolComp p q := by
  /- The empty coordinate list is unique and zeroth derivatives evaluate their
  functions. The scalar (-i)^0/0! is one. The remaining continuous linear map is
  p(x,ξ).comp(q(x,ξ)), with the same order of factors as P after Q. -/
  -- Empty coordinate lists and zeroth derivatives leave the original ordered product.
  funext x ξ
  simp [compositionExpansionTerm, symbolComp, iteratedFDeriv_zero_apply]

set_option maxHeartbeats 1500000 in
-- The mixed derivative induction retains arbitrary multilinear target spaces.
/-- Each degree-j composition coefficient has order l+m-j. -/
theorem isSymbol_compositionExpansionTerm (l m : ℝ)
    (p : SymbolFunction n s t) (q : SymbolFunction n r s)
    (hp : IsSymbol Set.univ l p) (hq : IsSymbol Set.univ m q) (j : ℕ) :
    IsSymbol Set.univ (l + m - (j : ℝ)) (compositionExpansionTerm p q j) := by
  /- The built-in j frequency derivatives lower the order of p by j, whereas the
  j spatial derivatives of q leave its order unchanged. Additional derivatives
  satisfy the product rule with the original matrix order preserved. Bound each
  coordinate contraction and finite sum on a compact x set to obtain l+m-j.
  Compact support and operator realizations are unnecessary for this coefficient estimate. -/
  -- Mixed Hessian symmetry and isometric currying control the original derivative order.
  have mixed_fderiv_comm {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (x : X) (y : Y) (u : X) (v : Y) :
      fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) y v u =
        fderiv ℝ (fun t ↦ fderiv ℝ (f t) y) x u v := by
    let F := Function.uncurry f
    let L : X →L[ℝ] X × Y := ContinuousLinearMap.inl ℝ X Y
    let R : Y →L[ℝ] X × Y := ContinuousLinearMap.inr ℝ X Y
    have hF : Differentiable ℝ F := hf.differentiable (by simp)
    have hDF : Differentiable ℝ (fderiv ℝ F) :=
      (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiable (by simp)
    -- Each partial first derivative is the full derivative restricted to one factor.
    have hleft (a : X) (b : Y) :
        fderiv ℝ (fun t ↦ f t b) a = (fderiv ℝ F (a, b)).comp L := by
      exact ((hF (a, b)).hasFDerivAt.comp a
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) a b)).fderiv
    have hright (a : X) (b : Y) :
        fderiv ℝ (f a) b = (fderiv ℝ F (a, b)).comp R :=
      ((hF (a, b)).hasFDerivAt.comp b (hasFDerivAt_prodMk_right (𝕜 := ℝ) a b)).fderiv
    -- Differentiate those restrictions through fixed continuous linear composition maps.
    have hxy : fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) y v u =
        fderiv ℝ (fderiv ℝ F) (x, y) (0, v) (u, 0) := by
      simp_rw [hleft]
      let C : ((X × Y) →L[ℝ] V) →L[ℝ] X →L[ℝ] V :=
        (ContinuousLinearMap.compL ℝ X (X × Y) V).flip L
      have hd := (hDF (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
      have hc := C.hasFDerivAt.comp y hd
      exact congrArg (fun K : Y →L[ℝ] X →L[ℝ] V ↦ K v u) hc.fderiv
    have hyx : fderiv ℝ (fun t ↦ fderiv ℝ (f t) y) x u v =
        fderiv ℝ (fderiv ℝ F) (x, y) (u, 0) (0, v) := by
      simp_rw [hright]
      let C : ((X × Y) →L[ℝ] V) →L[ℝ] Y →L[ℝ] V :=
        (ContinuousLinearMap.compL ℝ Y (X × Y) V).flip R
      have hd := (hDF (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
      have hc := C.hasFDerivAt.comp x hd
      exact congrArg (fun K : X →L[ℝ] Y →L[ℝ] V ↦ K u v) hc.fderiv
    -- Symmetry applies on the full product, with the original two factor directions.
    rw [hxy, hyx]
    exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) (0, v) (u, 0)
  have mixed_fderiv_apply_comm {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V)
      (hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : X) (y : Y) (u : X) (v : Y) :
      fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
        fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u := by
    have hl : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) := by
      have hh : ContDiff ℝ ∞ (Function.uncurry (fun z t ↦ f t z)) :=
        hf.comp (contDiff_snd.prodMk contDiff_fst)
      exact hh.fderiv contDiff_const (by simp)
    have hr : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ (f t) y) :=
      hf.fderiv contDiff_const (by simp)
    rw [fderiv_clm_apply (hl.differentiable (by simp) y) (differentiableAt_const u),
      fderiv_clm_apply (hr.differentiable (by simp) x) (differentiableAt_const v)]
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply] using mixed_fderiv_comm f hf x y u v
  have parametric {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
      ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
    induction k with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Y V).symm : _ →L[ℝ] Y [×0]→L[ℝ] V)
    | succ k ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : X × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ k (f z.1) η)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : X × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) V).symm :
          _ →L[ℝ] Y [×(k + 1)]→L[ℝ] V)
  have iterated_comm {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (comm : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
        (f : X → Y → W) (_hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : X) (y : Y) (u : X) (v : Y),
        fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
          fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u)
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) (x : X) (y : Y)
      (u : X) :
      iteratedFDeriv ℝ k (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y =
        fderiv ℝ (fun t ↦ iteratedFDeriv ℝ k (f t) y) x u := by
    induction k generalizing y with
    | zero =>
      let J := (continuousMultilinearCurryFin0 ℝ Y V).symm.toContinuousLinearEquiv
      exact (congrArg (fun T : X →L[ℝ] Y [×0]→L[ℝ] V ↦ T u)
        (J.comp_fderiv (f := fun t ↦ f t y) (x := x))).symm
    | succ k ih =>
      ext v
      have hs : ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) :=
        parametric f hf k
      rw [iteratedFDeriv_succ_apply_left]
      have hi : (fun z ↦ iteratedFDeriv ℝ k
          (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) z) =
          (fun z ↦ fderiv ℝ (fun t ↦ iteratedFDeriv ℝ k (f t) z) x u) := by
        funext z
        exact ih z
      change ((fderiv ℝ (fun z ↦ iteratedFDeriv ℝ k
        (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) z) y) (v 0)) (Fin.tail v) = _
      rw [hi]
      have hc := comm (fun t z ↦ iteratedFDeriv ℝ k (f t) z) hs x y u (v 0)
      rw [hc]
      have hd : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y) := by
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun t : X ↦ fun z : Y ↦ iteratedFDeriv ℝ k (f t) z)) := hs
        exact h.fderiv contDiff_const (by simp)
      have heq : (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y v) =
          (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y (v 0) (Fin.tail v)) := by
        funext t
        exact iteratedFDeriv_succ_apply_left v
      have hx : ContDiff ℝ ∞ (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y) :=
        (parametric f hf (k + 1)).comp (contDiff_id.prodMk contDiff_const)
      have ha : ContDiff ℝ ∞
          (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y (v 0)) :=
        hd.clm_apply contDiff_const
      rw [← fderiv_continuousMultilinear_apply_const_apply
        (hx.contDiffAt.differentiableAt (by simp)), heq,
        fderiv_continuousMultilinear_apply_const_apply (ha.contDiffAt.differentiableAt (by simp))]
  let mixed {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      P [×i]→L[ℝ] P [×j]→L[ℝ] V :=
    iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) x
  have mixed_map_bound {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
      (L : V →L[ℝ] W) (f : P → P → V)
      (hf : ContDiff ℝ ∞ (Function.uncurry f)) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ L (f y η)) i j x ξ‖ ≤ ‖L‖ * ‖mixed f i j x ξ‖ := by
    let T := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j ↦ P) V W L
    have hT : ‖T‖ ≤ ‖L‖ := by
      apply T.opNorm_le_bound (norm_nonneg _)
      intro v
      exact L.norm_compContinuousMultilinearMap_le v
    have heq : (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ L (f y η)) ξ) =
        T ∘ (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) := by
      funext y
      exact L.iteratedFDeriv_comp_left
        ((hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt) (by simp)
    unfold mixed
    rw [heq]
    exact (T.norm_iteratedFDeriv_comp_left
      (((parametric f hf j).comp (contDiff_id.prodMk contDiff_const)).contDiffAt)
        (by simp)).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have mixed_shift {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ fderiv ℝ (f y) η) i j x ξ‖ = ‖mixed f i (j + 1) x ξ‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ (j + 1) (f y) ξ) =
        (continuousMultilinearCurryRightEquiv' ℝ j P V).symm ∘
          (fun y ↦ iteratedFDeriv ℝ j (fderiv ℝ (f y)) ξ) := by
      funext y
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  -- Spatial differentiation preserves order; each frequency derivative lowers it by one.
  have spatial_symbol {n r q : ℕ}
      (comm : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
        (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → W)
        (_hf : ContDiff ℝ ∞ (Function.uncurry f)) (x y u v : EuclideanSpace ℝ (Fin n)),
        fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
          fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u)
      (m : ℝ) (a : SymbolFunction n r q) (ha : IsSymbol Set.univ m a)
      (u : EuclideanSpace ℝ (Fin n)) :
      IsSymbol Set.univ m (fun x ξ ↦ fderiv ℝ (fun y ↦ a y ξ) x u) := by
    let P := EuclideanSpace ℝ (Fin n)
    have hf : ContDiff ℝ ∞ (Function.uncurry a) := by
      simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
    have hd : ContDiff ℝ ∞ (fun z : P × P ↦ fderiv ℝ (fun y ↦ a y z.2) z.1) := by
      have h : ContDiff ℝ ∞ (Function.uncurry (fun z : P × P ↦ fun y : P ↦ a y z.2)) :=
        hf.comp (contDiff_snd.prodMk contDiff_fst.snd)
      exact h.fderiv contDiff_fst (by simp)
    refine ⟨?_, ?_⟩
    · rw [Set.univ_prod_univ]
      exact hd.contDiffOn.clm_apply contDiffOn_const
    intro K hK hcompact i j
    obtain ⟨C, hC, hbound⟩ := ha.2 K hK hcompact (i + 1) j
    refine ⟨‖u‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
    intro x hx ξ
    have heq : (fun y ↦ iteratedFDeriv ℝ j
        (fun η ↦ fderiv ℝ (fun z ↦ a z η) y u) ξ) =
        (fun y ↦ fderiv ℝ (fun z ↦ iteratedFDeriv ℝ j (a z) ξ) y u) := by
      funext y
      exact iterated_comm comm a hf j y ξ u
    unfold symbolDerivative
    rw [heq]
    have hs : ContDiff ℝ ∞ (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) :=
      (parametric a hf j).comp (contDiff_id.prodMk contDiff_const)
    have hds : ContDiff ℝ ∞ (fderiv ℝ (fun y ↦ iteratedFDeriv ℝ j (a y) ξ)) :=
      hs.fderiv_right (by simp)
    have h := norm_iteratedFDeriv_clm_apply_const hds.contDiffAt
      (x := x) (n := i) (c := u) (by simp)
    rw [norm_iteratedFDeriv_fderiv] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (hbound x hx ξ) (norm_nonneg _)).trans_eq
      (by ring))
  have frequency_symbol {n r q : ℕ}
      (m : ℝ) (a : SymbolFunction n r q) (ha : IsSymbol Set.univ m a)
      (u : EuclideanSpace ℝ (Fin n)) :
      IsSymbol Set.univ (m - 1) (fun x ξ ↦ fderiv ℝ (a x) ξ u) := by
    let P := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    have hf : ContDiff ℝ ∞ (Function.uncurry a) := by
      simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
    have hd : ContDiff ℝ ∞ (fun z : P × P ↦ fderiv ℝ (a z.1) z.2) := by
      have h : ContDiff ℝ ∞ (Function.uncurry (fun z : P × P ↦ fun η : P ↦ a z.1 η)) :=
        hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
      exact h.fderiv contDiff_snd (by simp)
    refine ⟨?_, ?_⟩
    · rw [Set.univ_prod_univ]
      exact hd.contDiffOn.clm_apply contDiffOn_const
    intro K hK hcompact i j
    obtain ⟨C, hC, hbound⟩ := ha.2 K hK hcompact i (j + 1)
    let L : (P →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V u
    refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
    intro x hx ξ
    have h := mixed_map_bound L (fun y η ↦ fderiv ℝ (a y) η) hd i j x ξ
    rw [mixed_shift] at h
    have hc := hbound x hx ξ
    have he : m - ((j + 1 : ℕ) : ℝ) = m - 1 - (j : ℝ) := by push_cast; ring
    rw [he] at hc
    exact h.trans ((mul_le_mul_of_nonneg_left hc (norm_nonneg _)).trans_eq (by ring))
  have spatial_iterated_symbol {n r q : ℕ}
      (comm : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
        (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → W)
        (_hf : ContDiff ℝ ∞ (Function.uncurry f)) (x y u v : EuclideanSpace ℝ (Fin n)),
        fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
          fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u)
      (m : ℝ) (a : SymbolFunction n r q) (ha : IsSymbol Set.univ m a)
      (j : ℕ) (v : Fin j → EuclideanSpace ℝ (Fin n)) :
      IsSymbol Set.univ m (fun x ξ ↦ iteratedFDeriv ℝ j (fun y ↦ a y ξ) x v) := by
    have hf : ContDiff ℝ ∞ (Function.uncurry a) := by
      simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
    induction j with
    | zero => simpa only [iteratedFDeriv_zero_apply] using ha
    | succ j ih =>
      have hh := spatial_symbol comm m
        (fun x ξ ↦ iteratedFDeriv ℝ j (fun y ↦ a y ξ) x (Fin.tail v))
        (ih (Fin.tail v)) (v 0)
      have heq : (fun x ξ ↦ fderiv ℝ
          (fun y ↦ iteratedFDeriv ℝ j (fun z ↦ a z ξ) y (Fin.tail v)) x (v 0)) =
          (fun x ξ ↦ iteratedFDeriv ℝ (j + 1) (fun y ↦ a y ξ) x v) := by
        funext x ξ
        have hs : ContDiff ℝ ∞ (fun y ↦ a y ξ) :=
          hf.comp (contDiff_id.prodMk contDiff_const)
        have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j (fun y ↦ a y ξ)) x :=
          hs.contDiffAt.differentiableAt_iteratedFDeriv (m := j)
            (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)
        exact hd.iteratedFDeriv_succ_apply_left'.symm
      rwa [heq] at hh
  have frequency_iterated_symbol {n r q : ℕ}
      (m : ℝ) (a : SymbolFunction n r q) (ha : IsSymbol Set.univ m a)
      (j : ℕ) (v : Fin j → EuclideanSpace ℝ (Fin n)) :
      IsSymbol Set.univ (m - (j : ℝ)) (fun x ξ ↦ iteratedFDeriv ℝ j (a x) ξ v) := by
    have hf : ContDiff ℝ ∞ (Function.uncurry a) := by
      simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
    induction j with
    | zero => simpa only [iteratedFDeriv_zero_apply, Nat.cast_zero, sub_zero] using ha
    | succ j ih =>
      have hh := frequency_symbol (m - (j : ℝ))
        (fun x ξ ↦ iteratedFDeriv ℝ j (a x) ξ (Fin.tail v)) (ih (Fin.tail v)) (v 0)
      have heq : (fun x ξ ↦ fderiv ℝ
          (fun η ↦ iteratedFDeriv ℝ j (a x) η (Fin.tail v)) ξ (v 0)) =
          (fun x ξ ↦ iteratedFDeriv ℝ (j + 1) (a x) ξ v) := by
        funext x ξ
        have hs : ContDiff ℝ ∞ (a x) := hf.comp (contDiff_const.prodMk contDiff_id)
        have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j (a x)) ξ :=
          hs.contDiffAt.differentiableAt_iteratedFDeriv (m := j)
            (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)
        exact hd.iteratedFDeriv_succ_apply_left'.symm
      have he : m - (j : ℝ) - 1 = m - ((j + 1 : ℕ) : ℝ) := by push_cast; ring
      rwa [he, heq] at hh
  -- Apply the original ordered matrix product estimate to each coordinate contraction.
  classical
  let c := (-Complex.I) ^ j / (j.factorial : ℂ)
  let terms (α : Fin j → Fin n) : SymbolFunction n r t := symbolComp
    (fun x ξ ↦ iteratedFDeriv ℝ j (p x) ξ (fun a ↦ EuclideanSpace.single (α a) 1))
    (fun x ξ ↦ iteratedFDeriv ℝ j (fun y ↦ q y ξ) x
      (fun a ↦ EuclideanSpace.single (α a) 1))
  have ht (α : Fin j → Fin n) : IsSymbol Set.univ (l + m - (j : ℝ)) (terms α) := by
    have h := (frequency_iterated_symbol l p hp j
      (fun a ↦ EuclideanSpace.single (α a) 1)).symbolComp isOpen_univ
      (spatial_iterated_symbol mixed_fderiv_apply_comm m q hq j
        (fun a ↦ EuclideanSpace.single (α a) 1))
    convert h using 1
    ring
  have hs : IsSymbol Set.univ (l + m - (j : ℝ)) (∑ α, terms α) :=
    (symbolSpace Set.univ isOpen_univ (l + m - (j : ℝ)) r t).sum_mem (fun α _ ↦ ht α)
  have heq : compositionExpansionTerm p q j = c • ∑ α, terms α := by
    funext x ξ
    simp only [compositionExpansionTerm, terms, symbolComp, c, Pi.smul_apply,
      Finset.sum_apply]
  rw [heq]
  exact hs.smul isOpen_univ c

/-- Operators supported in the same set remain supported there after composition. -/
theorem HasOperatorSupport.comp (K : Set (EuclideanSpace ℝ (Fin n)))
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin t)))
    (Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (hPK : HasOperatorSupport K P) (hQK : HasOperatorSupport K Q) :
    HasOperatorSupport K (P.comp Q) := by
  /- Every value Q u is a Schwartz input for P, so the output support of P(Q u)
  lies in K. If u has support disjoint from K, the second condition on Q gives
  Q u=0, and linearity of P gives P(Q u)=0. No topological condition on K is needed. -/
  -- The output condition comes from P, while the input annihilation comes from Q.
  constructor
  · intro u
    exact hPK.1 (Q u)
  · intro u hu
    change P (Q u) = 0
    rw [hQK.2 u hu, map_zero]

/-- SG 3.10: the reduced amplitude quantizes to the actual continuous operator composition. -/
theorem quantize_compositionSymbol (l m : ℝ)
    (p : SymbolFunction n s t) (q : SymbolFunction n r s)
    (hp : IsSymbol Set.univ l p) (hq : IsSymbol Set.univ m q)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin t)))
    (Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (hP : ∀ v x, P v x = quantize p v x) (hQ : ∀ u x, Q u x = quantize q u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hPK : HasOperatorSupport K P) (hQK : HasOperatorSupport K Q)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχSupp : HasCompactSupport χ) (hone : K ⊆ interior {x | χ x = 1})
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize (compositionSymbol χ p q) u x = P (Q u) x := by
  /- Stage 1: recover compact spatial supports of p and q from P,Q. Let A=Q*
  be localFormalAdjoint and a=adjointSymbol χ q its exact left symbol. Its support
  is compact and the full pairing gives FourierSG(Qu)=rightSymbolFourierApply(a†)u.
  Stage 2: insert this equality into quantize p (Q u). Pull p(x,ξ) and exp(i<x,ξ>)
  inside the integrable y integral; this gives precisely leftRightAmplitude p (a†).
  Stage 3: apply the exact amplitude reduction theorem. The inverse normalization
  (2π)^(-n) occurs once, and the equality includes every lower-order and smoothing term. -/
  -- Recover the two actual spatial supports from the original supported operators.
  have hpSupp : HasCompactSupport p := hK.of_isClosed_subset (isClosed_tsupport p)
    (tsupport_symbol_subset_of_hasOperatorSupport l p hp P hP K hK.isClosed hPK)
  have hqSupp : HasCompactSupport q := hK.of_isClosed_subset (isClosed_tsupport q)
    (tsupport_symbol_subset_of_hasOperatorSupport m q hq Q hQ K hK.isClosed hQK)
  let a := adjointSymbol χ q
  let A := localFormalAdjoint m q hq Q hQ K hK hQK
  have ha : IsSymbol Set.univ m a := isSymbol_adjointSymbol m q hq hqSupp χ hχ hχSupp
  have haSupp : HasCompactSupport a :=
    hχSupp.of_isClosed_subset (isClosed_tsupport _) (tsupport_adjointSymbol_subset χ q)
  have hb : IsSymbol Set.univ m (symbolAdjoint a) := ha.symbolAdjoint isOpen_univ
  have hbSupp : HasCompactSupport (symbolAdjoint a) := by
    simpa only [HasCompactSupport, tsupport_symbolAdjoint] using haSupp
  -- The full adjoint pairing identifies the Fourier transform of the same Q u.
  have hfourier (ξ : EuclideanSpace ℝ (Fin n)) :
      fourierSG (Q u) ξ = rightSymbolFourierApply (symbolAdjoint a) u ξ :=
    fourierSG_eq_rightSymbolFourierApply m a ha haSupp Q A
      (fun v x ↦ localFormalAdjoint_apply m q hq Q hQ K hK hQK χ hχ hχSupp hone v x)
      (isSchwartzFormalAdjoint_localFormalAdjoint m q hq Q hQ K hK hQK) u ξ
  have hreduce := quantize_amplitudeSymbol (l + m) (leftRightAmplitude p (symbolAdjoint a))
    (isAmplitude_leftRightAmplitude l m p _ hp hb)
    (hasCompactSupport_leftRightAmplitude p _ hpSupp hbSupp) u
  calc
    _ = amplitudeApply (leftRightAmplitude p (symbolAdjoint a)) u x := congrFun hreduce x
    _ = quantize p (Q u) x := by
      unfold amplitudeApply quantize
      congr 1
      apply integral_congr_ae
      filter_upwards with ξ
      rw [hfourier]
      unfold rightSymbolFourierApply
      -- At fixed frequency the right-symbol integrand is genuinely integrable in y.
      rw [← (p x ξ).integral_comp_comm
        (integrable_rightSymbolFourierApply m _ hb hbSupp u ξ), ← integral_smul]
      apply integral_congr_ae
      filter_upwards with y
      have hphase : Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) =
          Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
            Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) := by
        rw [← Complex.exp_add, inner_sub_left]
        congr 1
        push_cast
        ring
      simp only [leftRightAmplitude, ContinuousLinearMap.comp_apply, hphase, mul_smul, map_smul]
    _ = P (Q u) x := (hP (Q u) x).symm

open Set in
open scoped ComplexConjugate in
/-- SG (3.10): all finite remainders of the actual composition have the predicted order. -/
theorem hasSymbolExpansion_compositionSymbol (l m : ℝ)
    (p : SymbolFunction n s t) (q : SymbolFunction n r s)
    (hp : IsSymbol Set.univ l p) (hq : IsSymbol Set.univ m q)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin t)))
    (Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (hP : ∀ v x, P v x = quantize p v x) (hQ : ∀ u x, Q u x = quantize q u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hPK : HasOperatorSupport K P) (hQK : HasOperatorSupport K Q)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχSupp : HasCompactSupport χ) (hone : K ⊆ interior {x | χ x = 1}) :
    HasSymbolExpansion Set.univ (fun j ↦ l + m - (j : ℝ))
      (compositionSymbol χ p q) (compositionExpansionTerm p q) := by
  /- Reduce the original composition amplitude to every finite order. The local differential
  algebra below proves its exact Leibniz coefficients using smooth Hessian symmetry; it does
  not require analyticity. The actual double formal adjoint then identifies the right-symbol
  expansion with q. Finally, finite triangular regrouping bounds every remainder. -/
  -- Work inside the space of smooth functions so every constant derivative is an endomorphism.
  let smoothFunctionSpace {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] : Submodule ℝ (X → H) := {
    carrier := {f | ContDiff ℝ ∞ f}
    zero_mem' := by
      change ContDiff ℝ ∞ (0 : X → H)
      exact contDiff_const
    add_mem' := by
      intro f g hf hg
      change ContDiff ℝ ∞ f at hf
      change ContDiff ℝ ∞ g at hg
      exact hf.add hg
    smul_mem' := by
      intro c f hf
      change ContDiff ℝ ∞ f at hf
      exact hf.const_smul c }
  have contDiff_smoothFunction {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] (f : smoothFunctionSpace (X := X) (H := H)) :
      ContDiff ℝ ∞ f.val := f.property
  let directionalDerivEnd {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] (v : X) :
      Module.End ℝ (smoothFunctionSpace (X := X) (H := H)) := {
    toFun f := ⟨fun x ↦ fderiv ℝ f.val x v, by
      change ContDiff ℝ ∞ (fun x ↦ fderiv ℝ f.val x v)
      exact ((contDiff_smoothFunction f).fderiv_right (by simp)).clm_apply contDiff_const⟩
    map_add' f g := by
      apply Subtype.ext
      funext x
      change fderiv ℝ (f.val + g.val) x v = _
      rw [fderiv_add ((contDiff_smoothFunction f).differentiable (by simp) x)
        ((contDiff_smoothFunction g).differentiable (by simp) x)]
      rfl
    map_smul' c f := by
      apply Subtype.ext
      funext x
      change fderiv ℝ (c • f.val) x v = _
      rw [fderiv_const_smul ((contDiff_smoothFunction f).differentiable (by simp) x)]
      rfl }
  -- Smooth Hessian symmetry, followed by bilinearity, makes the contractions commute.
  have directionalDerivEnd_commute {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] (u v : X) :
      Commute (directionalDerivEnd (H := H) u) (directionalDerivEnd (H := H) v) := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change fderiv ℝ (fun y ↦ fderiv ℝ f.val y v) x u =
      fderiv ℝ (fun y ↦ fderiv ℝ f.val y u) x v
    have hs : ContDiff ℝ ∞ (fderiv ℝ f.val) :=
      (contDiff_smoothFunction f).fderiv_right (by simp)
    have hd : Differentiable ℝ (fderiv ℝ f.val) := hs.differentiable (by simp)
    rw [fderiv_clm_apply (hd x) (differentiableAt_const v),
      fderiv_clm_apply (hd x) (differentiableAt_const u)]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
    exact ((contDiff_smoothFunction f).contDiffAt.isSymmSndFDerivAt (by simp)) u v
  have directionalDerivEnd_add {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] (u v : X) :
      directionalDerivEnd (H := H) (u + v) =
        directionalDerivEnd u + directionalDerivEnd v := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    exact (fderiv ℝ f.val x).map_add u v
  let contractedDerivEnd {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type} [Fintype ι] (u v : ι → X) :
      Module.End ℝ (smoothFunctionSpace (X := X) (H := H)) :=
    ∑ i, directionalDerivEnd (u i) * directionalDerivEnd (v i)
  have contractedDerivEnd_commute {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {ι κ : Type} [Fintype ι] [Fintype κ]
      (u v : ι → X) (w z : κ → X) :
      Commute (contractedDerivEnd (H := H) u v) (contractedDerivEnd w z) := by
    apply Commute.sum_left
    intro i _
    apply Commute.sum_right
    intro j _
    exact ((directionalDerivEnd_commute (u i) (w j)).mul_left
      (directionalDerivEnd_commute (v i) (w j))).mul_right
      ((directionalDerivEnd_commute (u i) (z j)).mul_left
        (directionalDerivEnd_commute (v i) (z j)))
  have contractedDerivEnd_add_left {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type} [Fintype ι]
      (u v w : ι → X) :
      contractedDerivEnd (H := H) (u + v) w =
        contractedDerivEnd u w + contractedDerivEnd v w := by
    simp only [contractedDerivEnd, Pi.add_apply, directionalDerivEnd_add,
      add_mul, Finset.sum_add_distrib]
  have contractedDerivEnd_add_pow {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type} [Fintype ι]
      (u v w : ι → X) (j : ℕ) :
      contractedDerivEnd (H := H) (u + v) w ^ j =
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) •
          (contractedDerivEnd u w ^ i * contractedDerivEnd v w ^ (j - i)) := by
    rw [contractedDerivEnd_add_left]
    rw [(contractedDerivEnd_commute u w v w).add_pow]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_comm]
  -- Ordered coordinate words identify powers of a contraction with the original derivatives.
  let directionalWord {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {j : ℕ} : (Fin j → X) →
      Module.End ℝ (smoothFunctionSpace (X := X) (H := H)) :=
    Nat.rec (motive := fun j ↦ (Fin j → X) →
      Module.End ℝ (smoothFunctionSpace (X := X) (H := H))) (fun _ ↦ 1)
        (fun _ ih v ↦ directionalDerivEnd (v 0) * ih (Fin.tail v)) j
  have directionalWord_apply {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {j : ℕ} (v : Fin j → X)
      (f : smoothFunctionSpace (X := X) (H := H)) (x : X) :
      ((directionalWord v) f).val x = iteratedFDeriv ℝ j f.val x v := by
    induction j generalizing x with
    | zero =>
      simp [directionalWord, iteratedFDeriv_zero_apply]
    | succ j ih =>
      change fderiv ℝ (fun y ↦ ((directionalWord (Fin.tail v)) f).val y) x (v 0) = _
      have ht : (fun y ↦ ((directionalWord (Fin.tail v)) f).val y) =
          fun y ↦ iteratedFDeriv ℝ j f.val y (Fin.tail v) := by
        funext y
        exact ih (Fin.tail v) y
      rw [ht, iteratedFDeriv_succ_apply_left]
      have hs : ContDiff ℝ ∞ (iteratedFDeriv ℝ j f.val) :=
        (contDiff_smoothFunction f).iteratedFDeriv_right (by simp)
      exact fderiv_continuousMultilinear_apply_const_apply
        (hs.differentiable (by simp) x) (Fin.tail v) (v 0)
  have directionalWord_commute_end {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {j : ℕ} (v : Fin j → X) (u : X) :
      Commute (directionalWord (H := H) v) (directionalDerivEnd u) := by
    induction j with
    | zero => exact Commute.one_left _
    | succ j ih =>
      exact (directionalDerivEnd_commute (v 0) u).mul_left (ih (Fin.tail v))
  have contractedDerivEnd_pow {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type} [Fintype ι]
      (u v : ι → X) (j : ℕ) :
      contractedDerivEnd (H := H) u v ^ j =
        ∑ α : Fin j → ι, directionalWord (u ∘ α) * directionalWord (v ∘ α) := by
    classical
    induction j with
    | zero => simp [directionalWord]
    | succ j ih =>
      let e : (Fin (j + 1) → ι) ≃ ι × (Fin j → ι) :=
        { toFun := fun α ↦ (α 0, Fin.tail α)
          invFun := fun p ↦ Fin.cons p.1 p.2
          left_inv := fun α ↦ Fin.cons_self_tail α
          right_inv := fun p ↦ by simp }
      have hsum : (∑ α : Fin (j + 1) → ι,
          directionalWord (H := H) (u ∘ α) * directionalWord (v ∘ α)) =
          ∑ i, ∑ α : Fin j → ι,
            directionalWord (u ∘ Fin.cons i α) * directionalWord (v ∘ Fin.cons i α) := by
        rw [← Fintype.sum_prod_type (fun p : ι × (Fin j → ι) ↦
          directionalWord (H := H) (u ∘ Fin.cons p.1 p.2) *
            directionalWord (v ∘ Fin.cons p.1 p.2))]
        apply Fintype.sum_equiv e
        intro α
        change _ = directionalWord (u ∘ Fin.cons (α 0) (Fin.tail α)) *
          directionalWord (v ∘ Fin.cons (α 0) (Fin.tail α))
        rw [Fin.cons_self_tail]
      rw [hsum, pow_succ', ih]
      simp only [contractedDerivEnd, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro α _
      change (directionalDerivEnd (u i) * directionalDerivEnd (v i)) *
        (directionalWord (u ∘ α) * directionalWord (v ∘ α)) =
          (directionalDerivEnd (u i) * directionalWord (u ∘ α)) *
            (directionalDerivEnd (v i) * directionalWord (v ∘ α))
      rw [mul_assoc, ← mul_assoc (directionalDerivEnd (v i)),
        (directionalWord_commute_end (u ∘ α) (v i)).eq.symm]
      simp only [mul_assoc]
  have contractedDerivEnd_pow_apply {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type} [Fintype ι]
      (u v : ι → X) (j : ℕ) (f : smoothFunctionSpace (X := X) (H := H)) (x : X) :
      ((contractedDerivEnd u v ^ j) f).val x =
        ∑ α : Fin j → ι, iteratedFDeriv ℝ j
          (fun y ↦ iteratedFDeriv ℝ j f.val y (v ∘ α)) x (u ∘ α) := by
    rw [contractedDerivEnd_pow]
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro α _
    change ((directionalWord (u ∘ α)) ((directionalWord (v ∘ α)) f)).val x = _
    rw [directionalWord_apply]
    congr 2
    funext y
    exact directionalWord_apply (v ∘ α) f y
  -- Affine restriction intertwines all these derivatives, including their finite powers.
  have iteratedFDeriv_affine_comp {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {Y : Type} [NormedAddCommGroup Y]
      [NormedSpace ℝ Y] (f : X → H) (hf : ContDiff ℝ ∞ f) (L : Y →L[ℝ] X)
      (c : X) (y : Y) (j : ℕ) (v : Fin j → Y) :
      iteratedFDeriv ℝ j (fun z ↦ f (c + L z)) y v =
        iteratedFDeriv ℝ j f (c + L y) (L ∘ v) := by
    have hshift : ContDiff ℝ ∞ (fun z ↦ f (c + z)) :=
      hf.comp (contDiff_const.add contDiff_id)
    have h := congrArg (fun D ↦ D v) (L.iteratedFDeriv_comp_right hshift y (i := j) (by simp))
    simpa only [Function.comp_def, iteratedFDeriv_comp_add_left,
      ContinuousMultilinearMap.compContinuousLinearMap_apply] using h
  let smoothPullbackAffine {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (L : Y →L[ℝ] X) (c : X) :
      smoothFunctionSpace (X := X) (H := H) →ₗ[ℝ] smoothFunctionSpace (X := Y) (H := H) := {
    toFun f := ⟨fun y ↦ f.val (c + L y), by
      change ContDiff ℝ ∞ (fun y ↦ f.val (c + L y))
      exact (contDiff_smoothFunction f).comp (contDiff_const.add L.contDiff)⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have smoothPullbackAffine_directional {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {Y : Type} [NormedAddCommGroup Y]
      [NormedSpace ℝ Y] (L : Y →L[ℝ] X) (c : X) (u : Y) :
      (directionalDerivEnd (H := H) u).comp (smoothPullbackAffine L c) =
        (smoothPullbackAffine L c).comp (directionalDerivEnd (L u)) := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext y
    change fderiv ℝ (fun z ↦ f.val (c + L z)) y u =
      fderiv ℝ f.val (c + L y) (L u)
    have h := iteratedFDeriv_affine_comp f.val (contDiff_smoothFunction f) L c y 1
      (fun _ ↦ u)
    simpa only [iteratedFDeriv_one_apply, Function.comp_apply] using h
  have smoothPullbackAffine_contracted {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {Y : Type} [NormedAddCommGroup Y]
      [NormedSpace ℝ Y] {ι : Type} [Fintype ι] (L : Y →L[ℝ] X) (c : X)
      (u v : ι → Y) :
      (contractedDerivEnd (H := H) u v).comp (smoothPullbackAffine L c) =
        (smoothPullbackAffine L c).comp (contractedDerivEnd (L ∘ u) (L ∘ v)) := by
    apply LinearMap.ext
    intro f
    simp only [contractedDerivEnd, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change directionalDerivEnd (u i) (directionalDerivEnd (v i) (smoothPullbackAffine L c f)) =
      smoothPullbackAffine L c (directionalDerivEnd (L (u i))
        (directionalDerivEnd (L (v i)) f))
    have hv := LinearMap.congr_fun (smoothPullbackAffine_directional (H := H) L c (v i)) f
    have hu := LinearMap.congr_fun (smoothPullbackAffine_directional (H := H) L c (u i))
      (directionalDerivEnd (L (v i)) f)
    dsimp only [LinearMap.comp_apply] at hv hu
    rw [hv, hu]
  have smoothPullbackAffine_contracted_pow {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {Y : Type} [NormedAddCommGroup Y]
      [NormedSpace ℝ Y] {ι : Type} [Fintype ι] (L : Y →L[ℝ] X) (c : X)
      (u v : ι → Y) (j : ℕ) :
      (contractedDerivEnd (H := H) u v ^ j).comp (smoothPullbackAffine L c) =
        (smoothPullbackAffine L c).comp (contractedDerivEnd (L ∘ u) (L ∘ v) ^ j) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ, pow_succ]
      change ((contractedDerivEnd u v ^ j).comp (contractedDerivEnd u v)).comp
        (smoothPullbackAffine L c) = (smoothPullbackAffine L c).comp
          ((contractedDerivEnd (L ∘ u) (L ∘ v) ^ j).comp
            (contractedDerivEnd (L ∘ u) (L ∘ v)))
      rw [LinearMap.comp_assoc, smoothPullbackAffine_contracted,
        ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc]
  -- Differentiate separated factors before restricting their frequency variables to the diagonal.
  -- The bilinear map retains the order of the matrix factors throughout.
  let smoothSeparated {X H Y V W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] (B : H →L[ℝ] V →L[ℝ] W)
      (f : smoothFunctionSpace (X := X) (H := H))
      (g : smoothFunctionSpace (X := Y) (H := V)) :
      smoothFunctionSpace (X := X × Y) (H := W) :=
    ⟨fun z ↦ B (f.val z.1) (g.val z.2), by
      change ContDiff ℝ ∞ (fun z : X × Y ↦ B (f.val z.1) (g.val z.2))
      exact (B.contDiff.comp ((contDiff_smoothFunction f).comp contDiff_fst)).clm_apply
        ((contDiff_smoothFunction g).comp contDiff_snd)⟩
  have directionalDerivEnd_smoothSeparated {X H Y V W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] (B : H →L[ℝ] V →L[ℝ] W)
      (f : smoothFunctionSpace (X := X) (H := H))
      (g : smoothFunctionSpace (X := Y) (H := V)) (u : X) (v : Y) :
      directionalDerivEnd (u, v) (smoothSeparated B f g) =
        smoothSeparated B (directionalDerivEnd u f) g +
          smoothSeparated B f (directionalDerivEnd v g) := by
    apply Subtype.ext
    funext z
    change fderiv ℝ (fun z : X × Y ↦ B (f.val z.1) (g.val z.2)) z (u, v) = _
    have hf := (contDiff_smoothFunction f).differentiable (by simp) z.1
    have hg := (contDiff_smoothFunction g).differentiable (by simp) z.2
    have h := (B.hasFDerivAt.comp z (hf.hasFDerivAt.comp z hasFDerivAt_fst)).clm_apply
      (hg.hasFDerivAt.comp z hasFDerivAt_snd)
    dsimp only [Function.comp_def] at h
    rw [h.fderiv]
    change B (f.val z.1) (fderiv ℝ g.val z.2 v) +
        B (fderiv ℝ f.val z.1 u) (g.val z.2) = _
    exact add_comm _ _
  have directionalDerivEnd_smoothSeparated_left {X H Y V W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] (B : H →L[ℝ] V →L[ℝ] W)
      (f : smoothFunctionSpace (X := X) (H := H))
      (g : smoothFunctionSpace (X := Y) (H := V)) (u : X) :
      directionalDerivEnd (u, 0) (smoothSeparated B f g) =
        smoothSeparated B (directionalDerivEnd u f) g := by
    rw [directionalDerivEnd_smoothSeparated]
    have hzero : directionalDerivEnd (0 : Y) g = 0 := by
      apply Subtype.ext
      funext y
      exact map_zero (fderiv ℝ g.val y)
    rw [hzero]
    have hzero : smoothSeparated B f (0 : smoothFunctionSpace (X := Y) (H := V)) = 0 := by
      apply Subtype.ext
      funext z
      exact map_zero (B (f.val z.1))
    rw [hzero, add_zero]
  have directionalDerivEnd_smoothSeparated_right {X H Y V W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] (B : H →L[ℝ] V →L[ℝ] W)
      (f : smoothFunctionSpace (X := X) (H := H))
      (g : smoothFunctionSpace (X := Y) (H := V)) (v : Y) :
      directionalDerivEnd (0, v) (smoothSeparated B f g) =
        smoothSeparated B f (directionalDerivEnd v g) := by
    rw [directionalDerivEnd_smoothSeparated]
    have hzero : directionalDerivEnd (0 : X) f = 0 := by
      apply Subtype.ext
      funext x
      exact map_zero (fderiv ℝ f.val x)
    rw [hzero]
    have hzero : smoothSeparated B (0 : smoothFunctionSpace (X := X) (H := H)) g = 0 := by
      apply Subtype.ext
      funext z
      change B 0 (g.val z.2) = 0
      rw [map_zero, zero_apply]
    rw [hzero, zero_add]
  let smoothSeparatedRight {X H Y V W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] (B : H →L[ℝ] V →L[ℝ] W)
      (f : smoothFunctionSpace (X := X) (H := H)) :
      smoothFunctionSpace (X := Y) (H := V) →ₗ[ℝ]
        smoothFunctionSpace (X := X × Y) (H := W) := {
    toFun := smoothSeparated B f
    map_add' g h := by
      apply Subtype.ext
      funext z
      exact map_add (B (f.val z.1)) (g.val z.2) (h.val z.2)
    map_smul' c g := by
      apply Subtype.ext
      funext z
      exact map_smul (B (f.val z.1)) c (g.val z.2) }
  have smoothSeparatedRight_contracted {X H Y V W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] {ι : Type} [Fintype ι]
      (B : H →L[ℝ] V →L[ℝ] W) (f : smoothFunctionSpace (X := X) (H := H))
      (u v : ι → Y) (j : ℕ) (g : smoothFunctionSpace (X := Y) (H := V)) :
      (contractedDerivEnd (fun a ↦ (0, u a)) (fun a ↦ (0, v a)) ^ j)
          (smoothSeparated B f g) =
        smoothSeparated B f ((contractedDerivEnd u v ^ j) g) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', pow_succ']
      change contractedDerivEnd _ _ ((contractedDerivEnd _ _ ^ j) _) =
        smoothSeparated B f (contractedDerivEnd _ _ ((contractedDerivEnd _ _ ^ j) g))
      rw [ih]
      change (∑ a, directionalDerivEnd (H := W) ((0 : X), u a) *
        directionalDerivEnd (H := W) ((0 : X), v a))
        (smoothSeparated B f ((contractedDerivEnd u v ^ j) g)) =
        smoothSeparatedRight B f ((contractedDerivEnd u v)
          ((contractedDerivEnd u v ^ j) g))
      unfold contractedDerivEnd
      simp only [LinearMap.sum_apply, map_sum]
      apply Finset.sum_congr rfl
      intro a _
      change directionalDerivEnd (0, u a) (directionalDerivEnd (0, v a) _) = _
      rw [directionalDerivEnd_smoothSeparated_right, directionalDerivEnd_smoothSeparated_right]
      rfl
  have directionalWord_smoothSeparated_left {X H Y V W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] {j : ℕ}
      (B : H →L[ℝ] V →L[ℝ] W) (f : smoothFunctionSpace (X := X) (H := H))
      (g : smoothFunctionSpace (X := Y) (H := V)) (u : Fin j → X) :
      directionalWord (fun a ↦ (u a, 0)) (smoothSeparated B f g) =
        smoothSeparated B (directionalWord u f) g := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change directionalDerivEnd (u 0, 0)
        (directionalWord (fun a ↦ (Fin.tail u a, 0)) (smoothSeparated B f g)) = _
      rw [ih, directionalDerivEnd_smoothSeparated_left]
      rfl
  have directionalWord_smoothSeparated_right {X H Y V W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] {j : ℕ}
      (B : H →L[ℝ] V →L[ℝ] W) (f : smoothFunctionSpace (X := X) (H := H))
      (g : smoothFunctionSpace (X := Y) (H := V)) (v : Fin j → Y) :
      directionalWord (fun a ↦ (0, v a)) (smoothSeparated B f g) =
        smoothSeparated B f (directionalWord v g) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change directionalDerivEnd (0, v 0)
        (directionalWord (fun a ↦ (0, Fin.tail v a)) (smoothSeparated B f g)) = _
      rw [ih, directionalDerivEnd_smoothSeparated_right]
      rfl
  have contractedDerivEnd_pow_smoothSeparated_apply {X H Y V W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] {ι : Type} [Fintype ι]
      (B : H →L[ℝ] V →L[ℝ] W) (f : smoothFunctionSpace (X := X) (H := H))
      (g : smoothFunctionSpace (X := Y) (H := V)) (u : ι → X) (v : ι → Y)
      (j : ℕ) (x : X) (y : Y) :
      ((contractedDerivEnd (fun a ↦ (u a, 0)) (fun a ↦ (0, v a)) ^ j)
        (smoothSeparated B f g)).val (x, y) =
        ∑ α : Fin j → ι, B (iteratedFDeriv ℝ j f.val x (u ∘ α))
          (iteratedFDeriv ℝ j g.val y (v ∘ α)) := by
    rw [contractedDerivEnd_pow]
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro α _
    change (directionalWord (fun a ↦ (u (α a), 0))
      (directionalWord (fun a ↦ (0, v (α a))) (smoothSeparated B f g))).val (x, y) = _
    rw [directionalWord_smoothSeparated_right, directionalWord_smoothSeparated_left]
    change B ((directionalWord (u ∘ α) f).val x) ((directionalWord (v ∘ α) g).val y) = _
    rw [directionalWord_apply, directionalWord_apply]
  -- Relate ambient contraction powers to the nested derivatives used by SG coefficient formulas.
  have contDiff_parametric_iteratedFDeriv {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {Y : Type}
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (f : X → Y → H) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (j : ℕ) :
      ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ j (f z.1) z.2) := by
    induction j with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Y H).symm : _ →L[ℝ] Y [×0]→L[ℝ] H)
    | succ j ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : X × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ j (f z.1) η)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : X × Y ↦ fderiv ℝ (iteratedFDeriv ℝ j (f z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ Y) H).symm :
          _ →L[ℝ] Y [×(j + 1)]→L[ℝ] H)
  have contractedDerivEnd_pow_pair_apply {X H : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type} [Fintype ι]
      (e : ι → X) (g : smoothFunctionSpace (X := X × X) (H := H))
      (x ξ : X) (j : ℕ) :
      ((contractedDerivEnd (fun a ↦ (0, e a)) (fun a ↦ (e a, 0)) ^ j) g).val (x, ξ) =
        ∑ α : Fin j → ι,
          iteratedFDeriv ℝ j
            (fun η ↦ iteratedFDeriv ℝ j (fun y ↦ g.val (y, η)) x) ξ (e ∘ α) (e ∘ α) := by
    rw [contractedDerivEnd_pow_apply]
    apply Finset.sum_congr rfl
    intro α _
    let v := e ∘ α
    have hinner : (fun z : X × X ↦ iteratedFDeriv ℝ j g.val z (fun a ↦ (v a, 0))) =
        fun z ↦ iteratedFDeriv ℝ j (fun y ↦ g.val (y, z.2)) z.1 v := by
      funext z
      symm
      simpa only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, zero_add, add_zero,
        Function.comp_def] using iteratedFDeriv_affine_comp g.val
        (contDiff_smoothFunction g) (ContinuousLinearMap.inl ℝ X X) (0, z.2) z.1 j v
    have hs : ContDiff ℝ ∞ (fun z : X × X ↦
        iteratedFDeriv ℝ j g.val z (fun a ↦ (v a, 0))) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ X × X) H
        (fun a ↦ (v a, 0))).contDiff.comp
          ((contDiff_smoothFunction g).iteratedFDeriv_right (by simp))
    have houter := iteratedFDeriv_affine_comp
      (fun z : X × X ↦ iteratedFDeriv ℝ j g.val z (fun a ↦ (v a, 0))) hs
      (ContinuousLinearMap.inr ℝ X X) (x, 0) ξ j v
    simp only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero,
      Function.comp_def] at houter
    change iteratedFDeriv ℝ j
      (fun z : X × X ↦ iteratedFDeriv ℝ j g.val z (fun a ↦ (v a, 0))) (x, ξ)
        (fun a ↦ (0, v a)) = _
    rw [← houter]
    have heval : (fun z ↦ iteratedFDeriv ℝ j g.val (x, z) (fun a ↦ (v a, 0))) =
        fun z ↦ iteratedFDeriv ℝ j (fun y ↦ g.val (y, z)) x v :=
      congrArg (fun F : X × X → H ↦ fun z ↦ F (x, z)) hinner
    rw [heval]
    have hparam := contDiff_parametric_iteratedFDeriv (fun η y ↦ g.val (y, η))
      ((contDiff_smoothFunction g).comp (contDiff_snd.prodMk contDiff_fst)) j
    have hfixed : ContDiff ℝ ∞
        (fun η ↦ iteratedFDeriv ℝ j (fun y ↦ g.val (y, η)) x) :=
      hparam.comp (contDiff_id.prodMk contDiff_const)
    exact congrArg (fun D ↦ D v)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ X) H v).iteratedFDeriv_comp_left
        hfixed.contDiffAt (by simp))
  -- On the frequency diagonal, one derivative splits between the two independent factors.
  -- The finite binomial theorem gives the exact coefficients without an infinite rearrangement.
  have contractedDerivEnd_pow_leibniz {X H V W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] {ι : Type} [Fintype ι]
      (B : H →L[ℝ] V →L[ℝ] W) (f : smoothFunctionSpace (X := X) (H := H))
      (g : smoothFunctionSpace (X := X × X) (H := V)) (e : ι → X) (j : ℕ)
      (x ξ : X) :
      let a : smoothFunctionSpace (X := X × X) (H := W) :=
        ⟨fun z ↦ B (f.val z.2) (g.val z), by
          change ContDiff ℝ ∞ (fun z : X × X ↦ B (f.val z.2) (g.val z))
          exact (B.contDiff.comp ((contDiff_smoothFunction f).comp contDiff_snd)).clm_apply
            (contDiff_smoothFunction g)⟩
      ((contractedDerivEnd (fun a ↦ (0, e a)) (fun a ↦ (e a, 0)) ^ j) a).val (x, ξ) =
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) •
          ∑ α : Fin i → ι, B (iteratedFDeriv ℝ i f.val ξ (e ∘ α))
            (iteratedFDeriv ℝ i
              (fun y ↦ ((contractedDerivEnd (fun a ↦ (0, e a))
                (fun a ↦ (e a, 0)) ^ (j - i)) g).val (y, ξ)) x (e ∘ α)) := by
    intro a
    let L : X × X →L[ℝ] X × (X × X) :=
      (ContinuousLinearMap.snd ℝ X X).prod (ContinuousLinearMap.id ℝ (X × X))
    let F := smoothSeparated B f g
    let u : ι → X × (X × X) := fun a ↦ (e a, (0, 0))
    let v : ι → X × (X × X) := fun a ↦ (0, (0, e a))
    let w : ι → X × (X × X) := fun a ↦ (0, (e a, 0))
    have ha : a = smoothPullbackAffine L 0 F := by
      apply Subtype.ext
      funext z
      change B (f.val z.2) (g.val z) = F.val (0 + L z)
      rw [zero_add]
      rfl
    have hLfreq : L ∘ (fun a ↦ (0, e a)) = u + v := by
      funext a
      simp [L, u, v]
    have hLspace : L ∘ (fun a ↦ (e a, 0)) = w := by
      funext a
      rfl
    have hinter := LinearMap.congr_fun
      (smoothPullbackAffine_contracted_pow (H := W) L 0
        (fun a ↦ (0, e a)) (fun a ↦ (e a, 0)) j) F
    dsimp only [LinearMap.comp_apply] at hinter
    rw [hLfreq, hLspace] at hinter
    rw [ha, hinter, contractedDerivEnd_add_pow]
    simp only [LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
      Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change ((contractedDerivEnd (H := W) u w ^ i *
      contractedDerivEnd (H := W) v w ^ (j - i)) F).val
      (0 + L (x, ξ)) = _
    rw [zero_add]
    change ((contractedDerivEnd u w ^ i)
      ((contractedDerivEnd v w ^ (j - i)) F)).val (ξ, (x, ξ)) = _
    have hright := smoothSeparatedRight_contracted B f
      (fun a ↦ ((0 : X), e a)) (fun a ↦ (e a, (0 : X))) (j - i) g
    change ((contractedDerivEnd v w ^ (j - i)) F) = _ at hright
    rw [hright]
    change ((contractedDerivEnd (fun a ↦ (e a, (0 : X × X)))
        (fun a ↦ ((0 : X), (e a, (0 : X)))) ^ i)
      (smoothSeparated B f ((contractedDerivEnd _ _ ^ (j - i)) g))).val (ξ, (x, ξ)) = _
    rw [contractedDerivEnd_pow_smoothSeparated_apply]
    apply Finset.sum_congr rfl
    intro α _
    congr 1
    symm
    let g' := ((contractedDerivEnd (fun a ↦ ((0 : X), e a))
      (fun a ↦ (e a, (0 : X))) ^ (j - i)) g)
    simpa only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, zero_add, add_zero,
      Function.comp_def] using iteratedFDeriv_affine_comp g'.val (contDiff_smoothFunction g')
        (ContinuousLinearMap.inl ℝ X X) (0, ξ) x i (e ∘ α)
  -- The binomial coefficients cancel the ordered-list factorials with the original complex phase.
  have amplitudeExpansionTerm_leftRight {n r s t : ℕ}
      (p : SymbolFunction n s t) (a : SymbolFunction n s r)
      (hp : ContDiff ℝ ∞ (Function.uncurry p))
      (ha : ContDiff ℝ ∞ (Function.uncurry (symbolAdjoint a))) (j : ℕ) :
      amplitudeExpansionTerm (leftRightAmplitude p (symbolAdjoint a)) j =
        ∑ i ∈ Finset.range (j + 1),
          compositionExpansionTerm p (adjointExpansionTerm a (j - i)) i := by
    classical
    funext x ξ
    let X := EuclideanSpace ℝ (Fin n)
    let U := EuclideanSpace ℂ (Fin r)
    let V := EuclideanSpace ℂ (Fin s)
    let W := EuclideanSpace ℂ (Fin t)
    let e : Fin n → X := fun a ↦ EuclideanSpace.single a 1
    let c : ℕ → ℂ := fun j ↦ (-Complex.I) ^ j / (j.factorial : ℂ)
    let B := (ContinuousLinearMap.compL ℂ U V W).bilinearRestrictScalars ℝ
    let f : smoothFunctionSpace (X := X) (H := V →L[ℂ] W) :=
      ⟨p x, hp.comp (contDiff_const.prodMk contDiff_id)⟩
    let g : smoothFunctionSpace (X := X × X) (H := U →L[ℂ] V) :=
      ⟨Function.uncurry (symbolAdjoint a), ha⟩
    let A : smoothFunctionSpace (X := X × X) (H := U →L[ℂ] W) :=
      ⟨fun z ↦ B (f.val z.2) (g.val z), by
        change ContDiff ℝ ∞ (fun z : X × X ↦ B (f.val z.2) (g.val z))
        exact (B.contDiff.comp ((contDiff_smoothFunction f).comp contDiff_snd)).clm_apply
          (contDiff_smoothFunction g)⟩
    let T (k : ℕ) : smoothFunctionSpace (X := X × X) (H := U →L[ℂ] V) :=
      (contractedDerivEnd (fun a ↦ (0, e a)) (fun a ↦ (e a, 0)) ^ k) g
    have hT (k : ℕ) : (fun y ↦ adjointExpansionTerm a k y ξ) =
        fun y ↦ c k • (T k).val (y, ξ) := by
      funext y
      rw [show (T k).val (y, ξ) = _ from contractedDerivEnd_pow_pair_apply e g y ξ k]
      rfl
    have hc (i : ℕ) (hi : i ≤ j) : c j * (j.choose i : ℂ) = c i * c (j - i) := by
      have hfac : (j.choose i : ℂ) * (i.factorial : ℂ) * ((j - i).factorial : ℂ) =
          (j.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
      have hpow : (-Complex.I) ^ j = (-Complex.I) ^ i * (-Complex.I) ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_of_le hi]
      have hratio : (j.choose i : ℂ) / (j.factorial : ℂ) =
          1 / ((i.factorial : ℂ) * ((j - i).factorial : ℂ)) := by
        apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))
          (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i))
            (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j - i))))).mpr
        simpa only [one_mul, ← mul_assoc] using hfac
      dsimp only [c]
      calc
        _ = (-Complex.I) ^ j * ((j.choose i : ℂ) / (j.factorial : ℂ)) := by ring
        _ = (-Complex.I) ^ j * (1 / ((i.factorial : ℂ) * ((j - i).factorial : ℂ))) := by
          rw [hratio]
        _ = _ := by rw [div_mul_div_comm, hpow, mul_one_div]
    have hA : amplitudeExpansionTerm (leftRightAmplitude p (symbolAdjoint a)) j x ξ =
        c j • ((contractedDerivEnd (fun a ↦ (0, e a)) (fun a ↦ (e a, 0)) ^ j) A).val
          (x, ξ) := by
      rw [contractedDerivEnd_pow_pair_apply]
      rfl
    rw [hA]
    have hleibniz := contractedDerivEnd_pow_leibniz B f g e j x ξ
    change ((contractedDerivEnd (fun a ↦ (0, e a))
      (fun a ↦ (e a, 0)) ^ j) A).val (x, ξ) = _ at hleibniz
    rw [hleibniz, Finset.smul_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    change c j • ((j.choose i : ℝ) • ∑ α : Fin i → Fin n,
      (iteratedFDeriv ℝ i (p x) ξ (e ∘ α)).comp
        (iteratedFDeriv ℝ i (fun y ↦ (T (j - i)).val (y, ξ)) x (e ∘ α))) =
      c i • ∑ α : Fin i → Fin n,
        (iteratedFDeriv ℝ i (p x) ξ (e ∘ α)).comp
          (iteratedFDeriv ℝ i (fun y ↦ adjointExpansionTerm a (j - i) y ξ) x (e ∘ α))
    rw [hT]
    have hs : ContDiff ℝ ∞ (fun y ↦ (T (j - i)).val (y, ξ)) :=
      (contDiff_smoothFunction (T (j - i))).comp (contDiff_id.prodMk contDiff_const)
    rw [iteratedFDeriv_const_smul_apply' (hs.contDiffAt.of_le (by simp))]
    simp only [smul_apply, ContinuousLinearMap.comp_smul,
      ← Finset.smul_sum, ← Complex.coe_smul, smul_smul, Complex.ofReal_natCast]
    rw [hc i hi']
  -- Only finite sums are needed: the coefficient is linear in its right symbol.
  have compositionExpansionTerm_sub_sum {n r s t : ℕ}
      (p : SymbolFunction n s t) (q : SymbolFunction n r s) (a : ℕ → SymbolFunction n r s)
      (hq : ContDiff ℝ ∞ (Function.uncurry q))
      (ha : ∀ k, ContDiff ℝ ∞ (Function.uncurry (a k))) (i N : ℕ) :
      compositionExpansionTerm p (q - ∑ k ∈ Finset.range N, a k) i =
        compositionExpansionTerm p q i -
          ∑ k ∈ Finset.range N, compositionExpansionTerm p (a k) i := by
    funext x ξ
    have hqs : ContDiffAt ℝ i (fun y ↦ q y ξ) x :=
      (hq.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by simp)
    have has (k : ℕ) : ContDiffAt ℝ i (fun y ↦ a k y ξ) x :=
      ((ha k).comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by simp)
    have hcomp_sum
        (L : EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t))
        (R : ℕ → EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)) :
        L.comp (∑ k ∈ Finset.range N, R k) = ∑ k ∈ Finset.range N, L.comp (R k) := by
      ext v
      simp [ContinuousLinearMap.comp_apply]
    simp only [compositionExpansionTerm, Pi.sub_apply, Finset.sum_apply]
    rw [fun_iteratedFDeriv_sub_apply hqs (ContDiffAt.sum (fun k _ ↦ has k))]
    rw [iteratedFDeriv_fun_sum_apply (fun k _ ↦ has k)]
    simp only [sub_apply, sum_apply, ContinuousLinearMap.comp_sub,
      hcomp_sum, Finset.sum_sub_distrib, smul_sub]
    rw [Finset.sum_comm]
    simp only [Finset.smul_sum]
  -- Reindex the finite triangle by the number of derivatives falling on the left symbol.
  have triangular_sum {G : Type} [AddCommMonoid G] (f : ℕ → ℕ → G) (N : ℕ) :
      (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), f i (j - i)) =
        ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i), f i k := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have hinner : (∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N + 1 - i), f i k) =
          ∑ i ∈ Finset.range N, ((∑ k ∈ Finset.range (N - i), f i k) + f i (N - i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hei : N + 1 - i = (N - i) + 1 := by
          have := Finset.mem_range.mp hi
          omega
        rw [hei, Finset.sum_range_succ]
      rw [Finset.sum_range_succ (f := fun i ↦ ∑ k ∈ Finset.range (N + 1 - i), f i k),
        hinner, Finset.sum_add_distrib]
      simp only [Nat.add_sub_cancel_left, Finset.sum_range_one, Nat.sub_self, add_assoc]
  -- The full Schwartz pairing and symbol uniqueness identify the actual double adjoint with q.
  have composition_right_symbol_expansion {n r s : ℕ} (m : ℝ)
      (q : SymbolFunction n r s) (hq : IsSymbol univ m q)
      (Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
      (hQ : ∀ u x, Q u x = quantize q u x)
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hQK : HasOperatorSupport K Q)
      (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
      (hcχ : HasCompactSupport χ) (hone : K ⊆ interior {x | χ x = 1}) :
      HasSymbolExpansion univ (fun j ↦ m - (j : ℝ)) q
        (adjointExpansionTerm (adjointSymbol χ q)) := by
    -- Both adjoints use the original supported operator and the same cutoff.
    have hqSupp : HasCompactSupport q := hK.of_isClosed_subset (isClosed_tsupport q)
      (tsupport_symbol_subset_of_hasOperatorSupport m q hq Q hQ K hK.isClosed hQK)
    let a := adjointSymbol χ q
    let A := localFormalAdjoint m q hq Q hQ K hK hQK
    have ha : IsSymbol univ m a := isSymbol_adjointSymbol m q hq hqSupp χ hχ hcχ
    have hAact : ∀ u x, A u x = quantize a u x :=
      localFormalAdjoint_apply m q hq Q hQ K hK hQK χ hχ hcχ hone
    have hQA : IsSchwartzFormalAdjoint Q A :=
      isSchwartzFormalAdjoint_localFormalAdjoint m q hq Q hQ K hK hQK
    have hAK : HasOperatorSupport K A :=
      HasOperatorSupport.formalAdjoint K hK.isClosed Q A hQK hQA
    have haK : tsupport a ⊆ K :=
      tsupport_symbol_subset_of_hasOperatorSupport m a ha A hAact K hK.isClosed hAK
    have haSupp : HasCompactSupport a := hK.of_isClosed_subset (isClosed_tsupport a) haK
    -- Conjugate symmetry of the actual full Schwartz pairing identifies the second adjoint.
    have hAQ : IsSchwartzFormalAdjoint A Q := by
      intro u v
      simpa only [← integral_conj, inner_conj_symm] using
        (congrArg conj (hQA v u)).symm
    let B := localFormalAdjoint m a ha A hAact K hK hAK
    have hAB : IsSchwartzFormalAdjoint A B :=
      isSchwartzFormalAdjoint_localFormalAdjoint m a ha A hAact K hK hAK
    have hBQ : B = Q := (existsUnique_localFormalAdjoint m a ha A hAact K hK hAK).unique
      hAB hAQ
    have hsymbol : adjointSymbol χ a = q := by
      apply symbol_eq_of_quantize_eq m m _ _
        (isSymbol_adjointSymbol m a ha haSupp χ hχ hcχ) hq
      intro u x
      rw [← localFormalAdjoint_apply m a ha A hAact K hK hAK χ hχ hcχ hone,
        ← hQ]
      exact congrArg (fun T ↦ T u x) hBQ
    have h := hasSymbolExpansion_adjointSymbol m a ha haSupp χ hχ hcχ
      (fun x hx ↦ show x ∈ {y | χ y = 1} from interior_subset (hone (haK hx)))
    rwa [hsymbol] at h
  classical
  -- Now apply the exact amplitude expansion to the original operators and the same cutoff.
  have hpSupp : HasCompactSupport p := hK.of_isClosed_subset (isClosed_tsupport p)
    (tsupport_symbol_subset_of_hasOperatorSupport l p hp P hP K hK.isClosed hPK)
  have hqSupp : HasCompactSupport q := hK.of_isClosed_subset (isClosed_tsupport q)
    (tsupport_symbol_subset_of_hasOperatorSupport m q hq Q hQ K hK.isClosed hQK)
  let a := adjointSymbol χ q
  let b := symbolAdjoint a
  have ha : IsSymbol Set.univ m a := isSymbol_adjointSymbol m q hq hqSupp χ hχ hχSupp
  have hb : IsSymbol Set.univ m b := ha.symbolAdjoint isOpen_univ
  have haSupp : HasCompactSupport a :=
    hχSupp.of_isClosed_subset (isClosed_tsupport a) (tsupport_adjointSymbol_subset χ q)
  have hbSupp : HasCompactSupport b := by
    simpa only [b, HasCompactSupport, tsupport_symbolAdjoint] using haSupp
  have hexpand := hasSymbolExpansion_amplitudeSymbol (l + m) (leftRightAmplitude p b)
    (isAmplitude_leftRightAmplitude l m p b hp hb)
    (hasCompactSupport_leftRightAmplitude p b hpSupp hbSupp)
  have hqexpand := composition_right_symbol_expansion m q hq Q hQ K hK hQK
    χ hχ hχSupp hone
  let terms := adjointExpansionTerm a
  have hps : ContDiff ℝ ∞ (Function.uncurry p) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
  have hqs : ContDiff ℝ ∞ (Function.uncurry q) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using hq.1
  have hbs : ContDiff ℝ ∞ (Function.uncurry b) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using hb.1
  have hterms (k : ℕ) : ContDiff ℝ ∞ (Function.uncurry (terms k)) := by
    have hs := (hqexpand k).1.sub (hqexpand (k + 1)).1
    rw [Set.univ_prod_univ, contDiffOn_univ] at hs
    have heq : Function.uncurry (terms k) =
        (Function.uncurry (q - ∑ j ∈ Finset.range k, terms j)) -
          (Function.uncurry (q - ∑ j ∈ Finset.range (k + 1), terms j)) := by
      funext z
      simp only [Function.uncurry, Pi.sub_apply, Finset.sum_apply]
      rw [Finset.sum_range_succ]
      abel
    rw [heq]
    exact hs
  intro N
  -- Every omitted right-symbol remainder has order m-(N-i); its i-th coefficient has order l+m-N.
  let R := ∑ i ∈ Finset.range N,
    compositionExpansionTerm p (q - ∑ k ∈ Finset.range (N - i), terms k) i
  have hR : IsSymbol Set.univ (l + m - (N : ℝ)) R := by
    apply (symbolSpace Set.univ isOpen_univ (l + m - (N : ℝ)) r t).sum_mem
    intro i hi
    change IsSymbol Set.univ (l + m - (N : ℝ))
      (compositionExpansionTerm p (q - ∑ k ∈ Finset.range (N - i), terms k) i)
    have hiN : i ≤ N := Nat.le_of_lt (Finset.mem_range.mp hi)
    have h := isSymbol_compositionExpansionTerm l (m - ((N - i : ℕ) : ℝ))
      p (q - ∑ k ∈ Finset.range (N - i), terms k) hp (hqexpand (N - i)) i
    convert h using 1
    push_cast [Nat.cast_sub hiN]
    ring
  have hcoeff : ∑ j ∈ Finset.range N, amplitudeExpansionTerm (leftRightAmplitude p b) j =
      ∑ i ∈ Finset.range N,
        ∑ k ∈ Finset.range (N - i), compositionExpansionTerm p (terms k) i := by
    calc
      _ = ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1),
          compositionExpansionTerm p (terms (j - i)) i := by
        apply Finset.sum_congr rfl
        intro j _
        exact amplitudeExpansionTerm_leftRight p a hps hbs j
      _ = _ := triangular_sum (fun i k ↦ compositionExpansionTerm p (terms k) i) N
  -- Subtract the two finite expansions. Both remaining terms have the prescribed next order.
  have heq : compositionSymbol χ p q -
      ∑ i ∈ Finset.range N, compositionExpansionTerm p q i =
        (compositionSymbol χ p q -
          ∑ j ∈ Finset.range N, amplitudeExpansionTerm (leftRightAmplitude p b) j) - R := by
    dsimp only [R]
    simp_rw [compositionExpansionTerm_sub_sum p q terms hqs hterms]
    rw [Finset.sum_sub_distrib, hcoeff]
    abel
  rw [heq]
  exact (symbolSpace Set.univ isOpen_univ (l + m - (N : ℝ)) r t).sub_mem
    (hexpand N) hR

/-- The full composition symbol differs from the pointwise product by one lower order. -/
theorem isSymbol_compositionSymbol_sub (l m : ℝ)
    (p : SymbolFunction n s t) (q : SymbolFunction n r s)
    (hp : IsSymbol Set.univ l p) (hq : IsSymbol Set.univ m q)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin t)))
    (Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (hP : ∀ v x, P v x = quantize p v x) (hQ : ∀ u x, Q u x = quantize q u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hPK : HasOperatorSupport K P) (hQK : HasOperatorSupport K Q)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχSupp : HasCompactSupport χ) (hone : K ⊆ interior {x | χ x = 1}) :
    IsSymbol Set.univ (l + m - 1) (compositionSymbol χ p q - symbolComp p q) := by
  /- Reduce the actual left-right amplitude through degree zero. Its diagonal
  value is p times the pointwise adjoint of the reduced adjoint symbol of q.
  The adjoint remainder replaces that second factor by q modulo order m-1.
  This proves the leading composition formula without using the higher-order
  regrouping in the full composition expansion. -/
  have hpSupp : HasCompactSupport p := hK.of_isClosed_subset (isClosed_tsupport p)
    (tsupport_symbol_subset_of_hasOperatorSupport l p hp P hP K hK.isClosed hPK)
  have hqK : tsupport q ⊆ K :=
    tsupport_symbol_subset_of_hasOperatorSupport m q hq Q hQ K hK.isClosed hQK
  have hqSupp : HasCompactSupport q :=
    hK.of_isClosed_subset (isClosed_tsupport q) hqK
  let b := symbolAdjoint (adjointSymbol χ q)
  have hb : IsSymbol Set.univ m b :=
    (isSymbol_adjointSymbol m q hq hqSupp χ hχ hχSupp).symbolAdjoint isOpen_univ
  have hbSupp : HasCompactSupport b := by
    have haSupp : HasCompactSupport (adjointSymbol χ q) :=
      hχSupp.of_isClosed_subset (isClosed_tsupport _) (tsupport_adjointSymbol_subset χ q)
    simpa only [b, HasCompactSupport, tsupport_symbolAdjoint] using haSupp
  -- The N=1 amplitude remainder compares with its actual diagonal matrix product.
  have hzero : amplitudeExpansionTerm (leftRightAmplitude p b) 0 = symbolComp p b := by
    funext x ξ
    simp [amplitudeExpansionTerm, leftRightAmplitude, symbolComp, iteratedFDeriv_zero_apply]
  have hreduce : IsSymbol Set.univ (l + m - 1)
      (compositionSymbol χ p q - symbolComp p b) := by
    change IsSymbol Set.univ (l + m - 1)
      (amplitudeSymbol (leftRightAmplitude p b) - symbolComp p b)
    have h := hasSymbolExpansion_amplitudeSymbol (l + m) (leftRightAmplitude p b)
      (isAmplitude_leftRightAmplitude l m p b hp hb)
      (hasCompactSupport_leftRightAmplitude p b hpSupp hbSupp) 1
    simpa only [Finset.sum_range_one, Nat.cast_one, hzero] using h
  -- Pointwise adjunction is real linear and involutive on the original rectangular matrices.
  have hbq : IsSymbol Set.univ (m - 1) (b - q) := by
    have h := (isSymbol_adjointSymbol_sub m q hq hqSupp χ hχ hχSupp
      (fun x hx ↦ show x ∈ {y | χ y = 1} from
        interior_subset (hone (hqK hx)))).symbolAdjoint isOpen_univ
    have heq : symbolAdjoint (adjointSymbol χ q - symbolAdjoint q) = b - q := by
      funext x ξ
      simp [symbolAdjoint, b]
    rwa [heq] at h
  have hproduct : IsSymbol Set.univ (l + m - 1) (symbolComp p (b - q)) := by
    have horder : l + (m - 1) = l + m - 1 := by ring
    simpa only [horder] using hp.symbolComp isOpen_univ hbq
  have heq : compositionSymbol χ p q - symbolComp p q =
      (compositionSymbol χ p q - symbolComp p b) + symbolComp p (b - q) := by
    funext x ξ
    simp only [Pi.sub_apply, Pi.add_apply, symbolComp, ContinuousLinearMap.comp_sub]
    abel
  rw [heq]
  exact hreduce.add isOpen_univ hproduct

/-- Any two admissible cutoffs produce the same full composition symbol, exactly. -/
theorem compositionSymbol_eq (l m : ℝ)
    (p : SymbolFunction n s t) (q : SymbolFunction n r s)
    (hp : IsSymbol Set.univ l p) (hq : IsSymbol Set.univ m q)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin t)))
    (Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (hP : ∀ v x, P v x = quantize p v x) (hQ : ∀ u x, Q u x = quantize q u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hPK : HasOperatorSupport K P) (hQK : HasOperatorSupport K Q)
    (χ ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχSupp : HasCompactSupport χ) (hψSupp : HasCompactSupport ψ)
    (hχone : K ⊆ interior {x | χ x = 1}) (hψone : K ⊆ interior {x | ψ x = 1}) :
    compositionSymbol χ p q = compositionSymbol ψ p q := by
  /- Both reduced symbols have order l+m and quantize to P(Q u) at every x for
  every Schwartz input u. Apply uniqueness of the full left symbol. This argument
  gives equality as functions, including smoothing terms; equality of principal
  classes alone would not establish independence of the exact construction. -/
  have hpSupp : HasCompactSupport p := hK.of_isClosed_subset (isClosed_tsupport p)
    (tsupport_symbol_subset_of_hasOperatorSupport l p hp P hP K hK.isClosed hPK)
  have hqSupp : HasCompactSupport q := hK.of_isClosed_subset (isClosed_tsupport q)
    (tsupport_symbol_subset_of_hasOperatorSupport m q hq Q hQ K hK.isClosed hQK)
  -- Both original cutoff formulas give full left symbols of the very same composition.
  apply symbol_eq_of_quantize_eq (l + m) (l + m) _ _
    (isSymbol_compositionSymbol l m p q hp hq hpSupp hqSupp χ hχ hχSupp)
    (isSymbol_compositionSymbol l m p q hp hq hpSupp hqSupp ψ hψ hψSupp)
  intro u x
  rw [quantize_compositionSymbol l m p q hp hq P Q hP hQ K hK hPK hQK χ hχ hχSupp hχone,
    quantize_compositionSymbol l m p q hp hq P Q hP hQ K hK hPK hQK ψ hψ hψSupp hψone]

/-- The principal class of an actual operator composition equals the quotient matrix product. -/
theorem principalSymbolClass_eq_comp (l m : ℝ)
    (p : symbolSpace Set.univ isOpen_univ l s t)
    (q : symbolSpace Set.univ isOpen_univ m r s)
    (c : symbolSpace Set.univ isOpen_univ (l + m) r t)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin t)))
    (Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (hP : ∀ v x, P v x = quantize p.val v x)
    (hQ : ∀ u x, Q u x = quantize q.val u x)
    (hc : ∀ u x, quantize c.val u x = P (Q u) x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hPK : HasOperatorSupport K P) (hQK : HasOperatorSupport K Q) :
    principalSymbolClass Set.univ isOpen_univ (l + m) r t c =
      principalSymbolComp isOpen_univ
        (principalSymbolClass Set.univ isOpen_univ l s t p)
        (principalSymbolClass Set.univ isOpen_univ m r s q) := by
  /- Stage 1: choose a real smooth compact cutoff equal to one near K, which is
  possible for every compact Euclidean K. Exact symbol uniqueness identifies c
  with compositionSymbol χ p q. Stage 2: its difference from symbolComp p q has
  order l+m-1, hence the two symbols have the same class in the actual quotient.
  Stage 3: the already defined principalSymbolComp sends the classes of p,q to
  the class of their ordered pointwise product. This bridges the earlier algebraic
  quotient construction to actual operator composition, without assuming homogeneity. -/
  -- Select one compact cutoff, retaining the actual common operator support.
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    { rIn := max R 0 + 1
      rOut := max R 0 + 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hone : K ⊆ interior {x | χ x = 1} := by
    intro x hx
    have hxball : x ∈ Metric.ball 0 χ.rIn := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (hR x hx).trans_lt (lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one)
    exact mem_interior_iff_mem_nhds.mpr (χ.eventuallyEq_one_of_mem_ball hxball)
  have hpSupp : HasCompactSupport p.val := hK.of_isClosed_subset (isClosed_tsupport p.val)
    (tsupport_symbol_subset_of_hasOperatorSupport l p.val p.property P hP K hK.isClosed hPK)
  have hqSupp : HasCompactSupport q.val := hK.of_isClosed_subset (isClosed_tsupport q.val)
    (tsupport_symbol_subset_of_hasOperatorSupport m q.val q.property Q hQ K hK.isClosed hQK)
  -- Uniqueness of the full left symbol identifies the given c with this exact composition.
  have hsymbol : c.val = compositionSymbol χ p.val q.val := by
    apply symbol_eq_of_quantize_eq (l + m) (l + m) _ _ c.property
      (isSymbol_compositionSymbol l m p.val q.val p.property q.property
        hpSupp hqSupp χ χ.contDiff χ.hasCompactSupport)
    intro u x
    rw [hc, quantize_compositionSymbol l m p.val q.val p.property q.property
      P Q hP hQ K hK hPK hQK χ χ.contDiff χ.hasCompactSupport hone]
  -- The one-order remainder is exactly the denominator of the original principal quotient.
  rw [principalSymbolComp_class]
  apply (principalSymbolClass_eq_iff isOpen_univ c (symbolSpaceComp isOpen_univ p q)).mpr
  change IsSymbol Set.univ (l + m - 1) (c.val - symbolComp p.val q.val)
  rw [hsymbol]
  exact isSymbol_compositionSymbol_sub l m p.val q.val p.property q.property
    P Q hP hQ K hK hPK hQK χ χ.contDiff χ.hasCompactSupport hone

end AtiyahSinger
