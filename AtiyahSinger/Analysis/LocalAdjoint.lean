/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.TwoSidedCutoff
public import Mathlib.Analysis.InnerProductSpace.Adjoint

import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Local Hermitian adjoints and their symbols

Public module ID: M0783.

SG Theorem 3.11, (3.11)-(3.14), proved before composition in the book.
The formal adjoint uses Lebesgue measure and standard Hermitian fibers. It is an
operator on Schwartz functions, not a bounded adjoint on L² for arbitrary order.
The amplitude is χ(x)p(y,ξ)†. There is no frequency reflection or parity factor.
With ordinary derivatives the expansion coefficient is (-i)^j/j!, summed over
ordered coordinate lists. SG instead uses i^|α| times the conjugate transpose of
D_ξ^α D_x^α p, with D=-i∂; these conventions agree.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 15

variable {n r q : ℕ}

/-- Pointwise Hermitian matrix adjoint, reversing the input and output ranks. -/
def symbolAdjoint (p : SymbolFunction n r q) : SymbolFunction n q r :=
  fun x ξ ↦ (p x ξ).adjoint

/-- SG (3.14), after renaming the output variable x and input variable y. -/
def adjointAmplitude (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n r q) : AmplitudeFunction n q r :=
  fun x y ξ ↦ χ x • (p y ξ).adjoint

/-- The exact reduced symbol of the cutoff right-symbol formula for the adjoint. -/
def adjointSymbol (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n r q) : SymbolFunction n q r :=
  amplitudeSymbol (adjointAmplitude χ p)

/-- Degree-j ordinary-derivative form of SG (3.12), including the conjugate transpose. -/
def adjointExpansionTerm (p : SymbolFunction n r q) (j : ℕ) : SymbolFunction n q r :=
  fun x ξ ↦ ((-Complex.I) ^ j / (j.factorial : ℂ)) •
    ∑ α : Fin j → Fin n,
      iteratedFDeriv ℝ j
        (fun η ↦ iteratedFDeriv ℝ j (fun y ↦ symbolAdjoint p y η) x) ξ
        (fun t ↦ EuclideanSpace.single (α t) 1)
        (fun t ↦ EuclideanSpace.single (α t) 1)

/-- Formal adjoint identity on all Schwartz inputs, with the actual Lebesgue L² pairing. -/
def IsSchwartzFormalAdjoint
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) : Prop :=
  ∀ u v, (∫ x, inner ℂ (P u x) (v x)) = ∫ x, inner ℂ (u x) (Q v x)

set_option maxHeartbeats 800000 in

/-- Conjugate transpose is real linear and isometric, so it preserves amplitude estimates. -/
theorem isAmplitude_adjointAmplitude (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) : IsAmplitude m (adjointAmplitude χ p) := by
  /- Regard the matrix adjoint as a continuous real-linear isometry. It commutes
  with real derivatives and preserves their norms. Apply the product rule to χ(x)
  and p(y,ξ)† on a compact spatial pair set; only frequency derivatives change the
  symbol order. No holomorphic smoothness of the conjugate transpose is asserted. -/
  let P := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let H' := EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)
  let J : H ≃ₗᵢ[ℝ] H' := {
    toEquiv := (ContinuousLinearMap.adjoint : H ≃ₗᵢ⋆[ℂ] H').toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by
      intro c A
      change (c • A).adjoint = c • A.adjoint
      rw [← Complex.coe_smul c A, map_smulₛₗ]
      simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  have hps : ContDiff ℝ ∞ (Function.uncurry p) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
  -- Real matrix adjoint commutes with derivatives and preserves their norms.
  have hs : ContDiff ℝ ∞ (Function.uncurry (symbolAdjoint p)) := J.contDiff.comp hps
  have hsp : IsSymbol Set.univ m (symbolAdjoint p) := by
    refine ⟨by simpa only [Set.univ_prod_univ] using hs.contDiffOn, ?_⟩
    intro K hK hcompact i j
    obtain ⟨C, hC, hbound⟩ := hp.2 K hK hcompact i j
    refine ⟨C, hC, ?_⟩
    intro x hx ξ
    let Jj : (P [×j]→L[ℝ] H) ≃ₗᵢ[ℝ] (P [×j]→L[ℝ] H') := {
      toLinearEquiv := (J.toContinuousLinearEquiv.continuousMultilinearMapCongrRight
        (fun _ : Fin j ↦ P)).toLinearEquiv
      norm_map' := fun f ↦ J.toLinearIsometry.norm_compContinuousMultilinearMap f }
    have heq : (fun y ↦ iteratedFDeriv ℝ j (symbolAdjoint p y) ξ) =
        Jj ∘ (fun y ↦ iteratedFDeriv ℝ j (p y) ξ) := by
      funext y
      exact J.toContinuousLinearEquiv.iteratedFDeriv_comp_left
    change ‖iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (symbolAdjoint p y) ξ) x‖ ≤ _
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hbound x hx ξ
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
    (hs.comp (contDiff_fst.snd.prodMk contDiff_snd)), ?_⟩
  intro K hK i j k
  obtain ⟨C, hC⟩ := ((hK.image continuous_fst).image
    (hχ.continuous_iteratedFDeriv (m := i) (by simp)).norm).bddAbove
  obtain ⟨D, hD, hd⟩ := hsp.2 (Prod.snd '' K) (Set.subset_univ _)
    (hK.image continuous_snd) j k
  refine ⟨max C 0 * D, mul_nonneg (le_max_right _ _) hD, ?_⟩
  intro x y hxy ξ
  -- The three derivatives separate: frequency and input position hit p, output position hits χ.
  let d (w : P) := iteratedFDeriv ℝ k (symbolAdjoint p w) ξ
  have hfreq (z w : P) :
      iteratedFDeriv ℝ k (adjointAmplitude χ p z w) ξ = χ z • d w := by
    exact iteratedFDeriv_const_smul_apply'
      ((hs.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
  have hdSmooth : ContDiff ℝ ∞ d :=
    (parametric (symbolAdjoint p) hs k).comp (contDiff_id.prodMk contDiff_const)
  have heq : amplitudeDerivative (adjointAmplitude χ p) i j k x y ξ =
      (iteratedFDeriv ℝ i χ x).smulRight (symbolDerivative (symbolAdjoint p) j k y ξ) := by
    unfold amplitudeDerivative
    simp only [hfreq]
    have hy (z : P) : iteratedFDeriv ℝ j (fun w ↦ χ z • d w) y =
        χ z • iteratedFDeriv ℝ j d y :=
      iteratedFDeriv_const_smul_apply' (hdSmooth.contDiffAt.of_le (by simp))
    rw [show (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ χ z • d w) y) =
      (fun z ↦ χ z • iteratedFDeriv ℝ j d y) from funext hy]
    exact iteratedFDeriv_smul_const_apply (hχ.contDiffAt.of_le (by simp))
  rw [heq]
  calc
    _ ≤ ‖iteratedFDeriv ℝ i χ x‖ * ‖symbolDerivative (symbolAdjoint p) j k y ξ‖ :=
      (ContinuousMultilinearMap.norm_smulRight _ _).le
    _ ≤ max C 0 * (D * (1 + ‖ξ‖) ^ (m - (k : ℝ))) := by
      exact mul_le_mul ((hC ⟨x, ⟨(x, y), hxy, rfl⟩, rfl⟩).trans (le_max_left _ _))
        (hd y ⟨(x, y), hxy, rfl⟩ ξ) (norm_nonneg _) (le_max_right _ _)
    _ = _ := by ring

/-- Compact x support of p becomes compact input support for the adjoint amplitude. -/
theorem hasCompactSupport_adjointAmplitude (p : SymbolFunction n r q)
    (hp : HasCompactSupport p) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : HasCompactSupport χ) :
    HasCompactSupport (Function.uncurry (adjointAmplitude χ p)) := by
  /- The amplitude vanishes outside tsupport χ times tsupport p. The adjoint of
  the zero matrix is zero, and both supports are uniform in frequency. Their
  product is compact, hence contains the closed support of the full amplitude. -/
  -- A nonzero amplitude requires both original spatial factors to be nonzero.
  apply (hχ.prod hp).of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ ((isClosed_tsupport χ).prod (isClosed_tsupport p))
  intro z hz
  constructor
  · by_contra hχz
    apply hz
    funext ξ
    simp [Function.uncurry, adjointAmplitude, image_eq_zero_of_notMem_tsupport hχz]
  · by_contra hpz
    have hpzero : p z.2 = 0 := image_eq_zero_of_notMem_tsupport hpz
    apply hz
    funext ξ
    simp [Function.uncurry, adjointAmplitude, hpzero]

/-- The cutoff right-symbol formula reduces to a left symbol of the same order. -/
theorem isSymbol_adjointSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hsupp : HasCompactSupport p)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupp : HasCompactSupport χ) : IsSymbol Set.univ m (adjointSymbol χ p) := by
  /- Combine the adjoint amplitude estimates with its uniform compact spatial
  support, then apply the Workhorse Theorem 3.5. At this stage χ is any compact
  smooth cutoff; identifying the resulting operator as P's adjoint needs the
  separate operator support and cutoff-equals-one hypotheses below. -/
  exact isSymbol_amplitudeSymbol m _ (isAmplitude_adjointAmplitude m p hp χ hχ)
    (hasCompactSupport_adjointAmplitude p hsupp χ hχsupp)

/-- SG (3.12): a cutoff equal to one on the symbol support disappears from every coefficient. -/
theorem hasSymbolExpansion_adjointSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hsupp : HasCompactSupport p)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupp : HasCompactSupport χ) (hone : ∀ x ∈ tsupport p, χ x = 1) :
    HasSymbolExpansion Set.univ (fun j ↦ m - (j : ℝ))
      (adjointSymbol χ p) (adjointExpansionTerm p) := by
  /- Stage 1: apply the amplitude expansion to χ(x)p(y,ξ)†, differentiating in
  y and ξ before restricting y=x. Thus χ is never differentiated. Stage 2: outside
  tsupport p all derivatives of p vanish, while on that support χ is one. Remove
  χ from every coefficient. The ordered-list factor 1/j! equals 1/α! after grouping;
  the Taylor remainder has order m-N for every N, including N=0. -/
  -- On the symbol support χ is one. Outside it, the original symbol
  -- vanishes on a neighborhood, so all its spatial derivatives vanish there.
  have hinner (j : ℕ) (x η : EuclideanSpace ℝ (Fin n)) :
      iteratedFDeriv ℝ j (fun y ↦ adjointAmplitude χ p x y η) x =
        iteratedFDeriv ℝ j (fun y ↦ symbolAdjoint p y η) x := by
    have heq : (fun y ↦ adjointAmplitude χ p x y η) =ᶠ[nhds x]
        (fun y ↦ symbolAdjoint p y η) := by
      by_cases hx : x ∈ tsupport p
      · filter_upwards with y
        simp [adjointAmplitude, symbolAdjoint, hone x hx]
      · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
        filter_upwards [hz] with y hy
        have hpy : p y η = 0 := congrFun hy η
        simp [adjointAmplitude, symbolAdjoint, hpy]
    exact (heq.iteratedFDeriv ℝ j).eq_of_nhds
  have hterms : amplitudeExpansionTerm (adjointAmplitude χ p) = adjointExpansionTerm p := by
    funext j x ξ
    simp only [amplitudeExpansionTerm, adjointExpansionTerm, hinner]
  -- The full amplitude expansion now has exactly the prescribed coefficients.
  have h := hasSymbolExpansion_amplitudeSymbol m (adjointAmplitude χ p)
    (isAmplitude_adjointAmplitude m p hp χ hχ)
    (hasCompactSupport_adjointAmplitude p hsupp χ hχsupp)
  rwa [hterms] at h

/-- The leading adjoint symbol is the Hermitian adjoint of p modulo one lower order. -/
theorem isSymbol_adjointSymbol_sub (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hsupp : HasCompactSupport p)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupp : HasCompactSupport χ) (hone : ∀ x ∈ tsupport p, χ x = 1) :
    IsSymbol Set.univ (m - 1) (adjointSymbol χ p - symbolAdjoint p) := by
  /- Take the N=1 remainder in the full expansion. Its only retained term is
  degree zero, for which the two zeroth derivatives evaluate p† and the scalar
  coefficient is one. In particular there is no factor (-1)^m, unlike the
  bilinear transpose of a homogeneous differential symbol. The order m is real. -/
  have hterm : adjointExpansionTerm p 0 = symbolAdjoint p := by
    funext x ξ
    simp [adjointExpansionTerm, iteratedFDeriv_zero_apply]
  -- Retain exactly the degree-zero term of the original full expansion.
  have h := hasSymbolExpansion_adjointSymbol m p hp hsupp χ hχ hχsupp hone 1
  simpa only [Finset.sum_range_one, Nat.cast_one, hterm] using h

/-- Output support of an exactly quantized operator forces uniform x support of its symbol. -/
theorem tsupport_symbol_subset_of_hasOperatorSupport (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (hP : ∀ u x, P u x = quantize p u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K)
    (hPK : HasOperatorSupport K P) : tsupport p ⊆ K := by
  /- Fix x outside K. The output support condition makes quantize p u x zero
  for every Schwartz u. The Fourier transform is onto the Schwartz space;
  testing each matrix entry against arbitrary compact smooth frequency tests
  forces the smooth polynomially bounded function exp(i<x,ξ>)p(x,ξ) to vanish.
  Thus p(x,ξ)=0 for all ξ. Closedness of K also contains the closure of the support. -/
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
  apply closure_minimal ?_ hK
  intro x hx
  by_contra hxK
  have hzero (u : 𝓢(V, EuclideanSpace ℂ (Fin r))) : quantize p u x = 0 := by
    rw [← hP]
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hxK (hPK.1 u h))
  -- Real compact smooth tests separate the continuous matrix column at this fixed x.
  have hcolumn (v : EuclideanSpace ℂ (Fin r)) :
      ∀ ξ : V, p x ξ v = 0 := by
    let f (ξ : V) := Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • p x ξ v
    have hpcont : Continuous (fun ξ : V ↦ p x ξ) := by
      have h := hp.1.continuousOn
      rw [Set.univ_prod_univ] at h
      exact (continuousOn_univ.mp h).comp (continuous_const.prodMk continuous_id)
    have hphase : Continuous (fun ξ : V ↦
        Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) := by fun_prop
    have hcont : Continuous f := hphase.smul (hpcont.clm_apply continuous_const)
    have hae : ∀ᵐ ξ, f ξ = 0 := by
      apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hcont.locallyIntegrable
      intro φ hφ hcφ
      have hc : HasCompactSupport (fun ξ : V ↦ φ ξ • v) := hcφ.smul_right
      let ψ := hc.toSchwartzMap (hφ.smul contDiff_const)
      obtain ⟨u, hu⟩ := hfourier ψ
      have hz := hzero u
      change ((2 * Real.pi) ^ n)⁻¹ •
        (∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • p x ξ (fourierSG u ξ)) = 0 at hz
      have hi := (smul_eq_zero.mp hz).resolve_left (inv_ne_zero (pow_ne_zero _ hπ))
      rw [hu] at hi
      convert hi using 1
      congr 1
      funext ξ
      change φ ξ • (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • p x ξ v) =
        Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • p x ξ (φ ξ • v)
      rw [(p x ξ).map_smul_of_tower, smul_comm]
    have heq : f = 0 := Measure.eq_of_ae_eq hae hcont continuous_const
    intro ξ
    have h := congrFun heq ξ
    exact (smul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)
  apply hx
  funext ξ
  apply ContinuousLinearMap.ext
  intro v
  exact hcolumn v ξ

set_option maxSynthPendingDepth 20 in
set_option maxHeartbeats 1000000 in

/-- SG 3.11: a compactly supported local PDO has a unique continuous Schwartz formal adjoint. -/
theorem existsUnique_localFormalAdjoint (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (hP : ∀ u x, P u x = quantize p u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hPK : HasOperatorSupport K P) :
    ∃! Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
      IsSchwartzFormalAdjoint P Q := by
  /- Stage 1: recover tsupport p ⊆ K and choose a real smooth compact cutoff χ
  equal to one near K. The amplitude χ(x)p(y,ξ)† defines Q by SG 3.5.
  Stage 2: compact spatial support and Schwartz decay give a product of L¹
  bounds for the first double pairing. The amplitude integrability estimate
  controls the inner transform in the reverse pairing; a second L¹ product
  bound permits Fubini there. Fourier inversion identifies the two pairings,
  and the input support condition gives P(χu)=Pu.
  Stage 3: compact scalar tests in each fiber coordinate separate the outputs
  of any two formal adjoints. Their continuity upgrades the almost-everywhere
  equality to equality everywhere, proving uniqueness on Schwartz inputs. -/
  let V := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  have hpSupp : HasCompactSupport p :=
    hK.of_isClosed_subset (isClosed_tsupport p)
      (tsupport_symbol_subset_of_hasOperatorSupport m p hp P hP K hK.isClosed hPK)
  -- Two products of L1 bounds directly justify the integrated adjoint identity.
  have pairing (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))) :
      (∫ y, inner ℂ (quantize p u y) (v y)) = ((2 * Real.pi) ^ n)⁻¹ •
        ∫ ξ, inner ℂ (fourierSG u ξ)
          (∫ y, Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • (p y ξ).adjoint (v y)) := by
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let phase (y ξ : V) := Complex.exp (Complex.I * (inner ℝ y ξ : ℂ))
    have hphase (y ξ : V) : ‖phase y ξ‖ = 1 := by
      simp [phase, Complex.norm_exp, Complex.mul_re]
    have hpCont : Continuous (Function.uncurry p) := by
      simpa only [Set.univ_prod_univ, continuousOn_univ] using hp.1.continuousOn
    obtain ⟨C, hC, hbound⟩ := hp.2 (tsupport p) (Set.subset_univ _) hpSupp 0 0
    have hpnorm (y ξ : V) : ‖p y ξ‖ ≤ C * (1 + ‖ξ‖) ^ m := by
      by_cases hy : y ∈ tsupport p
      · simpa only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero]
          using hbound y hy ξ
      · have hz : p y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp only [hz, Pi.zero_apply, norm_zero]
        positivity
    -- A smooth polynomial weight bounds the order-m growth against this same Fourier input.
    obtain ⟨d, hd⟩ := exists_nat_ge m
    have hpi : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let e : V ≃L[ℝ] V :=
      (LinearEquiv.smulOfNeZero ℝ V ((2 * Real.pi)⁻¹) hpi).toContinuousLinearEquiv
    let fu : 𝓢(V, E) :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (FourierTransform.fourier u)
    have hfu (ξ : V) : fu ξ = fourierSG u ξ := rfl
    let weight (ξ : V) : ℂ := ((1 + ‖ξ‖ ^ 2) ^ d : ℝ)
    have hw : weight.HasTemperateGrowth := by dsimp [weight]; fun_prop
    let wu : 𝓢(V, E) := SchwartzMap.smulLeftCLM E weight fu
    have hwu (ξ : V) : ‖wu ξ‖ = (1 + ‖ξ‖ ^ 2) ^ d * ‖fourierSG u ξ‖ := by
      rw [show wu ξ = weight ξ • fu ξ from SchwartzMap.smulLeftCLM_apply_apply hw _ _,
        norm_smul, hfu]
      dsimp [weight]
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hweight (ξ : V) : (1 + ‖ξ‖) ^ m ≤ (2 : ℝ) ^ d * (1 + ‖ξ‖ ^ 2) ^ d := by
      have hbase : 1 + ‖ξ‖ ≤ 2 * (1 + ‖ξ‖ ^ 2) := by
        nlinarith [sq_nonneg (‖ξ‖ - 1)]
      calc
        _ ≤ (1 + ‖ξ‖) ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) hd
        _ = (1 + ‖ξ‖) ^ d := Real.rpow_natCast _ _
        _ ≤ (2 * (1 + ‖ξ‖ ^ 2)) ^ d := pow_le_pow_left₀ (by positivity) hbase d
        _ = _ := mul_pow _ _ _
    let D : ℝ := C * (2 : ℝ) ^ d
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hprod (y ξ : V) : ‖p y ξ‖ * ‖fourierSG u ξ‖ ≤ D * ‖wu ξ‖ := by
      calc
        _ ≤ (C * (1 + ‖ξ‖) ^ m) * ‖fourierSG u ξ‖ :=
          mul_le_mul_of_nonneg_right (hpnorm y ξ) (norm_nonneg _)
        _ ≤ (C * ((2 : ℝ) ^ d * (1 + ‖ξ‖ ^ 2) ^ d)) * ‖fourierSG u ξ‖ := by
          gcongr
          exact hweight ξ
        _ = _ := by rw [hwu]; dsimp [D]; ring
    let g (y ξ : V) := phase y ξ • p y ξ (fourierSG u ξ)
    have hg (y ξ : V) : ‖g y ξ‖ ≤ D * ‖wu ξ‖ := by
      dsimp only [g]
      rw [norm_smul, hphase, one_mul]
      exact ((p y ξ).le_opNorm _).trans (hprod y ξ)
    have hgcont : Continuous (Function.uncurry g) := by
      have hph : Continuous (Function.uncurry phase) := by dsimp [phase]; fun_prop
      exact hph.smul (hpCont.clm_apply (fu.continuous.comp continuous_snd))
    have hgint (y : V) : Integrable (g y) :=
      (wu.integrable.norm.const_mul D).mono'
        ((hgcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
        (Filter.Eventually.of_forall (hg y))
    -- The double pairing is bounded by the product of two genuine L1 functions.
    let H (y ξ : V) := inner ℂ (g y ξ) (v y)
    have hHcont : Continuous (Function.uncurry H) :=
      hgcont.inner (v.continuous.comp continuous_fst)
    have hHint : Integrable (Function.uncurry H) := by
      apply ((v.integrable.norm.mul_prod wu.integrable.norm).const_mul D).mono'
        hHcont.aestronglyMeasurable
      filter_upwards with z
      calc
        ‖H z.1 z.2‖ ≤ ‖g z.1 z.2‖ * ‖v z.1‖ := norm_inner_le_norm _ _
        _ ≤ (D * ‖wu z.2‖) * ‖v z.1‖ :=
          mul_le_mul_of_nonneg_right (hg z.1 z.2) (norm_nonneg _)
        _ = D * (‖v z.1‖ * ‖wu z.2‖) := by ring
    have hIntegral {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
        [CompleteSpace F] (f : V → F) (hf : Integrable f) (z : F) :
        inner ℂ (∫ x, f x) z = ∫ x, inner ℂ (f x) z := by
      simpa only [← integral_conj, inner_conj_symm] using
        (congrArg (starRingEnd ℂ) (integral_inner (𝕜 := ℂ) hf z)).symm
    have hpoint (ξ : V) : (∫ y, H y ξ) = inner ℂ (fourierSG u ξ)
        (∫ y, Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • (p y ξ).adjoint (v y)) := by
      let f (y : V) := Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) •
        (p y ξ).adjoint (v y)
      have hfcont : Continuous f := by
        have hpc : Continuous (fun y ↦ p y ξ) :=
          hpCont.comp (continuous_id.prodMk continuous_const)
        have hph : Continuous (fun y ↦ Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ))) := by
          fun_prop
        exact hph.smul ((ContinuousLinearMap.adjoint.continuous.comp hpc).clm_apply v.continuous)
      have hfint : Integrable f := by
        apply hfcont.integrable_of_hasCompactSupport
        apply hpSupp.of_isClosed_subset (isClosed_tsupport _)
        apply closure_minimal ?_ (isClosed_tsupport p)
        intro y hy
        by_contra h
        have hz : p y = 0 := image_eq_zero_of_notMem_tsupport h
        exact hy (by simp [f, hz])
      rw [← integral_inner hfint]
      apply integral_congr_ae
      filter_upwards with y
      change inner ℂ (phase y ξ • p y ξ (fourierSG u ξ)) (v y) =
        inner ℂ (fourierSG u ξ) (Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) •
          (p y ξ).adjoint (v y))
      rw [inner_smul_left, inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
      congr 1
      dsimp [phase]
      rw [← Complex.exp_conj]
      congr 1
      simp
    calc
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ y, ∫ ξ, H y ξ := by
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards with y
        change inner ℂ (((2 * Real.pi) ^ n)⁻¹ • ∫ ξ, g y ξ) (v y) = _
        rw [inner_smul_left_eq_smul, hIntegral (g y) (hgint y)]
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ ξ, ∫ y, H y ξ := by
        rw [integral_integral_swap hHint]
      _ = _ := by
        simp_rw [hpoint]
        rfl
  have ampPairing (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
      (hcχ : HasCompactSupport χ) (hχ0 : χ 0 = 1)
      (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))) :
      (∫ y, inner ℂ (quantize p
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (χ x : ℂ)) u) y) (v y)) =
        ∫ x, inner ℂ (u x) (amplitudeApply (adjointAmplitude χ p) v x) := by
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let phase (x ξ : V) := Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))
    let R (ξ : V) := ∫ y,
      Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • (p y ξ).adjoint (v y)
    let w := SchwartzMap.smulLeftCLM E (fun x ↦ (χ x : ℂ)) u
    have hχgrowth : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
      (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hχ)
    have hw (x : V) : w x = χ x • u x := by
      simpa only [Complex.coe_smul] using
        SchwartzMap.smulLeftCLM_apply_apply hχgrowth u x
    -- The dependence on x is exactly a fixed scalar phase and the selected real cutoff.
    have hfactor (x ξ : V) :
        (∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
          adjointAmplitude χ p x y ξ (v y)) = χ x • (phase x ξ • R ξ) := by
      dsimp only [R]
      rw [← integral_smul, ← integral_smul]
      apply integral_congr_ae
      filter_upwards with y
      have hphase : Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) =
          phase x ξ * Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) := by
        dsimp [phase]
        rw [← Complex.exp_add, inner_sub_left]
        congr 1
        push_cast
        ring
      simp only [adjointAmplitude, smul_apply, hphase, ← Complex.coe_smul, smul_smul]
      congr 1
      ring
    have hRint : Integrable R := by
      have h := integrable_amplitudeApply_outer m (adjointAmplitude χ p)
        (isAmplitude_adjointAmplitude m p hp χ hχ)
        (hasCompactSupport_adjointAmplitude p hpSupp χ hcχ) v 0
      change Integrable (fun ξ : V ↦ ∫ y : V,
        Complex.exp (Complex.I * (inner ℝ (0 - y) ξ : ℂ)) •
          adjointAmplitude χ p 0 y ξ (v y)) at h
      simpa only [hfactor, hχ0, phase, inner_zero_left, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, one_smul] using h
    have hamp (x : V) : amplitudeApply (adjointAmplitude χ p) v x =
        ((2 * Real.pi) ^ n)⁻¹ • (χ x • ∫ ξ, phase x ξ • R ξ) := by
      change ((2 * Real.pi) ^ n)⁻¹ • (∫ ξ : V, ∫ y : V,
        Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
          adjointAmplitude χ p x y ξ (v y)) = _
      simp_rw [hfactor]
      rw [integral_smul]
    -- Products of the two L1 norms justify the actual spatial-frequency swap.
    let G (x ξ : V) := inner ℂ (w x) (phase x ξ • R ξ)
    have hphaseCont : Continuous (Function.uncurry phase) := by dsimp [phase]; fun_prop
    have hphaseNorm (x ξ : V) : ‖phase x ξ‖ = 1 := by
      simp [phase, Complex.norm_exp, Complex.mul_re]
    have hGmeas : AEStronglyMeasurable (Function.uncurry G) :=
      w.continuous.aestronglyMeasurable.comp_fst.inner
        (hphaseCont.aestronglyMeasurable.smul hRint.aestronglyMeasurable.comp_snd)
    have hGint : Integrable (Function.uncurry G) := by
      apply (w.integrable.norm.mul_prod hRint.norm).mono' hGmeas
      filter_upwards with z
      exact (norm_inner_le_norm _ _).trans_eq
        (by rw [norm_smul, hphaseNorm, one_mul])
    have hphaseInt (x : V) : Integrable (fun ξ ↦ phase x ξ • R ξ) := by
      apply hRint.norm.mono'
        ((hphaseCont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.smul
          hRint.aestronglyMeasurable)
      filter_upwards with ξ
      change ‖phase x ξ • R ξ‖ ≤ ‖R ξ‖
      rw [norm_smul, hphaseNorm, one_mul]
    have hfourier (ξ : V) : fourierSG w ξ =
        ∫ x, Complex.exp (-Complex.I * (inner ℝ x ξ : ℂ)) • w x := by
      unfold fourierSG
      rw [SchwartzMap.fourier_coe, Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with x
      congr 2
      rw [inner_smul_right]
      push_cast
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
    have hpoint (ξ : V) : (∫ x, G x ξ) = inner ℂ (fourierSG w ξ) (R ξ) := by
      have hfint : Integrable (fun x ↦
          Complex.exp (-Complex.I * (inner ℝ x ξ : ℂ)) • w x) := by
        have hcont : Continuous (fun x : V ↦
            Complex.exp (-Complex.I * (inner ℝ x ξ : ℂ)) • w x) := by fun_prop
        apply w.integrable.norm.mono' hcont.aestronglyMeasurable
        filter_upwards with x
        simp [norm_smul, Complex.norm_exp, Complex.mul_re]
      have hi := congrArg (starRingEnd ℂ) (integral_inner (𝕜 := ℂ) hfint (R ξ))
      simp only [← integral_conj, inner_conj_symm] at hi
      rw [hfourier, ← hi]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [G]
      rw [inner_smul_left, inner_smul_right]
      congr 1
      dsimp [phase]
      rw [← Complex.exp_conj]
      congr 1
      simp
    calc
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ ξ, inner ℂ (fourierSG w ξ) (R ξ) :=
        pairing w v
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ ξ, ∫ x, G x ξ := by
        simp_rw [hpoint]
        rfl
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ x, ∫ ξ, G x ξ := by
        rw [integral_integral_swap hGint]
      _ = _ := by
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards with x
        rw [hamp, inner_smul_right_eq_smul]
        congr 1
        rw [inner_smul_right_eq_smul, ← integral_inner (hphaseInt x), ← integral_smul]
        apply integral_congr_ae
        filter_upwards with ξ
        dsimp only [G]
        rw [hw, inner_smul_left_eq_smul]
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let χ : ContDiffBump (0 : V) :=
    { rIn := max R 0 + 1
      rOut := max R 0 + 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hKB : K ⊆ Metric.ball (0 : V) χ.rIn := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    exact (hR x hx).trans_lt (lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one)
  have hχ0 : χ 0 = 1 := by
    apply χ.one_of_mem_closedBall
    simp only [Metric.mem_closedBall, dist_self]
    exact χ.rIn_pos.le
  let Q := amplitudeOperator m (adjointAmplitude χ p)
    (isAmplitude_adjointAmplitude m p hp χ χ.contDiff)
    (hasCompactSupport_adjointAmplitude p hpSupp χ χ.hasCompactSupport)
  -- The input-support condition removes this same cutoff from every original input.
  have hQ : IsSchwartzFormalAdjoint P Q := by
    intro u v
    let w := SchwartzMap.smulLeftCLM E (fun x ↦ (χ x : ℂ)) u
    have hχgrowth : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
      (χ.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp χ.contDiff)
    have hw (x : V) : w x = χ x • u x := by
      simpa only [Complex.coe_smul] using SchwartzMap.smulLeftCLM_apply_apply hχgrowth u x
    have hzero : P (u - w) = 0 := by
      apply hPK.2
      have hsupp : tsupport (u - w) ⊆ (Metric.ball (0 : V) χ.rIn)ᶜ := by
        apply closure_minimal ?_ Metric.isOpen_ball.isClosed_compl
        intro x hx hxB
        apply hx
        change u x - w x = 0
        rw [hw, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hxB), one_smul,
          sub_self]
      exact Set.disjoint_left.mpr (fun x hx hxK ↦ hsupp hx (hKB hxK))
    have hPw : P w = P u := by
      rw [map_sub] at hzero
      exact (sub_eq_zero.mp hzero).symm
    calc
      _ = ∫ y, inner ℂ (quantize p w y) (v y) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [← hP w y, hPw]
      _ = ∫ x, inner ℂ (u x) (amplitudeApply (adjointAmplitude χ p) v x) :=
        ampPairing χ χ.contDiff χ.hasCompactSupport hχ0 u v
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [show Q v x = amplitudeApply (adjointAmplitude χ p) v x from
          amplitudeOperator_apply m (adjointAmplitude χ p) _ _ v x]
  refine ⟨Q, hQ, ?_⟩
  -- Compact coordinate tests separate each continuous output, proving uniqueness of the map.
  intro T hT
  apply ContinuousLinearMap.ext
  intro v
  ext x i
  have hf : Continuous (fun y ↦ T v y i) := (EuclideanSpace.proj i).continuous.comp (T v).continuous
  have hg : Continuous (fun y ↦ Q v y i) := (EuclideanSpace.proj i).continuous.comp (Q v).continuous
  have hae : (fun y ↦ T v y i) =ᵐ[volume] (fun y ↦ Q v y i) := by
    apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable
    intro φ hφ hcφ
    let ψ : 𝓢(V, E) := hcφ.smul_right.toSchwartzMap
      (hφ.smul (contDiff_const (c := EuclideanSpace.single i (1 : ℂ))))
    have heq := (hT ψ v).symm.trans (hQ ψ v)
    change (∫ y, inner ℂ (φ y • EuclideanSpace.single i 1) (T v y)) =
      ∫ y, inner ℂ (φ y • EuclideanSpace.single i 1) (Q v y) at heq
    simpa only [inner_smul_left_eq_smul, EuclideanSpace.inner_single_left,
      map_one, one_mul] using heq
  exact congrFun (Measure.eq_of_ae_eq hae hf hg) x

/-- The unique formal adjoint, specified by the actual integrated Hermitian pairing. -/
def localFormalAdjoint (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (hP : ∀ u x, P u x = quantize p u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hPK : HasOperatorSupport K P) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
  (existsUnique_localFormalAdjoint m p hp P hP K hK hPK).exists.choose

/-- The chosen operator satisfies the formal adjoint identity on all Schwartz tests. -/
theorem isSchwartzFormalAdjoint_localFormalAdjoint (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (hP : ∀ u x, P u x = quantize p u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hPK : HasOperatorSupport K P) :
    IsSchwartzFormalAdjoint P (localFormalAdjoint m p hp P hP K hK hPK) := by
  /- Unfold localFormalAdjoint and use the existence theorem's specification.
  That specification uses the Lebesgue integral of the actual pointwise Hermitian
  inner products, with conjugate-linearity in the first argument as in mathlib. -/
  exact (existsUnique_localFormalAdjoint m p hp P hP K hK hPK).exists.choose_spec

/-- Duality exchanges the two support conditions, so the formal adjoint has the same support. -/
theorem HasOperatorSupport.formalAdjoint
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (hPK : HasOperatorSupport K P) (hQ : IsSchwartzFormalAdjoint P Q) :
    HasOperatorSupport K Q := by
  /- Stage 1: test Qv against smooth compact inputs supported in the open complement
  of K. P annihilates these tests, hence Qv vanishes there; closedness of K gives
  its support inclusion. Stage 2: when v has support disjoint from K, its pairing
  with every Pu is zero because Pu is supported in K. Nondegeneracy of the Schwartz
  L² pairing gives Qv=0. No symbol order or ellipticity assumption is needed. -/
  let V := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  -- Compact scalar tests in each fiber coordinate separate continuous outputs on an open set.
  have hseparate (w : 𝓢(V, E)) (U : Set V) (hU : IsOpen U)
      (hw : ∀ u : 𝓢(V, E), tsupport u ⊆ U →
        (∫ x, inner ℂ (u x) (w x)) = 0) : ∀ x ∈ U, w x = 0 := by
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
      change (∫ x, inner ℂ (φ x • EuclideanSpace.single i 1) (w x)) = 0 at hi
      simpa only [inner_smul_left_eq_smul,
        EuclideanSpace.inner_single_left, map_one, one_mul] using hi
    have hae' : (fun y ↦ w y i) =ᵐ[volume.restrict U] (fun _ ↦ 0) := by
      exact (ae_restrict_iff' hU.measurableSet).mpr hae
    exact Measure.eqOn_open_of_ae_eq hae' hU hcont.continuousOn continuousOn_const hx
  constructor
  · intro v
    apply closure_minimal ?_ hK
    intro x hx
    by_contra hxK
    apply hx
    apply hseparate (Q v) Kᶜ hK.isOpen_compl ?_ x hxK
    intro u hu
    have huK : Disjoint (tsupport u) K := Set.disjoint_left.mpr (fun _ hz hKz ↦ hu hz hKz)
    rw [← hQ u v, hPK.2 u huK]
    simp
  · intro v hv
    have hz : ∀ x ∈ (Set.univ : Set V), Q v x = 0 := by
      apply hseparate (Q v) Set.univ isOpen_univ
      intro u _
      rw [← hQ u v]
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

/-- SG (3.14): any admissible cutoff gives the exact symbol of the chosen formal adjoint. -/
theorem localFormalAdjoint_apply (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (hP : ∀ u x, P u x = quantize p u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hPK : HasOperatorSupport K P)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupp : HasCompactSupport χ) (hone : K ⊆ interior {x | χ x = 1})
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (x : EuclideanSpace ℝ (Fin n)) :
    localFormalAdjoint m p hp P hP K hK hPK v x = quantize (adjointSymbol χ p) v x := by
  /- Stage 1: the support recovery lemma makes the adjoint amplitude uniformly compact.
  Use two genuine L¹ bounds to justify the pairing identity for this χ.
  Since χ=1 near K, the closed support of (1-χ)u is disjoint from K, giving P(χu)=Pu.
  Stage 2: uniqueness identifies this amplitude operator with localFormalAdjoint.
  Exact amplitude reduction identifies its action with quantize (adjointSymbol χ p).
  Thus the resulting operator, including smoothing terms, is independent of the cutoff. -/
  let V := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  have hpSupp : HasCompactSupport p :=
    hK.of_isClosed_subset (isClosed_tsupport p)
      (tsupport_symbol_subset_of_hasOperatorSupport m p hp P hP K hK.isClosed hPK)
  -- Two products of L1 bounds directly justify the integrated adjoint identity.
  have pairing (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))) :
      (∫ y, inner ℂ (quantize p u y) (v y)) = ((2 * Real.pi) ^ n)⁻¹ •
        ∫ ξ, inner ℂ (fourierSG u ξ)
          (∫ y, Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • (p y ξ).adjoint (v y)) := by
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let phase (y ξ : V) := Complex.exp (Complex.I * (inner ℝ y ξ : ℂ))
    have hphase (y ξ : V) : ‖phase y ξ‖ = 1 := by
      simp [phase, Complex.norm_exp, Complex.mul_re]
    have hpCont : Continuous (Function.uncurry p) := by
      simpa only [Set.univ_prod_univ, continuousOn_univ] using hp.1.continuousOn
    obtain ⟨C, hC, hbound⟩ := hp.2 (tsupport p) (Set.subset_univ _) hpSupp 0 0
    have hpnorm (y ξ : V) : ‖p y ξ‖ ≤ C * (1 + ‖ξ‖) ^ m := by
      by_cases hy : y ∈ tsupport p
      · simpa only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero]
          using hbound y hy ξ
      · have hz : p y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp only [hz, Pi.zero_apply, norm_zero]
        positivity
    -- A smooth polynomial weight bounds the order-m growth against this same Fourier input.
    obtain ⟨d, hd⟩ := exists_nat_ge m
    have hpi : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let e : V ≃L[ℝ] V :=
      (LinearEquiv.smulOfNeZero ℝ V ((2 * Real.pi)⁻¹) hpi).toContinuousLinearEquiv
    let fu : 𝓢(V, E) :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (FourierTransform.fourier u)
    have hfu (ξ : V) : fu ξ = fourierSG u ξ := rfl
    let weight (ξ : V) : ℂ := ((1 + ‖ξ‖ ^ 2) ^ d : ℝ)
    have hw : weight.HasTemperateGrowth := by dsimp [weight]; fun_prop
    let wu : 𝓢(V, E) := SchwartzMap.smulLeftCLM E weight fu
    have hwu (ξ : V) : ‖wu ξ‖ = (1 + ‖ξ‖ ^ 2) ^ d * ‖fourierSG u ξ‖ := by
      rw [show wu ξ = weight ξ • fu ξ from SchwartzMap.smulLeftCLM_apply_apply hw _ _,
        norm_smul, hfu]
      dsimp [weight]
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hweight (ξ : V) : (1 + ‖ξ‖) ^ m ≤ (2 : ℝ) ^ d * (1 + ‖ξ‖ ^ 2) ^ d := by
      have hbase : 1 + ‖ξ‖ ≤ 2 * (1 + ‖ξ‖ ^ 2) := by
        nlinarith [sq_nonneg (‖ξ‖ - 1)]
      calc
        _ ≤ (1 + ‖ξ‖) ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) hd
        _ = (1 + ‖ξ‖) ^ d := Real.rpow_natCast _ _
        _ ≤ (2 * (1 + ‖ξ‖ ^ 2)) ^ d := pow_le_pow_left₀ (by positivity) hbase d
        _ = _ := mul_pow _ _ _
    let D : ℝ := C * (2 : ℝ) ^ d
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hprod (y ξ : V) : ‖p y ξ‖ * ‖fourierSG u ξ‖ ≤ D * ‖wu ξ‖ := by
      calc
        _ ≤ (C * (1 + ‖ξ‖) ^ m) * ‖fourierSG u ξ‖ :=
          mul_le_mul_of_nonneg_right (hpnorm y ξ) (norm_nonneg _)
        _ ≤ (C * ((2 : ℝ) ^ d * (1 + ‖ξ‖ ^ 2) ^ d)) * ‖fourierSG u ξ‖ := by
          gcongr
          exact hweight ξ
        _ = _ := by rw [hwu]; dsimp [D]; ring
    let g (y ξ : V) := phase y ξ • p y ξ (fourierSG u ξ)
    have hg (y ξ : V) : ‖g y ξ‖ ≤ D * ‖wu ξ‖ := by
      dsimp only [g]
      rw [norm_smul, hphase, one_mul]
      exact ((p y ξ).le_opNorm _).trans (hprod y ξ)
    have hgcont : Continuous (Function.uncurry g) := by
      have hph : Continuous (Function.uncurry phase) := by dsimp [phase]; fun_prop
      exact hph.smul (hpCont.clm_apply (fu.continuous.comp continuous_snd))
    have hgint (y : V) : Integrable (g y) :=
      (wu.integrable.norm.const_mul D).mono'
        ((hgcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
        (Filter.Eventually.of_forall (hg y))
    -- The double pairing is bounded by the product of two genuine L1 functions.
    let H (y ξ : V) := inner ℂ (g y ξ) (v y)
    have hHcont : Continuous (Function.uncurry H) :=
      hgcont.inner (v.continuous.comp continuous_fst)
    have hHint : Integrable (Function.uncurry H) := by
      apply ((v.integrable.norm.mul_prod wu.integrable.norm).const_mul D).mono'
        hHcont.aestronglyMeasurable
      filter_upwards with z
      calc
        ‖H z.1 z.2‖ ≤ ‖g z.1 z.2‖ * ‖v z.1‖ := norm_inner_le_norm _ _
        _ ≤ (D * ‖wu z.2‖) * ‖v z.1‖ :=
          mul_le_mul_of_nonneg_right (hg z.1 z.2) (norm_nonneg _)
        _ = D * (‖v z.1‖ * ‖wu z.2‖) := by ring
    have hIntegral {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
        [CompleteSpace F] (f : V → F) (hf : Integrable f) (z : F) :
        inner ℂ (∫ x, f x) z = ∫ x, inner ℂ (f x) z := by
      simpa only [← integral_conj, inner_conj_symm] using
        (congrArg (starRingEnd ℂ) (integral_inner (𝕜 := ℂ) hf z)).symm
    have hpoint (ξ : V) : (∫ y, H y ξ) = inner ℂ (fourierSG u ξ)
        (∫ y, Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • (p y ξ).adjoint (v y)) := by
      let f (y : V) := Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) •
        (p y ξ).adjoint (v y)
      have hfcont : Continuous f := by
        have hpc : Continuous (fun y ↦ p y ξ) :=
          hpCont.comp (continuous_id.prodMk continuous_const)
        have hph : Continuous (fun y ↦ Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ))) := by
          fun_prop
        exact hph.smul ((ContinuousLinearMap.adjoint.continuous.comp hpc).clm_apply v.continuous)
      have hfint : Integrable f := by
        apply hfcont.integrable_of_hasCompactSupport
        apply hpSupp.of_isClosed_subset (isClosed_tsupport _)
        apply closure_minimal ?_ (isClosed_tsupport p)
        intro y hy
        by_contra h
        have hz : p y = 0 := image_eq_zero_of_notMem_tsupport h
        exact hy (by simp [f, hz])
      rw [← integral_inner hfint]
      apply integral_congr_ae
      filter_upwards with y
      change inner ℂ (phase y ξ • p y ξ (fourierSG u ξ)) (v y) =
        inner ℂ (fourierSG u ξ) (Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) •
          (p y ξ).adjoint (v y))
      rw [inner_smul_left, inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
      congr 1
      dsimp [phase]
      rw [← Complex.exp_conj]
      congr 1
      simp
    calc
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ y, ∫ ξ, H y ξ := by
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards with y
        change inner ℂ (((2 * Real.pi) ^ n)⁻¹ • ∫ ξ, g y ξ) (v y) = _
        rw [inner_smul_left_eq_smul, hIntegral (g y) (hgint y)]
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ ξ, ∫ y, H y ξ := by
        rw [integral_integral_swap hHint]
      _ = _ := by
        simp_rw [hpoint]
        rfl
  have ampPairing (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
      (hcχ : HasCompactSupport χ)
      (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))) :
      (∫ y, inner ℂ (quantize p
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (χ x : ℂ)) u) y) (v y)) =
        ∫ x, inner ℂ (u x) (amplitudeApply (adjointAmplitude χ p) v x) := by
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let phase (x ξ : V) := Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))
    let R (ξ : V) := ∫ y,
      Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • (p y ξ).adjoint (v y)
    let w := SchwartzMap.smulLeftCLM E (fun x ↦ (χ x : ℂ)) u
    have hχgrowth : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
      (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hχ)
    have hw (x : V) : w x = χ x • u x := by
      simpa only [Complex.coe_smul] using
        SchwartzMap.smulLeftCLM_apply_apply hχgrowth u x
    -- The dependence on x is exactly a fixed scalar phase and the selected real cutoff.
    have hfactor (ψ : V → ℝ) (x ξ : V) :
        (∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
          adjointAmplitude ψ p x y ξ (v y)) = ψ x • (phase x ξ • R ξ) := by
      dsimp only [R]
      rw [← integral_smul, ← integral_smul]
      apply integral_congr_ae
      filter_upwards with y
      have hphase : Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) =
          phase x ξ * Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) := by
        dsimp [phase]
        rw [← Complex.exp_add, inner_sub_left]
        congr 1
        push_cast
        ring
      simp only [adjointAmplitude, smul_apply, hphase, ← Complex.coe_smul, smul_smul]
      congr 1
      ring
    have hRint : Integrable R := by
      -- An auxiliary cutoff equal to one at the origin proves decay independently of χ.
      let β : ContDiffBump (0 : V) :=
        { rIn := 1
          rOut := 2
          rIn_pos := by norm_num
          rIn_lt_rOut := by norm_num }
      have hβ0 : β 0 = 1 := β.one_of_mem_closedBall (by simp [β])
      have h := integrable_amplitudeApply_outer m (adjointAmplitude β p)
        (isAmplitude_adjointAmplitude m p hp β β.contDiff)
        (hasCompactSupport_adjointAmplitude p hpSupp β β.hasCompactSupport) v 0
      change Integrable (fun ξ : V ↦ ∫ y : V,
        Complex.exp (Complex.I * (inner ℝ (0 - y) ξ : ℂ)) •
          adjointAmplitude β p 0 y ξ (v y)) at h
      simpa only [hfactor β, hβ0, phase, inner_zero_left, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, one_smul] using h
    have hamp (x : V) : amplitudeApply (adjointAmplitude χ p) v x =
        ((2 * Real.pi) ^ n)⁻¹ • (χ x • ∫ ξ, phase x ξ • R ξ) := by
      change ((2 * Real.pi) ^ n)⁻¹ • (∫ ξ : V, ∫ y : V,
        Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
          adjointAmplitude χ p x y ξ (v y)) = _
      simp_rw [hfactor χ]
      rw [integral_smul]
    -- Products of the two L1 norms justify the actual spatial-frequency swap.
    let G (x ξ : V) := inner ℂ (w x) (phase x ξ • R ξ)
    have hphaseCont : Continuous (Function.uncurry phase) := by dsimp [phase]; fun_prop
    have hphaseNorm (x ξ : V) : ‖phase x ξ‖ = 1 := by
      simp [phase, Complex.norm_exp, Complex.mul_re]
    have hGmeas : AEStronglyMeasurable (Function.uncurry G) :=
      w.continuous.aestronglyMeasurable.comp_fst.inner
        (hphaseCont.aestronglyMeasurable.smul hRint.aestronglyMeasurable.comp_snd)
    have hGint : Integrable (Function.uncurry G) := by
      apply (w.integrable.norm.mul_prod hRint.norm).mono' hGmeas
      filter_upwards with z
      exact (norm_inner_le_norm _ _).trans_eq
        (by rw [norm_smul, hphaseNorm, one_mul])
    have hphaseInt (x : V) : Integrable (fun ξ ↦ phase x ξ • R ξ) := by
      apply hRint.norm.mono'
        ((hphaseCont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.smul
          hRint.aestronglyMeasurable)
      filter_upwards with ξ
      change ‖phase x ξ • R ξ‖ ≤ ‖R ξ‖
      rw [norm_smul, hphaseNorm, one_mul]
    have hfourier (ξ : V) : fourierSG w ξ =
        ∫ x, Complex.exp (-Complex.I * (inner ℝ x ξ : ℂ)) • w x := by
      unfold fourierSG
      rw [SchwartzMap.fourier_coe, Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with x
      congr 2
      rw [inner_smul_right]
      push_cast
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
    have hpoint (ξ : V) : (∫ x, G x ξ) = inner ℂ (fourierSG w ξ) (R ξ) := by
      have hfint : Integrable (fun x ↦
          Complex.exp (-Complex.I * (inner ℝ x ξ : ℂ)) • w x) := by
        have hcont : Continuous (fun x : V ↦
            Complex.exp (-Complex.I * (inner ℝ x ξ : ℂ)) • w x) := by fun_prop
        apply w.integrable.norm.mono' hcont.aestronglyMeasurable
        filter_upwards with x
        simp [norm_smul, Complex.norm_exp, Complex.mul_re]
      have hi := congrArg (starRingEnd ℂ) (integral_inner (𝕜 := ℂ) hfint (R ξ))
      simp only [← integral_conj, inner_conj_symm] at hi
      rw [hfourier, ← hi]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [G]
      rw [inner_smul_left, inner_smul_right]
      congr 1
      dsimp [phase]
      rw [← Complex.exp_conj]
      congr 1
      simp
    calc
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ ξ, inner ℂ (fourierSG w ξ) (R ξ) :=
        pairing w v
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ ξ, ∫ x, G x ξ := by
        simp_rw [hpoint]
        rfl
      _ = ((2 * Real.pi) ^ n)⁻¹ • ∫ x, ∫ ξ, G x ξ := by
        rw [integral_integral_swap hGint]
      _ = _ := by
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards with x
        rw [hamp, inner_smul_right_eq_smul]
        congr 1
        rw [inner_smul_right_eq_smul, ← integral_inner (hphaseInt x), ← integral_smul]
        apply integral_congr_ae
        filter_upwards with ξ
        dsimp only [G]
        rw [hw, inner_smul_left_eq_smul]
  let Q := amplitudeOperator m (adjointAmplitude χ p)
    (isAmplitude_adjointAmplitude m p hp χ hχ)
    (hasCompactSupport_adjointAmplitude p hpSupp χ hχsupp)
  -- Inserting the supplied cutoff leaves P unchanged because it is one near K.
  have hQ : IsSchwartzFormalAdjoint P Q := by
    intro u v
    let w := SchwartzMap.smulLeftCLM E (fun x ↦ (χ x : ℂ)) u
    have hχgrowth : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
      (hχsupp.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hχ)
    have hw (x : V) : w x = χ x • u x := by
      simpa only [Complex.coe_smul] using SchwartzMap.smulLeftCLM_apply_apply hχgrowth u x
    have hzero : P (u - w) = 0 := by
      apply hPK.2
      have hsupp : tsupport (u - w) ⊆ (interior {x | χ x = 1})ᶜ := by
        apply closure_minimal ?_ isOpen_interior.isClosed_compl
        intro x hx hxone
        apply hx
        change u x - w x = 0
        have hχx : χ x = 1 :=
          (interior_subset (s := {y : V | χ y = 1})) hxone
        rw [hw, hχx, one_smul, sub_self]
      exact Set.disjoint_left.mpr (fun x hx hxK ↦ hsupp hx (hone hxK))
    have hPw : P w = P u := by
      rw [map_sub] at hzero
      exact (sub_eq_zero.mp hzero).symm
    calc
      _ = ∫ y, inner ℂ (quantize p w y) (v y) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [← hP w y, hPw]
      _ = ∫ x, inner ℂ (u x) (amplitudeApply (adjointAmplitude χ p) v x) :=
        ampPairing χ hχ hχsupp u v
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [show Q v x = amplitudeApply (adjointAmplitude χ p) v x from
          amplitudeOperator_apply m (adjointAmplitude χ p) _ _ v x]
  -- Uniqueness concerns the actual Schwartz operator, then reduction gives its exact symbol.
  have heq : localFormalAdjoint m p hp P hP K hK hPK = Q :=
    (existsUnique_localFormalAdjoint m p hp P hP K hK hPK).unique
      (isSchwartzFormalAdjoint_localFormalAdjoint m p hp P hP K hK hPK) hQ
  calc
    _ = amplitudeApply (adjointAmplitude χ p) v x := by
      rw [heq]
      exact amplitudeOperator_apply m _ _ _ v x
    _ = quantize (adjointSymbol χ p) v x :=
      (congrFun (quantize_amplitudeSymbol m _ (isAmplitude_adjointAmplitude m p hp χ hχ)
        (hasCompactSupport_adjointAmplitude p hpSupp χ hχsupp) v) x).symm

end AtiyahSinger
