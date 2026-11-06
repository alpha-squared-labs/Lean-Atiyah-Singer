/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FiniteProductFourier
public import AtiyahSinger.Analysis.SchwartzTensor
public import AtiyahSinger.Analysis.SchwartzWindowReconstruction

/-!
# Constructing continuous Schwartz kernels

Public module ID: M0945.

The windowed Fourier coefficient of a tensor factors in the original finite
product coordinates. Continuous bilinear pairings of window atoms have only
polynomial growth, so the window integral defines an actual continuous
functional on the product Schwartz space. Reconstruction then checks its
value on the original tensor tests.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option backward.isDefEq.respectTransparency false

attribute [local instance 2000] NormedField.toNormedCommRing Real.normedCommRing

open MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => EuclideanSpace ℝ (Fin (n + n))

/-- Separated windows and separated tests have factored windowed Fourier
coefficients in the fixed Euclidean product coordinates. -/
theorem schwartzWindowCoefficient_finAdd_tensor (g φ ψ : 𝓢(V, ℂ))
    (G f : 𝓢(Z, ℂ))
    (hG : ∀ z, G z = g (EuclideanSpace.finAddEquivProd z).1 *
      g (EuclideanSpace.finAddEquivProd z).2)
    (hf : ∀ z, f z = φ (EuclideanSpace.finAddEquivProd z).1 *
      ψ (EuclideanSpace.finAddEquivProd z).2) (a ξ : Z) :
    schwartzWindowCoefficient G f (a, ξ) =
      schwartzWindowCoefficient g φ
        ((EuclideanSpace.finAddEquivProd a).1, (EuclideanSpace.finAddEquivProd ξ).1) *
      schwartzWindowCoefficient g ψ
        ((EuclideanSpace.finAddEquivProd a).2, (EuclideanSpace.finAddEquivProd ξ).2) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := n)
  let u := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) φ
    (SchwartzMap.compSubConstCLM ℂ (e a).1 g)
  let v := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) ψ
    (SchwartzMap.compSubConstCLM ℂ (e a).2 g)
  let w := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f
    (SchwartzMap.compSubConstCLM ℂ a G)
  have hw (x y : V) : w (e.symm (x, y)) = v y • u x := by
    change f (e.symm (x, y)) * G (e.symm (x, y) - a) =
      (ψ y * g (y - (e a).2)) * (φ x * g (x - (e a).1))
    rw [hf, hG]
    change φ (e (e.symm (x, y))).1 * ψ (e (e.symm (x, y))).2 *
      (g (e (e.symm (x, y) - a)).1 * g (e (e.symm (x, y) - a)).2) = _
    rw [map_sub, e.apply_symm_apply]
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  have h := fourier_finAdd_smul u v w hw ξ
  change (𝓕 w : 𝓢(Z, ℂ)) ξ = (𝓕 u : 𝓢(V, ℂ)) (e ξ).1 *
    (𝓕 v : 𝓢(V, ℂ)) (e ξ).2
  rw [h]
  exact mul_comm _ _

/-- Reordering two independent pairs preserves their product volumes. This is
used to keep each position coordinate beside its own frequency coordinate. -/
theorem volume_preserving_schwartzPhaseSpace_reorder :
    MeasurePreserving (fun p : (V × V) × (V × V) ↦ ((p.1.1, p.2.1), (p.1.2, p.2.2))) := by
  let A : (V × V) × (V × V) ≃ᵐ V × (V × (V × V)) := MeasurableEquiv.prodAssoc
  let B : V × (V × V) ≃ᵐ (V × V) × V := MeasurableEquiv.prodAssoc.symm
  let C : (V × V) × V ≃ᵐ (V × V) × V :=
    MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl V)
  let D : (V × V) × V ≃ᵐ V × (V × V) := MeasurableEquiv.prodAssoc
  let J := (B.trans C).trans D
  have hA : MeasurePreserving A := volume_preserving_prodAssoc
  have hB : MeasurePreserving B := (volume_preserving_prodAssoc (α₁ := V) (β₁ := V)
    (γ₁ := V)).symm
  have hC : MeasurePreserving C :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id (volume : Measure V))
  have hD : MeasurePreserving D := volume_preserving_prodAssoc
  have hJ : MeasurePreserving J := hD.comp (hC.comp hB)
  have h := hA.symm.comp (((MeasurePreserving.id (volume : Measure V)).prod hJ).comp hA)
  exact h

/-- A nondegenerate compact window extends a jointly continuous bilinear Schwartz
pairing to a continuous functional on the original product Schwartz space. -/
theorem exists_temperedKernel_of_schwartzWindow (g : 𝓢(V, ℂ))
    (hg : HasCompactSupport g) (hgmass : (∫ a : V, g a ^ 2) ≠ 0)
    (b : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) →ₗ[ℂ] ℂ)
    (hb : Continuous (fun z : 𝓢(V, ℂ) × 𝓢(V, ℂ) ↦ b z.1 z.2)) :
    ∃ K : 𝓢(V × V, ℂ) →L[ℂ] ℂ,
      ∀ φ ψ : 𝓢(V, ℂ), K (schwartzTensor φ ψ) = b φ ψ := by
  classical
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := n)
  let J : 𝓢(V × V, ℂ) →L[ℂ] 𝓢(Z, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  let G := J (schwartzTensor g g)
  have hG (z : Z) : G z = g (e z).1 * g (e z).2 := schwartzTensor_apply g g (e z)
  have hcompact : HasCompactSupport G := by
    have htensor : HasCompactSupport (schwartzTensor g g) := by
      apply HasCompactSupport.of_support_subset_isCompact (hg.prod hg)
      intro z hz
      constructor
      · apply subset_tsupport g
        intro hz₁
        exact hz (by rw [schwartzTensor_apply, hz₁, zero_mul])
      · apply subset_tsupport g
        intro hz₂
        exact hz (by rw [schwartzTensor_apply, hz₂, mul_zero])
    exact htensor.comp_homeomorph e.toHomeomorph
  let H (z : Z × Z) : ℂ :=
    b (schwartzWindowAtom g ((e z.1).1, (e z.2).1))
      (schwartzWindowAtom g ((e z.1).2, (e z.2).2))
  have hH : Continuous H := by
    have hfirst : Continuous (fun z : Z × Z ↦ ((e z.1).1, (e z.2).1)) :=
      (e.continuous.comp continuous_fst).fst.prodMk
        (e.continuous.comp continuous_snd).fst
    have hsecond : Continuous (fun z : Z × Z ↦ ((e z.1).2, (e z.2).2)) :=
      (e.continuous.comp continuous_fst).snd.prodMk
        (e.continuous.comp continuous_snd).snd
    have hW : Continuous (schwartzWindowAtom g) :=
      continuous_schwartz_modulation_translation g hg
    exact hb.comp ((hW.comp hfirst).prodMk (hW.comp hsecond))
  -- Joint continuity of b and polynomial growth of each atom control its amplitude.
  obtain ⟨s, t, _, _, Cb, hCb, hbnd⟩ := exists_schwartz_bilinear_seminorm_bound b hb
  let p := s.sup (schwartzSeminormFamily ℂ V ℂ)
  let q := t.sup (schwartzSeminormFamily ℂ V ℂ)
  have hp : Continuous p := Seminorm.continuous_finsetSup
    (fun i _ ↦ (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i)
  have hq : Continuous q := Seminorm.continuous_finsetSup
    (fun i _ ↦ (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i)
  obtain ⟨Cp, hCp, N, hpN⟩ := exists_schwartz_modulation_translation_seminorm_bound p hp g
  obtain ⟨Cq, hCq, M, hqM⟩ := exists_schwartz_modulation_translation_seminorm_bound q hq g
  let D : ℝ := 1 + ‖e.toContinuousLinearMap‖
  let C : ℝ := Cb * Cp * Cq * D ^ (N + M)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (z : Z × Z) : ‖H z‖ ≤ C * (1 + ‖z.1‖ + ‖z.2‖) ^ (N + M) := by
    let B : ℝ := 1 + ‖z.1‖ + ‖z.2‖
    have hcoordinate (v : Z) : ‖(e v).1‖ ≤ ‖e.toContinuousLinearMap‖ * ‖v‖ ∧
        ‖(e v).2‖ ≤ ‖e.toContinuousLinearMap‖ * ‖v‖ :=
      ⟨(norm_fst_le (e v)).trans (e.toContinuousLinearMap.le_opNorm v),
        (norm_snd_le (e v)).trans (e.toContinuousLinearMap.le_opNorm v)⟩
    have hfirst : 1 + ‖(e z.1).1‖ + ‖(e z.2).1‖ ≤ D * B := by
      dsimp [D, B]
      nlinarith [(hcoordinate z.1).1, (hcoordinate z.2).1,
        norm_nonneg e.toContinuousLinearMap, norm_nonneg z.1, norm_nonneg z.2]
    have hsecond : 1 + ‖(e z.1).2‖ + ‖(e z.2).2‖ ≤ D * B := by
      dsimp [D, B]
      nlinarith [(hcoordinate z.1).2, (hcoordinate z.2).2,
        norm_nonneg e.toContinuousLinearMap, norm_nonneg z.1, norm_nonneg z.2]
    have hpn : p (schwartzWindowAtom g ((e z.1).1, (e z.2).1)) ≤ Cp * (D * B) ^ N :=
      (hpN _ _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hfirst N) hCp)
    have hqm : q (schwartzWindowAtom g ((e z.1).2, (e z.2).2)) ≤ Cq * (D * B) ^ M :=
      (hqM _ _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hsecond M) hCq)
    calc
      _ ≤ Cb * p (schwartzWindowAtom g ((e z.1).1, (e z.2).1)) *
          q (schwartzWindowAtom g ((e z.1).2, (e z.2).2)) := hbnd _ _
      _ ≤ Cb * (Cp * (D * B) ^ N) * (Cq * (D * B) ^ M) := by gcongr
      _ = C * B ^ (N + M) := by
        dsimp [C]
        simp only [mul_pow, pow_add]
        ring
  obtain ⟨L, hL⟩ := exists_schwartzWindowFunctional G hcompact H hH C hC (N + M) hbound
  -- The same estimates justify the eventual product-measure Fubini step.
  have hI (f : 𝓢(Z, ℂ)) :
      Integrable (fun z ↦ schwartzWindowCoefficient G f z * H z) := by
    obtain ⟨_, _, hI⟩ := exists_schwartzWindowCoefficient_integral_bound G hcompact
      (fun z ↦ ‖H z‖) hH.norm (fun _ ↦ norm_nonneg _) C hC (N + M) hbound
    apply (integrable_norm_iff
      ((continuous_schwartzWindowCoefficient G f hcompact).fun_mul hH).aestronglyMeasurable).mp
    simpa only [norm_mul] using (hI f).1
  -- Pair each position coordinate with its own frequency, preserving actual product volume.
  let j : Z ≃ₗᵢ[ℝ] WithLp 2 (V × V) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
      (PiLp.sumPiLpEquivProdLpPiLp 2 _)
  have he : MeasurePreserving e :=
    (WithLp.volume_preserving_ofLp V V).comp j.measurePreserving
  let r : Z × Z ≃ᵐ (V × V) × (V × V) :=
    (e.toHomeomorph.toMeasurableEquiv.prodCongr e.toHomeomorph.toMeasurableEquiv).trans
      (Homeomorph.prodProdProdComm V V V V).toMeasurableEquiv
  have hr : MeasurePreserving r :=
    volume_preserving_schwartzPhaseSpace_reorder.comp (he.prod he)
  let c : ℂ := ∫ a : V, g a ^ 2
  refine ⟨c⁻¹ ^ 2 • L.comp J, ?_⟩
  intro φ ψ
  let f := J (schwartzTensor φ ψ)
  have hf (z : Z) : f z = φ (e z).1 * ψ (e z).2 := schwartzTensor_apply φ ψ (e z)
  let F (z : (V × V) × (V × V)) : ℂ :=
    (schwartzWindowCoefficient g φ z.1 * schwartzWindowCoefficient g ψ z.2) *
      b (schwartzWindowAtom g z.1) (schwartzWindowAtom g z.2)
  have hfactor (z : Z × Z) : schwartzWindowCoefficient G f z * H z = F (r z) := by
    rw [schwartzWindowCoefficient_finAdd_tensor g φ ψ G f hG hf z.1 z.2]
    rfl
  have hFI : Integrable F := (hr.integrable_comp_emb r.measurableEmbedding).mp (by
    convert hI f using 1
    funext z
    exact (hfactor z).symm)
  have hLF : L f = c ^ 2 * b φ ψ := by
    rw [hL]
    calc
      _ = ∫ z : Z × Z, F (r z) := integral_congr_ae (Filter.Eventually.of_forall hfactor)
      _ = ∫ z : (V × V) × (V × V), F z := hr.integral_comp' F
      _ = ∫ p : V × V, ∫ q : V × V, F (p, q) := integral_prod F hFI
      _ = c ^ 2 * b φ ψ := integral_integral_schwartzWindow_bilinear g φ ψ hg b hb
  change c⁻¹ ^ 2 * L f = b φ ψ
  rw [hLF]
  have hc : c ≠ 0 := hgmass
  field_simp

end AtiyahSinger
