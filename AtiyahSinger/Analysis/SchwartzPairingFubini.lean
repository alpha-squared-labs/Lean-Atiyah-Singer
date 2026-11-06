/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzPartialPairing
public import AtiyahSinger.Analysis.SchwartzTensorDensity

/-!
# Commuting localized Schwartz functionals in independent variables

Public module ID: M0947.

The actual two partial pairings are continuous linear maps on the full
product Schwartz space. Separated tests give the same iterated scalar
pairing; density in the full Schwartz topology extends this to every test.
The supplied compact cutoffs occur once, in their original variables.
This is the local distributional Fubini step for the horizontal and vertical
PDOs; their global geometric assembly is separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff SchwartzMap

variable {n m : ℕ}

local notation "X" => Fin n → ℝ
local notation "Y" => Fin m → ℝ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same compactly localized Schwartz functionals commute on the full product space. -/
theorem exists_schwartzLocalizedPairings_commute
    (φ : 𝓢(X, ℂ)) (hφ : HasCompactSupport φ)
    (ψ : 𝓢(Y, ℂ)) (hψ : HasCompactSupport ψ)
    (R : 𝓢(X, ℂ) →L[ℂ] ℂ) (L : 𝓢(Y, ℂ) →L[ℂ] ℂ) :
    let W := SchwartzMap.smulLeftCLM ℂ (fun z : X × Y ↦ φ z.1 * ψ z.2)
    let S : 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(Y × X, ℂ) :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.prodComm ℝ Y X)
    ∃ (A : 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(X, ℂ)) (B : 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ)),
      (∀ f x, A f x = L (schwartzSliceCLM x (W f))) ∧
      (∀ f y, B f y = R (schwartzSliceCLM y (S (W f)))) ∧ R.comp A = L.comp B := by
  classical
  let W := SchwartzMap.smulLeftCLM ℂ (fun z : X × Y ↦ φ z.1 * ψ z.2)
  let S : 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(Y × X, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.prodComm ℝ Y X)
  have hweight : (fun z : X × Y ↦ φ z.1 * ψ z.2).HasTemperateGrowth :=
    (φ.hasTemperateGrowth.comp (ContinuousLinearMap.fst ℝ X Y).hasTemperateGrowth).mul
      (ψ.hasTemperateGrowth.comp (ContinuousLinearMap.snd ℝ X Y).hasTemperateGrowth)
  have hW (f : 𝓢(X × Y, ℂ)) (z : X × Y) : W f z = φ z.1 * ψ z.2 * f z := by
    exact SchwartzMap.smulLeftCLM_apply_apply hweight f z
  have hsupp (f : 𝓢(X × Y, ℂ)) : tsupport (W f) ⊆ tsupport φ ×ˢ tsupport ψ := by
    apply closure_minimal ?_ ((isClosed_tsupport φ).prod (isClosed_tsupport ψ))
    intro z hz
    have hnz : φ z.1 * ψ z.2 * f z ≠ 0 := by
      change W f z ≠ 0 at hz
      rw [hW] at hz
      exact hz
    have hprod := (mul_ne_zero_iff.mp hnz).1
    exact ⟨subset_tsupport φ (mul_ne_zero_iff.mp hprod).1,
      subset_tsupport ψ (mul_ne_zero_iff.mp hprod).2⟩
  have hswap (f : 𝓢(X × Y, ℂ)) : tsupport (S (W f)) ⊆ tsupport ψ ×ˢ tsupport φ := by
    apply closure_minimal ?_ ((isClosed_tsupport ψ).prod (isClosed_tsupport φ))
    intro z hz
    have h := hsupp f (subset_tsupport (W f) hz)
    exact ⟨h.2, h.1⟩
  -- Construct both actual partial maps from the same localized input.
  obtain ⟨a, ha, haval, _⟩ := exists_continuous_schwartzPartialPairing
    W W.continuous (tsupport φ) (tsupport ψ) hφ hψ hsupp L
  obtain ⟨b, hb, hbval, _⟩ := exists_continuous_schwartzPartialPairing
    (S.comp W) (S.comp W).continuous (tsupport ψ) (tsupport φ) hψ hφ hswap R
  let A : 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(X, ℂ) :=
    { toFun := a
      map_add' f g := by
        ext x
        change a (f + g) x = a f x + a g x
        rw [haval, haval, haval, map_add, map_add, map_add]
      map_smul' c f := by
        ext x
        change a (c • f) x = c • a f x
        rw [haval, haval, map_smul, map_smul, map_smul]
      cont := ha }
  let B : 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
    { toFun := b
      map_add' f g := by
        ext y
        change b (f + g) y = b f y + b g y
        rw [hbval, hbval, hbval, map_add, map_add, map_add]
      map_smul' c f := by
        ext y
        change b (c • f) y = c • b f y
        rw [hbval, hbval, map_smul, map_smul, map_smul]
      cont := hb }
  refine ⟨A, B, haval, hbval, ?_⟩
  have hseparated (f : 𝓢(X × Y, ℂ)) (u : 𝓢(X, ℂ)) (v : 𝓢(Y, ℂ))
      (hf : ∀ z : X × Y, f z = u z.1 * v z.2) : R (A f) = L (B f) := by
    let u' := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) φ u
    let v' := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) ψ v
    have hA : A f = L v' • u' := by
      ext x
      change a f x = L v' * u' x
      rw [haval]
      have hx : schwartzSliceCLM x (W f) = u' x • v' := by
        ext y
        change W f (x, y) = u' x * v' y
        rw [hW, hf]
        change φ x * ψ y * (u x * v y) = (φ x * u x) * (ψ y * v y)
        ring
      rw [hx, map_smul]
      exact mul_comm _ _
    have hB : B f = R u' • v' := by
      ext y
      change b f y = R u' * v' y
      rw [hbval]
      have hy : schwartzSliceCLM y ((S.comp W) f) = v' y • u' := by
        ext x
        change W f (x, y) = v' y * u' x
        rw [hW, hf]
        change φ x * ψ y * (u x * v y) = (ψ y * v y) * (φ x * u x)
        ring
      rw [hy, map_smul]
      exact mul_comm _ _
    rw [hA, hB, map_smul, map_smul]
    exact mul_comm _ _
  -- Transfer the existing full Schwartz tensor density through the fixed coordinate equivalence.
  let Z := EuclideanSpace ℝ (Fin (n + m))
  let e₀ := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let eX := EuclideanSpace.equiv (Fin n) ℝ
  let eY := EuclideanSpace.equiv (Fin m) ℝ
  let e : Z ≃L[ℝ] X × Y := e₀.trans (eX.prodCongr eY)
  let J : 𝓢(Z, ℂ) →L[ℂ] 𝓢(X × Y, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  have hgenerators : Set.EqOn ((R.comp A).comp J).toLinearMap
      ((L.comp B).comp J).toLinearMap
      {f : 𝓢(Z, ℂ) | ∃ u : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        ∃ v : 𝓢(EuclideanSpace ℝ (Fin m), ℂ), ∀ z, f z = u (e₀ z).1 * v (e₀ z).2} := by
    rintro f ⟨u, v, hf⟩
    let u' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eX.symm u
    let v' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eY.symm v
    apply hseparated (J f) u' v'
    intro z
    change f (e.symm z) = u (eX.symm z.1) * v (eY.symm z.2)
    rw [hf]
    change u (e₀ (e₀.symm (eX.symm z.1, eY.symm z.2))).1 *
      v (e₀ (e₀.symm (eX.symm z.1, eY.symm z.2))).2 = _
    rw [e₀.apply_symm_apply]
  have hspan := LinearMap.eqOn_span' hgenerators
  have hall (f : 𝓢(Z, ℂ)) : R (A (J f)) = L (B (J f)) :=
    (dense_span_schwartz_products n m).induction
      (fun f hf ↦ hspan hf)
      (isClosed_eq (((R.comp A).comp J).continuous) (((L.comp B).comp J).continuous)) f
  apply ContinuousLinearMap.ext
  intro f
  change R (A f) = L (B f)
  let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hu : J u = f := by
    ext z
    change f (e (e.symm z)) = f z
    rw [e.apply_symm_apply]
  simpa only [hu] using hall u

end AtiyahSinger
