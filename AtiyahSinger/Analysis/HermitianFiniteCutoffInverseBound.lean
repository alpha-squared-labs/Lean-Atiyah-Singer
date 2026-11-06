/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FiniteFiberFullSymbolCutoffInverseBound

/-!
# Quantitative cutoff ellipticity for specified Hermitian forms and adjoints

The original finite factors may be given as algebraic maps with energy bounds
in prescribed Hermitian forms. Realize exactly these forms as norms on each
fiber and apply the uniform finite two-cone estimate. Its constants are chosen
before selecting a fiber. The reverse factors in the resulting matrix remain
the supplied maps: their original pairing identities identify them with the
adjoints for these same forms.

This is the metric formulation of the finite full-symbol estimate. The actual
geometric axis, transverse, vertical and active-chart bounds are still needed
when applying it to an associated-sphere operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct unitInterval

variable {Z X Y ι : Type*} {E₀ E₁ F₀ F₁ : Z → Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [∀ z, AddCommGroup (E₀ z)] [∀ z, Module ℂ (E₀ z)]
  [∀ z, FiniteDimensional ℂ (E₀ z)]
  [∀ z, AddCommGroup (E₁ z)] [∀ z, Module ℂ (E₁ z)]
  [∀ z, FiniteDimensional ℂ (E₁ z)]
  [∀ z, AddCommGroup (F₀ z)] [∀ z, Module ℂ (F₀ z)]
  [∀ z, FiniteDimensional ℂ (F₀ z)]
  [∀ z, AddCommGroup (F₁ z)] [∀ z, Module ℂ (F₁ z)]
  [∀ z, FiniteDimensional ℂ (F₁ z)] [Fintype ι]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in

/-- Energy bounds in the specified forms control the same cutoff matrix and reverse maps. -/
theorem exists_hermitianFiniteFullSymbolCutoffHomotopy_inverse_bound
    (h₀ : ∀ z, InnerProductSpace.Core ℂ (E₀ z))
    (h₁ : ∀ z, InnerProductSpace.Core ℂ (E₁ z))
    (k₀ : ∀ z, InnerProductSpace.Core ℂ (F₀ z))
    (k₁ : ∀ z, InnerProductSpace.Core ℂ (F₁ z))
    (w v : ι → Z → ℝ)
    (p : ι → unitInterval → ∀ z : Z, X → Y → E₀ z →ₗ[ℂ] E₁ z)
    (q : ι → ∀ z : Z, Y → F₀ z →ₗ[ℂ] F₁ z)
    (r : unitInterval → ∀ z : Z, X → Y → E₀ z →ₗ[ℂ] E₁ z)
    (a : ∀ z : Z, X → E₀ z →ₗ[ℂ] E₁ z)
    (A : ι → Z → X →L[ℝ] X) (B : ι → Z → Y →L[ℝ] X)
    (V : ι → Z → Y →L[ℝ] Y)
    (D : ℝ) (hD : 1 ≤ D)
    (hgeom : ∀ i z, w i z ≠ 0 ∨ v i z ≠ 0 →
      ‖A i z‖ ≤ D ∧ (∀ ξ, ‖ξ‖ ≤ D * ‖A i z ξ‖) ∧ ‖B i z‖ ≤ D ∧
        ‖V i z‖ ≤ D ∧ ∀ η, ‖η‖ ≤ D * ‖V i z η‖)
    (R₀ C L N : ℝ) (hR₀ : 0 ≤ R₀) (hC : 0 ≤ C) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (haxis : ∀ z ξ, R₀ ≤ ‖ξ‖ → Function.Bijective (a z ξ) ∧ ∀ u,
      ((h₀ z).inner u u).re ≤ (C / (1 + ‖ξ‖)) ^ 2 *
        ((h₁ z).inner (a z ξ u) (a z ξ u)).re)
    (herror : ∀ t z ξ η, R₀ ≤ ‖ξ‖ → ∀ u,
      let e := ((∑ i, (w i z : ℂ) • p i t z ξ η) + r t z ξ η) - a z ξ
      ((h₁ z).inner (e u) (e u)).re ≤ (L * ‖η‖ + N) ^ 2 * ((h₀ z).inner u u).re)
    (S CQ : ℝ) (hS : 0 ≤ S) (hCQ : 0 ≤ CQ)
    (hq : ∀ z η, S ≤ ‖η‖ →
      let Q := ∑ i, (v i z : ℂ) • q i z η
      Function.Bijective Q ∧ ∀ u, ((k₀ z).inner u u).re ≤
        (CQ / (1 + ‖η‖)) ^ 2 * ((k₁ z).inner (Q u) (Q u)).re) :
    letI : ∀ z, InnerProductSpace.Core ℂ (E₀ z) := h₀
    letI : ∀ z, InnerProductSpace.Core ℂ (E₁ z) := h₁
    letI : ∀ z, InnerProductSpace.Core ℂ (F₀ z) := k₀
    letI : ∀ z, InnerProductSpace.Core ℂ (F₁ z) := k₁
    letI : ∀ z, NormedAddCommGroup (E₀ z) := fun _ ↦
      InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    letI : ∀ z, NormedAddCommGroup (E₁ z) := fun _ ↦
      InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    letI : ∀ z, NormedAddCommGroup (F₀ z) := fun _ ↦
      InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    letI : ∀ z, NormedAddCommGroup (F₁ z) := fun _ ↦
      InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    letI : ∀ z, InnerProductSpace ℂ (E₀ z) := fun _ ↦ InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ _)
    letI : ∀ z, InnerProductSpace ℂ (E₁ z) := fun _ ↦ InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ _)
    letI : ∀ z, InnerProductSpace ℂ (F₀ z) := fun _ ↦ InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ _)
    letI : ∀ z, InnerProductSpace ℂ (F₁ z) := fun _ ↦ InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ _)
    ∃ ε₀ R K : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < R ∧ 0 ≤ K ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (t : unitInterval) z ξ η, R ≤ ‖ξ‖ + ‖η‖ →
        let P := (∑ i, ((w i z * productCutoffHomotopyWeight ε t
          ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ : ℝ) : ℂ) • p i t z ξ η) + r t z ξ η
        let Q := ∑ i, ((v i z * productCutoffHomotopyWeight ε t
          ‖V i z η‖ ‖A i z ξ + (t : ℝ) • B i z η‖ : ℝ) : ℂ) • q i z η
        ∀ (pi : E₁ z →ₗ[ℂ] E₀ z) (qi : F₁ z →ₗ[ℂ] F₀ z),
          (∀ u v, (h₁ z).inner (P u) v = (h₀ z).inner u (pi v)) →
          (∀ u v, (k₁ z).inner (Q u) v = (k₀ z).inner u (qi v)) →
          let T := (reciprocalTensorSymbol P pi Q qi).toContinuousLinearMap
          T.IsInvertible ∧ ‖T.inverse‖ ≤ K / (1 + ‖ξ‖ + ‖η‖) := by
  classical
  dsimp only
  -- Local norms are induced by exactly the original four forms on every original fiber.
  let := h₀
  let := h₁
  let := k₀
  let := k₁
  let : ∀ z, NormedAddCommGroup (E₀ z) := fun _ ↦
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : ∀ z, NormedAddCommGroup (E₁ z) := fun _ ↦
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : ∀ z, NormedAddCommGroup (F₀ z) := fun _ ↦
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : ∀ z, NormedAddCommGroup (F₁ z) := fun _ ↦
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : ∀ z, InnerProductSpace ℂ (E₀ z) := fun _ ↦ InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  let : ∀ z, InnerProductSpace ℂ (E₁ z) := fun _ ↦ InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  let : ∀ z, InnerProductSpace ℂ (F₀ z) := fun _ ↦ InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  let : ∀ z, InnerProductSpace ℂ (F₁ z) := fun _ ↦ InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  -- The horizontal energy estimate controls the inverse of that same bijective map.
  have haxis' (z : Z) (ξ : X) (hξ : R₀ ≤ ‖ξ‖) :
      (a z ξ).toContinuousLinearMap.IsInvertible ∧
        ‖(a z ξ).toContinuousLinearMap.inverse‖ ≤ C / (1 + ‖ξ‖) := by
    obtain ⟨hi, he⟩ := haxis z ξ hξ
    let f := (a z ξ).toContinuousLinearMap
    have hf : f.IsInvertible :=
      ⟨(LinearEquiv.ofBijective (a z ξ) hi).toContinuousLinearEquiv, rfl⟩
    refine ⟨hf, ?_⟩
    have hc : 0 ≤ C / (1 + ‖ξ‖) := div_nonneg hC (by positivity)
    apply f.inverse.opNorm_le_bound hc
    intro u
    have hb := he (f.inverse u)
    change (inner ℂ (f.inverse u) (f.inverse u)).re ≤ (C / (1 + ‖ξ‖)) ^ 2 *
      (inner ℂ (f (f.inverse u)) (f (f.inverse u))).re at hb
    rw [hf.self_apply_inverse] at hb
    have hi₀ : (inner ℂ (f.inverse u) (f.inverse u)).re = ‖f.inverse u‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) (f.inverse u)).symm
    have hi₁ : (inner ℂ u u).re = ‖u‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
    rw [hi₀, hi₁, ← mul_pow] at hb
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp hb
  -- The vertical energy bound gives the inverse estimate for the same weighted vertical map.
  have hq' (z : Z) (η : Y) (hη : S ≤ ‖η‖) :
      (∑ i, (v i z : ℂ) • (q i z η).toContinuousLinearMap).IsInvertible ∧
        ‖(∑ i, (v i z : ℂ) • (q i z η).toContinuousLinearMap).inverse‖ ≤
          CQ / (1 + ‖η‖) := by
    obtain ⟨hi, he⟩ := hq z η hη
    let f := (∑ i, (v i z : ℂ) • q i z η).toContinuousLinearMap
    have hf : f.IsInvertible :=
      ⟨(LinearEquiv.ofBijective (∑ i, (v i z : ℂ) • q i z η) hi).toContinuousLinearEquiv, rfl⟩
    have hb : f.IsInvertible ∧ ‖f.inverse‖ ≤ CQ / (1 + ‖η‖) := by
      refine ⟨hf, ?_⟩
      have hc : 0 ≤ CQ / (1 + ‖η‖) := div_nonneg hCQ (by positivity)
      apply f.inverse.opNorm_le_bound hc
      intro u
      have hv := he (f.inverse u)
      change (inner ℂ (f.inverse u) (f.inverse u)).re ≤ (CQ / (1 + ‖η‖)) ^ 2 *
        (inner ℂ (f (f.inverse u)) (f (f.inverse u))).re at hv
      rw [hf.self_apply_inverse] at hv
      have hi₀ : (inner ℂ (f.inverse u) (f.inverse u)).re = ‖f.inverse u‖ ^ 2 :=
        (norm_sq_eq_re_inner (𝕜 := ℂ) (f.inverse u)).symm
      have hi₁ : (inner ℂ u u).re = ‖u‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
      rw [hi₀, hi₁, ← mul_pow] at hv
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp hv
    simpa only [f, map_sum, map_smul] using hb
  have herror' (t : unitInterval) (z : Z) (ξ : X) (η : Y) (hξ : R₀ ≤ ‖ξ‖) :
      ‖((∑ i, (w i z : ℂ) • (p i t z ξ η).toContinuousLinearMap) +
        (r t z ξ η).toContinuousLinearMap) - (a z ξ).toContinuousLinearMap‖ ≤ L * ‖η‖ + N := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    have hb := herror t z ξ η hξ u
    change (inner ℂ _ _).re ≤ (L * ‖η‖ + N) ^ 2 * (inner ℂ u u).re at hb
    have hi₀ : (inner ℂ u u).re = ‖u‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
    have hi₁ (v : E₁ z) : (inner ℂ v v).re = ‖v‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
    rw [hi₀, hi₁, ← mul_pow] at hb
    have hc : 0 ≤ (L * ‖η‖ + N) * ‖u‖ := by positivity
    have hnorm := (sq_le_sq₀ (norm_nonneg
      (((∑ i, (w i z : ℂ) • p i t z ξ η) + r t z ξ η - a z ξ) u)) hc).mp hb
    simpa using hnorm
  -- The uniform two-cone theorem applies to these maps with the shared scalar constants.
  obtain ⟨ε₀, R, K, hε₀, hε₀one, hR, hK, hb⟩ :=
    exists_finiteFiberFullSymbolCutoffHomotopy_inverse_bound w v
      (fun i t z ξ η ↦ (p i t z ξ η).toContinuousLinearMap)
      (fun i z η ↦ (q i z η).toContinuousLinearMap)
      (fun t z ξ η ↦ (r t z ξ η).toContinuousLinearMap)
      (fun z ξ ↦ (a z ξ).toContinuousLinearMap)
      A B V D hD hgeom R₀ C L N hR₀ hC hL hN haxis' herror' S CQ hS hCQ hq'
  refine ⟨ε₀, R, K, hε₀, hε₀one, hR, hK, ?_⟩
  intro ε hε hεle t z ξ η hlarge pi qi hpi hqi
  let P := (∑ i, ((w i z * productCutoffHomotopyWeight ε t
    ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ : ℝ) : ℂ) • p i t z ξ η) + r t z ξ η
  let Q := ∑ i, ((v i z * productCutoffHomotopyWeight ε t
    ‖V i z η‖ ‖A i z ξ + (t : ℝ) • B i z η‖ : ℝ) : ℂ) • q i z η
  change (reciprocalTensorSymbol P pi Q qi).toContinuousLinearMap.IsInvertible ∧
    ‖(reciprocalTensorSymbol P pi Q qi).toContinuousLinearMap.inverse‖ ≤
      K / (1 + ‖ξ‖ + ‖η‖)
  -- Pairing uniqueness identifies the supplied reverse maps with the actual metric adjoints.
  have hpi' : pi = P.adjoint := by
    have he : P = pi.adjoint := (LinearMap.eq_adjoint_iff P pi).mpr hpi
    rw [he, LinearMap.adjoint_adjoint]
  have hqi' : qi = Q.adjoint := by
    have he : Q = qi.adjoint := (LinearMap.eq_adjoint_iff Q qi).mpr hqi
    rw [he, LinearMap.adjoint_adjoint]
  rw [hpi', hqi']
  have h := hb ε hε hεle t z ξ η hlarge
  have hP : ((∑ i, ((w i z * productCutoffHomotopyWeight ε t
      ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ : ℝ) : ℂ) •
        (p i t z ξ η).toContinuousLinearMap) +
      (r t z ξ η).toContinuousLinearMap).toLinearMap = P := by
    ext u
    simp [P]
  have hQ : (∑ i, ((v i z * productCutoffHomotopyWeight ε t
      ‖V i z η‖ ‖A i z ξ + (t : ℝ) • B i z η‖ : ℝ) : ℂ) •
        (q i z η).toContinuousLinearMap).toLinearMap = Q := by
    ext u
    simp [Q]
  dsimp only at h
  rw [hP, hQ] at h
  exact h

end AtiyahSinger
