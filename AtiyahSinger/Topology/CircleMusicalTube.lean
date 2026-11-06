/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CircleAngularChart
public import AtiyahSinger.Geometry.TangentMusical
public import AtiyahSinger.Topology.EuclideanTangentKTheory
public import AtiyahSinger.Topology.TangentEmbeddingOpenRestriction

/-!
# The musical derivative tube and the specified circle point tube

Public module ID: M1613.

For any positive smooth metric, the derivative of the normalized angular
chart followed by the actual musical map differs from the specified cotangent
tube by a positive vertical coefficient. Interpolating that coefficient gives
a homeomorphism of the whole parameter cylinder. Open-extension invariance
therefore compares the actual maps on all compact-support classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff unitInterval

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
  t2Space_cotangent locallyCompactSpace_cotangent

local notation "ER" => EuclideanSpace ℝ (Fin 1)
local notation "TR" => TangentBundle (𝓡 1) ER
local notation "TC" => TangentBundle (𝓡 1) Circle
local notation "CT" => CotangentTotalSpace (n := 1) (M := Circle)

set_option maxHeartbeats 1400000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Positive musical scaling of the derivative tube preserves its actual open extension. -/
theorem circlePointMusicalTube_openPushforward (a : Circle)
    (c : ContMDiffMap (𝓡 1) (𝓡 1) ER Circle ∞)
    (hc : IsLocalDiffeomorph (𝓡 1) (𝓡 1) ∞ c) (hinj : Function.Injective c)
    (hvalue : ∀ u : ER, c u = a * Circle.exp (2 * Real.arctan (u 0 / 2)))
    (hder : ∀ (u v : ER), mfderiv (𝓡 1) (𝓡 1) c u v =
      (((1 + (u 0 / 2) ^ 2)⁻¹ * v 0) : ℝ) • circleAngularTangent (c u))
    (g : SmoothTangentMetric (n := 1) (M := Circle)) :
    let Q : ℂ ≃ₜ TR := (Homeomorph.funUnique (Fin 1) ℂ).symm.trans
      (euclideanTangentComplexHomeomorph 1).symm
    let β : C(ℂ, CT) :=
      ⟨g.flatHomeomorph ∘ smoothTangentMap c ∘ Q,
        g.flatHomeomorph.continuous.comp
          ((smoothTangentMap c).contMDiff.continuous.comp Q.continuous)⟩
    let hβ : IsOpenEmbedding β := g.flatHomeomorph.isOpenEmbedding.comp
      ((isOpenEmbedding_smoothTangentMap c hc hinj).comp Q.isOpenEmbedding)
    compactSupportKZeroOpenPushforward β hβ =
      compactSupportKZeroOpenPushforward (circlePointCotangentTube a)
        (isOpenEmbedding_circlePointCotangentTube a) := by
  classical
  let Q : ℂ ≃ₜ TR := (Homeomorph.funUnique (Fin 1) ℂ).symm.trans
    (euclideanTangentComplexHomeomorph 1).symm
  let β : C(ℂ, CT) :=
    ⟨g.flatHomeomorph ∘ smoothTangentMap c ∘ Q,
      g.flatHomeomorph.continuous.comp
        ((smoothTangentMap c).contMDiff.continuous.comp Q.continuous)⟩
  have hβ : IsOpenEmbedding β := g.flatHomeomorph.isOpenEmbedding.comp
    ((isOpenEmbedding_smoothTangentMap c hc hinj).comp Q.isOpenEmbedding)
  let point (u : ℝ) : ER := WithLp.toLp 2 (fun _ ↦ u)
  let weight : C(ℝ, ℝ) :=
    ⟨fun u ↦ (circleCotangentTrivialization (β ((u : ℂ) + Complex.I))).2, by fun_prop⟩
  have hraw (z : ℂ) : circleCotangentTrivialization (β z) =
      (c (point z.re), ((1 + (z.re / 2) ^ 2)⁻¹ * z.im) *
        g.inner (c (point z.re)) (circleAngularTangent (c (point z.re)))
          (circleAngularTangent (c (point z.re)))) := by
    rw [circleCotangentTrivialization_apply]
    change (c (point z.re), g.inner (c (point z.re))
      (mfderiv (𝓡 1) (𝓡 1) c (point z.re) (point z.im))
        (circleAngularTangent (c (point z.re)))) = _
    rw [hder]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rfl
  have hweight (u : ℝ) : weight u = (1 + (u / 2) ^ 2)⁻¹ *
      g.inner (c (point u)) (circleAngularTangent (c (point u)))
        (circleAngularTangent (c (point u))) := by
    have hre : ((u : ℂ) + Complex.I).re = u := by simp
    have him : ((u : ℂ) + Complex.I).im = 1 := by simp
    exact (congrArg Prod.snd (hraw ((u : ℂ) + Complex.I))).trans (by
      rw [hre, him, mul_one])
  have hweightpos (u : ℝ) : 0 < weight u := by
    rw [hweight]
    apply mul_pos (by positivity)
    apply g.pos
    intro hz
    have h := mfderiv_coe_circleAngularTangent (c (point u))
    rw [hz, map_zero] at h
    exact mul_ne_zero (c (point u)).coe_ne_zero Complex.I_ne_zero h.symm
  have hcoords (z : ℂ) : circleCotangentTrivialization (β z) =
      (a * Circle.exp (2 * Real.arctan (z.re / 2)), weight z.re * z.im) := by
    rw [hraw, hweight]
    apply Prod.ext
    · exact hvalue (point z.re)
    · dsimp only
      ring
  change compactSupportKZeroOpenPushforward β hβ = _
  clear hraw hweight
  clear_value weight β
  -- Each positive coefficient is interpolated without changing the real base coordinate.
  let scale (t : I) (u : ℝ) : ℝ := (1 - (t : ℝ)) * weight u + t
  have hscale (t : I) (u : ℝ) : 0 < scale t u := by
    dsimp [scale]
    by_cases ht : (t : ℝ) = 1
    · simp [ht]
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr (lt_of_le_of_ne t.property.2 ht)) (hweightpos u)) t.property.1
  have hs : Continuous (fun p : I × ℂ ↦ scale p.1 p.2.re) := by
    dsimp [scale]
    fun_prop
  let A : (I × ℂ) ≃ₜ (I × ℂ) :=
    { toFun p := (p.1, (p.2.re : ℂ) + (scale p.1 p.2.re * p.2.im : ℝ) * Complex.I)
      invFun p := (p.1, (p.2.re : ℂ) + (p.2.im / scale p.1 p.2.re : ℝ) * Complex.I)
      left_inv := by
        rintro ⟨t, z⟩
        apply Prod.ext
        · rfl
        dsimp only
        apply Complex.ext
        · simp
        · simpa using mul_div_cancel_left₀ z.im (hscale t z.re).ne'
      right_inv := by
        rintro ⟨t, z⟩
        apply Prod.ext
        · rfl
        dsimp only
        apply Complex.ext
        · simp
        · simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
            Complex.I_im, mul_zero, mul_one, add_zero, zero_add, sub_zero]
          exact (mul_comm _ _).trans (div_mul_cancel₀ z.im (hscale t z.re).ne')
      continuous_toFun := continuous_fst.prodMk
        ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp continuous_snd)).add
          ((Complex.continuous_ofReal.comp
            (hs.mul (Complex.continuous_im.comp continuous_snd))).mul continuous_const))
      continuous_invFun := continuous_fst.prodMk
        ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp continuous_snd)).add
          ((Complex.continuous_ofReal.comp
            ((Complex.continuous_im.comp continuous_snd).div hs
              (fun p ↦ (hscale p.1 p.2.re).ne'))).mul continuous_const)) }
  let tube : C(ℂ, CT) :=
    ⟨circlePointCotangentTube a, (isOpenEmbedding_circlePointCotangentTube a).continuous⟩
  let H : ContinuousMap.Homotopy β tube :=
    { toFun p := tube (A p).2
      continuous_toFun := tube.continuous.comp (continuous_snd.comp A.continuous)
      map_zero_left := by
        intro z
        apply circleCotangentTrivialization.injective
        rw [hcoords]
        change circleCotangentTrivialization
          (circleCotangentTrivialization.symm
            (a * Circle.exp (2 * Real.arctan ((A (0, z)).2.re / 2)), (A (0, z)).2.im)) = _
        rw [circleCotangentTrivialization.apply_symm_apply]
        simp [A, scale]
      map_one_left := by
        intro z
        apply congrArg tube
        apply Complex.ext <;> simp [A, scale] }
  have hH : IsOpenEmbedding (fun p : I × ℂ ↦ (p.1, H p)) := by
    change IsOpenEmbedding ((Prod.map id tube) ∘ A)
    exact (IsOpenEmbedding.id.prodMap
      (isOpenEmbedding_circlePointCotangentTube a)).comp A.isOpenEmbedding
  exact compactSupportKZeroOpenPushforward_eq_of_isotopy (f := β) (g := tube) hβ
    (isOpenEmbedding_circlePointCotangentTube a) H hH

end AtiyahSinger
