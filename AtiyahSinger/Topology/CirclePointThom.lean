/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CircleFourierPseudodifferential
public import AtiyahSinger.Topology.CircleAffineSymbol
public import AtiyahSinger.Topology.CirclePointPushforward

/-!
# The sign of the circle Fourier symbol relative to the point Thom class

Public module ID: M1615.

AR02: Atiyah--Singer I, section 8, p.526 and Figure 3. The actual Fourier
symbol is multiplication by the circle point on positive covectors and by one
on negative covectors. It is the negative of the original point pushforward,
with the normal/base coordinate first and the covector/vertical coordinate
second. This comparison concerns the prescribed two compact-support classes;
it does not infer their equality merely from both being generators.

The original source compares boundary maps on a rectangle with the line symbol
`x + iξ` on a circle. The rectangle's positively oriented top edge runs from
right to left, so its increasing angular phase contributes winding minus one.
The point and both supplied metrics are arbitrary. The proof uses two explicit
nonvanishing scalar homotopies on one compact cotangent strip, followed by
the affine symbol comparison through the prescribed point tube.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Filter
open scoped Topology

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  trivialTopology isFiniteRank_trivial isFiniteRank_pullback

set_option maxHeartbeats 1800000 in
-- Normalize the original native point frame and the Fourier symbol sign comparison.
/-- ASI Figure 3: the actual Fourier symbol is minus the actual positive point pushforward. -/
theorem circleFourierSymbolKClass_eq_neg_circlePointPushforward (a : Circle)
    (g₀ : SmoothTangentMetric (n := 0) (M := EuclideanSpace ℝ (Fin 0)))
    (g₁ : SmoothTangentMetric (n := 1) (M := Circle)) :
    circleFourierSymbolKClass = -circlePointPushforward a g₀ g₁ := by
  have hFourier : circleFourierSymbolKClass =
      (circleAffineSymbol a).compactSupportClass := by
    classical
    let CT := CotangentTotalSpace (n := 1) (M := Circle)
    let V := EuclideanSpace ℂ (Fin 1)
    let := modelTopology V FourierCircleLine
    let := isFiniteRank_model V FourierCircleLine
    let L := Bundle.Trivial CT (Fin 1 → ℂ)
    let πC := cotangentProjection (n := 1) (M := Circle)
    let A := ellipticSymbolTriple circleFourierPrincipalSymbol
      isSmoothOffZeroGlobalSymbol_circleFourierPrincipalSymbol.continuous
      isEllipticGlobalSymbol_circleFourierPrincipalSymbol
    -- Use the original native trivial frame and its complex-linear coordinate map.
    let eV := EuclideanSpace.equiv (Fin 1) ℂ
    let e₀ : Iso FourierCircleLine (Bundle.Trivial Circle (Fin 1 → ℂ)) :=
      { linearEquiv _ := eV.toLinearEquiv
        continuous_total := by
          apply continuous_induced_rng.mpr
          have hp := (Bundle.Trivial.homeomorphProd Circle V).continuous.comp
            (continuous_unitTotalEquiv V FourierCircleLine)
          exact (continuous_fst.comp hp).prodMk (eV.continuous.comp (continuous_snd.comp hp))
        continuous_symm := by
          apply (continuous_modelTotal_iff V FourierCircleLine _).mpr
          have hp : Continuous (fun z : TotalSpace Unit (Bundle.Trivial Circle (Fin 1 → ℂ)) ↦
              (z.proj, z.snd)) := continuous_induced_dom
          exact (Bundle.Trivial.homeomorphProd Circle V).symm.continuous.comp
            ((continuous_fst.comp hp).prodMk (eV.symm.continuous.comp (continuous_snd.comp hp))) }
    let e := (e₀.pullback πC).trans (pullbackTrivialIso πC 1)
    let B := A.congr e e
    have hB : B.compactSupportClass = circleFourierSymbolKClass := A.compactSupportClass_congr e e
    let coords := circleCotangentTrivialization
    let K : Set CT := coords.symm '' (Set.univ ×ˢ Set.Icc (-1 : ℝ) 1)
    have hK : IsCompact K := (isCompact_univ.prod isCompact_Icc).image coords.symm.continuous
    have hKmem (z : CT) : z ∈ K ↔ -1 ≤ (coords z).2 ∧ (coords z).2 ≤ 1 := by
      constructor
      · rintro ⟨p, hp, rfl⟩
        simpa only [coords.apply_symm_apply, Set.mem_Icc] using hp.2
      · intro h
        exact ⟨coords z, ⟨Set.mem_univ _, h⟩, coords.symm_apply_apply z⟩
    have hBK : B.control ⊆ K := by
      intro z hz
      apply (hKmem z).mpr
      change z.snd = 0 at hz
      change -1 ≤ (circleCotangentTrivialization z).2 ∧ _
      rw [circleCotangentTrivialization_apply, hz]
      norm_num [circleCovectorCoordinate]
    have hAK : (circleAffineSymbol a).control ⊆ K := by
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      apply (hKmem _).mpr
      rw [coords.apply_symm_apply]
      norm_num
    let W := (Kᶜ : Set CT)
    have hout (z : W) : (coords z.val).2 < -1 ∨ 1 < (coords z.val).2 := by
      have h := z.property
      rw [Set.mem_compl_iff, hKmem] at h
      simpa only [not_and_or, not_le] using h
    let φ : C(unitInterval, ℂ) :=
      ⟨fun t ↦ (Circle.exp ((t : ℝ) * Complex.arg ((-a⁻¹ : Circle) : ℂ)) : ℂ), by fun_prop⟩
    have hφ₀ : φ 0 = 1 := by simp [φ]
    have hφ₁ : φ 1 = (-a⁻¹ : Circle) := by
      change (Circle.exp ((1 : ℝ) * Complex.arg ((-a⁻¹ : Circle) : ℂ)) : ℂ) = _
      rw [one_mul, Circle.exp_arg]
    have hφne (t : unitInterval) : φ t ≠ 0 := (Circle.exp _).coe_ne_zero
    -- The two branches are separated on the entire exterior of this one compact strip.
    have hbranch (f : C(unitInterval × W, ℂ)) :
        Continuous (fun p : unitInterval × W ↦
          if 0 < (coords p.2.val).2 then f p else 1) := by
      have hv : Continuous (fun p : unitInterval × W ↦ (coords p.2.val).2) := by fun_prop
      apply continuous_iff_continuousAt.mpr
      intro p
      by_cases hp : 0 < (coords p.2.val).2
      · have hh : ∀ᶠ q in 𝓝 p, 0 < (coords q.2.val).2 :=
          (isOpen_lt continuous_const hv).mem_nhds hp
        apply f.continuous.continuousAt.congr_of_eventuallyEq
        filter_upwards [hh] with q hq
        exact ite_eq_left hq
      · have hp' : (coords p.2.val).2 < 0 := by rcases hout p.2 with h | h <;> linarith
        have hh : ∀ᶠ q in 𝓝 p, (coords q.2.val).2 < 0 :=
          (isOpen_lt hv continuous_const).mem_nhds hp'
        apply (continuousAt_const (y := (1 : ℂ))).congr_of_eventuallyEq
        filter_upwards [hh] with q hq
        exact ite_eq_right (by linarith)
    let H₀ : C(unitInterval × W, ℂ) :=
      ⟨fun p ↦ if 0 < (coords p.2.val).2 then φ p.1 * ((coords p.2.val).1 : ℂ) else 1,
        hbranch ⟨fun p ↦ φ p.1 * ((coords p.2.val).1 : ℂ), by fun_prop⟩⟩
    have hH₀ (p : unitInterval × W) : H₀ p ≠ 0 := by
      dsimp [H₀]
      split
      · exact mul_ne_zero (hφne p.1) (coords p.2.val).1.coe_ne_zero
      · exact one_ne_zero
    let c : C(W, ℂ) := H₀.comp ⟨fun z ↦ (1, z), continuous_const.prodMk continuous_id⟩
    let C := scalarSupportTriple L K hK c (fun z ↦ hH₀ (1, z))
    have hBC : B.Homotopic C := by
      apply CompactSupportTriple.homotopic_of_scalar L B C K hK hBK (Set.Subset.refl _) H₀ hH₀
      · intro z v
        rw [CompactSupportTriple.enlarge_apply]
        let z₀ : PuncturedCotangentBundle (n := 1) (M := Circle) :=
          ⟨z.val, fun hz ↦ z.property (hBK hz)⟩
        change ((A.congr e e).boundary.linearEquiv z₀) v = _
        refine (A.congr_apply e e z₀ v).trans ?_
        have hs := ellipticSymbolTriple_boundary_apply circleFourierPrincipalSymbol
          isSmoothOffZeroGlobalSymbol_circleFourierPrincipalSymbol.continuous
          isEllipticGlobalSymbol_circleFourierPrincipalSymbol z₀ (e.symm.linearEquiv z.val v)
        change A.boundary.linearEquiv z₀ (e.symm.linearEquiv z.val v) = _ at hs
        rw [hs]
        change e.linearEquiv z.val
          (circleFourierPrincipalSymbol z.val.proj z.val.snd
            (e.symm.linearEquiv z.val v)) = H₀ (0, z) • v
        change e.linearEquiv z.val
          ((if 0 < circleCovectorCoordinate z.val.proj z.val.snd then (z.val.proj : ℂ) else 1) •
            (e.symm.linearEquiv z.val v)) = H₀ (0, z) • v
        rw [map_smul, show e.linearEquiv z.val (e.symm.linearEquiv z.val v) = v from
          (e.linearEquiv z.val).apply_symm_apply v]
        change _ = (if 0 < (circleCotangentTrivialization z.val).2 then
          φ 0 * ((circleCotangentTrivialization z.val).1 : ℂ) else 1) • v
        rw [circleCotangentTrivialization_apply, hφ₀, one_mul]
      · intro z v
        rw [CompactSupportTriple.enlarge_apply]
        rfl
    have hphase (z : W) : φ 1 * ((coords z.val).1 : ℂ) =
        -(((coords z.val).1 / a : Circle) : ℂ) := by
      rw [hφ₁]
      simp [div_eq_mul_inv, mul_comm]
    have hvalue (z : W) : H₀ (1, z) =
        if 0 < (coords z.val).2 then -(((coords z.val).1 / a : Circle) : ℂ) else 1 := by
      change (if 0 < (coords z.val).2 then φ 1 * ((coords z.val).1 : ℂ) else 1) = _
      rw [hphase]
    let H₁ : C(unitInterval × W, ℂ) :=
      ⟨fun p ↦ (1 - (p.1 : ℝ) : ℂ) * H₀ (1, p.2) +
        (p.1 : ℝ) * circleAffineScalar a p.2.val, by fun_prop⟩
    have hnonzero (r s : ℝ) (q : Circle) (hrs : |r| ≠ |s|) :
        (r : ℂ) * q + (s : ℂ) ≠ 0 := by
      intro h
      have heq := eq_neg_of_add_eq_zero_left h
      have hn := congrArg (fun z : ℂ ↦ ‖z‖) heq
      apply hrs
      simpa only [norm_mul, Circle.norm_coe, mul_one, norm_neg,
        Complex.norm_real, Real.norm_eq_abs] using hn
    have hH₁ (p : unitInterval × W) : H₁ p ≠ 0 := by
      let t : ℝ := p.1
      let v : ℝ := (coords p.2.val).2
      let q : Circle := (coords p.2.val).1 / a
      have ht0 : 0 ≤ t := p.1.property.1
      have ht1 : t ≤ 1 := p.1.property.2
      have hF : circleAffineScalar a p.2.val = (1 - v : ℂ) - (1 + v : ℂ) * q := rfl
      rcases hout p.2 with hv | hv
      · have hv' : v < -1 := hv
        have hp : ¬0 < (coords p.2.val).2 := by linarith
        have hform : H₁ p = (-(t * (1 + v)) : ℝ) * (q : ℂ) + (1 - t * v : ℝ) := by
          change (1 - t : ℂ) * H₀ (1, p.2) + (t : ℂ) * circleAffineScalar a p.2.val = _
          rw [hvalue, ite_eq_right hp, hF]
          push_cast
          ring
        rw [hform]
        apply hnonzero
        have htv : t * v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 (by linarith)
        have hleft : 0 ≤ -(t * (1 + v)) := neg_nonneg.mpr
          (mul_nonpos_of_nonneg_of_nonpos ht0 (by linarith))
        rw [abs_of_nonneg hleft, abs_of_nonneg (by linarith : 0 ≤ 1 - t * v)]
        intro h
        nlinarith
      · have hv' : 1 < v := hv
        have hp : 0 < (coords p.2.val).2 := by linarith
        have hform : H₁ p = (-(1 + t * v) : ℝ) * (q : ℂ) + (t * (1 - v) : ℝ) := by
          change (1 - t : ℂ) * H₀ (1, p.2) + (t : ℂ) * circleAffineScalar a p.2.val = _
          rw [hvalue, ite_eq_left hp, hF]
          change (1 - t : ℂ) * -(q : ℂ) + (t : ℂ) *
            ((1 - v : ℂ) - (1 + v : ℂ) * q) = _
          push_cast
          ring
        rw [hform]
        apply hnonzero
        have htv : 0 ≤ t * v := mul_nonneg ht0 (by linarith)
        have hright : t * (1 - v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 (by linarith)
        rw [abs_of_nonpos (by linarith : -(1 + t * v) ≤ 0), abs_of_nonpos hright]
        intro h
        nlinarith
    -- Both endpoint triples use the same compact strip in this second homotopy.
    have hCA : C.Homotopic (circleAffineSymbol a) := by
      apply CompactSupportTriple.homotopic_of_scalar L C (circleAffineSymbol a)
        K hK (Set.Subset.refl _) hAK H₁ hH₁
      · intro z v
        rw [CompactSupportTriple.enlarge_apply]
        change c z • v = ((1 - (0 : ℝ) : ℂ) * H₀ (1, z) +
          (0 : ℝ) * circleAffineScalar a z.val) • v
        simp
        rfl
      · intro z v
        rw [CompactSupportTriple.enlarge_apply]
        change circleAffineScalar a z.val • v =
          ((1 - (1 : ℝ) : ℂ) * H₀ (1, z) + (1 : ℝ) * circleAffineScalar a z.val) • v
        simp
    exact hB.symm.trans ((B.compactSupportClass_eq_of_homotopic C hBC).trans
      (C.compactSupportClass_eq_of_homotopic (circleAffineSymbol a) hCA))
  -- The same point tube identifies the affine class and fixes the negative Bott sign.
  rw [hFourier, circleAffineSymbol_compactSupportClass,
    circlePointPushforward_eq_openPushforward]

end AtiyahSinger
