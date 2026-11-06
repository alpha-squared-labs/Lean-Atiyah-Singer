/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialParametrix
public import AtiyahSinger.Analysis.UniformSymbolRegularization

/-!
# Homogeneous principal data from an actual symbol at infinity

Public module ID: M0744.

An order-one full symbol which is exactly homogeneous on every sufficiently
large metric ray has a representative homogeneous of degree one and smooth
off zero. Rescaling its restriction to one fixed metric sphere preserves the actual high-frequency
values. Compact frequency support then identifies the principal classes.

This is the radial bridge needed for the actual product cutoff PDOs. The
hypothesis is exact homogeneity at infinity, which must be checked for the
specified full symbol before applying this theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000 in

/-- Exact degree-one homogeneity at infinity supplies the same homogeneous principal class. -/
theorem exists_homogeneousSymbol_of_degree_one_at_infinity
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F 1)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) (hR : 0 < R)
    (hscale : ∀ x ξ (t : ℝ), 0 < t → R ≤ g.length x ξ →
      R ≤ g.length x (t • ξ) → a.val x (t • ξ) = (t : ℂ) • a.val x ξ) :
    ∃ b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 1,
      (∀ x ξ, R ≤ g.length x ξ → b.val x ξ = a.val x ξ) ∧
      ∀ A : QuantizationPresentation (n := n) (r := r) (q := q) E F,
        globalPrincipalSymbolClass E F 1 a = globalPrincipalSymbolClass E F 1
          (A.regularizedSymbol 1 b.val b.property.1 b.property.2) := by
  classical
  let s : GlobalSymbolFunction (n := n) E F := fun x ξ ↦ (R⁻¹ : ℂ) • a.val x (R • ξ)
  have hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F s := by
    intro c hc e f _ _
    have hcov (x : M) (η : EuclideanSpace ℝ (Fin n)) :
        covectorFromChart c x (R • η) = R • covectorFromChart c x η := by
      ext v
      change inner ℝ (R • η) (mfderiv _ _ c x v) = _
      exact real_inner_smul_left η _ R
    have hformula (z η : EuclideanSpace ℝ (Fin n)) :
        globalSymbolInChart E F s c e f z η =
          (R⁻¹ : ℂ) • globalSymbolInChart E F a.val c e f z (R • η) := by
      simp only [s, globalSymbolInChart, hcov, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.comp_smul]
    have hmap : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) ↦ (z.1, R • z.2)) :=
      contDiff_fst.prodMk (contDiff_snd.const_smul R)
    have hmaps : MapsTo
        (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦ (z.1, R • z.2))
        (symbolChartDomain E F c e f ×ˢ {ξ | ξ ≠ 0})
        (symbolChartDomain E F c e f ×ˢ univ) :=
      fun _ hz ↦ ⟨hz.1, mem_univ _⟩
    have h := (a.property c hc e f).1.comp hmap.contDiffOn hmaps
    exact ((contDiffOn_const (c := (R⁻¹ : ℂ))).smul h).congr
      (fun z _ ↦ hformula z.1 z.2)
  let b := smoothCosphereExtension g 1
    ⟨cosphereRestriction g s, isSmoothCosphereSymbol_restriction g s hs⟩
  have hhigh (x : M) (ξ : CotangentFiber (n := n) x) (hξ : R ≤ g.length x ξ) :
      b.val x ξ = a.val x ξ := by
    have hne : ξ ≠ 0 := by
      intro hzero
      rw [hzero, (g.length_eq_zero_iff x 0).mpr rfl] at hξ
      exact (not_le_of_gt hR) hξ
    let w := R • g.normalize x ξ
    let t := g.length x ξ / R
    have ht : 0 < t := div_pos (g.length_pos x ξ hne) hR
    have hw : g.length x w = R := by
      rw [g.length_smul, abs_of_pos hR, g.length_normalize x ξ hne, mul_one]
    have htw : t • w = ξ := by
      dsimp only [t, w]
      rw [smul_smul, div_mul_cancel₀ _ hR.ne', g.length_smul_normalize]
    have h := hscale x w t ht hw.ge (by simpa only [htw] using hξ)
    rw [htw] at h
    change cosphereExtension g 1 (cosphereRestriction g s) x ξ = _
    rw [cosphereExtension_of_ne_zero g 1 (cosphereRestriction g s) x ξ hne]
    change ((g.length x ξ ^ (1 : ℝ) : ℝ) : ℂ) •
      ((R⁻¹ : ℂ) • a.val x w) = a.val x ξ
    rw [Real.rpow_one, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    have hscalar : g.length x ξ * R⁻¹ = t := by dsimp [t]; rw [div_eq_mul_inv]
    rw [hscalar]
    exact h.symm
  refine ⟨b, hhigh, ?_⟩
  intro A
  let c := A.regularizedSymbol 1 b.val b.property.1 b.property.2
  obtain ⟨R₀, hR₀, hrecover⟩ := A.exists_regularizedSymbolFunction_eq_of_length_ge g
  let L := max R R₀
  have hsame (x : M) (ξ : CotangentFiber (n := n) x) (hξ : L ≤ g.length x ξ) :
      a.val x ξ = c.val x ξ := by
    change _ = A.regularizedSymbolFunction b.val x ξ
    rw [hrecover b.val x ξ ((le_max_right _ _).trans hξ)]
    exact (hhigh x ξ ((le_max_left _ _).trans hξ)).symm
  -- Local compact windows convert the fixed metric radius into a frequency support bound.
  apply (globalPrincipalSymbolClass_eq_iff E F 1 a c).mpr
  intro d hd e f _ _
  let U := symbolChartDomain E F d e f
  have hU : IsOpen U := isOpen_symbolChartDomain E F d e f
  let p := globalSymbolInChart E F a.val d e f - globalSymbolInChart E F c.val d e f
  have hp : ContDiffOn ℝ ∞ (Function.uncurry p) (U ×ˢ univ) :=
    (a.property d hd e f).1.sub (c.property d hd e f).1
  have hsub : globalSymbolInChart E F (a.val - c.val) d e f = p := by
    ext z η v
    simp [p, globalSymbolInChart]
  rw [hsub]
  refine ⟨hp, ?_⟩
  intro K hKU hK i j
  obtain ⟨K', hK', hKK', hK'U⟩ := exists_compact_between hK hU hKU
  obtain ⟨b₀, B₀, hb₀, _, hnorm⟩ := g.exists_length_bounds_on d hd K' hK'
    (fun z hz ↦ (hK'U hz).1.1)
  have hsupp : ∀ z ∈ interior K', ∀ η, L / b₀ ≤ ‖η‖ → p z η = 0 := by
    intro z hz η hη
    have hlen : L ≤ g.length (d.symm z) (covectorFromChart d (d.symm z) η) :=
      ((div_le_iff₀ hb₀).mp hη).trans
        (by simpa only [mul_comm] using (hnorm z (interior_subset hz) η).1)
    dsimp only [p, Pi.sub_apply, globalSymbolInChart]
    rw [hsame _ _ hlen, sub_self]
  have hlocal := isSmoothingSymbol_of_frequency_support isOpen_interior p (L / b₀)
    (hp.mono (Set.prod_mono (interior_subset.trans hK'U) subset_rfl)) hsupp (1 - 1)
  exact hlocal.2 K hKK' hK i j

/-- An invertible degree-one tail supplies an elliptic homogeneous representative
of the same actual full-symbol class. -/
theorem exists_ellipticHomogeneousSymbol_of_degree_one_at_infinity
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F 1)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) (hR : 0 < R)
    (hscale : ∀ x ξ (t : ℝ), 0 < t → R ≤ g.length x ξ →
      R ≤ g.length x (t • ξ) → a.val x (t • ξ) = (t : ℂ) • a.val x ξ)
    (hbij : ∀ x ξ, R ≤ g.length x ξ → Function.Bijective (a.val x ξ)) :
    ∃ b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 1,
      IsEllipticGlobalSymbol E F b.val ∧
      (∀ x ξ, R ≤ g.length x ξ → b.val x ξ = a.val x ξ) ∧
      ∀ A : QuantizationPresentation (n := n) (r := r) (q := q) E F,
        globalPrincipalSymbolClass E F 1 a = globalPrincipalSymbolClass E F 1
          (A.regularizedSymbol 1 b.val b.property.1 b.property.2) := by
  obtain ⟨b, hhigh, hclass⟩ :=
    exists_homogeneousSymbol_of_degree_one_at_infinity a g R hR hscale
  refine ⟨b, ?_, hhigh, hclass⟩
  intro x ξ hξ
  let t := R / g.length x ξ
  have ht : 0 < t := div_pos hR (g.length_pos x ξ hξ)
  have hlength : g.length x (t • ξ) = R := by
    rw [g.length_smul, abs_of_pos ht]
    exact div_mul_cancel₀ R (g.length_pos x ξ hξ).ne'
  have htail : Function.Bijective (b.val x (t • ξ)) := by
    rw [hhigh x (t • ξ) hlength.ge]
    exact hbij x (t • ξ) hlength.ge
  have hscaled : b.val x (t • ξ) = (t : ℂ) • b.val x ξ := by
    simpa only [Real.rpow_one] using b.property.2 x ξ hξ t ht
  have htz : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  let e := LinearEquiv.smulOfNeZero ℂ (F x) (t : ℂ) htz
  -- The nonzero real radial factor changes neither kernel nor surjectivity.
  have hcomp : Function.Bijective (e ∘ b.val x ξ) := by
    have hfun : (b.val x (t • ξ) : E x → F x) = e ∘ b.val x ξ := by
      funext v
      rw [hscaled]
      rfl
    rwa [hfun] at htail
  exact (Function.Bijective.of_comp_iff' e.bijective (b.val x ξ)).mp hcomp

end AtiyahSinger
