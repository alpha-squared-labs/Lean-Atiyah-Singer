/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FourierCircle

/-!
# Period-one angular coordinates in the original circle atlas

Public module ID: M1123.

The positive covering t ↦ exp(2πit), restricted between two consecutive lifts
of a deleted pole, is compared with any original stereographic circle chart.
The resulting Euclidean coordinate change and its inverse are smooth in the
original atlas. This provides the genuine coordinate change for local periodic
Fourier symbols; the angular chart is not substituted into the native atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Function Metric
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 1200000 in
-- The inverse chart is recovered through the nonvanishing original angular velocity.
/-- Every native circle chart has a compatible positive period-one angular chart. -/
theorem exists_circlePeriodOneChart
    (c : OpenPartialHomeomorph Circle (EuclideanSpace ℝ (Fin 1)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin 1)) Circle) :
    let l : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ :=
      (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
    ∃ (a : ℝ) (b : OpenPartialHomeomorph ℝ Circle),
      (∀ t : ℝ, b t = Circle.exp (2 * Real.pi * t)) ∧
      b.source = Ioo a (a + 1) ∧ b.target = c.source ∧
      let e := l.toHomeomorph.toOpenPartialHomeomorph.trans (b.trans c)
      e.source = l ⁻¹' Ioo a (a + 1) ∧ e.target = univ ∧
      (∀ x, e x = c (Circle.exp (2 * Real.pi * l x))) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiff ℝ ∞ e.symm := by
  classical
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  change ∃ v : sphere (0 : ℂ) 1, c = stereographic' 1 v at hc
  obtain ⟨v, rfl⟩ := hc
  let X := EuclideanSpace ℝ (Fin 1)
  let I := 𝓘(ℝ, X)
  let c : OpenPartialHomeomorph Circle X := stereographic' 1 v
  let l : X ≃ₗᵢ[ℝ] ℝ := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let a : ℝ := Complex.arg (v : ℂ) / (2 * Real.pi)
  let b : OpenPartialHomeomorph ℝ Circle :=
    (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).trans
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).toOpenPartialHomeomorph
  have hbfun (t : ℝ) : b t = Circle.exp (2 * Real.pi * t) := by
    change AddCircle.homeomorphCircle one_ne_zero (t : AddCircle (1 : ℝ)) = _
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, div_one]
  have hbS : b.source = Ioo a (a + 1) := by simp [b]
  have hbT : b.target = c.source := by
    ext z
    simp only [b, OpenPartialHomeomorph.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target, mem_inter_iff, mem_univ, true_and,
      AddCircle.openPartialHomeomorphCoe_target, mem_preimage, mem_compl_iff,
      mem_singleton_iff, Homeomorph.toOpenPartialHomeomorph_symm_apply]
    change (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z ≠
      (a : AddCircle (1 : ℝ)) ↔ z ∈ c.source
    have hpole : AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero a = (v : Circle) := by
      rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, div_one]
      have hperiod : 2 * Real.pi ≠ 0 := by positivity
      rw [show 2 * Real.pi * a = Complex.arg (v : ℂ) from
        mul_div_cancel₀ _ hperiod]
      exact Circle.exp_arg (v : Circle)
    have heq : (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z =
        (a : AddCircle (1 : ℝ)) ↔ z = (v : Circle) := by
      constructor
      · intro hz
        have hh := congrArg (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) hz
        exact ((AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z).symm.trans
          (hh.trans hpole)
      · intro hz
        rw [hz, ← hpole, Homeomorph.symm_apply_apply]
    simp only [c, stereographic'_source]
    exact not_congr heq
  -- First work in the scalar native coordinate, where the ordinary inverse theorem applies.
  let d : OpenPartialHomeomorph ℝ ℝ :=
    (b.trans c).trans l.toHomeomorph.toOpenPartialHomeomorph
  have hdfun (t : ℝ) : d t = l (c (Circle.exp (2 * Real.pi * t))) := by
    change l (c (b t)) = _
    rw [hbfun]
  have hdS : d.source = Ioo a (a + 1) := by
    ext t
    simp only [d, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      Homeomorph.toOpenPartialHomeomorph_source, mem_univ, and_true]
    constructor
    · exact fun ht ↦ hbS ▸ ht.1
    · intro ht
      have htb : t ∈ b.source := hbS.symm ▸ ht
      exact ⟨htb, hbT ▸ b.map_source htb⟩
  have hdT : d.target = univ := by
    ext z
    simp only [d, OpenPartialHomeomorph.trans_target, mem_inter_iff, mem_preimage,
      Homeomorph.toOpenPartialHomeomorph_target, mem_univ, true_and]
    change l.symm z ∈ c.target ∧ c.symm (l.symm z) ∈ b.target ↔ True
    simp only [c, stereographic'_target, mem_univ, true_and, iff_true]
    rw [hbT]
    exact c.map_target (by simp [c])
  have hdsmooth (t : ℝ) (ht : t ∈ d.source) : ContDiffAt ℝ ∞ d t := by
    have htb : t ∈ b.source := hbS.symm ▸ (hdS ▸ ht)
    have htc : Circle.exp (2 * Real.pi * t) ∈ c.source := by
      rw [← hbfun, ← hbT]
      exact b.map_source htb
    have hchart := contMDiffOn_of_mem_maximalAtlas
      (I := I) (n := (∞ : ℕ∞ω))
      (IsManifold.subset_maximalAtlas (show c ∈ atlas X Circle from ⟨v, rfl⟩))
    have hcc := (hchart _ htc).contMDiffAt (c.open_source.mem_nhds htc)
    have hscale : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ 2 * Real.pi * t) :=
      (contDiff_const.mul contDiff_id).contMDiff
    have hcover := contMDiff_circleExp.comp hscale
    have hlocal := l.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff
      |>.contMDiffAt.comp t (hcc.comp t hcover.contMDiffAt)
    apply (contMDiffAt_iff_contDiffAt.mp hlocal).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall hdfun
  let p (z : ℝ) : ℂ := (c.symm (l.symm z) : ℂ)
  have hpsmooth : ContDiff ℝ ∞ p := by
    have hchart := contMDiffOn_symm_of_mem_maximalAtlas
      (I := I) (n := (∞ : ℕ∞ω))
      (IsManifold.subset_maximalAtlas (show c ∈ atlas X Circle from ⟨v, rfl⟩))
    have hcu : ContMDiff I I ∞ c.symm := by
      apply contMDiffOn_univ.mp
      simpa [c] using hchart
    exact contMDiff_iff_contDiff.mp
      (contMDiff_coe_sphere.comp
        (hcu.comp l.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff))
  have hnonzero (t : ℝ) (ht : t ∈ d.source) : deriv d t ≠ 0 := by
    have hdder := (hdsmooth t ht).differentiableAt (by simp)
    have hchain := (hpsmooth.differentiable (by simp) (d t)).hasDerivAt.scomp t
      hdder.hasDerivAt
    have hsame : (p ∘ d) =ᶠ[𝓝 t] fun s : ℝ ↦
        Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) := by
      filter_upwards [d.open_source.mem_nhds ht] with s hs
      have hsc : Circle.exp (2 * Real.pi * s) ∈ c.source := by
        rw [← hbfun, ← hbT]
        exact b.map_source (hbS.symm ▸ (hdS ▸ hs))
      simp only [comp_apply, p, hdfun, l.symm_apply_apply, c.left_inv hsc, Circle.coe_exp]
    have hexp := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul
      ((2 * Real.pi : ℝ) : ℂ)).mul_const Complex.I).cexp
    have heq := (hchain.congr_of_eventuallyEq hsame.symm).unique
      (by simpa only [Complex.ofRealCLM_apply, Complex.ofReal_mul, mul_one] using hexp)
    intro hz
    simp only [hz, zero_smul] at heq
    have hperiod : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (by positivity :
      0 < (2 * Real.pi : ℝ))
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_one, mul_one]
      at heq hperiod
    exact (mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero hperiod Complex.I_ne_zero)) heq.symm
  have hgsmooth : ContDiff ℝ ∞ d.symm := by
    rw [contDiff_iff_contDiffAt]
    intro z
    have hzt : z ∈ d.target := hdT.symm ▸ mem_univ z
    have hzs := d.map_target hzt
    exact d.contDiffAt_symm_deriv (hnonzero _ hzs) hzt
      ((hdsmooth _ hzs).differentiableAt (by simp)).hasDerivAt (hdsmooth _ hzs)
  -- Return to the actual one-dimensional Euclidean model on both sides.
  let e := l.toHomeomorph.toOpenPartialHomeomorph.trans (b.trans c)
  have heS : e.source = l ⁻¹' Ioo a (a + 1) := by
    ext x
    simp only [e, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, mem_inter_iff, mem_univ, true_and,
      mem_preimage, Homeomorph.toOpenPartialHomeomorph_apply]
    change l x ∈ b.source ∧ b (l x) ∈ c.source ↔ l x ∈ Ioo a (a + 1)
    rw [← hbS]
    exact and_iff_left_of_imp (fun hx ↦ hbT ▸ b.map_source hx)
  have heT : e.target = univ := by
    ext x
    simp only [e, OpenPartialHomeomorph.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target, mem_inter_iff, mem_univ, and_true,
      mem_preimage]
    change x ∈ c.target ∧ c.symm x ∈ b.target ↔ True
    simp only [c, stereographic'_target, mem_univ, true_and, iff_true]
    rw [hbT]
    exact c.map_target (by simp [c])
  have hefun (x : X) : e x = l.symm (d (l x)) := by
    change c (b (l x)) = l.symm (l (c (b (l x))))
    exact (l.symm_apply_apply _).symm
  have hesym (x : X) : e.symm x = l.symm (d.symm (l x)) := by
    change l.symm (b.symm (c.symm x)) = l.symm (b.symm (c.symm (l.symm (l x))))
    rw [l.symm_apply_apply]
  refine ⟨a, b, hbfun, hbS, hbT, heS, heT, ?_, ?_, ?_⟩
  · intro x
    change c (b (l x)) = _
    rw [hbfun]
  · intro x hx
    have hx' : l x ∈ Ioo a (a + 1) := by
      exact (heS ▸ hx : x ∈ l ⁻¹' Ioo a (a + 1))
    have hdx : l x ∈ d.source := hdS.symm ▸ hx'
    have hcompose := l.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp x
      ((hdsmooth _ hdx).comp x l.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt)
    exact (hcompose.congr_of_eventuallyEq (Filter.Eventually.of_forall hefun)).contDiffWithinAt
  · change ContDiff ℝ ∞ e.symm
    rw [show (e.symm : X → X) = (fun x : X ↦ l.symm (d.symm (l x))) from funext hesym]
    exact l.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
      (hgsmooth.comp l.toContinuousLinearEquiv.toContinuousLinearMap.contDiff)

end AtiyahSinger
