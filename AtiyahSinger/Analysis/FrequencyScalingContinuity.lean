/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FrequencyScaling
public import AtiyahSinger.Analysis.GlobalFullSymbolEllipticity
public import AtiyahSinger.Analysis.ParametricQuantization
public import AtiyahSinger.Analysis.SymbolTopology

import all AtiyahSinger.Analysis.SymbolCoordinateEstimates
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Ring

/-!
# Continuity of frequency scaling on positive parameter intervals

Public module ID: M2291.

The same order-zero symbol is continuous in every weighted derivative seminorm when
the frequency scale varies in a closed interval bounded away from zero. A uniform
parameter derivative estimate gives a Lipschitz bound for each seminorm separately.
The spatial compact set and both bundle ranks remain those of the original symbol.
The native cotangent family reads as that same family in every original chart.
Full quantitative ellipticity survives positive scaling, and the original fixed
quantizer yields operator-norm continuity on the same Sobolev spaces.
No assertion of convergence in the symbol topology at zero is made.

Sources: Taylor, *Pseudodifferential Operators*, II.7, p. 53, for the scaled symbol
family and its topology. The explicit positive-interval Lipschitz argument is a project
supplement using the existing parameter-dependent linear frequency substitution estimate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter
open scoped ContDiff Topology

variable {n r q : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

attribute [local instance] symbolTopology

set_option maxHeartbeats 600000 in
-- The nested multilinear derivative restrictions require this local elaboration budget.
/-- On any positive closed parameter interval, every weighted mixed derivative is Lipschitz. -/
theorem IsSymbol.exists_frequencyScale_sub_derivative_bound {a : SymbolFunction n r q}
    (ha : IsSymbol U 0 a) (hU : IsOpen U) (δ : ℝ) (hδ : 0 < δ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ U) (hK : IsCompact K) (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc δ 1, ∀ t ∈ Set.Icc δ 1, ∀ x ∈ K, ∀ ξ,
      ‖symbolDerivative (frequencyScaleSymbol t a - frequencyScaleSymbol s a) i j x ξ‖ ≤
        C * |t - s| * (1 + ‖ξ‖) ^ (-(j : ℝ)) := by
  /- Regard parameter and base point as one variable. The existing substitution
  theorem bounds its complete derivative, uniformly on the same parameter interval
  and spatial compact set. Restrict derivatives to the spatial factor, then use
  the mean value theorem only on the parameter interval; K need not be convex. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let Z := ℝ × X
  let V : Set Z := Set.Ioi 0 ×ˢ U
  let D : Set Z := Set.Icc δ 1 ×ˢ K
  let Θ : Z → X →L[ℝ] X := fun z ↦ z.1 • ContinuousLinearMap.id ℝ X
  have hΘapply (z : Z) (η : X) : Θ z η = z.1 • η := by
    change z.1 • (ContinuousLinearMap.id ℝ X) η = z.1 • η
    rw [ContinuousLinearMap.id_apply]
  have hV : IsOpen V := isOpen_Ioi.prod hU
  have hD : IsCompact D := isCompact_Icc.prod hK
  have hDV : D ⊆ V := fun z hz ↦ ⟨hδ.trans_le hz.1.1, hKU hz.2⟩
  have hΘ : ContDiffOn ℝ ∞ Θ V :=
    (contDiff_fst.smul contDiff_const).contDiffOn
  have hinv : ∀ z ∈ V, (Θ z).IsInvertible := by
    intro z hz
    refine ⟨ContinuousLinearEquiv.smulLeft (Units.mk0 z.1 hz.1.ne'), ?_⟩
    ext v
    simp [Θ]
  obtain ⟨C, hC, hbound⟩ := exists_bound_symbol_comp_linear_frequency U hU 0 a ha V hV
    Prod.snd contDiff_snd.contDiffOn (fun z hz ↦ hz.2) Θ hΘ hinv D hD hDV (i + 1) j
  refine ⟨C, hC, ?_⟩
  -- A spatial cutoff supplies a globally smooth representative of the same germs on K.
  obtain ⟨β, hβ, hβone, hβzero⟩ := exists_symbol_cutoff U K hU hK hKU
  let a' : X → X → H := fun x ξ ↦ β x • a x ξ
  have ha' : ContDiff ℝ ∞ (Function.uncurry a') := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z.1 ∈ U
    · exact (hβ.comp contDiff_fst).contDiffAt.smul
        (ha.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hz, Set.mem_univ _⟩))
    · apply (contDiffAt_const (c := (0 : H))).congr_of_eventuallyEq
      have heq := (hβzero z.1 hz).comp_tendsto continuous_fst.continuousAt
      filter_upwards [heq] with w hw
      change β w.1 = 0 at hw
      simp only [a', Function.uncurry, hw, zero_smul]
  let f : Z → X → H := fun z ξ ↦ a' z.2 (z.1 • ξ)
  have hf : ContDiff ℝ ∞ (Function.uncurry f) :=
    ha'.comp (contDiff_fst.snd.prodMk (contDiff_fst.fst.smul contDiff_snd))
  -- Frequency differentiation of this smooth family remains smooth in both variables.
  have hfreq (k : ℕ) :
      ContDiff ℝ ∞ (fun p : Z × X ↦ iteratedFDeriv ℝ k (f p.1) p.2) := by
    induction k with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ X H).symm : _ →L[ℝ] X [×0]→L[ℝ] H)
    | succ k ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun p : Z × X ↦
            fun η : X ↦ iteratedFDeriv ℝ k (f p.1) η)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun p : Z × X ↦ fderiv ℝ (iteratedFDeriv ℝ k (f p.1)) p.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) H).symm :
          _ →L[ℝ] X [×(k + 1)]→L[ℝ] H)
  intro s hs t ht x hx ξ
  let Y := X [×j]→L[ℝ] H
  let : NormedAddCommGroup Y := inferInstanceAs (NormedAddCommGroup (X [×j]→L[ℝ] H))
  let : NormedSpace ℝ Y := inferInstanceAs (NormedSpace ℝ (X [×j]→L[ℝ] H))
  let F : Z → Y := fun z ↦ iteratedFDeriv ℝ j (f z) ξ
  have hF : ContDiff ℝ ∞ F := (hfreq j).comp (contDiff_id.prodMk contDiff_const)
  have hFi : ContDiff ℝ ∞ (iteratedFDeriv ℝ i F) :=
    hF.iteratedFDeriv_right (by simp)
  have hmeasured (u : ℝ) (hu : u ∈ Set.Icc δ 1) :
      ‖iteratedFDeriv ℝ (i + 1) F (u, x)‖ ≤
        C * (1 + ‖ξ‖) ^ (-(j : ℝ)) := by
    have hlocal : f =ᶠ[𝓝 (u, x)] (fun z η ↦ a z.2 (z.1 • η)) := by
      have hsnd : Tendsto (fun z : Z ↦ z.2) (𝓝 (u, x)) (𝓝 x) :=
        (continuous_snd : Continuous (fun z : Z ↦ z.2)).tendsto (u, x)
      have heq := (hβone x hx).comp_tendsto hsnd
      filter_upwards [heq] with z hz
      change β z.2 = 1 at hz
      funext η
      simp only [f, a', hz, one_smul]
    have hder : F =ᶠ[𝓝 (u, x)]
        (fun z ↦ iteratedFDeriv ℝ j (fun η ↦ a z.2 (z.1 • η)) ξ) := by
      filter_upwards [hlocal] with z hz
      change iteratedFDeriv ℝ j (f z) ξ = _
      rw [hz]
    rw [(hder.iteratedFDeriv ℝ (i + 1)).eq_of_nhds]
    have hb := hbound (u, x) ⟨hu, hx⟩ ξ
    simp_rw [hΘapply] at hb
    simpa only [zero_sub] using hb
  -- Extract the original spatial derivative by a fixed norm-at-most-one inclusion.
  let L : X →L[ℝ] Z := ContinuousLinearMap.inr ℝ ℝ X
  let T : (Z [×i]→L[ℝ] Y) →L[ℝ] (X [×i]→L[ℝ] Y) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i ↦ L)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro v
    change ‖((0, v) : Z)‖ ≤ 1 * ‖v‖
    simp only [Prod.norm_mk, norm_zero, one_mul, sup_le_iff, Std.le_refl, and_true]
    exact norm_nonneg v
  have hT : ‖T‖ ≤ 1 :=
    (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le Y _).trans
      (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hL))
  have hspatial (u : ℝ) :
      symbolDerivative (frequencyScaleSymbol u a') i j x ξ =
        T (iteratedFDeriv ℝ i F (u, x)) := by
    let g : Z → Y := fun z ↦ F ((u, 0) + z)
    have hg : ContDiff ℝ ∞ g := hF.comp (contDiff_const.add contDiff_id)
    have hshift (y : X) : (u, 0) + L y = (u, y) := by
      change ((u, 0) + (0, y) : Z) = (u, y)
      exact Prod.fst_add_snd (u, y)
    have heq : (fun y ↦ iteratedFDeriv ℝ j (frequencyScaleSymbol u a' y) ξ) =
        g ∘ L := by
      funext y
      change iteratedFDeriv ℝ j (fun η ↦ a' y (u • η)) ξ =
        iteratedFDeriv ℝ j (f ((u, 0) + L y)) ξ
      rw [hshift]
    have hG : iteratedFDeriv ℝ i g (L x) = iteratedFDeriv ℝ i F (u, x) := by
      change iteratedFDeriv ℝ i (fun z : Z ↦ F ((u, 0) + z)) (L x) = _
      rw [iteratedFDeriv_comp_add_left, hshift]
    have hleft : symbolDerivative (frequencyScaleSymbol u a') i j x ξ =
        iteratedFDeriv ℝ i (g ∘ L) x :=
      congrArg (fun k : X → Y ↦ iteratedFDeriv ℝ i k x) heq
    have hright : iteratedFDeriv ℝ i (g ∘ L) x = T (iteratedFDeriv ℝ i F (u, x)) := by
      have hc := L.iteratedFDeriv_comp_right hg x (i := i) (by simp)
      rw [hG] at hc
      exact hc
    exact hleft.trans hright
  -- A parameter derivative is another restriction of the same complete derivative.
  let R : ℝ →L[ℝ] Z := ContinuousLinearMap.inl ℝ ℝ X
  have hR : ‖R‖ ≤ 1 := by
    apply R.opNorm_le_bound zero_le_one
    intro v
    change ‖((v, 0) : Z)‖ ≤ 1 * ‖v‖
    simp
  have hparam (u : ℝ) :
      ‖fderiv ℝ (fun v ↦ iteratedFDeriv ℝ i F (v, x)) u‖ ≤
        ‖iteratedFDeriv ℝ (i + 1) F (u, x)‖ := by
    let g : Z → Z [×i]→L[ℝ] Y := fun z ↦ iteratedFDeriv ℝ i F ((0, x) + z)
    have hg : ContDiff ℝ ∞ g := hFi.comp (contDiff_const.add contDiff_id)
    have hshift (v : ℝ) : (0, x) + R v = (v, x) := by
      change ((0, x) + (v, 0) : Z) = (v, x)
      rw [add_comm]
      exact Prod.fst_add_snd (v, x)
    have heq : (fun v ↦ iteratedFDeriv ℝ i F (v, x)) = g ∘ R := by
      funext v
      change iteratedFDeriv ℝ i F (v, x) = iteratedFDeriv ℝ i F ((0, x) + R v)
      rw [hshift]
    rw [heq, _root_.fderiv_comp (𝕜 := ℝ) (f := (R : ℝ → Z)) (g := g) u
      (hg.differentiable (by simp) (R u)) R.differentiableAt, R.fderiv]
    calc
      _ ≤ ‖fderiv ℝ g (R u)‖ * ‖R‖ := (fderiv ℝ g (R u)).opNorm_comp_le R
      _ ≤ ‖fderiv ℝ g (R u)‖ := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hR (norm_nonneg (fderiv ℝ g (R u)))
      _ = ‖iteratedFDeriv ℝ (i + 1) F (u, x)‖ := by
        rw [fderiv_comp_add_left, norm_fderiv_iteratedFDeriv]
        rw [hshift]
  have hpath : ContDiff ℝ ∞ (fun v ↦ iteratedFDeriv ℝ i F (v, x)) :=
    hFi.comp (contDiff_id.prodMk contDiff_const)
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun u _ ↦ hpath.differentiable (by simp) u)
    (fun u hu ↦ (hparam u).trans (hmeasured u hu)) (convex_Icc δ 1) hs ht
  -- The cutoff changed no germ on K, including those of the difference being measured.
  have hlocalSub :
      (fun y ↦ iteratedFDeriv ℝ j
        ((frequencyScaleSymbol t a - frequencyScaleSymbol s a) y) ξ) =ᶠ[𝓝 x]
      (fun y ↦ iteratedFDeriv ℝ j
        ((frequencyScaleSymbol t a' - frequencyScaleSymbol s a') y) ξ) := by
    filter_upwards [hβone x hx] with y hy
    have heq : (frequencyScaleSymbol t a - frequencyScaleSymbol s a) y =
        (frequencyScaleSymbol t a' - frequencyScaleSymbol s a') y := by
      funext η
      simp only [frequencyScaleSymbol, Pi.sub_apply, a', hy, one_smul]
    rw [heq]
  have hslice (u : ℝ) (y : X) : ContDiff ℝ ∞ (frequencyScaleSymbol u a' y) :=
    ha'.comp (contDiff_const.prodMk (contDiff_id.const_smul u))
  have hdiffFreq (y : X) :
      iteratedFDeriv ℝ j ((frequencyScaleSymbol t a' - frequencyScaleSymbol s a') y) ξ =
        iteratedFDeriv ℝ j (frequencyScaleSymbol t a' y) ξ -
          iteratedFDeriv ℝ j (frequencyScaleSymbol s a' y) ξ :=
    iteratedFDeriv_sub_apply ((hslice t y).contDiffAt.of_le (by simp))
      ((hslice s y).contDiffAt.of_le (by simp))
  have hsmoothSpatial (u : ℝ) :
      ContDiff ℝ ∞ (fun y ↦ iteratedFDeriv ℝ j (frequencyScaleSymbol u a' y) ξ) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
  rw [(hlocalSub.iteratedFDeriv ℝ i).eq_of_nhds]
  simp_rw [hdiffFreq]
  change ‖iteratedFDeriv ℝ i
    ((fun y : X ↦ iteratedFDeriv ℝ j (frequencyScaleSymbol t a' y) ξ) -
      (fun y : X ↦ iteratedFDeriv ℝ j (frequencyScaleSymbol s a' y) ξ)) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply ((hsmoothSpatial t).contDiffAt.of_le (by simp))
    ((hsmoothSpatial s).contDiffAt.of_le (by simp))]
  change ‖symbolDerivative (frequencyScaleSymbol t a') i j x ξ -
    symbolDerivative (frequencyScaleSymbol s a') i j x ξ‖ ≤ _
  have hTsub : T (iteratedFDeriv ℝ i F (t, x) - iteratedFDeriv ℝ i F (s, x)) =
      T (iteratedFDeriv ℝ i F (t, x)) - T (iteratedFDeriv ℝ i F (s, x)) := by
    ext v
    rfl
  rw [hspatial t, hspatial s, ← hTsub]
  calc
    _ ≤ ‖T‖ * ‖iteratedFDeriv ℝ i F (t, x) - iteratedFDeriv ℝ i F (s, x)‖ :=
      T.le_opNorm _
    _ ≤ ‖iteratedFDeriv ℝ i F (t, x) - iteratedFDeriv ℝ i F (s, x)‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    _ ≤ C * (1 + ‖ξ‖) ^ (-(j : ℝ)) * ‖t - s‖ := hmv
    _ = C * |t - s| * (1 + ‖ξ‖) ^ (-(j : ℝ)) := by
      rw [Real.norm_eq_abs]
      ring

/-- Positive contraction of the existing symbol, bundled in the same order-zero carrier. -/
def frequencyScaleSymbolSpace (hU : IsOpen U) (a : symbolSpace U hU 0 r q)
    (t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1) : symbolSpace U hU 0 r q :=
  ⟨frequencyScaleSymbol t a.val, a.property.frequencyScale t ht ht₁⟩

/-- The complete weighted symbol topology sees positive frequency scaling continuously. -/
theorem continuous_frequencyScaleSymbolSpace (hU : IsOpen U)
    (a : symbolSpace U hU 0 r q) (δ : ℝ) (hδ : 0 < δ) :
    Continuous (fun t : ↥(Set.Icc δ 1) ↦
      frequencyScaleSymbolSpace hU a t.val (hδ.trans_le t.property.1) t.property.2) := by
  /- For each seminorm, choose its uniform Lipschitz constant before varying the
  parameter. The scalar bound tends to zero at every positive interval point,
  and the seminorm-of-differences criterion gives the full symbol convergence. -/
  classical
  rw [continuous_iff_continuousAt]
  intro s
  apply (tendsto_symbolTopology_iff hU 0 (𝓝 s) _ _).mpr
  intro J ε hε
  obtain ⟨C, hC, hbound⟩ := a.property.exists_frequencyScale_sub_derivative_bound hU δ hδ
    J.compactSet J.subset_domain J.isCompact J.spatialOrder J.frequencyOrder
  have hcont : Continuous (fun t : ↥(Set.Icc δ 1) ↦ C * |t.val - s.val|) :=
    continuous_const.mul ((continuous_subtype_val.sub continuous_const).abs)
  have hevent : ∀ᶠ t : ↥(Set.Icc δ 1) in 𝓝 s, C * |t.val - s.val| < ε :=
    (isOpen_lt hcont continuous_const).mem_nhds (by
      change C * |s.val - s.val| < ε
      simpa only [sub_self, abs_zero, mul_zero] using hε)
  filter_upwards [hevent] with t ht
  apply lt_of_le_of_lt ?_ ht
  change symbolSeminormValue hU 0 J _ ≤ C * |t.val - s.val|
  by_cases hnonempty : J.compactSet.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hnonempty
    unfold symbolSeminormValue
    refine csSup_le ⟨_, x₀, hx₀, 0, rfl⟩ ?_
    rintro v ⟨x, hx, ξ, rfl⟩
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr
    simpa only [frequencyScaleSymbolSpace, Submodule.coe_sub, zero_sub]
      using hbound s.val s.property t.val t.property x hx ξ
  · have hempty := Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [symbolSeminormValue, hempty, Set.mem_empty_iff_false, false_and,
      exists_false, Set.ofPred_false, Real.sSup_empty]
    exact mul_nonneg hC (abs_nonneg _)


/-- Positive scaling preserves order-zero quantitative ellipticity on the same base domain. -/
theorem IsEllipticFullSymbol.frequencyScale {a : SymbolFunction n r q}
    (ha : IsEllipticFullSymbol U 0 a) (t : ℝ) (ht : 0 < t) :
    IsEllipticFullSymbol U 0 (frequencyScaleSymbol t a) := by
  /- The original exterior radius is divided by the same positive parameter.
  At order zero the original inverse bound has no changing frequency weight. -/
  intro K hKU hK
  obtain ⟨R, C, hR, hC, hbound⟩ := ha K hKU hK
  refine ⟨R / t, C, div_pos hR ht, hC, ?_⟩
  intro x hx ξ hξ
  have hlarge : R ≤ ‖t • ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    simpa only [mul_comm] using (div_le_iff₀ ht).mp hξ
  obtain ⟨hinv, hb⟩ := hbound x hx (t • ξ) hlarge
  refine ⟨hinv, ?_⟩
  simpa only [frequencyScaleSymbol, neg_zero, Real.rpow_zero, mul_one] using hb

open Bundle MeasureTheory
open scoped Manifold

variable {M : Type*} [TopologicalSpace M]
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

attribute [local instance] globalSymbolTopology
  GlobalSymbolSeminormIndex.input_mem_atlas GlobalSymbolSeminormIndex.output_mem_atlas

/-- Frequency scaling in each original native cotangent fiber. -/
def frequencyScaleGlobalSymbol (t : ℝ) (a : GlobalSymbolFunction (n := n) E F) :
    GlobalSymbolFunction (n := n) E F := fun x ξ ↦ a x (t • ξ)

/-- Native frequency scaling reads as the same scaling in each original chart and frame. -/
theorem globalSymbolInChart_frequencyScale (t : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    globalSymbolInChart E F (frequencyScaleGlobalSymbol t a) c e f =
      frequencyScaleSymbol t (globalSymbolInChart E F a c e f) := by
  /- The original chart derivative pulls coordinate covectors back linearly.
  Scaling that same covector commutes with both fixed original bundle frames. -/
  funext z η
  have hcov : covectorFromChart c (c.symm z) (t • η) =
      t • covectorFromChart c (c.symm z) η := by
    ext v
    change inner ℝ (t • η)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c (c.symm z) v) =
      t * inner ℝ η
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c (c.symm z) v)
    exact real_inner_smul_left _ _ _
  change (f.continuousLinearMapAt ℂ (c.symm z)).comp
      ((a (c.symm z) (t • covectorFromChart c (c.symm z) η)).comp
        (e.symmL ℂ (c.symm z))) =
    (f.continuousLinearMapAt ℂ (c.symm z)).comp
      ((a (c.symm z) (covectorFromChart c (c.symm z) (t • η))).comp
        (e.symmL ℂ (c.symm z)))
  rw [hcov]

/-- Positive native contractions preserve the original global order-zero symbol estimates. -/
theorem IsGlobalSymbol.frequencyScale {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsGlobalSymbol (r := r) (q := q) E F 0 a)
    (t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1) :
    IsGlobalSymbol (r := r) (q := q) E F 0 (frequencyScaleGlobalSymbol t a) := by
  intro c hc e f he hf
  rw [globalSymbolInChart_frequencyScale]
  exact (ha c hc e f).frequencyScale t ht ht₁

/-- The original generally elliptic global symbol remains elliptic at every positive scale. -/
theorem IsEllipticFullGlobalSymbol.frequencyScale {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F 0 a)
    (t : ℝ) (ht : 0 < t) :
    IsEllipticFullGlobalSymbol (r := r) (q := q) E F 0 (frequencyScaleGlobalSymbol t a) := by
  intro c hc e f he hf
  rw [globalSymbolInChart_frequencyScale]
  exact (ha c hc e f).frequencyScale t ht

/-- The native scaled symbol belongs to the same original global order-zero carrier. -/
def frequencyScaleGlobalSymbolSpace
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1) :
    globalSymbolSpace (n := n) (r := r) (q := q) E F 0 :=
  ⟨frequencyScaleGlobalSymbol t a.val, a.property.frequencyScale t ht ht₁⟩

/-- Native scaling is continuous in all actual chartwise weighted symbol seminorms. -/
theorem continuous_frequencyScaleGlobalSymbolSpace
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (δ : ℝ) (hδ : 0 < δ) :
    Continuous (fun t : ↥(Set.Icc δ 1) ↦
      frequencyScaleGlobalSymbolSpace a t.val (hδ.trans_le t.property.1) t.property.2) := by
  /- A fixed original chart reads exactly the already controlled local family.
  Its seminorm of a difference is precisely the defining pulled-back global seminorm.
  Test every global chart index, with both original frames and the same compact set. -/
  rw [continuous_iff_continuousAt]
  intro s
  apply (tendsto_globalSymbolTopology_iff E F 0 (𝓝 s) _ _).mpr
  intro J ε hε
  let hU := isOpen_symbolChartDomain E F J.chart J.inputFrame J.outputFrame
  let b := globalSymbolInChartSpace E F 0 a J.chart J.mem_atlas
    J.inputFrame J.outputFrame
  have hlocal : Continuous (fun t : ↥(Set.Icc δ 1) ↦
      frequencyScaleSymbolSpace hU b t.val (hδ.trans_le t.property.1) t.property.2) :=
    continuous_frequencyScaleSymbolSpace hU b δ hδ
  have heq (t : ↥(Set.Icc δ 1)) :
      globalSymbolInChartLinearMap E F 0 J
        (frequencyScaleGlobalSymbolSpace a t.val
          (hδ.trans_le t.property.1) t.property.2) =
      frequencyScaleSymbolSpace hU b t.val (hδ.trans_le t.property.1) t.property.2 := by
    apply Subtype.ext
    exact globalSymbolInChart_frequencyScale t.val a.val J.chart J.inputFrame J.outputFrame
  have hevent := ((tendsto_symbolTopology_iff hU 0 (𝓝 s) _ _).mp
    (hlocal.continuousAt (x := s)).tendsto) J.localIndex ε hε
  filter_upwards [hevent] with t ht
  change symbolSeminorm hU 0 J.localIndex
      (globalSymbolInChartLinearMap E F 0 J
        (frequencyScaleGlobalSymbolSpace a t.val (hδ.trans_le t.property.1) t.property.2 -
          frequencyScaleGlobalSymbolSpace a s.val (hδ.trans_le s.property.1)
            s.property.2)) < ε
  rw [map_sub (globalSymbolInChartLinearMap E F 0 J), heq t, heq s]
  exact ht

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ in
/-- The same fixed quantizer yields operator-norm continuity on each positive interval. -/
theorem QuantizationPresentation.continuous_sobolevQuantization_frequencyScale
    (C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) (s : ℝ)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (δ : ℝ) (hδ : 0 < δ) :
    Continuous (fun t : ↥(Set.Icc δ 1) ↦
      (C.quantize μ (frequencyScaleGlobalSymbolSpace a t.val
        (hδ.trans_le t.property.1) t.property.2)).sobolevExtension A B s) := by
  /- The original quantization map is continuous from the complete symbol topology
  into the original bounded Sobolev operators. Compose it with the same scaled family. -/
  exact C.continuous_sobolevQuantization μ A B s 0 _
    (continuous_frequencyScaleGlobalSymbolSpace a δ hδ)

end AtiyahSinger
