/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolTopology
public import AtiyahSinger.Analysis.AtlasParametricQuantization

import AtiyahSinger.Analysis.CosphereRegularity
import AtiyahSinger.Analysis.SymbolCoordinateEstimates

/-!
# Fixed regularization and quantization of homogeneous atlas families

Public module ID: M0248.

A03: the existing metric radial cutoff is linear and continuous from the
standard punctured smooth topology to the full order-m symbol topology.
The estimate is a theorem about independently defined derivative seminorms,
not a topology declared to make regularization continuous. Composing with
one fixed atlas quantizer gives the same original bounded Sobolev operators.

Sources: SG III.3, III.7.10--7.11 and III.13 (13.5). The explicit finite-seminorm
bounds are project supplements spelling out the parameter-control argument.
Linearity and the uniform continuity estimates retain the specified radial cutoff.
The fixed quantizer's principal-class theorem uses representation independence.
No ellipticity or density is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Set
open scoped Manifold ContDiff Topology NNReal

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [hT : T2Space M]
  (g : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ)

attribute [local instance] atlasHomogeneousSymbolTopology atlasGlobalSymbolTopology

/-- The already specified radial regularization is linear in its actual homogeneous field. -/
theorem atlasRegularizedSymbol_linear :
    IsLinearMap ℂ (fun a : homogeneousAtlasSymbolSpace A B m ↦
      atlasRegularizedSymbol A B g m a.val a.property.1 a.property.2) := by
  /- The cutoff is fixed independently of a. Distribute its scalar through
  sums and commute it with complex scalar multiplication in the original
  fiber maps, then use subtype extensionality. No choice of symbol or metric
  is made depending on the input. -/
  constructor
  · intro a b
    apply Subtype.ext
    funext x ξ
    exact smul_add _ _ _
  · intro z a
    apply Subtype.ext
    funext x ξ
    dsimp only [atlasRegularizedSymbol, atlasRegularizedSymbolFunction]
    exact smul_comm
      (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (g.length x ξ)) : ℂ)
      z (a.val x ξ)

/-- The actual radial-cutoff formula packaged as a linear map. -/
def atlasRegularizationLinearMap :
    homogeneousAtlasSymbolSpace A B m →ₗ[ℂ] atlasGlobalSymbolSpace A B m :=
  IsLinearMap.mk' (fun a ↦ atlasRegularizedSymbol A B g m a.val a.property.1 a.property.2)
    (atlasRegularizedSymbol_linear A B g m)

set_option maxHeartbeats 1600000 in
-- The extended limit accommodates the uniform derivative and full-symbol seminorm estimates.
include hM hT in
/-- Every full-symbol seminorm has a uniform finite bound by punctured smooth seminorms. -/
theorem exists_atlasRegularization_seminorm_bound (J : AtlasGlobalSymbolSeminormIndex A B) :
    ∃ (I : Finset (AtlasHomogeneousSymbolSeminormIndex A B)) (K : ℝ≥0),
      ∀ a : homogeneousAtlasSymbolSpace A B m,
        atlasGlobalSymbolSeminorm A B m J (atlasRegularizationLinearMap A B g m a) ≤
          (K : ℝ) * (I.sup (atlasHomogeneousSymbolSeminorm A B m)) a := by
  /- Stage 1: on the fixed compact base set, positive definiteness compares
  metric length with coordinate frequency norm uniformly. The cutoff kills
  all sufficiently small frequencies, without conditions on a at zero.
  Stage 2: differentiate the fixed radial cutoff and a. On its transition
  annulus all derivatives are controlled by compact punctured seminorms.
  Outside this annulus differentiated homogeneity reduces each term to
  such compact data with the precise order m minus frequency-order weight.
  Stage 3: the finite Leibniz and chain-rule terms determine I and K before
  a. Divide by the target weight and take suprema. For n=0 the cutoff
  regularization is zero and the estimate holds with K=0. -/
  classical
  have cutoffProperties
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) (j : B.Index)
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hKU : K ⊆ atlasSymbolChartDomain A B c i j) :
      ∃ χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiffOn ℝ ∞ χ (atlasSymbolChartDomain A B c i j ×ˢ Set.univ) ∧
        (∀ a : AtlasSymbolFunction (n := n) E F, ∀ z η,
          atlasGlobalSymbolInChart A B (atlasRegularizedSymbolFunction g a) c i j z η =
            (χ (z, η) : ℂ) • atlasGlobalSymbolInChart A B a c i j z η) ∧
        (∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ K, ∀ η, ‖η‖ ≤ ε → χ (z, η) = 0) ∧
        (∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ η, R ≤ ‖η‖ → χ (z, η) = 1) := by
    let V := atlasSymbolChartDomain A B c i j
    let L (z η : EuclideanSpace ℝ (Fin n)) :=
      g.length (c.symm z) (covectorFromChart c (c.symm z) η)
    let χ (z η : EuclideanSpace ℝ (Fin n)) :=
      highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (L z η))
    have hV : IsOpen V := isOpen_atlasSymbolChartDomain A B c i j
    have hcov_smul (z η : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
        covectorFromChart c (c.symm z) (t • η) = t • covectorFromChart c (c.symm z) η := by
      ext v
      change inner ℝ (t • η) (mfderiv _ _ c (c.symm z) v) =
        t * inner ℝ η (mfderiv _ _ c (c.symm z) v)
      exact real_inner_smul_left η _ t
    have hcov_ne (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
        (η : EuclideanSpace ℝ (Fin n)) (hη : η ≠ 0) :
        covectorFromChart c (c.symm z) η ≠ 0 := by
      intro hzero
      have h := covectorInChart_covectorFromChart c hc (c.symm z) (c.map_target hz) η
      rw [hzero] at h
      have hzero' : covectorInChart c (c.symm z) 0 = 0 := by ext k; rfl
      exact hη (h.symm.trans hzero')
    have hL_smul (z η : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
        L z (t • η) = |t| * L z η := by
      dsimp [L]
      rw [hcov_smul, g.length_smul]
    have hL_zero (z : EuclideanSpace ℝ (Fin n)) : L z 0 = 0 := by
      dsimp [L]
      have hz : covectorFromChart c (c.symm z) 0 = 0 := by
        ext v
        change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (mfderiv _ _ c (c.symm z) v) = 0
        exact inner_zero_left _
      rw [hz]
      exact (g.length_eq_zero_iff _ _).mpr rfl
    have hL_smooth : ContDiffOn ℝ ∞ (Function.uncurry L) (c.target ×ˢ {η | η ≠ 0}) :=
      g.contDiffOn_length_covectorFromChart c hc
    -- Compact coordinate spheres give uniform lower and upper metric bounds.
    have hbounds (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
        (hKc : K ⊆ c.target) :
        ∃ b B : ℝ, 0 < b ∧ 0 < B ∧ ∀ z ∈ K, ∀ η,
          b * ‖η‖ ≤ L z η ∧ L z η ≤ B * ‖η‖ := by
      let S := K ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
      have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
      have hne (η : EuclideanSpace ℝ (Fin n))
          (hη : η ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : η ≠ 0 := by
        intro hz
        simp [hz] at hη
      have hcont : ContinuousOn (Function.uncurry L) S := hL_smooth.continuousOn.mono
        (fun z hz ↦ ⟨hKc hz.1, hne z.2 hz.2⟩)
      obtain ⟨b, hb, hlow⟩ := hS.exists_forall_le' hcont (a := 0) (by
        intro z hz
        exact g.length_pos _ _ (hcov_ne z.1 (hKc hz.1) z.2 (hne z.2 hz.2)))
      obtain ⟨B, hupper⟩ := (hS.image_of_continuousOn hcont).bddAbove
      refine ⟨b, max B 1, hb, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
      intro z hz η
      by_cases hη : η = 0
      · subst η
        simp only [norm_zero, mul_zero, hL_zero, le_refl, and_self]
      let v := ‖η‖⁻¹ • η
      have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hη
      have hscale : ‖η‖ • v = η := by simp [v, smul_smul, norm_ne_zero_iff.mpr hη]
      have hlen : L z η = ‖η‖ * L z v := by
        conv_lhs => rw [← hscale, hL_smul]
        rw [abs_of_nonneg (norm_nonneg η)]
      rw [hlen]
      constructor
      · simpa only [Function.uncurry, mul_comm] using
          mul_le_mul_of_nonneg_left (hlow (z, v) ⟨hz, hv⟩) (norm_nonneg η)
      · have hbound := (hupper ⟨(z, v), ⟨hz, hv⟩, rfl⟩).trans (le_max_left B 1)
        simpa only [Function.uncurry, mul_comm] using
          mul_le_mul_of_nonneg_left hbound (norm_nonneg η)
    have hχnorm (z η : EuclideanSpace ℝ (Fin n)) :
        ‖EuclideanSpace.single (0 : Fin 1) (L z η)‖ = L z η := by
      rw [PiLp.norm_single, Real.norm_eq_abs]
      exact abs_of_nonneg (g.length_nonneg _ _)
    have hχzero (z η : EuclideanSpace ℝ (Fin n)) (h : L z η ≤ 1 / 2) : χ z η = 0 := by
      apply highFrequencyCutoff_eq_zero
      simpa only [hχnorm] using h
    have hχone (z η : EuclideanSpace ℝ (Fin n)) (h : 1 ≤ L z η) : χ z η = 1 := by
      apply highFrequencyCutoff_eq_one
      simpa only [hχnorm] using h
    -- The actual metric cutoff is locally zero at every zero covector.
    have hreg : ContDiffOn ℝ ∞ (Function.uncurry χ)
        (V ×ˢ Set.univ) := by
      intro w hw
      by_cases hη : w.2 = 0
      · obtain ⟨K, hK, hwK, hKV⟩ := exists_compact_subset hV hw.1
        obtain ⟨b, B', hb, hB, hboundsK⟩ := hbounds K hK (fun z hz ↦ (hKV hz).1.1)
        have hrad : 0 < 1 / (2 * B') := by positivity
        have hnear : Function.uncurry χ =ᶠ[nhds w] 0 := by
          filter_upwards [(isOpen_interior.prod Metric.isOpen_ball).mem_nhds
            (show w ∈ interior K ×ˢ Metric.ball 0 (1 / (2 * B')) by
              exact ⟨hwK, by simpa only [Metric.mem_ball, dist_zero_right, hη, norm_zero]⟩)]
            with z hz
          have hnormz : ‖z.2‖ < 1 / (2 * B') := by
            simpa only [Metric.mem_ball, dist_zero_right] using hz.2
          have hsmall : L z.1 z.2 ≤ 1 / 2 := by
            have hu := (hboundsK z.1 (interior_subset hz.1) z.2).2
            have hmul := (lt_div_iff₀ (show 0 < 2 * B' by positivity)).mp hnormz
            nlinarith
          simp only [Function.uncurry, hχzero _ _ hsmall, Pi.zero_apply]
        exact (contDiffAt_const.congr_of_eventuallyEq hnear).contDiffWithinAt
      · have hwp : w ∈ V ×ˢ {η | η ≠ 0} := ⟨hw.1, hη⟩
        have hLp : ContDiffAt ℝ ∞ (Function.uncurry L) w :=
          hL_smooth.contDiffAt ((c.open_target.prod isOpen_ne).mem_nhds
            ⟨hw.1.1.1, hη⟩)
        have hsingle : ContDiffAt ℝ ∞
            (fun w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
              EuclideanSpace.single (0 : Fin 1) (L w.1 w.2)) w := by
          apply contDiffAt_piLp'
          intro k
          have hk : k = 0 := Subsingleton.elim _ _
          subst k
          convert hLp using 1
          funext z
          simp [Function.uncurry]
        have hχ : ContDiffAt ℝ ∞ (fun w ↦ χ w.1 w.2) w :=
          contDiff_highFrequencyCutoff.contDiffAt.comp w hsingle
        exact hχ.contDiffWithinAt
    refine ⟨Function.uncurry χ, hreg, ?_, ?_, ?_⟩
    · intro a z η
      ext v
      by_cases hz : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet
      · simp [atlasGlobalSymbolInChart, atlasRegularizedSymbolFunction, χ, L, hz]
        simp only [← Complex.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul]
      · simp [atlasGlobalSymbolInChart, hz]
    · obtain ⟨b, D, hb, hD, hboundsK⟩ := hbounds K hK (fun z hz ↦ (hKU hz).1.1)
      refine ⟨1 / (2 * D), by positivity, ?_⟩
      intro z hz η hη
      apply hχzero
      have hmul := (le_div_iff₀ (show 0 < 2 * D by positivity)).mp hη
      have hu := (hboundsK z hz η).2
      nlinarith
    · obtain ⟨b, D, hb, hD, hboundsK⟩ := hbounds K hK (fun z hz ↦ (hKU hz).1.1)
      refine ⟨b⁻¹, inv_pos.mpr hb, ?_⟩
      intro z hz η hη
      apply hχone
      have hmul := mul_le_mul_of_nonneg_left hη hb.le
      rw [mul_inv_cancel₀ hb.ne'] at hmul
      exact hmul.trans (hboundsK z hz η).1
  have compactProductBound {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
      [FiniteDimensional ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
      (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
      (K L : Set X) (hK : IsCompact K) (hL : IsCompact L)
      (hKU : K ⊆ U) (hLW : L ⊆ W)
      (χ : X × X → ℝ) (hχ : ContDiffOn ℝ ∞ χ (U ×ˢ W)) (i j : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p : X → X → V,
        ContDiffOn ℝ ∞ (Function.uncurry p) (U ×ˢ W) →
        ∀ A : ℝ, 0 ≤ A →
        (∀ a ≤ i + j, ∀ b ≤ i + j, ∀ x ∈ K, ∀ ξ ∈ L,
          ‖iteratedFDeriv ℝ a (fun y ↦ iteratedFDeriv ℝ b (p y) ξ) x‖ ≤ A) →
        ∀ x ∈ K, ∀ ξ ∈ L,
          ‖iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j
            (fun η ↦ χ (y, η) • p y η) ξ) x‖ ≤ C * A := by
    classical
    have globalize {D T : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
        [FiniteDimensional ℝ D] [NormedAddCommGroup T] [NormedSpace ℝ T]
        (f : D → T) (O S : Set D) (hO : IsOpen O) (hS : IsCompact S) (hSO : S ⊆ O)
        (hf : ContDiffOn ℝ ∞ f O) :
        ∃ g : D → T, ContDiff ℝ ∞ g ∧ ∀ x ∈ S, g =ᶠ[𝓝 x] f := by
      obtain ⟨O₁, hO₁, hSO₁, hO₁O, hO₁c⟩ :=
        exists_open_between_and_isCompact_closure hS hO hSO
      obtain ⟨O₂, hO₂, hO₁O₂, hO₂O, _⟩ :=
        exists_open_between_and_isCompact_closure hO₁c hO hO₁O
      obtain ⟨β, hβ, _, hβs, hβone⟩ :=
        exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hO₂ isClosed_closure hO₁O₂
      have hβO : tsupport β ⊆ O := by
        rw [tsupport, hβs]
        exact hO₂O
      refine ⟨fun x ↦ β x • f x, ?_, ?_⟩
      · apply contDiff_iff_contDiffAt.mpr
        intro x
        by_cases hx : x ∈ tsupport β
        · exact hβ.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds (hβO hx)))
        · apply (contDiffAt_const (c := (0 : T))).congr_of_eventuallyEq
          filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hx] with y hy
          rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
      · intro x hx
        filter_upwards [hO₁.mem_nhds (hSO₁ hx)] with y hy
        rw [(hβone y).mp (subset_closure hy), one_smul]
    have mixedEq (p q : X → X → V) (x y : X)
        (h : Function.uncurry p =ᶠ[𝓝 (x, y)] Function.uncurry q) (a b : ℕ) :
        iteratedFDeriv ℝ a (fun z ↦ iteratedFDeriv ℝ b (p z) y) x =
          iteratedFDeriv ℝ a (fun z ↦ iteratedFDeriv ℝ b (q z) y) x := by
      obtain ⟨U₁, hU₁, W₁, hW₁, hUW₁⟩ := mem_nhds_prod_iff.mp h
      have heq : (fun z ↦ iteratedFDeriv ℝ b (p z) y) =ᶠ[𝓝 x]
          (fun z ↦ iteratedFDeriv ℝ b (q z) y) := by
        filter_upwards [hU₁] with z hz
        have hpq : p z =ᶠ[𝓝 y] q z := by
          filter_upwards [hW₁] with v hv
          exact @hUW₁ (z, v) ⟨hz, hv⟩
        exact (hpq.iteratedFDeriv ℝ b).eq_of_nhds
      exact (heq.iteratedFDeriv ℝ a).eq_of_nhds
    obtain ⟨g, hg, hgeq⟩ := globalize χ (U ×ˢ W) (K ×ˢ L)
      (hU.prod hW) (hK.prod hL) (prod_mono hKU hLW) hχ
    have hgb (a : ℕ) : ∃ D : ℝ, 0 ≤ D ∧
        ∀ z ∈ K ×ˢ L, ‖iteratedFDeriv ℝ a g z‖ ≤ D := by
      obtain ⟨D, hD⟩ := (hK.prod hL).exists_bound_of_continuousOn
        (hg.continuous_iteratedFDeriv (by simp)).continuousOn
      exact ⟨max D 0, le_max_right _ _, fun z hz ↦ (hD z hz).trans (le_max_left _ _)⟩
    choose D hD hDb using hgb
    let N := i + j
    let C : ℝ := ∑ a ∈ Finset.range (N + 1),
      (N.choose a : ℝ) * D a * 2 ^ (N - a)
    have hC : 0 ≤ C := Finset.sum_nonneg (fun a _ ↦
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hD a)) (by positivity))
    refine ⟨C, hC, ?_⟩
    intro p hp A hA hAb x hx ξ hξ
    obtain ⟨q, hq, hqeq⟩ := globalize (Function.uncurry p) (U ×ˢ W) (K ×ˢ L)
      (hU.prod hW) (hK.prod hL) (prod_mono hKU hLW) hp
    have heq : (fun z : X × X ↦ χ z • p z.1 z.2) =ᶠ[𝓝 (x, ξ)]
        (fun z ↦ g z • q z) := by
      filter_upwards [hgeq (x, ξ) ⟨hx, hξ⟩, hqeq (x, ξ) ⟨hx, hξ⟩] with z hz₁ hz₂
      rw [hz₁, hz₂]
      rfl
    rw [mixedEq (fun y η ↦ χ (y, η) • p y η)
      (fun y η ↦ g (y, η) • q (y, η)) x ξ heq i j]
    apply (norm_mixed_iteratedFDeriv_le (fun y η ↦ g (y, η) • q (y, η))
      (hg.smul hq) i j x ξ).trans
    apply (norm_iteratedFDeriv_smul_le hg hq (x, ξ) (n := N) (by simp)).trans
    change _ ≤ C * A
    dsimp only [C]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    have hpfull : ‖iteratedFDeriv ℝ (N - a) q (x, ξ)‖ ≤ 2 ^ (N - a) * A := by
      apply norm_iteratedFDeriv_uncurry_le_of_mixed (fun y η ↦ q (y, η)) hq
        (N - a) x ξ A hA
      intro b hb d hd
      rw [mixedEq (fun y η ↦ q (y, η)) p x ξ
        (hqeq (x, ξ) ⟨hx, hξ⟩) b d]
      exact hAb b (hb.trans (Nat.sub_le _ _)) d (hd.trans (Nat.sub_le _ _)) x hx ξ hξ
    calc
      _ ≤ (N.choose a : ℝ) * D a * (2 ^ (N - a) * A) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hDb a (x, ξ) ⟨hx, hξ⟩)
          (Nat.cast_nonneg _)) hpfull (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (hD a))
      _ = _ := by ring
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin (A.rank J.inputIndex)) →L[ℂ]
    EuclideanSpace ℂ (Fin (B.rank J.outputIndex))
  let U := atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
  let K := J.localIndex.compactSet
  let i := J.localIndex.spatialOrder
  let j := J.localIndex.frequencyOrder
  let N := i + j
  let k := m - (j : ℝ)
  have hU : IsOpen U := isOpen_atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
  have hK : IsCompact K := J.localIndex.isCompact
  have hKU : K ⊆ U := J.localIndex.subset_domain
  -- The larger compact neighborhood makes both cutoff identities valid for all derivatives.
  obtain ⟨K', hK', hKK', hK'U⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ, hχ, hformula, ⟨ε₀, hε₀, hzero⟩, ⟨R₀, hR₀, hone⟩⟩ :=
    cutoffProperties J.chart J.mem_atlas J.inputIndex J.outputIndex K' hK' hK'U
  let ε := min ε₀ 1
  let radius := max R₀ 1
  have hε : 0 < ε := lt_min hε₀ zero_lt_one
  have hradius : 1 ≤ radius := le_max_right _ _
  let W : Set X := {ξ | ε / 2 ≤ ‖ξ‖} ∩ Metric.closedBall 0 (2 * radius)
  have hW : IsCompact W := (isCompact_closedBall _ _).inter_left
    (isClosed_le continuous_const continuous_norm)
  have hWne : W ⊆ {ξ : X | ξ ≠ 0} := by
    intro ξ hξ hξzero
    have h : ε / 2 ≤ ‖ξ‖ := hξ.1
    rw [hξzero, norm_zero] at h
    linarith
  have hsphere (ξ : X) (hξ : ‖ξ‖ = 1) : ξ ∈ W := by
    constructor
    · change ε / 2 ≤ ‖ξ‖
      rw [hξ]
      have he : ε ≤ 1 := min_le_right _ _
      linarith
    · simpa only [Metric.mem_closedBall, dist_zero_right, hξ] using
        (show (1 : ℝ) ≤ 2 * radius by linarith)
  let index (a b : ℕ) : AtlasHomogeneousSymbolSeminormIndex A B :=
    { toAtlasGlobalSymbolSeminormIndex :=
        { J with localIndex := { J.localIndex with spatialOrder := a, frequencyOrder := b } }
      frequencySet := W
      isCompact_frequencySet := hW
      frequency_ne_zero := hWne }
  let indices := ((Finset.range (N + 1)).product (Finset.range (N + 1))).image
    (fun ab : ℕ × ℕ ↦ index ab.1 ab.2)
  have boundSource (p : homogeneousAtlasSymbolSpace A B m)
      (a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) (x ξ : X) (hx : x ∈ K) (hξ : ξ ∈ W) :
      ‖symbolDerivative (atlasGlobalSymbolInChart A B p.val J.chart J.inputIndex J.outputIndex)
        a b x ξ‖ ≤ (indices.sup (atlasHomogeneousSymbolSeminorm A B m)) p := by
    have hmem : index a b ∈ indices := Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ha),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩, rfl⟩
    have hbound : ‖symbolDerivative
        (atlasGlobalSymbolInChart A B p.val J.chart J.inputIndex J.outputIndex) a b x ξ‖ ≤
          atlasHomogeneousSymbolSeminorm A B m (index a b) p :=
      le_csSup (bddAbove_atlasHomogeneousSymbolSeminormValue_set A B m (index a b) p)
        ⟨x, hx, ξ, hξ, rfl⟩
    exact hbound.trans ((Finset.le_sup (f := atlasHomogeneousSymbolSeminorm A B m) hmem) p)
  obtain ⟨C, hC, hproduct⟩ := compactProductBound (V := V) U {ξ : X | ξ ≠ 0} hU isOpen_ne
    K W hK hW hKU hWne χ (hχ.mono (prod_mono subset_rfl (subset_univ _))) i j
  have hweightCont : Continuous (fun ξ : X ↦ (1 + ‖ξ‖) ^ (-k)) :=
    (continuous_const.add continuous_norm : Continuous (fun ξ : X ↦ (1 : ℝ) + ‖ξ‖)).rpow_const
      (fun ξ ↦ Or.inl (ne_of_gt (show 0 < (1 : ℝ) + ‖ξ‖ by positivity)))
  obtain ⟨D₀, hD₀⟩ := hW.exists_bound_of_continuousOn hweightCont.continuousOn
  let D := max D₀ 0
  have hD : 0 ≤ D := le_max_right _ _
  have hweightBound (ξ : X) (hξ : ξ ∈ W) : (1 + ‖ξ‖) ^ (-k) ≤ D := by
    have hd : |(1 + ‖ξ‖) ^ (-k)| ≤ D₀ := by
      simpa only [Real.norm_eq_abs] using hD₀ ξ hξ
    exact (le_abs_self _).trans (hd.trans (le_max_left _ _))
  have mixedEq (p q : X → X → V) (x y : X)
      (h : Function.uncurry p =ᶠ[𝓝 (x, y)] Function.uncurry q) (a b : ℕ) :
      iteratedFDeriv ℝ a (fun z ↦ iteratedFDeriv ℝ b (p z) y) x =
        iteratedFDeriv ℝ a (fun z ↦ iteratedFDeriv ℝ b (q z) y) x := by
    obtain ⟨U₁, hU₁, W₁, hW₁, hUW₁⟩ := mem_nhds_prod_iff.mp h
    have heq : (fun z ↦ iteratedFDeriv ℝ b (p z) y) =ᶠ[𝓝 x]
        (fun z ↦ iteratedFDeriv ℝ b (q z) y) := by
      filter_upwards [hU₁] with z hz
      have hpq : p z =ᶠ[𝓝 y] q z := by
        filter_upwards [hW₁] with v hv
        exact @hUW₁ (z, v) ⟨hz, hv⟩
      exact (hpq.iteratedFDeriv ℝ b).eq_of_nhds
    exact (heq.iteratedFDeriv ℝ a).eq_of_nhds
  have scaleDerivative (p : SymbolFunction n (A.rank J.inputIndex) (B.rank J.outputIndex))
      (hp : IsHomogeneousSymbol U m p)
      (a b : ℕ) (x : X) (hx : x ∈ U) (ξ : X) (hξ : ξ ≠ 0) (t : ℝ) (ht : 0 < t) :
      symbolDerivative p a b x (t • ξ) =
        t ^ (m - (b : ℝ)) • symbolDerivative p a b x ξ := by
    have deriv_comp_smul {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
        [NormedAddCommGroup W] [NormedSpace ℝ W] (t : ℝ) (ht : t ≠ 0) (f : V → W) (j : ℕ) (ξ : V) :
        iteratedFDeriv ℝ j (fun ζ ↦ f (t • ζ)) ξ =
          t ^ j • iteratedFDeriv ℝ j f (t • ξ) := by
      let e : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)
      have h := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := ξ) (mem_univ _) j
      simp only [preimage_univ, iteratedFDerivWithin_univ] at h
      change iteratedFDeriv ℝ j (f ∘ e) ξ = _
      rw [h]
      ext v
      change (iteratedFDeriv ℝ j f (t • ξ)) (fun i ↦ t • v i) = _
      rw [ContinuousMultilinearMap.map_smul_univ]
      simp
    have deriv_smul {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
        [NormedAddCommGroup W] [NormedSpace ℝ W] (t : ℝ) (ht : t ≠ 0) (f : V → W) (j : ℕ) (ξ : V) :
        iteratedFDeriv ℝ j (fun ζ ↦ t • f ζ) ξ = t • iteratedFDeriv ℝ j f ξ := by
      let e : W ≃L[ℝ] W := ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)
      have h := e.iteratedFDeriv_comp_left (f := f) (x := ξ) (i := j)
      change iteratedFDeriv ℝ j (e ∘ f) ξ = _
      rw [h]
      rfl
    -- Differentiate homogeneity first in frequency and then on the original open base domain.
    have hscale (i j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
        (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) (t : ℝ) (ht : 0 < t) :
        symbolDerivative p i j x (t • ξ) = t ^ (m - (j : ℝ)) • symbolDerivative p i j x ξ := by
      have hfreq (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U) :
          iteratedFDeriv ℝ j (p y) (t • ξ) =
            t ^ (m - (j : ℝ)) • iteratedFDeriv ℝ j (p y) ξ := by
        have heq : (fun ζ ↦ p y (t • ζ)) =ᶠ[𝓝 ξ] (fun ζ ↦ (t ^ m) • p y ζ) := by
          filter_upwards [(isOpen_ne : IsOpen {ζ : EuclideanSpace ℝ (Fin n) | ζ ≠ 0}).mem_nhds hξ]
            with ζ hζ
          exact hp y hy ζ hζ t ht
        have hd := (heq.iteratedFDeriv ℝ j).eq_of_nhds
        rw [deriv_comp_smul t ht.ne', deriv_smul (t ^ m) (Real.rpow_pos_of_pos ht m).ne'] at hd
        calc
          _ = (t ^ j)⁻¹ • (t ^ j • iteratedFDeriv ℝ j (p y) (t • ξ)) := by
            rw [inv_smul_smul₀ (pow_ne_zero _ ht.ne')]
          _ = ((t ^ j)⁻¹ * t ^ m) • iteratedFDeriv ℝ j (p y) ξ := by rw [hd, smul_smul]
          _ = _ := by
            rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
            congr 2
            ring
      have heq : (fun y ↦ iteratedFDeriv ℝ j (p y) (t • ξ)) =ᶠ[𝓝 x]
          (fun y ↦ t ^ (m - (j : ℝ)) • iteratedFDeriv ℝ j (p y) ξ) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact hfreq y hy
      have hd := (heq.iteratedFDeriv ℝ i).eq_of_nhds
      rw [deriv_smul _ (Real.rpow_pos_of_pos ht _).ne'] at hd
      exact hd
    exact hscale a b x hx ξ hξ t ht
  have hweight (k t : ℝ) (ht : 1 ≤ t) :
      t ^ k ≤ (2 : ℝ) ^ |k| * (1 + t) ^ k := by
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    by_cases hk : 0 ≤ k
    · have htwo : (1 : ℝ) ≤ 2 ^ |k| := Real.one_le_rpow (by norm_num) (abs_nonneg _)
      calc
        t ^ k ≤ (1 + t) ^ k := Real.rpow_le_rpow htpos.le (by linarith) hk
        _ ≤ 2 ^ |k| * (1 + t) ^ k := le_mul_of_one_le_left (by positivity) htwo
    · have hk' : k ≤ 0 := (lt_of_not_ge hk).le
      have hcomp : (2 * t) ^ k ≤ (1 + t) ^ k :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hk'
      calc
        t ^ k = 2 ^ |k| * (2 * t) ^ k := by
          rw [Real.mul_rpow (by norm_num) htpos.le, abs_of_nonpos hk', ← mul_assoc,
            ← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero, one_mul]
        _ ≤ 2 ^ |k| * (1 + t) ^ k := mul_le_mul_of_nonneg_left hcomp (by positivity)
  let Ctotal := C * D + 2 ^ |k|
  have hB : 0 ≤ Ctotal := add_nonneg (mul_nonneg hC hD) (by positivity)
  refine ⟨indices, ⟨Ctotal, hB⟩, ?_⟩
  intro p
  let S := (indices.sup (atlasHomogeneousSymbolSeminorm A B m)) p
  have hS : 0 ≤ S := apply_nonneg _ _
  let a := atlasGlobalSymbolInChart A B p.val J.chart J.inputIndex J.outputIndex
  let b := atlasGlobalSymbolInChart A B (atlasRegularizationLinearMap A B g m p).val
    J.chart J.inputIndex J.outputIndex
  have hb (x ξ : X) : b x ξ = χ (x, ξ) • a x ξ := hformula p.val x ξ
  have ha : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ {ξ : X | ξ ≠ 0}) :=
    p.property.1 J.chart J.mem_atlas J.inputIndex J.outputIndex
  have hh : IsHomogeneousSymbol U m a := by
    intro z hz η hη t ht
    have hframes : J.chart.symm z ∈ (A.chart J.inputIndex).baseSet ∧
        J.chart.symm z ∈ (B.chart J.outputIndex).baseSet := ⟨hz.1.2, hz.2⟩
    have hcov : covectorFromChart J.chart (J.chart.symm z) (t • η) =
        t • covectorFromChart J.chart (J.chart.symm z) η := by
      ext v
      exact real_inner_smul_left η _ t
    have hne : covectorFromChart J.chart (J.chart.symm z) η ≠ 0 := by
      intro hzero
      have h := covectorInChart_covectorFromChart J.chart J.mem_atlas
        (J.chart.symm z) (J.chart.map_target hz.1.1) η
      rw [hzero] at h
      exact hη (h.symm.trans (by ext k; rfl))
    ext v
    simp [a, atlasGlobalSymbolInChart, hframes, hcov, p.property.2 _ _ hne t ht]
    simp only [← Complex.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  change symbolSeminormValue _ m J.localIndex
    (atlasGlobalSymbolInChartLinearMap A B m J
      (atlasRegularizationLinearMap A B g m p)) ≤ Ctotal * S
  by_cases hnonempty : K.Nonempty
  swap
  · have hKzero : J.localIndex.compactSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [symbolSeminormValue, hKzero, Set.mem_empty_iff_false, false_and,
      exists_false, Set.ofPred_false, Real.sSup_empty]
    exact mul_nonneg hB hS
  obtain ⟨x₀, hx₀⟩ := hnonempty
  change sSup {t : ℝ | ∃ x ∈ K, ∃ ξ : X,
    t = ‖symbolDerivative b i j x ξ‖ / (1 + ‖ξ‖) ^ k} ≤ Ctotal * S
  refine csSup_le ⟨_, x₀, hx₀, 0, rfl⟩ ?_
  rintro t ⟨x, hx, ξ, rfl⟩
  have hden : 0 < (1 + ‖ξ‖) ^ k := Real.rpow_pos_of_pos (by positivity) _
  by_cases hsmall : ‖ξ‖ < ε
  · -- A neighborhood vanishes identically, so the full mixed derivative vanishes too.
    have heq : Function.uncurry b =ᶠ[𝓝 (x, ξ)] Function.uncurry (fun _ _ ↦ (0 : V)) := by
      filter_upwards [(isOpen_interior.prod (isOpen_lt continuous_norm continuous_const)).mem_nhds
        (show (x, ξ) ∈ interior K' ×ˢ {η : X | ‖η‖ < ε} from ⟨hKK' hx, hsmall⟩)]
        with z hz
      change b z.1 z.2 = 0
      rw [hb, hzero z.1 (interior_subset hz.1) z.2
        (hz.2.le.trans (min_le_left _ _)), zero_smul]
    have hd := mixedEq b (fun _ _ ↦ (0 : V)) x ξ heq i j
    change symbolDerivative b i j x ξ = _ at hd
    rw [hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, zero_div]
    exact mul_nonneg hB hS
  by_cases hlarge : radius < ‖ξ‖
  · -- Positive homogeneity transfers the entire high-frequency jet to the same unit sphere.
    have heq : Function.uncurry b =ᶠ[𝓝 (x, ξ)] Function.uncurry a := by
      filter_upwards [(isOpen_interior.prod (isOpen_lt continuous_const continuous_norm)).mem_nhds
        (show (x, ξ) ∈ interior K' ×ˢ {η : X | radius < ‖η‖} from ⟨hKK' hx, hlarge⟩)]
        with z hz
      change b z.1 z.2 = a z.1 z.2
      rw [hb, hone z.1 (interior_subset hz.1) z.2
        ((le_max_left _ _).trans hz.2.le), one_smul]
    have hder := mixedEq b a x ξ heq i j
    have hξpos : 0 < ‖ξ‖ := lt_of_lt_of_le zero_lt_one (hradius.trans hlarge.le)
    let η := ‖ξ‖⁻¹ • ξ
    have hηnorm : ‖η‖ = 1 := by
      simpa [η] using norm_smul_inv_norm (𝕜 := ℝ) (norm_pos_iff.mp hξpos)
    have hηne : η ≠ 0 := by intro hz; simp [hz] at hηnorm
    have hreconstruct : ‖ξ‖ • η = ξ := smul_inv_smul₀ hξpos.ne' ξ
    have hsource : ‖symbolDerivative a i j x η‖ ≤ S :=
      boundSource p i j (Nat.le_add_right _ _) (Nat.le_add_left _ _)
        x η hx (hsphere η hηnorm)
    have hd : ‖symbolDerivative b i j x ξ‖ =
        ‖ξ‖ ^ k * ‖symbolDerivative a i j x η‖ := by
      change symbolDerivative b i j x ξ = symbolDerivative a i j x ξ at hder
      rw [hder]
      conv_lhs => rw [← hreconstruct, scaleDerivative a hh i j x (hKU hx) η hηne ‖ξ‖ hξpos]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hξpos _)]
    apply (div_le_iff₀ hden).mpr
    rw [hd]
    calc
      _ ≤ ‖ξ‖ ^ k * S := mul_le_mul_of_nonneg_left hsource (by positivity)
      _ ≤ (2 ^ |k| * (1 + ‖ξ‖) ^ k) * S :=
        mul_le_mul_of_nonneg_right (hweight k ‖ξ‖ (hradius.trans hlarge.le)) hS
      _ ≤ (Ctotal * S) * (1 + ‖ξ‖) ^ k := by
        have hCD : 0 ≤ C * D := mul_nonneg hC hD
        dsimp only [Ctotal]
        nlinarith [mul_nonneg hCD (mul_nonneg hS hden.le)]
  · -- The remaining frequencies lie in one fixed compact punctured annulus.
    have hξW : ξ ∈ W := by
      constructor
      · change ε / 2 ≤ ‖ξ‖
        have hl : ε ≤ ‖ξ‖ := le_of_not_gt hsmall
        linarith
      · have hu : ‖ξ‖ ≤ radius := le_of_not_gt hlarge
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          (show ‖ξ‖ ≤ 2 * radius by linarith)
    have hbound := hproduct a ha S hS
      (fun a' ha' b' hb' x' hx' ξ' hξ' ↦
        boundSource p a' b' ha' hb' x' ξ' hx' hξ') x hx ξ hξW
    have hbeq : b = fun y η ↦ χ (y, η) • a y η := funext (fun y ↦ funext (hb y))
    change ‖symbolDerivative (fun y η ↦ χ (y, η) • a y η) i j x ξ‖ ≤ C * S at hbound
    rw [← hbeq] at hbound
    have hpow : ((1 + ‖ξ‖) ^ k)⁻¹ = (1 + ‖ξ‖) ^ (-k) :=
      (Real.rpow_neg (by positivity) k).symm
    rw [div_eq_mul_inv, hpow]
    calc
      _ ≤ (C * S) * D := mul_le_mul hbound (hweightBound ξ hξW)
        (Real.rpow_nonneg (by positivity) _) (mul_nonneg hC hS)
      _ ≤ Ctotal * S := by
        dsimp only [Ctotal]
        nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ |k| by positivity) hS]

/-- Fixed radial regularization is continuous between the two derivative topologies. -/
theorem continuous_atlasRegularizationLinearMap :
    Continuous (atlasRegularizationLinearMap A B g m) := by
  /- Apply the linear continuity criterion for WithSeminorms using the
  preceding finite estimate for each target test. Both topologies were
  defined from coordinate derivatives independently of regularization. -/
  apply WithSeminorms.continuous_of_isBounded
    (withSeminorms_atlasHomogeneousSymbolTopology A B m)
    (withSeminorms_atlasGlobalSymbolTopology A B m)
  intro J
  obtain ⟨I, K, hbound⟩ := exists_atlasRegularization_seminorm_bound A B g m J
  exact ⟨I, K, hbound⟩

/-- Fixed radial regularization with its established continuity certificate. -/
def atlasRegularizationCLM :
    homogeneousAtlasSymbolSpace A B m →L[ℂ] atlasGlobalSymbolSpace A B m where
  toLinearMap := atlasRegularizationLinearMap A B g m
  cont := continuous_atlasRegularizationLinearMap A B g m

variable [SecondCountableTopology M] [CompactSpace M]

namespace AtlasQuantizationPresentation

variable {A B} (C : AtlasQuantizationPresentation A B)

/-- Quantize the specified homogeneous field with the same metric and finite presentation. -/
def quantizeHomogeneous (a : homogeneousAtlasSymbolSpace A B m) :
    AtlasPseudodifferentialOperator A B m :=
  C.quantize (atlasRegularizationLinearMap A B g m a)

/-- This actual operator has precisely the regularized homogeneous principal class. -/
theorem principalSymbol_quantizeHomogeneous (a : homogeneousAtlasSymbolSpace A B m) :
    (C.quantizeHomogeneous g m a).principalSymbol =
      atlasGlobalPrincipalSymbolClass A B m
        (atlasRegularizedSymbol A B g m a.val a.property.1 a.property.2) := by
  /- Use the principal-symbol theorem for this same fixed quantizer and
  its actual radial regularization. The equality identifies the original
  principal quotient, not a separately selected representative operator. -/
  exact C.principalSymbol_quantize (atlasRegularizationLinearMap A B g m a)

/-- A fixed homogeneous quantization carries smooth-topology families to norm-continuous
operators. -/
theorem continuous_sobolevQuantizeHomogeneous
    (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B)
    {Z : Type*} [TopologicalSpace Z] (a : Z → homogeneousAtlasSymbolSpace A B m)
    (ha : Continuous a) (s : ℝ) :
    Continuous (fun z ↦ (C.quantizeHomogeneous g m (a z)).sobolevExtension L K s) := by
  /- Compose the given family with atlasRegularizationCLM and the fixed
  sobolevQuantizationCLM. Their underlying functions are respectively the
  specified cutoff symbol and the unique bounded extension of the same
  finite Fourier sum. The parameter need not be compact, and neither
  ellipticity nor continuity of a choice of inverses is used. -/
  exact (C.continuous_sobolevQuantization L K s m
    (fun z ↦ atlasRegularizationLinearMap A B g m (a z))
    ((continuous_atlasRegularizationLinearMap A B g m).comp ha))

end AtlasQuantizationPresentation

end AtiyahSinger
