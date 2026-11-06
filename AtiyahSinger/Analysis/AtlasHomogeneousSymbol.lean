/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasGlobalSymbol
public import AtiyahSinger.Analysis.HomogeneousCutoff
public import AtiyahSinger.Geometry.CotangentMetric

import AtiyahSinger.Analysis.CosphereRegularity
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Homogeneous principal data on locally finite-rank smooth bundles

Public module ID: M0249.

A10: the actual cotangent Hom family is smooth off zero and positively
homogeneous. Ellipticity means bijectivity at every nonzero covector. These
standard conditions do not constrain its value at zero or require global
constant ranks. They are not a definition of ellipticity for arbitrary PDOs.

A specified cotangent metric supplies a radial cutoff of the original family.
The cutoff vanishes near zero and is exactly one beyond unit metric length,
so it gives SG's weak homogeneous principal representative. There is no full
polyhomogeneous-expansion predicate. The chosen metric affects the full symbol
but not its principal class or its recovered homogeneous data off zero.

Sources: SG III.3.18--3.19 and III.13 (13.5)--(13.7), pp.245--246. The metric
radial regularization and variable-rank atlas formulas are project supplements
of the same local homogeneous-symbol argument. All original regularization, symbol
estimates and principal-class comparison statements below are proved.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set Function
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 20


set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- Smoothness of the actual coordinate Hom family on the punctured cotangent bundle. -/
def IsSmoothOffZeroAtlasSymbol (a : AtlasSymbolFunction (n := n) E F) : Prop :=
  ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M → ∀ (i : A.Index) (j : B.Index),
      ContDiffOn ℝ ∞ (Function.uncurry (atlasGlobalSymbolInChart A B a c i j))
        (atlasSymbolChartDomain A B c i j ×ˢ {ξ | ξ ≠ 0})

/-- Positive real homogeneity of the original fiber maps, with no condition at zero. -/
def IsHomogeneousAtlasSymbol (m : ℝ) (a : AtlasSymbolFunction (n := n) E F) : Prop :=
  ∀ x : M, ∀ ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ,
    ξ ≠ 0 → ∀ t : ℝ, 0 < t → a x (t • ξ) = ((t ^ m : ℝ) : ℂ) • a x ξ

/-- Ellipticity of the displayed homogeneous data is bijectivity off the zero section. -/
def IsEllipticAtlasSymbol (a : AtlasSymbolFunction (n := n) E F) : Prop :=
  ∀ x : M, ∀ ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ,
    ξ ≠ 0 → Function.Bijective (a x ξ)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  (g : SmoothCotangentMetric (n := n) (M := M))

/-- Apply the fixed one-dimensional cutoff to the actual metric covector length. -/
def atlasRegularizedSymbolFunction (a : AtlasSymbolFunction (n := n) E F) :
    AtlasSymbolFunction (n := n) E F :=
  fun x ξ ↦
    (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (g.length x ξ)) : ℂ) • a x ξ

include hM in
/-- The cutoff is zero near the zero section and retains the exact homogeneous field at infinity. -/
theorem atlasRegularizedSymbolFunction_cutoff (a : AtlasSymbolFunction (n := n) E F) :
    (∀ (x : M) (ξ : CotangentFiber (n := n) x), g.length x ξ ≤ 1 / 2 →
      atlasRegularizedSymbolFunction g a x ξ = 0) ∧
    (∀ (x : M) (ξ : CotangentFiber (n := n) x), 1 ≤ g.length x ξ →
      atlasRegularizedSymbolFunction g a x ξ = a x ξ) := by
  /- Stage 1: the Euclidean norm of the single coordinate is the absolute
  metric length, which equals that length by its nonnegativity.
  Stage 2: use the existing cutoff's inner-ball and outer-ball identities.
  Multiplication by zero or one gives the two formulas on the original
  fiber maps. No smoothness or homogeneity is needed for these identities;
  arbitrary zero-section values are suppressed even in dimension zero. -/
  have hnorm (x : M) (ξ : CotangentFiber (n := n) x) :
      ‖EuclideanSpace.single (0 : Fin 1) (g.length x ξ)‖ = g.length x ξ := by
    simp only [EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs,
      abs_of_nonneg (g.length_nonneg x ξ)]
  constructor
  · intro x ξ hξ
    have hzero := highFrequencyCutoff_eq_zero
      (EuclideanSpace.single (0 : Fin 1) (g.length x ξ)) (by simpa only [hnorm] using hξ)
    simp only [atlasRegularizedSymbolFunction, hzero, Complex.ofReal_zero, zero_smul]
  · intro x ξ hξ
    have hone := highFrequencyCutoff_eq_one
      (EuclideanSpace.single (0 : Fin 1) (g.length x ξ)) (by simpa only [hnorm] using hξ)
    simp only [atlasRegularizedSymbolFunction, hone, Complex.ofReal_one, one_smul]

variable [hT : T2Space M]

include hM hT in
/-- The radial regularization of smooth homogeneous data is a genuine order-m atlas symbol. -/
theorem isAtlasGlobalSymbol_atlasRegularizedSymbolFunction (m : ℝ)
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a) :
    IsAtlasGlobalSymbol A B m (atlasRegularizedSymbolFunction g a) := by
  /- Stage 1: on every actual chart/frame overlap the metric length is
  smooth off zero. The product is zero on a neighborhood of each zero
  covector, so it extends smoothly there without differentiating a norm
  at zero or requiring a value of a to be continuous at zero.
  Stage 2: on each compact spatial subset, positive definiteness bounds
  metric length above and below by the coordinate covector norm. Homogeneity
  controls every mixed derivative of a by the usual order m frequency weight.
  The cutoff transition lies in a uniformly bounded annulus on that compact
  subset; all metric and frame derivatives are bounded there. Product rules
  give the required symbol estimates, with the original independent local
  source and target ranks. In dimension zero the regularized function is zero. -/
  classical
  intro c hc i j
  let V := atlasSymbolChartDomain A B c i j
  let p := atlasGlobalSymbolInChart A B a c i j
  let L (z η : EuclideanSpace ℝ (Fin n)) :=
    g.length (c.symm z) (covectorFromChart c (c.symm z) η)
  let χ (z η : EuclideanSpace ℝ (Fin n)) :=
    highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (L z η))
  have hV : IsOpen V := by
    simpa only [V, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      c.continuousOn_symm.isOpen_inter_preimage c.open_target
        ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
  have hcoord : atlasGlobalSymbolInChart A B (atlasRegularizedSymbolFunction g a) c i j =
      fun z η ↦ (χ z η : ℂ) • p z η := by
    ext z η v
    by_cases hz : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet
    · simp [atlasGlobalSymbolInChart, atlasRegularizedSymbolFunction, χ, L, p, hz]
      simp only [← Complex.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul]
    · simp [atlasGlobalSymbolInChart, p, hz]
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
  have hhom : IsHomogeneousSymbol V m p := by
    intro z hz η hη t ht
    have hz' : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet :=
      ⟨hz.1.2, hz.2⟩
    have hη' := hcov_ne z hz.1.1 η hη
    ext v
    simp [p, atlasGlobalSymbolInChart, hz', hcov_smul, hh _ _ hη' t ht]
    simp only [← Complex.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  have hs' := hs c hc i j
  have hstandard := isSymbol_frequencyCutoffSymbol V hV m p hs' hhom
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
  have hreg : ContDiffOn ℝ ∞ (Function.uncurry (fun z η ↦ (χ z η : ℂ) • p z η))
      (V ×ˢ Set.univ) := by
    intro w hw
    by_cases hη : w.2 = 0
    · obtain ⟨K, hK, hwK, hKV⟩ := exists_compact_subset hV hw.1
      obtain ⟨b, B', hb, hB, hboundsK⟩ := hbounds K hK (fun z hz ↦ (hKV hz).1.1)
      have hrad : 0 < 1 / (2 * B') := by positivity
      have hnear : Function.uncurry (fun z η ↦ (χ z η : ℂ) • p z η) =ᶠ[nhds w] 0 := by
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
        simp only [Function.uncurry, hχzero _ _ hsmall, Complex.ofReal_zero, zero_smul,
          Pi.zero_apply]
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
      have hp : ContDiffAt ℝ ∞ (Function.uncurry p) w :=
        hs'.contDiffAt ((hV.prod isOpen_ne).mem_nhds hwp)
      exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp w hχ).smul hp).contDiffWithinAt
  rw [hcoord]
  refine ⟨hreg, ?_⟩
  intro K hKV hK α β
  -- Compare on a genuine neighborhood of K before taking any spatial derivatives.
  obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
  obtain ⟨b, B', hb, hB, hboundsK⟩ := hbounds K' hK' (fun z hz ↦ (hK'V hz).1.1)
  let R : ℝ := max 1 b⁻¹
  let d : SymbolFunction n (A.rank i) (B.rank j) :=
    (fun z η ↦ (χ z η : ℂ) • p z η) - frequencyCutoffSymbol p
  have hint : interior K' ⊆ V := interior_subset.trans hK'V
  have hd : ContDiffOn ℝ ∞ (Function.uncurry d) (interior K' ×ˢ Set.univ) :=
    (hreg.mono (Set.prod_mono hint subset_rfl)).sub
      (hstandard.1.mono (Set.prod_mono hint subset_rfl))
  have hsupp : ∀ z ∈ interior K', ∀ η, R ≤ ‖η‖ → d z η = 0 := by
    intro z hz η hη
    have hnorm : 1 ≤ ‖η‖ := (le_max_left _ _).trans hη
    have hlow : 1 ≤ L z η := by
      have h := mul_le_mul_of_nonneg_left ((le_max_right 1 b⁻¹).trans hη) hb.le
      rw [mul_inv_cancel₀ hb.ne'] at h
      exact h.trans (hboundsK z (interior_subset hz) η).1
    simp only [d, Pi.sub_apply, hχone z η hlow, Complex.ofReal_one, one_smul,
      frequencyCutoffSymbol_eq_of_one_le_norm p z η hnorm, sub_self]
  have hdSymbol := isSmoothingSymbol_of_frequency_support isOpen_interior d R hd hsupp m
  have hstandardLocal : IsSymbol (interior K') m (frequencyCutoffSymbol p) := by
    refine ⟨hstandard.1.mono (Set.prod_mono hint subset_rfl), ?_⟩
    intro C hC hcompact u v
    exact hstandard.2 C (hC.trans hint) hcompact u v
  have hsum := hdSymbol.add isOpen_interior hstandardLocal
  have heq : d + frequencyCutoffSymbol p = fun z η ↦ (χ z η : ℂ) • p z η := by
    dsimp [d]
    abel
  rw [heq] at hsum
  exact hsum.2 K hKK' hK α β

/-- The actual radial regularization packaged in the existing order-m symbol module. -/
def atlasRegularizedSymbol (m : ℝ) (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a) :
    atlasGlobalSymbolSpace A B m :=
  ⟨atlasRegularizedSymbolFunction g a,
    isAtlasGlobalSymbol_atlasRegularizedSymbolFunction A B g m a hs hh⟩

include hM hT in
/-- At a fixed degree the principal quotient recovers the exact homogeneous field off zero. -/
theorem atlasRegularizedSymbol_principalClass_eq_iff
    (k : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ)
    (a b : AtlasSymbolFunction (n := n) E F)
    (ha : IsSmoothOffZeroAtlasSymbol A B a) (hha : IsHomogeneousAtlasSymbol m a)
    (hb : IsSmoothOffZeroAtlasSymbol A B b) (hhb : IsHomogeneousAtlasSymbol m b) :
    atlasGlobalPrincipalSymbolClass A B m (atlasRegularizedSymbol A B g m a ha hha) =
        atlasGlobalPrincipalSymbolClass A B m (atlasRegularizedSymbol A B k m b hb hhb) ↔
      ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → a x ξ = b x ξ := by
  /- Forward: quotient equality says that the regularized difference has
  order m-1. Fix a nonzero covector in any valid chart and dilate it by t>0.
  For sufficiently large t both cutoffs equal one. Divide the difference
  estimate by t^m and use homogeneity; the remaining t^(-1) bound tends
  to zero, forcing equality of the two original fiber maps.
  Reverse: if the off-zero fields agree, the two regularizations differ
  only where at least one cutoff is not one. On every compact spatial
  subset this frequency region is bounded, by the two metric comparisons.
  The smooth difference therefore satisfies all orders, in particular m-1.
  The argument compares the same original bundles. When n=0 both sides
  are vacuous or zero, without identifying different source/target bundles. -/
  classical
  have hopen (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (i : A.Index) (j : B.Index) : IsOpen (atlasSymbolChartDomain A B c i j) := by
    simpa only [atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      c.continuousOn_symm.isOpen_inter_preimage c.open_target
        ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
  have hrestrict {U V : Set (EuclideanSpace ℝ (Fin n))} {r q : ℕ} {l : ℝ}
      {p : SymbolFunction n r q} (hp : IsSymbol U l p) (hVU : V ⊆ U) : IsSymbol V l p :=
    ⟨hp.1.mono (Set.prod_mono hVU subset_rfl),
      fun K hK hc i j ↦ hp.2 K (hK.trans hVU) hc i j⟩
  have hcov_smul (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (z η : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
      covectorFromChart c (c.symm z) (t • η) = t • covectorFromChart c (c.symm z) η := by
    ext v
    change inner ℝ (t • η) (mfderiv _ _ c (c.symm z) v) =
      t * inner ℝ η (mfderiv _ _ c (c.symm z) v)
    exact real_inner_smul_left η _ t
  have hcov_ne (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
      (η : EuclideanSpace ℝ (Fin n)) (hη : η ≠ 0) :
      covectorFromChart c (c.symm z) η ≠ 0 := by
    intro hzero
    have h := covectorInChart_covectorFromChart c hc (c.symm z) (c.map_target hz) η
    rw [hzero] at h
    have hzero' : covectorInChart c (c.symm z) 0 = 0 := by ext u; rfl
    exact hη (h.symm.trans hzero')
  have hhom (p : AtlasSymbolFunction (n := n) E F) (hp : IsHomogeneousAtlasSymbol m p)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) (j : B.Index) :
      IsHomogeneousSymbol (atlasSymbolChartDomain A B c i j) m
        (atlasGlobalSymbolInChart A B p c i j) := by
    intro z hz η hη t ht
    have hz' : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet :=
      ⟨hz.1.2, hz.2⟩
    have hη' := hcov_ne c hc z hz.1.1 η hη
    ext v
    simp [atlasGlobalSymbolInChart, hz', hcov_smul, hp _ _ hη' t ht]
    simp only [← Complex.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  -- Each metric has one exact recovery radius on any compact coordinate set.
  have hrecovery (ℓ : SmoothCotangentMetric (n := n) (M := M))
      (p : AtlasSymbolFunction (n := n) E F)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) (j : B.Index)
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hKV : K ⊆ atlasSymbolChartDomain A B c i j) :
      ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ η, R ≤ ‖η‖ →
        atlasGlobalSymbolInChart A B (atlasRegularizedSymbolFunction ℓ p) c i j z η =
          atlasGlobalSymbolInChart A B p c i j z η := by
    let L (z η : EuclideanSpace ℝ (Fin n)) :=
      ℓ.length (c.symm z) (covectorFromChart c (c.symm z) η)
    let S := K ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
    have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
    have hne (η : EuclideanSpace ℝ (Fin n))
        (hη : η ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : η ≠ 0 := by
      intro hz
      simp [hz] at hη
    have hcont : ContinuousOn (Function.uncurry L) S :=
      (ℓ.contDiffOn_length_covectorFromChart c hc).continuousOn.mono
        (fun z hz ↦ ⟨(hKV hz.1).1.1, hne z.2 hz.2⟩)
    obtain ⟨d, hd, hlow⟩ := hS.exists_forall_le' hcont (a := 0) (by
      intro z hz
      exact ℓ.length_pos _ _ (hcov_ne c hc z.1 (hKV hz.1).1.1 z.2 (hne z.2 hz.2)))
    refine ⟨d⁻¹, inv_pos.mpr hd, ?_⟩
    intro z hz η hη
    have hηpos : 0 < ‖η‖ := lt_of_lt_of_le (inv_pos.mpr hd) hη
    have hηne : η ≠ 0 := norm_pos_iff.mp hηpos
    let v := ‖η‖⁻¹ • η
    have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hηne
    have hscale : ‖η‖ • v = η := by simp [v, smul_smul, norm_ne_zero_iff.mpr hηne]
    have hlen : L z η = ‖η‖ * L z v := by
      dsimp [L]
      conv_lhs => rw [← hscale, hcov_smul, ℓ.length_smul]
      rw [abs_of_nonneg (norm_nonneg η)]
    have hlength : 1 ≤ L z η := by
      rw [hlen]
      have h := mul_le_mul_of_nonneg_left hη hd.le
      rw [mul_inv_cancel₀ hd.ne'] at h
      have hl := mul_le_mul_of_nonneg_left (hlow (z, v) ⟨hz, hv⟩) (norm_nonneg η)
      exact h.trans (by simpa only [Function.uncurry, mul_comm] using hl)
    have heq := (AtiyahSinger.atlasRegularizedSymbolFunction_cutoff ℓ p).2
      (c.symm z) (covectorFromChart c (c.symm z) η) hlength
    simp only [atlasGlobalSymbolInChart, heq]
  constructor
  · intro hclass x ξ hξ
    -- Select the original chart and both independent bundle frames at this same point.
    obtain ⟨i, hi⟩ := A.covers x
    obtain ⟨j, hj⟩ := B.covers x
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hc := chart_mem_atlas (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    let V := atlasSymbolChartDomain A B c i j
    have hz : c x ∈ V :=
      ⟨⟨c.map_source hx, by simpa only [Set.mem_preimage, c.left_inv hx] using hi⟩,
        by simpa only [Set.mem_preimage, c.left_inv hx] using hj⟩
    obtain ⟨K, hK, hzK, hKV⟩ := exists_compact_subset (hopen c i j) hz
    have hint : interior K ⊆ V := interior_subset.trans hKV
    obtain ⟨Rg, hRg, hag⟩ := hrecovery g a c hc i j K hK hKV
    obtain ⟨Rk, hRk, hbk⟩ := hrecovery k b c hc i j K hK hKV
    let A' : symbolSpace (interior K) isOpen_interior m (A.rank i) (B.rank j) :=
      ⟨atlasGlobalSymbolInChart A B (atlasRegularizedSymbolFunction g a) c i j,
        hrestrict ((isAtlasGlobalSymbol_atlasRegularizedSymbolFunction A B g m a ha hha)
          c hc i j) hint⟩
    let B' : symbolSpace (interior K) isOpen_interior m (A.rank i) (B.rank j) :=
      ⟨atlasGlobalSymbolInChart A B (atlasRegularizedSymbolFunction k b) c i j,
        hrestrict ((isAtlasGlobalSymbol_atlasRegularizedSymbolFunction A B k m b hb hhb)
          c hc i j) hint⟩
    have hdiff := (atlasGlobalPrincipalSymbolClass_eq_iff A B m _ _).mp hclass c hc i j
    have hdiff' : IsSymbol (interior K) (m - 1) (A'.val - B'.val) := by
      have hsub : atlasGlobalSymbolInChart A B
          ((atlasRegularizedSymbol A B g m a ha hha).val -
            (atlasRegularizedSymbol A B k m b hb hhb).val) c i j = A'.val - B'.val := by
        ext z η v
        by_cases hz : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet
        · simp [atlasGlobalSymbolInChart, A', B', atlasRegularizedSymbol, hz]
        · simp [atlasGlobalSymbolInChart, A', B', hz]
      rw [hsub] at hdiff
      exact hrestrict hdiff hint
    have hclass' := (principalSymbolClass_eq_iff isOpen_interior A' B').mpr hdiff'
    have hη : covectorInChart c x ξ ≠ 0 := by
      intro hz
      have h := covectorFromChart_covectorInChart c hc x hx ξ
      rw [hz] at h
      have hzero : covectorFromChart c x 0 = 0 := by
        ext v
        change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (mfderiv _ _ c x v) = 0
        exact inner_zero_left _
      exact hξ (h.symm.trans hzero)
    have hmap := homogeneous_eq_of_principalSymbolClass_eq isOpen_interior A' B'
      (atlasGlobalSymbolInChart A B a c i j) (atlasGlobalSymbolInChart A B b c i j)
      (fun z hz ↦ hhom a hha c hc i j z (hint hz))
      (fun z hz ↦ hhom b hhb c hc i j z (hint hz))
      (max Rg Rk) (lt_of_lt_of_le hRg (le_max_left _ _))
      (fun z hz η hη ↦ hag z (interior_subset hz) η ((le_max_left _ _).trans hη))
      (fun z hz η hη ↦ hbk z (interior_subset hz) η ((le_max_right _ _).trans hη))
      hclass' (c x) hzK (covectorInChart c x ξ) hη
    -- Undo the same frames before transporting the dependent base fiber back to x.
    let y := c.symm (c x)
    have hiy : y ∈ (A.chart i).baseSet := by simpa only [y, c.left_inv hx] using hi
    have hjy : y ∈ (B.chart j).baseSet := by simpa only [y, c.left_inv hx] using hj
    let input := (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).toLinearEquiv.trans
      (A.frameLinearEquiv i y hiy).symm
    let output := (B.frameLinearEquiv j y hjy).trans
      (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm.toLinearEquiv
    have hval : a y (covectorFromChart c y (covectorInChart c x ξ)) =
        b y (covectorFromChart c y (covectorInChart c x ξ)) := by
      unfold atlasGlobalSymbolInChart at hmap
      simp only [dite_eq_left (show c.symm (c x) ∈ (A.chart i).baseSet ∧
        c.symm (c x) ∈ (B.chart j).baseSet from ⟨hiy, hjy⟩)] at hmap
      ext v
      have htest := congrArg
        (fun T : EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ]
            EuclideanSpace ℂ (Fin (B.rank j)) ↦ output.symm (T (input.symm v))) hmap
      change output.symm (output ((a y (covectorFromChart c y (covectorInChart c x ξ)))
        (input (input.symm v)))) = output.symm
          (output ((b y (covectorFromChart c y (covectorInChart c x ξ)))
            (input (input.symm v)))) at htest
      simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] using htest
    have hxval : a x (covectorFromChart c x (covectorInChart c x ξ)) =
        b x (covectorFromChart c x (covectorInChart c x ξ)) :=
      (congrArg (fun z : M ↦ a z (covectorFromChart c z (covectorInChart c x ξ)) =
        b z (covectorFromChart c z (covectorInChart c x ξ))) (c.left_inv hx)).mp hval
    rwa [covectorFromChart_covectorInChart c hc x hx ξ] at hxval
  · intro hab
    apply (atlasGlobalPrincipalSymbolClass_eq_iff A B m _ _).mpr
    intro c hc i j
    let V := atlasSymbolChartDomain A B c i j
    let pg := atlasGlobalSymbolInChart A B (atlasRegularizedSymbolFunction g a) c i j
    let pk := atlasGlobalSymbolInChart A B (atlasRegularizedSymbolFunction k b) c i j
    have hsub : atlasGlobalSymbolInChart A B
        ((atlasRegularizedSymbol A B g m a ha hha).val -
          (atlasRegularizedSymbol A B k m b hb hhb).val) c i j = pg - pk := by
      ext z η v
      by_cases hz : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet
      · simp [atlasGlobalSymbolInChart, pg, pk, atlasRegularizedSymbol, hz]
      · simp [atlasGlobalSymbolInChart, pg, pk, hz]
    rw [hsub]
    have hg := (isAtlasGlobalSymbol_atlasRegularizedSymbolFunction A B g m a ha hha)
      c hc i j
    have hk := (isAtlasGlobalSymbol_atlasRegularizedSymbolFunction A B k m b hb hhb)
      c hc i j
    have hd : ContDiffOn ℝ ∞ (Function.uncurry (pg - pk)) (V ×ˢ Set.univ) := hg.1.sub hk.1
    refine ⟨hd, ?_⟩
    intro K hKV hK α β
    -- Both metric cutoffs agree on one enlarged base neighborhood above a common radius.
    obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK (hopen c i j) hKV
    obtain ⟨Rg, hRg, hag⟩ := hrecovery g a c hc i j K' hK' hK'V
    obtain ⟨Rk, hRk, hbk⟩ := hrecovery k b c hc i j K' hK' hK'V
    let R := max Rg Rk
    have hint : interior K' ⊆ V := interior_subset.trans hK'V
    have hsupp : ∀ z ∈ interior K', ∀ η, R ≤ ‖η‖ → (pg - pk) z η = 0 := by
      intro z hz η hη
      have hηne : η ≠ 0 := norm_pos_iff.mp
        (lt_of_lt_of_le hRg ((le_max_left Rg Rk).trans hη))
      have hvalue := hab (c.symm z) (covectorFromChart c (c.symm z) η)
        (hcov_ne c hc z (hint hz).1.1 η hηne)
      have hcoords : atlasGlobalSymbolInChart A B a c i j z η =
          atlasGlobalSymbolInChart A B b c i j z η := by
        simp only [atlasGlobalSymbolInChart, hvalue]
      change pg z η - pk z η = 0
      dsimp only [pg, pk]
      rw [hag z (interior_subset hz) η ((le_max_left _ _).trans hη),
        hbk z (interior_subset hz) η ((le_max_right _ _).trans hη), hcoords, sub_self]
    have hsmooth := isSmoothingSymbol_of_frequency_support isOpen_interior (pg - pk) R
      (hd.mono (Set.prod_mono hint subset_rfl)) hsupp (m - 1)
    exact hsmooth.2 K hKK' hK α β

end AtiyahSinger
