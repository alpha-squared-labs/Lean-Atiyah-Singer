/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousQuantization
public import AtiyahSinger.Geometry.CosphereBundle

import AtiyahSinger.Analysis.CosphereRegularity

/-!
# Smooth cosphere families on locally finite-rank bundles

Public module ID: M0235.

A03: restriction and radial extension use the specified fibers and metric
cosphere. Degree-zero radial extension defines smoothness and induces the
compact punctured C-infinity topology. Multiplication by the positive metric
length to a fixed real power gives continuous extension at that degree.

The fixed finite quantization retains the radial regularization as its
principal class. Continuous families in the smooth cosphere topology give
continuous Sobolev operators for the specified finite presentations.

Sources: SG III.3.18--3.19, III.7.10--7.11 and III.13 (13.5). The radial
and topology comparisons are project supplements; the family theorem uses
the smooth topology and does not approximate continuous homotopies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  (g : SmoothCotangentMetric (n := n) (M := M))

/-- Hom sections on the actual metric cosphere, with regularity supplied separately. -/
abbrev AtlasCosphereSymbolFunction : Type _ :=
  ∀ z : CosphereBundle g, E z.val.proj →ₗ[ℂ] F z.val.proj

/-- Restrict the original Hom field to the actual unit covectors. -/
def atlasCosphereRestriction (a : AtlasSymbolFunction (n := n) E F) :
    AtlasCosphereSymbolFunction (E := E) (F := F) g :=
  fun z ↦ a z.val.proj z.val.snd

/-- The actual positive radial extension, assigning zero on the zero section. -/
def atlasCosphereExtension (m : ℝ)
    (a : AtlasCosphereSymbolFunction (E := E) (F := F) g) :
    AtlasSymbolFunction (n := n) E F := by
  classical
  exact fun x ξ ↦ if hξ : ξ = 0 then 0 else
    ((g.length x ξ ^ m : ℝ) : ℂ) • a (g.radial ⟨⟨x, ξ⟩, hξ⟩)

/-- Smoothness of cosphere sections via their standard degree-zero radial extension. -/
def IsSmoothAtlasCosphereSymbol
    (a : AtlasCosphereSymbolFunction (E := E) (F := F) g) : Prop :=
  IsSmoothOffZeroAtlasSymbol A B (atlasCosphereExtension g 0 a)

/-- The standard carrier of smooth sections of the original Hom bundle over the cosphere. -/
abbrev SmoothAtlasCosphereSymbols : Type _ :=
  {a : AtlasCosphereSymbolFunction (E := E) (F := F) g // IsSmoothAtlasCosphereSymbol A B g a}

include hM in
/-- Smooth cosphere sections extend smoothly and homogeneously at every real degree. -/
theorem atlasCosphereExtension_properties (m : ℝ)
    (a : SmoothAtlasCosphereSymbols A B g) :
    IsSmoothOffZeroAtlasSymbol A B (atlasCosphereExtension g m a.val) ∧
      IsHomogeneousAtlasSymbol m (atlasCosphereExtension g m a.val) ∧
        atlasCosphereRestriction g (atlasCosphereExtension g m a.val) = a.val := by
  /- Stage 1: off zero, multiply the smooth degree-zero radial extension
  by the smooth positive metric length to the real power m. Positive
  dilation fixes the radial direction and scales length by its scalar;
  the real-power product rule gives degree-m homogeneity.
  Stage 2: on a unit covector the radial map is the identity and length
  is one. Thus restriction recovers the exact original section. For n=0
  the cosphere is empty and the extension is zero; no positive dimension
  or equal source/target rank is needed. -/
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- In each actual frame, change degree by the smooth positive metric-length weight.
    intro c hc i j
    let U : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
      atlasSymbolChartDomain A B c i j ×ˢ {ξ | ξ ≠ 0}
    let w (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
      g.length (c.symm p.1) (covectorFromChart c (c.symm p.1) p.2)
    have hne (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
        (hp : p ∈ U) : covectorFromChart c (c.symm p.1) p.2 ≠ 0 := by
      intro hz
      have hi := covectorInChart_covectorFromChart c hc (c.symm p.1)
        (c.map_target hp.1.1.1) p.2
      rw [hz] at hi
      have hzcoord : covectorInChart c (c.symm p.1) 0 = 0 := by ext j; rfl
      exact hp.2 (hi.symm.trans hzcoord)
    have hw : ContDiffOn ℝ ∞ w U :=
      (g.contDiffOn_length_covectorFromChart c hc).mono (fun _ hp ↦ ⟨hp.1.1.1, hp.2⟩)
    have hpow : ContDiffOn ℝ ∞ (fun p ↦ ((w p ^ m : ℝ) : ℂ)) U :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        (hw.rpow_const_of_ne (fun p hp ↦ (g.length_pos _ _ (hne p hp)).ne'))
    apply (hpow.smul (a.property c hc i j)).congr
    intro p hp
    have hval : atlasCosphereExtension g m a.val (c.symm p.1)
        (covectorFromChart c (c.symm p.1) p.2) =
        ((w p ^ m : ℝ) : ℂ) • atlasCosphereExtension g 0 a.val (c.symm p.1)
          (covectorFromChart c (c.symm p.1) p.2) := by
      simp only [atlasCosphereExtension, hne p hp, ↓reduceDIte, Real.rpow_zero,
        Complex.ofReal_one, one_smul]
      rfl
    have hframes : c.symm p.1 ∈ (A.chart i).baseSet ∧
        c.symm p.1 ∈ (B.chart j).baseSet := ⟨hp.1.1.2, hp.1.2⟩
    change atlasGlobalSymbolInChart A B (atlasCosphereExtension g m a.val) c i j p.1 p.2 =
      ((w p ^ m : ℝ) : ℂ) •
        atlasGlobalSymbolInChart A B (atlasCosphereExtension g 0 a.val) c i j p.1 p.2
    apply ContinuousLinearMap.ext
    intro v
    simp [atlasGlobalSymbolInChart, hframes, hval]
    simp only [← Complex.coe_smul, map_smul]
    rfl
  · -- Positive rescaling preserves the same radial direction and scales its length.
    intro x ξ hξ t ht
    have htξ : t • ξ ≠ 0 := smul_ne_zero ht.ne' hξ
    simp only [atlasCosphereExtension, htξ, hξ, ↓reduceDIte]
    rw [g.length_smul, abs_of_pos ht, Real.mul_rpow ht.le (g.length_pos x ξ hξ).le]
    let b : {η : CotangentFiber (n := n) x // g.length x η = 1} → (E x →ₗ[ℂ] F x) :=
      fun η ↦ a.val ⟨⟨x, η.val⟩, η.property⟩
    change (((t ^ m * g.length x ξ ^ m : ℝ) : ℂ) •
        b ⟨g.normalize x (t • ξ), g.length_normalize x (t • ξ) htξ⟩) =
      ((t ^ m : ℝ) : ℂ) • ((g.length x ξ ^ m : ℝ) : ℂ) •
        b ⟨g.normalize x ξ, g.length_normalize x ξ hξ⟩
    rw [Complex.ofReal_mul, mul_smul]
    congr 2
    exact congrArg b (Subtype.ext (g.normalize_pos_smul x ξ t ht))
  · -- Restriction to a unit covector recovers the original fiber value exactly.
    funext z
    obtain ⟨⟨x, ξ⟩, hunit⟩ := z
    have hξ : ξ ≠ 0 := g.cosphere_ne_zero ⟨⟨x, ξ⟩, hunit⟩
    change atlasCosphereExtension g m a.val x ξ = a.val ⟨⟨x, ξ⟩, hunit⟩
    simp only [atlasCosphereExtension, hξ, ↓reduceDIte, hunit, Real.one_rpow,
      Complex.ofReal_one, one_smul]
    let b : {η : CotangentFiber (n := n) x // g.length x η = 1} → (E x →ₗ[ℂ] F x) :=
      fun η ↦ a.val ⟨⟨x, η.val⟩, η.property⟩
    change b ⟨g.normalize x ξ, g.length_normalize x ξ hξ⟩ = b ⟨ξ, hunit⟩
    congr 1
    exact Subtype.ext (g.normalize_of_length_eq_one x ξ hunit)

/-- The actual extension as an element of the smooth homogeneous-symbol space. -/
def smoothAtlasCosphereExtension (m : ℝ) (a : SmoothAtlasCosphereSymbols A B g) :
    homogeneousAtlasSymbolSpace A B m :=
  ⟨atlasCosphereExtension g m a.val, (atlasCosphereExtension_properties A B g m a).1,
    (atlasCosphereExtension_properties A B g m a).2.1⟩

attribute [local instance] atlasHomogeneousSymbolTopology

/-- The standard smooth topology represented by degree-zero extension, before quantization. -/
@[instance_reducible]
def smoothAtlasCosphereSymbolTopology : TopologicalSpace (SmoothAtlasCosphereSymbols A B g) :=
  TopologicalSpace.induced (smoothAtlasCosphereExtension A B g 0) inferInstance

attribute [local instance] smoothAtlasCosphereSymbolTopology

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
-- The extended limit accommodates the punctured derivative estimates for radial extension.
open Filter in
/-- Extension at every fixed real degree is continuous in the punctured derivative topology. -/
theorem continuous_smoothAtlasCosphereExtension (m : ℝ) :
    Continuous (smoothAtlasCosphereExtension A B g m) := by
  /- Degree-zero extension defines the standard smooth section topology:
  radial restriction is its inverse on the unit cosphere, and smooth
  radial projection compares compact derivative tests with those on the
  sphere. For any fixed real m, multiply by length^m off zero. Leibniz
  bounds on each compact punctured product control this operation by
  finitely many source derivative seminorms. This is independent of the
  choice of quantization, and makes no assertion about C-zero families. -/
  classical
  let P := EuclideanSpace ℝ (Fin n)
  let mixed {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :=
    iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) x
  -- Parameter differentiation retains smooth dependence on both original variables.
  have parametric {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (x ξ : P)
      (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, ξ)) (j : ℕ) :
      ContDiffAt ℝ ∞ (fun p : P × P ↦ iteratedFDeriv ℝ j (f p.1) p.2) (x, ξ) := by
    induction j with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ P V).symm : _ →L[ℝ] P [×0]→L[ℝ] V)
    | succ j ih =>
      have h : ContDiffAt ℝ ∞
          (Function.uncurry (fun p : P × P ↦ fun z : P ↦ iteratedFDeriv ℝ j (f p.1) z))
          ((x, ξ), ξ) := ih.comp ((x, ξ), ξ) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hd : ContDiffAt ℝ ∞
          (fun p : P × P ↦ fderiv ℝ (iteratedFDeriv ℝ j (f p.1)) p.2) (x, ξ) :=
        h.fderiv contDiffAt_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ P) V).symm :
          _ →L[ℝ] P [×(j + 1)]→L[ℝ] V)
  -- Currying identifies derivatives of fderiv f with the next frequency derivative.
  have mixed_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ fderiv ℝ (f y) η) i j x ξ‖ = ‖mixed f i (j + 1) x ξ‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ (j + 1) (f y) ξ) =
        (continuousMultilinearCurryRightEquiv' ℝ j P V).symm ∘
          (fun y ↦ iteratedFDeriv ℝ j (fderiv ℝ (f y)) ξ) := by
      funext y
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact ((continuousMultilinearCurryRightEquiv' ℝ j P V).symm.norm_iteratedFDeriv_comp_left
      (fun y ↦ iteratedFDeriv ℝ j (fderiv ℝ (f y)) ξ) x i).symm
  have mixed_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i : ℕ) (x ξ : P) :
      ‖mixed f i 0 x ξ‖ = ‖iteratedFDeriv ℝ i (fun y ↦ f y ξ) x‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ 0 (f y) ξ) =
        (continuousMultilinearCurryFin0 ℝ P V).symm ∘ (fun y ↦ f y ξ) := by
      rfl
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  have smooth_frequency_derivative {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      {U Ω : Set P} (hU : IsOpen U) (hΩ : IsOpen Ω) (f : P → P → V)
      (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ Ω)) :
      ContDiffOn ℝ ∞ (fun p : P × P ↦ fderiv ℝ (f p.1) p.2) (U ×ˢ Ω) := by
    intro p hp
    have hf' := hf.contDiffAt ((hU.prod hΩ).mem_nhds hp)
    have h : ContDiffAt ℝ ∞
        (Function.uncurry (fun z : P × P ↦ fun η : P ↦ f z.1 η)) (p, p.2) :=
      hf'.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact (h.fderiv contDiffAt_snd (by simp)).contDiffWithinAt
  have mixed_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      {U Ω : Set P} (hU : IsOpen U) (hΩ : IsOpen Ω) (f g : P → P → V)
      (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ Ω))
      (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ Ω))
      (i j : ℕ) (x ξ : P) (hx : x ∈ U) (hξ : ξ ∈ Ω) :
      mixed (fun y η ↦ f y η + g y η) i j x ξ =
        mixed f i j x ξ + mixed g i j x ξ := by
    have hlocal (y η : P) (hy : y ∈ U) (hη : η ∈ Ω) :
        ContDiffAt ℝ ∞ (Function.uncurry f) (y, η) ∧
          ContDiffAt ℝ ∞ (Function.uncurry g) (y, η) :=
      ⟨hf.contDiffAt ((hU.prod hΩ).mem_nhds ⟨hy, hη⟩),
        hg.contDiffAt ((hU.prod hΩ).mem_nhds ⟨hy, hη⟩)⟩
    have heq : (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ f y η + g y η) ξ) =ᶠ[𝓝 x]
        (fun y ↦ iteratedFDeriv ℝ j (f y) ξ + iteratedFDeriv ℝ j (g y) ξ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact iteratedFDeriv_add_apply
        (((hlocal y ξ hy hξ).1.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
        (((hlocal y ξ hy hξ).2.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
    have hf' := (parametric f x ξ (hlocal x ξ hx hξ).1 j).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
    have hg' := (parametric g x ξ (hlocal x ξ hx hξ).2 j).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
    exact ((heq.iteratedFDeriv ℝ i).eq_of_nhds).trans
      (iteratedFDeriv_add_apply (hf'.of_le (by simp)) (hg'.of_le (by simp)))
  have estimate (j : ℕ) : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {V W Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
        [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
        (B : V →L[ℝ] W →L[ℝ] Z) (f : P → P → V) (g : P → P → W)
        (U Ω : Set P) (hU : IsOpen U) (hΩ : IsOpen Ω)
        (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ Ω))
        (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ Ω))
        (x ξ : P) (hx : x ∈ U) (hξ : ξ ∈ Ω)
        (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D),
        (∀ a ≤ i, ∀ b ≤ j, ‖mixed f a b x ξ‖ ≤ A) →
        (∀ a ≤ i, ∀ b ≤ j, ‖mixed g a b x ξ‖ ≤ D) →
        ‖mixed (fun y η ↦ B (f y η) (g y η)) i j x ξ‖ ≤ C * ‖B‖ * A * D := by
    induction j with
    | zero =>
      intro i
      refine ⟨∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ),
        Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _), ?_⟩
      intro V W Z _ _ _ _ _ _ B f g U Ω hU hΩ hf hg x ξ hx hξ A D hA hD hfb hgb
      rw [mixed_zero]
      have hf' : ContDiffOn ℝ ∞ (fun y ↦ f y ξ) U :=
        hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hξ⟩)
      have hg' : ContDiffOn ℝ ∞ (fun y ↦ g y ξ) U :=
        hg.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hξ⟩)
      have h := B.norm_iteratedFDerivWithin_le_of_bilinear hf' hg' hU.uniqueDiffOn hx
        (n := i) (by simp)
      simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at h
      apply h.trans
      calc
        ‖B‖ * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
            ‖iteratedFDeriv ℝ k (fun y ↦ f y ξ) x‖ *
            ‖iteratedFDeriv ℝ (i - k) (fun y ↦ g y ξ) x‖ ≤
            ‖B‖ * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * A * D := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply Finset.sum_le_sum
          intro k hk
          have hfk := hfb k (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)) 0 (by simp)
          have hgk := hgb (i - k) (Nat.sub_le _ _) 0 (by simp)
          rw [mixed_zero] at hfk hgk
          exact mul_le_mul (mul_le_mul_of_nonneg_left hfk (Nat.cast_nonneg _)) hgk
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
        _ = _ := by simp only [← Finset.sum_mul]; ring
    | succ j ih =>
      intro i
      obtain ⟨C, hC, hbound⟩ := ih i
      refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
      intro V W Z _ _ _ _ _ _ B f g U Ω hU hΩ hf hg x ξ hx hξ A D hA hD hfb hgb
      let df : P → P → P →L[ℝ] V := fun y η ↦ fderiv ℝ (f y) η
      let dg : P → P → P →L[ℝ] W := fun y η ↦ fderiv ℝ (g y) η
      have hdf := smooth_frequency_derivative hU hΩ f hf
      have hdg := smooth_frequency_derivative hU hΩ g hg
      have hdfb : ∀ a ≤ i, ∀ b ≤ j, ‖mixed df a b x ξ‖ ≤ A := by
        intro a ha b hb
        rw [mixed_shift]
        exact hfb a ha (b + 1) (Nat.add_le_add_right hb 1)
      have hdgb : ∀ a ≤ i, ∀ b ≤ j, ‖mixed dg a b x ξ‖ ≤ D := by
        intro a ha b hb
        rw [mixed_shift]
        exact hgb a ha (b + 1) (Nat.add_le_add_right hb 1)
      let p : P → P → P →L[ℝ] Z := fun y η ↦ B.precompR P (f y η) (dg y η)
      let q : P → P → P →L[ℝ] Z := fun y η ↦ B.precompL P (df y η) (g y η)
      have hp := hbound (B.precompR P) f dg U Ω hU hΩ hf hdg x ξ hx hξ A D hA hD
        (fun a ha b hb ↦ hfb a ha b (Nat.le_trans hb (Nat.le_succ j))) hdgb
      have hq := hbound (B.precompL P) df g U Ω hU hΩ hdf hg x ξ hx hξ A D hA hD
        hdfb (fun a ha b hb ↦ hgb a ha b (Nat.le_trans hb (Nat.le_succ j)))
      have hps : ContDiffOn ℝ ∞ (Function.uncurry p) (U ×ˢ Ω) :=
        (B.precompR P).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hf hdg
      have hqs : ContDiffOn ℝ ∞ (Function.uncurry q) (U ×ˢ Ω) :=
        (B.precompL P).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hdf hg
      have heq : (fun y ↦ iteratedFDeriv ℝ j
          (fun η ↦ fderiv ℝ (fun η ↦ B (f y η) (g y η)) η) ξ) =ᶠ[𝓝 x]
          (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ p y η + q y η) ξ) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        have hinner : (fun η ↦ fderiv ℝ (fun η ↦ B (f y η) (g y η)) η) =ᶠ[𝓝 ξ]
            (fun η ↦ p y η + q y η) := by
          filter_upwards [hΩ.mem_nhds hξ] with η hη
          have hf' := (hf.contDiffAt ((hU.prod hΩ).mem_nhds ⟨hy, hη⟩)).comp η
            (contDiffAt_const.prodMk contDiffAt_id)
          have hg' := (hg.contDiffAt ((hU.prod hΩ).mem_nhds ⟨hy, hη⟩)).comp η
            (contDiffAt_const.prodMk contDiffAt_id)
          exact B.fderiv_of_bilinear (hf'.differentiableAt (by simp))
            (hg'.differentiableAt (by simp))
        exact (hinner.iteratedFDeriv ℝ j).eq_of_nhds
      rw [← mixed_shift]
      change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
      rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds]
      change ‖mixed (fun y η ↦ p y η + q y η) i j x ξ‖ ≤ _
      rw [mixed_add hU hΩ p q hps hqs i j x ξ hx hξ]
      apply (norm_add_le _ _).trans
      apply (add_le_add hp hq).trans
      have hpr : C * ‖B.precompR P‖ * A * D ≤ C * ‖B‖ * A * D := by
        gcongr
        exact ContinuousLinearMap.norm_precompR_le P B
      have hpl : C * ‖B.precompL P‖ * A * D ≤ C * ‖B‖ * A * D := by
        gcongr
        exact ContinuousLinearMap.norm_precompL_le P B
      exact (add_le_add hpr hpl).trans_eq (by ring)
  -- Degree zero is the inducing map; every other degree multiplies this same field.
  let S := smoothAtlasCosphereExtension A B g 0
  let T := smoothAtlasCosphereExtension A B g m
  let w (x : M) (ξ : CotangentFiber (n := n) x) : ℂ := (g.length x ξ ^ m : ℝ)
  have hw (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) :
      ContDiffOn ℝ ∞ (fun p ↦ w (c.symm p.1) (covectorFromChart c (c.symm p.1) p.2))
        (c.target ×ˢ {ξ | ξ ≠ 0}) := by
    apply Complex.ofRealCLM.contDiff.comp_contDiffOn
    apply (g.contDiffOn_length_covectorFromChart c hc).rpow_const_of_ne
    intro p hp
    apply (g.length_pos _ _ ?_).ne'
    intro hzero
    have hi := covectorInChart_covectorFromChart c hc (c.symm p.1) (c.map_target hp.1) p.2
    rw [hzero] at hi
    exact hp.2 (hi.symm.trans (by ext k; rfl))
  have hT (a : SmoothAtlasCosphereSymbols A B g) (x : M)
      (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      (T a).val x ξ = w x ξ • (S a).val x ξ := by
    simp only [T, S, smoothAtlasCosphereExtension, atlasCosphereExtension,
      hξ, ↓reduceDIte, Real.rpow_zero, Complex.ofReal_one, one_smul]
    rfl
  -- On each compact product the fixed multiplier has finitely many bounded derivatives.
  have hbound (J : AtlasHomogeneousSymbolSeminormIndex A B) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ a b,
        atlasHomogeneousSymbolSeminorm A B m J (T a - T b) ≤ C *
          ∑ i ∈ Finset.range (J.localIndex.spatialOrder + 1),
            ∑ j ∈ Finset.range (J.localIndex.frequencyOrder + 1),
              atlasHomogeneousSymbolSeminorm A B 0
                { J with
                  localIndex := { J.localIndex with spatialOrder := i, frequencyOrder := j } }
                (S a - S b) := by
    let U := atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
    have hU : IsOpen U := isOpen_atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex
    let K := J.localIndex.compactSet
    let L := J.frequencySet
    let H := EuclideanSpace ℂ (Fin (A.rank J.inputIndex)) →L[ℂ]
      EuclideanSpace ℂ (Fin (B.rank J.outputIndex))
    let v : P → P → ℂ := fun x ξ ↦
      w (J.chart.symm x) (covectorFromChart J.chart (J.chart.symm x) ξ)
    have hv : ContDiffOn ℝ ∞ (Function.uncurry v) (U ×ˢ {ξ | ξ ≠ 0}) :=
      (hw J.chart J.mem_atlas).mono (fun _ hp ↦ ⟨hp.1.1.1, hp.2⟩)
    have hvb (i j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ ∈ L,
        ‖mixed v i j x ξ‖ ≤ C := by
      have hcont : ContinuousOn (fun p : P × P ↦ mixed v i j p.1 p.2) (K ×ˢ L) := by
        intro p hp
        have hvp := hv.contDiffAt ((hU.prod isOpen_ne).mem_nhds
          ⟨J.localIndex.subset_domain hp.1, J.frequency_ne_zero p.2 hp.2⟩)
        have hξ := parametric v p.1 p.2 hvp j
        have hswap : ContDiffAt ℝ ∞
            (Function.uncurry (fun ξ x ↦ iteratedFDeriv ℝ j (v x) ξ)) (p.2, p.1) :=
          hξ.comp (p.2, p.1) (contDiffAt_snd.prodMk contDiffAt_fst)
        have hx := parametric _ p.2 p.1 hswap i
        exact ((hx.comp p (contDiffAt_snd.prodMk contDiffAt_fst)).continuousAt).continuousWithinAt
      have hcompact := J.localIndex.isCompact.prod J.isCompact_frequencySet
      obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont
      exact ⟨max C 0, le_max_right _ _, fun x hx ξ hξ ↦
        (hC (x, ξ) ⟨hx, hξ⟩).trans (le_max_left _ _)⟩
    choose D hD hvb using hvb
    let i := J.localIndex.spatialOrder
    let j := J.localIndex.frequencyOrder
    let Cweight : ℝ := ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), D a b
    have hA : 0 ≤ Cweight := Finset.sum_nonneg (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ hD a b))
    have hDA (a b : ℕ) (ha : a ≤ i) (hb : b ≤ j) : D a b ≤ Cweight := by
      apply (Finset.single_le_sum (fun k _ ↦ hD a k)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hb))).trans
      exact Finset.single_le_sum (fun k _ ↦ Finset.sum_nonneg (fun t _ ↦ hD k t))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))
    obtain ⟨C, hC, hestimate⟩ := estimate j i
    let μ : ℂ →L[ℝ] H →L[ℝ] H := ContinuousLinearMap.lsmul ℝ ℂ
    refine ⟨C * ‖μ‖ * Cweight, mul_nonneg (mul_nonneg hC (norm_nonneg _)) hA, ?_⟩
    intro a b
    let Q (s t : ℕ) : AtlasHomogeneousSymbolSeminormIndex A B :=
      { J with localIndex := { J.localIndex with spatialOrder := s, frequencyOrder := t } }
    let R : ℝ := ∑ s ∈ Finset.range (i + 1),
      ∑ t ∈ Finset.range (j + 1), atlasHomogeneousSymbolSeminorm A B 0 (Q s t) (S a - S b)
    have hR : 0 ≤ R := Finset.sum_nonneg (fun s _ ↦ Finset.sum_nonneg
      (fun t _ ↦ apply_nonneg (atlasHomogeneousSymbolSeminorm A B 0 (Q s t)) _))
    have hQR (s t : ℕ) (hs : s ≤ i) (ht : t ≤ j) :
        atlasHomogeneousSymbolSeminorm A B 0 (Q s t) (S a - S b) ≤ R := by
      apply (Finset.single_le_sum (fun k _ ↦ apply_nonneg
        (atlasHomogeneousSymbolSeminorm A B 0 (Q s k)) _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))).trans
      exact Finset.single_le_sum (fun k _ ↦ Finset.sum_nonneg (fun u _ ↦ apply_nonneg
        (atlasHomogeneousSymbolSeminorm A B 0 (Q k u)) _))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hs))
    let f := atlasGlobalSymbolInChart A B (S a - S b).val J.chart J.inputIndex J.outputIndex
    let out := atlasGlobalSymbolInChart A B (T a - T b).val J.chart J.inputIndex J.outputIndex
    have hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ {ξ | ξ ≠ 0}) :=
      (S a - S b).property.1 J.chart J.mem_atlas J.inputIndex J.outputIndex
    have heq (x ξ : P) (hx : x ∈ U) (hξ : ξ ≠ 0) : out x ξ = v x ξ • f x ξ := by
      have hne : covectorFromChart J.chart (J.chart.symm x) ξ ≠ 0 := by
        intro hz
        have h := covectorInChart_covectorFromChart J.chart J.mem_atlas
          (J.chart.symm x) (J.chart.map_target hx.1.1) ξ
        rw [hz] at h
        exact hξ (h.symm.trans (by ext k; rfl))
      change atlasGlobalSymbolInChart A B ((T a).val - (T b).val) J.chart J.inputIndex
        J.outputIndex x ξ = v x ξ • atlasGlobalSymbolInChart A B ((S a).val - (S b).val)
          J.chart J.inputIndex J.outputIndex x ξ
      apply ContinuousLinearMap.ext
      intro u
      have hframes : J.chart.symm x ∈ (A.chart J.inputIndex).baseSet ∧
          J.chart.symm x ∈ (B.chart J.outputIndex).baseSet := ⟨hx.1.2, hx.2⟩
      simp [atlasGlobalSymbolInChart, hframes, hT a _ _ hne, hT b _ _ hne,
        ← smul_sub, v]
    have hpoint (x ξ : P) (hx : x ∈ K) (hξ : ξ ∈ L) :
        ‖mixed out i j x ξ‖ ≤ C * ‖μ‖ * Cweight * R := by
      have hder : mixed out i j x ξ = mixed (fun y η ↦ μ (v y η) (f y η)) i j x ξ := by
        have houter : (fun y ↦ iteratedFDeriv ℝ j (out y) ξ) =ᶠ[𝓝 x]
            (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ μ (v y η) (f y η)) ξ) := by
          filter_upwards [hU.mem_nhds (J.localIndex.subset_domain hx)] with y hy
          have hinner : out y =ᶠ[𝓝 ξ] (fun η ↦ μ (v y η) (f y η)) := by
            filter_upwards [isOpen_ne.mem_nhds (J.frequency_ne_zero ξ hξ)] with η hη
            exact heq y η hy hη
          exact (hinner.iteratedFDeriv ℝ j).eq_of_nhds
        exact (houter.iteratedFDeriv ℝ i).eq_of_nhds
      rw [hder]
      apply hestimate μ v f U {ξ | ξ ≠ 0} hU isOpen_ne hv hf x ξ
        (J.localIndex.subset_domain hx) (J.frequency_ne_zero ξ hξ) Cweight R hA hR
      · intro s hs t ht
        exact (hvb s t x hx ξ hξ).trans (hDA s t hs ht)
      · intro s hs t ht
        apply le_trans ?_ (hQR s t hs ht)
        exact le_csSup (bddAbove_atlasHomogeneousSymbolSeminormValue_set A B 0 (Q s t) (S a - S b))
          ⟨x, hx, ξ, hξ, rfl⟩
    change atlasHomogeneousSymbolSeminorm A B m J (T a - T b) ≤ C * ‖μ‖ * Cweight * R
    change atlasHomogeneousSymbolSeminormValue A B m J (T a - T b) ≤ _
    by_cases hK : K.Nonempty
    · by_cases hL : L.Nonempty
      · apply csSup_le
        · obtain ⟨x, hx⟩ := hK
          obtain ⟨ξ, hξ⟩ := hL
          exact ⟨_, ⟨x, hx, ξ, hξ, rfl⟩⟩
        · rintro t ⟨x, hx, ξ, hξ, rfl⟩
          exact hpoint x ξ hx hξ
      · have hL' : J.frequencySet = ∅ := Set.not_nonempty_iff_eq_empty.mp hL
        simp only [atlasHomogeneousSymbolSeminormValue, hL', Set.mem_empty_iff_false,
          false_and, exists_false, and_false, Set.ofPred_false, Real.sSup_empty]
        positivity
    · have hK' : J.localIndex.compactSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hK
      simp only [atlasHomogeneousSymbolSeminormValue, hK', Set.mem_empty_iff_false,
        false_and, exists_false, Set.ofPred_false, Real.sSup_empty]
      positivity
  -- Difference seminorms tend to zero; finite lower-order tests control every output test.
  have : IsTopologicalAddGroup (homogeneousAtlasSymbolSpace A B 0) :=
    (withSeminorms_atlasHomogeneousSymbolTopology A B 0).isTopologicalAddGroup
  have hS : Continuous S := continuous_induced_dom
  rw [continuous_iff_continuousAt]
  intro a
  apply (tendsto_atlasHomogeneousSymbolTopology_iff A B m (𝓝 a) T (T a)).mpr
  intro J ε hε
  obtain ⟨C, hC, hb⟩ := hbound J
  let R (b : SmoothAtlasCosphereSymbols A B g) : ℝ :=
    ∑ i ∈ Finset.range (J.localIndex.spatialOrder + 1),
      ∑ j ∈ Finset.range (J.localIndex.frequencyOrder + 1),
        atlasHomogeneousSymbolSeminorm A B 0
          { J with
            localIndex := { J.localIndex with spatialOrder := i, frequencyOrder := j } } (S b - S a)
  have hR : Tendsto R (𝓝 a) (𝓝 0) := by
    have hcont : Continuous R := by
      apply continuous_finsetSum
      intro i hi
      apply continuous_finsetSum
      intro j hj
      exact ((withSeminorms_atlasHomogeneousSymbolTopology A B 0).continuous_seminorm
        { J with
          localIndex := { J.localIndex with spatialOrder := i, frequencyOrder := j } }).comp
            (hS.sub continuous_const)
    have hz : R a = 0 := by simp [R]
    simpa only [hz] using (hcont.continuousAt (x := a)).tendsto
  have hCR : Tendsto (fun b ↦ C * R b) (𝓝 a) (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hR
  have hsmall := hCR.eventually (Iio_mem_nhds hε)
  filter_upwards [hsmall] with b hbsmall
  exact lt_of_le_of_lt (hb b a) hbsmall

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

namespace AtlasQuantizationPresentation

variable {A B} (C : AtlasQuantizationPresentation A B)

/-- Quantize a smooth cosphere section with the same metric, order, and finite coordinate data. -/
def quantizeCosphere (m : ℝ) (a : SmoothAtlasCosphereSymbols A B g) :
    AtlasPseudodifferentialOperator A B m :=
  C.quantizeHomogeneous g m (smoothAtlasCosphereExtension A B g m a)

/-- The actual cosphere realization retains its exact homogeneous principal representative. -/
theorem principalSymbol_quantizeCosphere (m : ℝ) (a : SmoothAtlasCosphereSymbols A B g) :
    (C.quantizeCosphere g m a).principalSymbol =
      atlasGlobalPrincipalSymbolClass A B m
        (atlasRegularizationLinearMap A B g m (smoothAtlasCosphereExtension A B g m a)) := by
  /- Apply principalSymbol_quantize to the same radial regularization.
  The extension theorem recovers a on the unit cosphere. Thus the
  principal data are precisely those supplied, rather than an unrelated
  representative selected using an existence theorem. -/
  exact C.principalSymbol_quantize
    (atlasRegularizationLinearMap A B g m (smoothAtlasCosphereExtension A B g m a))

/-- A smooth-topology cosphere family quantizes continuously in the actual Sobolev operator norm. -/
theorem continuous_sobolevQuantizeCosphere (m s : ℝ)
    (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B)
    {Z : Type*} [TopologicalSpace Z] (a : Z → SmoothAtlasCosphereSymbols A B g)
    (ha : Continuous a) :
    Continuous (fun z ↦ (C.quantizeCosphere g m (a z)).sobolevExtension L K s) := by
  /- Compose the continuous radial extension at degree m, the fixed
  metric regularization, and the fixed Sobolev quantization CLM.
  Each stage acts on the same original E,F fibers and the same symbol.
  All charts, frames, cutoffs and Sobolev presentations stay fixed for
  the whole family. No compactness of the parameter space is required. -/
  exact C.continuous_sobolevQuantizeHomogeneous g m L K
    (fun z ↦ smoothAtlasCosphereExtension A B g m (a z))
    ((continuous_smoothAtlasCosphereExtension A B g m).comp ha) s

end AtlasQuantizationPresentation

end AtiyahSinger
