/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialOperator
public import AtiyahSinger.Geometry.AtlasHermitianMetric
public import AtiyahSinger.Geometry.AtlasSectionMaps
public import AtiyahSinger.Geometry.HermitianPairing
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Matrix.Normed

import AtiyahSinger.Analysis.FrameChange
import AtiyahSinger.Analysis.LocalAdjoint

/-!
# Formal adjoints on noncompact bundle atlases

Public module ID: M0241.

UL03: the supplied Hermitian forms and smooth positive measure determine
fiber adjoints and the integral adjunction identity. Finite-dimensional
Riesz adjunction gives the fiber map; positive Gram operators prove its
smoothness. Locally varying and unequal ranks are allowed. A bijective
isometry has its inverse as adjoint for these same forms.

The integral identity tests a compactly supported source against an
arbitrary smooth target, which gives uniqueness on all smooth sections.
A smooth multiplier plus a finite sum of order-zero Fourier pieces has
a smooth formal adjoint. Reversing the specified cutoffs confines its
residual from the metric-adjoint multiplier to the supplied compact set.
The base need not be compact.

Sources: SG III.3, pp.183, 185--187, and III.13.4, p.248;
Taylor II.4.1--4.2, p.45.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap ComplexConjugate Matrix.Norms.Elementwise

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)
  (h : ComplexBundle.ContinuousHermitianMetric E)
  (k : ComplexBundle.ContinuousHermitianMetric F)

include A B in
/-- The metric adjoint exists on each original locally finite-dimensional fiber. -/
theorem existsUnique_atlasFiberAdjoint (x : M) (c : E x →ₗ[ℂ] F x) :
    ∃! d : F x →ₗ[ℂ] E x, ∀ u : E x, ∀ v : F x,
      (k.toCore x).inner (c u) v = (h.toCore x).inner u (d v) := by
  /- The covering frames establish finite dimensionality of the two fibers.
  Equip each fiber locally with the inner product induced by its supplied
  positive form and apply finite-dimensional Riesz adjunction. Definiteness
  makes the pairing identity unique on the same original fibers. -/
  classical
  -- Use finite-dimensional Riesz adjunction locally for the two specified forms.
  obtain ⟨i, hi⟩ := A.covers x
  obtain ⟨j, hj⟩ := B.covers x
  let : FiniteDimensional ℂ (E x) :=
    (A.frameLinearEquiv i x hi).symm.finiteDimensional
  let : FiniteDimensional ℂ (F x) :=
    (B.frameLinearEquiv j x hj).symm.finiteDimensional
  let moduleE : Module ℂ (E x) := inferInstance
  let moduleF : Module ℂ (F x) := inferInstance
  let : NormedAddCommGroup (E x) := (h.toCore x).toNormedAddCommGroup
  let : Module ℂ (E x) := moduleE
  let : InnerProductSpace ℂ (E x) := InnerProductSpace.ofCore (h.toCore x).toCore
  let : NormedAddCommGroup (F x) := (k.toCore x).toNormedAddCommGroup
  let : Module ℂ (F x) := moduleF
  let : InnerProductSpace ℂ (F x) := InnerProductSpace.ofCore (k.toCore x).toCore
  refine ⟨c.adjoint, ?_, ?_⟩
  · intro u v
    exact (LinearMap.adjoint_inner_right c u v).symm
  · intro d hd
    -- Definiteness makes the pairing property determine every value on the original fiber.
    apply LinearMap.ext
    intro v
    apply ext_inner_left ℂ
    intro u
    exact (hd u v).symm.trans (LinearMap.adjoint_inner_right c u v).symm

/-- The actual original-fiber adjoint selected by its unique pairing property. -/
def atlasFiberAdjoint (x : M) (c : E x →ₗ[ℂ] F x) : F x →ₗ[ℂ] E x :=
  (existsUnique_atlasFiberAdjoint A B h k x c).exists.choose

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]

include hM hT hSC in
open scoped ComplexConjugate Matrix.Norms.Elementwise in
set_option linter.unusedSectionVars false in
/-- Smooth adjoints retain their exact pairing and invertibility properties. -/
theorem atlasFiberAdjoint_properties (hh : A.IsSmoothHermitianMetric h)
    (hk : B.IsSmoothHermitianMetric k) (c : ∀ x, E x →ₗ[ℂ] F x)
    (hc : IsSmoothAtlasBundleMap A B c) :
    IsSmoothAtlasBundleMap B A (fun x ↦ atlasFiberAdjoint A B h k x (c x)) ∧
      (∀ x u v, (k.toCore x).inner (c x u) v =
        (h.toCore x).inner u (atlasFiberAdjoint A B h k x (c x) v)) ∧
      (∀ x, Function.Bijective (atlasFiberAdjoint A B h k x (c x)) ↔
        Function.Bijective (c x)) := by
  /- The chosen map has its defining pairing identity. In each frame its
  coordinates are H_E⁻¹ c* H_F, so smooth Gram operators and their inverses
  prove smoothness. Finite-dimensional orthogonal kernel/range duality
  identifies adjoint injectivity with original surjectivity and adjoint
  surjectivity with original injectivity, giving bijectivity equivalence. -/
  classical
  have hpair (x : M) (u : E x) (v : F x) :
      (k.toCore x).inner (c x u) v =
        (h.toCore x).inner u (atlasFiberAdjoint A B h k x (c x) v) :=
    (existsUnique_atlasFiberAdjoint A B h k x (c x)).exists.choose_spec u v
  refine ⟨?_, hpair, ?_⟩
  · refine ⟨contMDiff_id, ?_⟩
    intro j i l
    let V := Fin (A.rank i) → ℂ
    let W := Fin (B.rank j) → ℂ
    let S : Set M := (B.chart j).baseSet ∩ (A.chart i).baseSet
    let H (y : M) : Matrix (Fin (A.rank i)) (Fin (A.rank i)) ℂ :=
      fun a b ↦ if hy : y ∈ (A.chart i).baseSet then
        (h.toCore y).inner ((A.frameLinearEquiv i y hy).symm (Pi.single a 1))
          ((A.frameLinearEquiv i y hy).symm (Pi.single b 1)) else 0
    let K (y : M) : Matrix (Fin (B.rank j)) (Fin (B.rank j)) ℂ :=
      fun a b ↦ if hy : y ∈ (B.chart j).baseSet then
        (k.toCore y).inner ((B.frameLinearEquiv j y hy).symm (Pi.single a 1))
          ((B.frameLinearEquiv j y hy).symm (Pi.single b 1)) else 0
    let C (y : M) (a : Fin (A.rank i)) : W :=
      if hy : y ∈ (A.chart i).baseSet then
        (B.chart j ⟨y, c y ((A.frameLinearEquiv i y hy).symm (Pi.single a 1))⟩).2
      else 0
    -- A local coordinate expansion works for either of the two original positive forms.
    have hexpand (r : ℕ) (Q : (Fin r → ℂ) →ₗ⋆[ℂ] (Fin r → ℂ) →ₗ[ℂ] ℂ)
        (u v : Fin r → ℂ) :
        Q u v = ∑ a, ∑ b, conj (u a) * Q (Pi.single a 1) (Pi.single b 1) * v b := by
      have hu := (Pi.basisFun ℂ (Fin r)).sum_repr u
      have hv := (Pi.basisFun ℂ (Fin r)).sum_repr v
      simp only [Pi.basisFun_repr, Pi.basisFun_apply] at hu hv
      conv_lhs => rw [← hu, map_sum]
      simp only [LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply]
      apply Finset.sum_congr rfl
      intro a _
      conv_lhs => rw [← hv, map_sum]
      simp only [map_smul, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    have hHpair (y : M) (hy : y ∈ (A.chart i).baseSet) (u v : E y) :
        (h.toCore y).inner u v =
          ∑ a, ∑ b, conj ((A.frameLinearEquiv i y hy) u a) * H y a b *
            (A.frameLinearEquiv i y hy) v b := by
      let : InnerProductSpace.Core ℂ (E y) := h.toCore y
      let Q : E y →ₗ⋆[ℂ] E y →ₗ[ℂ] ℂ :=
        LinearMap.mk₂'ₛₗ _ _ (h.toCore y).inner
          (fun a b d ↦ (h.toCore y).add_left a b d)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
          (fun a b d ↦ InnerProductSpace.Core.inner_add_right a b d)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
      have he := hexpand (A.rank i)
        ((Q.comp (A.frameLinearEquiv i y hy).symm.toLinearMap).compl₂
          (A.frameLinearEquiv i y hy).symm.toLinearMap)
        ((A.frameLinearEquiv i y hy) u) ((A.frameLinearEquiv i y hy) v)
      simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, Q, LinearMap.mk₂'ₛₗ_apply, H,
        dite_eq_left hy] using he
    have hKpair (y : M) (hy : y ∈ (B.chart j).baseSet) (u v : F y) :
        (k.toCore y).inner u v =
          ∑ a, ∑ b, conj ((B.frameLinearEquiv j y hy) u a) * K y a b *
            (B.frameLinearEquiv j y hy) v b := by
      let : InnerProductSpace.Core ℂ (F y) := k.toCore y
      let Q : F y →ₗ⋆[ℂ] F y →ₗ[ℂ] ℂ :=
        LinearMap.mk₂'ₛₗ _ _ (k.toCore y).inner
          (fun a b d ↦ (k.toCore y).add_left a b d)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
          (fun a b d ↦ InnerProductSpace.Core.inner_add_right a b d)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
      have he := hexpand (B.rank j)
        ((Q.comp (B.frameLinearEquiv j y hy).symm.toLinearMap).compl₂
          (B.frameLinearEquiv j y hy).symm.toLinearMap)
        ((B.frameLinearEquiv j y hy) u) ((B.frameLinearEquiv j y hy) v)
      simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, Q, LinearMap.mk₂'ₛₗ_apply, K,
        dite_eq_left hy] using he
    let toOp : Matrix (Fin (A.rank i)) (Fin (A.rank i)) ℂ →ₗ[ℂ] (V →L[ℂ] V) :=
      LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toLin'.toLinearMap
    let toOpC := LinearMap.toContinuousLinearMap (toOp.restrictScalars ℝ)
    let G (y : M) : V →L[ℂ] V := toOpC (H y)
    have hG : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V →L[ℂ] V) ∞
        G (A.chart i).baseSet := by
      apply toOpC.contDiff.contMDiff.comp_contMDiffOn
      apply contMDiffOn_pi_space.mpr
      intro a
      apply contMDiffOn_pi_space.mpr
      intro b
      exact hh i a b
    have hequiv (y : M) (hy : y ∈ (A.chart i).baseSet) :
        ∃ L : V ≃L[ℂ] V, L.toContinuousLinearMap = G y := by
      have hker (v : V) (hv : G y v = 0) : v = 0 := by
        let w := (A.frameLinearEquiv i y hy).symm v
        have hw : (h.toCore y).inner w w = 0 := by
          rw [hHpair y hy, LinearEquiv.apply_symm_apply]
          simp only [mul_assoc, ← Finset.mul_sum]
          apply Finset.sum_eq_zero
          intro a _
          have ha := congrFun hv a
          change ∑ b, H y a b * v b = 0 at ha
          rw [ha, mul_zero]
        have hwzero := (h.toCore y).definite w hw
        have he := congrArg (A.frameLinearEquiv i y hy) hwzero
        simpa only [w, LinearEquiv.apply_symm_apply, map_zero] using he
      have hinj : Function.Injective (G y) := LinearMap.ker_eq_bot.mp
        (LinearMap.ker_eq_bot'.mpr hker)
      let L := (LinearEquiv.ofBijective (G y).toLinearMap
        ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv
      exact ⟨L, rfl⟩
    -- Smooth inversion takes place only in the fixed finite coordinate space.
    have hinverse : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, V →L[ℂ] V) ∞ (fun y ↦ (G y).inverse) (A.chart i).baseSet := by
      intro y hy
      obtain ⟨L, hL⟩ := hequiv y hy
      have hinv : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G y) := by
        rw [← hL]
        exact (contDiffAt_map_inverse L).restrict_scalars ℝ
      exact hinv.contMDiffAt.comp_contMDiffWithinAt y (hG y hy)
    let R (y : M) : V := fun a ↦ ∑ b, conj (C y a b) * K y b l
    have hR : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞ R S := by
      apply contMDiffOn_pi_space.mpr
      intro a
      apply contMDiffOn_finsetSum
      intro b _
      have hC := ((contMDiffOn_pi_space.mp (hc.2 i j a)) b).mono
        (show S ⊆ (A.chart i).baseSet ∩ id ⁻¹' (B.chart j).baseSet from
          fun _ hy ↦ ⟨hy.2, hy.1⟩)
      have hconj := Complex.conjCLE.contDiff.contMDiff.comp_contMDiffOn hC
      have hmul : ContDiff ℝ ∞ (fun p : ℂ × ℂ ↦ p.1 * p.2) := contDiff_mul
      exact hmul.contMDiff.comp_contMDiffOn
        (hconj.prodMk_space ((hk j b l).mono Set.inter_subset_left))
    have heval : ContDiff ℝ ∞ (fun p : (V →L[ℂ] V) × V ↦ p.1 p.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
    have hsmooth := heval.contMDiff.comp_contMDiffOn
      ((hinverse.mono Set.inter_subset_right).prodMk_space hR)
    -- Test the adjunction on each source basis vector: H times this column is C* K.
    apply hsmooth.congr
    intro y hy
    have hyB : y ∈ (B.chart j).baseSet := hy.1
    have hyA : y ∈ (A.chart i).baseSet := hy.2
    obtain ⟨L, hL⟩ := hequiv y hyA
    simp only [Function.comp_apply, id_eq, dite_eq_left hyB]
    apply L.injective
    rw [← hL, ContinuousLinearMap.inverse_equiv]
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    change L.toContinuousLinearMap ((A.frameLinearEquiv i y hyA)
      (atlasFiberAdjoint A B h k y (c y)
        ((B.frameLinearEquiv j y hyB).symm (Pi.single l 1)))) = R y
    rw [hL]
    ext a
    have he := hpair y ((A.frameLinearEquiv i y hyA).symm (Pi.single a 1))
      ((B.frameLinearEquiv j y hyB).symm (Pi.single l 1))
    rw [hHpair y hyA, hKpair y hyB] at he
    simp only [LinearEquiv.apply_symm_apply] at he
    change (∑ b, H y a b * ((A.frameLinearEquiv i y hyA)
      (atlasFiberAdjoint A B h k y (c y)
        ((B.frameLinearEquiv j y hyB).symm (Pi.single l 1)))) b) = R y a
    simpa [R, C, dite_eq_left hyA, Pi.single_apply,
      SmoothComplexBundleAtlas.frameLinearEquiv] using he.symm
  · intro x
    -- Orthogonal kernel/range duality proves the two directions for unequal fiber ranks.
    obtain ⟨i, hi⟩ := A.covers x
    obtain ⟨j, hj⟩ := B.covers x
    let : FiniteDimensional ℂ (E x) :=
      (A.frameLinearEquiv i x hi).symm.finiteDimensional
    let : FiniteDimensional ℂ (F x) :=
      (B.frameLinearEquiv j x hj).symm.finiteDimensional
    let moduleE : Module ℂ (E x) := inferInstance
    let moduleF : Module ℂ (F x) := inferInstance
    let : NormedAddCommGroup (E x) := (h.toCore x).toNormedAddCommGroup
    let : Module ℂ (E x) := moduleE
    let : InnerProductSpace ℂ (E x) := InnerProductSpace.ofCore (h.toCore x).toCore
    let : NormedAddCommGroup (F x) := (k.toCore x).toNormedAddCommGroup
    let : Module ℂ (F x) := moduleF
    let : InnerProductSpace ℂ (F x) := InnerProductSpace.ofCore (k.toCore x).toCore
    have heq : atlasFiberAdjoint A B h k x (c x) = (c x).adjoint := by
      apply LinearMap.ext
      intro v
      apply ext_inner_left ℂ
      intro u
      exact (hpair x u v).symm.trans (LinearMap.adjoint_inner_right (c x) u v).symm
    rw [heq]
    have hinj : Function.Injective (c x).adjoint ↔ Function.Surjective (c x) := by
      rw [← LinearMap.ker_eq_bot, ← (c x).orthogonal_range,
        Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]
    have hsurj : Function.Surjective (c x).adjoint ↔ Function.Injective (c x) := by
      rw [← LinearMap.range_eq_top, ← (c x).orthogonal_ker,
        Submodule.orthogonal_eq_top_iff, LinearMap.ker_eq_bot]
    exact ⟨fun hb ↦ ⟨hsurj.mp hb.2, hinj.mp hb.1⟩,
      fun hb ↦ ⟨hinj.mpr hb.2, hsurj.mpr hb.1⟩⟩


set_option linter.unusedSectionVars false in
/-- A bijective isometry has its inverse as the metric adjoint. -/
theorem atlasFiberAdjoint_of_isometry (x : M) (c : E x →ₗ[ℂ] F x)
    (hc : Function.Bijective c)
    (hu : ∀ u v : E x, (k.toCore x).inner (c u) (c v) = (h.toCore x).inner u v) :
    (∀ u, atlasFiberAdjoint A B h k x c (c u) = u) ∧
      (∀ v, c (atlasFiberAdjoint A B h k x c v) = v) := by
  /- Pair c u with c v and use the isometry identity in the defining
  adjunction. Nondegeneracy identifies the left inverse, and surjectivity
  supplies the right inverse. Arbitrary metrics do not satisfy this premise. -/
  classical
  have hpair (u : E x) (v : F x) :
      (k.toCore x).inner (c u) v =
        (h.toCore x).inner u (atlasFiberAdjoint A B h k x c v) :=
    (existsUnique_atlasFiberAdjoint A B h k x c).exists.choose_spec u v
  have hleft (u : E x) : atlasFiberAdjoint A B h k x c (c u) = u := by
    -- Test the difference with itself, using the same specified source metric.
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    apply sub_eq_zero.mp
    apply (h.toCore x).definite
    rw [InnerProductSpace.Core.inner_sub_right, ← hpair, hu, sub_self]
  refine ⟨hleft, ?_⟩
  intro v
  -- Surjectivity supplies the second inverse identity without choosing another metric.
  obtain ⟨u, rfl⟩ := hc.2 v
  rw [hleft]

variable [MeasurableSpace M] [BorelSpace M] (μ : Measure M)

/-- The compact-source integral identity for the actual smooth formal adjoint. -/
def IsAtlasFormalAdjoint (P : A.smoothSections →ₗ[ℂ] B.smoothSections)
    (Q : B.smoothSections →ₗ[ℂ] A.smoothSections) : Prop :=
  ∀ u : A.smoothSections, IsCompact (closure {x | u.val x ≠ 0}) →
    ∀ v : B.smoothSections,
      (∫ x, (k.toCore x).inner ((P u).val x) (v.val x) ∂μ) =
        ∫ x, (h.toCore x).inner (u.val x) ((Q v).val x) ∂μ

variable [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT hSC hμ in
/-- The same-metric formal adjoint, when it exists, is unique on all smooth sections. -/
theorem IsAtlasFormalAdjoint.unique (hh : A.IsSmoothHermitianMetric h)
    (hk : B.IsSmoothHermitianMetric k)
    {P : A.smoothSections →ₗ[ℂ] B.smoothSections}
    {Q R : B.smoothSections →ₗ[ℂ] A.smoothSections}
    (hQ : IsAtlasFormalAdjoint A B h k μ P Q)
    (hR : IsAtlasFormalAdjoint A B h k μ P R) : Q = R := by
  /- Fix any smooth v, not necessarily compactly supported. Subtract the
  adjunction identities for every compactly supported u. Local frame tests
  with bumps and the positive smooth density imply (Q-R)v=0 pointwise.
  Smoothness and positive definiteness justify the local test argument.
  Extensionality in the arbitrary v identifies the original linear maps. -/
  classical
  have _ : B.IsSmoothHermitianMetric k := hk
  -- Positive smooth chart densities are locally finite on the original noncompact base.
  let : IsLocallyFiniteMeasure μ := by
    constructor
    intro x
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    have hcx : c x ∈ c.target := c.map_source hx
    obtain ⟨w, hw, hwpos, hmap⟩ := hμ.exists_smooth_density c (chart_mem_atlas _ x)
    have hwcont : ContinuousAt w (c x) :=
      hw.continuousOn.continuousAt (c.open_target.mem_nhds hcx)
    have hneigh : c.target ∩ {z | w z < w (c x) + 1} ∈ nhds (c x) :=
      Filter.inter_mem (c.open_target.mem_nhds hcx)
        (hwcont.eventually (gt_mem_nhds (lt_add_one _)))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hneigh
    let U := c ⁻¹' Metric.ball (c x) ε ∩ c.source
    have hUnhds : U ∈ nhds x :=
      Filter.inter_mem ((c.continuousAt hx).preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
        (c.open_source.mem_nhds hx)
    refine ⟨U, hUnhds, ?_⟩
    -- The chart pushforward measures the same restricted neighborhood.
    have heq : μ U = ((volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z))) (Metric.ball (c x) ε) := by
      rw [← hmap, Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) measurableSet_ball,
        Measure.restrict_apply' c.open_source.measurableSet]
    rw [heq, withDensity_apply _ measurableSet_ball]
    have hbound : (∫⁻ z in Metric.ball (c x) ε, ENNReal.ofReal (w z)
        ∂(volume.restrict c.target)) ≤ ENNReal.ofReal (w (c x) + 1) *
          volume (Metric.ball (c x) ε) := by
      calc
        _ ≤ ∫⁻ _z in Metric.ball (c x) ε, ENNReal.ofReal (w (c x) + 1)
            ∂(volume.restrict c.target) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
          exact ENNReal.ofReal_le_ofReal (hball hz).2.le
        _ ≤ _ := by
          rw [lintegral_const, Measure.restrict_apply_univ]
          exact mul_le_mul_right (Measure.restrict_apply_le _ _) _
    exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top)
  -- The same strictly positive densities give every nonempty open set positive mass.
  let : μ.IsOpenPosMeasure := by
    constructor
    intro U hU hUne hzero
    obtain ⟨x, hxU⟩ := hUne
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    obtain ⟨w, hw, hwpos, hmap⟩ := hμ.exists_smooth_density c (chart_mem_atlas _ x)
    let A := c '' (c.source ∩ U)
    have hAopen : IsOpen A := c.isOpen_image_source_inter hU
    have hAnon : A.Nonempty := ⟨c x, ⟨x, ⟨hx, hxU⟩, rfl⟩⟩
    have hAsub : A ⊆ c.target := by
      rintro _ ⟨y, hy, rfl⟩
      exact c.map_source hy.1
    have hpre : c ⁻¹' A ∩ c.source ⊆ U := by
      rintro y ⟨⟨z, hz, hzy⟩, hy⟩
      have heq : z = y := c.injOn hz.1 hy hzy
      simpa only [← heq] using hz.2
    have hAnull : ((volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z))) A = 0 := by
      rw [← hmap, Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) hAopen.measurableSet,
        Measure.restrict_apply' c.open_source.measurableSet]
      exact measure_mono_null hpre hzero
    -- Positivity makes coordinate Lebesgue measure absolutely continuous in the density.
    have hac : volume.restrict c.target ≪ (volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z)) := by
      apply withDensity_absolutelyContinuous'
        (hw.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      exact (ENNReal.ofReal_pos.mpr (hwpos z hz)).ne'
    have hvol := hac hAnull
    rw [Measure.restrict_apply hAopen.measurableSet,
      Set.inter_eq_left.mpr hAsub] at hvol
    exact hAopen.measure_ne_zero volume hAnon hvol
  -- Only the compact source factor is needed to integrate the exact original pairing.
  have hintegrable (u t : A.smoothSections)
      (hu : IsCompact (closure {y | u.val y ≠ 0})) :
      Integrable (fun y ↦ (h.toCore y).inner (u.val y) (t.val y)) μ := by
    have hcont := (A.contMDiff_pairing h hh u t).continuous
    have hsupport : Function.support (fun y ↦ (h.toCore y).inner (u.val y) (t.val y)) ⊆
        {y | u.val y ≠ 0} := by
      intro y hy hzero
      apply hy
      change (h.toCore y).inner (u.val y) (t.val y) = 0
      rw [hzero]
      let : InnerProductSpace.Core ℂ (E y) := h.toCore y
      exact InnerProductSpace.Core.inner_zero_left _
    exact hcont.integrable_of_hasCompactSupport
      (hu.of_isClosed_subset isClosed_closure (closure_mono hsupport))
  apply LinearMap.ext
  intro v
  apply sub_eq_zero.mp
  apply Subtype.ext
  funext x
  let w : A.smoothSections := Q v - R v
  change w.val x = 0
  -- A nonnegative compact cutoff makes this arbitrary smooth difference an admissible test.
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨K, hK, hKinner, _⟩ := exists_compact_between
    (K := ({x} : Set M)) (U := Set.univ) isCompact_singleton isOpen_univ
    (Set.subset_univ _)
  obtain ⟨χ, hχone, hχzero, hχbounds⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (n := (⊤ : ℕ∞)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_singleton hKinner
  have hχx : χ x = 1 := hχone.self_of_nhdsSet x (Set.mem_singleton x)
  let u : A.smoothSections := atlasSectionMul A (fun y ↦ (χ y : ℂ))
    (Complex.ofRealCLM.contMDiff.comp χ.contMDiff) w
  have huval (y : M) : u.val y = (χ y : ℂ) • w.val y := rfl
  have husupport : closure {y | u.val y ≠ 0} ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (by rw [huval, hχzero y hyK, Complex.ofReal_zero, zero_smul])
  have hu : IsCompact (closure {y | u.val y ≠ 0}) :=
    hK.of_isClosed_subset isClosed_closure husupport
  -- The left integral may be nonintegrable; eliminate it by equality before subtracting.
  have hsame : (∫ y, (h.toCore y).inner (u.val y) ((Q v).val y) ∂μ) =
      ∫ y, (h.toCore y).inner (u.val y) ((R v).val y) ∂μ :=
    (hQ u hu v).symm.trans (hR u hu v)
  have hdiff : (∫ y, (h.toCore y).inner (u.val y) (w.val y) ∂μ) = 0 := by
    have heval (y : M) : (h.toCore y).inner (u.val y) (w.val y) =
        (h.toCore y).inner (u.val y) ((Q v).val y) -
          (h.toCore y).inner (u.val y) ((R v).val y) := by
      let : InnerProductSpace.Core ℂ (E y) := h.toCore y
      exact InnerProductSpace.Core.inner_sub_right _ _ _
    simp_rw [heval]
    rw [integral_sub (hintegrable u (Q v) hu) (hintegrable u (R v) hu),
      hsame, sub_self]
  -- The resulting scalar is nonnegative and continuous, so zero integral means zero everywhere.
  let f (y : M) : ℝ := χ y * ((h.toCore y).inner (w.val y) (w.val y)).re
  have hfre (y : M) : f y = ((h.toCore y).inner (u.val y) (w.val y)).re := by
    rw [huval, (h.toCore y).smul_left]
    simp [f, Complex.mul_re]
  have hfcont : Continuous f :=
    χ.contMDiff.continuous.mul
      (Complex.continuous_re.comp (A.contMDiff_pairing h hh w w).continuous)
  have hfintegrable : Integrable f μ := by
    have heq : f = fun y ↦ ((h.toCore y).inner (u.val y) (w.val y)).re := funext hfre
    rw [heq]
    exact Complex.reCLM.integrable_comp (hintegrable u w hu)
  have hfzero : (∫ y, f y ∂μ) = 0 := by
    calc
      _ = (∫ y, (h.toCore y).inner (u.val y) (w.val y) ∂μ).re := by
        simp_rw [hfre]
        simpa only [RCLike.re_eq_complex_re] using integral_re (hintegrable u w hu)
      _ = 0 := congrArg Complex.re hdiff
  have hfae : f =ᵐ[μ] fun _ ↦ 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun y ↦ mul_nonneg (hχbounds y).1 ((h.toCore y).re_inner_nonneg (w.val y)))
      hfintegrable).mp hfzero
  have hpoint : f x = 0 :=
    congrFun ((hfcont.ae_eq_iff_eq μ continuous_const).mp hfae) x
  have hrealzero : ((h.toCore x).inner (w.val x) (w.val x)).re = 0 := by
    simpa only [f, hχx, one_mul] using hpoint
  -- At the selected point the cutoff is one; original definiteness annihilates w itself.
  apply (h.toCore x).definite
  apply Complex.ext
  · exact hrealzero
  · have hsym := congrArg Complex.im ((h.toCore x).conj_inner_symm (w.val x) (w.val x))
    simp only [Complex.conj_im] at hsym
    change ((h.toCore x).inner (w.val x) (w.val x)).im = 0
    linarith

private theorem integrable_atlasPairing_of_compact_left
    (hh : A.IsSmoothHermitianMetric h) (u t : A.smoothSections)
    (hu : IsCompact (closure {y | u.val y ≠ 0})) :
    Integrable (fun y ↦ (h.toCore y).inner (u.val y) (t.val y)) μ := by
  let : IsLocallyFiniteMeasure μ := by
    constructor
    intro x
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    have hcx : c x ∈ c.target := c.map_source hx
    obtain ⟨w, hw, hwpos, hmap⟩ := hμ.exists_smooth_density c (chart_mem_atlas _ x)
    have hwcont : ContinuousAt w (c x) :=
      hw.continuousOn.continuousAt (c.open_target.mem_nhds hcx)
    have hneigh : c.target ∩ {z | w z < w (c x) + 1} ∈ nhds (c x) :=
      Filter.inter_mem (c.open_target.mem_nhds hcx)
        (hwcont.eventually (gt_mem_nhds (lt_add_one _)))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hneigh
    let U := c ⁻¹' Metric.ball (c x) ε ∩ c.source
    have hUnhds : U ∈ nhds x :=
      Filter.inter_mem ((c.continuousAt hx).preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
        (c.open_source.mem_nhds hx)
    refine ⟨U, hUnhds, ?_⟩
    -- The chart pushforward measures the same restricted neighborhood.
    have heq : μ U = ((volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z))) (Metric.ball (c x) ε) := by
      rw [← hmap, Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) measurableSet_ball,
        Measure.restrict_apply' c.open_source.measurableSet]
    rw [heq, withDensity_apply _ measurableSet_ball]
    have hbound : (∫⁻ z in Metric.ball (c x) ε, ENNReal.ofReal (w z)
        ∂(volume.restrict c.target)) ≤ ENNReal.ofReal (w (c x) + 1) *
          volume (Metric.ball (c x) ε) := by
      calc
        _ ≤ ∫⁻ _z in Metric.ball (c x) ε, ENNReal.ofReal (w (c x) + 1)
            ∂(volume.restrict c.target) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
          exact ENNReal.ofReal_le_ofReal (hball hz).2.le
        _ ≤ _ := by
          rw [lintegral_const, Measure.restrict_apply_univ]
          exact mul_le_mul_right (Measure.restrict_apply_le _ _) _
    exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top)
  have hcont := (A.contMDiff_pairing h hh u t).continuous
  have hsupport : Function.support (fun y ↦ (h.toCore y).inner (u.val y) (t.val y)) ⊆
      {y | u.val y ≠ 0} := by
    intro y hy hzero
    apply hy
    change (h.toCore y).inner (u.val y) (t.val y) = 0
    rw [hzero]
    let : InnerProductSpace.Core ℂ (E y) := h.toCore y
    exact InnerProductSpace.Core.inner_zero_left _
  exact hcont.integrable_of_hasCompactSupport
    (hu.of_isClosed_subset isClosed_closure (closure_mono hsupport))

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] hM hT hSC in
private theorem integral_eq_atlasChart_integral
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (μ : Measure M)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContinuousOn w c.target)
    (hpos : ∀ z ∈ c.target, 0 ≤ w z)
    (hmap : Measure.map c (μ.restrict c.source) =
      (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (w z)))
    (f : M → ℂ) (hf : Continuous f) (hsupp : Function.support f ⊆ c.source) :
    (∫ x, f x ∂μ) = ∫ z in c.target, w z • f (c.symm z) := by
  classical
  -- Extend the target test by zero outside the prescribed chart target.
  let g : EuclideanSpace ℝ (Fin n) → ℂ := c.target.piecewise (fun z ↦ f (c.symm z)) (fun _ ↦ 0)
  have hg : Measurable g :=
    (hf.comp_continuousOn c.continuousOn_symm).measurable_piecewise
      continuousOn_const c.open_target.measurableSet
  have hwmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z)) (volume.restrict c.target) :=
    ENNReal.continuous_ofReal.continuousOn.comp hw (Set.mapsTo_univ _ _)
      |>.aemeasurable c.open_target.measurableSet
  calc
    (∫ x, f x ∂μ) = ∫ x in c.source, f x ∂μ := by
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ Function.notMem_support.mp (fun h ↦ hx (hsupp h)))
    _ = ∫ x in c.source, g (c x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
      simp [g, Set.piecewise_eq_of_mem, c.map_source hx, c.left_inv hx]
    _ = ∫ z, g z ∂Measure.map c (μ.restrict c.source) :=
      (integral_map (c.continuousOn.aemeasurable c.open_source.measurableSet)
        hg.aestronglyMeasurable).symm
    _ = ∫ z in c.target, (ENNReal.ofReal (w z)).toReal • g z := by
      rw [hmap]
      exact integral_withDensity_eq_integral_toReal_smul₀ hwmeas
        (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) g
    _ = ∫ z in c.target, w z • f (c.symm z) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      simp [g, Set.piecewise_eq_of_mem, hz, ENNReal.toReal_ofReal (hpos z hz)]

omit hT hSC [MeasurableSpace M] [BorelSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Coordinate Gram weights are needed for exact local adjunction with the original metric.
private theorem exists_atlasGramOperator
    (hh : A.IsSmoothHermitianMetric h)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) :
    ∃ G : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ] EuclideanSpace ℂ (Fin (A.rank i)),
      ContDiffOn ℝ ∞ G (c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) ∧
      ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse)
        (c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) ∧
      ∀ z (hz : z ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet),
        (∃ J : EuclideanSpace ℂ (Fin (A.rank i)) ≃L[ℂ]
            EuclideanSpace ℂ (Fin (A.rank i)), J.toContinuousLinearMap = G z) ∧
        ∀ u v : E (c.symm z),
          (h.toCore (c.symm z)).inner u v =
            inner ℂ ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
              (A.frameLinearEquiv i (c.symm z) hz.2 u))
              (G z ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
                (A.frameLinearEquiv i (c.symm z) hz.2 v))) := by
  classical
  let r := A.rank i
  let V := EuclideanSpace ℂ (Fin r)
  let H (y : M) : Matrix (Fin r) (Fin r) ℂ := fun a b ↦
    if hy : y ∈ (A.chart i).baseSet then
      (h.toCore y).inner ((A.frameLinearEquiv i y hy).symm (Pi.single a 1))
        ((A.frameLinearEquiv i y hy).symm (Pi.single b 1)) else 0
  let toOp : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (V →L[ℂ] V) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap.toLinearMap.comp
        Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
  let G (z : EuclideanSpace ℝ (Fin n)) : V →L[ℂ] V := toOp (H (c.symm z))
  have hG : ContDiffOn ℝ ∞ G (c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    apply toOp.contDiff.contDiffAt.comp z
    apply contDiffAt_pi.mpr
    intro a
    apply contDiffAt_pi.mpr
    intro b
    have hH : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
        (fun y ↦ H y a b) (A.chart i).baseSet := hh i a b
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) hc) hz.1
    exact ((hH.contMDiffAt ((A.chart i).open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
  have hexpand (r : ℕ) (Q : (Fin r → ℂ) →ₗ⋆[ℂ] (Fin r → ℂ) →ₗ[ℂ] ℂ)
      (u v : Fin r → ℂ) :
      Q u v = ∑ a, ∑ b, conj (u a) * Q (Pi.single a 1) (Pi.single b 1) * v b := by
    have hu := (Pi.basisFun ℂ (Fin r)).sum_repr u
    have hv := (Pi.basisFun ℂ (Fin r)).sum_repr v
    simp only [Pi.basisFun_repr, Pi.basisFun_apply] at hu hv
    conv_lhs => rw [← hu, map_sum]
    simp only [LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro a _
    conv_lhs => rw [← hv, map_sum]
    simp only [map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hHpair (y : M) (hy : y ∈ (A.chart i).baseSet) (u v : E y) :
      (h.toCore y).inner u v =
        ∑ a, ∑ b, conj ((A.frameLinearEquiv i y hy) u a) * H y a b *
          (A.frameLinearEquiv i y hy) v b := by
    let : InnerProductSpace.Core ℂ (E y) := h.toCore y
    let Q : E y →ₗ⋆[ℂ] E y →ₗ[ℂ] ℂ :=
      LinearMap.mk₂'ₛₗ _ _ (h.toCore y).inner
        (fun a b d ↦ (h.toCore y).add_left a b d)
        (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
        (fun a b d ↦ InnerProductSpace.Core.inner_add_right a b d)
        (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
    have he := hexpand (A.rank i)
      ((Q.comp (A.frameLinearEquiv i y hy).symm.toLinearMap).compl₂
        (A.frameLinearEquiv i y hy).symm.toLinearMap)
      ((A.frameLinearEquiv i y hy) u) ((A.frameLinearEquiv i y hy) v)
    simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, Q, LinearMap.mk₂'ₛₗ_apply, H,
      dite_eq_left hy] using he
  have hpair (z) (hz : z ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet)
      (u v : E (c.symm z)) :
      (h.toCore (c.symm z)).inner u v =
        inner ℂ ((EuclideanSpace.equiv (Fin r) ℂ).symm
          (A.frameLinearEquiv i (c.symm z) hz.2 u))
          (G z ((EuclideanSpace.equiv (Fin r) ℂ).symm
            (A.frameLinearEquiv i (c.symm z) hz.2 v))) := by
    rw [hHpair (c.symm z) hz.2 u v, PiLp.inner_apply]
    change (∑ a : Fin r, ∑ b : Fin r,
      conj (A.frameLinearEquiv i (c.symm z) hz.2 u a) * H (c.symm z) a b *
        A.frameLinearEquiv i (c.symm z) hz.2 v b) =
      ∑ a : Fin r, (∑ b : Fin r, H (c.symm z) a b *
        A.frameLinearEquiv i (c.symm z) hz.2 v b) *
          conj (A.frameLinearEquiv i (c.symm z) hz.2 u a)
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hequiv (z) (hz : z ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) :
      ∃ J : V ≃L[ℂ] V, J.toContinuousLinearMap = G z := by
    have hinj : Function.Injective (G z) := by
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro v hv
      let u := (A.frameLinearEquiv i (c.symm z) hz.2).symm
        ((EuclideanSpace.equiv (Fin r) ℂ) v)
      have hu := hpair z hz u u
      simp only [u, LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] at hu
      have hzpair : inner ℂ v (G z v) = 0 :=
        (congrArg (inner ℂ v) hv).trans (inner_zero_right v)
      have hzero := (h.toCore (c.symm z)).definite u (hu.trans hzpair)
      have hcoord := congrArg (fun w ↦ (EuclideanSpace.equiv (Fin r) ℂ).symm
        (A.frameLinearEquiv i (c.symm z) hz.2 w)) hzero
      simpa [u] using hcoord
    exact ⟨(LinearEquiv.ofBijective (G z).toLinearMap
      ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩
  refine ⟨G, hG, ?_, fun z hz ↦ ⟨hequiv z hz, hpair z hz⟩⟩
  intro z hz
  obtain ⟨J, hJ⟩ := hequiv z hz
  have hinv : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G z) := by
    rw [← hJ]
    exact (contDiffAt_map_inverse J).restrict_scalars ℝ
  exact hinv.comp_contDiffWithinAt z (hG z hz)

omit hμ in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
-- Both formulas use the original coordinate extension and the same density and Gram weight.
private theorem atlasChartCutoff_pairing
    (hh : A.IsSmoothHermitianMetric h)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (D : AtlasChartCutoff A c)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContinuousOn ρ c.target)
    (hρpos : ∀ z ∈ c.target, 0 ≤ ρ z)
    (hρmap : Measure.map c (μ.restrict c.source) =
      (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (ρ z)))
    (G : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin (A.rank D.frameIndex)) →L[ℂ]
        EuclideanSpace ℂ (Fin (A.rank D.frameIndex)))
    (hG : ∀ z (hz : z ∈ c.target ∩ c.symm ⁻¹' (A.chart D.frameIndex).baseSet),
      ∀ u v : E (c.symm z),
        (h.toCore (c.symm z)).inner u v =
          inner ℂ ((EuclideanSpace.equiv (Fin (A.rank D.frameIndex)) ℂ).symm
            (A.frameLinearEquiv D.frameIndex (c.symm z) hz.2 u))
            (G z ((EuclideanSpace.equiv (Fin (A.rank D.frameIndex)) ℂ).symm
              (A.frameLinearEquiv D.frameIndex (c.symm z) hz.2 v))))
    (u : A.smoothSections)
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D.frameIndex)))) :
    ((∫ x, (h.toCore x).inner ((D.extend hc v).val x) (u.val x) ∂μ) =
      ∫ z, inner ℂ (v z) (ρ z • G z (D.localize hc u z))) ∧
    ((∫ x, (h.toCore x).inner (u.val x) ((D.extend hc v).val x) ∂μ) =
      ∫ z, inner ℂ (D.localize hc u z) (ρ z • G z (v z))) := by
  classical
  have hzero (x : M) (hx : x ∉ c.source) : (D.extend hc v).val x = 0 := by
    simp [AtlasChartCutoff.extend, AtlasChartCutoff.extendedFunction, hx]
  have hcoord (z) (hz : z ∈ tsupport D.cutoff) :
      atlasSectionInChart A c D.frameIndex u.val z =
        (EuclideanSpace.equiv (Fin (A.rank D.frameIndex)) ℂ).symm
          (A.frameLinearEquiv D.frameIndex (c.symm z) (D.support_subset hz).2
            (u.val (c.symm z))) := rfl
  constructor
  · rw [integral_eq_atlasChart_integral c μ ρ hρ hρpos hρmap _
      (A.contMDiff_pairing h hh (D.extend hc v) u).continuous (by
        intro x hx
        by_contra hxc
        apply hx
        change (h.toCore x).inner ((D.extend hc v).val x) (u.val x) = 0
        rw [hzero x hxc]
        let : InnerProductSpace.Core ℂ (E x) := h.toCore x
        exact InnerProductSpace.Core.inner_zero_left _)]
    calc
      _ = ∫ z in c.target, inner ℂ (v z) (ρ z • G z (D.localize hc u z)) := by
        apply setIntegral_congr_fun c.open_target.measurableSet
        intro z hz
        by_cases hzD : z ∈ tsupport D.cutoff
        · have hzF := (D.support_subset hzD).2
          have hzS : c.symm z ∈ c.source ∩ (A.chart D.frameIndex).baseSet :=
            ⟨c.map_target hz, hzF⟩
          change ρ z • (h.toCore (c.symm z)).inner
            (D.extendedFunction v (c.symm z)) (u.val (c.symm z)) = _
          simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hzS, c.right_inv hz]
          let : InnerProductSpace.Core ℂ (E (c.symm z)) := h.toCore (c.symm z)
          rw [InnerProductSpace.Core.inner_smul_left, Complex.conj_ofReal,
            hG z (D.support_subset hzD)]
          simp only [LinearEquiv.apply_symm_apply,
            ContinuousLinearEquiv.symm_apply_apply]
          change _ = inner ℂ (v z) (ρ z • G z (D.localizedFunction u z))
          rw [AtlasChartCutoff.localizedFunction, ite_eq_left hz, hcoord z hzD, map_smul]
          simp only [inner_smul_right, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
        · have hext : D.extendedFunction v (c.symm z) = 0 := by
            unfold AtlasChartCutoff.extendedFunction
            split_ifs with hv
            · rw [c.right_inv hz, image_eq_zero_of_notMem_tsupport hzD]
              simp
            · rfl
          change ρ z • (h.toCore (c.symm z)).inner
            (D.extendedFunction v (c.symm z)) (u.val (c.symm z)) = _
          rw [hext]
          let : InnerProductSpace.Core ℂ (E (c.symm z)) := h.toCore (c.symm z)
          rw [InnerProductSpace.Core.inner_zero_left, smul_zero]
          simp [AtlasChartCutoff.localize, AtlasChartCutoff.localizedFunction,
            image_eq_zero_of_notMem_tsupport hzD]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
        intro z hz
        simp [AtlasChartCutoff.localize, AtlasChartCutoff.localizedFunction, hz])
  · rw [integral_eq_atlasChart_integral c μ ρ hρ hρpos hρmap _
      (A.contMDiff_pairing h hh u (D.extend hc v)).continuous (by
        intro x hx
        by_contra hxc
        apply hx
        change (h.toCore x).inner (u.val x) ((D.extend hc v).val x) = 0
        rw [hzero x hxc]
        let : InnerProductSpace.Core ℂ (E x) := h.toCore x
        exact InnerProductSpace.Core.inner_zero_right _)]
    calc
      _ = ∫ z in c.target, inner ℂ (D.localize hc u z) (ρ z • G z (v z)) := by
        apply setIntegral_congr_fun c.open_target.measurableSet
        intro z hz
        by_cases hzD : z ∈ tsupport D.cutoff
        · have hzF := (D.support_subset hzD).2
          have hzS : c.symm z ∈ c.source ∩ (A.chart D.frameIndex).baseSet :=
            ⟨c.map_target hz, hzF⟩
          change ρ z • (h.toCore (c.symm z)).inner
            (u.val (c.symm z)) (D.extendedFunction v (c.symm z)) = _
          simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hzS, c.right_inv hz]
          let : InnerProductSpace.Core ℂ (E (c.symm z)) := h.toCore (c.symm z)
          rw [InnerProductSpace.Core.inner_smul_right, hG z (D.support_subset hzD)]
          simp only [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
          change _ = inner ℂ (D.localizedFunction u z) (ρ z • G z (v z))
          rw [AtlasChartCutoff.localizedFunction, ite_eq_left hz, hcoord z hzD]
          simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal,
            RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
        · have hext : D.extendedFunction v (c.symm z) = 0 := by
            unfold AtlasChartCutoff.extendedFunction
            split_ifs with hv
            · rw [c.right_inv hz, image_eq_zero_of_notMem_tsupport hzD]
              simp
            · rfl
          change ρ z • (h.toCore (c.symm z)).inner
            (u.val (c.symm z)) (D.extendedFunction v (c.symm z)) = _
          rw [hext]
          let : InnerProductSpace.Core ℂ (E (c.symm z)) := h.toCore (c.symm z)
          rw [InnerProductSpace.Core.inner_zero_right, smul_zero]
          simp [AtlasChartCutoff.localize, AtlasChartCutoff.localizedFunction,
            image_eq_zero_of_notMem_tsupport hzD]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
        intro z hz
        simp [AtlasChartCutoff.localize, AtlasChartCutoff.localizedFunction, hz])

include hM hT hSC hμ in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
-- The extended limit accommodates the same finite Fourier pieces and their integral adjunction.
/-- The specified multiplier plus finite Fourier pieces has its actual smooth adjoint. -/
theorem exists_atlasRelative_formalAdjoint (hh : A.IsSmoothHermitianMetric h)
    (hk : B.IsSmoothHermitianMetric k) (c : ∀ x, E x →ₗ[ℂ] F x)
    (hc : IsSmoothAtlasBundleMap A B c) (N : ℕ)
    (T : Fin N → AtlasPseudodifferentialPiece A B 0)
    (L : Set M) (hL : IsCompact L)
    (hTL : ∀ j, (T j).chart.symm ''
      (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ L) :
    ∃ Q : B.smoothSections →ₗ[ℂ] A.smoothSections,
      IsAtlasFormalAdjoint A B h k μ
        (atlasSmoothSectionMap A B c hc + ∑ j, (T j).toLinearMap) Q ∧
      HasAtlasSectionOperatorSupport B A L
        (Q - atlasSmoothSectionMap B A
          (fun x ↦ atlasFiberAdjoint A B h k x (c x))
          (atlasFiberAdjoint_properties A B h k hh hk c hc).1) ∧
      ∀ (v : B.smoothSections) (x : M), x ∉ L →
        (Q v).val x = atlasFiberAdjoint A B h k x (c x) (v.val x) := by
  /- For each piece, insert a common compact plateau around both original
  cutoffs and apply the Schwartz formal-adjoint construction. Conjugate
  this map by the local density and positive Gram operators, then reverse
  the two cutoffs and transport through their original frames. The chart
  pairing formulas identify the resulting integral with the original
  compact-source adjunction identity.
  Sum these maps and add the smooth fiber-adjoint multiplier. Compact
  supports justify the finite integral sum. The reversed cutoffs give
  both residual support controls and the stated value outside L. -/
  classical
  -- Adjoint each original piece before summing, retaining both original supports.
  have hpiece {m : ℝ} (R : AtlasPseudodifferentialPiece A B m)
      (hRL : R.chart.symm '' (tsupport R.input.cutoff ∪ tsupport R.output.cutoff) ⊆ L) :
      ∃ S : B.smoothSections →ₗ[ℂ] A.smoothSections,
        IsAtlasFormalAdjoint A B h k μ R.toLinearMap S ∧
          HasAtlasSectionOperatorSupport B A L S := by
    classical
    let r := A.rank R.input.frameIndex
    let q := B.rank R.output.frameIndex
    let V := EuclideanSpace ℝ (Fin n)
    let H (s : ℕ) := EuclideanSpace ℂ (Fin s)
    let c := R.chart
    -- A common plateau lies strictly inside the original chart and both original frames.
    let K := tsupport R.input.cutoff ∪ tsupport R.output.cutoff
    let U := c.target ∩ c.symm ⁻¹'
      ((A.chart R.input.frameIndex).baseSet ∩ (B.chart R.output.frameIndex).baseSet)
    have hK : IsCompact K := R.input.compact_support.union R.output.compact_support
    have hU : IsOpen U := c.continuousOn_symm.isOpen_inter_preimage c.open_target
      ((A.chart R.input.frameIndex).open_baseSet.inter (B.chart R.output.frameIndex).open_baseSet)
    have hKU : K ⊆ U := by
      rintro z (hz | hz)
      · exact ⟨(R.input.support_subset hz).1, (R.input.support_subset hz).2,
          R.input_support_in_output_frame hz⟩
      · exact ⟨(R.output.support_subset hz).1, R.output_support_in_input_frame hz,
          (R.output.support_subset hz).2⟩
    have hcutoff (S O : Set V) (hS : IsCompact S) (hO : IsOpen O) (hSO : S ⊆ O) :
        ∃ β : V → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ O ∧
          S ⊆ interior {z | β z = 1} := by
      obtain ⟨W, hW, hSW, hWO, hWcompact⟩ :=
        exists_open_between_and_isCompact_closure hS hO hSO
      obtain ⟨D, hD, hWD, hDO, hDcompact⟩ :=
        exists_open_between_and_isCompact_closure hWcompact hO hWO
      obtain ⟨β, hβ, _, hsupp, hone⟩ :=
        exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hD isClosed_closure hWD
      have hts : tsupport β = closure D := congrArg closure hsupp
      refine ⟨β, hβ, ?_, ?_, ?_⟩
      · change IsCompact (tsupport β)
        rwa [hts]
      · rwa [hts]
      · apply hSW.trans
        apply interior_maximal ?_ hW
        intro z hz
        exact (hone z).mp (subset_closure hz)
    obtain ⟨β, hβ, hcβ, hsβ, honeβ⟩ := hcutoff K U hK hU hKU
    have hβK (z : V) (hz : z ∈ K) : β z = 1 :=
      (interior_subset (s := {z : V | β z = 1})) (honeβ hz)
    -- Compactify the original Schwartz operator before transposing it.
    let p₀ := cutoffSymbol β β R.symbol
    have hp₀ : IsSymbol Set.univ m p₀ :=
      isSymbol_cutoffSymbol m R.symbol R.isSymbol β β hβ hβ hcβ hcβ
    let P₀ := amplitudeOperator m (cutoffAmplitude β β R.symbol)
      (isAmplitude_cutoffAmplitude m R.symbol R.isSymbol β β hβ hβ)
      (hasCompactSupport_cutoffAmplitude R.symbol β β hcβ hcβ)
    have hP₀ (v : 𝓢(V, H r)) (z : V) : P₀ v z = quantize p₀ v z := by
      rw [show P₀ v z = amplitudeApply (cutoffAmplitude β β R.symbol) v z from
        amplitudeOperator_apply m _ _ _ v z]
      exact (congrFun (quantize_amplitudeSymbol m _
        (isAmplitude_cutoffAmplitude m R.symbol R.isSymbol β β hβ hβ)
        (hasCompactSupport_cutoffAmplitude R.symbol β β hcβ hcβ) v) z).symm
    have hP₀support : HasOperatorSupport (tsupport β) P₀ := by
      simpa only [Set.union_self] using
        hasOperatorSupport_cutoff m R.symbol R.isSymbol β β hβ hβ hcβ hcβ
    let Q := localFormalAdjoint m p₀ hp₀ P₀ hP₀ (tsupport β) hcβ hP₀support
    have hQpair : IsSchwartzFormalAdjoint P₀ Q :=
      isSchwartzFormalAdjoint_localFormalAdjoint m p₀ hp₀ P₀ hP₀
        (tsupport β) hcβ hP₀support
    -- The density and its inverse need smoothness only on this chart target.
    obtain ⟨ρ, hρ, hρpos, hρmap⟩ := hμ.exists_smooth_density c R.chart_mem_atlas
    obtain ⟨GE, _, hGEinv, hGEpair⟩ :=
      exists_atlasGramOperator A h hh c R.chart_mem_atlas R.input.frameIndex
    obtain ⟨GF, hGF, _, hGFpair⟩ :=
      exists_atlasGramOperator B k hk c R.chart_mem_atlas R.output.frameIndex
    have hUE : U ⊆ c.target ∩ c.symm ⁻¹' (A.chart R.input.frameIndex).baseSet :=
      fun z hz ↦ ⟨hz.1, hz.2.1⟩
    have hUF : U ⊆ c.target ∩ c.symm ⁻¹' (B.chart R.output.frameIndex).baseSet :=
      fun z hz ↦ ⟨hz.1, hz.2.2⟩
    let WA : V → H r →L[ℂ] H r := cutoffMatrix β (fun z ↦ (ρ z)⁻¹ • (GE z).inverse)
    let WB : V → H q →L[ℂ] H q := cutoffMatrix β (fun z ↦ ρ z • GF z)
    have hA : ContDiff ℝ ∞ WA := contDiff_cutoffMatrix U hU _
      (((hρ.mono (fun z hz ↦ hz.1)).inv
        (fun z hz ↦ ne_of_gt (hρpos z hz.1))).smul (hGEinv.mono hUE)) β hβ hsβ
    have hB : ContDiff ℝ ∞ WB := contDiff_cutoffMatrix U hU _
      ((hρ.mono (fun z hz ↦ hz.1)).smul (hGF.mono hUF)) β hβ hsβ
    have hcA : HasCompactSupport WA := hasCompactSupport_cutoffMatrix β _ hcβ
    have hcB : HasCompactSupport WB := hasCompactSupport_cutoffMatrix β _ hcβ
    let W := (matrixMultiplierCLM WA hA hcA).comp
      (Q.comp (matrixMultiplierCLM WB hB hcB))
    let S : B.smoothSections →ₗ[ℂ] A.smoothSections :=
      (R.input.extendLinearMap R.chart_mem_atlas).comp
        (W.toLinearMap.comp (R.output.localizeLinearMap R.chart_mem_atlas))
    have hsupp : HasAtlasSectionOperatorSupport B A L S := by
      constructor
      · intro v
        apply closure_minimal _ hL.isClosed
        intro x hx
        by_contra hxL
        exact hx ((R.input.extendedFunction_properties R.chart_mem_atlas
          (W (R.output.localize R.chart_mem_atlas v))).2 x (by
            rintro ⟨z, hz, rfl⟩
            exact hxL (hRL ⟨z, Or.inl hz, rfl⟩)))
      · intro v hv
        have hlocal : R.output.localize R.chart_mem_atlas v = 0 := by
          apply SchwartzMap.ext
          intro z
          by_cases hz : z ∈ tsupport R.output.cutoff
          · have hxL := hRL ⟨z, Or.inr hz, rfl⟩
            have hzv : v.val (R.chart.symm z) = 0 := by
              by_contra hne
              exact Set.disjoint_left.mp hv (subset_closure hne) hxL
            have hframezero : ((B.chart R.output.frameIndex)
                ⟨R.chart.symm z, (0 : F (R.chart.symm z))⟩).2 = 0 :=
              (B.frameLinearEquiv R.output.frameIndex (R.chart.symm z)
                (R.output.support_subset hz).2).map_zero
            change R.output.localizedFunction v z = 0
            simp [AtlasChartCutoff.localizedFunction, atlasSectionInChart, hzv, hframezero]
          · change R.output.localizedFunction v z = 0
            simp [AtlasChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
        change R.input.extendLinearMap R.chart_mem_atlas
          (W (R.output.localize R.chart_mem_atlas v)) = 0
        rw [hlocal, map_zero, map_zero]
    refine ⟨S, ?_, hsupp⟩
    intro u _ v
    let u₀ := R.input.localize R.chart_mem_atlas u
    let v₀ := R.output.localize R.chart_mem_atlas v
    let b := matrixMultiplierCLM WB hB hcB v₀
    have hu₀zero (z : V) (hz : z ∉ tsupport R.input.cutoff) : u₀ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hz' ↦ hz ((R.input.localizedFunction_properties R.chart_mem_atlas u).2.1 hz'))
    have hv₀zero (z : V) (hz : z ∉ tsupport R.output.cutoff) : v₀ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hz' ↦ hz ((R.output.localizedFunction_properties R.chart_mem_atlas v).2.1 hz'))
    have hβgrowth : (fun z : V ↦ (β z : ℂ)).HasTemperateGrowth :=
      (hcβ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hβ)
    have hβu : SchwartzMap.smulLeftCLM (H r) (fun z ↦ (β z : ℂ)) u₀ = u₀ := by
      ext z : 1
      rw [SchwartzMap.smulLeftCLM_apply_apply hβgrowth]
      by_cases hz : z ∈ tsupport R.input.cutoff
      · rw [hβK z (Or.inl hz), Complex.ofReal_one, one_smul]
      · rw [hu₀zero z hz, smul_zero]
    have hP₀apply (z : V) : P₀ u₀ z = β z • R.operator u₀ z := by
      rw [show P₀ u₀ z = amplitudeApply (cutoffAmplitude β β R.symbol) u₀ z from
        amplitudeOperator_apply m _ _ _ u₀ z]
      rw [amplitudeApply_cutoffAmplitude m R.symbol R.isSymbol β β hβ hβ hcβ hcβ,
        hβu, ← R.operator_apply]
    have hb (z : V) : b z = ρ z • GF z (v₀ z) := by
      rw [show b z = WB z (v₀ z) from matrixMultiplierCLM_apply WB hB hcB v₀ z]
      change β z • (ρ z • GF z (v₀ z)) = _
      by_cases hz : z ∈ tsupport R.output.cutoff
      · rw [hβK z (Or.inr hz), one_smul]
      · rw [hv₀zero z hz, map_zero, smul_zero, smul_zero]
    have hWapply (z : V) :
        W v₀ z = β z • ((ρ z)⁻¹ • (GE z).inverse (Q b z)) :=
      matrixMultiplierCLM_apply WA hA hcA (Q b) z
    have hleftChart := (atlasChartCutoff_pairing B k μ hk R.chart R.chart_mem_atlas
      R.output ρ hρ.continuousOn (fun z hz ↦ (hρpos z hz).le) hρmap GF
      (fun z hz ↦ (hGFpair z hz).2) v (R.operator u₀)).1
    have hrightChart := (atlasChartCutoff_pairing A h μ hh R.chart R.chart_mem_atlas
      R.input ρ hρ.continuousOn (fun z hz ↦ (hρpos z hz).le) hρmap GE
      (fun z hz ↦ (hGEpair z hz).2) u (W v₀)).2
    have hleft (z : V) : inner ℂ (P₀ u₀ z) (b z) =
        inner ℂ (R.operator u₀ z) (ρ z • GF z (v₀ z)) := by
      rw [hP₀apply, hb]
      by_cases hz : z ∈ tsupport R.output.cutoff
      · rw [hβK z (Or.inr hz), one_smul]
      · simp [hv₀zero z hz]
    have hright (z : V) : inner ℂ (u₀ z) (ρ z • GE z (W v₀ z)) =
        inner ℂ (u₀ z) (Q b z) := by
      by_cases hz : z ∈ tsupport R.input.cutoff
      · have hzE := R.input.support_subset hz
        obtain ⟨J, hJ⟩ := (hGEpair z hzE).1
        have hGI (a : H r) : GE z ((GE z).inverse a) = a := by
          rw [← hJ, ContinuousLinearMap.inverse_equiv]
          exact J.apply_symm_apply a
        rw [hWapply, hβK z (Or.inl hz), one_smul, ContinuousLinearMap.map_smul_of_tower, hGI,
          smul_smul, mul_inv_cancel₀ (ne_of_gt (hρpos z hzE.1)), one_smul]
      · simp [hu₀zero z hz]
    change (∫ x, (k.toCore x).inner
      ((R.output.extend R.chart_mem_atlas (R.operator u₀)).val x) (v.val x) ∂μ) =
        ∫ x, (h.toCore x).inner (u.val x)
          ((R.input.extend R.chart_mem_atlas (W v₀)).val x) ∂μ
    rw [hleftChart, hrightChart]
    calc
      _ = ∫ z, inner ℂ (P₀ u₀ z) (b z) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ (hleft z).symm))
      _ = ∫ z, inner ℂ (u₀ z) (Q b z) := hQpair u₀ b
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ (hright z).symm))
  choose S hS hsupport using fun j ↦ hpiece (T j) (hTL j)
  let d := fun x ↦ atlasFiberAdjoint A B h k x (c x)
  have hd : IsSmoothAtlasBundleMap B A d :=
    (atlasFiberAdjoint_properties A B h k hh hk c hc).1
  let Q : B.smoothSections →ₗ[ℂ] A.smoothSections :=
    atlasSmoothSectionMap B A d hd + ∑ j, S j
  have hsumSupport : HasAtlasSectionOperatorSupport B A L (∑ j, S j) := by
    constructor
    · intro v
      apply closure_minimal _ hL.isClosed
      intro x hx
      by_contra hxL
      have hj (j : Fin N) : (S j v).val x = 0 := by
        by_contra hne
        exact hxL ((hsupport j).1 v (subset_closure hne))
      apply hx
      simp [LinearMap.sum_apply, Finset.sum_apply, hj]
    · intro v hv
      simp only [LinearMap.sum_apply]
      exact Finset.sum_eq_zero (fun j _ ↦ (hsupport j).2 v hv)
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro u hu v
    have hcu : IsCompact (closure {x | (atlasSmoothSectionMap A B c hc u).val x ≠ 0}) :=
      hu.of_isClosed_subset isClosed_closure (closure_mono (by
        intro x hx hzero
        apply hx
        change c x (u.val x) = 0
        rw [hzero, map_zero]))
    have hTu (j : Fin N) : IsCompact (closure {x | ((T j).toLinearMap u).val x ≠ 0}) := by
      apply hL.of_isClosed_subset isClosed_closure
      apply closure_minimal _ hL.isClosed
      intro x hx
      by_contra hxL
      exact hx ((T j).toLinearMap_support_properties.1 u x (by
        rintro ⟨z, hz, rfl⟩
        exact hxL (hTL j ⟨z, Or.inr hz, rfl⟩)))
    have hIntC := integrable_atlasPairing_of_compact_left B k μ hk
      (atlasSmoothSectionMap A B c hc u) v hcu
    have hIntT (j : Fin N) := integrable_atlasPairing_of_compact_left B k μ hk
      ((T j).toLinearMap u) v (hTu j)
    have hIntD := integrable_atlasPairing_of_compact_left A h μ hh
      u (atlasSmoothSectionMap B A d hd v) hu
    have hIntS (j : Fin N) := integrable_atlasPairing_of_compact_left A h μ hh u (S j v) hu
    have hleft : (fun x ↦ (k.toCore x).inner
        (((atlasSmoothSectionMap A B c hc + ∑ j, (T j).toLinearMap) u).val x) (v.val x)) =
        fun x ↦ (k.toCore x).inner ((atlasSmoothSectionMap A B c hc u).val x) (v.val x) +
          ∑ j, (k.toCore x).inner (((T j).toLinearMap u).val x) (v.val x) := by
      funext x
      let : InnerProductSpace.Core ℂ (F x) := k.toCore x
      let H : F x →ₗ⋆[ℂ] F x →ₗ[ℂ] ℂ :=
        LinearMap.mk₂'ₛₗ _ _ (k.toCore x).inner
          (fun a b c ↦ (k.toCore x).add_left a b c)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
          (fun a b c ↦ InnerProductSpace.Core.inner_add_right a b c)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
      change H (((atlasSmoothSectionMap A B c hc + ∑ j, (T j).toLinearMap) u).val x)
        (v.val x) = H ((atlasSmoothSectionMap A B c hc u).val x) (v.val x) +
          ∑ j, H (((T j).toLinearMap u).val x) (v.val x)
      simp only [LinearMap.add_apply, LinearMap.sum_apply, Submodule.coe_add, Submodule.coe_sum,
        Pi.add_apply, Finset.sum_apply, map_add, map_sum]
    have hright : (fun x ↦ (h.toCore x).inner (u.val x) ((Q v).val x)) =
        fun x ↦ (h.toCore x).inner (u.val x) ((atlasSmoothSectionMap B A d hd v).val x) +
          ∑ j, (h.toCore x).inner (u.val x) ((S j v).val x) := by
      funext x
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      let H : E x →ₗ⋆[ℂ] E x →ₗ[ℂ] ℂ :=
        LinearMap.mk₂'ₛₗ _ _ (h.toCore x).inner
          (fun a b c ↦ (h.toCore x).add_left a b c)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
          (fun a b c ↦ InnerProductSpace.Core.inner_add_right a b c)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
      change H (u.val x) ((Q v).val x) =
        H (u.val x) ((atlasSmoothSectionMap B A d hd v).val x) +
          ∑ j, H (u.val x) ((S j v).val x)
      simp only [Q, LinearMap.add_apply, LinearMap.sum_apply, Submodule.coe_add,
        Submodule.coe_sum, Pi.add_apply, Finset.sum_apply, map_add, map_sum]
    rw [hleft, hright, integral_add hIntC (integrable_finsetSum _ (fun j _ ↦ hIntT j)),
      integral_add hIntD (integrable_finsetSum _ (fun j _ ↦ hIntS j)),
      integral_finsetSum _ (fun j _ ↦ hIntT j),
      integral_finsetSum _ (fun j _ ↦ hIntS j)]
    congr 1
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦
        (atlasFiberAdjoint_properties A B h k hh hk c hc).2.1 x (u.val x) (v.val x))
    · exact Finset.sum_congr rfl (fun j _ ↦ hS j u hu v)
  · change HasAtlasSectionOperatorSupport B A L
      ((atlasSmoothSectionMap B A d hd + ∑ j, S j) - atlasSmoothSectionMap B A d hd)
    simpa only [add_sub_cancel_left] using hsumSupport
  · intro v x hx
    have hz : ((∑ j, S j) v).val x = 0 := by
      by_contra hne
      exact hx (hsumSupport.1 v (subset_closure hne))
    change (atlasSmoothSectionMap B A d hd v).val x + ((∑ j, S j) v).val x = _
    rw [hz, add_zero]
    rfl

end AtiyahSinger
