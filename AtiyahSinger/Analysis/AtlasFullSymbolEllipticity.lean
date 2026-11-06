/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbol
public import AtiyahSinger.Analysis.FullSymbolEllipticity

import AtiyahSinger.Analysis.CosphereRegularity

/-!
# Quantitative full-symbol ellipticity on the original bundle atlases

Public module ID: M0242.

D03 / A04. SG III.4, Definition 4.1 and Remark 4.7, pp.188--191;
Taylor, Pseudodifferential Operators, III.1.1--1.3, pp.60--61.
Use the standard compact-local inverse estimate on every original common
base-chart and bundle-frame domain. The source and target coordinate ranks
are those of the two given frames; no norm is imposed on an original fiber
and no globally constant or equal rank is assumed.

For arbitrary order-m full symbols, high-frequency invertibility alone is
insufficient: the inverse must obey the order-minus-m bound, uniformly over
each compact base subset. These bounds are stable under strictly lower order
perturbations and therefore define a condition on the actual principal quotient.
Regularity remains the separate IsAtlasGlobalSymbol condition. No homogeneous
representative, inverse operator or Fredholm conclusion is built into ellipticity.

On a compact base the finite-chart norm comparisons recover SG's metric-bound
formulation. The chosen condition also makes sense on noncompact bases, without
requiring a single global radius or bound. The radial homogeneous comparison
uses the specified cotangent metric only for that existing regularization.
In dimension zero both high-frequency and off-zero conditions are vacuous.
The lower-order perturbation, principal-quotient invariance and radial homogeneous
comparison are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- Uniform high-frequency inverse bounds on compact subsets of every actual frame overlap. -/
def IsEllipticFullAtlasSymbol (m : ℝ) (a : AtlasSymbolFunction (n := n) E F) : Prop :=
  ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M → ∀ (i : A.Index) (j : B.Index),
      IsEllipticFullSymbol (atlasSymbolChartDomain A B c i j) m
        (atlasGlobalSymbolInChart A B a c i j)

/-- A strictly lower-order perturbation preserves the compact-local inverse condition. -/
theorem IsEllipticFullAtlasSymbol.add_lowerOrder {m : ℝ}
    {a b : AtlasSymbolFunction (n := n) E F}
    (ha : IsEllipticFullAtlasSymbol A B m a)
    (ε : ℝ) (hε : 0 < ε) (hb : IsAtlasGlobalSymbol A B (m - ε) b) :
    IsEllipticFullAtlasSymbol A B m (a + b) := by
  /- Stage 1: on the same common chart/frame domain, the actual coordinate
  expression of a+b is the sum of the coordinate expressions of a and b.
  The inverse estimate for a and the order-(m-ε) bound for b make a⁻¹b
  uniformly small above a sufficiently large radius on each compact set.
  Stage 2: apply IsEllipticFullSymbol.add_lowerOrder there. Absorbing the
  perturbation gives a lower bound; finite-dimensional injectivity and
  surjectivity then give invertibility and the order -m inverse bound.
  Quantify the original charts and both frame indices. -/
  classical
  intro c hc i j
  -- Fix the original common domain and retain the independent source and target frame ranks.
  have hadd : atlasGlobalSymbolInChart A B (a + b) c i j =
      atlasGlobalSymbolInChart A B a c i j + atlasGlobalSymbolInChart A B b c i j := by
    ext z η v
    by_cases h : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet
    · simp [atlasGlobalSymbolInChart, h]
    · simp [atlasGlobalSymbolInChart, h]
  rw [hadd]
  exact (ha c hc i j).add_lowerOrder ε hε (hb c hc i j)

/-- Quantitative ellipticity is independent of the representative in the principal quotient. -/
theorem isEllipticFullAtlasSymbol_iff_of_class_eq {m : ℝ}
    (a b : atlasGlobalSymbolSpace A B m)
    (hab : atlasGlobalPrincipalSymbolClass A B m a =
      atlasGlobalPrincipalSymbolClass A B m b) :
    IsEllipticFullAtlasSymbol A B m a.val ↔
      IsEllipticFullAtlasSymbol A B m b.val := by
  /- Stage 1: the actual quotient equality says that a-b has order m-1
  on every original common chart/frame domain.
  Stage 2: apply the compact-local lower-order invariance in both
  directions, writing b=a-(a-b) and a=b+(a-b). Negation preserves
  the order estimates. No representative is replaced by a homogeneous
  model, and no estimate at the zero covector is required. -/
  classical
  have hdiff := (atlasGlobalPrincipalSymbolClass_eq_iff A B m a b).mp hab
  -- The two coordinate expressions use the very same frames before quotient invariance is applied.
  have hlocal (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) (j : B.Index) :
      IsEllipticFullSymbol (atlasSymbolChartDomain A B c i j) m
          (atlasGlobalSymbolInChart A B a.val c i j) ↔
        IsEllipticFullSymbol (atlasSymbolChartDomain A B c i j) m
          (atlasGlobalSymbolInChart A B b.val c i j) := by
    apply isEllipticFullSymbol_iff_of_isSymbol_sub
    have hsub : atlasGlobalSymbolInChart A B (a.val - b.val) c i j =
        atlasGlobalSymbolInChart A B a.val c i j -
          atlasGlobalSymbolInChart A B b.val c i j := by
      ext z η v
      by_cases h : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet
      · simp [atlasGlobalSymbolInChart, h]
      · simp [atlasGlobalSymbolInChart, h]
    rw [← hsub]
    exact hdiff c hc i j
  constructor
  · intro ha c hc i j
    exact (hlocal c hc i j).mp (ha c hc i j)
  · intro hb c hc i j
    exact (hlocal c hc i j).mpr (hb c hc i j)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [hT : T2Space M]

include hM hT in
/-- The existing radial homogeneous realization satisfies the full-symbol definition exactly. -/
theorem isEllipticFullAtlasSymbol_atlasRegularizedSymbol_iff
    (g : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ)
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a) :
    IsEllipticFullAtlasSymbol A B m (atlasRegularizedSymbol A B g m a hs hh).val ↔
      IsEllipticAtlasSymbol a := by
  /- Stage 1: on a compact base subset in the given common frame domain,
  the specified metric length is uniformly comparable with the coordinate
  covector norm. Beyond a compact-dependent radius the radial cutoff is
  one, so the regularized coordinate symbol is exactly the given a.
  Stage 2: off-zero invertibility, smoothness and homogeneity bound the
  inverse on the compact base subset times the coordinate unit sphere.
  Rescaling gives its degree -m estimate at every sufficiently large
  frequency. Source and target ranks agree there as a consequence of
  invertibility, rather than an imposed rank equation.
  Stage 3: conversely fix x and a nonzero covector, use a compact singleton
  in a valid chart, and dilate past its inverse and cutoff radii. Positive
  homogeneity then implies bijectivity at the original covector. When n=0
  both conditions are vacuous; no claim at the zero covector is inserted. -/
  classical
  have hopen (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (i : A.Index) (j : B.Index) : IsOpen (atlasSymbolChartDomain A B c i j) := by
    simpa only [atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      c.continuousOn_symm.isOpen_inter_preimage c.open_target
        ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
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
  -- Equality beyond compact-dependent radii transfers quantitative ellipticity exactly.
  have hcomparison (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) (j : B.Index) :
      IsEllipticFullSymbol (atlasSymbolChartDomain A B c i j) m
          (atlasGlobalSymbolInChart A B (atlasRegularizedSymbol A B g m a hs hh).val c i j) ↔
        IsEllipticSymbol (atlasSymbolChartDomain A B c i j)
          (atlasGlobalSymbolInChart A B a c i j) := by
    rw [← isEllipticFullSymbol_frequencyCutoffSymbol_iff (hopen c i j)
      (atlasGlobalSymbolInChart A B a c i j) (hs c hc i j) (hhom a hh c hc i j)]
    have heq (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ atlasSymbolChartDomain A B c i j)
        (hK : IsCompact K) : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ η, R ≤ ‖η‖ →
          atlasGlobalSymbolInChart A B (atlasRegularizedSymbol A B g m a hs hh).val c i j z η =
            frequencyCutoffSymbol (atlasGlobalSymbolInChart A B a c i j) z η := by
      obtain ⟨R, hR, hbound⟩ := hrecovery g a c hc i j K hK hKU
      refine ⟨max R 1, lt_of_lt_of_le hR (le_max_left _ _), ?_⟩
      intro z hz η hη
      rw [frequencyCutoffSymbol_eq_of_one_le_norm _ z η ((le_max_right _ _).trans hη)]
      exact hbound z hz η ((le_max_left _ _).trans hη)
    constructor
    · intro hp K hKU hK
      obtain ⟨R, C, hR, hC, hbound⟩ := hp K hKU hK
      obtain ⟨S, hS, hsame⟩ := heq K hKU hK
      refine ⟨max R S, C, lt_of_lt_of_le hR (le_max_left _ _), hC, ?_⟩
      intro z hz η hη
      rw [← hsame z hz η ((le_max_right _ _).trans hη)]
      exact hbound z hz η ((le_max_left _ _).trans hη)
    · intro hp K hKU hK
      obtain ⟨R, C, hR, hC, hbound⟩ := hp K hKU hK
      obtain ⟨S, hS, hsame⟩ := heq K hKU hK
      refine ⟨max R S, C, lt_of_lt_of_le hR (le_max_left _ _), hC, ?_⟩
      intro z hz η hη
      rw [hsame z hz η ((le_max_right _ _).trans hη)]
      exact hbound z hz η ((le_max_left _ _).trans hη)
  -- The original independent frames are actual linear isomorphisms, without a rank equation.
  have hframes (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (i : A.Index) (j : B.Index) (z : EuclideanSpace ℝ (Fin n))
      (hz : z ∈ atlasSymbolChartDomain A B c i j) (η : EuclideanSpace ℝ (Fin n)) :
      Function.Bijective (atlasGlobalSymbolInChart A B a c i j z η) ↔
        Function.Bijective (a (c.symm z) (covectorFromChart c (c.symm z) η)) := by
    let input := (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).toLinearEquiv.trans
      (A.frameLinearEquiv i (c.symm z) hz.1.2).symm
    let output := (B.frameLinearEquiv j (c.symm z) hz.2).trans
      (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm.toLinearEquiv
    simp only [atlasGlobalSymbolInChart, dite_eq_left (show c.symm z ∈ (A.chart i).baseSet ∧
      c.symm z ∈ (B.chart j).baseSet from ⟨hz.1.2, hz.2⟩)]
    change Function.Bijective (fun v ↦ output
      (a (c.symm z) (covectorFromChart c (c.symm z) η) (input v))) ↔ _
    constructor
    · intro h
      have h' := output.symm.bijective.comp (h.comp input.symm.bijective)
      simpa only [Function.comp_def, LinearEquiv.apply_symm_apply,
        LinearEquiv.symm_apply_apply] using h'
    · intro h
      exact output.bijective.comp (h.comp input.bijective)
  constructor
  · intro he x ξ hξ
    -- Recover the original map at the same point and covector from one valid chart and frame pair.
    obtain ⟨i, hi⟩ := A.covers x
    obtain ⟨j, hj⟩ := B.covers x
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hc := chart_mem_atlas (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    have hz : c x ∈ atlasSymbolChartDomain A B c i j :=
      ⟨⟨c.map_source hx, by simpa only [Set.mem_preimage, c.left_inv hx] using hi⟩,
        by simpa only [Set.mem_preimage, c.left_inv hx] using hj⟩
    have hη : covectorInChart c x ξ ≠ 0 := by
      intro hzero
      have h := covectorFromChart_covectorInChart c hc x hx ξ
      rw [hzero] at h
      have hz' : covectorFromChart c x 0 = 0 := by
        ext v
        change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (mfderiv _ _ c x v) = 0
        exact inner_zero_left _
      exact hξ (h.symm.trans hz')
    have hlocal := (hcomparison c hc i j).mp (he c hc i j)
      (c x) hz (covectorInChart c x ξ) hη
    have hmap := (hframes c i j (c x) hz (covectorInChart c x ξ)).mp hlocal
    have hxmap : Function.Bijective (a x (covectorFromChart c x (covectorInChart c x ξ))) :=
      (congrArg (fun z : M ↦ Function.Bijective
        (a z (covectorFromChart c z (covectorInChart c x ξ)))) (c.left_inv hx)).mp hmap
    rwa [covectorFromChart_covectorInChart c hc x hx ξ] at hxmap
  · intro he c hc i j
    apply (hcomparison c hc i j).mpr
    intro z hz η hη
    apply (hframes c i j z hz η).mpr
    exact he (c.symm z) (covectorFromChart c (c.symm z) η)
      (hcov_ne c hc z hz.1.1 η hη)

end AtiyahSinger
