/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereEllipticity
public import AtiyahSinger.Analysis.FullSymbolCompactDeviation
public import AtiyahSinger.Analysis.FullSymbolExterior

import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Radial models constructed from the original full symbol

Public module ID: M2287.

Restrict the original smooth full symbol to a sufficiently large metric sphere and extend
those same bundle maps homogeneously. Quantitative ellipticity supplies that radius, so
the resulting model is elliptic on every nonzero covector. The source and target bundles
remain the original ones. These are the radial geometric constructions underlying SG
III.13.3. They do not identify the full principal quotient of a general symbol with a
homogeneous quotient, and do not yet compare the two operators' analytic indices.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Set IsManifold
open scoped Manifold ContDiff Topology

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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

/-- The original full-symbol maps on a radius-R metric sphere, normalized to degree m. -/
def fullSymbolRadialCosphereSymbol {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) :
    CosphereSymbolFunction (E := E) (F := F) g :=
  fun z ↦ ((R ^ (-m) : ℝ) : ℂ) • a.val z.val.proj (R • z.val.snd)

/-- Restriction of the same full symbol to a metric sphere gives smooth cosphere data. -/
theorem isSmoothCosphereSymbol_fullSymbolRadialCosphereSymbol {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) :
    IsSmoothCosphereSymbol (r := r) (q := q) g (fullSymbolRadialCosphereSymbol a g R) := by
  /- Constant frequency scaling preserves the original chartwise smoothness, including
  zero frequency. The existing smooth restriction theorem then performs the actual radial
  normalization; its scalar normalization is constant on the cosphere. -/
  let b : GlobalSymbolFunction (n := n) E F := fun x ξ ↦ a.val x (R • ξ)
  have hs : IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F b := by
    intro c hc e f _ _
    have hmap : ContDiffOn ℝ ∞
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          (p.1, R • p.2)) (symbolChartDomain E F c e f ×ˢ {ξ | ξ ≠ 0}) :=
      (contDiff_fst.prodMk (contDiff_snd.const_smul R)).contDiffOn
    have hmaps : Set.MapsTo
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          (p.1, R • p.2)) (symbolChartDomain E F c e f ×ˢ {ξ | ξ ≠ 0})
        (symbolChartDomain E F c e f ×ˢ Set.univ) :=
      fun p hp ↦ ⟨hp.1, Set.mem_univ _⟩
    apply ((a.property c hc e f).1.comp hmap hmaps).congr
    intro p hp
    have hscale : covectorFromChart c (c.symm p.1) (R • p.2) =
        R • covectorFromChart c (c.symm p.1) p.2 := by
      ext v
      simp [covectorFromChart]
      rfl
    change globalSymbolInChart E F b c e f p.1 p.2 =
      globalSymbolInChart E F a.val c e f p.1 (R • p.2)
    simp only [globalSymbolInChart, b, hscale]
  exact IsSmoothCosphereSymbol.smul g ((R ^ (-m) : ℝ) : ℂ)
    (isSmoothCosphereSymbol_restriction g b hs)

/-- The smooth homogeneous model obtained from the original full-symbol sphere data. -/
def fullSymbolRadialPrincipalSymbol {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) :
    homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m :=
  smoothCosphereExtension g m ⟨fullSymbolRadialCosphereSymbol a g R,
    isSmoothCosphereSymbol_fullSymbolRadialCosphereSymbol a g R⟩

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- Ellipticity of the original full symbol supplies an elliptic radial homogeneous model. -/
theorem IsEllipticFullGlobalSymbol.exists_radialPrincipalModel {m : ℝ}
    {a : globalSymbolSpace (n := n) (r := r) (q := q) E F m}
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val)
    (g : SmoothCotangentMetric (n := n) (M := M)) :
    ∃ R : ℝ, 0 < R ∧
      IsEllipticGlobalSymbol E F (fullSymbolRadialPrincipalSymbol a g R).val := by
  /- Choose one sphere strictly outside the original ellipticity disk. Every matrix
  on that sphere is invertible. A nonzero constant normalization preserves bijectivity,
  and the existing cosphere extension theorem propagates it along every positive ray. -/
  obtain ⟨L, hL, houter⟩ := ha.exists_metric_radius g
  let R : ℝ := L + 1
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hcos : IsEllipticCosphereSymbol g (fullSymbolRadialCosphereSymbol a g R) := by
    intro z
    have hlarge : L < g.length z.val.proj (R • z.val.snd) := by
      rw [g.length_smul, abs_of_pos hR, z.property, mul_one]
      dsimp [R]
      linarith
    have hinv := houter z.val.proj (R • z.val.snd) hlarge
    have hscalar : ((R ^ (-m) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hR (-m)).ne'
    exact (IsUnit.smul_bijective (isUnit_iff_ne_zero.mpr hscalar)).comp hinv.bijective
  refine ⟨R, hR, ?_⟩
  exact (isEllipticGlobalSymbol_cosphereExtension_iff g m
    (fullSymbolRadialCosphereSymbol a g R)).mpr hcos

section FrozenFunction

omit [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- The radial factor is one below radius 2R and R/r beyond radius 4R. -/
def fullSymbolFreezeScale (R r : ℝ) : ℝ :=
  let k := Real.smoothTransition ((r - 2 * R) / (2 * R))
  (1 - k) + k * (R / r)

/-- The radial construction agrees with the unchanged full symbol on its inner disk. -/
theorem fullSymbolFreezeScale_eq_one (R r : ℝ) (hR : 0 < R) (hr : r ≤ 2 * R) :
    fullSymbolFreezeScale R r = 1 := by
  have hk : Real.smoothTransition ((r - 2 * R) / (2 * R)) = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hr) (by positivity))
  simp only [fullSymbolFreezeScale, hk, sub_zero, zero_mul, add_zero]

/-- The radial rescaling remains positive on every positive metric radius. -/
theorem fullSymbolFreezeScale_pos (R r : ℝ) (hR : 0 < R) (hr : 0 < r) :
    0 < fullSymbolFreezeScale R r := by
  let k := Real.smoothTransition ((r - 2 * R) / (2 * R))
  have hk₀ : 0 ≤ k := Real.smoothTransition.nonneg _
  have hk₁ : k ≤ 1 := Real.smoothTransition.le_one _
  change 0 < (1 - k) + k * (R / r)
  by_cases hk : k = 1
  · rw [hk, sub_self, zero_add, one_mul]
    exact div_pos hR hr
  · exact add_pos_of_pos_of_nonneg (sub_pos.mpr (lt_of_le_of_ne hk₁ hk))
      (mul_nonneg hk₀ (div_pos hR hr).le)

/-- Freeze the actual full symbol along rays, retaining its original maps on the inner disk. -/
def fullSymbolFrozenFunction {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) :
    GlobalSymbolFunction (n := n) E F :=
  fun x ξ ↦
    let l := fullSymbolFreezeScale R (g.length x ξ)
    ((l ^ (-m) : ℝ) : ℂ) • a.val x (l • ξ)

/-- The freezing uses exactly the original full symbol at all frequencies in the inner disk. -/
theorem fullSymbolFrozenFunction_eq_of_length_le {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) (hR : 0 < R)
    (x : M) (ξ : CotangentFiber (n := n) x) (hξ : g.length x ξ ≤ 2 * R) :
    fullSymbolFrozenFunction a g R x ξ = a.val x ξ := by
  simp only [fullSymbolFrozenFunction, fullSymbolFreezeScale_eq_one R _ hR hξ,
    Real.one_rpow, Complex.ofReal_one, one_smul]

private theorem contMDiffOn_covectorFromChart_total
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
      (fun p ↦ (⟨c.symm p.1, covectorFromChart c (c.symm p.1) p.2⟩ :
        CotangentTotalSpace (n := n) (M := M))) (c.target ×ˢ univ) := by
  /- The actual inverse chart and its differential give a smooth cotangent map,
  including zero frequency. This is the chart-map part of the existing metric
  length proof; here its all-frequency domain is needed for the inner disk. -/
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  have hcm : c ∈ maximalAtlas I ∞ M := subset_maximalAtlas (I := I) hc
  intro p hp
  have hbase : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) I ∞
      (fun z ↦ c.symm z.1) p :=
    (contMDiffAt_symm_of_mem_maximalAtlas hcm hp.1).comp p contDiffAt_fst.contMDiffAt
  have hd := ((contMDiffAt_of_mem_maximalAtlas hcm (c.map_target hp.1)).mfderiv_const
    (m := (∞ : WithTop ℕ∞)) (by simp)).comp p hbase
  have hinner : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, CotangentModel n) ∞ (fun z ↦ innerSL ℝ z.2) p :=
    (innerSL ℝ).contDiff.contMDiff.contMDiffAt.comp p contDiffAt_snd.contMDiffAt
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨hbase, ?_⟩
  apply (hinner.clm_comp hd).congr_of_eventuallyEq
  filter_upwards with z
  ext v
  simp [covectorFromChart, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    Function.id_def, ContinuousLinearMap.comp_apply, I]
  rfl

/-- The actual radially frozen full symbol is smooth at every frequency. -/
theorem isSmoothFullGlobalSymbol_fullSymbolFrozenFunction {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) (hR : 0 < R) :
    IsSmoothFullGlobalSymbol (r := r) (q := q) E F (fullSymbolFrozenFunction a g R) := by
  /- On the inner disk the function is exactly the original smooth a. Elsewhere
  the metric radius is nonzero, so both the radial substitution and its positive
  real power are smooth. These neighborhoods cover every actual frequency. -/
  intro c hc e f _ _
  let V := symbolChartDomain E F c e f
  let W := V ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))
  let w (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    g.length (c.symm p.1) (covectorFromChart c (c.symm p.1) p.2)
  have hV : IsOpen V := isOpen_symbolChartDomain E F c e f
  have hW : IsOpen W := hV.prod isOpen_univ
  have hwcont : ContinuousOn w W :=
    (g.continuous_length.comp_continuousOn
      (contMDiffOn_covectorFromChart_total c hc).continuousOn).mono
        (fun p hp ↦ ⟨hp.1.1.1, mem_univ _⟩)
  have hcov_smul (z η : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
      covectorFromChart c (c.symm z) (t • η) =
        t • covectorFromChart c (c.symm z) η := by
    ext v
    exact real_inner_smul_left η _ t
  intro p hp
  by_cases hsmall : w p < 2 * R
  · -- On a whole neighborhood the unchanged full-symbol formula applies, even at zero.
    have hwAt : ContinuousAt w p := (hwcont p hp).continuousAt (hW.mem_nhds hp)
    have hnear : ∀ᶠ z in 𝓝 p, w z < 2 * R := hwAt (isOpen_Iio.mem_nhds hsmall)
    apply ContDiffAt.contDiffWithinAt
    apply ((a.property c hc e f).1.contDiffAt (hW.mem_nhds hp)).congr_of_eventuallyEq
    filter_upwards [hnear] with z hz
    change globalSymbolInChart E F (fullSymbolFrozenFunction a g R) c e f z.1 z.2 =
      globalSymbolInChart E F a.val c e f z.1 z.2
    simp only [globalSymbolInChart,
      fullSymbolFrozenFunction_eq_of_length_le a g R hR _ _ hz.le]
  · have hwp : 0 < w p := (show 0 < 2 * R by positivity).trans_le (le_of_not_gt hsmall)
    have hpne : p.2 ≠ 0 := by
      intro hz
      have hzero : covectorFromChart c (c.symm p.1) p.2 = 0 := by
        rw [hz]
        ext v
        change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (mfderiv _ _ c (c.symm p.1) v) = 0
        exact inner_zero_left _
      have hwzero : w p = 0 := (g.length_eq_zero_iff _ _).mpr hzero
      exact hwp.ne' hwzero
    let Q := c.target ×ˢ {η : EuclideanSpace ℝ (Fin n) | η ≠ 0}
    have hQ : IsOpen Q := c.open_target.prod isOpen_ne
    have hwAt : ContDiffAt ℝ ∞ w p :=
      (g.contDiffOn_length_covectorFromChart c hc).contDiffAt
        (hQ.mem_nhds ⟨hp.1.1.1, hpne⟩)
    let k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
      Real.smoothTransition ((w z - 2 * R) / (2 * R))
    let l (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
      fullSymbolFreezeScale R (w z)
    have hk : ContDiffAt ℝ ∞ k p :=
      Real.smoothTransition.contDiff.contDiffAt.comp p
        ((hwAt.sub contDiffAt_const).div_const (2 * R))
    have hl : ContDiffAt ℝ ∞ l p :=
      (contDiffAt_const.sub hk).add (hk.mul (contDiffAt_const.div hwAt hwp.ne'))
    have hlpos : 0 < l p := fullSymbolFreezeScale_pos R (w p) hR hwp
    have hfactor : ContDiffAt ℝ ∞ (fun z ↦ ((l z ^ (-m) : ℝ) : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p (hl.rpow_const_of_ne hlpos.ne')
    have harg : ContDiffAt ℝ ∞ (fun z ↦ (z.1, l z • z.2)) p :=
      contDiffAt_fst.prodMk (hl.smul contDiffAt_snd)
    have haAt : ContDiffAt ℝ ∞ (Function.uncurry (globalSymbolInChart E F a.val c e f))
        (p.1, l p • p.2) :=
      (a.property c hc e f).1.contDiffAt (hW.mem_nhds ⟨hp.1, mem_univ _⟩)
    apply ContDiffAt.contDiffWithinAt
    apply (hfactor.smul (haAt.comp p harg)).congr_of_eventuallyEq
    filter_upwards with z
    change globalSymbolInChart E F (fullSymbolFrozenFunction a g R) c e f z.1 z.2 =
      ((l z ^ (-m) : ℝ) : ℂ) • globalSymbolInChart E F a.val c e f z.1 (l z • z.2)
    simp only [globalSymbolInChart, fullSymbolFrozenFunction, l, w, hcov_smul,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end FrozenFunction

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
/-- Beyond the freezing radius, the actual function is its original radial homogeneous model. -/
theorem fullSymbolFrozenFunction_eq_radialPrincipalSymbol_of_length_ge {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) (hR : 0 < R)
    (x : M) (ξ : CotangentFiber (n := n) x) (hξ : 4 * R ≤ g.length x ξ) :
    fullSymbolFrozenFunction a g R x ξ = (fullSymbolRadialPrincipalSymbol a g R).val x ξ := by
  /- The transition is exactly one here. Its substitution returns to the same radius-R
  sphere and its scalar is the same homogeneous normalization, including arbitrary m. -/
  let r := g.length x ξ
  have hr : 0 < r := (show 0 < 4 * R by positivity).trans_le hξ
  have hne : ξ ≠ 0 := fun hz ↦ hr.ne' ((g.length_eq_zero_iff x ξ).mpr hz)
  have hk : Real.smoothTransition ((r - 2 * R) / (2 * R)) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ (show 0 < 2 * R by positivity)).mpr
    dsimp only [r]
    linarith
  have hscale : fullSymbolFreezeScale R r = R / r := by
    simp only [fullSymbolFreezeScale, hk, sub_self, zero_add, one_mul]
  have hpower : (R / r) ^ (-m) = r ^ m * R ^ (-m) := by
    rw [Real.div_rpow hR.le hr.le, Real.rpow_neg hr.le, div_inv_eq_mul]
    ring
  change (((fullSymbolFreezeScale R r ^ (-m) : ℝ) : ℂ) •
      a.val x (fullSymbolFreezeScale R r • ξ)) =
    cosphereExtension g m (fullSymbolRadialCosphereSymbol a g R) x ξ
  rw [hscale, cosphereExtension_of_ne_zero g m _ x ξ hne]
  change (((R / r) ^ (-m) : ℝ) : ℂ) • a.val x ((R / r) • ξ) =
    ((r ^ m : ℝ) : ℂ) • (((R ^ (-m) : ℝ) : ℂ) • a.val x (R • (r⁻¹ • ξ)))
  rw [hpower, Complex.ofReal_mul]
  simp only [mul_smul, div_eq_mul_inv]

omit [SecondCountableTopology M] [CompactSpace M] in
/-- The actual frozen function is an order-m symbol with the original radial principal class. -/
theorem exists_fullSymbolFrozenSymbol {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) (hR : 0 < R)
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F) :
    ∃ b : globalSymbolSpace (n := n) (r := r) (q := q) E F m,
      b.val = fullSymbolFrozenFunction a g R ∧
        globalPrincipalSymbolClass E F m b =
          globalPrincipalSymbolClass E F m
            (A.regularizedSymbol m (fullSymbolRadialPrincipalSymbol a g R).val
              (fullSymbolRadialPrincipalSymbol a g R).property.1
              (fullSymbolRadialPrincipalSymbol a g R).property.2) := by
  /- The original finite regularization recovers the homogeneous model beyond one
  metric radius. The frozen function agrees there and is already smooth everywhere.
  Its deviation is supported at bounded frequencies, so the existing smoothing theorem
  supplies order m and equality in the genuine principal quotient. -/
  let p := fullSymbolRadialPrincipalSymbol a g R
  let c := A.regularizedSymbol m p.val p.property.1 p.property.2
  obtain ⟨C, hC, hnorm⟩ := A.exists_covectorInChart_norm_bounds g
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hrecover (x : M) (ξ : CotangentFiber (n := n) x) (hξ : C ≤ g.length x ξ) :
      c.val x ξ = p.val x ξ := by
    have hcut (i : Fin A.size) : (A.patch i).weight x *
        highFrequencyCutoff n (covectorInChart (A.patch i).chart x ξ) = (A.patch i).weight x := by
      by_cases hw : (A.patch i).weight x = 0
      · simp only [hw, zero_mul]
      · have hn := (hnorm i x hw ξ).1
        have hlarge : 1 ≤ ‖covectorInChart (A.patch i).chart x ξ‖ := by
          by_contra h
          have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge h) hCpos
          rw [mul_one] at hlt
          linarith
        rw [highFrequencyCutoff_eq_one _ hlarge, mul_one]
    change (∑ i, (((A.patch i).weight x *
      highFrequencyCutoff n (covectorInChart (A.patch i).chart x ξ) : ℝ) : ℂ) • p.val x ξ) = _
    simp only [hcut, ← Finset.sum_smul, ← Complex.ofReal_sum, A.sum_weight,
      Complex.ofReal_one, one_smul]
  let L := max (4 * R) C
  have hagree : ∀ x ξ, L ≤ g.length x ξ → fullSymbolFrozenFunction a g R x ξ = c.val x ξ := by
    intro x ξ hξ
    exact (fullSymbolFrozenFunction_eq_radialPrincipalSymbol_of_length_ge a g R hR x ξ
      ((le_max_left _ _).trans hξ)).trans
        (hrecover x ξ ((le_max_right _ _).trans hξ)).symm
  have hb : IsGlobalSymbol (r := r) (q := q) E F m (fullSymbolFrozenFunction a g R) :=
    isGlobalSymbol_of_eq_metric_high_frequency c (fullSymbolFrozenFunction a g R)
      (isSmoothFullGlobalSymbol_fullSymbolFrozenFunction a g R hR) g L hagree
  let b : globalSymbolSpace (n := n) (r := r) (q := q) E F m :=
    ⟨fullSymbolFrozenFunction a g R, hb⟩
  refine ⟨b, rfl, ?_⟩
  exact globalPrincipalSymbolClass_eq_of_eq_metric_high_frequency b c g L hagree


/-- A general elliptic symbol admits an actual elliptic freezing with its radial principal class. -/
theorem IsEllipticFullGlobalSymbol.exists_fullSymbolFrozenEllipticSymbol {m : ℝ}
    {a : globalSymbolSpace (n := n) (r := r) (q := q) E F m}
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F) :
    ∃ R : ℝ, 0 < R ∧
      ∃ b : globalSymbolSpace (n := n) (r := r) (q := q) E F m,
        b.val = fullSymbolFrozenFunction a g R ∧
        IsEllipticFullGlobalSymbol (r := r) (q := q) E F m b.val ∧
        (∀ x (ξ : CotangentFiber (n := n) x), R < g.length x ξ →
          (a.val x ξ).IsInvertible ∧ (b.val x ξ).IsInvertible) ∧
        globalPrincipalSymbolClass E F m b =
          globalPrincipalSymbolClass E F m
            (A.regularizedSymbol m (fullSymbolRadialPrincipalSymbol a g R).val
              (fullSymbolRadialPrincipalSymbol a g R).property.1
              (fullSymbolRadialPrincipalSymbol a g R).property.2) := by
  /- Freeze outside the original ellipticity disk. The interpolation samples only
  invertible original maps on that exterior. Its eventual homogeneous model supplies
  quantitative ellipticity through the accepted regularized-class comparison. -/
  obtain ⟨L, hL, houter⟩ := ha.exists_metric_radius g
  let R : ℝ := L + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hLR : L < R := by dsimp [R]; linarith
  -- The same original radius-R sphere supplies the elliptic homogeneous model.
  have hcos : IsEllipticCosphereSymbol g (fullSymbolRadialCosphereSymbol a g R) := by
    intro z
    have hlarge : L < g.length z.val.proj (R • z.val.snd) := by
      rw [g.length_smul, abs_of_pos hR, z.property, mul_one]
      exact hLR
    have hscalar : ((R ^ (-m) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hR (-m)).ne'
    exact (IsUnit.smul_bijective (isUnit_iff_ne_zero.mpr hscalar)).comp
      (houter z.val.proj (R • z.val.snd) hlarge).bijective
  have hrad : IsEllipticGlobalSymbol E F (fullSymbolRadialPrincipalSymbol a g R).val :=
    (isEllipticGlobalSymbol_cosphereExtension_iff g m
      (fullSymbolRadialCosphereSymbol a g R)).mpr hcos
  obtain ⟨b, hb, hclass⟩ := exists_fullSymbolFrozenSymbol a g R hR A
  have hbe : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m b.val :=
    (isEllipticFullGlobalSymbol_iff_of_class_eq b
      (A.regularizedSymbol m (fullSymbolRadialPrincipalSymbol a g R).val
        (fullSymbolRadialPrincipalSymbol a g R).property.1
        (fullSymbolRadialPrincipalSymbol a g R).property.2) hclass).mpr
          ((isEllipticFullGlobalSymbol_regularizedSymbol_iff A m _ _ _).mpr hrad)
  refine ⟨R, hR, b, hb, hbe, ?_, hclass⟩
  intro x ξ hξ
  refine ⟨houter x ξ (hLR.trans hξ), ?_⟩
  -- On this exterior the actual rescaled radius lies between R and the original radius.
  let t : ℝ := g.length x ξ
  let k : ℝ := Real.smoothTransition ((t - 2 * R) / (2 * R))
  let l : ℝ := fullSymbolFreezeScale R t
  have ht : 0 < t := hR.trans hξ
  have hk₀ : 0 ≤ k := Real.smoothTransition.nonneg _
  have hk₁ : k ≤ 1 := Real.smoothTransition.le_one _
  have hl : 0 < l := fullSymbolFreezeScale_pos R t hR ht
  have hlower : R ≤ l * t := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr hk₁) (sub_nonneg.mpr hξ.le)
    have hformula : l * t = (1 - k) * t + k * R := by
      dsimp only [l, fullSymbolFreezeScale, k]
      field_simp
    rw [hformula]
    nlinarith
  have hlarge : L < g.length x (l • ξ) := by
    rw [g.length_smul, abs_of_pos hl]
    exact hLR.trans_le hlower
  have hscalar : ((l ^ (-m) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hl (-m)).ne'
  have hbij : Function.Bijective (fullSymbolFrozenFunction a g R x ξ) :=
    (IsUnit.smul_bijective (isUnit_iff_ne_zero.mpr hscalar)).comp
      (houter x (l • ξ) hlarge).bijective
  rw [hb]
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let e : E x ≃L[ℂ] F x :=
    LinearEquiv.toContinuousLinearEquiv
      (LinearEquiv.ofBijective (fullSymbolFrozenFunction a g R x ξ).toLinearMap hbij)
  exact ⟨e, rfl⟩

end AtiyahSinger
