/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CotangentChartNormBounds
public import AtiyahSinger.Analysis.FullSymbolMetricInverseBound
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# One elliptic parameter from a finite metric cover

Public module ID: M0626.

A finite compact chart cover and the original Hermitian energy estimates
choose one positive parameter before every point and cotangent chart. Compact
comparison with a fixed smooth cotangent metric transports these estimates
to all original native charts and frames. The conclusion is quantitative
first-order full-symbol ellipticity, not only pointwise invertibility.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Set
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  (E F : SmoothFiniteComplexBundle (n := n) M)

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1800000 in
-- Transfer metric estimates through the original source and target frame comparisons.
/-- Finite compact metric estimates choose a common parameter and imply full ellipticity. -/
theorem exists_isEllipticFullGlobalSymbol_of_finite_metric_bounds
    {ι : Type*} [Finite ι]
    (g : SmoothCotangentMetric (n := n) (M := M))
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
    (p : ℝ → GlobalSymbolFunction (n := n) E.Fiber F.Fiber)
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (K : ι → Set M) (hK : ∀ i, IsCompact (K i))
    (hKc : ∀ i, K i ⊆ (c i).source) (hcover : ∀ x, ∃ i, x ∈ K i)
    (hlocal : ∀ i, ∃ ε₀ R C : ℝ, 0 < ε₀ ∧ 0 < R ∧ 0 ≤ C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ x ∈ K i, ∀ η : CotangentFiber (n := n) x,
        R ≤ ‖covectorInChart (c i) x η‖ → Function.Bijective (p ε x η) ∧
          ∀ u : E.Fiber x, (1 + ‖covectorInChart (c i) x η‖) ^ 2 *
            (h.pairing x u u).re ≤ C * (k.pairing x (p ε x η u) (p ε x η u)).re) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      IsEllipticFullGlobalSymbol (r := E.rank) (q := F.rank) E.Fiber F.Fiber 1 (p ε) := by
  classical
  let := Fintype.ofFinite ι
  choose εj Rj Cj hεj hRj hCj hbound using hlocal
  let ε₀ := (1 + ∑ i, (εj i)⁻¹)⁻¹
  have hsumε : 0 ≤ ∑ i, (εj i)⁻¹ :=
    Finset.sum_nonneg (fun i _ ↦ inv_nonneg.mpr (hεj i).le)
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hεle (i : ι) : ε₀ ≤ εj i := by
    dsimp [ε₀]
    rw [← one_div]
    apply (div_le_iff₀ (by positivity : 0 < 1 + ∑ i, (εj i)⁻¹)).mpr
    have hi := Finset.single_le_sum (fun j _ ↦ inv_nonneg.mpr (hεj j).le)
      (Finset.mem_univ i)
    have hh := mul_le_mul_of_nonneg_left hi (hεj i).le
    rw [mul_inv_cancel₀ (hεj i).ne'] at hh
    nlinarith [hεj i]
  -- The chosen cotangent metric compares all of the finitely many source frequencies.
  have hnorm (i : ι) : ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K i, ∀ η : CotangentFiber x,
      g.length x η ≤ B * ‖covectorInChart (c i) x η‖ := by
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let X := EuclideanSpace ℝ (Fin n)
    let d := c i
    have hd := hc i
    have himage : IsCompact (c i '' K i) :=
      (hK i).image_of_continuousOn ((c i).continuousOn.mono (hKc i))
    let S := (d '' K i) ×ˢ Metric.sphere (0 : X) 1
    have hS : IsCompact S := himage.prod (isCompact_sphere _ _)
    have hcont : ContinuousOn (fun z : X × X ↦
        g.length (d.symm z.1) (covectorFromChart d (d.symm z.1) z.2)) S := by
      intro z hz
      have hzTarget : z.1 ∈ d.target := by
        obtain ⟨x, hx, heq⟩ := hz.1
        rw [← heq]
        exact d.map_source (hKc i hx)
      have hbase : ContMDiffAt 𝓘(ℝ, X × X) I ∞ (fun w ↦ d.symm w.1) z :=
        (contMDiffAt_symm_of_mem_maximalAtlas hd hzTarget).comp z
          contDiffAt_fst.contMDiffAt
      have hderiv := ((contMDiffAt_of_mem_maximalAtlas hd (d.map_target hzTarget)).mfderiv_const
        (m := (∞ : WithTop ℕ∞)) (by simp)).comp z hbase
      have hinner : ContMDiffAt 𝓘(ℝ, X × X) 𝓘(ℝ, CotangentModel n) ∞
          (fun w ↦ innerSL ℝ w.2) z :=
        (innerSL ℝ).contDiff.contMDiff.contMDiffAt.comp z contDiffAt_snd.contMDiffAt
      have hmap : ContMDiffAt 𝓘(ℝ, X × X) (I.prod 𝓘(ℝ, CotangentModel n)) ∞
          (fun w ↦ (⟨d.symm w.1, covectorFromChart d (d.symm w.1) w.2⟩ :
            CotangentTotalSpace)) z := by
        apply (contMDiffAt_hom_bundle _).mpr
        refine ⟨hbase, ?_⟩
        apply (hinner.clm_comp hderiv).congr_of_eventuallyEq
        filter_upwards with w
        ext v
        simp [covectorFromChart, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
          Function.id_def, ContinuousLinearMap.comp_apply]
        rfl
      exact (g.continuous_length.continuousAt.comp hmap.continuousAt).continuousWithinAt
    obtain ⟨B, hBbound⟩ := hS.exists_bound_of_continuousOn hcont
    refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro x hx η
    have hdiff : d.MDifferentiable I I :=
      ⟨(contMDiffOn_of_mem_maximalAtlas hd).mdifferentiableOn (by simp),
        (contMDiffOn_symm_of_mem_maximalAtlas hd).mdifferentiableOn (by simp)⟩
    have hrecover : covectorFromChart d x (covectorInChart d x η) = η := by
      have hcoord : innerSL ℝ (covectorInChart d x η) =
          η.comp (mfderiv I I d.symm (d x)) := by
        apply ContinuousLinearMap.coe_injective
        apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
        intro j
        simp [covectorInChart, EuclideanSpace.basisFun_apply,
          EuclideanSpace.inner_single_right]
        rfl
      ext v
      have hi := congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x ↦ L v)
        (hdiff.symm_comp_deriv (hKc i hx))
      exact (DFunLike.congr_fun hcoord (mfderiv I I d x v)).trans (congrArg η hi)
    let ξ := covectorInChart d x η
    by_cases hξ : ξ = 0
    · have hη : η = 0 := by
        change covectorFromChart d x ξ = η at hrecover
        rw [hξ] at hrecover
        apply hrecover.symm.trans
        ext v
        change inner ℝ (0 : X) (mfderiv I I d x v) = 0
        exact inner_zero_left _
      rw [(g.length_eq_zero_iff x η).mpr hη]
      exact mul_nonneg (zero_le_one.trans (le_max_right _ _)) (norm_nonneg _)
    let v := ‖ξ‖⁻¹ • ξ
    have hv : v ∈ Metric.sphere (0 : X) 1 := by
      simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hξ
    have hscale : ‖ξ‖ • v = ξ := by simp [v, smul_smul, norm_ne_zero_iff.mpr hξ]
    have hcov : covectorFromChart d x ξ = ‖ξ‖ • covectorFromChart d x v := by
      calc
        covectorFromChart d x ξ = covectorFromChart d x (‖ξ‖ • v) :=
          congrArg (covectorFromChart d x) hscale.symm
        _ = ‖ξ‖ • covectorFromChart d x v := by
          ext w
          change inner ℝ (‖ξ‖ • v) (mfderiv I I d x w) =
            ‖ξ‖ * inner ℝ v (mfderiv I I d x w)
          exact real_inner_smul_left _ _ _
    have hvalue := hBbound (d x, v) ⟨⟨x, hx, rfl⟩, hv⟩
    rw [d.left_inv (hKc i hx), Real.norm_eq_abs,
      abs_of_nonneg (g.length_nonneg _ _)] at hvalue
    change g.length x (covectorFromChart d x v) ≤ B at hvalue
    calc
      g.length x η = ‖ξ‖ * g.length x (covectorFromChart d x v) := by
        rw [← hrecover, hcov, g.length_smul, abs_of_nonneg (norm_nonneg ξ)]
      _ ≤ max B 1 * ‖ξ‖ := by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (hvalue.trans (le_max_left _ _)) (norm_nonneg ξ)
  choose B hB hlength using hnorm
  let R₀ := 1 + ∑ i, B i * Rj i
  let C₀ := ∑ i, (1 + B i) ^ 2 * Cj i
  have hR₀ : 0 < R₀ := by
    have hs : 0 ≤ ∑ i, B i * Rj i :=
      Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hB i).le (hRj i).le)
    dsimp [R₀]
    linarith
  have hC₀ : 0 ≤ C₀ :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (sq_nonneg _) (hCj i))
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  have hglobal (x : M) (η : CotangentFiber x) (hlarge : R₀ ≤ g.length x η) :
      Function.Bijective (p ε x η) ∧ ∀ u : E.Fiber x,
        (1 + g.length x η) ^ 2 * (h.pairing x u u).re ≤
          C₀ * (k.pairing x (p ε x η u) (p ε x η u)).re := by
    obtain ⟨i, hx⟩ := hcover x
    have hRi : B i * Rj i ≤ R₀ := by
      have hi := Finset.single_le_sum (fun j _ ↦ mul_nonneg (hB j).le (hRj j).le)
        (Finset.mem_univ i)
      dsimp [R₀]
      linarith
    have hfreq : Rj i ≤ ‖covectorInChart (c i) x η‖ := by
      have hh := hlength i x hx η
      nlinarith [hB i]
    obtain ⟨hbij, he⟩ := hbound i ε hε (hεsmall.trans (hεle i)) x hx η hfreq
    refine ⟨hbij, ?_⟩
    intro u
    have hlenNonneg := g.length_nonneg x η
    have hweight : 1 + g.length x η ≤ (1 + B i) *
        (1 + ‖covectorInChart (c i) x η‖) := by
      have hh := hlength i x hx η
      nlinarith [hB i, norm_nonneg (covectorInChart (c i) x η)]
    have hweightSq := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + g.length x η) hweight 2
    rw [mul_pow] at hweightSq
    calc
      (1 + g.length x η) ^ 2 * (h.pairing x u u).re ≤
          ((1 + B i) ^ 2 * (1 + ‖covectorInChart (c i) x η‖) ^ 2) *
            (h.pairing x u u).re :=
        mul_le_mul_of_nonneg_right hweightSq ((h.toCore x).re_inner_nonneg u)
      _ ≤ ((1 + B i) ^ 2 * Cj i) * (k.pairing x (p ε x η u) (p ε x η u)).re := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (he u) (sq_nonneg (1 + B i))
      _ ≤ C₀ * (k.pairing x (p ε x η u) (p ε x η u)).re :=
        mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun j _ ↦ mul_nonneg (sq_nonneg (1 + B j)) (hCj j))
            (Finset.mem_univ i))
          ((k.toCore x).re_inner_nonneg _)
  -- Test every native chart and frame pair, with their own compact metric comparison.
  intro d hd e f _ _ L hL hLc
  have hbase : IsCompact (d.symm '' L) :=
    hLc.image_of_continuousOn (d.continuousOn_symm.mono (fun x hx ↦ (hL hx).1.1))
  have hbaseE : d.symm '' L ⊆ d.source ∩ e.baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨d.map_target (hL hz).1.1, (hL hz).1.2⟩
  have hbaseF : d.symm '' L ⊆ d.source ∩ f.baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨d.map_target (hL hz).1.1, (hL hz).2⟩
  obtain ⟨b, _, hb, _, hcoordinates⟩ :=
    g.exists_length_bounds_on d hd L hLc (fun x hx ↦ (hL hx).1.1)
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let : MeasurableSpace M := borel M
  let AE := nativeSmoothComplexBundleAtlas (n := n) (r := E.rank) E.Fiber
  let AF := nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber
  obtain ⟨aE, _, haE, _, hEbound⟩ := AE.exists_covariant_array_norm_sq_bounds g
    h.toContinuousHermitianMetric h.isSmoothHermitianMetric_nativeAtlas
    d hd ⟨e, inferInstance⟩ 0 (d.symm '' L) hbase hbaseE
  obtain ⟨_, bF, _, hbF, hFbound⟩ := AF.exists_covariant_array_norm_sq_bounds g
    k.toContinuousHermitianMetric k.isSmoothHermitianMetric_nativeAtlas
    d hd ⟨f, inferInstance⟩ 0 (d.symm '' L) hbase hbaseF
  let D := C₀ * bF / aE
  let C := (D + 1) * (1 + b⁻¹)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨R₀ / b, C, div_pos hR₀ hb, hC, ?_⟩
  intro z hz ξ hξ
  let x := d.symm z
  let η := covectorFromChart d x ξ
  have hlenNonneg := g.length_nonneg x η
  let ec := e.continuousLinearEquivAt ℂ x (hL hz).1.2
  let fc := f.continuousLinearEquivAt ℂ x (hL hz).2
  let a := globalSymbolInChart E.Fiber F.Fiber (p ε) d e f z ξ
  have hlarge : R₀ ≤ g.length x η := by
    have hbb := (hcoordinates z hz ξ).1
    have hh : R₀ ≤ b * ‖ξ‖ := by simpa [mul_comm] using (div_le_iff₀ hb).mp hξ
    exact hh.trans hbb
  obtain ⟨hbij, henergy⟩ := hglobal x η hlarge
  have ha : a = fc.toContinuousLinearMap.comp ((p ε x η).comp ec.symm.toContinuousLinearMap) := by
    dsimp only [a, globalSymbolInChart]
    rw [← f.coe_continuousLinearEquivAt_eq' (R := ℂ) (hL hz).2,
      ← e.symm_continuousLinearEquivAt_eq' (R := ℂ) (hL hz).1.2]
  have hai : a.IsInvertible := by
    let : FiniteDimensional ℂ (E.Fiber x) := .of_injective ec.toLinearMap ec.injective
    rw [ha]
    exact ⟨ec.symm.trans
      ((LinearEquiv.ofBijective (p ε x η).toLinearMap hbij).toContinuousLinearEquiv.trans fc),
      rfl⟩
  refine ⟨hai, ?_⟩
  change ‖a.inverse‖ ≤ C * (1 + ‖ξ‖) ^ (-(1 : ℝ))
  rw [Real.rpow_neg_one, ← div_eq_mul_inv]
  apply a.inverse.opNorm_le_bound (by positivity)
  intro v
  have hx : x ∈ d.symm '' L := ⟨z, hz, rfl⟩
  have hEcoord (w : EuclideanSpace ℂ (Fin E.rank)) :
      aE * ‖w‖ ^ 2 ≤ (h.pairing x (ec.symm w) (ec.symm w)).re := by
    have hframe : AE.frameLinearEquiv ⟨e, inferInstance⟩ x (hbaseE hx).2 =
        ec.toLinearEquiv.trans (EuclideanSpace.equiv (Fin E.rank) ℂ).toLinearEquiv := by
      ext u
      rfl
    have heq : (AE.frameLinearEquiv ⟨e, inferInstance⟩ x (hbaseE hx).2).symm
        ((EuclideanSpace.equiv (Fin E.rank) ℂ) w) = ec.symm w := by
      rw [hframe]
      exact congrArg ec.symm ((EuclideanSpace.equiv (Fin E.rank) ℂ).symm_apply_apply w)
    have hh := (hEbound x hx (fun _ ↦ w)).1
    simp only [Finset.univ_unique, Finset.sum_singleton, Fin.prod_univ_zero, one_mul] at hh
    change aE * ‖w‖ ^ 2 ≤ (h.pairing x
      ((AE.frameLinearEquiv ⟨e, inferInstance⟩ x (hbaseE hx).2).symm
        ((EuclideanSpace.equiv (Fin E.rank) ℂ) w))
      ((AE.frameLinearEquiv ⟨e, inferInstance⟩ x (hbaseE hx).2).symm
        ((EuclideanSpace.equiv (Fin E.rank) ℂ) w))).re at hh
    rwa [heq] at hh
  have hFcoord : (k.pairing x (fc.symm v) (fc.symm v)).re ≤ bF * ‖v‖ ^ 2 := by
    have hframe : AF.frameLinearEquiv ⟨f, inferInstance⟩ x (hbaseF hx).2 =
        fc.toLinearEquiv.trans (EuclideanSpace.equiv (Fin F.rank) ℂ).toLinearEquiv := by
      ext u
      rfl
    have heq : (AF.frameLinearEquiv ⟨f, inferInstance⟩ x (hbaseF hx).2).symm
        ((EuclideanSpace.equiv (Fin F.rank) ℂ) v) = fc.symm v := by
      rw [hframe]
      exact congrArg fc.symm ((EuclideanSpace.equiv (Fin F.rank) ℂ).symm_apply_apply v)
    have hh := (hFbound x hx (fun _ ↦ v)).2
    simp only [Finset.univ_unique, Finset.sum_singleton, Fin.prod_univ_zero, one_mul] at hh
    change (k.pairing x
      ((AF.frameLinearEquiv ⟨f, inferInstance⟩ x (hbaseF hx).2).symm
        ((EuclideanSpace.equiv (Fin F.rank) ℂ) v))
      ((AF.frameLinearEquiv ⟨f, inferInstance⟩ x (hbaseF hx).2).symm
        ((EuclideanSpace.equiv (Fin F.rank) ℂ) v))).re ≤ bF * ‖v‖ ^ 2 at hh
    rwa [heq] at hh
  have hvalue : p ε x η (ec.symm (a.inverse v)) = fc.symm v := by
    apply fc.injective
    rw [fc.apply_symm_apply]
    exact (congrArg (fun T ↦ T (a.inverse v)) ha).symm.trans (hai.self_apply_inverse v)
  have he := henergy (ec.symm (a.inverse v))
  rw [hvalue] at he
  have hs : ((1 + g.length x η) * ‖a.inverse v‖) ^ 2 ≤ D * ‖v‖ ^ 2 := by
    have hlow := mul_le_mul_of_nonneg_left (hEcoord (a.inverse v))
      (sq_nonneg (1 + g.length x η))
    have hhigh := mul_le_mul_of_nonneg_left hFcoord hC₀
    have hall := hlow.trans (he.trans hhigh)
    dsimp [D]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ haE).mpr
    nlinarith [hall]
  have hn : (1 + g.length x η) * ‖a.inverse v‖ ≤ (D + 1) * ‖v‖ := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    have hd : D ≤ (D + 1) ^ 2 := by nlinarith
    calc
      ((1 + g.length x η) * ‖a.inverse v‖) ^ 2 ≤ D * ‖v‖ ^ 2 := hs
      _ ≤ (D + 1) ^ 2 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
      _ = _ := (mul_pow _ _ _).symm
  have hlengthScale : 1 + ‖ξ‖ ≤ (1 + b⁻¹) * (1 + g.length x η) := by
    have hh : ‖ξ‖ ≤ b⁻¹ * g.length x η := (le_inv_mul_iff₀ hb).mpr
      (hcoordinates z hz ξ).1
    have hbi : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
    nlinarith [g.length_nonneg x η]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 1 + ‖ξ‖)).mpr
  dsimp [C]
  have hfirst := mul_le_mul_of_nonneg_right hlengthScale (norm_nonneg (a.inverse v))
  have hsecond := mul_le_mul_of_nonneg_left hn (show 0 ≤ 1 + b⁻¹ by positivity)
  nlinarith

end AtiyahSinger
