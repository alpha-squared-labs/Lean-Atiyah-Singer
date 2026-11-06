/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EuclideanSobolev
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Local smoothness and singular support of tempered distributions

Public module ID: M0441.

D05/A02 prerequisites for SG III.3.9. Local smoothness means agreement with a
smooth function on compactly supported tests inside the open set. No global growth
condition is imposed on this local representative. Singular support has its usual
meaning, as in Taylor II.2, p.39; it is different from distributional support.
The regularity APIs below use open sets. Complex test functions pair bilinearly
with vector-valued distributions, consistently with mathlib's tempered model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

variable {n r : ℕ}

/-- Agreement with a smooth representative on all compact tests supported in U. -/
def IsSmoothDistributionOn
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r),
    ContDiffOn ℝ ∞ f U ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), HasCompactSupport φ → tsupport φ ⊆ U →
        u φ = ∫ x, φ x • f x

/-- Points with no open neighborhood on which the distribution is smooth. -/
def singularSupport
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ¬ ∃ U : Set (EuclideanSpace ℝ (Fin n)),
    IsOpen U ∧ x ∈ U ∧ IsSmoothDistributionOn u U}

/-- A Schwartz function induces a smooth distribution on every open set. -/
theorem isSmoothDistributionOn_schwartz
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) :
    IsSmoothDistributionOn
      (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) U := by
  /- Use u itself as representative and restrict its global real smoothness to U.
  The Schwartz-to-distribution coercion is defined by the bilinear integral
  against scalar test functions, with no complex conjugation in that formula. -/
  refine ⟨u, hU.contDiffOn_iff.mpr (fun _ _ ↦ (u.smooth ⊤).contDiffAt), ?_⟩
  intro φ hφ hφU
  exact SchwartzMap.coe_apply u φ

/-- Smoothness of a distribution restricts to any smaller open set. -/
theorem IsSmoothDistributionOn.mono
    {u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hu : IsSmoothDistributionOn u U)
    (hV : IsOpen V) (hVU : V ⊆ U) : IsSmoothDistributionOn u V := by
  /- Restrict the same smooth representative to V. A compactly supported test
  whose closed support lies in V also has support in U, so the original integral
  identity applies. The representative needs no growth control away from U. -/
  obtain ⟨f, hf, hrepr⟩ := hu
  refine ⟨f, hV.contDiffOn_iff.mpr (fun _ hx ↦
    hf.contDiffAt (Filter.mem_of_superset (hV.mem_nhds hx) hVU)), ?_⟩
  intro φ hφ hφV
  exact hrepr φ hφ (hφV.trans hVU)

/-- The sum of locally smooth distributions is represented by the sum of the functions. -/
theorem IsSmoothDistributionOn.add
    {u v : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hu : IsSmoothDistributionOn u U) (hv : IsSmoothDistributionOn v U) :
    IsSmoothDistributionOn (u + v) U := by
  /- Add the two smooth representatives on U. For every admitted test, both
  products with the representatives are continuous and compactly supported:
  near its support use smoothness on U, and off that support the product is zero.
  Their integrability justifies adding the two defining integrals. -/
  obtain ⟨f, hf, huf⟩ := hu
  obtain ⟨g, hg, hvg⟩ := hv
  refine ⟨fun x ↦ f x + g x, hf.add hg, ?_⟩
  intro φ hφ hφU
  -- A compact test removes any behavior of its representative outside U.
  have integrable_test_product
      (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
      (ha : ContDiffOn ℝ ∞ a U) : Integrable (fun x ↦ φ x • a x) := by
    have hcont : Continuous (fun x ↦ φ x • a x) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      by_cases hx : x ∈ tsupport φ
      · exact φ.continuous.continuousAt.smul
          (ha.continuousOn.continuousAt (hU.mem_nhds (hφU hx)))
      · apply (continuousAt_const (y := (0 : EuclideanSpace ℂ (Fin r)))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
        simp [image_eq_zero_of_notMem_tsupport hy]
    exact hcont.integrable_of_hasCompactSupport hφ.smul_right
  -- Both defining pairings are integrable, so their sum is the pairing with f + g.
  change u φ + v φ = _
  rw [huf φ hφ hφU, hvg φ hφ hφU]
  simp_rw [smul_add]
  exact (integral_add (integrable_test_product f hf)
    (integrable_test_product g hg)).symm

/-- Singular support is closed, because having a smooth representative is locally open. -/
theorem isClosed_singularSupport
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    IsClosed (singularSupport u) := by
  /- The complement is the union of all open sets on which u is represented
  by a smooth function. Such a union is open. This argument uses only the
  neighborhood definition and does not confuse singular support with ordinary support. -/
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change ¬ ¬ ∃ U, IsOpen U ∧ x ∈ U ∧ IsSmoothDistributionOn u U at hx
  obtain ⟨U, hU, hxU, hu⟩ := not_not.mp hx
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy
  change ¬ ¬ ∃ V, IsOpen V ∧ y ∈ V ∧ IsSmoothDistributionOn u V
  exact not_not.mpr ⟨U, hU, hy, hu⟩

open scoped Manifold Topology in
/-- On open sets, avoiding singular support is equivalent to having a smooth representative. -/
theorem isSmoothDistributionOn_iff_disjoint_singularSupport
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) :
    IsSmoothDistributionOn u U ↔ Disjoint U (singularSupport u) := by
  /- One direction uses U itself as a smooth neighborhood. Conversely, every
  point of U has a smaller smooth neighborhood. Two continuous representatives
  of the same distribution agree on overlaps: test their difference against
  compact smooth scalar functions, component by component. Glue the representatives
  and use a finite partition of unity on each compact test support to verify the
  integral identity. No assertion of global polynomial growth follows from gluing. -/
  classical
  constructor
  · intro hu
    refine Set.disjoint_left.mpr ?_
    intro x hxU hxs
    exact hxs ⟨U, hU, hxU, hu⟩
  intro hdisjoint
  -- Local representatives exist at every point and can be restricted inside U.
  have local_representative (x : U) :
      ∃ V : Set (EuclideanSpace ℝ (Fin n)),
        ∃ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r),
          IsOpen V ∧ x.1 ∈ V ∧ V ⊆ U ∧ ContDiffOn ℝ ∞ f V ∧
            ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
              HasCompactSupport φ → tsupport φ ⊆ V → u φ = ∫ y, φ y • f y := by
    have hx : x.1 ∉ singularSupport u := fun hs ↦
      Set.disjoint_left.mp hdisjoint x.2 hs
    change ¬ ¬ ∃ V, IsOpen V ∧ x.1 ∈ V ∧ IsSmoothDistributionOn u V at hx
    obtain ⟨V, hV, hxV, f, hf, hrepr⟩ := not_not.mp hx
    refine ⟨V ∩ U, f, hV.inter hU, ⟨hxV, x.2⟩, Set.inter_subset_right,
      hf.mono Set.inter_subset_left, ?_⟩
    intro φ hφ hφV
    exact hrepr φ hφ (hφV.trans Set.inter_subset_left)
  choose V f hV hxV hVU hf hrepr using local_representative
  -- Compact test factors make a merely local continuous representative integrable.
  have integrable_product
      (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
      (W : Set (EuclideanSpace ℝ (Fin n))) (hW : IsOpen W)
      (ha : ContinuousOn a W) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (hφ : HasCompactSupport φ) (hφW : tsupport φ ⊆ W) :
      Integrable (fun y ↦ φ y • a y) := by
    have hcont : Continuous (fun y ↦ φ y • a y) := by
      apply continuous_iff_continuousAt.mpr
      intro y
      by_cases hy : y ∈ tsupport φ
      · exact φ.continuous.continuousAt.smul
          (ha.continuousAt (hW.mem_nhds (hφW hy)))
      · apply (continuousAt_const (y := (0 : EuclideanSpace ℂ (Fin r)))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hy] with z hz
        simp [image_eq_zero_of_notMem_tsupport hz]
    exact hcont.integrable_of_hasCompactSupport hφ.smul_right
  -- Distributional equality implies pointwise equality of continuous local representatives.
  have agree (i j : U) : Set.EqOn (f i) (f j) (V i ∩ V j) := by
    have hopen : IsOpen (V i ∩ V j) := (hV i).inter (hV j)
    have hfi := (hf i).continuousOn.mono (Set.inter_subset_left (t := V j))
    have hfj := (hf j).continuousOn.mono (Set.inter_subset_right (s := V i))
    have hzero : ∀ᵐ y ∂volume, y ∈ V i ∩ V j → (f i - f j) y = 0 := by
      apply hopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((hfi.sub hfj).locallyIntegrableOn hopen.measurableSet)
      intro α hα hcα hαV
      have hcψ : HasCompactSupport (Complex.ofRealCLM ∘ α) := hcα.comp_left rfl
      have hψsmooth : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ α) := by fun_prop
      let ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := hcψ.toSchwartzMap hψsmooth
      have hψV : tsupport ψ ⊆ V i ∩ V j :=
        (tsupport_comp_subset (g := Complex.ofRealCLM) rfl α).trans hαV
      have hi : Integrable (fun y ↦ (α y : ℂ) • f i y) :=
        integrable_product (f i) (V i) (hV i) (hf i).continuousOn ψ hcψ
          (hψV.trans Set.inter_subset_left)
      have hj : Integrable (fun y ↦ (α y : ℂ) • f j y) :=
        integrable_product (f j) (V j) (hV j) (hf j).continuousOn ψ hcψ
          (hψV.trans Set.inter_subset_right)
      have hpair : (∫ y, (α y : ℂ) • f i y) = ∫ y, (α y : ℂ) • f j y := by
        exact (hrepr i ψ hcψ (hψV.trans Set.inter_subset_left)).symm.trans
          (hrepr j ψ hcψ (hψV.trans Set.inter_subset_right))
      simpa only [Pi.sub_apply, smul_sub, ← Complex.coe_smul,
        integral_sub hi hj, sub_eq_zero] using hpair
    have hae : f i =ᵐ[volume.restrict (V i ∩ V j)] f j := by
      apply (ae_restrict_iff' hopen.measurableSet).mpr
      filter_upwards [hzero] with y hy hmem
      exact sub_eq_zero.mp (hy hmem)
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae hopen hfi hfj
  -- Choose the representative based at each point; overlap uniqueness makes this choice smooth.
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r) :=
    fun y ↦ if hy : y ∈ U then f ⟨y, hy⟩ y else 0
  have hgf (i : U) : Set.EqOn g (f i) (V i) := by
    intro y hy
    have hyU : y ∈ U := hVU i hy
    dsimp [g]
    rw [dite_eq_left hyU]
    exact agree ⟨y, hyU⟩ i ⟨hxV ⟨y, hyU⟩, hy⟩
  have hg : ContDiffOn ℝ ∞ g U := by
    apply hU.contDiffOn_iff.mpr
    intro y hy
    let i : U := ⟨y, hy⟩
    apply ((hf i).contDiffAt ((hV i).mem_nhds (hxV i))).congr_of_eventuallyEq
    exact Filter.eventually_of_mem ((hV i).mem_nhds (hxV i)) (fun z hz ↦ hgf i hz)
  refine ⟨g, hg, ?_⟩
  intro φ hφ hφU
  -- Decompose this compact test using a subordinate smooth partition of unity.
  have hcover : tsupport φ ⊆ ⋃ i : U, V i := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hφU hy⟩, hxV ⟨y, hφU hy⟩⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (isClosed_tsupport φ) V hV hcover
  have hfinite : {i : U | (Function.support (ρ i) ∩ tsupport φ).Nonempty}.Finite :=
    ρ.locallyFinite.finite_nonempty_inter_compact hφ
  let S : Finset U := hfinite.toFinset
  let ψ (i : U) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (hφ.smul_left (f := fun y ↦ ρ i y)).toSchwartzMap
      ((ρ i).contMDiff.contDiff.smul (φ.smooth ⊤))
  have hψcompact (i : U) : HasCompactSupport (ψ i) := hφ.smul_left
  have hψV (i : U) : tsupport (ψ i) ⊆ V i :=
    (tsupport_smul_subset_left (fun y ↦ ρ i y) φ).trans (hρ i)
  have hψU (i : U) : tsupport (ψ i) ⊆ U :=
    (hψV i).trans (hVU i)
  have hdecomp : φ = ∑ i ∈ S, ψ i := by
    ext y
    by_cases hy : φ y = 0
    · simp [ψ, hy]
    have hyφ : y ∈ tsupport φ := subset_tsupport φ hy
    have hsum : ∑ i ∈ S, ρ i y = 1 := by
      apply ρ.sum_finsupport' y hyφ
      intro i hi
      have hiρ : y ∈ Function.support (ρ i) := by
        simpa only [SmoothPartitionOfUnity.mem_finsupport, Function.mem_support] using hi
      exact hfinite.mem_toFinset.mpr ⟨y, hiρ, hyφ⟩
    simp only [sum_apply]
    change φ y = ∑ i ∈ S, ρ i y • φ y
    rw [← Finset.sum_smul, hsum, one_smul]
  -- Local distribution identities recombine into the original global pairing.
  calc
    u φ = ∑ i ∈ S, u (ψ i) := by rw [hdecomp, map_sum]
    _ = ∑ i ∈ S, ∫ y, ψ i y • g y := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrepr i (ψ i) (hψcompact i) (hψV i)]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change ψ i y • f i y = ψ i y • g y
      by_cases hy : ψ i y = 0
      · simp [hy]
      rw [hgf i (hψV i (subset_tsupport (ψ i) hy))]
    _ = ∫ y, ∑ i ∈ S, ψ i y • g y :=
      (integral_finsetSum S (fun i _ ↦
        integrable_product g U hU hg.continuousOn (ψ i) (hψcompact i) (hψU i))).symm
    _ = ∫ y, φ y • g y := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change (∑ i ∈ S, ψ i y • g y) = φ y • g y
      rw [← Finset.sum_smul]
      congr 1
      simpa only [sum_apply] using (DFunLike.congr_fun hdecomp y).symm

/-- Smoothness on U is detected by compact smooth cutoffs whose closed supports lie in U. -/
theorem isSmoothDistributionOn_iff_schwartz_cutoffs
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) :
    IsSmoothDistributionOn u U ↔
      ∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ U → ∃ v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
          TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin r))
            (fun x ↦ (χ x : ℂ)) u = (v : 𝓢'(_, _)) := by
  /- Stage 1: multiply a local representative by χ and extend by zero. Since
  tsupport χ lies inside U, this is globally smooth and compactly supported,
  hence Schwartz. On arbitrary Schwartz tests, χ times the test is compactly
  supported inside U, so the given local identity proves equality of distributions.
  Smooth compact χ has temperate growth, making mathlib's multiplier pointwise.
  Stage 2: near each point choose such a χ equal to one. The corresponding v
  represents u there. Glue the local representatives using overlap uniqueness. -/
  constructor
  · rintro ⟨f, hf, hrepr⟩ χ hχ hcχ hχU
    -- Multiplication by a cutoff kills the representative before reaching the boundary of U.
    have hχcomplex : ContDiff ℝ ∞ (fun y ↦ (χ y : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hχ
    have hcχcomplex : HasCompactSupport (fun y ↦ (χ y : ℂ)) :=
      hcχ.comp_left (g := Complex.ofRealCLM) rfl
    have hχgrowth : (fun y ↦ (χ y : ℂ)).HasTemperateGrowth :=
      hcχcomplex.hasTemperateGrowth hχcomplex
    have hvcompact : HasCompactSupport (fun y ↦ (χ y : ℂ) • f y) :=
      hcχcomplex.smul_right
    have hvsmooth : ContDiff ℝ ∞ (fun y ↦ (χ y : ℂ) • f y) := by
      apply contDiff_iff_contDiffAt.mpr
      intro y
      by_cases hy : y ∈ tsupport χ
      · exact hχcomplex.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hχU hy)))
      · apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r)))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy] with z hz
        simp [image_eq_zero_of_notMem_tsupport hz]
    let v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
      hvcompact.toSchwartzMap hvsmooth
    refine ⟨v, ?_⟩
    ext1 φ
    -- The multiplied Schwartz test is compactly supported inside U.
    let ψ := SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ)) φ
    have hψcompact : HasCompactSupport ψ := by
      change HasCompactSupport (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ)) φ)
      rw [SchwartzMap.smulLeftCLM_apply hχgrowth]
      simpa only [smul_eq_mul, Pi.mul_def] using
        (hcχcomplex.mul_right (f' := (φ : _ → ℂ)))
    have hψU : tsupport ψ ⊆ U := by
      exact ((SchwartzMap.tsupport_smulLeftCLM_subset _ φ).trans Set.inter_subset_right).trans
        ((tsupport_comp_subset (g := Complex.ofRealCLM) rfl χ).trans hχU)
    rw [TemperedDistribution.smulLeftCLM_apply_apply, hrepr ψ hψcompact hψU,
      SchwartzMap.coe_apply]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    change ψ y • f y = φ y • ((χ y : ℂ) • f y)
    rw [SchwartzMap.smulLeftCLM_apply_apply hχgrowth]
    simpa only [smul_eq_mul, mul_smul] using smul_comm (χ y : ℂ) (φ y) (f y)
  · intro hcutoff
    -- Around each point choose one compact bump equal to one on a smaller ball.
    apply (isSmoothDistributionOn_iff_disjoint_singularSupport u U hU).mpr
    apply Set.disjoint_left.mpr
    intro x hxU hxs
    obtain ⟨d, hd, hdU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hxU)
    let χ : ContDiffBump x :=
      { rIn := d / 2
        rOut := d
        rIn_pos := half_pos hd
        rIn_lt_rOut := half_lt_self hd }
    have hχU : tsupport χ ⊆ U := by
      rw [χ.tsupport_eq]
      exact hdU
    obtain ⟨v, hv⟩ := hcutoff χ χ.contDiff χ.hasCompactSupport hχU
    apply hxs
    refine ⟨Metric.ball x χ.rIn, Metric.isOpen_ball, Metric.mem_ball_self χ.rIn_pos,
      v, ?_, ?_⟩
    · exact (v.smooth ⊤).contDiffOn
    intro φ hφ hφball
    -- On these tests the multiplier is literally the identity; use the same v.
    have hχgrowth : (fun y ↦ (χ y : ℂ)).HasTemperateGrowth :=
      (χ.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp χ.contDiff)
    have hmult : SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ)) φ = φ := by
      ext y
      rw [SchwartzMap.smulLeftCLM_apply_apply hχgrowth]
      by_cases hy : φ y = 0
      · simp [hy]
      have hyball := hφball (subset_tsupport φ hy)
      rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hyball)]
      simp
    have hpair := congrArg
      (fun w : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) ↦ w φ) hv
    rw [TemperedDistribution.smulLeftCLM_apply_apply, hmult, SchwartzMap.coe_apply] at hpair
    exact hpair

/-- Membership in every real L² Sobolev order yields a globally smooth representative. -/
theorem isSmoothDistributionOn_of_forall_memSobolev
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (hu : ∀ s : ℝ, u.MemSobolev s 2) : IsSmoothDistributionOn u Set.univ := by
  /- For every nonnegative integer k choose s>n/2+k. The Bessel-coordinate
  characterization and Sobolev embedding give a C^k representative of u.
  These representatives agree pointwise, because continuous functions defining
  the same distribution agree. A single representative is consequently C^k for
  every k and therefore smooth. No uniform-in-k Sobolev bound is required. -/
  -- Sobolev embedding supplies a representative at each finite differentiability order.
  have exists_representative (k : ℕ) :
      ∃ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r),
        ContDiff ℝ k f ∧ ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          u φ = ∫ x, φ x • f x := by
    let s : ℝ := (n : ℝ) / 2 + k + 1
    obtain ⟨f, hf⟩ := (memSobolev_iff_exists_besselRealization s u).mp (hu s)
    obtain ⟨C, hC, hembed⟩ := sobolev_embedding n r k s (by dsimp [s]; linarith)
    obtain ⟨g, hg, hrepr, hbound⟩ := hembed f
    refine ⟨g, hg, ?_⟩
    intro φ
    rw [← hf]
    exact hrepr φ
  obtain ⟨g, hg, hrepr⟩ := exists_representative 0
  refine ⟨g, ?_, fun φ hφ hφU ↦ hrepr φ⟩
  -- Distributional uniqueness identifies every C^k representative with this fixed C^0 one.
  apply ContDiff.contDiffOn
  apply contDiff_infty.mpr
  intro k
  obtain ⟨f, hf, hfrepr⟩ := exists_representative k
  have hfg_ae : f =ᵐ[volume] g := by
    apply ae_eq_of_integral_contDiff_smul_eq hf.continuous.locallyIntegrable
      hg.continuous.locallyIntegrable
    intro φ hφ hcφ
    have hcomplex_support : HasCompactSupport (Complex.ofRealCLM ∘ φ) :=
      hcφ.comp_left rfl
    have hcomplex_smooth : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
    let ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
      hcomplex_support.toSchwartzMap hcomplex_smooth
    calc
      (∫ x, φ x • f x) = u ψ := by
        simpa [ψ, Function.comp_def] using (hfrepr ψ).symm
      _ = ∫ x, φ x • g x := by
        simpa [ψ, Function.comp_def] using hrepr ψ
  have hfg : f = g := MeasureTheory.Measure.eq_of_ae_eq hfg_ae hf.continuous hg.continuous
  rw [← hfg]
  exact hf

/-- A distribution supported in a closed set can have singularities only in that set. -/
theorem singularSupport_subset_of_isSupportedIn
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K) (hu : IsSupportedIn u K) :
    singularSupport u ⊆ K := by
  /- On the open complement of K choose the zero representative. Every compact
  test supported there has closed support disjoint from K, so the support
  hypothesis makes its pairing zero. This proves smoothness off K, not equality
  between the singular support and the support of the distribution. -/
  intro x hx
  by_contra hxK
  apply hx
  refine ⟨Kᶜ, hK.isOpen_compl, hxK, fun _ ↦ 0, contDiffOn_const, ?_⟩
  intro φ hφ hφK
  have hdisjoint : Disjoint (tsupport φ) K := by
    refine Set.disjoint_left.mpr ?_
    intro y hy hyK
    exact hφK hy hyK
  rw [hu.apply_eq_zero φ hφ hdisjoint]
  simp

end AtiyahSinger
