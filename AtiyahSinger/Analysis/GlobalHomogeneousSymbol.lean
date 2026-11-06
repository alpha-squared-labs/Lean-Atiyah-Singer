/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalQuantization
public import AtiyahSinger.Analysis.HomogeneousCutoff
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Global representatives of homogeneous principal data

Public module ID: M0672.

Smoothness on the punctured cotangent bundle and positive real homogeneity
are standard conditions, kept separate. A fixed finite presentation supplies an
explicit sum of coordinate frequency cutoffs. It regularizes the zero section and
recovers the original data at high frequency locally uniformly in the base.

The principal class is independent of the regularization presentation and determines
the data off zero. These are the homogeneous realization steps behind SG III.13 (13.5).
No cotangent metric, cosphere-bundle model, general symbol topology, or full classical
expansion is introduced. The proofs retain the given finite presentation, including
its actual weights, cutoffs and original cotangent Hom values.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold Set
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 15


set_option linter.unusedSectionVars false

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- Smoothness of an actual cotangent Hom function on the complement of the zero section. -/
def IsSmoothOffZeroGlobalSymbol (a : GlobalSymbolFunction (n := n) E F) : Prop :=
  ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
          (π (EuclideanSpace ℂ (Fin r)) E))
        (f : Trivialization (EuclideanSpace ℂ (Fin q))
          (π (EuclideanSpace ℂ (Fin q)) F))
        [MemTrivializationAtlas e] [MemTrivializationAtlas f],
        ContDiffOn ℝ ∞ (Function.uncurry (globalSymbolInChart E F a c e f))
          (symbolChartDomain E F c e f ×ˢ {ξ | ξ ≠ 0})

/-- Positive real homogeneity on nonzero actual cotangent fibers, without a condition at zero. -/
def IsHomogeneousGlobalSymbol (m : ℝ) (a : GlobalSymbolFunction (n := n) E F) : Prop :=
  ∀ x : M, ∀ ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ,
    ξ ≠ 0 → ∀ t : ℝ, 0 < t → a x (t • ξ) = ((t ^ m : ℝ) : ℂ) • a x ξ

variable {E F} [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM in
/-- Intrinsic positive homogeneity has the same degree in every valid coordinate frame. -/
theorem IsHomogeneousGlobalSymbol.in_chart {m : ℝ}
    {a : GlobalSymbolFunction (n := n) E F} (ha : IsHomogeneousGlobalSymbol E F m a)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    IsHomogeneousSymbol (symbolChartDomain E F c e f) m (globalSymbolInChart E F a c e f) := by
  /- In the common valid domain, covectorFromChart is a real-linear isomorphism
  in the frequency variable and takes a nonzero frequency to a nonzero covector.
  Apply ha and pass the real scaling factor through the two complex-linear frame
  maps. The real and complex scalar actions on the Euclidean model agree. -/
  intro z hz η hη t ht
  -- The actual cotangent chart is real linear and injective at every valid base point.
  have hscale : covectorFromChart c (c.symm z) (t • η) =
      t • covectorFromChart c (c.symm z) η := by
    ext v
    change inner ℝ (t • η) (mfderiv _ _ c (c.symm z) v) =
      t * inner ℝ η (mfderiv _ _ c (c.symm z) v)
    exact real_inner_smul_left η _ t
  have hne : covectorFromChart c (c.symm z) η ≠ 0 := by
    intro hzero
    have hinv := covectorInChart_covectorFromChart c hc (c.symm z)
      (c.map_target hz.1.1) η
    rw [hzero] at hinv
    have hcoord : covectorInChart c (c.symm z) 0 = 0 := by
      ext i
      rfl
    exact hη (hinv.symm.trans hcoord)
  -- Both original complex-linear frames preserve the positive real scaling factor.
  ext v
  simp only [globalSymbolInChart, hscale, ha _ _ hne t ht,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_apply]
  simp only [← Complex.coe_smul]

namespace QuantizationPresentation

variable (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)

/-- An explicit finite gluing of frequency cutoffs applied to the actual global Hom data. -/
def regularizedSymbolFunction (a : GlobalSymbolFunction (n := n) E F) :
    GlobalSymbolFunction (n := n) E F :=
  fun x ξ ↦ ∑ j, (((A.patch j).weight x *
    highFrequencyCutoff n (covectorInChart (A.patch j).chart x ξ) : ℝ) : ℂ) • a x ξ

/-- The frequency cutoff forces the regularized representative to vanish on the zero section. -/
theorem regularizedSymbolFunction_zero_covector (a : GlobalSymbolFunction (n := n) E F) (x : M) :
    A.regularizedSymbolFunction a x 0 = 0 := by
  /- The coordinate vector of the zero covector is zero in every chart, even for
  the totalized formula. Each frequency cutoff is consequently zero. Sum the zero
  terms; no value of a on the zero section survives this construction. -/
  have hcoord (j : Fin A.size) : covectorInChart (A.patch j).chart x 0 = 0 := by
    ext i
    rfl
  -- Every cutoff vanishes at the same actual zero covector.
  simp only [regularizedSymbolFunction, hcoord,
    highFrequencyCutoff_eq_zero (0 : EuclideanSpace ℝ (Fin n)) (by norm_num),
    mul_zero, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero]

/-- Values assigned to homogeneous data on the zero section cannot affect the regularization. -/
theorem regularizedSymbolFunction_congr (a b : GlobalSymbolFunction (n := n) E F)
    (hab : ∀ x ξ, ξ ≠ 0 → a x ξ = b x ξ) :
    A.regularizedSymbolFunction a = A.regularizedSymbolFunction b := by
  /- At a nonzero covector substitute hab into each summand. At the zero covector
  both representatives vanish by the preceding theorem. Dependent function
  extensionality combines these pointwise identities into the displayed equality. -/
  funext x ξ
  by_cases hξ : ξ = 0
  · subst ξ
    rw [A.regularizedSymbolFunction_zero_covector, A.regularizedSymbolFunction_zero_covector]
  · -- Only the same original off-zero Hom values enter the finite formula.
    simp only [regularizedSymbolFunction, hab x ξ hξ]

/-- Keeping the presentation fixed makes regularization additive in the supplied data. -/
theorem regularizedSymbolFunction_add (a b : GlobalSymbolFunction (n := n) E F) :
    A.regularizedSymbolFunction (a + b) =
      A.regularizedSymbolFunction a + A.regularizedSymbolFunction b := by
  /- Each summand is multiplication by the same fixed complex scalar. Distribute
  it over the two Hom values and distribute the finite sum pointwise. No analytic
  assumptions or quotient comparison are needed for this exact identity. -/
  -- Distribute inside each original fiber, keeping all cutoff scalars fixed.
  funext x ξ
  simp only [regularizedSymbolFunction, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Regularization commutes with complex scalar multiplication of the original Hom values. -/
theorem regularizedSymbolFunction_smul (z : ℂ) (a : GlobalSymbolFunction (n := n) E F) :
    A.regularizedSymbolFunction (z • a) = z • A.regularizedSymbolFunction a := by
  /- The scalar z commutes with every real cutoff scalar in each complex Hom
  space. Move it through the finite sum. No conjugation or change of frequency occurs. -/
  -- Complex scalar multiplication commutes with the real cutoff factors.
  funext x ξ
  simp only [regularizedSymbolFunction, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ z _

variable [hT : T2Space M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT in
/-- Recovery at infinity is uniform on every compact subset of a valid coordinate domain. -/
theorem regularizedSymbolFunction_eq_inChart_at_high_frequency
    (a : GlobalSymbolFunction (n := n) E F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKU : K ⊆ symbolChartDomain E F c e f) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ η, R ≤ ‖η‖ →
      globalSymbolInChart E F (A.regularizedSymbolFunction a) c e f z η =
        globalSymbolInChart E F a c e f z η := by
  /- Stage 1: intersect the compact base set c.symm(K) with each compact input
  support. On this overlap the invertible coordinate covector transition has a
  uniformly bounded inverse. Thus sufficiently large c-frequencies have norm at
  least one in every patch contributing a nonzero weight. Take one positive bound
  for the finite family. Stage 2: every contributing cutoff is one above that bound;
  sum_weight gives the original Hom value. Transport it into the requested frames.
  No homogeneity or smoothness of a is needed for this pointwise recovery formula.
  The radius may depend on K and c; no global bound over an arbitrary chart is claimed. -/
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let T (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (z η : EuclideanSpace ℝ (Fin n)) :=
    covectorInChart d (c.symm z) (covectorFromChart c (c.symm z) η)
  have htransition (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (z η : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
      (hdz : c.symm z ∈ d.source) :
      ContDiffAt ℝ ∞ (Function.uncurry (T d)) (z, η) := by
    have hcM := subset_maximalAtlas (I := I) (n := ∞) hc
    have hdM := subset_maximalAtlas (I := I) (n := ∞) hd
    have hforward : ContDiffAt ℝ ∞ (d ∘ c.symm) z := by
      exact ((contMDiffAt_of_mem_maximalAtlas hdM hdz).comp z
        (contMDiffAt_symm_of_mem_maximalAtlas hcM hz)).contDiffAt
    have hinverse : ContDiffAt ℝ ∞ (c ∘ d.symm) (d (c.symm z)) := by
      have hbase : d.symm (d (c.symm z)) ∈ c.source := by
        rw [d.left_inv hdz]
        exact c.map_target hz
      exact ((contMDiffAt_of_mem_maximalAtlas hcM hbase).comp (d (c.symm z))
        (contMDiffAt_symm_of_mem_maximalAtlas hdM (d.map_source hdz))).contDiffAt
    have hderiv := (hinverse.fderiv_right (m := ∞) (by simp)).comp (z, η)
      (hforward.comp (z, η) contDiffAt_fst)
    apply contDiffAt_piLp'
    intro j
    have heval := hderiv.clm_apply (contDiffAt_const (c := EuclideanSpace.single j 1))
    have hscalar := contDiffAt_snd.inner ℝ heval
    apply hscalar.congr_of_eventuallyEq
    have hopen : IsOpen (c.target ∩ c.symm ⁻¹' d.source) :=
      c.continuousOn_symm.isOpen_inter_preimage c.open_target d.open_source
    filter_upwards [hopen.prod isOpen_univ |>.mem_nhds
      (show (z, η) ∈ (c.target ∩ c.symm ⁻¹' d.source) ×ˢ univ from ⟨⟨hz, hdz⟩, trivial⟩)]
      with p hp
    have hsource := hp.1.2
    have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) (d (c.symm p.1))
      (by
        simpa only [d.left_inv hsource] using
          (contMDiffAt_of_mem_maximalAtlas hcM (c.map_target hp.1.1)).mdifferentiableAt
            (by simp))
      ((contMDiffAt_symm_of_mem_maximalAtlas hdM (d.map_source hsource)).mdifferentiableAt
        (by simp))
    rw [mfderiv_eq_fderiv] at hcomp
    dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel] at hcomp
    rw [d.left_inv hsource] at hcomp
    change inner ℝ p.2 ((mfderiv I I c (c.symm p.1))
        ((mfderiv I I d.symm (d (c.symm p.1))) (EuclideanSpace.single j 1))) =
      inner ℝ p.2
        ((fderiv ℝ (c ∘ d.symm) (d (c.symm p.1))) (EuclideanSpace.single j 1))
    change fderiv ℝ (c ∘ d.symm) (d (c.symm p.1)) =
      (mfderiv I I c (c.symm p.1)).comp (mfderiv I I d.symm (d (c.symm p.1))) at hcomp
    rw [hcomp]
    rfl
  -- Each original patch has a fixed compact support wholly inside its own valid chart.
  let P (j : Fin A.size) := (A.patch j).chart.symm '' tsupport (A.patch j).input.cutoff
  have hP (j : Fin A.size) : IsCompact (P j) :=
    (A.patch j).input.compact_support.image_of_continuousOn
      ((A.patch j).chart.continuousOn_symm.mono
        (fun y hy ↦ ((A.patch j).input.support_subset hy).1))
  have hPsource (j : Fin A.size) : P j ⊆ (A.patch j).chart.source := by
    rintro x ⟨y, hy, rfl⟩
    exact (A.patch j).chart.map_target (((A.patch j).input.support_subset hy).1)
  have hweight (j : Fin A.size) (x : M) (hx : (A.patch j).weight x ≠ 0) : x ∈ P j := by
    have hsource : x ∈ (A.patch j).chart.source := by
      by_contra hout
      exact hx (by simp [QuantizationPatch.weight, hout])
    have hcut : (A.patch j).input.cutoff ((A.patch j).chart x) ≠ 0 := by
      simpa only [QuantizationPatch.weight, ite_eq_left hsource] using hx
    exact ⟨(A.patch j).chart x, subset_tsupport _ hcut,
      (A.patch j).chart.left_inv hsource⟩
  have hbaseK : IsCompact (c.symm '' K) := hK.image_of_continuousOn
    (c.continuousOn_symm.mono (fun z hz ↦ (hKU hz).1.1))
  have hbaseKsource : c.symm '' K ⊆ c.source := by
    rintro x ⟨z, hz, rfl⟩
    exact c.map_target (hKU hz).1.1
  -- On each compact overlap, invertibility gives a positive bound on the unit sphere.
  have hbound (j : Fin A.size) :
      ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, (A.patch j).weight (c.symm z) ≠ 0 →
        ∀ η, R ≤ ‖η‖ → 1 ≤ ‖T (A.patch j).chart z η‖ := by
    let d := (A.patch j).chart
    have hd := (A.patch j).chart_mem_atlas
    let Q := c '' ((c.symm '' K) ∩ P j)
    have hQ : IsCompact Q := (hbaseK.inter (hP j)).image_of_continuousOn
      (c.continuousOn.mono (fun x hx ↦ hbaseKsource hx.1))
    have hQtarget : Q ⊆ c.target := by
      rintro z ⟨x, hx, rfl⟩
      exact c.map_source (hbaseKsource hx.1)
    have hQsource : ∀ z ∈ Q, c.symm z ∈ d.source := by
      rintro z ⟨x, hx, rfl⟩
      rw [c.left_inv (hbaseKsource hx.1)]
      exact hPsource j hx.2
    have hnonzero (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Q)
        (η : EuclideanSpace ℝ (Fin n)) (hη : η ≠ 0) : T d z η ≠ 0 := by
      intro hzero
      have hinv := covectorFromChart_covectorInChart d hd (c.symm z) (hQsource z hz)
        (covectorFromChart c (c.symm z) η)
      have hd0 : covectorFromChart d (c.symm z) 0 = 0 := by
        ext v
        change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) ((mfderiv I I d (c.symm z)) v) = 0
        exact inner_zero_left _
      change covectorFromChart d (c.symm z) (T d z η) = _ at hinv
      rw [hzero, hd0] at hinv
      have hback := covectorInChart_covectorFromChart c hc (c.symm z)
        (c.map_target (hQtarget hz)) η
      rw [← hinv] at hback
      have hc0 : covectorInChart c (c.symm z) 0 = 0 := by
        ext i
        rfl
      exact hη (hback.symm.trans hc0)
    let S := Q ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
    have hS : IsCompact S := hQ.prod (isCompact_sphere _ _)
    have hcontinuous : ContinuousOn (fun w ↦ ‖T d w.1 w.2‖) S := by
      intro w hw
      exact ((htransition d hd w.1 w.2 (hQtarget hw.1)
        (hQsource w.1 hw.1)).continuousAt.norm).continuousWithinAt
    obtain ⟨b, hb, hlow⟩ := hS.exists_forall_le' hcontinuous (a := 0) (by
      intro w hw
      apply norm_pos_iff.mpr
      apply hnonzero w.1 hw.1
      intro hzero
      simpa only [hzero, Metric.mem_sphere, dist_self, zero_ne_one] using hw.2)
    refine ⟨b⁻¹, inv_pos.mpr hb, ?_⟩
    intro z hz hw η hη
    have hzQ : z ∈ Q :=
      ⟨c.symm z, ⟨⟨z, hz, rfl⟩, hweight j (c.symm z) hw⟩, c.right_inv (hKU hz).1.1⟩
    have hηpos : 0 < ‖η‖ := lt_of_lt_of_le (inv_pos.mpr hb) hη
    have hηne := norm_pos_iff.mp hηpos
    let v := ‖η‖⁻¹ • η
    have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hηne
    have hscale : ‖η‖ • v = η := by
      simp [v, smul_smul, norm_ne_zero_iff.mpr hηne]
    have hlinear (t : ℝ) : T d z (t • v) = t • T d z v := by
      ext i
      change inner ℝ (t • v) _ = t * inner ℝ v _
      exact real_inner_smul_left v _ t
    have hnorm : ‖T d z η‖ = ‖η‖ * ‖T d z v‖ := by
      calc
        ‖T d z η‖ = ‖T d z (‖η‖ • v)‖ :=
          congrArg (fun ξ ↦ ‖T d z ξ‖) hscale.symm
        _ = ‖η‖ * ‖T d z v‖ := by
          rw [hlinear, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg η)]
    rw [hnorm]
    have hone : 1 ≤ ‖η‖ * b := by
      have h := mul_le_mul_of_nonneg_right hη hb.le
      rw [inv_mul_cancel₀ hb.ne'] at h
      exact h
    exact hone.trans (mul_le_mul_of_nonneg_left (hlow (z, v) ⟨hzQ, hv⟩) (norm_nonneg η))
  choose R hR hRbound using hbound
  let radius : ℝ := 1 + ∑ j, max 0 (R j)
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  refine ⟨radius, hradius, ?_⟩
  intro z hz η hη
  -- One radius works for every nonzero-weight summand of the same original partition.
  have hcut (j : Fin A.size) :
      (A.patch j).weight (c.symm z) *
        highFrequencyCutoff n (T (A.patch j).chart z η) = (A.patch j).weight (c.symm z) := by
    by_cases hw : (A.patch j).weight (c.symm z) = 0
    · simp only [hw, zero_mul]
    · have hRle : R j ≤ radius := by
        have hsum : max 0 (R j) ≤ ∑ l, max 0 (R l) :=
          Finset.single_le_sum (fun l _ ↦ le_max_left 0 (R l)) (Finset.mem_univ j)
        exact (le_max_right 0 (R j)).trans (hsum.trans (by dsimp [radius]; linarith))
      rw [highFrequencyCutoff_eq_one _ (hRbound j z hz hw η (hRle.trans hη)), mul_one]
  have hraw : A.regularizedSymbolFunction a (c.symm z) (covectorFromChart c (c.symm z) η) =
      a (c.symm z) (covectorFromChart c (c.symm z) η) := by
    change (∑ j, (((A.patch j).weight (c.symm z) *
      highFrequencyCutoff n (T (A.patch j).chart z η) : ℝ) : ℂ) •
        a (c.symm z) (covectorFromChart c (c.symm z) η)) = _
    simp only [hcut, ← Finset.sum_smul, ← Complex.ofReal_sum, A.sum_weight,
      Complex.ofReal_one, one_smul]
  -- Apply the same two frame maps to this equality of actual cotangent Hom values.
  simp only [globalSymbolInChart, hraw]

set_option maxHeartbeats 1000000 in
-- The all-chart argument combines smooth chart transitions and finite cutoff localizations.
include hM hT hE hF in
/-- The finite cutoff formula converts punctured homogeneous data into an order-m global symbol. -/
theorem isGlobalSymbol_regularizedSymbolFunction (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F m (A.regularizedSymbolFunction a) := by
  /- Stage 1: in every requested chart, differentiate the actual cotangent chart
  transitions. Each original weighted cutoff summand is smooth away from zero;
  it vanishes near zero frequency and outside its compact patch support. Summing
  therefore gives full smoothness, regardless of the original zero-section values.
  Stage 2: enlarge each spatial compact set inside the chart domain. High-frequency
  recovery makes the difference from the standard homogeneous cutoff have bounded
  frequency support on this neighborhood. The existing smoothing estimate controls
  all mixed derivatives of that difference at order m. Adding the standard cutoff
  supplies every required estimate in the original chart and frames. -/
  classical
  intro c hc e f _ _
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let V := symbolChartDomain E F c e f
  let p := globalSymbolInChart E F a c e f
  let T (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (z η : EuclideanSpace ℝ (Fin n)) :=
    covectorInChart d (c.symm z) (covectorFromChart c (c.symm z) η)
  have hV : IsOpen V := isOpen_symbolChartDomain E F c e f
  have htransition (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (z η : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
      (hdz : c.symm z ∈ d.source) :
      ContDiffAt ℝ ∞ (Function.uncurry (T d)) (z, η) := by
    have hcM := subset_maximalAtlas (I := I) (n := ∞) hc
    have hdM := subset_maximalAtlas (I := I) (n := ∞) hd
    have hforward : ContDiffAt ℝ ∞ (d ∘ c.symm) z := by
      exact ((contMDiffAt_of_mem_maximalAtlas hdM hdz).comp z
        (contMDiffAt_symm_of_mem_maximalAtlas hcM hz)).contDiffAt
    have hinverse : ContDiffAt ℝ ∞ (c ∘ d.symm) (d (c.symm z)) := by
      have hbase : d.symm (d (c.symm z)) ∈ c.source := by
        rw [d.left_inv hdz]
        exact c.map_target hz
      exact ((contMDiffAt_of_mem_maximalAtlas hcM hbase).comp (d (c.symm z))
        (contMDiffAt_symm_of_mem_maximalAtlas hdM (d.map_source hdz))).contDiffAt
    have hderiv := (hinverse.fderiv_right (m := ∞) (by simp)).comp (z, η)
      (hforward.comp (z, η) contDiffAt_fst)
    apply contDiffAt_piLp'
    intro j
    have heval := hderiv.clm_apply (contDiffAt_const (c := EuclideanSpace.single j 1))
    have hscalar := contDiffAt_snd.inner ℝ heval
    apply hscalar.congr_of_eventuallyEq
    have hopen : IsOpen (c.target ∩ c.symm ⁻¹' d.source) :=
      c.continuousOn_symm.isOpen_inter_preimage c.open_target d.open_source
    filter_upwards [hopen.prod isOpen_univ |>.mem_nhds
      (show (z, η) ∈ (c.target ∩ c.symm ⁻¹' d.source) ×ˢ univ from ⟨⟨hz, hdz⟩, trivial⟩)]
      with p hp
    have hsource := hp.1.2
    have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) (d (c.symm p.1))
      (by
        simpa only [d.left_inv hsource] using
          (contMDiffAt_of_mem_maximalAtlas hcM (c.map_target hp.1.1)).mdifferentiableAt
            (by simp))
      ((contMDiffAt_symm_of_mem_maximalAtlas hdM (d.map_source hsource)).mdifferentiableAt
        (by simp))
    rw [mfderiv_eq_fderiv] at hcomp
    dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel] at hcomp
    rw [d.left_inv hsource] at hcomp
    change inner ℝ p.2 ((mfderiv I I c (c.symm p.1))
        ((mfderiv I I d.symm (d (c.symm p.1))) (EuclideanSpace.single j 1))) =
      inner ℝ p.2
        ((fderiv ℝ (c ∘ d.symm) (d (c.symm p.1))) (EuclideanSpace.single j 1))
    change fderiv ℝ (c ∘ d.symm) (d (c.symm p.1)) =
      (mfderiv I I c (c.symm p.1)).comp (mfderiv I I d.symm (d (c.symm p.1))) at hcomp
    rw [hcomp]
    rfl
  let P (j : Fin A.size) := (A.patch j).chart.symm '' tsupport (A.patch j).input.cutoff
  have hP (j : Fin A.size) : IsCompact (P j) :=
    (A.patch j).input.compact_support.image_of_continuousOn
      ((A.patch j).chart.continuousOn_symm.mono
        (fun y hy ↦ ((A.patch j).input.support_subset hy).1))
  have hPsource (j : Fin A.size) : P j ⊆ (A.patch j).chart.source := by
    rintro x ⟨y, hy, rfl⟩
    exact (A.patch j).chart.map_target (((A.patch j).input.support_subset hy).1)
  have hweight (j : Fin A.size) (x : M) (hx : (A.patch j).weight x ≠ 0) : x ∈ P j := by
    have hsource : x ∈ (A.patch j).chart.source := by
      by_contra hout
      exact hx (by simp [QuantizationPatch.weight, hout])
    have hcut : (A.patch j).input.cutoff ((A.patch j).chart x) ≠ 0 := by
      simpa only [QuantizationPatch.weight, ite_eq_left hsource] using hx
    exact ⟨(A.patch j).chart x, subset_tsupport _ hcut,
      (A.patch j).chart.left_inv hsource⟩
  have hcoord : globalSymbolInChart E F (A.regularizedSymbolFunction a) c e f =
      fun z η ↦ ∑ j, (((A.patch j).weight (c.symm z) *
        highFrequencyCutoff n (T (A.patch j).chart z η) : ℝ) : ℂ) • p z η := by
    ext z η v
    simp [globalSymbolInChart, regularizedSymbolFunction, p, T]
  -- Prove actual smoothness in every original chart, including its zero covectors.
  have hreg : ContDiffOn ℝ ∞
      (Function.uncurry (globalSymbolInChart E F (A.regularizedSymbolFunction a) c e f))
      (V ×ˢ univ) := by
    rw [hcoord]
    intro w hw
    have hbasecont : ContinuousAt (fun y : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) ↦ c.symm y.1) w :=
      (c.continuousOn_symm.continuousAt (c.open_target.mem_nhds hw.1.1.1)).comp
        continuousAt_fst
    have hterm (j : Fin A.size) :
        ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          (((A.patch j).weight (c.symm y.1) *
            highFrequencyCutoff n (T (A.patch j).chart y.1 y.2) : ℝ) : ℂ) • p y.1 y.2) w := by
      let d := (A.patch j).chart
      have hd := (A.patch j).chart_mem_atlas
      by_cases hbase : c.symm w.1 ∈ P j
      · have hsource := hPsource j hbase
        by_cases hη : w.2 = 0
        · -- Near zero, this original patch cutoff kills even arbitrary zero-section values.
          have hzero : T d w.1 w.2 = 0 := by
            rw [hη]
            ext i
            change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) _ = 0
            exact inner_zero_left _
          have hsmall : ∀ᶠ y in 𝓝 w, ‖T d y.1 y.2‖ < 1 / 2 :=
            (htransition d hd w.1 w.2 hw.1.1.1 hsource).continuousAt.norm
              (Iio_mem_nhds (by
                change ‖T d w.1 w.2‖ < (1 / 2 : ℝ)
                rw [hzero]
                norm_num))
          apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r) →L[ℂ]
            EuclideanSpace ℂ (Fin q)))).congr_of_eventuallyEq
          filter_upwards [hsmall] with y hy
          change (((A.patch j).weight (c.symm y.1) *
            highFrequencyCutoff n (T d y.1 y.2) : ℝ) : ℂ) • p y.1 y.2 = 0
          rw [highFrequencyCutoff_eq_zero _ hy.le]
          simp only [mul_zero, Complex.ofReal_zero, zero_smul]
        · -- Away from zero, use the smooth original symbol and the same two chart derivatives.
          have hcM := subset_maximalAtlas (I := I) (n := ∞) hc
          have hdM := subset_maximalAtlas (I := I) (n := ∞) hd
          have hforward : ContDiffAt ℝ ∞ (d ∘ c.symm) w.1 :=
            ((contMDiffAt_of_mem_maximalAtlas hdM hsource).comp w.1
              (contMDiffAt_symm_of_mem_maximalAtlas hcM hw.1.1.1)).contDiffAt
          have hweightSmooth := (A.patch j).input.smooth_cutoff.contDiffAt.comp w
            (hforward.comp w contDiffAt_fst)
          have hcutSmooth := contDiff_highFrequencyCutoff.contDiffAt.comp w
            (htransition d hd w.1 w.2 hw.1.1.1 hsource)
          have hfactor := Complex.ofRealCLM.contDiff.contDiffAt.comp w
            (hweightSmooth.mul hcutSmooth)
          have hp : ContDiffAt ℝ ∞ (Function.uncurry p) w :=
            (hs c hc e f).contDiffAt ((hV.prod isOpen_ne).mem_nhds ⟨hw.1, hη⟩)
          apply (hfactor.smul hp).congr_of_eventuallyEq
          filter_upwards [hbasecont (d.open_source.mem_nhds hsource)] with y hy
          change (((A.patch j).weight (c.symm y.1) *
            highFrequencyCutoff n (T d y.1 y.2) : ℝ) : ℂ) • p y.1 y.2 =
            (((A.patch j).input.cutoff (d (c.symm y.1)) *
              highFrequencyCutoff n (T d y.1 y.2) : ℝ) : ℂ) • p y.1 y.2
          have hy' : c.symm y.1 ∈ (A.patch j).chart.source := hy
          rw [QuantizationPatch.weight, ite_eq_left hy']
      · -- Across a patch boundary the fixed compact support leaves a genuine zero neighborhood.
        apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r) →L[ℂ]
          EuclideanSpace ℂ (Fin q)))).congr_of_eventuallyEq
        filter_upwards [hbasecont ((hP j).isClosed.isOpen_compl.mem_nhds hbase)] with y hy
        have hzero : (A.patch j).weight (c.symm y.1) = 0 := by
          by_contra hne
          exact hy (hweight j (c.symm y.1) hne)
        simp only [hzero, zero_mul, Complex.ofReal_zero, zero_smul]
    change ContDiffWithinAt ℝ ∞ (fun y ↦ ∑ j,
      (((A.patch j).weight (c.symm y.1) *
        highFrequencyCutoff n (T (A.patch j).chart y.1 y.2) : ℝ) : ℂ) • p y.1 y.2)
      (V ×ˢ univ) w
    exact (ContDiffAt.sum (s := Finset.univ) (fun j _ ↦ hterm j)).contDiffWithinAt
  -- On an enlarged compact neighborhood the deviation from the standard cutoff has bounded
  -- frequency support. The existing smoothing estimate controls every mixed derivative.
  refine ⟨hreg, ?_⟩
  intro K hKV hK α β
  obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
  have hint : interior K' ⊆ V := interior_subset.trans hK'V
  obtain ⟨R, hR, hrecovery⟩ :=
    A.regularizedSymbolFunction_eq_inChart_at_high_frequency a c hc e f K' hK' hK'V
  have hstandard := isSymbol_frequencyCutoffSymbol V hV m p (hs c hc e f)
    (hh.in_chart c hc e f)
  let d := globalSymbolInChart E F (A.regularizedSymbolFunction a) c e f - frequencyCutoffSymbol p
  have hd : ContDiffOn ℝ ∞ (Function.uncurry d) (interior K' ×ˢ univ) :=
    (hreg.mono (Set.prod_mono hint subset_rfl)).sub
      (hstandard.1.mono (Set.prod_mono hint subset_rfl))
  have hsupp : ∀ z ∈ interior K', ∀ η, max R 1 ≤ ‖η‖ → d z η = 0 := by
    intro z hz η hη
    change globalSymbolInChart E F (A.regularizedSymbolFunction a) c e f z η -
      frequencyCutoffSymbol p z η = 0
    rw [hrecovery z (interior_subset hz) η ((le_max_left _ _).trans hη),
      frequencyCutoffSymbol_eq_of_one_le_norm p z η ((le_max_right _ _).trans hη)]
    exact sub_self _
  have hdSymbol := isSmoothingSymbol_of_frequency_support isOpen_interior d (max R 1) hd hsupp m
  have hstandardLocal : IsSymbol (interior K') m (frequencyCutoffSymbol p) := by
    refine ⟨hstandard.1.mono (Set.prod_mono hint subset_rfl), ?_⟩
    intro C hC hcompact i j
    exact hstandard.2 C (hC.trans hint) hcompact i j
  have hsum := hdSymbol.add isOpen_interior hstandardLocal
  have heq : d + frequencyCutoffSymbol p =
      globalSymbolInChart E F (A.regularizedSymbolFunction a) c e f :=
    sub_add_cancel _ _
  rw [heq] at hsum
  exact hsum.2 K hKK' hK α β

/-- The constructed global symbol, with its order property recorded separately. -/
def regularizedSymbol (m : ℝ) (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) :
    globalSymbolSpace (n := n) (r := r) (q := q) E F m :=
  ⟨A.regularizedSymbolFunction a, A.isGlobalSymbol_regularizedSymbolFunction m a hs hh⟩


include hM hT hE hF in
/-- Changing the regularization presentation changes the symbol by every lower order. -/
theorem isGlobalSymbol_sub_regularizedSymbolFunction
    (B : QuantizationPresentation (n := n) (r := r) (q := q) E F) (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (l : ℝ) :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F l
      (A.regularizedSymbolFunction a - B.regularizedSymbolFunction a) := by
  /- Both terms are globally smooth symbols. On each compact coordinate set the
  two high-frequency recovery statements make their difference zero above a common
  radius. To control spatial derivatives, first enlarge the compact set inside the
  open chart domain. On its neighborhood the difference has bounded frequency support.
  All mixed derivatives are bounded on the resulting compact product, and the bounded
  frequency weights can absorb any real order l. Quantify over all charts and l. -/
  classical
  intro c hc e f _ _
  let V := symbolChartDomain E F c e f
  let pa := globalSymbolInChart E F (A.regularizedSymbolFunction a) c e f
  let pb := globalSymbolInChart E F (B.regularizedSymbolFunction a) c e f
  have hV : IsOpen V := isOpen_symbolChartDomain E F c e f
  have hsub : globalSymbolInChart E F
      (A.regularizedSymbolFunction a - B.regularizedSymbolFunction a) c e f = pa - pb := by
    ext z η v
    simp [globalSymbolInChart, pa, pb]
  rw [hsub]
  have ha := A.isGlobalSymbol_regularizedSymbolFunction m a hs hh c hc e f
  have hb := B.isGlobalSymbol_regularizedSymbolFunction m a hs hh c hc e f
  have hd : ContDiffOn ℝ ∞ (Function.uncurry (pa - pb)) (V ×ˢ univ) := ha.1.sub hb.1
  refine ⟨hd, ?_⟩
  intro K hKV hK α β
  -- Enlarge the compact set first, so frequency agreement also controls spatial derivatives.
  obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
  have hint : interior K' ⊆ V := interior_subset.trans hK'V
  obtain ⟨RA, hRA, hrecoverA⟩ :=
    A.regularizedSymbolFunction_eq_inChart_at_high_frequency a c hc e f K' hK' hK'V
  obtain ⟨RB, hRB, hrecoverB⟩ :=
    B.regularizedSymbolFunction_eq_inChart_at_high_frequency a c hc e f K' hK' hK'V
  have hsupp : ∀ z ∈ interior K', ∀ η, max RA RB ≤ ‖η‖ → (pa - pb) z η = 0 := by
    intro z hz η hη
    change globalSymbolInChart E F (A.regularizedSymbolFunction a) c e f z η -
      globalSymbolInChart E F (B.regularizedSymbolFunction a) c e f z η = 0
    rw [hrecoverA z (interior_subset hz) η ((le_max_left _ _).trans hη),
      hrecoverB z (interior_subset hz) η ((le_max_right _ _).trans hη), sub_self]
  -- A smooth function with this local finite frequency support has every real symbol order.
  have hlocal := isSmoothingSymbol_of_frequency_support isOpen_interior (pa - pb) (max RA RB)
    (hd.mono (Set.prod_mono hint subset_rfl)) hsupp l
  exact hlocal.2 K hKK' hK α β

/-- The common principal class identifies homogeneous data exactly off the zero section. -/
theorem regularizedSymbol_class_eq_iff
    (B : QuantizationPresentation (n := n) (r := r) (q := q) E F) (m : ℝ)
    (a b : GlobalSymbolFunction (n := n) E F)
    (has : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hah : IsHomogeneousGlobalSymbol E F m a)
    (hbs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F b)
    (hbh : IsHomogeneousGlobalSymbol E F m b) :
    globalPrincipalSymbolClass E F m (A.regularizedSymbol m a has hah) =
        globalPrincipalSymbolClass E F m (B.regularizedSymbol m b hbs hbh) ↔
      ∀ x ξ, ξ ≠ 0 → a x ξ = b x ξ := by
  /- Forward: select a common chart and valid frames at x. The quotient equality
  gives an order-(m-1) estimate for the representative difference. High-frequency
  recovery on the singleton coordinate set identifies its values on large t*ξ with
  t^m times a(x,ξ)-b(x,ξ). Divide by t^m and let t tend to infinity; the one-order
  gain forces the difference to vanish for every real m. Reverse: regularization_congr
  removes any discrepancy at zero; the preceding all-order difference theorem gives
  equal principal classes for the two presentations. Nothing is asserted at ξ=0. -/
  classical
  have hrestrict {U V : Set (EuclideanSpace ℝ (Fin n))} {l : ℝ}
      {p : SymbolFunction n r q} (hp : IsSymbol U l p) (hVU : V ⊆ U) : IsSymbol V l p :=
    ⟨hp.1.mono (Set.prod_mono hVU subset_rfl),
      fun K hK hc i j ↦ hp.2 K (hK.trans hVU) hc i j⟩
  constructor
  · intro hclass x ξ hξ
    -- Select one actual chart and the two original bundle frames at this same base point.
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hc := chart_mem_atlas (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    have hf : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
    let V := symbolChartDomain E F c e f
    have hV : IsOpen V := isOpen_symbolChartDomain E F c e f
    have hz : c x ∈ V :=
      ⟨⟨c.map_source hx, by simpa only [Set.mem_preimage, c.left_inv hx] using he⟩,
        by simpa only [Set.mem_preimage, c.left_inv hx] using hf⟩
    obtain ⟨K, hK, hzK, hKV⟩ := exists_compact_subset hV hz
    have hint : interior K ⊆ V := interior_subset.trans hKV
    obtain ⟨RA, hRA, hrecoverA⟩ :=
      A.regularizedSymbolFunction_eq_inChart_at_high_frequency a c hc e f K hK hKV
    obtain ⟨RB, hRB, hrecoverB⟩ :=
      B.regularizedSymbolFunction_eq_inChart_at_high_frequency b c hc e f K hK hKV
    let pa : symbolSpace (interior K) isOpen_interior m r q :=
      ⟨globalSymbolInChart E F (A.regularizedSymbolFunction a) c e f,
        hrestrict (A.isGlobalSymbol_regularizedSymbolFunction m a has hah c hc e f) hint⟩
    let pb : symbolSpace (interior K) isOpen_interior m r q :=
      ⟨globalSymbolInChart E F (B.regularizedSymbolFunction b) c e f,
        hrestrict (B.isGlobalSymbol_regularizedSymbolFunction m b hbs hbh c hc e f) hint⟩
    have hdiffGlobal := (globalPrincipalSymbolClass_eq_iff E F m _ _).mp hclass
    have hdiff := hdiffGlobal c hc e f
    have hsub : globalSymbolInChart E F
        ((A.regularizedSymbol m a has hah).val - (B.regularizedSymbol m b hbs hbh).val)
        c e f = pa.val - pb.val := by
      ext z η v
      simp [globalSymbolInChart, regularizedSymbol, pa, pb]
    rw [hsub] at hdiff
    have hlocalclass := (principalSymbolClass_eq_iff isOpen_interior pa pb).mpr
      (hrestrict hdiff hint)
    have hη : covectorInChart c x ξ ≠ 0 := by
      intro hzero
      have hinv := covectorFromChart_covectorInChart c hc x hx ξ
      rw [hzero] at hinv
      have hc0 : covectorFromChart c x 0 = 0 := by
        ext v
        change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) _ = 0
        exact inner_zero_left _
      exact hξ (hinv.symm.trans hc0)
    -- The local uniqueness theorem uses the one-order gain on positive rays.
    have hmap := homogeneous_eq_of_principalSymbolClass_eq isOpen_interior pa pb
      (globalSymbolInChart E F a c e f) (globalSymbolInChart E F b c e f)
      (fun z hz ↦ hah.in_chart c hc e f z (hint hz))
      (fun z hz ↦ hbh.in_chart c hc e f z (hint hz))
      (max RA RB) (lt_of_lt_of_le hRA (le_max_left _ _))
      (fun z hz η hη ↦ hrecoverA z (interior_subset hz) η ((le_max_left _ _).trans hη))
      (fun z hz η hη ↦ hrecoverB z (interior_subset hz) η ((le_max_right _ _).trans hη))
      hlocalclass (c x) hzK (covectorInChart c x ξ) hη
    rw [globalSymbolInChart_covectorInChart E F a c hc e f x hx ξ,
      globalSymbolInChart_covectorInChart E F b c hc e f x hx ξ] at hmap
    -- Undo exactly the frames selected above, retaining the actual original fiber maps.
    ext v
    have htest := congrArg
      (fun L : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) ↦
        f.symmL ℂ x (L (e.continuousLinearMapAt ℂ x v))) hmap
    simpa only [ContinuousLinearMap.comp_apply, e.symmL_continuousLinearMapAt he,
      f.symmL_continuousLinearMapAt hf] using htest
  · intro hab
    -- Values at zero do not affect regularization; changing only the presentation is smoothing.
    apply (globalPrincipalSymbolClass_eq_iff E F m _ _).mpr
    change IsGlobalSymbol E F (m - 1)
      (A.regularizedSymbolFunction a - B.regularizedSymbolFunction b)
    rw [← B.regularizedSymbolFunction_congr a b hab]
    exact A.isGlobalSymbol_sub_regularizedSymbolFunction B m a has hah (m - 1)

end QuantizationPresentation

end AtiyahSinger
