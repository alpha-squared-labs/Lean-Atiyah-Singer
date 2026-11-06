/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HomogeneousSymbolTopology
public import AtiyahSinger.Analysis.PseudodifferentialIndexStability

import AtiyahSinger.Analysis.SymbolCoordinateEstimates

/-!
# Continuous realization of homogeneous principal-symbol families

Public module ID: M0746.

A03/A08: the existing fixed cutoff formula is a continuous complex-linear lift
from punctured smooth homogeneous data to the weighted full-symbol topology.
Composing it with fixed quantization gives operator-norm continuity and the index
invariance of SG III.7.10--7.11 for these families. Both presentations stay fixed.

The finite-seminorm bound supplies the analytic bridge. Pointwise continuity,
a merely continuous cosphere homotopy, and smoothing such a homotopy into this
C-infinity topology are distinct questions; the latter use the separate relative-smoothing bridge.
The fixed regularization, its operator-norm continuity, and the resulting index
conclusions are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold Set
open scoped Manifold ContDiff Topology NNReal

set_option maxSynthPendingDepth 15

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

variable {E F}
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

attribute [local instance] homogeneousSymbolTopology globalSymbolTopology
  GlobalSymbolSeminormIndex.input_mem_atlas GlobalSymbolSeminormIndex.output_mem_atlas

namespace QuantizationPresentation

variable (R : QuantizationPresentation (n := n) (r := r) (q := q) E F) (m : ℝ)

/-- The existing finite cutoff, as a linear map on smooth homogeneous data. -/
def regularizationLinearMap :
    homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m →ₗ[ℂ]
      globalSymbolSpace (n := n) (r := r) (q := q) E F m where
  toFun := fun a ↦ R.regularizedSymbol m a.val a.property.1 a.property.2
  map_add' := fun a b ↦ Subtype.ext (R.regularizedSymbolFunction_add a.val b.val)
  map_smul' := fun z a ↦ Subtype.ext (R.regularizedSymbolFunction_smul z a.val)

set_option maxHeartbeats 1600000 in
-- The extended limit accommodates the finite derivative bounds in the punctured-symbol topology.
/-- Each target symbol seminorm is uniformly controlled by finitely many punctured seminorms. -/
theorem exists_regularization_seminorm_bound
    (J : GlobalSymbolSeminormIndex (n := n) (r := r) (q := q) E F) :
    ∃ (I : Finset (HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F))
      (K : ℝ≥0), ∀ a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m,
        globalSymbolSeminorm E F m J (R.regularizationLinearMap m a) ≤
          (K : ℝ) * (I.sup (homogeneousSymbolSeminorm E F m)) a := by
  /- Factor the specified regularization into one fixed scalar cutoff in the target chart.
  Compact overlap bounds give a uniform zero neighborhood and a uniform high-frequency plateau.
  On the intervening compact annulus, higher Leibniz estimates involve only finitely many
  original mixed derivatives. Outside it, differentiate homogeneity and compare the weights.
  Every compact set, derivative index and constant is fixed before the input symbol is chosen. -/
  classical
  have cutoffProperties (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f]
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hKU : K ⊆ symbolChartDomain E F c e f) :
      ∃ χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiffOn ℝ ∞ χ (symbolChartDomain E F c e f ×ˢ Set.univ) ∧
        (∀ a : GlobalSymbolFunction (n := n) E F, ∀ z η,
          globalSymbolInChart E F (A.regularizedSymbolFunction a) c e f z η =
            (χ (z, η) : ℂ) • globalSymbolInChart E F a c e f z η) ∧
        (∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ K, ∀ η, ‖η‖ ≤ ε → χ (z, η) = 0) ∧
        (∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ η, R ≤ ‖η‖ → χ (z, η) = 1) := by
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
    let χ (w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : ℝ :=
      ∑ j, (A.patch j).weight (c.symm w.1) *
        highFrequencyCutoff n (T (A.patch j).chart w.1 w.2)
    refine ⟨χ, ?_, ?_, ?_, ?_⟩
    · intro w hw
      have hbasecont : ContinuousAt (fun y : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin n) ↦ c.symm y.1) w :=
        (c.continuousOn_symm.continuousAt (c.open_target.mem_nhds hw.1.1.1)).comp
          continuousAt_fst
      have hterm (j : Fin A.size) :
          ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
            (A.patch j).weight (c.symm y.1) *
              highFrequencyCutoff n (T (A.patch j).chart y.1 y.2)) w := by
        let d := (A.patch j).chart
        have hd := (A.patch j).chart_mem_atlas
        by_cases hbase : c.symm w.1 ∈ P j
        · have hsource := hPsource j hbase
          have hcM := subset_maximalAtlas (I := I) (n := ∞) hc
          have hdM := subset_maximalAtlas (I := I) (n := ∞) hd
          have hforward : ContDiffAt ℝ ∞ (d ∘ c.symm) w.1 :=
            ((contMDiffAt_of_mem_maximalAtlas hdM hsource).comp w.1
              (contMDiffAt_symm_of_mem_maximalAtlas hcM hw.1.1.1)).contDiffAt
          have hweightSmooth := (A.patch j).input.smooth_cutoff.contDiffAt.comp w
            (hforward.comp w contDiffAt_fst)
          have hcutSmooth := contDiff_highFrequencyCutoff.contDiffAt.comp w
            (htransition d hd w.1 w.2 hw.1.1.1 hsource)
          apply (hweightSmooth.mul hcutSmooth).congr_of_eventuallyEq
          filter_upwards [hbasecont (d.open_source.mem_nhds hsource)] with y hy
          have hy' : c.symm y.1 ∈ (A.patch j).chart.source := hy
          rw [QuantizationPatch.weight, ite_eq_left hy']
          rfl
        · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
          filter_upwards [hbasecont ((hP j).isClosed.isOpen_compl.mem_nhds hbase)] with y hy
          have hzero : (A.patch j).weight (c.symm y.1) = 0 := by
            by_contra hne
            exact hy (hweight j (c.symm y.1) hne)
          simp only [hzero, zero_mul]
      exact (ContDiffAt.sum (s := Finset.univ) (fun j _ ↦ hterm j)).contDiffWithinAt
    · intro a z η
      ext v
      simp [globalSymbolInChart, QuantizationPresentation.regularizedSymbolFunction,
        χ, T, Complex.ofReal_sum, Finset.sum_smul]
    · have hbaseK : IsCompact (c.symm '' K) := hK.image_of_continuousOn
        (c.continuousOn_symm.mono (fun z hz ↦ (hKU hz).1.1))
      have hbaseKsource : c.symm '' K ⊆ c.source := by
        rintro x ⟨z, hz, rfl⟩
        exact c.map_target (hKU hz).1.1
      have hbound (j : Fin A.size) :
          ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, (A.patch j).weight (c.symm z) ≠ 0 →
            ∀ η, ‖T (A.patch j).chart z η‖ ≤ C * ‖η‖ := by
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
        let S := Q ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
        have hS : IsCompact S := hQ.prod (isCompact_sphere _ _)
        have hcontinuous : ContinuousOn (fun w ↦ T d w.1 w.2) S := by
          intro w hw
          exact (htransition d hd w.1 w.2 (hQtarget hw.1)
            (hQsource w.1 hw.1)).continuousAt.continuousWithinAt
        obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcontinuous
        refine ⟨max C 0, le_max_right _ _, ?_⟩
        intro z hz hw η
        by_cases hη : η = 0
        · have hzero : T d z 0 = 0 := by
            ext i
            change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) _ = 0
            exact inner_zero_left _
          rw [hη, hzero, norm_zero, mul_zero]
        · have hzQ : z ∈ Q :=
            ⟨c.symm z, ⟨⟨z, hz, rfl⟩, hweight j (c.symm z) hw⟩,
              c.right_inv (hKU hz).1.1⟩
          let v := ‖η‖⁻¹ • η
          have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
            simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hη
          have hscale : ‖η‖ • v = η := by
            simp [v, smul_smul, norm_ne_zero_iff.mpr hη]
          have hlinear (t : ℝ) : T d z (t • v) = t • T d z v := by
            ext i
            change inner ℝ (t • v) _ = t * inner ℝ v _
            exact real_inner_smul_left v _ t
          calc
            ‖T d z η‖ = ‖T d z (‖η‖ • v)‖ :=
              congrArg (fun ξ ↦ ‖T d z ξ‖) hscale.symm
            _ = ‖η‖ * ‖T d z v‖ := by
              rw [hlinear, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg η)]
            _ ≤ ‖η‖ * max C 0 :=
              mul_le_mul_of_nonneg_left ((hC (z, v) ⟨hzQ, hv⟩).trans
                (le_max_left _ _)) (norm_nonneg _)
            _ = _ := mul_comm _ _
      choose C hC hCb using hbound
      let D : ℝ := 1 + ∑ j, C j
      have hD : 0 < D := lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ ↦ hC j)))
      refine ⟨(2 * D)⁻¹, inv_pos.mpr (by positivity), ?_⟩
      intro z hz η hη
      apply Finset.sum_eq_zero
      intro j _
      by_cases hw : (A.patch j).weight (c.symm z) = 0
      · simp only [hw, zero_mul]
      · have hCD : C j ≤ D :=
          (Finset.single_le_sum (fun l _ ↦ hC l) (Finset.mem_univ j)).trans
            (le_add_of_nonneg_left zero_le_one)
        have hsmall : ‖T (A.patch j).chart z η‖ ≤ 1 / 2 := by
          calc
            _ ≤ C j * ‖η‖ := hCb j z hz hw η
            _ ≤ D * (2 * D)⁻¹ := mul_le_mul hCD hη (norm_nonneg _) hD.le
            _ = 1 / 2 := by field_simp
        rw [highFrequencyCutoff_eq_zero _ hsmall, mul_zero]
    · have hbaseK : IsCompact (c.symm '' K) := hK.image_of_continuousOn
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
      simp only [χ, hcut, A.sum_weight]
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
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let U := symbolChartDomain E F J.chart J.inputFrame J.outputFrame
  let K := J.localIndex.compactSet
  let i := J.localIndex.spatialOrder
  let j := J.localIndex.frequencyOrder
  let N := i + j
  let k := m - (j : ℝ)
  have hU : IsOpen U := isOpen_symbolChartDomain E F J.chart J.inputFrame J.outputFrame
  have hK : IsCompact K := J.localIndex.isCompact
  have hKU : K ⊆ U := J.localIndex.subset_domain
  -- The larger compact neighborhood makes both cutoff identities valid for all derivatives.
  obtain ⟨K', hK', hKK', hK'U⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ, hχ, hformula, ⟨ε₀, hε₀, hzero⟩, ⟨R₀, hR₀, hone⟩⟩ :=
    cutoffProperties R J.chart J.mem_atlas J.inputFrame J.outputFrame K' hK' hK'U
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
  let index (a b : ℕ) : HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F :=
    { toGlobalSymbolSeminormIndex :=
        { J with localIndex := { J.localIndex with spatialOrder := a, frequencyOrder := b } }
      frequencySet := W
      isCompact_frequencySet := hW
      frequency_ne_zero := hWne }
  let indices := ((Finset.range (N + 1)).product (Finset.range (N + 1))).image
    (fun ab : ℕ × ℕ ↦ index ab.1 ab.2)
  have boundSource (p : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
      (a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) (x ξ : X) (hx : x ∈ K) (hξ : ξ ∈ W) :
      ‖symbolDerivative (globalSymbolInChart E F p.val J.chart J.inputFrame J.outputFrame)
        a b x ξ‖ ≤ (indices.sup (homogeneousSymbolSeminorm E F m)) p := by
    have hmem : index a b ∈ indices := Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ha),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩, rfl⟩
    have hbound : ‖symbolDerivative
        (globalSymbolInChart E F p.val J.chart J.inputFrame J.outputFrame) a b x ξ‖ ≤
          homogeneousSymbolSeminorm E F m (index a b) p :=
      le_csSup (bddAbove_homogeneousSymbolSeminormValue_set E F m (index a b) p)
        ⟨x, hx, ξ, hξ, rfl⟩
    exact hbound.trans ((Finset.le_sup (f := homogeneousSymbolSeminorm E F m) hmem) p)
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
  have scaleDerivative (p : SymbolFunction n r q) (hp : IsHomogeneousSymbol U m p)
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
  let B := C * D + 2 ^ |k|
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hC hD) (by positivity)
  refine ⟨indices, ⟨B, hB⟩, ?_⟩
  intro p
  let S := (indices.sup (homogeneousSymbolSeminorm E F m)) p
  have hS : 0 ≤ S := apply_nonneg _ _
  let a := globalSymbolInChart E F p.val J.chart J.inputFrame J.outputFrame
  let b := globalSymbolInChart E F (R.regularizationLinearMap m p).val
    J.chart J.inputFrame J.outputFrame
  have hb (x ξ : X) : b x ξ = χ (x, ξ) • a x ξ := hformula p.val x ξ
  have ha : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ {ξ : X | ξ ≠ 0}) :=
    p.property.1 J.chart J.mem_atlas J.inputFrame J.outputFrame
  have hh : IsHomogeneousSymbol U m a :=
    p.property.2.in_chart J.chart J.mem_atlas J.inputFrame J.outputFrame
  change symbolSeminormValue _ m J.localIndex
    (globalSymbolInChartLinearMap E F m J (R.regularizationLinearMap m p)) ≤ B * S
  by_cases hnonempty : K.Nonempty
  swap
  · have hKzero : J.localIndex.compactSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [symbolSeminormValue, hKzero, Set.mem_empty_iff_false, false_and,
      exists_false, Set.ofPred_false, Real.sSup_empty]
    exact mul_nonneg hB hS
  obtain ⟨x₀, hx₀⟩ := hnonempty
  change sSup {t : ℝ | ∃ x ∈ K, ∃ ξ : X,
    t = ‖symbolDerivative b i j x ξ‖ / (1 + ‖ξ‖) ^ k} ≤ B * S
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
      _ ≤ (B * S) * (1 + ‖ξ‖) ^ k := by
        have hCD : 0 ≤ C * D := mul_nonneg hC hD
        dsimp only [B]
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
      _ ≤ B * S := by
        dsimp only [B]
        nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ |k| by positivity) hS]

/-- Fixed regularization is continuous for the two explicit derivative topologies. -/
theorem continuous_regularizationLinearMap :
    Continuous (R.regularizationLinearMap m) := by
  /- For each target seminorm use the preceding bound by a finite supremum of
  source seminorms. Apply the linear-map continuity criterion for the two displayed
  WithSeminorms structures. No choice varying with the input is made. -/
  apply WithSeminorms.continuous_of_isBounded
    (withSeminorms_homogeneousSymbolTopology E F m)
    (withSeminorms_globalSymbolTopology E F m)
  intro J
  obtain ⟨I, K, hbound⟩ := R.exists_regularization_seminorm_bound m J
  exact ⟨I, K, hbound⟩

/-- The concrete regularization formula with its continuity certificate. -/
def regularizationCLM :
    homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m →L[ℂ]
      globalSymbolSpace (n := n) (r := r) (q := q) E F m where
  toLinearMap := R.regularizationLinearMap m
  cont := R.continuous_regularizationLinearMap m

/-- A continuous family of homogeneous data has an explicit continuous full-symbol lift. -/
theorem continuous_regularizedSymbol {Z : Type*} [TopologicalSpace Z]
    (a : Z → homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : Continuous a) :
    Continuous (fun z ↦ R.regularizedSymbol m (a z).val (a z).property.1 (a z).property.2) := by
  /- Compose ha with regularizationCLM. Its underlying function is the previously
  defined cutoff symbol, so this constructs the required lift without a selection
  theorem. The parameter space need not be compact, smooth, or an interval. -/
  exact (R.regularizationCLM m).continuous.comp ha

variable [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : MeasureTheory.Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  (C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

include hM hT2 hE hF hSC hC hμ

/-- Fixed quantization of a smooth-topology homogeneous family is operator-norm continuous. -/
theorem continuous_sobolevQuantizeHomogeneous {Z : Type*} [TopologicalSpace Z]
    (a : Z → homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : Continuous a) (s : ℝ) :
    Continuous (fun z ↦
      (C.quantizeHomogeneous R μ m (a z).val
        (a z).property.1 (a z).property.2).sobolevExtension A B s) := by
  /- First lift a continuously with the fixed R regularization. Then apply
  continuous_sobolevQuantization for C and the fixed Sobolev presentations A,B.
  Unfold quantizeHomogeneous to identify the actual family. No ellipticity or
  uniform inverse bounds are needed to obtain continuity of these operators. -/
  exact (C.sobolevQuantizationCLM μ A B s m).continuous.comp
    (R.continuous_regularizedSymbol m a ha)

/-- Smooth convergence of homogeneous symbols gives convergence in the Sobolev operator norm. -/
theorem tendsto_sobolevQuantizeHomogeneous {Z : Type*} (l : Filter Z)
    (a : Z → homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : Tendsto a l (𝓝 b)) (s : ℝ) :
    Tendsto (fun z ↦
      (C.quantizeHomogeneous R μ m (a z).val
        (a z).property.1 (a z).property.2).sobolevExtension A B s) l
      (𝓝 ((C.quantizeHomogeneous R μ m b.val
        b.property.1 b.property.2).sobolevExtension A B s)) := by
  /- Compose filter convergence first with regularizationCLM and then with
  the existing sobolevQuantizationCLM. Their composite acts by the specified
  quantized operator, with fixed real orders m,s and fixed presentations. -/
  exact ((C.sobolevQuantizationCLM μ A B s m).continuous.comp
    (R.regularizationCLM m).continuous).continuousAt.tendsto.comp ha

include A B in
/-- SG III.7.10--7.11 for elliptic homogeneous paths in the punctured smooth topology. -/
theorem index_quantizeHomogeneous_eq_of_continuous
    (D : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (a : unitInterval → homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : Continuous a) (he : ∀ t, IsEllipticGlobalSymbol E F (a t).val) :
    (C.quantizeHomogeneous R μ m (a 0).val
      (a 0).property.1 (a 0).property.2).toLinearMap.index =
      (C.quantizeHomogeneous R μ m (a 1).val
        (a 1).property.1 (a 1).property.2).toLinearMap.index := by
  /- Lift the path by the fixed R regularization and apply the existing
  index_quantize_eq_of_homogeneous_principalSymbol_path theorem. Its inputs
  are the same punctured smooth symbols, ellipticity and explicit full-symbol
  path. That theorem supplies Fredholm index stability; no continuous choice
  of parametrices or parameter differentiability is assumed. -/
  exact C.index_quantize_eq_of_homogeneous_principalSymbol_path A B R D
    (fun t ↦ R.regularizedSymbol m (a t).val (a t).property.1 (a t).property.2)
    (R.continuous_regularizedSymbol m a ha) (fun t ↦ (a t).val)
    (fun t ↦ (a t).property.1) (fun t ↦ (a t).property.2) he (fun _ ↦ rfl)

end QuantizationPresentation

namespace PseudodifferentialOperator

variable [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : MeasureTheory.Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hE hF hSC hC hμ

/-- Elliptically homotopic homogeneous principal data identify the original endpoint indices. -/
theorem index_eq_of_continuous_homogeneous_principalSymbol
    (m : ℝ) (P Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (R C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (D : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (a : unitInterval → homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : Continuous a) (he : ∀ t, IsEllipticGlobalSymbol E F (a t).val)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m (a 0).val (a 0).property.1 (a 0).property.2))
    (hQ : Q.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m (a 1).val (a 1).property.1 (a 1).property.2)) :
    P.toLinearMap.index = Q.toLinearMap.index := by
  /- Compare P and Q separately with the fixed quantizations of the two endpoint
  symbols, using equality of their elliptic principal classes. The preceding path
  theorem equates the two quantized smooth indices. Transitivity gives the original
  endpoint indices. P and Q may have arbitrary lower-order and smoothing terms;
  no continuous operator family with these exact endpoints needs to be supplied. -/
  let L (t : unitInterval) := C.quantizeHomogeneous R μ m (a t).val
    (a t).property.1 (a t).property.2
  have hclass (t : unitInterval) : (L t).principalSymbol =
      globalPrincipalSymbolClass E F m
        (R.regularizedSymbol m (a t).val (a t).property.1 (a t).property.2) :=
    C.principalSymbol_quantizeHomogeneous R μ m (a t).val (a t).property.1 (a t).property.2
  -- Compare the exact original endpoints through their displayed principal classes.
  have hleft : P.toLinearMap.index = (L 0).toLinearMap.index :=
    P.index_eq_of_homogeneous_principalSymbol A B R D (a 0).val
      (a 0).property.1 (a 0).property.2 (he 0) hP (L 0) (hP.trans (hclass 0).symm)
  have hright : Q.toLinearMap.index = (L 1).toLinearMap.index :=
    Q.index_eq_of_homogeneous_principalSymbol A B R D (a 1).val
      (a 1).property.1 (a 1).property.2 (he 1) hQ (L 1) (hQ.trans (hclass 1).symm)
  -- The fixed homogeneous family gives the middle equality of actual smooth indices.
  exact hleft.trans ((R.index_quantizeHomogeneous_eq_of_continuous m μ C A B D a ha he).trans
    hright.symm)

end PseudodifferentialOperator

end AtiyahSinger
