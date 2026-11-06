/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricPseudodifferentialAdjoint
public import AtiyahSinger.Analysis.SmoothSectionMultiplication

/-!
# Two-sided cutoff of actual bundle section operators

Public module ID: M0955.

UL03: the standard sandwich by one real smooth scalar cutoff. The section-map
construction and its two support conditions require no compact base. The PDO
membership and adjoint comparisons use the existing compact-base PDO model.
Sources: SG III.3.8, III.3.11 and III.13.4; these global bundle formulations are
project supplements to the book's local calculus and excision argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

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

/-- The actual operator u ↦ χ · R(χ · u), with the same real cutoff on both bundles. -/
def twoSidedSectionCutoff
    (R : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ) :
    smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F :=
  (smoothSectionMul F (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)).comp
    (R.comp (smoothSectionMul E (fun x ↦ (χ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hχ)))

/-- The sandwich controls both output support and dependence on input values. -/
theorem twoSidedSectionCutoff_support
    (R : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ) :
    (∀ u, closure {x | (twoSidedSectionCutoff R χ hχ u).val x ≠ 0} ⊆ tsupport χ) ∧
      (∀ u, (∀ x ∈ tsupport χ, u.val x = 0) → twoSidedSectionCutoff R χ hχ u = 0) := by
  /- Output control: the outer multiplier vanishes off tsupport χ, a closed set.
  Hence the closure of the nonzero locus is contained in that same set.
  Input control: an input zero on tsupport χ becomes the zero section after the
  inner multiplier. Linearity of R and the outer multiplier gives zero output.
  These are the two operator-support conditions, not just a statement about
  principal-symbol support. No continuity or locality of R is needed here. -/
  let T := smoothSectionMul (n := n) (r := r) E (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hχ)
  constructor
  · -- The closed cutoff support contains the complete output nonzero locus.
    intro u
    apply closure_minimal ?_ (isClosed_tsupport χ)
    intro x hx
    by_contra hxχ
    apply hx
    change (χ x : ℂ) • (R (T u)).val x = 0
    simp [image_eq_zero_of_notMem_tsupport hxχ]
  · -- A section vanishing on that support is killed by the actual inner multiplier.
    intro u hu
    have hzero : T u = 0 := by
      apply Subtype.ext
      funext x
      change (χ x : ℂ) • u.val x = 0
      by_cases hx : x ∈ tsupport χ
      · rw [hu x hx, smul_zero]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    change smoothSectionMul (n := n) (r := q) F (fun x ↦ (χ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hχ) (R (T u)) = 0
    rw [hzero, map_zero, map_zero]


variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT hSC hE hF

variable [hC : CompactSpace M] [MeasurableSpace M] [hB : BorelSpace M]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hC hB hμ

/-- Smooth cutoff multiplication on both sides preserves the real PDO order. -/
theorem isPseudodifferentialOperator_twoSidedSectionCutoff {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ) :
    IsPseudodifferentialOperator E F μ m (twoSidedSectionCutoff P.toLinearMap χ hχ) := by
  /- In every local piece absorb the two restrictions of χ into its compact
  input and output cutoffs. Their supports still lie in the same valid frames.
  The smooth remainder kernel is multiplied by χ(x)χ(y), and stays smooth.
  This gives a representation of the exact section map, including all lower
  orders. Compactness is inherited from the current global PDO carrier. -/
  classical
  let T := smoothSectionMul (n := n) (r := r) E (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hχ)
  let S := smoothSectionMul (n := n) (r := q) F (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hχ)
  -- Multiplying an old compact chart cutoff absorbs the global smooth scalar.
  have hcutoff (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
      (hs : tsupport f ⊆ c.target) :
      ContDiff ℝ ∞ (fun z ↦ f z * χ (c.symm z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport f
    · have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) hc) (hs hz)
      exact hf.contDiffAt.mul ((hχ.contMDiffAt.comp z hchart).contDiffAt)
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hz] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
  obtain ⟨N, L, K, hK⟩ := P.isPseudodifferentialOperator
  let input (j : Fin N) : BundleChartCutoff (r := r) E (L j).chart :=
    { (L j).input with
      cutoff := fun z ↦ (L j).input.cutoff z * χ ((L j).chart.symm z)
      smooth_cutoff := hcutoff _ (L j).chart_mem_atlas _ (L j).input.smooth_cutoff
        (fun _ hz ↦ ((L j).input.support_subset hz).1)
      compact_support := (L j).input.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans (L j).input.support_subset }
  let output (j : Fin N) : BundleChartCutoff (r := q) F (L j).chart :=
    { (L j).output with
      cutoff := fun z ↦ (L j).output.cutoff z * χ ((L j).chart.symm z)
      smooth_cutoff := hcutoff _ (L j).chart_mem_atlas _ (L j).output.smooth_cutoff
        (fun _ hz ↦ ((L j).output.support_subset hz).1)
      compact_support := (L j).output.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans (L j).output.support_subset }
  let L' (j : Fin N) : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
    { L j with
      input := input j
      output := output j
      input_support_in_output_frame :=
        tsupport_mul_subset_left.trans (L j).input_support_in_output_frame
      output_support_in_input_frame :=
        tsupport_mul_subset_left.trans (L j).output_support_in_input_frame }
  have hinput (j : Fin N) (u : smoothSections (n := n) (r := r) E) :
      (input j).localize (L j).chart_mem_atlas u =
        (L j).input.localize (L j).chart_mem_atlas (T u) := by
    apply DFunLike.ext
    intro z
    by_cases hz : z ∈ tsupport (L j).input.cutoff
    · have hzc := ((L j).input.support_subset hz).1
      have hzf := ((L j).input.support_subset hz).2
      let := (L j).input.frame_mem_atlas
      change (input j).localizedFunction u z = (L j).input.localizedFunction (T u) z
      simp only [BundleChartCutoff.localizedFunction, hzc, ↓reduceIte]
      dsimp only [input]
      change _ = ((L j).input.cutoff z : ℂ) •
        ((L j).input.frame.linearEquivAt ℂ ((L j).chart.symm z) hzf)
          ((χ ((L j).chart.symm z) : ℂ) • u.val ((L j).chart.symm z))
      rw [map_smul, Complex.ofReal_mul, smul_smul]
      rfl
    · have hz0 := image_eq_zero_of_notMem_tsupport hz
      simp [BundleChartCutoff.localize, BundleChartCutoff.localizedFunction, input, hz0]
  have houtput (j : Fin N)
      (v : SchwartzMap (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℂ (Fin q))) :
      (output j).extend (L j).chart_mem_atlas v =
        S ((L j).output.extend (L j).chart_mem_atlas v) := by
    apply Subtype.ext
    funext x
    change (output j).extendedFunction v x =
      (χ x : ℂ) • (L j).output.extendedFunction v x
    by_cases hx : x ∈ (L j).chart.source
    · simp only [BundleChartCutoff.extendedFunction, hx, ↓reduceIte]
      dsimp only [output]
      rw [(L j).chart.left_inv hx, Complex.ofReal_mul, smul_smul, mul_comm]
    · simp [BundleChartCutoff.extendedFunction, hx]
  have hpiece (j : Fin N) :
      (L' j).toLinearMap = S.comp ((L j).toLinearMap.comp T) := by
    apply LinearMap.ext
    intro u
    change (output j).extend (L j).chart_mem_atlas
      ((L j).operator ((input j).localize (L j).chart_mem_atlas u)) = _
    rw [hinput, houtput]
    rfl
  -- The original remainder kernel acquires exactly one scalar in each variable.
  let K' : SmoothKernel (n := n) (r := r) (q := q) E F :=
    { toFun := fun x y ↦ ((χ x : ℂ) * (χ y : ℂ)) • K.toFun x y
      isSmooth := by
        intro e f _ _
        have hw : ContMDiff
            (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
            𝓘(ℝ, ℂ) ∞ (fun z : M × M ↦ (χ z.1 : ℂ) * (χ z.2 : ℂ)) :=
          (contDiff_fst.mul contDiff_snd :
            ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2)).contMDiff.comp
              (((Complex.ofRealCLM.contMDiff.comp hχ).comp contMDiff_fst).prodMk_space
                ((Complex.ofRealCLM.contMDiff.comp hχ).comp contMDiff_snd))
        have hsmul : ContDiff ℝ ∞ (fun z : ℂ ×
            (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ↦ z.1 • z.2) :=
          (show ContDiff ℂ ∞ _ from contDiff_fst.smul contDiff_snd).restrict_scalars ℝ
        apply (hsmul.contMDiff.comp_contMDiffOn
          (hw.contMDiffOn.prodMk_space (K.isSmooth e f))).congr
        intro z hz
        simp only [kernelInFrames, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul]
        rfl }
  have hkernel : K'.toLinearMap μ = S.comp ((K.toLinearMap μ).comp T) := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
    change (∫ y, ((χ x : ℂ) * (χ y : ℂ)) • K.toFun x y (u.val y) ∂μ) =
      (χ x : ℂ) • ∫ y, K.toFun x y ((χ y : ℂ) • u.val y) ∂μ
    simp_rw [map_smul, mul_smul]
    exact integral_smul _ _
  -- Distribute the two fixed multipliers over the same finite decomposition.
  refine ⟨N, L', K', ?_⟩
  rw [hkernel, hK]
  simp only [hpiece]
  apply LinearMap.ext
  intro u
  change S ((P.toLinearMap - ∑ j, (L j).toLinearMap) (T u)) =
    S (P.toLinearMap (T u)) - (∑ j, S.comp ((L j).toLinearMap.comp T)) u
  simp


/-- Real cutoffs commute with taking the actual explicit-metric formal adjoint. -/
theorem PseudodifferentialOperator.metricFormalAdjoint_twoSidedSectionCutoff {m : ℝ}
    (P Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ)
    (hQ : Q.toLinearMap = twoSidedSectionCutoff P.toLinearMap χ hχ)
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F) :
    (Q.metricFormalAdjoint h k).toLinearMap =
      twoSidedSectionCutoff (P.metricFormalAdjoint h k).toLinearMap χ hχ := by
  /- Move the outer real multiplier across the k pairing, apply P's integral
  adjoint identity, then move the inner real multiplier across the h pairing.
  Both multipliers are self-adjoint for any of the supplied Hermitian metrics.
  Uniqueness of the same-density adjoint identifies the right-hand section
  map with Q's adjoint.
  The equality is exact, including the smoothing remainder. A complex cutoff
  would require complex conjugation and cannot use this formula unchanged. -/
  let T := smoothSectionMul (n := n) (r := r) E (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hχ)
  let S := smoothSectionMul (n := n) (r := q) F (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hχ)
  -- Real scalar multiplication is self-adjoint for each of the two original metrics.
  have hT (u v : smoothSections (n := n) (r := r) E) :
      h.sectionPairing μ (T u) v = h.sectionPairing μ u (T v) := by
    apply integral_congr_ae
    filter_upwards [] with x
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    change (h.toCore x).inner ((χ x : ℂ) • u.val x) (v.val x) =
      (h.toCore x).inner (u.val x) ((χ x : ℂ) • v.val x)
    rw [InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ),
      InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ)]
    simp
  have hS (u v : smoothSections (n := n) (r := q) F) :
      k.sectionPairing μ (S u) v = k.sectionPairing μ u (S v) := by
    apply integral_congr_ae
    filter_upwards [] with x
    let : InnerProductSpace.Core ℂ (F x) := k.toCore x
    change (k.toCore x).inner ((χ x : ℂ) • u.val x) (v.val x) =
      (k.toCore x).inner (u.val x) ((χ x : ℂ) • v.val x)
    rw [InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ),
      InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ)]
    simp
  -- Uniqueness compares the exact section maps, so it needs no composition certificate.
  apply (Q.isMetricFormalAdjoint_metricFormalAdjoint h k).unique
  intro u v
  rw [hQ]
  change k.sectionPairing μ (S (P.toLinearMap (T u))) v =
    h.sectionPairing μ u (T ((P.metricFormalAdjoint h k).toLinearMap (S v)))
  rw [hS, P.isMetricFormalAdjoint_metricFormalAdjoint h k, hT]


end AtiyahSinger
