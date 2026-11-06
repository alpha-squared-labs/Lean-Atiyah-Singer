/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactQuantization
public import AtiyahSinger.Analysis.DifferentialSymbol
public import AtiyahSinger.Analysis.SmoothKernelDensity
public import AtiyahSinger.Analysis.SmoothingOperator
public import AtiyahSinger.Analysis.TwoSidedCutoff
public import AtiyahSinger.Geometry.ChartLocalization

import AtiyahSinger.Analysis.SobolevLocalization

/-!
# Global pseudodifferential operators on a closed manifold

Public module ID: M0674.

Spin Geometry III.3.15 and the bounded-extension part of III.3.17.
A local piece is the actual composite of cutoff restriction, a Schwartz operator
with a specified S^m_(1,0) symbol, and cutoff extension in the same base chart.
The two cutoffs give compact operator support. A global operator is a finite sum
of these pieces modulo an actual smooth-kernel operator for a fixed positive density.
No Sobolev bound, global symbol or parametrix is a field of these structures.

The local representative is required to act continuously on Schwartz functions;
this includes SG's compactly supported representatives. Two-sided cutoffs ensure
that allowing larger Schwartz representatives does not enlarge the global class.
The density is auxiliary: its independence is a separate theorem. No metric,
ellipticity or homogeneous-symbol hypothesis is imposed. The differential-to-PDO
inclusion below is proved by an exact finite local representation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

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

/-- Auxiliary local representation data for a compactly supported PDO piece.
The symbol identity specifies the operator's action, rather than assuming an analytic estimate. -/
structure PseudodifferentialPiece (m : ℝ) where
  /-- The same base chart is used on the input and output. -/
  chart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  /-- Smoothness of this base chart in the given atlas. -/
  chart_mem_atlas : chart ∈ atlas (EuclideanSpace ℝ (Fin n)) M
  /-- Input frame and compact cutoff in chart coordinates. -/
  input : BundleChartCutoff (r := r) E chart
  /-- Output frame and compact cutoff in chart coordinates. -/
  output : BundleChartCutoff (r := q) F chart
  /-- Both frames are valid near the entire input cutoff support. -/
  input_support_in_output_frame : tsupport input.cutoff ⊆ chart.symm ⁻¹' output.frame.baseSet
  /-- Both frames are valid near the entire output cutoff support. -/
  output_support_in_input_frame : tsupport output.cutoff ⊆ chart.symm ⁻¹' input.frame.baseSet
  /-- The actual continuous operator between coordinate Schwartz spaces. -/
  operator : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))
  /-- A full left symbol representing this operator. -/
  symbol : SymbolFunction n r q
  /-- The usual local-in-space symbol estimates, of order at most m. -/
  isSymbol : IsSymbol Set.univ m symbol
  /-- Exact action with SG's Fourier normalization, before applying the outer cutoffs. -/
  operator_apply : ∀ u x, operator u x = quantize symbol u x

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

namespace PseudodifferentialPiece

variable {E F} {m : ℝ} (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)

/-- The compact coordinate operator with both cutoffs, constructed by its actual amplitude. -/
def coordinateOperator : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) :=
  amplitudeOperator m (cutoffAmplitude L.output.cutoff L.input.cutoff L.symbol)
    (isAmplitude_cutoffAmplitude m L.symbol L.isSymbol _ _
      L.output.smooth_cutoff L.input.smooth_cutoff)
    (hasCompactSupport_cutoffAmplitude L.symbol _ _
      L.output.compact_support L.input.compact_support)

set_option linter.unusedSectionVars false in

/-- The amplitude realization is exactly the original operator between its two cutoffs. -/
theorem coordinateOperator_apply
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (z : EuclideanSpace ℝ (Fin n)) :
    L.coordinateOperator v z = L.output.cutoff z • L.operator
      (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
        (fun y ↦ (L.input.cutoff y : ℂ)) v) z := by
  /- The amplitude action formula factors out the output cutoff and inserts the
  input cutoff into the Fourier integral. The recorded operator_apply identifies
  that integral with L.operator. Compact smooth cutoffs justify the Schwartz multiplier. -/
  -- The actual amplitude action retains both cutoffs and the original Fourier normalization.
  rw [coordinateOperator, amplitudeOperator_apply,
    amplitudeApply_cutoffAmplitude m L.symbol L.isSymbol _ _
      L.output.smooth_cutoff L.input.smooth_cutoff
      L.output.compact_support L.input.compact_support, L.operator_apply]

set_option linter.unusedSectionVars false in

/-- Each piece has precisely the two-sided compact support required in SG Definition 3.15. -/
theorem hasOperatorSupport_coordinateOperator :
    HasOperatorSupport (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)
      L.coordinateOperator := by
  /- Apply hasOperatorSupport_cutoff to the defining compact amplitude. The union
  is compact. Both its parts lie in the common chart/frame overlap by support_subset
  and the two cross-frame support fields, so this is a valid local SG representative. -/
  -- Apply the support theorem to exactly the amplitude used by this coordinate operator.
  exact hasOperatorSupport_cutoff m L.symbol L.isSymbol _ _
    L.output.smooth_cutoff L.input.smooth_cutoff
    L.output.compact_support L.input.compact_support

set_option linter.unusedSectionVars false in

/-- The compact coordinate representative has the exact reduced left symbol. -/
theorem coordinateOperator_eq_quantize
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (z : EuclideanSpace ℝ (Fin n)) :
    L.coordinateOperator v z = quantize
      (cutoffSymbol L.output.cutoff L.input.cutoff L.symbol) v z := by
  /- Use amplitudeOperator_apply and the exact amplitude symbol reduction.
  This equality retains every lower-order and smoothing term; the same reduced
  symbol has order m by isSymbol_cutoffSymbol and needs no homogeneity assumption. -/
  rw [coordinateOperator, amplitudeOperator_apply]
  exact (congrFun (quantize_amplitudeSymbol m _
    (isAmplitude_cutoffAmplitude m L.symbol L.isSymbol _ _
      L.output.smooth_cutoff L.input.smooth_cutoff)
    (hasCompactSupport_cutoffAmplitude L.symbol _ _
      L.output.compact_support L.input.compact_support) v) z).symm

/-- Restriction, the given local operator, and inverse-frame extension on global smooth sections. -/
def toLinearMap : smoothSections (n := n) (r := r) E →ₗ[ℂ]
    smoothSections (n := n) (r := q) F :=
  (L.output.extendLinearMap L.chart_mem_atlas).comp
    (L.operator.toLinearMap.comp (L.input.localizeLinearMap L.chart_mem_atlas))

/-- The output coordinates retain the exact quantization formula and the output cutoff. -/
theorem toLinearMap_in_frame (u : smoothSections (n := n) (r := r) E)
    (x : M) (hx : x ∈ L.chart.source) (hf : x ∈ L.output.frame.baseSet) :
    (L.output.frame ⟨x, (L.toLinearMap u).val x⟩).2 =
      (L.output.cutoff (L.chart x) : ℂ) •
        quantize L.symbol (L.input.localize L.chart_mem_atlas u) (L.chart x) := by
  /- Unfold the three actual maps. The source assumption selects the extension
  branch, and the frame-base assumption lets the output frame cancel symmL.
  Finally apply operator_apply; the input remains the actual cutoff localization. -/
  classical
  let := L.output.frame_mem_atlas
  -- Evaluate the actual cutoff extension in the same valid output frame.
  change (L.output.frame ⟨x, L.output.extendedFunction
    (L.operator (L.input.localize L.chart_mem_atlas u)) x⟩).2 = _
  simp only [BundleChartCutoff.extendedFunction, ite_eq_left hx]
  change (L.output.frame.linearEquivAt ℂ x hf)
    ((L.output.cutoff (L.chart x) : ℂ) • L.output.frame.symmL ℂ x
      (L.operator (L.input.localize L.chart_mem_atlas u) (L.chart x))) = _
  rw [map_smul, L.output.frame.symmL_apply hf]
  change (L.output.cutoff (L.chart x) : ℂ) •
    (L.output.frame.linearEquivAt ℂ x hf)
      ((L.output.frame.linearEquivAt ℂ x hf).symm
        (L.operator (L.input.localize L.chart_mem_atlas u) (L.chart x))) = _
  rw [LinearEquiv.apply_symm_apply, L.operator_apply]

/-- Output is zero away from the compact output coordinate support. -/
theorem toLinearMap_eq_zero (u : smoothSections (n := n) (r := r) E) (x : M)
    (hx : x ∉ L.chart.symm '' tsupport L.output.cutoff) : (L.toLinearMap u).val x = 0 := by
  /- Apply extendedFunction_eq_zero to the Schwartz output of L.operator. The
  inverse image of the output cutoff support is compact and lies in the chart
  source and output frame. This does not require a globally compact base. -/
  exact L.output.extendedFunction_eq_zero
    (L.operator (L.input.localize L.chart_mem_atlas u)) x hx

/-- Input values only on the compact input cutoff support can affect the output. -/
theorem toLinearMap_eq_of_eq_on_support (u v : smoothSections (n := n) (r := r) E)
    (h : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, u.val x = v.val x) :
    L.toLinearMap u = L.toLinearMap v := by
  /- On the input cutoff support, h identifies the two sections in the input
  frame. Off it both localized functions are zero. Thus the two Schwartz inputs
  agree, and applying the same operator and cutoff extension preserves equality. -/
  classical
  -- The cutoff identifies the actual Schwartz inputs before applying the local map.
  have hlocal : L.input.localize L.chart_mem_atlas u =
      L.input.localize L.chart_mem_atlas v := by
    apply DFunLike.ext
    intro z
    change L.input.localizedFunction u z = L.input.localizedFunction v z
    by_cases hz : z ∈ tsupport L.input.cutoff
    · simp only [BundleChartCutoff.localizedFunction, sectionInChart,
        h _ ⟨z, hz, rfl⟩]
    · simp [BundleChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
  change L.output.extend L.chart_mem_atlas
    (L.operator (L.input.localize L.chart_mem_atlas u)) =
      L.output.extend L.chart_mem_atlas (L.operator (L.input.localize L.chart_mem_atlas v))
  rw [hlocal]

end PseudodifferentialPiece

variable [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

/-- SG Definition 3.15: finite local PDO pieces modulo an actual smooth-kernel operator. -/
def IsPseudodifferentialOperator (m : ℝ)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F) : Prop :=
  ∃ (N : ℕ) (L : Fin N → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m),
    IsSmoothingOperator μ (P - ∑ j, (L j).toLinearMap)

/-- A global PDO consists of its actual section action and the standard local representation. -/
structure PseudodifferentialOperator (m : ℝ) where
  /-- The actual complex-linear action on global smooth sections. -/
  toLinearMap : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F
  /-- A finite local representation modulo smooth kernels. -/
  isPseudodifferentialOperator : IsPseudodifferentialOperator E F μ m toLinearMap

variable {E F μ}

/-- A single transported local piece is a global PDO of the same order. -/
theorem PseudodifferentialPiece.isPseudodifferentialOperator (m : ℝ)
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) :
    IsPseudodifferentialOperator E F μ m L.toLinearMap := by
  /- Choose one local piece, namely L itself. The remainder is the zero operator,
  represented by the zero smooth bundle kernel. The two cutoff supports make this
  precisely a compactly supported local term in SG Definition 3.15. -/
  classical
  -- A one-term family leaves exactly the zero section operator.
  refine ⟨1, fun _ ↦ L, ?_⟩
  simp only [Fin.sum_univ_one, sub_self]
  let K : SmoothKernel (n := n) (r := r) (q := q) E F :=
    { toFun := fun _ _ ↦ 0
      isSmooth := by
        intro e f _ _
        change ContMDiffOn _ _ ∞ (fun z : M × M ↦
          kernelInFrames E F (fun _ _ ↦ 0) e f z) _
        simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
          ContinuousLinearMap.comp_zero]
        exact contMDiffOn_const }
  refine ⟨K, ?_⟩
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  change (∫ y, (0 : E y →L[ℂ] F x) (u.val y) ∂μ) = 0
  simp

/-- Every smoothing operator belongs to every real PDO order. -/
theorem IsSmoothingOperator.isPseudodifferentialOperator (m : ℝ)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (hP : IsSmoothingOperator μ P) : IsPseudodifferentialOperator E F μ m P := by
  /- Use an empty finite family of local pieces. Its sum is zero, so the remainder
  is exactly P, with the given smooth-kernel representation hP. This works for all
  real m and does not require choosing a local symbol for the smoothing operator. -/
  refine ⟨0, Fin.elim0, ?_⟩
  simpa only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] using hP

/-- Increasing the order bound preserves the global PDO class. -/
theorem IsPseudodifferentialOperator.mono {m l : ℝ} (hml : m ≤ l)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (hP : IsPseudodifferentialOperator E F μ m P) :
    IsPseudodifferentialOperator E F μ l P := by
  /- Keep the same charts, cutoffs, local maps and symbols. Monotonicity of local
  symbol estimates promotes each order-m bound to order l. The global smooth-kernel
  remainder is unchanged. Only the order proof in the local data is replaced. -/
  obtain ⟨N, L, hL⟩ := hP
  -- Change only the order certificate; every local section map is definitionally unchanged.
  let L' (j : Fin N) : PseudodifferentialPiece (n := n) (r := r) (q := q) E F l :=
    { L j with isSymbol := (L j).isSymbol.mono hml }
  exact ⟨N, L', hL⟩

/-- The order-m class is closed under addition on the actual section maps. -/
theorem IsPseudodifferentialOperator.add (m : ℝ)
    (P Q : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (hP : IsPseudodifferentialOperator E F μ m P)
    (hQ : IsPseudodifferentialOperator E F μ m Q) :
    IsPseudodifferentialOperator E F μ m (P + Q) := by
  /- Concatenate the two finite families of local pieces and reindex by Fin.
  Their sum subtracts from P+Q to give the sum of the original smooth remainders.
  Add their actual fiber kernels; smoothness and integral linearity identify the sum. -/
  classical
  obtain ⟨N, L, K, hK⟩ := hP
  obtain ⟨N', L', K', hK'⟩ := hQ
  -- Concatenate the original chart pieces and add their genuine smooth kernels.
  let Ksum : SmoothKernel (n := n) (r := r) (q := q) E F :=
    { toFun := fun x y ↦ K.toFun x y + K'.toFun x y
      isSmooth := by
        intro e f _ _
        apply ((K.isSmooth e f).add (K'.isSmooth e f)).congr
        intro z hz
        simp only [kernelInFrames, Pi.add_apply, ContinuousLinearMap.add_comp,
          ContinuousLinearMap.comp_add] }
  have hsum : Ksum.toLinearMap μ = K.toLinearMap μ + K'.toLinearMap μ := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
    change (∫ y, (K.toFun x y + K'.toFun x y) (u.val y) ∂μ) =
      (∫ y, K.toFun x y (u.val y) ∂μ) + ∫ y, K'.toFun x y (u.val y) ∂μ
    simp only [add_apply]
    exact integral_add (K.integrable_apply μ u x) (K'.integrable_apply μ u x)
  refine ⟨N + N', Fin.append L L', Ksum, ?_⟩
  -- The same two remainders add after the finite-family reindexing.
  rw [hsum, hK, hK', Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  abel

/-- The order-m class is closed under multiplication by a complex scalar. -/
theorem IsPseudodifferentialOperator.smul (m : ℝ) (a : ℂ)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (hP : IsPseudodifferentialOperator E F μ m P) :
    IsPseudodifferentialOperator E F μ m (a • P) := by
  /- Multiply each local Schwartz operator and its symbol by a, retaining all
  chart and cutoff data. Quantization is complex-linear in the symbol. Multiply
  the smooth remainder kernel by a; integration gives the required remainder. -/
  classical
  obtain ⟨N, L, K, hK⟩ := hP
  -- Scale each actual local operator and its recorded full symbol in the same chart.
  let L' (j : Fin N) : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
    { L j with
      operator := a • (L j).operator
      symbol := a • (L j).symbol
      isSymbol := (L j).isSymbol.smul isOpen_univ a
      operator_apply := by
        intro u x
        change a • (L j).operator u x = quantize (a • (L j).symbol) u x
        rw [(L j).operator_apply]
        simp only [quantize, Pi.smul_apply, smul_apply]
        simp_rw [smul_comm (Complex.exp _) a]
        rw [integral_smul, smul_comm] }
  have hlocal (j : Fin N) : (L' j).toLinearMap = a • (L j).toLinearMap := by
    apply LinearMap.ext
    intro u
    change (L j).output.extendLinearMap (L j).chart_mem_atlas
      (a • (L j).operator ((L j).input.localize (L j).chart_mem_atlas u)) =
        a • (L j).output.extendLinearMap (L j).chart_mem_atlas
          ((L j).operator ((L j).input.localize (L j).chart_mem_atlas u))
    exact map_smul _ a _
  -- Scale the smooth remainder in the input integral without changing its density.
  let Ka : SmoothKernel (n := n) (r := r) (q := q) E F :=
    { toFun := fun x y ↦ a • K.toFun x y
      isSmooth := by
        intro e f _ _
        have hscale : ContDiff ℝ ∞ (fun T : EuclideanSpace ℂ (Fin r) →L[ℂ]
            EuclideanSpace ℂ (Fin q) ↦ a • T) :=
          contDiff_const_smul a
        apply (hscale.contMDiff.comp_contMDiffOn (K.isSmooth e f)).congr
        intro z hz
        simp only [Function.comp_apply, kernelInFrames, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul] }
  have hkernel : Ka.toLinearMap μ = a • K.toLinearMap μ := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
    change (∫ y, (a • K.toFun x y) (u.val y) ∂μ) =
      a • ∫ y, K.toFun x y (u.val y) ∂μ
    simp only [smul_apply]
    exact integral_smul a _
  refine ⟨N, L', Ka, ?_⟩
  rw [hkernel, hK, smul_sub, Finset.smul_sum]
  simp only [hlocal]

/-- The auxiliary positive smooth density does not change the global PDO class. -/
theorem isPseudodifferentialOperator_measure_iff
    (ν : Measure M) [IsSmoothPositiveMeasure (n := n) ν] (m : ℝ)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F) :
    IsPseudodifferentialOperator E F μ m P ↔ IsPseudodifferentialOperator E F ν m P := by
  /- Keep the same finite local family. The smoothing remainder is independent
  of the positive density by reweighting its kernel in the input variable with
  the smooth density ratio. Apply isSmoothingOperator_measure_iff in each
  direction. The kernel changes, while its section map is preserved. -/

  constructor
  · rintro ⟨N, L, hL⟩
    exact ⟨N, L, (isSmoothingOperator_measure_iff μ ν _).mp hL⟩
  · rintro ⟨N, L, hL⟩
    exact ⟨N, L, (isSmoothingOperator_measure_iff μ ν _).mpr hL⟩

open Filter in
open scoped Topology in
/-- SG p.186: every global differential operator is a PDO of its finite order. -/
theorem DifferentialOperator.isPseudodifferentialOperator {k : ℕ}
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F k) :
    IsPseudodifferentialOperator E F μ (k : ℝ) P.toLinearMap := by


  /- Stage 1: choose a finite output partition subordinate to domains carrying
  P's actual coordinate differential expressions. Each input cutoff is one on an
  open neighborhood of its output support. Use that same cutoff to zero-extend
  the local polynomial symbol; its compact spatial support gives the existing
  continuous Schwartz quantization.
  Stage 2: on each output support the input cutoff preserves the original
  coordinate germ, so polynomial quantization is exactly P's recorded action.
  The original output frame therefore gives the partition weight times P(u).
  Sum the finite partition identity; the remainder is the actual zero kernel.
  Placing the partition on the output avoids differentiating its weights. -/
  classical
  -- Use the actual differential expressions, refining the chart/frame cover before partitioning.
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let f (x : M) := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  have hexpr (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ Q : CoordinateDifferentialOperator n r q k (c x '' U),
        HasCoordinateExpression E F k P.toLinearMap (c x) (e x) (f x) U Q :=
    P.isDifferentialOperator (c x) (chart_mem_atlas _ x) (e x) (f x) x
      ⟨⟨mem_chart_source _ x, mem_baseSet_trivializationAt _ _ x⟩,
        mem_baseSet_trivializationAt _ _ x⟩
  choose U hU hxU Q hQ using hexpr
  have hcover : Set.univ ⊆ ⋃ x, U x := fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let index : Fin s.card ≃ s := s.equivFin.symm
  let V (j : Fin s.card) := U (index j)
  have hfinitecover : Set.univ ⊆ ⋃ j, V j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨index.symm ⟨y, hy⟩, by simpa [V] using hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ V
    (fun j ↦ hU (index j)) hfinitecover
  -- Transfer the output partition to the same coordinates, preserving its compact support.
  let χ (j : Fin s.card) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
    if z ∈ (c (index j)).target then ρ j ((c (index j)).symm z) else 0
  let K (j : Fin s.card) := (c (index j)) '' tsupport (ρ j)
  have hK (j : Fin s.card) : IsCompact (K j) :=
    (HasCompactSupport.of_compactSpace (ρ j)).image_of_continuousOn
      ((c (index j)).continuousOn.mono (fun x hx ↦ ((hQ (index j)).1 (hρ j hx)).1.1))
  have hχ (j : Fin s.card) : tsupport (χ j) ⊆ K j := by
    apply closure_minimal ?_ (hK j).isClosed
    intro z hz
    have ht : z ∈ (c (index j)).target := by
      by_contra ht
      exact hz (by simp [χ, ht])
    have hr : (c (index j)).symm z ∈ tsupport (ρ j) := by
      by_contra hr
      exact hz (by simp [χ, ht, image_eq_zero_of_notMem_tsupport hr])
    exact ⟨(c (index j)).symm z, hr, (c (index j)).right_inv ht⟩
  have hχcompact (j : Fin s.card) : HasCompactSupport (χ j) :=
    (hK j).of_isClosed_subset (isClosed_tsupport _) (hχ j)
  have hχsmooth (j : Fin s.card) : ContDiff ℝ ∞ (χ j) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ K j
    · obtain ⟨x, hx, rfl⟩ := hz
      have hxsource := ((hQ (index j)).1 (hρ j hx)).1.1
      have ht := (c (index j)).map_source hxsource
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) (chart_mem_atlas _ (index j : M))) ht
      have hlocal := ((ρ j).contMDiff.contMDiffAt.comp _ hchart).contDiffAt
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [(c (index j)).open_target.mem_nhds ht] with y hy
      simp only [χ, ite_eq_left hy]
      rfl
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(hK j).isClosed.isOpen_compl.mem_nhds hz] with y hy
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hχ j h))
  let D (j : Fin s.card) := c (index j) '' U (index j)
  have hD (j : Fin s.card) : IsOpen (D j) :=
    (c (index j)).isOpen_image_of_subset_source (hU (index j))
      (fun x hx ↦ ((hQ (index j)).1 hx).1.1)
  have hKD (j : Fin s.card) : K j ⊆ D j := Set.image_mono (hρ j)
  have hdomain (j : Fin s.card) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ D j) :
      z ∈ (c (index j)).target ∧
        (c (index j)).symm z ∈ (e (index j)).baseSet ∩ (f (index j)).baseSet := by
    obtain ⟨x, hx, rfl⟩ := hz
    have hu := (hQ (index j)).1 hx
    exact ⟨(c (index j)).map_source hu.1.1,
      by simpa only [(c (index j)).left_inv hu.1.1, Set.mem_inter_iff] using
        And.intro hu.1.2 hu.2⟩
  -- A smooth input cutoff is identically one on an open neighborhood of the output support.
  have hinput (j : Fin s.card) :
      ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        tsupport ψ ⊆ D j ∧ ∃ W, IsOpen W ∧ tsupport (χ j) ⊆ W ∧
          ∀ z ∈ W, ψ z = 1 := by
    obtain ⟨W, hW, hKW, hWD, hWcompact⟩ :=
      exists_open_between_and_isCompact_closure (hK j) (hD j) (hKD j)
    obtain ⟨O, hO, hWO, hOD, hOcompact⟩ :=
      exists_open_between_and_isCompact_closure hWcompact (hD j) hWD
    obtain ⟨ψ, hψ, _, hsupp, hone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hO isClosed_closure hWO
    have hts : tsupport ψ = closure O := congrArg closure hsupp
    refine ⟨ψ, hψ, ?_, ?_, W, hW, (hχ j).trans hKW, ?_⟩
    · change IsCompact (tsupport ψ)
      rwa [hts]
    · rwa [hts]
    · intro z hz
      exact (hone z).mp (subset_closure hz)
  choose ψ hψsmooth hψcompact hψsupport hψone using hinput
  let a (j : Fin s.card) := zeroExtendedSymbol (D j) (ψ j) (Q (index j)).totalSymbol
  have ha (j : Fin s.card) : IsSymbol Set.univ (k : ℝ) (a j) :=
    isSymbol_zeroExtendedSymbol (D j) (hD j) k (ψ j) (hψsmooth j)
      (hψcompact j) (hψsupport j) _ ((Q (index j)).isSymbol_totalSymbol (hD j))
  have hacompact (j : Fin s.card) : HasCompactSupport (a j) :=
    hasCompactSupport_zeroExtendedSymbol (D j) (ψ j) _ (hψcompact j)
  let L (j : Fin s.card) : PseudodifferentialPiece (n := n) (r := r) (q := q) E F k :=
    { chart := c (index j)
      chart_mem_atlas := chart_mem_atlas _ (index j : M)
      input :=
        { frame := e (index j)
          frame_mem_atlas := inferInstance
          cutoff := ψ j
          smooth_cutoff := hψsmooth j
          compact_support := hψcompact j
          support_subset := fun z hz ↦
            ⟨(hdomain j (hψsupport j hz)).1, (hdomain j (hψsupport j hz)).2.1⟩ }
      output :=
        { frame := f (index j)
          frame_mem_atlas := inferInstance
          cutoff := χ j
          smooth_cutoff := hχsmooth j
          compact_support := hχcompact j
          support_subset := fun z hz ↦
            ⟨(hdomain j (hKD j (hχ j hz))).1, (hdomain j (hKD j (hχ j hz))).2.2⟩ }
      input_support_in_output_frame := fun z hz ↦ (hdomain j (hψsupport j hz)).2.2
      output_support_in_input_frame := fun z hz ↦ (hdomain j (hKD j (hχ j hz))).2.1
      operator := quantizeSchwartz k (a j) (ha j) (hacompact j)
      symbol := a j
      isSymbol := ha j
      operator_apply := quantizeSchwartz_apply k (a j) (ha j) (hacompact j) }
  -- The remaining comparison uses the same local expression and the actual cutoff plateau.
  have hpiece (j : Fin s.card) (u : smoothSections (n := n) (r := r) E) (x : M) :
      ((L j).toLinearMap u).val x = (ρ j x : ℂ) • (P.toLinearMap u).val x := by
    have hχx (hx : x ∈ (c (index j)).source) : χ j (c (index j) x) = ρ j x := by
      simp only [χ, ite_eq_left ((c (index j)).map_source hx),
        (c (index j)).left_inv hx]
    by_cases hr : ρ j x = 0
    · -- Off the partition support the actual output cutoff makes this piece vanish.
      change (L j).output.extendedFunction
        ((L j).operator ((L j).input.localize (L j).chart_mem_atlas u)) x = _
      by_cases hx : x ∈ (c (index j)).source
      · simp only [BundleChartCutoff.extendedFunction, L, ite_eq_left hx, hχx hx, hr,
          Complex.ofReal_zero, zero_smul]
      · simp only [BundleChartCutoff.extendedFunction, L, ite_eq_right hx, hr,
          Complex.ofReal_zero, zero_smul]
    · have hxU : x ∈ U (index j) := hρ j (subset_tsupport _ hr)
      have hu := (hQ (index j)).1 hxU
      have hxD : c (index j) x ∈ D j := ⟨x, hxU, rfl⟩
      have hxχ : c (index j) x ∈ tsupport (χ j) :=
        subset_tsupport _ (by
          change χ j (c (index j) x) ≠ 0
          rwa [hχx hu.1.1])
      obtain ⟨W, hW, hχW, hψW⟩ := hψone j
      have hψx := hψW _ (hχW hxχ)
      -- The localized input has exactly the original coordinate germ on this plateau.
      have hnear : ((L j).input.localize (L j).chart_mem_atlas u :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r)) =ᶠ[nhds (c (index j) x)]
            sectionInChart E (c (index j)) (e (index j)) u.val := by
        filter_upwards [hW.mem_nhds (hχW hxχ),
          (c (index j)).open_target.mem_nhds ((c (index j)).map_source hu.1.1)] with z hz hzT
        change (L j).input.localizedFunction u z = _
        simp only [BundleChartCutoff.localizedFunction, L, ite_eq_left hzT, hψW z hz,
          Complex.ofReal_one, one_smul]
      have hpoly : (Q (index j)).apply
          ((L j).input.localize (L j).chart_mem_atlas u) (c (index j) x) =
          (Q (index j)).apply
            (sectionInChart E (c (index j)) (e (index j)) u.val) (c (index j) x) := by
        simp only [CoordinateDifferentialOperator.apply]
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro α _
        rw [(hnear.iteratedFDeriv ℝ l.val).eq_of_nhds]
      have haeq (ξ : EuclideanSpace ℝ (Fin n)) :
          a j (c (index j) x) ξ = (Q (index j)).totalSymbol (c (index j) x) ξ := by
        simp only [a, zeroExtendedSymbol, ite_eq_left hxD, hψx,
          Complex.ofReal_one, one_smul]
      have hquant : quantize (a j) ((L j).input.localize (L j).chart_mem_atlas u)
          (c (index j) x) = (Q (index j)).apply
            (sectionInChart E (c (index j)) (e (index j)) u.val) (c (index j) x) := by
        calc
          _ = quantize (Q (index j)).totalSymbol
              ((L j).input.localize (L j).chart_mem_atlas u) (c (index j) x) := by
            simp only [quantize, haeq]
          _ = _ := ((Q (index j)).quantize_totalSymbol _ _).trans hpoly
      -- The same output frame recovers the original fiber value, multiplied only by ρ.
      have hframe := (L j).toLinearMap_in_frame u x hu.1.1 hu.2
      change (f (index j) ⟨x, ((L j).toLinearMap u).val x⟩).2 =
        (χ j (c (index j) x) : ℂ) • quantize (a j)
          ((L j).input.localize (L j).chart_mem_atlas u) (c (index j) x) at hframe
      rw [hχx hu.1.1, hquant, ← (hQ (index j)).2 u x hxU] at hframe
      apply ((f (index j)).linearEquivAt ℂ x hu.2).injective
      rw [map_smul]
      exact hframe
  have hsum : P.toLinearMap = ∑ j, (L j).toLinearMap := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, hpiece,
      ← Finset.sum_smul]
    have hρsum : ∑ j, ρ j x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
    rw [← Complex.ofReal_sum, hρsum, Complex.ofReal_one, one_smul]
  refine ⟨s.card, L, ?_⟩
  rw [hsum, sub_self]
  let Kzero : SmoothKernel (n := n) (r := r) (q := q) E F :=
    { toFun := fun _ _ ↦ 0
      isSmooth := by
        intro e f _ _
        change ContMDiffOn _ _ ∞ (fun z : M × M ↦
          kernelInFrames E F (fun _ _ ↦ 0) e f z) _
        simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
          ContinuousLinearMap.comp_zero]
        exact contMDiffOn_const }
  refine ⟨Kzero, ?_⟩
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  change (∫ y, (0 : E y →L[ℂ] F x) (u.val y) ∂μ) = 0
  simp

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- SG Theorem 3.17(i): the original section map obeys the order-m Sobolev estimate. -/
theorem exists_norm_smoothToSobolev_apply_le (s : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : smoothSections (n := n) (r := r) E,
      ‖B.smoothToSobolev (s - m) (P.toLinearMap u)‖ ≤ C * ‖A.smoothToSobolev s u‖ := by
  /- Stage 1: represent P by its finite local pieces and smooth-kernel remainder.
  For a piece, insert compact chart cutoffs and finite presentation cutoffs. The
  exact two-sided cutoff symbol is of order m and has compact spatial support.
  Local Sobolev boundedness gives H^s -> H^(s-m); smooth coordinate pullbacks and
  frame multiplication on compact overlaps compare these norms to A and B.
  Stage 2: the smooth remainder has the same bound by its all-order extension.
  Sum the finitely many bounds, enlarging the constant to make it positive.
  This is valid for every real s,m and requires neither ellipticity nor a metric. -/
  classical
  -- Bound each specified piece before summing the original representation.
  have hpiece (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : smoothSections (n := n) (r := r) E,
        ‖B.smoothToSobolev (s - m) (L.toLinearMap u)‖ ≤
          C * ‖A.smoothToSobolev s u‖ := by
    let X := EuclideanSpace ℝ (Fin n)
    let Vin := EuclideanSpace ℂ (Fin r)
    let Vout := EuclideanSpace ℂ (Fin q)
    -- Plateaus retain the original frames and are one near the existing cutoff supports.
    have plateau (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
        ∃ χ : X → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
          tsupport χ ⊆ U ∧ K ⊆ interior {x | χ x = 1} := by
      obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
        exists_open_between_and_isCompact_closure hK hU hKU
      obtain ⟨O', hO'o, hOO', hO'U, hO'c⟩ :=
        exists_open_between_and_isCompact_closure hOc hU hOU
      obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
        (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
      have hχsupport : tsupport χ = closure O' := congrArg closure hsχ
      refine ⟨χ, hχ, by simpa [HasCompactSupport, hχsupport] using hO'c,
        by rwa [hχsupport], ?_⟩
      intro x hx
      apply mem_interior.mpr
      refine ⟨O, ?_, hOo, hKO hx⟩
      intro y hy
      exact (honeχ y).mp (subset_closure hy)
    have hUi : IsOpen (L.chart.target ∩ L.chart.symm ⁻¹' L.input.frame.baseSet) :=
      L.chart.continuousOn_symm.isOpen_inter_preimage
        L.chart.open_target L.input.frame.open_baseSet
    have hUo : IsOpen (L.chart.target ∩ L.chart.symm ⁻¹' L.output.frame.baseSet) :=
      L.chart.continuousOn_symm.isOpen_inter_preimage
        L.chart.open_target L.output.frame.open_baseSet
    obtain ⟨ρ, hρ, hcρ, hρU, hρnear⟩ :=
      plateau _ _ L.input.compact_support hUi L.input.support_subset
    obtain ⟨σ, hσ, hcσ, hσU, hσnear⟩ :=
      plateau _ _ L.output.compact_support hUo L.output.support_subset
    have hρone (x : X) (hx : x ∈ tsupport L.input.cutoff) : ρ x = 1 :=
      (interior_subset (s := {x | ρ x = 1})) (hρnear hx)
    have hσone (x : X) (hx : x ∈ tsupport L.output.cutoff) : σ x = 1 :=
      (interior_subset (s := {x | σ x = 1})) (hσnear hx)
    let D : BundleChartCutoff (r := q) F L.chart :=
      { L.output with cutoff := σ
                      smooth_cutoff := hσ
                      compact_support := hcσ
                      support_subset := hσU }
    -- Only the original output cutoff appears in the compact symbol; the input plateau is neutral.
    let p := cutoffSymbol L.output.cutoff ρ L.symbol
    have hp : IsSymbol univ m p := isSymbol_cutoffSymbol m L.symbol L.isSymbol _ _
      L.output.smooth_cutoff hρ L.output.compact_support hcρ
    have hcp : HasCompactSupport p := hasCompactSupport_amplitudeSymbol _
      (hasCompactSupport_cutoffAmplitude L.symbol _ _ L.output.compact_support hcρ)
    let T := quantizeSobolev m s p hp hcp
    have hρgrowth : (fun x ↦ (ρ x : ℂ)).HasTemperateGrowth :=
      (hcρ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hρ)
    have hχgrowth : (fun x ↦ (L.output.cutoff x : ℂ)).HasTemperateGrowth :=
      (L.output.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp L.output.smooth_cutoff)
    let v (u : smoothSections (n := n) (r := r) E) : 𝓢(X, Vin) :=
      L.input.localize L.chart_mem_atlas u
    let w (u : smoothSections (n := n) (r := r) E) : 𝓢(X, Vout) :=
      SchwartzMap.smulLeftCLM Vout (fun x ↦ (L.output.cutoff x : ℂ)) (L.operator (v u))
    have hwin (u : smoothSections (n := n) (r := r) E) :
        SchwartzMap.smulLeftCLM Vin (fun x ↦ (ρ x : ℂ)) (v u) = v u := by
      apply DFunLike.ext
      intro x
      rw [SchwartzMap.smulLeftCLM_apply_apply hρgrowth]
      by_cases hx : x ∈ tsupport L.input.cutoff
      · rw [hρone x hx, Complex.ofReal_one, one_smul]
      · have hvzero : v u x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h ↦ hx (L.input.tsupport_localizedFunction_subset u h))
        rw [hvzero, smul_zero]
    have hwout (u : smoothSections (n := n) (r := r) E) (x : X) :
        w u x = (L.output.cutoff x : ℂ) • L.operator (v u) x :=
      SchwartzMap.smulLeftCLM_apply_apply hχgrowth _ x
    have hquant (u : smoothSections (n := n) (r := r) E) (x : X) :
        quantize p (v u) x = w u x := by
      rw [show p = cutoffSymbol L.output.cutoff ρ L.symbol from rfl,
        quantize_cutoffSymbol m L.symbol L.isSymbol _ _
          L.output.smooth_cutoff hρ L.output.compact_support hcρ, hwin, ← L.operator_apply,
        hwout, Complex.coe_smul]
    -- The named Euclidean Sobolev quantizer has precisely this Schwartz output.
    have hT (u : smoothSections (n := n) (r := r) E) :
        T (schwartzSobolevCoordinate s (v u)) = schwartzSobolevCoordinate (s - m) (w u) := by
      apply besselRealization_injective n q (s - m)
      ext1 φ
      rw [besselRealization_quantizeSobolev, besselRealization_schwartzSobolevCoordinate,
        SchwartzMap.coe_apply]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hquant]
    -- The extension plateau removes the outer support boundary without squaring its cutoff.
    let := L.output.frame_mem_atlas
    have hreconstruct (u : smoothSections (n := n) (r := r) E) :
        D.extend L.chart_mem_atlas (w u) = L.toLinearMap u := by
      apply Subtype.ext
      funext x
      change D.extendedFunction (w u) x = L.output.extendedFunction (L.operator (v u)) x
      by_cases hx : x ∈ L.chart.source
      · simp only [BundleChartCutoff.extendedFunction, ite_eq_left hx]
        change (σ (L.chart x) : ℂ) • L.output.frame.symmL ℂ x (w u (L.chart x)) =
          (L.output.cutoff (L.chart x) : ℂ) •
            L.output.frame.symmL ℂ x (L.operator (v u) (L.chart x))
        rw [hwout, map_smul, smul_smul]
        by_cases hz : L.chart x ∈ tsupport L.output.cutoff
        · rw [hσone _ hz, Complex.ofReal_one, one_mul]
        · simp only [image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero, mul_zero,
            zero_smul]
      · simp only [BundleChartCutoff.extendedFunction, ite_eq_right hx]
    -- Compose the actual input, compact quantizer and plateau-extension estimates.
    obtain ⟨Ci, hCi, hinput⟩ :=
      L.input.exists_norm_localize_sobolev_le L.chart_mem_atlas A s
    obtain ⟨Co, hCo, houtput⟩ :=
      D.exists_norm_extend_sobolev_le L.chart_mem_atlas B (s - m)
    refine ⟨Co * ‖T‖ * Ci, mul_nonneg (mul_nonneg hCo (norm_nonneg T)) hCi, ?_⟩
    intro u
    rw [← hreconstruct]
    calc
      _ ≤ Co * ‖schwartzSobolevCoordinate (s - m) (w u)‖ := houtput (w u)
      _ = Co * ‖T (schwartzSobolevCoordinate s (v u))‖ := by rw [hT]
      _ ≤ Co * (‖T‖ * ‖schwartzSobolevCoordinate s (v u)‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm _) hCo
      _ ≤ Co * (‖T‖ * (Ci * ‖A.smoothToSobolev s u‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hinput u) (norm_nonneg T)) hCo
      _ = _ := by ring
  -- The smooth remainder acts between arbitrary real orders; the finite sum is exact.
  obtain ⟨N, L, K, hK⟩ := P.isPseudodifferentialOperator
  choose C hC hb using fun j ↦ hpiece (L j)
  obtain ⟨CK, hCK, hbK⟩ := K.exists_norm_smoothToSobolev_apply_le μ A B s (s - m)
  have hdecomp : P.toLinearMap = (∑ j, (L j).toLinearMap) + K.toLinearMap μ := by
    rw [hK]
    abel
  refine ⟨(∑ j, C j) + CK, add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ ↦ hC j) hCK,
    ?_⟩
  intro u
  rw [hdecomp, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
  calc
    _ ≤ ‖∑ j, B.smoothToSobolev (s - m) ((L j).toLinearMap u)‖ +
        ‖B.smoothToSobolev (s - m) (K.toLinearMap μ u)‖ := norm_add_le _ _
    _ ≤ (∑ j, ‖B.smoothToSobolev (s - m) ((L j).toLinearMap u)‖) +
        CK * ‖A.smoothToSobolev s u‖ := add_le_add (norm_sum_le _ _) (hbK u)
    _ ≤ (∑ j, C j * ‖A.smoothToSobolev s u‖) + CK * ‖A.smoothToSobolev s u‖ :=
      add_le_add (Finset.sum_le_sum fun j _ ↦ hb j u) le_rfl
    _ = _ := by rw [← Finset.sum_mul, add_mul]

/-- The Sobolev extension is uniquely specified by agreement on actual smooth sections. -/
theorem existsUnique_sobolevExtension (s : ℝ) :
    ∃! T : A.SobolevSpace s →L[ℂ] B.SobolevSpace (s - m),
      ∀ u : smoothSections (n := n) (r := r) E,
        T (A.smoothToSobolev s u) = B.smoothToSobolev (s - m) (P.toLinearMap u) := by
  /- The preceding estimate extends the section map from A's dense smooth image
  into B's complete Sobolev space. Injectivity of smoothToSobolev identifies that
  image with the original sections. Continuous maps agreeing there agree everywhere,
  giving uniqueness. No extension is assumed in the definition of a global PDO. -/
  -- Extend the bounded action from the original dense smooth image.
  obtain ⟨C, _, hC⟩ := P.exists_norm_smoothToSobolev_apply_le A B s
  let f := (B.smoothToSobolev (s - m)).comp P.toLinearMap
  let T : A.SobolevSpace s →L[ℂ] B.SobolevSpace (s - m) :=
    f.extendOfNorm (A.smoothToSobolev s)
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (A.smoothToSobolev s u) = B.smoothToSobolev (s - m) (P.toLinearMap u) :=
    LinearMap.extendOfNorm_eq (A.denseRange_smoothToSobolev s) ⟨C, hC⟩ u
  refine ⟨T, hT, ?_⟩
  -- Agreement on the same smooth sections identifies every continuous extension.
  intro R hR
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer R.continuous T.continuous
  funext u
  exact (hR u).trans (hT u).symm

/-- The bounded realization of the specified global PDO, selected by its unique action. -/
def sobolevExtension (s : ℝ) : A.SobolevSpace s →L[ℂ] B.SobolevSpace (s - m) :=
  Classical.choose (P.existsUnique_sobolevExtension A B s).exists

/-- The chosen bounded realization agrees with the original global section action. -/
theorem sobolevExtension_smoothToSobolev (s : ℝ)
    (u : smoothSections (n := n) (r := r) E) :
    P.sobolevExtension A B s (A.smoothToSobolev s u) =
      B.smoothToSobolev (s - m) (P.toLinearMap u) := by
  /- Apply the action specification of the unique continuous extension selected
  in sobolevExtension. Its source is the actual H^s completion and its target has
  order s-m; the section on the right is the original globally assembled output. -/
  exact (P.existsUnique_sobolevExtension A B s).exists.choose_spec u

end PseudodifferentialOperator

end AtiyahSinger
