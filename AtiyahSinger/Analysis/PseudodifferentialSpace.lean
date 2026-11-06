/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalQuantization
public import Mathlib.LinearAlgebra.Isomorphisms

import all AtiyahSinger.Analysis.SmoothingOperator

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The filtered PDO space and its principal-symbol exact sequence

Public module ID: M0901.

D05/A02/A03: the order-m PDOs form an actual submodule of linear section maps.
The principal symbol is linear and surjective, and its kernel consists exactly
of operators of order m-1. The resulting first-isomorphism equivalence is a
quotient of actual operators. Equality of principal classes loses one order;
it does not identify operators modulo infinitely smoothing kernels.

These are consequences of SG III.3.13-3.19 and the local N=1 symbol calculus,
not additional numbered book lemmas. All source and target ranks remain independent.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set Filter
open scoped Manifold ContDiff SchwartzMap Topology

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

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

/-- The zero section operator belongs to every real PDO order. -/
theorem isPseudodifferentialOperator_zero (m : ℝ) :
    IsPseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m 0 := by
  /- Use the empty local family and the zero smooth kernel. Its integral is
  the zero section map, so it is exactly the required remainder. -/
  -- The zero fiber maps form a smooth kernel in the original bundle frames.
  let K : SmoothKernel (n := n) (r := r) (q := q) E F :=
    { toFun := fun _ _ ↦ 0
      isSmooth := by
        intro e f _ _
        change ContMDiffOn _ _ ∞ (fun z : M × M ↦
          kernelInFrames E F (fun _ _ ↦ 0) e f z) _
        simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
          ContinuousLinearMap.comp_zero]
        exact contMDiffOn_const }
  -- Its integral is the zero section map, which has an empty PDO representation.
  apply IsSmoothingOperator.isPseudodifferentialOperator m 0
  refine ⟨K, ?_⟩
  ext u x
  change K.apply μ u x = 0
  simp [SmoothKernel.apply, K]

/-- The standard filtered vector space Ψ^m(E,F) of actual smooth-section operators. -/
def pseudodifferentialSpace (m : ℝ) :
    Submodule ℂ (smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F) where
  carrier := {P | IsPseudodifferentialOperator E F μ m P}
  zero_mem' := isPseudodifferentialOperator_zero E F μ m
  add_mem' := fun {P Q} hP hQ ↦ IsPseudodifferentialOperator.add m P Q hP hQ
  smul_mem' := fun a P hP ↦ IsPseudodifferentialOperator.smul m a P hP

/-- The PDO spaces increase with their real order bounds. -/
theorem pseudodifferentialSpace_mono {m l : ℝ} (hml : m ≤ l) :
    pseudodifferentialSpace (n := n) (r := r) (q := q) E F μ m ≤
      pseudodifferentialSpace (n := n) (r := r) (q := q) E F μ l := by
  /- The underlying ambient space is the same space of linear section maps.
  Apply IsPseudodifferentialOperator.mono to membership of each map. -/
  intro P hP
  exact IsPseudodifferentialOperator.mono hml P hP

variable {E F μ}

/-- Regard a bundled PDO as its actual map in the order-m submodule. -/
def PseudodifferentialOperator.toSpace {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m) :
    pseudodifferentialSpace (n := n) (r := r) (q := q) E F μ m :=
  ⟨P.toLinearMap, P.isPseudodifferentialOperator⟩

/-- Bundle the actual map and membership proof of an element of Ψ^m(E,F). -/
def pseudodifferentialOperatorOfSpace {m : ℝ}
    (P : pseudodifferentialSpace (n := n) (r := r) (q := q) E F μ m) :
    PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m where
  toLinearMap := P.val
  isPseudodifferentialOperator := P.property

namespace PseudodifferentialOperator

variable {m : ℝ} (P Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

/-- Addition of bundled PDOs is addition of their actual section maps. -/
def add : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m where
  toLinearMap := P.toLinearMap + Q.toLinearMap
  isPseudodifferentialOperator := IsPseudodifferentialOperator.add m P.toLinearMap Q.toLinearMap
    P.isPseudodifferentialOperator Q.isPseudodifferentialOperator

/-- Complex scaling of a bundled PDO keeps the exact scaled section action. -/
def smul (a : ℂ) : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m where
  toLinearMap := a • P.toLinearMap
  isPseudodifferentialOperator :=
    IsPseudodifferentialOperator.smul m a P.toLinearMap P.isPseudodifferentialOperator

/-- The principal class of a sum is the sum of the principal classes. -/
theorem principalSymbol_add :
    (P.add Q).principalSymbol = P.principalSymbol + Q.principalSymbol := by
  /- Concatenate finite local representations of P and Q. The remainders add as
  actual smooth kernels, while the sum of global symbols is the sum of the two
  former symbol sums. Apply the representation formula and the linear quotient map. -/
  classical
  obtain ⟨N, L, K, hK⟩ := P.isPseudodifferentialOperator
  obtain ⟨N', L', K', hK'⟩ := Q.isPseudodifferentialOperator
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
  have hrep : IsSmoothingOperator μ
      ((P.add Q).toLinearMap - ∑ j, (Fin.append L L' j).toLinearMap) := by
    refine ⟨Ksum, ?_⟩
    rw [hsum, hK, hK', Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, add]
    abel
  -- The same concatenation adds the transported global symbols and their classes.
  rw [(P.add Q).principalSymbol_eq_of_representation (N + N') (Fin.append L L') hrep,
    P.principalSymbol_eq_of_representation N L ⟨K, hK⟩,
    Q.principalSymbol_eq_of_representation N' L' ⟨K', hK'⟩, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, map_add]

/-- The principal class scales complex-linearly with the section operator. -/
theorem principalSymbol_smul (a : ℂ) :
    (P.smul a).principalSymbol = a • P.principalSymbol := by
  /- Scale every local operator and symbol by a, and scale the smooth remainder
  kernel by a. The exact Fourier action is linear in the symbol. The principal
  representation formula and quotient linearity then give the stated equality. -/
  classical
  obtain ⟨N, L, K, hK⟩ := P.isPseudodifferentialOperator
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
  have hrep : IsSmoothingOperator μ
      ((P.smul a).toLinearMap - ∑ j, (L' j).toLinearMap) := by
    refine ⟨Ka, ?_⟩
    rw [hkernel, hK, smul_sub, Finset.smul_sum]
    simp only [hlocal, smul]
  -- Transport through the same frames preserves the scalar on every principal symbol.
  have hglobal (j : Fin N) : (L' j).globalSymbol = a • (L j).globalSymbol := by
    apply Subtype.ext
    funext x ξ
    change (L' j).globalSymbolFunction x ξ = a • (L j).globalSymbolFunction x ξ
    simp only [PseudodifferentialPiece.globalSymbolFunction, L',
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, Pi.smul_apply]
    split_ifs <;> simp only [smul_zero, smul_smul, mul_comm]
  rw [(P.smul a).principalSymbol_eq_of_representation N L' hrep,
    P.principalSymbol_eq_of_representation N L ⟨K, hK⟩]
  simp only [hglobal, ← Finset.smul_sum, map_smul]

/-- Vanishing of the principal class is exactly membership in the next lower PDO order. -/
theorem principalSymbol_eq_zero_iff :
    P.principalSymbol = 0 ↔ IsPseudodifferentialOperator E F μ (m - 1) P.toLinearMap := by
  /- Forward, stage 1: localize a finite representation of P near the diagonal
  in common base charts and frames. Combine overlapping terms into the exact
  local full symbol before testing its order. Vanishing of the global class
  implies that this combined symbol is in S^(m-1), by local quotient detection
  and the N=1 coordinate/frame and cutoff comparisons.
  Stage 2: a finite partition and nested cutoffs yield local pieces of order m-1;
  each off-diagonal piece is also lower order by the N=1 cutoff expansion, while
  the original remainder retains its actual smooth kernel. Thus the same section
  operator belongs to Ψ^(m-1). Individual original summands need not
  have lower order: cancellation is used only after combining their local symbols.
  Reverse: promote an order-(m-1) representation to order m. Its symbol sum lies
  in the lower-order submodule, so its principal class vanishes. No homogeneity or
  ellipticity is required, and a one-order loss is not infinite smoothing. -/
  classical
  -- Stage 1: retain the exact cutoff operator when its full symbol has lower order.
  have hpieceLower {m l : ℝ}
      (R : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
      (hR : IsSymbol Set.univ l (cutoffSymbol R.output.cutoff R.input.cutoff R.symbol)) :
      IsPseudodifferentialOperator E F μ l R.toLinearMap := by
    let := R.input.frame_mem_atlas
    let := R.output.frame_mem_atlas
    let X := EuclideanSpace ℝ (Fin n)
    let U := R.chart.target ∩ R.chart.symm ⁻¹' (R.input.frame.baseSet ∩ R.output.frame.baseSet)
    let K := tsupport R.output.cutoff ∪ tsupport R.input.cutoff
    have hU : IsOpen U := R.chart.isOpen_inter_preimage_symm
      (R.input.frame.open_baseSet.inter R.output.frame.open_baseSet)
    have hK : IsCompact K := R.output.compact_support.union R.input.compact_support
    have hKU : K ⊆ U := by
      intro z hz
      rcases hz with hz | hz
      · exact ⟨(R.output.support_subset hz).1, R.output_support_in_input_frame hz,
          (R.output.support_subset hz).2⟩
      · exact ⟨(R.input.support_subset hz).1, (R.input.support_subset hz).2,
          R.input_support_in_output_frame hz⟩
    obtain ⟨O, hOo, hKO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    obtain ⟨δ, hδ, _, hsδ, honeδ⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hOo hK.isClosed hKO
    have hδsupport : tsupport δ = closure O := congrArg closure hsδ
    have hcδ : HasCompactSupport δ := by simpa [HasCompactSupport, hδsupport] using hOc
    have hδU : tsupport δ ⊆ U := by rwa [hδsupport]
    have hδone (z : X) (hz : z ∈ K) : δ z = 1 := (honeδ z).mp hz
    let A : BundleChartCutoff (r := r) E R.chart :=
      { frame := R.input.frame
        frame_mem_atlas := R.input.frame_mem_atlas
        cutoff := δ
        smooth_cutoff := hδ
        compact_support := hcδ
        support_subset := fun z hz ↦ ⟨(hδU hz).1, (hδU hz).2.1⟩ }
    let B : BundleChartCutoff (r := q) F R.chart :=
      { frame := R.output.frame
        frame_mem_atlas := R.output.frame_mem_atlas
        cutoff := δ
        smooth_cutoff := hδ
        compact_support := hcδ
        support_subset := fun z hz ↦ ⟨(hδU hz).1, (hδU hz).2.2⟩ }
    let L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F l :=
      { chart := R.chart
        chart_mem_atlas := R.chart_mem_atlas
        input := A
        output := B
        input_support_in_output_frame := fun z hz ↦ (hδU hz).2.2
        output_support_in_input_frame := fun z hz ↦ (hδU hz).2.1
        operator := R.coordinateOperator
        symbol := cutoffSymbol R.output.cutoff R.input.cutoff R.symbol
        isSymbol := hR
        operator_apply := R.coordinateOperator_eq_quantize }
    have hg : (fun z ↦ (R.input.cutoff z : ℂ)).HasTemperateGrowth :=
      (R.input.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp R.input.smooth_cutoff)
    have hinput (u : smoothSections (n := n) (r := r) E) :
        SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
          (fun z ↦ (R.input.cutoff z : ℂ)) (A.localize R.chart_mem_atlas u) =
            R.input.localize R.chart_mem_atlas u := by
      apply SchwartzMap.ext
      intro z
      rw [SchwartzMap.smulLeftCLM_apply_apply hg]
      change (R.input.cutoff z : ℂ) • A.localizedFunction u z = R.input.localizedFunction u z
      by_cases hz : z ∈ tsupport R.input.cutoff
      · have hzt := (R.input.support_subset hz).1
        have hone : δ z = 1 := hδone z (Or.inr hz)
        simp only [BundleChartCutoff.localizedFunction, hzt, ↓reduceIte]
        change (R.input.cutoff z : ℂ) • ((δ z : ℂ) • _) = _
        rw [hone, Complex.ofReal_one, one_smul]
      · simp [BundleChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
    have heq : L.toLinearMap = R.toLinearMap := by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext x
      change B.extendedFunction (R.coordinateOperator (A.localize R.chart_mem_atlas u)) x =
        R.output.extendedFunction (R.operator (R.input.localize R.chart_mem_atlas u)) x
      by_cases hx : x ∈ R.chart.source
      · simp only [BundleChartCutoff.extendedFunction, hx, ↓reduceIte]
        change (δ (R.chart x) : ℂ) • R.output.frame.symmL ℂ x
          (R.coordinateOperator (A.localize R.chart_mem_atlas u) (R.chart x)) = _
        rw [R.coordinateOperator_apply, hinput, ← Complex.coe_smul, map_smul, smul_smul]
        by_cases hz : R.chart x ∈ tsupport R.output.cutoff
        · rw [hδone _ (Or.inl hz), Complex.ofReal_one, one_mul]
        · simp [image_eq_zero_of_notMem_tsupport hz]
      · simp only [BundleChartCutoff.extendedFunction, hx, ↓reduceIte]
    rw [← heq]
    exact L.isPseudodifferentialOperator l
  -- Stage 2: disjoint scalar cutoffs annihilate the leading diagonal symbol.
  have hoffDiagonal {m : ℝ}
      (R : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
      (φ ψ : M → ℝ) (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ φ)
      (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ)
      (hzero : ∀ x, φ x * ψ x = 0) :
      IsPseudodifferentialOperator E F μ (m - 1)
        ((smoothSectionMul F (fun x ↦ (φ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hφ)).comp
          (R.toLinearMap.comp
            (smoothSectionMul E (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ)))) := by
    let X := EuclideanSpace ℝ (Fin n)
    let I := 𝓘(ℝ, X)
    let T := smoothSectionMul (n := n) (r := r) E (fun x ↦ (ψ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hψ)
    let S := smoothSectionMul (n := n) (r := q) F (fun x ↦ (φ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hφ)
    have hcutoff (a : X → ℝ) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ R.chart.target)
        (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ) ∞ χ) :
        ContDiff ℝ ∞ (fun z ↦ a z * χ (R.chart.symm z)) := by
      apply contDiff_iff_contDiffAt.mpr
      intro z
      by_cases hz : z ∈ tsupport a
      · have hchart := contMDiffAt_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I) (n := ∞) R.chart_mem_atlas) (hs hz)
        exact ha.contDiffAt.mul ((hχ.contMDiffAt.comp z hchart).contDiffAt)
      · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hz] with y hy
        simp [image_eq_zero_of_notMem_tsupport hy]
    let A : BundleChartCutoff (r := r) E R.chart :=
      { R.input with
        cutoff := fun z ↦ R.input.cutoff z * ψ (R.chart.symm z)
        smooth_cutoff := hcutoff _ R.input.smooth_cutoff
          (fun z hz ↦ (R.input.support_subset hz).1) ψ hψ
        compact_support := R.input.compact_support.of_isClosed_subset isClosed_closure
          tsupport_mul_subset_left
        support_subset := tsupport_mul_subset_left.trans R.input.support_subset }
    let B : BundleChartCutoff (r := q) F R.chart :=
      { R.output with
        cutoff := fun z ↦ R.output.cutoff z * φ (R.chart.symm z)
        smooth_cutoff := hcutoff _ R.output.smooth_cutoff
          (fun z hz ↦ (R.output.support_subset hz).1) φ hφ
        compact_support := R.output.compact_support.of_isClosed_subset isClosed_closure
          tsupport_mul_subset_left
        support_subset := tsupport_mul_subset_left.trans R.output.support_subset }
    let L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
      { R with input := A, output := B
               input_support_in_output_frame :=
                 tsupport_mul_subset_left.trans R.input_support_in_output_frame
               output_support_in_input_frame :=
                 tsupport_mul_subset_left.trans R.output_support_in_input_frame }
    have hinput (u : smoothSections (n := n) (r := r) E) :
        A.localize R.chart_mem_atlas u = R.input.localize R.chart_mem_atlas (T u) := by
      apply SchwartzMap.ext
      intro z
      by_cases hz : z ∈ tsupport R.input.cutoff
      · have hzc := (R.input.support_subset hz).1
        have hzf := (R.input.support_subset hz).2
        let := R.input.frame_mem_atlas
        change A.localizedFunction u z = R.input.localizedFunction (T u) z
        simp only [BundleChartCutoff.localizedFunction, hzc, ↓reduceIte]
        change ((R.input.cutoff z * ψ (R.chart.symm z) : ℝ) : ℂ) •
          (R.input.frame.linearEquivAt ℂ (R.chart.symm z) hzf) (u.val (R.chart.symm z)) =
          (R.input.cutoff z : ℂ) • (R.input.frame.linearEquivAt ℂ (R.chart.symm z) hzf)
            ((ψ (R.chart.symm z) : ℂ) • u.val (R.chart.symm z))
        rw [map_smul, Complex.ofReal_mul, smul_smul]
      · simp [BundleChartCutoff.localize, BundleChartCutoff.localizedFunction,
          A, image_eq_zero_of_notMem_tsupport hz]
    have houtput (v : 𝓢(X, EuclideanSpace ℂ (Fin q))) :
        B.extend R.chart_mem_atlas v = S (R.output.extend R.chart_mem_atlas v) := by
      apply Subtype.ext
      funext x
      change B.extendedFunction v x = (φ x : ℂ) • R.output.extendedFunction v x
      by_cases hx : x ∈ R.chart.source
      · simp only [BundleChartCutoff.extendedFunction, hx, ↓reduceIte]
        dsimp only [B]
        rw [R.chart.left_inv hx, Complex.ofReal_mul, smul_smul, mul_comm]
      · simp [BundleChartCutoff.extendedFunction, hx]
    have heq : L.toLinearMap = S.comp (R.toLinearMap.comp T) := by
      apply LinearMap.ext
      intro u
      change B.extend R.chart_mem_atlas (R.operator (A.localize R.chart_mem_atlas u)) = _
      rw [hinput, houtput]
      rfl
    have hsymbol : IsSymbol Set.univ (m - 1) (cutoffSymbol B.cutoff A.cutoff R.symbol) := by
      have h := hasSymbolExpansion_cutoffSymbol m R.symbol R.isSymbol
        B.cutoff A.cutoff B.smooth_cutoff A.smooth_cutoff B.compact_support A.compact_support 1
      have hdiag : (fun x ξ ↦ cutoffAmplitude B.cutoff A.cutoff R.symbol x x ξ) = 0 := by
        funext x ξ
        have hz : B.cutoff x * A.cutoff x = 0 := by
          change (R.output.cutoff x * φ (R.chart.symm x)) *
            (R.input.cutoff x * ψ (R.chart.symm x)) = 0
          calc
            _ = (R.output.cutoff x * R.input.cutoff x) *
                (φ (R.chart.symm x) * ψ (R.chart.symm x)) := by ring
            _ = 0 := by rw [hzero, mul_zero]
        simp only [cutoffAmplitude, Pi.zero_apply, hz, zero_smul]
      simpa only [Nat.cast_one, Finset.sum_range_one, amplitudeExpansionTerm_zero,
        hdiag, sub_zero] using h
    rw [← heq]
    exact hpieceLower L hsymbol
  -- Stage 3: a local lower-order symbol realizes the exact doubly localized action.
  have hnearDiagonal {l : ℝ}
      (T : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
      (hAB : A.cutoff = B.cutoff)
      (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
      (hχc : tsupport χ ⊆ c.source)
      (hone : ∀ y ∈ c '' tsupport χ, A.cutoff y = 1)
      (V : Set (EuclideanSpace ℝ (Fin n))) (hV : IsOpen V)
      (hVone : ∀ y ∈ V, χ (c.symm y) = 1)
      (p : SymbolFunction n r q) (hp : IsSymbol V l p)
      (hact : ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) y,
        quantize p u y = B.localize hc
          (smoothSectionMul F (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
            (T (smoothSectionMul E (fun x ↦ (χ x : ℂ))
              (Complex.ofRealCLM.contMDiff.comp hχ) (A.extend hc u)))) y)
      (φ : M → ℝ) (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ φ)
      (hφsupp : tsupport φ ⊆ c.source ∩ c ⁻¹' V) :
      IsPseudodifferentialOperator E F μ l
        ((smoothSectionMul F (fun x ↦ (φ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hφ)).comp
          (T.comp (smoothSectionMul E (fun x ↦ (χ x : ℂ))
            (Complex.ofRealCLM.contMDiff.comp hχ)))) := by
    let := A.frame_mem_atlas
    let := B.frame_mem_atlas
    let Tin := smoothSectionMul (n := n) (r := r) E (fun x ↦ (χ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hχ)
    let Tout := smoothSectionMul (n := n) (r := q) F (fun x ↦ (χ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hχ)
    let S := smoothSectionMul (n := n) (r := q) F (fun x ↦ (φ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hφ)
    have hcφ : HasCompactSupport φ := isCompact_univ.of_isClosed_subset
      (isClosed_tsupport φ) (Set.subset_univ _)
    obtain ⟨a, ha, hca, hs, heval⟩ := coordinate_cutoff_exists c hc φ hφ hcφ
      (fun x hx ↦ (hφsupp hx).1)
    have haV : tsupport a ⊆ V := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hs hz
      exact (hφsupp hx).2
    let p' := zeroExtendedSymbol V a p
    have hp' : IsSymbol Set.univ l p' := isSymbol_zeroExtendedSymbol V hV l a ha hca haV p hp
    have hcp' : HasCompactSupport p' := hasCompactSupport_zeroExtendedSymbol V a p hca
    let L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F l :=
      { chart := c
        chart_mem_atlas := hc
        input := A
        output := B
        input_support_in_output_frame := by
          intro z hz
          exact (B.support_subset (by rwa [hAB] at hz)).2
        output_support_in_input_frame := by
          intro z hz
          exact (A.support_subset (by rwa [← hAB] at hz)).2
        operator := quantizeSchwartz l p' hp' hcp'
        symbol := p'
        isSymbol := hp'
        operator_apply := quantizeSchwartz_apply l p' hp' hcp' }
    have hrow (z η : EuclideanSpace ℝ (Fin n)) : p' z η = (a z : ℂ) • p z η := by
      by_cases hz : z ∈ V
      · exact zeroExtendedSymbol_apply_of_mem V a p z η hz
      · have haz : a z = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (haV h))
        simp [p', zeroExtendedSymbol, hz, haz]
    have hquant (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) z :
        quantize p' u z = (a z : ℂ) • quantize p u z := by
      simp only [quantize, hrow, smul_apply]
      simp_rw [smul_comm _ (a z : ℂ)]
      rw [integral_smul, smul_comm]
    have hinput (u : smoothSections (n := n) (r := r) E) :
        Tin (A.extend hc (A.localize hc u)) = Tin u := by
      apply Subtype.ext
      funext x
      change (χ x : ℂ) • A.extendedFunction (A.localize hc u) x = (χ x : ℂ) • u.val x
      by_cases hx : χ x = 0
      · simp [hx]
      · have hxχ : x ∈ tsupport χ := subset_tsupport χ hx
        have hxc := hχc hxχ
        have hcut : A.cutoff (c x) = 1 := hone _ ⟨x, hxχ, rfl⟩
        have hxs : c x ∈ tsupport A.cutoff := subset_tsupport _
          (show A.cutoff (c x) ≠ 0 by rw [hcut]; norm_num)
        have hxf : x ∈ A.frame.baseSet := by
          have h := (A.support_subset hxs).2
          change c.symm (c x) ∈ A.frame.baseSet at h
          rwa [c.left_inv hxc] at h
        simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte, hcut,
          Complex.ofReal_one, one_smul]
        change (χ x : ℂ) • A.frame.symmL ℂ x (A.localizedFunction u (c x)) = _
        simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
          hcut, Complex.ofReal_one, one_smul]
        have hcoord : sectionInChart E c A.frame u.val (c x) =
            (A.frame ⟨x, u.val x⟩).2 := by
          unfold sectionInChart
          congr 2
          exact congrArg (fun y ↦ (⟨y, u.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
            (c.left_inv hxc)
        rw [hcoord, A.frame.symmL_apply hxf]
        exact congrArg ((χ x : ℂ) • ·)
          ((A.frame.linearEquivAt ℂ x hxf).symm_apply_apply (u.val x))
    have heq : L.toLinearMap = S.comp (T.comp Tin) := by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext x
      change B.extendedFunction (L.operator (A.localize hc u)) x = (φ x : ℂ) • (T (Tin u)).val x
      by_cases hx : φ x = 0
      · rw [hx, Complex.ofReal_zero, zero_smul]
        by_cases hxc : x ∈ c.source
        · simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
          rw [L.operator_apply, hquant, heval, ite_eq_left (c.map_source hxc), c.left_inv hxc, hx]
          simp
        · simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
      · have hxs := subset_tsupport φ hx
        have hxc := (hφsupp hxs).1
        have hxV := (hφsupp hxs).2
        have hxχ : χ x = 1 := by simpa only [c.left_inv hxc] using hVone (c x) hxV
        have hxχs : x ∈ tsupport χ := subset_tsupport _ (show χ x ≠ 0 by rw [hxχ]; norm_num)
        have hcut : B.cutoff (c x) = 1 := by rw [← hAB]; exact hone _ ⟨x, hxχs, rfl⟩
        have hxf : x ∈ B.frame.baseSet := by
          have h := (B.support_subset (subset_tsupport _ (show B.cutoff (c x) ≠ 0 by
            rw [hcut]; norm_num))).2
          change c.symm (c x) ∈ B.frame.baseSet at h
          rwa [c.left_inv hxc] at h
        apply (B.frame.linearEquivAt ℂ x hxf).injective
        have h := L.toLinearMap_in_frame u x hxc hxf
        change (B.frame.linearEquivAt ℂ x hxf) _ = _ at h
        rw [hquant, heval, ite_eq_left (c.map_source hxc), c.left_inv hxc, hcut,
          Complex.ofReal_one, one_smul, hact] at h
        change _ = (φ x : ℂ) • B.localizedFunction (Tout (T (Tin (A.extend hc (A.localize hc u)))))
          (c x) at h
        rw [hinput] at h
        simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
          hcut, Complex.ofReal_one, one_smul] at h
        have hcoord : sectionInChart F c B.frame (Tout (T (Tin u))).val (c x) =
            (B.frame ⟨x, (Tout (T (Tin u))).val x⟩).2 := by
          unfold sectionInChart
          congr 2
          exact congrArg (fun y ↦
            (⟨y, (Tout (T (Tin u))).val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin q)) F))
            (c.left_inv hxc)
        rw [hcoord] at h
        change _ = (φ x : ℂ) • (B.frame.linearEquivAt ℂ x hxf)
          ((χ x : ℂ) • (T (Tin u)).val x) at h
        rw [hxχ, Complex.ofReal_one, one_smul] at h
        rw [map_smul]
        exact h
    rw [← heq]
    exact L.isPseudodifferentialOperator l
  -- Stage 4: combine overlapping symbols, then glue by a finite output partition.
  have hfamilyLower {m : ℝ} {N : ℕ}
      (J : Fin N → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
      (hglobal : IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1)
        (∑ j, (J j).globalSymbol).val) :
      IsPseudodifferentialOperator E F μ (m - 1) (∑ j, (J j).toLinearMap) := by
    let T := ∑ j, (J j).toLinearMap
    -- Combine the symbols of all overlapping pieces before using cancellation.
    have hlocal (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ∀ (φ : M → ℝ) (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ φ),
          tsupport φ ⊆ U → IsPseudodifferentialOperator E F μ (m - 1)
            ((smoothSectionMul F (fun y ↦ (φ y : ℂ))
              (Complex.ofRealCLM.contMDiff.comp hφ)).comp T) := by
      let c := chartAt (EuclideanSpace ℝ (Fin n)) x
      let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
      let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
      have hxc : x ∈ c.source := mem_chart_source _ x
      have hz : c x ∈ symbolChartDomain E F c e f := by
        refine ⟨⟨c.map_source hxc, ?_⟩, ?_⟩ <;>
          simpa only [Set.mem_preimage, c.left_inv hxc] using
            mem_baseSet_trivializationAt _ _ x
      obtain ⟨χ, hχ, A, B, V, p, _, hχsupp, _, _, hAB, hone,
        hVone, hV, hxV, hVD, hp, hdiff, hact⟩ :=
        exists_common_local_symbols_with_cutoffs J c (chart_mem_atlas _ x) e f (c x) hz
      let Tin := smoothSectionMul (n := n) (r := r) E (fun y ↦ (χ y : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hχ)
      let Tout := smoothSectionMul (n := n) (r := q) F (fun y ↦ (χ y : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hχ)
      let pSum : SymbolFunction n r q := ∑ j, p j
      have hcoord : globalSymbolInChart E F (∑ j, (J j).globalSymbol).val c e f =
          ∑ j, globalSymbolInChart E F (J j).globalSymbolFunction c e f := by
        ext z η v
        simp [globalSymbolInChart]
        rfl
      have hpSum : IsSymbol V (m - 1) pSum := by
        have hd : IsSymbol V (m - 1)
            (∑ j, (p j - globalSymbolInChart E F (J j).globalSymbolFunction c e f)) :=
          (symbolSpace V hV (m - 1) r q).sum_mem (fun j _ ↦ hdiff j)
        have hg := (hglobal c (chart_mem_atlas _ x) e f).restrict hVD
        rw [hcoord] at hg
        have h := hd.add hV hg
        simpa only [Finset.sum_sub_distrib, sub_add_cancel] using h
      -- The finite Fourier integral is additive because every frequency integrand is Schwartz.
      have hInt (a : SymbolFunction n r q) (ha : IsSymbol Set.univ m a)
          (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
          (z : EuclideanSpace ℝ (Fin n)) :
          Integrable (fun η ↦ Complex.exp (Complex.I * (inner ℝ z η : ℂ)) •
            a z η (fourierSG u η)) := by
        let X := EuclideanSpace ℝ (Fin n)
        have hg : (a z).HasTemperateGrowth := by
          refine ⟨?_, ?_⟩
          · have hs : ContDiff ℝ ∞ (Function.uncurry a) := by
              simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
            exact hs.comp (contDiff_const.prodMk contDiff_id)
          · intro j
            obtain ⟨C, hC, hbound⟩ := ha.2 {z} (Set.subset_univ _) isCompact_singleton 0 j
            refine ⟨⌈m - (j : ℝ)⌉₊, C, fun η ↦ ?_⟩
            have h := hbound z (Set.mem_singleton z) η
            simp only [symbolDerivative, norm_iteratedFDeriv_zero] at h
            apply h.trans
            apply mul_le_mul_of_nonneg_left _ hC
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg η]) (Nat.le_ceil _)
        have hphase :
            (fun η : X ↦ Complex.exp (Complex.I * (inner ℝ z η : ℂ))).HasTemperateGrowth := by
          simpa [Function.comp_def, mul_comm] using
            Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ z).hasTemperateGrowth
        have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
          inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        let d : X ≃L[ℝ] X :=
          (LinearEquiv.smulOfNeZero ℝ X ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
        let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ d (FourierTransform.fourier u)
        exact (SchwartzMap.bilinLeftCLM
          (ContinuousLinearMap.id ℂ
            (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))).flip
            (hphase.smul hg) w).integrable
      have hquant (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) z :
          quantize pSum u z = ∑ j, quantize (p j) u z := by
        simp only [quantize, pSum, Finset.sum_apply, _root_.sum_apply,
          Finset.smul_sum]
        rw [integral_finsetSum _ (fun j _ ↦ hInt (p j) (hp j) u z), Finset.smul_sum]
      have hsumact (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) z :
          quantize pSum u z = B.localize (chart_mem_atlas _ x)
            (Tout (T (Tin (A.extend (chart_mem_atlas _ x) u)))) z := by
        rw [hquant]
        simp only [hact]
        have hlocsum (s : Finset (Fin N))
            (v : Fin N → smoothSections (n := n) (r := q) F) :
            B.localize (chart_mem_atlas _ x) (∑ j ∈ s, v j) =
              ∑ j ∈ s, B.localize (chart_mem_atlas _ x) (v j) := by
          induction s using Finset.induction_on with
          | empty =>
            simp only [Finset.sum_empty]
            simpa only [zero_smul] using B.localize_smul (chart_mem_atlas _ x) (0 : ℂ) 0
          | @insert j s hj ih =>
            simp only [Finset.sum_insert hj, B.localize_add, ih]
        simp only [T, LinearMap.sum_apply, map_sum, hlocsum, _root_.sum_apply]
        rfl
      refine ⟨c.source ∩ c ⁻¹' V, c.isOpen_inter_preimage hV, ⟨hxc, hxV⟩, ?_⟩
      intro φ hφ hφsupp
      let S := smoothSectionMul (n := n) (r := q) F (fun y ↦ (φ y : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hφ)
      let hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ (fun y ↦ 1 - χ y) :=
        contMDiff_const.sub hχ
      let Tin' := smoothSectionMul (n := n) (r := r) E (fun y ↦ ((1 - χ y : ℝ) : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hψ)
      have hnear : IsPseudodifferentialOperator E F μ (m - 1) (S.comp (T.comp Tin)) :=
        hnearDiagonal T c (chart_mem_atlas _ x) A B hAB χ hχ
          (fun y hy ↦ (hχsupp hy).1.1) hone V hV hVone pSum hpSum hsumact φ hφ hφsupp
      have hzero (y : M) : φ y * (1 - χ y) = 0 := by
        by_cases hy : φ y = 0
        · simp [hy]
        · have hs := hφsupp (subset_tsupport _ hy)
          have hχy : χ y = 1 := by
            simpa only [c.left_inv hs.1] using hVone (c y) hs.2
          simp [hχy]
      have hfar : IsPseudodifferentialOperator E F μ (m - 1) (S.comp (T.comp Tin')) := by
        have hj (j : Fin N) : IsPseudodifferentialOperator E F μ (m - 1)
            (S.comp ((J j).toLinearMap.comp Tin')) :=
          hoffDiagonal (J j) φ (fun y ↦ 1 - χ y) hφ hψ hzero
        have h := (pseudodifferentialSpace E F μ (m - 1)).sum_mem
          (t := Finset.univ) (fun j _ ↦ hj j)
        have heq : S.comp (T.comp Tin') = ∑ j, S.comp ((J j).toLinearMap.comp Tin') := by
          ext u
          simp only [LinearMap.comp_apply, T, LinearMap.sum_apply, map_sum]
        rw [heq]
        exact h
      have hsplit : S.comp T = S.comp (T.comp Tin) + S.comp (T.comp Tin') := by
        have hin : Tin + Tin' = LinearMap.id := by
          ext u y
          change (χ y : ℂ) • u.val y + ((1 - χ y : ℝ) : ℂ) • u.val y = u.val y
          rw [← add_smul, ← Complex.ofReal_add]
          simp
        rw [← LinearMap.comp_add, ← LinearMap.comp_add, hin, LinearMap.comp_id]
      rw [hsplit]
      exact IsPseudodifferentialOperator.add (m - 1) _ _ hnear hfar
    -- A finite smooth output partition glues the exact local lower-order maps.
    choose U hU hxU hcut using hlocal
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
      (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩)
    let index : Fin s.card ≃ s := s.equivFin.symm
    let V (j : Fin s.card) := U (index j)
    have hcover : Set.univ ⊆ ⋃ j, V j := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
      exact Set.mem_iUnion.mpr ⟨index.symm ⟨y, hy⟩, by simpa [V] using hxy⟩
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ V
      (fun j ↦ hU (index j)) hcover
    let L (j : Fin s.card) :=
      (smoothSectionMul F (fun y ↦ (ρ j y : ℂ))
        (Complex.ofRealCLM.contMDiff.comp (ρ j).contMDiff)).comp T
    have hL (j : Fin s.card) : IsPseudodifferentialOperator E F μ (m - 1) (L j) :=
      hcut (index j) (ρ j) (ρ j).contMDiff (hρ j)
    have hsum : (∑ j, L j) = T := by
      ext u y
      simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
      change (∑ j, (ρ j y : ℂ) • (T u).val y) = (T u).val y
      rw [← Finset.sum_smul, ← Complex.ofReal_sum, ← finsum_eq_sum_of_fintype,
        ρ.sum_eq_one (Set.mem_univ y)]
      simp
    change IsPseudodifferentialOperator E F μ (m - 1) T
    rw [← hsum]
    exact (pseudodifferentialSpace E F μ (m - 1)).sum_mem (fun j _ ↦ hL j)
  -- Apply the preceding construction to the original finite representation and kernel.
  constructor
  · intro hP
    obtain ⟨N, J, K, hK⟩ := P.isPseudodifferentialOperator
    have hg : IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1)
        (∑ j, (J j).globalSymbol).val := by
      apply (globalPrincipalSymbolClass_eq_zero_iff E F m _).mp
      rw [← P.principalSymbol_eq_of_representation N J ⟨K, hK⟩]
      exact hP
    have hsum := hfamilyLower J hg
    have hrem := IsSmoothingOperator.isPseudodifferentialOperator (m - 1)
      (K.toLinearMap μ) ⟨K, rfl⟩
    have heq : P.toLinearMap = (∑ j, (J j).toLinearMap) + K.toLinearMap μ := by
      rw [hK]
      abel
    rw [heq]
    exact IsPseudodifferentialOperator.add (m - 1) _ _ hsum hrem
  · intro hP
    obtain ⟨N, L, hL⟩ := hP
    let L' (j : Fin N) : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
      { L j with isSymbol := (L j).isSymbol.mono (by linarith) }
    rw [P.principalSymbol_eq_of_representation N L' hL]
    apply (globalPrincipalSymbolClass_eq_zero_iff E F m _).mpr
    have hsame (j : Fin N) : (L' j).globalSymbol.val = (L j).globalSymbol.val := rfl
    simp only [Submodule.coe_sum, hsame]
    have hlow := (∑ j, (L j).globalSymbol).property
    change IsGlobalSymbol E F (m - 1) (∑ j, (L j).globalSymbol).val at hlow
    simpa only [Submodule.coe_sum] using hlow

/-- Equality of principal classes is precisely a one-order improvement of the actual difference. -/
theorem principalSymbol_eq_iff :
    P.principalSymbol = Q.principalSymbol ↔
      IsPseudodifferentialOperator E F μ (m - 1) (P.toLinearMap - Q.toLinearMap) := by
  /- Represent the difference by P.add (Q.smul (-1)). Linearity identifies its
  principal class with the difference of the original classes. Apply the preceding
  zero criterion. The section map is exactly P-Q, not a chosen equivalent map. -/
  have h := (P.add (Q.smul (-1))).principalSymbol_eq_zero_iff
  rw [principalSymbol_add, principalSymbol_smul] at h
  simpa only [neg_smul, one_smul, ← sub_eq_add_neg, sub_eq_zero, add, smul] using h

end PseudodifferentialOperator

variable (E F μ)

/-- The complex-linear principal-symbol map on the actual order-m PDO module. -/
def principalSymbolLinearMap (m : ℝ) :
    pseudodifferentialSpace (n := n) (r := r) (q := q) E F μ m →ₗ[ℂ]
      GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m where
  toFun := fun P ↦ (pseudodifferentialOperatorOfSpace P).principalSymbol
  map_add' := fun P Q ↦ (pseudodifferentialOperatorOfSpace P).principalSymbol_add
    (pseudodifferentialOperatorOfSpace Q)
  map_smul' := fun a P ↦ (pseudodifferentialOperatorOfSpace P).principalSymbol_smul a

/-- The principal-symbol kernel is the lower-order PDO submodule inside Ψ^m. -/
theorem ker_principalSymbolLinearMap (m : ℝ) :
    (principalSymbolLinearMap (n := n) (r := r) (q := q) E F μ m).ker =
      (pseudodifferentialSpace (n := n) (r := r) (q := q) E F μ (m - 1)).comap
        (pseudodifferentialSpace (n := n) (r := r) (q := q) E F μ m).subtype := by
  /- For each element of Ψ^m, kernel membership says its actual principal class
  vanishes. The preceding zero criterion identifies this with order-(m-1)
  membership of its underlying section map, exactly the displayed comap. -/
  ext P
  exact (pseudodifferentialOperatorOfSpace P).principalSymbol_eq_zero_iff

/-- The linear principal-symbol map is surjective by the constructed global quantization. -/
theorem principalSymbolLinearMap_surjective (m : ℝ) :
    Function.Surjective (principalSymbolLinearMap (n := n) (r := r) (q := q) E F μ m) := by
  /- Realize the desired principal class by the global quantization surjectivity
  theorem. Pass the resulting bundled PDO to its actual submodule element with
  toSpace; rebundling preserves both the map and its defining property. -/
  intro σ
  obtain ⟨P, hP⟩ := PseudodifferentialOperator.principalSymbol_surjective
    (E := E) (F := F) μ m σ
  exact ⟨P.toSpace, hP⟩

/-- The first-isomorphism equivalence for the principal symbol of actual operators. -/
def pseudodifferentialPrincipalSymbolEquiv (m : ℝ) :
    (pseudodifferentialSpace (n := n) (r := r) (q := q) E F μ m ⧸
      (principalSymbolLinearMap (n := n) (r := r) (q := q) E F μ m).ker) ≃ₗ[ℂ]
        GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m :=
  (principalSymbolLinearMap E F μ m).quotKerEquivOfSurjective
    (principalSymbolLinearMap_surjective E F μ m)

/-- The quotient equivalence sends an actual operator class to its actual principal class. -/
theorem pseudodifferentialPrincipalSymbolEquiv_mk (m : ℝ)
    (P : pseudodifferentialSpace (n := n) (r := r) (q := q) E F μ m) :
    pseudodifferentialPrincipalSymbolEquiv E F μ m (Submodule.Quotient.mk P) =
      principalSymbolLinearMap E F μ m P := by
  /- This is the application rule for mathlib's first-isomorphism equivalence.
  The separately stated kernel formula identifies the quotient with loss of
  precisely one PDO order; no homogeneous representative is chosen. -/
  rfl

variable {E F μ}

/-- Fixed-presentation quantization as a linear map into the actual PDO submodule. -/
def QuantizationPresentation.quantizationSpaceLinearMap
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ] (m : ℝ) :
    globalSymbolSpace (n := n) (r := r) (q := q) E F m →ₗ[ℂ]
      pseudodifferentialSpace (n := n) (r := r) (q := q) E F μ m :=
  A.quantizationLinearMap.codRestrict (pseudodifferentialSpace E F μ m)
    (fun p ↦ A.isPseudodifferentialOperator_toLinearMap μ p)

/-- Quantization lifts the symbol quotient projection at the level of linear maps. -/
theorem QuantizationPresentation.principalSymbolLinearMap_comp_quantization
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ] (m : ℝ) :
    (principalSymbolLinearMap E F μ m).comp (A.quantizationSpaceLinearMap μ m) =
      globalPrincipalSymbolClass E F m := by
  /- Evaluate both linear maps on a genuine symbol p. The constructed PDO
  is A.quantize μ p on its actual section action, so principalSymbol_quantize
  computes exactly the right-hand quotient projection. Apply linear-map extensionality. -/
  apply LinearMap.ext
  intro p
  exact A.principalSymbol_quantize μ p

end AtiyahSinger
