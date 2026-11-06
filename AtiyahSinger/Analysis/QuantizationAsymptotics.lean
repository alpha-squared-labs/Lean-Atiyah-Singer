/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialRegularity
public import AtiyahSinger.Analysis.SymbolExistence

/-!
# Asymptotic summation in a fixed quantization presentation

Public module ID: M0907.

The local symbol summation theorem, applied in each of the same finitely many
patches, gives one actual section operator with all prescribed remainders.
A fixed spatial plateau preserves each original local symbol and makes the
summed symbol a continuous Schwartz operator. This is the quantization step in
SG III.3.4 and III.3.15; it supplies no inverse or Fredholm assumption.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory
open scoped Manifold ContDiff SchwartzMap

set_option maxSynthPendingDepth 15

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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

set_option backward.isDefEq.respectTransparency false in
/-- A fixed finite quantization preserves asymptotic summability of symbol sequences. -/
theorem QuantizationPresentation.exists_pseudodifferential_expansion
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (m : ℕ → ℝ) (hm : StrictAnti m) (hlim : Tendsto m atTop atBot)
    (p : ∀ j, globalSymbolSpace (n := n) (r := r) (q := q) E F (m j)) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (m 0),
      ∀ N, IsPseudodifferentialOperator E F μ (m N)
        (Q.toLinearMap - ∑ j ∈ Finset.range N, A.toLinearMap (p j)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  -- Quantization is additive on compact symbols, independent of the chosen certificates.
  have hquantAdd (l : ℝ) (a b : SymbolFunction n r q)
      (ha : IsSymbol Set.univ l a) (hb : IsSymbol Set.univ l b)
      (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
      (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      AtiyahSinger.quantize (a + b) u x =
        AtiyahSinger.quantize a u x + AtiyahSinger.quantize b u x := by
    have h := congrArg (fun T : 𝓢(X, EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(X, EuclideanSpace ℂ (Fin q)) ↦ T u x)
      (quantizeSchwartz_add l a b ha hb hca hcb
        (ha.add isOpen_univ hb) (hca.add hcb))
    simp only [add_apply] at h
    rw [quantizeSchwartz_apply l (a + b), quantizeSchwartz_apply l a,
      quantizeSchwartz_apply l b] at h
    exact h
  -- Each patch uses one spatial plateau for the entire infinite sequence.
  have hpatch (C : QuantizationPatch (n := n) (r := r) (q := q) E F) :
      ∃ L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F (m 0),
        ∀ N, ∃ R : PseudodifferentialPiece (n := n) (r := r) (q := q) E F (m N),
          R.toLinearMap = L.toLinearMap -
            ∑ j ∈ Finset.range N, (C.toPiece (p j)).toLinearMap := by
    let a (j : ℕ) := C.localSymbol (p j).val
    have ha (j : ℕ) : IsSymbol Set.univ (m j) (a j) := C.isSymbol_localSymbol (p j)
    have hca (j : ℕ) : HasCompactSupport (a j) := C.hasCompactSupport_localSymbol (p j).val
    obtain ⟨b, hb⟩ := exists_symbol_expansion Set.univ isOpen_univ m hm hlim a ha
    obtain ⟨O, hO, hKO, _, hOc⟩ := exists_open_between_and_isCompact_closure
      C.output.compact_support isOpen_univ (Set.subset_univ _)
    obtain ⟨δ, hδ, _, hsδ, honeδ⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hO (isClosed_tsupport C.output.cutoff) hKO
    have hcδ : HasCompactSupport δ := by
      simpa only [HasCompactSupport, tsupport, hsδ] using hOc
    have hδone (x : X) (hx : x ∈ tsupport C.output.cutoff) : δ x = 1 :=
      (honeδ x).mp hx
    let clip (a : SymbolFunction n r q) := zeroExtendedSymbol Set.univ δ a
    have hclip {l : ℝ} {a : SymbolFunction n r q} (ha : IsSymbol Set.univ l a) :
        IsSymbol Set.univ l (clip a) :=
      isSymbol_zeroExtendedSymbol Set.univ isOpen_univ l δ hδ hcδ (Set.subset_univ _) a ha
    have hcclip (a : SymbolFunction n r q) : HasCompactSupport (clip a) :=
      hasCompactSupport_zeroExtendedSymbol Set.univ δ a hcδ
    have hclipa (j : ℕ) : clip (a j) = a j := by
      funext x ξ
      by_cases hx : x ∈ tsupport C.output.cutoff
      · simp only [clip, zeroExtendedSymbol, Set.mem_univ, ite_true, hδone x hx,
          Complex.ofReal_one, one_smul]
      · have hzero : a j x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h ↦ hx (tsupport_zeroExtendedSymbol_subset _ _ _ h))
        simp only [clip, zeroExtendedSymbol, Set.mem_univ, ite_true, hzero,
          Pi.zero_apply, smul_zero]
    let s (N : ℕ) : SymbolFunction n r q := ∑ j ∈ Finset.range N, a j
    have hs (N : ℕ) : IsSymbol Set.univ (m 0) (s N) := by
      change s N ∈ symbolSpace Set.univ isOpen_univ (m 0) r q
      exact (symbolSpace Set.univ isOpen_univ (m 0) r q).sum_mem
        fun j _ ↦ (ha j).mono (hm.antitone (Nat.zero_le j))
    have hcs (N : ℕ) : HasCompactSupport (s N) := by
      induction N with
      | zero => simp [s, HasCompactSupport]
      | succ N hN => simpa only [s, Finset.sum_range_succ] using hN.add (hca N)
    have hclipS (N : ℕ) : clip (s N) = s N := by
      funext x ξ
      simp only [clip, zeroExtendedSymbol, Set.mem_univ, ite_true, s,
        Finset.sum_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simpa only [clip, zeroExtendedSymbol, Set.mem_univ, ite_true] using
        congrFun (congrFun (hclipa j) x) ξ
    let c := clip b
    let d (N : ℕ) := clip (b - s N)
    have hc : IsSymbol Set.univ (m 0) c := by
      apply hclip
      simpa only [HasSymbolExpansion, Finset.range_zero, Finset.sum_empty, sub_zero] using hb 0
    have hd (N : ℕ) : IsSymbol Set.univ (m N) (d N) := hclip (hb N)
    have hdeq (N : ℕ) : d N = c - s N := by
      have heq : clip (b - s N) = clip b - clip (s N) := by
        funext x ξ
        simp [clip, zeroExtendedSymbol, smul_sub]
      exact heq.trans (congrArg (fun z ↦ c - z) (hclipS N))
    let T := quantizeSchwartz (m 0) c hc (hcclip b)
    let L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F (m 0) :=
      { chart := C.chart
        chart_mem_atlas := C.chart_mem_atlas
        input := C.input
        output := C.output
        input_support_in_output_frame := C.input_support_in_output_frame
        output_support_in_input_frame := C.output_support_in_input_frame
        operator := T
        symbol := c
        isSymbol := hc
        operator_apply := quantizeSchwartz_apply (m 0) c hc (hcclip b) }
    have hsum (N : ℕ) (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
        AtiyahSinger.quantize (s N) u x =
          ∑ j ∈ Finset.range N, AtiyahSinger.quantize (a j) u x := by
      induction N with
      | zero => simp [s, AtiyahSinger.quantize]
      | succ N hN =>
        have heq : s (N + 1) = s N + a N := Finset.sum_range_succ _ N
        rw [heq, hquantAdd (m 0) (s N) (a N) (hs N)
          ((ha N).mono (hm.antitone (Nat.zero_le N))) (hcs N) (hca N),
          hN, Finset.sum_range_succ]
    refine ⟨L, fun N ↦ ?_⟩
    let R : PseudodifferentialPiece (n := n) (r := r) (q := q) E F (m N) :=
      { L with
        operator := T - ∑ j ∈ Finset.range N, (C.toPiece (p j)).operator
        symbol := d N
        isSymbol := hd N
        operator_apply := by
          intro u x
          have heq : c = d N + s N := by rw [hdeq]; abel
          have hq := hquantAdd (m 0) (d N) (s N)
            ((hd N).mono (hm.antitone (Nat.zero_le N))) (hs N)
            (hcclip (b - s N)) (hcs N) u x
          rw [← heq, hsum] at hq
          simp only [sub_apply, sum_apply, T, QuantizationPatch.toPiece, quantizeSchwartz_apply]
          change AtiyahSinger.quantize c u x -
            ∑ j ∈ Finset.range N, AtiyahSinger.quantize (a j) u x = _
          exact sub_eq_iff_eq_add.mpr hq }
    refine ⟨R, ?_⟩
    apply LinearMap.ext
    intro u
    simp only [PseudodifferentialPiece.toLinearMap, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.sum_apply, ContinuousLinearMap.coe_coe, R, L,
      QuantizationPatch.toPiece,
      sub_apply, sum_apply, map_sub, map_sum]
  -- Finite assembly commutes with every original finite partial sum.
  choose L hL using fun j ↦ hpatch (A.patch j)
  let Qmap := ∑ j, (L j).toLinearMap
  have hzero : IsSmoothingOperator μ
      (0 : smoothSections (n := n) (r := r) E →ₗ[ℂ]
        smoothSections (n := n) (r := q) F) := by
    obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
    obtain ⟨C⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
    apply (isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ 0 B C).mpr
    exact fun l ↦ isPseudodifferentialOperator_zero E F μ l
  have hQ : IsPseudodifferentialOperator E F μ (m 0) Qmap :=
    ⟨A.size, L, by simpa only [Qmap, sub_self] using hzero⟩
  refine ⟨⟨Qmap, hQ⟩, fun N ↦ ?_⟩
  choose R hR using fun j ↦ hL j N
  refine ⟨A.size, R, ?_⟩
  have heq : Qmap - ∑ k ∈ Finset.range N, A.toLinearMap (p k) =
      ∑ j, (R j).toLinearMap := by
    simp only [hR, Finset.sum_sub_distrib, Qmap, QuantizationPresentation.toLinearMap]
    congr 1
    exact Finset.sum_comm
  change IsSmoothingOperator μ
    ((Qmap - ∑ k ∈ Finset.range N, A.toLinearMap (p k)) - ∑ j, (R j).toLinearMap)
  rw [heq, sub_self]
  exact hzero

end AtiyahSinger
