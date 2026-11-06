/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialFiltration
public import AtiyahSinger.Analysis.AtlasQuantization
public import AtiyahSinger.Analysis.SymbolExistence

/-!
# Asymptotic summation in a fixed quantization presentation

Public module ID: M0297.

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

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- Equality of the actual principal classes is precisely one-order-lower difference. -/
theorem AtlasPseudodifferentialOperator.principalSymbol_eq_iff {m : ℝ}
    (P Q : AtlasPseudodifferentialOperator A B m) :
    P.principalSymbol = Q.principalSymbol ↔
      IsAtlasPseudodifferentialOperator A B (m - 1) (P.toLinearMap - Q.toLinearMap) := by
  classical
  obtain ⟨N, L, hL⟩ := P.isPseudodifferentialOperator
  obtain ⟨N', J, hJ⟩ := Q.isPseudodifferentialOperator
  -- Negate the original local coordinate operator and full symbol together.
  let J' (j : Fin N') : AtlasPseudodifferentialPiece A B m :=
    { J j with
      operator := -(J j).operator
      symbol := -(J j).symbol
      isSymbol := by
        simpa only [neg_one_smul] using (J j).isSymbol.smul isOpen_univ (-1 : ℂ)
      operator_apply := by
        intro u x
        simp only [neg_apply, (J j).operator_apply]
        simp [quantize, MeasureTheory.integral_neg] }
  have hmap (j : Fin N') : (J' j).toLinearMap = -(J j).toLinearMap := by
    apply LinearMap.ext
    intro u
    change (J j).output.extendLinearMap (J j).chart_mem_atlas
      (-((J j).operator ((J j).input.localize (J j).chart_mem_atlas u))) = _
    exact map_neg _ _
  have hsymbol (j : Fin N') : (J' j).globalSymbol = -(J j).globalSymbol := by
    apply Subtype.ext
    funext x ξ
    apply LinearMap.ext
    intro v
    change ((J' j).globalSymbolFunction x ξ) v = -((J j).globalSymbolFunction x ξ) v
    simp only [AtlasPseudodifferentialPiece.globalSymbolFunction, J']
    split_ifs <;> simp
  let R : AtlasPseudodifferentialOperator A B m :=
    ⟨P.toLinearMap - Q.toLinearMap,
      (atlasPseudodifferentialSpace A B m).sub_mem
        P.isPseudodifferentialOperator Q.isPseudodifferentialOperator⟩
  let pieces := Fin.append L J'
  have hrepr : IsAtlasSmoothingOperator A B
      (R.toLinearMap - ∑ j, (pieces j).toLinearMap) := by
    intro D H s t
    obtain ⟨T, hT⟩ := hL D H s t
    obtain ⟨S, hS⟩ := hJ D H s t
    refine ⟨T - S, ?_⟩
    intro u
    rw [sub_apply, hT, hS, ← map_sub]
    congr 1
    simp only [pieces, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      hmap, Finset.sum_neg_distrib, R, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.neg_apply]
    abel
  -- This one concatenated family calculates the difference principal class.
  have hclass : R.principalSymbol = P.principalSymbol - Q.principalSymbol := by
    rw [R.principalSymbol_eq_of_representation (N + N') pieces hrepr,
      P.principalSymbol_eq_of_representation N L hL,
      Q.principalSymbol_eq_of_representation N' J hJ]
    simp only [pieces, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      hsymbol, Finset.sum_neg_distrib, map_add, map_neg, sub_eq_add_neg]
  -- Apply the previously established zero-class criterion to this actual difference.
  have h := R.principalSymbol_eq_zero_iff
  rw [hclass, sub_eq_zero] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- A fixed finite quantization preserves asymptotic summability of symbol sequences. -/
theorem AtlasQuantizationPresentation.exists_pseudodifferential_expansion
    (C : AtlasQuantizationPresentation A B)
    (m : ℕ → ℝ) (hm : StrictAnti m) (hlim : Tendsto m atTop atBot)
    (p : ∀ j, atlasGlobalSymbolSpace A B (m j)) :
    ∃ Q : AtlasPseudodifferentialOperator A B (m 0),
      ∀ N, IsAtlasPseudodifferentialOperator A B (m N)
        (Q.toLinearMap - ∑ j ∈ Finset.range N, C.toLinearMap (p j)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  -- Quantization is additive on compact symbols, independent of the chosen certificates.
  have hquantAdd {r q : ℕ} (l : ℝ) (a b : SymbolFunction n r q)
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
  have hpatch (D : AtlasQuantizationPatch A B) :
      ∃ L : AtlasPseudodifferentialPiece A B (m 0),
        ∀ N, ∃ R : AtlasPseudodifferentialPiece A B (m N),
          R.toLinearMap = L.toLinearMap -
            ∑ j ∈ Finset.range N, (D.toPiece (p j)).toLinearMap := by
    let r := A.rank D.input.frameIndex
    let q := B.rank D.output.frameIndex
    let a (j : ℕ) := D.localSymbol (p j).val
    have ha (j : ℕ) : IsSymbol Set.univ (m j) (a j) := (D.localSymbol_properties (p j)).2
    have hca (j : ℕ) : HasCompactSupport (a j) := (D.localSymbol_properties (p j)).1
    obtain ⟨b, hb⟩ := exists_symbol_expansion Set.univ isOpen_univ m hm hlim a ha
    obtain ⟨O, hO, hKO, _, hOc⟩ := exists_open_between_and_isCompact_closure
      D.input.compact_support isOpen_univ (Set.subset_univ _)
    obtain ⟨δ, hδ, _, hsδ, honeδ⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hO (isClosed_tsupport D.input.cutoff) hKO
    have hcδ : HasCompactSupport δ := by
      simpa only [HasCompactSupport, tsupport, hsδ] using hOc
    have hδone (x : X) (hx : x ∈ tsupport D.input.cutoff) : δ x = 1 :=
      (honeδ x).mp hx
    let clip (a : SymbolFunction n r q) := zeroExtendedSymbol Set.univ δ a
    have hclip {l : ℝ} {a : SymbolFunction n r q} (ha : IsSymbol Set.univ l a) :
        IsSymbol Set.univ l (clip a) :=
      isSymbol_zeroExtendedSymbol Set.univ isOpen_univ l δ hδ hcδ (Set.subset_univ _) a ha
    have hcclip (a : SymbolFunction n r q) : HasCompactSupport (clip a) :=
      hasCompactSupport_zeroExtendedSymbol Set.univ δ a hcδ
    have hclipa (j : ℕ) : clip (a j) = a j := by
      funext x ξ
      by_cases hx : x ∈ tsupport D.input.cutoff
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
    let L : AtlasPseudodifferentialPiece A B (m 0) :=
      { chart := D.chart
        chart_mem_atlas := D.chart_mem_atlas
        input := D.input
        output := D.output
        input_support_in_output_frame := D.input_support_in_output_frame
        output_support_in_input_frame := D.output_support_in_input_frame
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
    let R : AtlasPseudodifferentialPiece A B (m N) :=
      { chart := D.chart
        chart_mem_atlas := D.chart_mem_atlas
        input := D.input
        output := D.output
        input_support_in_output_frame := D.input_support_in_output_frame
        output_support_in_input_frame := D.output_support_in_input_frame
        operator := T - ∑ j ∈ Finset.range N,
          quantizeSchwartz (m j) (a j) (ha j) (hca j)
        symbol := d N
        isSymbol := hd N
        operator_apply := by
          intro u x
          have heq : c = d N + s N := by rw [hdeq]; abel
          have hq := hquantAdd (m 0) (d N) (s N)
            ((hd N).mono (hm.antitone (Nat.zero_le N))) (hs N)
            (hcclip (b - s N)) (hcs N) u x
          rw [← heq, hsum] at hq
          simp only [sub_apply, sum_apply, T, quantizeSchwartz_apply]
          rw [quantizeSchwartz_apply (m 0) c hc (hcclip b)]
          exact sub_eq_iff_eq_add.mpr hq }
    refine ⟨R, ?_⟩
    apply LinearMap.ext
    intro u
    simp only [AtlasPseudodifferentialPiece.toLinearMap, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.sum_apply, ContinuousLinearMap.coe_coe, R, L,
      AtlasQuantizationPatch.toPiece,
      sub_apply, sum_apply, map_sub, map_sum]
    rfl
  -- Finite assembly commutes with every original finite partial sum.
  choose L hL using fun j ↦ hpatch (C.patch j)
  let Qmap := ∑ j, (L j).toLinearMap
  have hzero : IsAtlasSmoothingOperator A B
      (0 : A.smoothSections →ₗ[ℂ] B.smoothSections) := by
    intro L K s t
    exact ⟨0, fun u ↦ by simp⟩
  have hQ : IsAtlasPseudodifferentialOperator A B (m 0) Qmap :=
    ⟨C.size, L, by simpa only [Qmap, sub_self] using hzero⟩
  refine ⟨⟨Qmap, hQ⟩, fun N ↦ ?_⟩
  choose R hR using fun j ↦ hL j N
  refine ⟨C.size, R, ?_⟩
  have heq : Qmap - ∑ k ∈ Finset.range N, C.toLinearMap (p k) =
      ∑ j, (R j).toLinearMap := by
    simp only [hR, Finset.sum_sub_distrib, Qmap, AtlasQuantizationPresentation.toLinearMap]
    congr 1
    exact Finset.sum_comm
  change IsAtlasSmoothingOperator A B
    ((Qmap - ∑ k ∈ Finset.range N, C.toLinearMap (p k)) - ∑ j, (R j).toLinearMap)
  rw [heq, sub_self]
  exact hzero

end AtiyahSinger
