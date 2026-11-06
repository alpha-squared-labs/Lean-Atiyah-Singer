/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ExternalTensorBundle
public import AtiyahSinger.Geometry.WeightedFrameSection

/-!
# Finite separated generators for an external tensor bundle

Public module ID: M1231.

The original factor partitions give finitely many smooth pure tensor sections
which generate every smooth product section with smooth scalar coefficients.
The squared partition weights have a strictly positive sum, and its reciprocal
normalizes the two frame reconstructions. This is the finite-frame part of
the standard geometric L2 tensor-density argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

variable {n m r s : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  {E : M → Type*} {F : N → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := m) (r := s) F]

set_option maxHeartbeats 800000 in

/-- Weighted factor frames generate every product section with smooth scalar coefficients. -/
theorem exists_externalTensorSection_decomposition
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := m) (r := s) F) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
    ∀ w : smoothSections (n := n + m) (r := r * s) (externalTensorFiber E F),
    ∃ f : (Fin A.size × Fin r) → (Fin B.size × Fin s) → M × N → ℂ,
      (∀ i j, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) 𝓘(ℝ, ℂ) ∞ (f i j)) ∧
        ∀ z : M × N, w.val z =
          ∑ i, ∑ j, f i j z •
            ((A.weightedFrameSection i.1 (EuclideanSpace.single i.2 1)).val z.1 ⊗ₜ[ℂ]
              (B.weightedFrameSection j.1 (EuclideanSpace.single j.2 1)).val z.2) := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
  intro w
  let : ∀ i, MemTrivializationAtlas (A.frame i) := A.frame_mem_atlas
  let : ∀ j, MemTrivializationAtlas (B.frame j) := B.frame_mem_atlas
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m)))
  -- Undo the fixed concatenation before applying the smooth product projections.
  have hproj :
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (Prod.fst : M × N → M) ∧
        ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ (Prod.snd : M × N → N) := by
    let P := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)
    let J := 𝓘(ℝ, P)
    let c := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
    let : ChartedSpace P (M × N) := prodChartedSpace _ M _ N
    have hid : ContMDiff I J ∞ (id : M × N → M × N) := by
      intro z
      apply contMDiffAt_iff.mpr
      refine ⟨continuousAt_id, ?_⟩
      have heq : writtenInExtChartAt I J z (id : M × N → M × N) =ᶠ[
          nhds (extChartAt I z z)] c.symm := by
        have hmem : c.symm (extChartAt I z z) ∈ (chartAt P z).target := by
          change c.symm (c ((chartAt P z) z)) ∈ (chartAt P z).target
          rw [c.symm_apply_apply]
          exact (chartAt P z).map_source (mem_chart_source P z)
        filter_upwards [((chartAt P z).open_target.preimage c.symm.continuous).mem_nhds hmem]
          with y hy
        change (chartAt P z) ((chartAt P z).symm (c.symm y)) = c.symm y
        exact (chartAt P z).right_inv hy
      exact (c.symm.contDiff.contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt
    have hf : ContMDiff J 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (Prod.fst : M × N → M) := by
      simpa only [J, P, modelWithCornersSelf_prod] using
        (contMDiff_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (n := ∞))
    have hg : ContMDiff J 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
        (Prod.snd : M × N → N) := by
      simpa only [J, P, modelWithCornersSelf_prod] using
        (contMDiff_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (n := ∞))
    exact ⟨hf.comp hid, hg.comp hid⟩
  -- Normalize the squared weights. Their sum cannot vanish because the weights sum to one.
  let SA (x : M) : ℝ := ∑ i, A.cutoff i x ^ 2
  have hposA (x : M) : 0 < SA x := by
    have hn : ∃ i, A.cutoff i x ≠ 0 := by
      by_contra! hzero
      have hsum := A.sum_cutoff x
      simp only [hzero, Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    obtain ⟨i, hi⟩ := hn
    exact Finset.sum_pos' (fun j _ ↦ sq_nonneg (A.cutoff j x))
      ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  have hSA : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ SA := by
    apply contMDiff_finsetSum
    intro i _
    have hp : ContDiff ℝ ∞ (fun t : ℝ ↦ t ^ 2) := contDiff_id.pow 2
    exact hp.comp_contMDiff (A.smooth_cutoff i)
  let a (x : M) : ℂ := ((SA x)⁻¹ : ℝ)
  have ha : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ a :=
    Complex.ofRealCLM.contMDiff.comp (hSA.inv₀ (fun x ↦ (hposA x).ne'))
  have haone (x : M) : a x * ∑ i, (A.cutoff i x : ℂ) ^ 2 = 1 := by
    have heq : ∑ i, (A.cutoff i x : ℂ) ^ 2 = (SA x : ℂ) := by simp [SA]
    rw [heq]
    dsimp only [a]
    rw [Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hposA x).ne')]
  let SB (x : N) : ℝ := ∑ i, B.cutoff i x ^ 2
  have hposB (x : N) : 0 < SB x := by
    have hn : ∃ i, B.cutoff i x ≠ 0 := by
      by_contra! hzero
      have hsum := B.sum_cutoff x
      simp only [hzero, Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    obtain ⟨i, hi⟩ := hn
    exact Finset.sum_pos' (fun j _ ↦ sq_nonneg (B.cutoff j x))
      ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  have hSB : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ) ∞ SB := by
    apply contMDiff_finsetSum
    intro i _
    have hp : ContDiff ℝ ∞ (fun t : ℝ ↦ t ^ 2) := contDiff_id.pow 2
    exact hp.comp_contMDiff (B.smooth_cutoff i)
  let b (x : N) : ℂ := ((SB x)⁻¹ : ℝ)
  have hb : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, ℂ) ∞ b :=
    Complex.ofRealCLM.contMDiff.comp (hSB.inv₀ (fun x ↦ (hposB x).ne'))
  have hbone (x : N) : b x * ∑ i, (B.cutoff i x : ℂ) ^ 2 = 1 := by
    have heq : ∑ i, (B.cutoff i x : ℂ) ^ 2 = (SB x : ℂ) := by simp [SB]
    rw [heq]
    dsimp only [b]
    rw [Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hposB x).ne')]
  -- Select product frames from the same witness that defines the original tensor atlas.
  have hframes := (exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s)
    E F).choose_spec.choose_spec.2.1
  choose t ht hbase hpure using fun i j ↦
    hframes (A.frame i) (A.frame_mem_atlas i) (B.frame j) (B.frame_mem_atlas j)
  let c (i : Fin A.size × Fin r) (j : Fin B.size × Fin s) (z : M × N) : ℂ :=
    (A.cutoff i.1 z.1 : ℂ) * (B.cutoff j.1 z.2 : ℂ) *
      (t i.1 j.1 ⟨z, w.val z⟩).2 (finProdFinEquiv (i.2, j.2))
  let f (i : Fin A.size × Fin r) (j : Fin B.size × Fin s) (z : M × N) : ℂ :=
    (a z.1 * b z.2) * c i j z
  have hmul : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2) := contDiff_mul
  have hweights (i : Fin A.size) (j : Fin B.size) : ContMDiff I 𝓘(ℝ, ℂ) ∞
      (fun z : M × N ↦ (A.cutoff i z.1 : ℂ) * (B.cutoff j z.2 : ℂ)) :=
    hmul.contMDiff.comp
      (((Complex.ofRealCLM.contMDiff.comp (A.smooth_cutoff i)).comp hproj.1).prodMk_space
        ((Complex.ofRealCLM.contMDiff.comp (B.smooth_cutoff j)).comp hproj.2))
  have hc (i : Fin A.size × Fin r) (j : Fin B.size × Fin s) :
      ContMDiff I 𝓘(ℝ, ℂ) ∞ (c i j) := by
    intro z
    by_cases hi : z.1 ∈ tsupport (A.cutoff i.1)
    · by_cases hj : z.2 ∈ tsupport (B.cutoff j.1)
      · have hz : z ∈ (t i.1 j.1).baseSet := by
          rw [hbase]
          exact ⟨(A.support_subset i.1 hi).2, (B.support_subset j.1 hj).2⟩
        have hcoord := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin (r * s) ↦ ℂ)
          (finProdFinEquiv (i.2, j.2))).restrictScalars ℝ |>.contMDiff.comp_contMDiffOn
            (w.property (t i.1 j.1) (ht i.1 j.1))
        exact hmul.contMDiff.contMDiffAt.comp z ((hweights i.1 j.1 z).prodMk_space
          (hcoord.contMDiffAt ((t i.1 j.1).open_baseSet.mem_nhds hz)))
      · apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
          ((isClosed_tsupport (B.cutoff j.1)).isOpen_compl.mem_nhds hj)] with y hy
        simp [c, image_eq_zero_of_notMem_tsupport hy]
    · apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
        ((isClosed_tsupport (A.cutoff i.1)).isOpen_compl.mem_nhds hi)] with y hy
      simp [c, image_eq_zero_of_notMem_tsupport hy]
  refine ⟨f, ?_, ?_⟩
  · intro i j
    exact hmul.contMDiff.comp
      ((hmul.contMDiff.comp ((ha.comp hproj.1).prodMk_space (hb.comp hproj.2))).prodMk_space
        (hc i j))
  · intro z
    -- Each product frame reconstructs the original tensor vector; squared weights glue it.
    have hreconstruct (i : Fin A.size) (j : Fin B.size)
        (hi : z.1 ∈ (A.frame i).baseSet) (hj : z.2 ∈ (B.frame j).baseSet) :
        ∑ u : Fin r, ∑ v : Fin s,
          (t i j ⟨z, w.val z⟩).2 (finProdFinEquiv (u, v)) •
            ((A.frame i).symmL ℂ z.1 (EuclideanSpace.single u 1) ⊗ₜ[ℂ]
              (B.frame j).symmL ℂ z.2 (EuclideanSpace.single v 1)) = w.val z := by
      let := A.frame_mem_atlas i
      let := B.frame_mem_atlas j
      let := ht i j
      have hz : z ∈ (t i j).baseSet := by rw [hbase]; exact ⟨hi, hj⟩
      apply ((t i j).linearEquivAt ℂ z hz).injective
      simp only [map_sum, map_smul]
      apply PiLp.ext
      intro l
      obtain ⟨⟨u, v⟩, rfl⟩ := finProdFinEquiv.surjective l
      change (∑ u', ∑ v',
        (t i j ⟨z, w.val z⟩).2 (finProdFinEquiv (u', v')) •
          (t i j ⟨z, (A.frame i).symmL ℂ z.1 (EuclideanSpace.single u' 1) ⊗ₜ[ℂ]
            (B.frame j).symmL ℂ z.2 (EuclideanSpace.single v' 1)⟩).2)
              (finProdFinEquiv (u, v)) = _
      change (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin (r * s) ↦ ℂ)
        (finProdFinEquiv (u, v))) _ = _
      simp only [map_sum, map_smul]
      change (∑ u', ∑ v',
        (t i j ⟨z, w.val z⟩).2 (finProdFinEquiv (u', v')) *
          (t i j ⟨z, (A.frame i).symmL ℂ z.1 (EuclideanSpace.single u' 1) ⊗ₜ[ℂ]
            (B.frame j).symmL ℂ z.2 (EuclideanSpace.single v' 1)⟩).2
              (finProdFinEquiv (u, v))) = _
      simp_rw [hpure i j z ⟨hi, hj⟩, (A.frame i).symmL_apply hi,
        (B.frame j).symmL_apply hj]
      simp [(A.frame i).apply_mk_symm hi, (B.frame j).apply_mk_symm hj]
    have hblock (i : Fin A.size) (j : Fin B.size) :
        ∑ u : Fin r, ∑ v : Fin s,
          f (i, u) (j, v) z •
            ((A.weightedFrameSection i (EuclideanSpace.single u 1)).val z.1 ⊗ₜ[ℂ]
              (B.weightedFrameSection j (EuclideanSpace.single v 1)).val z.2) =
          ((a z.1 * b z.2) *
            ((A.cutoff i z.1 : ℂ) ^ 2 * (B.cutoff j z.2 : ℂ) ^ 2)) • w.val z := by
      by_cases hi : z.1 ∈ (A.frame i).baseSet
      · by_cases hj : z.2 ∈ (B.frame j).baseSet
        · have hterm (u : Fin r) (v : Fin s) :
              f (i, u) (j, v) z •
                ((A.weightedFrameSection i (EuclideanSpace.single u 1)).val z.1 ⊗ₜ[ℂ]
                  (B.weightedFrameSection j (EuclideanSpace.single v 1)).val z.2) =
              ((a z.1 * b z.2) *
                ((A.cutoff i z.1 : ℂ) ^ 2 * (B.cutoff j z.2 : ℂ) ^ 2)) •
                  ((t i j ⟨z, w.val z⟩).2 (finProdFinEquiv (u, v)) •
                    ((A.frame i).symmL ℂ z.1 (EuclideanSpace.single u 1) ⊗ₜ[ℂ]
                      (B.frame j).symmL ℂ z.2 (EuclideanSpace.single v 1))) := by
            change ((a z.1 * b z.2) * ((A.cutoff i z.1 : ℂ) * (B.cutoff j z.2 : ℂ) *
              (t i j ⟨z, w.val z⟩).2 (finProdFinEquiv (u, v)))) •
                (((A.cutoff i z.1 : ℂ) • _) ⊗ₜ[ℂ] ((B.cutoff j z.2 : ℂ) • _)) = _
            rw [TensorProduct.smul_tmul_smul]
            simp only [smul_smul]
            congr 1
            ring
          simp_rw [hterm, ← Finset.smul_sum, hreconstruct i j hi hj]
        · have hz : B.cutoff j z.2 = 0 := image_eq_zero_of_notMem_tsupport
            (fun h ↦ hj (B.support_subset j h).2)
          simp [f, c, hz]
      · have hz : A.cutoff i z.1 = 0 := image_eq_zero_of_notMem_tsupport
          (fun h ↦ hi (A.support_subset i h).2)
        simp [f, c, hz]
    have hsum :
        (∑ i : Fin A.size × Fin r, ∑ j : Fin B.size × Fin s, f i j z •
          ((A.weightedFrameSection i.1 (EuclideanSpace.single i.2 1)).val z.1 ⊗ₜ[ℂ]
            (B.weightedFrameSection j.1 (EuclideanSpace.single j.2 1)).val z.2)) =
        ∑ i : Fin A.size, ∑ j : Fin B.size,
          ((a z.1 * b z.2) *
            ((A.cutoff i z.1 : ℂ) ^ 2 * (B.cutoff j z.2 : ℂ) ^ 2)) • w.val z := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ ↦ hblock i j)
    have hsumscalar : (∑ i : Fin A.size, ∑ j : Fin B.size,
        (a z.1 * b z.2) *
          ((A.cutoff i z.1 : ℂ) ^ 2 * (B.cutoff j z.2 : ℂ) ^ 2)) = 1 := by
      calc
        _ = (a z.1 * ∑ i, (A.cutoff i z.1 : ℂ) ^ 2) *
            (b z.2 * ∑ j, (B.cutoff j z.2 : ℂ) ^ 2) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 1 := by rw [haone, hbone, one_mul]
    rw [hsum]
    simp_rw [← Finset.sum_smul]
    rw [hsumscalar, one_smul]

end AtiyahSinger
