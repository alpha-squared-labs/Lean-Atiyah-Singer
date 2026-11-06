/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ExternalTensorSectionDecomposition

/-!
# The original product chart and frame presentation

Public module ID: M1230.

The product partition and the tensor charts selected by the external tensor
bundle witness give a finite smooth presentation on the actual product bundle. Its
indexing uses `finProdFinEquiv` for the presentation indices, independently of
the same standard indexing of the fiber tensor basis.

This construction supplies common localizations for product Sobolev estimates.
It changes neither the manifold model nor the tensor-bundle atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

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

/-- The two original finite presentations give their product partition and tensor frames. -/
def externalTensorPresentation
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
    SmoothBundlePresentation (n := n + m) (r := r * s) (externalTensorFiber E F) := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let idx : Fin (A.size * B.size) ≃ Fin A.size × Fin B.size := finProdFinEquiv.symm
  let charts (i : Fin A.size) (j : Fin B.size) :=
    ((A.chart i).prod (B.chart j)).trans e.symm.toHomeomorph.toOpenPartialHomeomorph
  have hcharts (i : Fin A.size) (j : Fin B.size) :
      charts i j ∈ atlas (EuclideanSpace ℝ (Fin (n + m))) (M × N) := by
    refine ⟨(A.chart i).prod (B.chart j), ?_,
      e.symm.toHomeomorph.toOpenPartialHomeomorph, Set.mem_singleton _, rfl⟩
    exact ⟨A.chart i, A.chart_mem_atlas i, B.chart j, B.chart_mem_atlas j, rfl⟩
  -- Select the charts from the same witness defining the external tensor bundle.
  let result := exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s) E F
  have hframes (i : Fin A.size) (j : Fin B.size) :=
    result.choose_spec.choose_spec.2.1 (A.frame i) (A.frame_mem_atlas i)
      (B.frame j) (B.frame_mem_atlas j)
  choose t ht hbase _ using hframes
  have hproj :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (Prod.fst : M × N → M) ∧
        ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ (Prod.snd : M × N → N) := by
    let P := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)
    let : ChartedSpace P (M × N) := prodChartedSpace _ M _ N
    let : IsManifold 𝓘(ℝ, P) ∞ (M × N) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) M N
    have hid : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m)))
        𝓘(ℝ, P) ∞ (id : M × N → M × N) :=
      (contMDiff_mfderiv_linearModelId e.symm (M × N)).1.2
    have hf : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (Prod.fst : M × N → M) := by
      simpa only [P, modelWithCornersSelf_prod] using
        (contMDiff_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (n := ∞))
    have hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
        (Prod.snd : M × N → N) := by
      simpa only [P, modelWithCornersSelf_prod] using
        (contMDiff_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (n := ∞))
    exact ⟨hf.comp hid, hg.comp hid⟩
  let w (i : Fin A.size) (j : Fin B.size) (z : M × N) := A.cutoff i z.1 * B.cutoff j z.2
  have hmul : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ z.1 * z.2) := contDiff_mul
  have hsupport (i : Fin A.size) (j : Fin B.size) :
      tsupport (w i j) ⊆ tsupport (A.cutoff i) ×ˢ tsupport (B.cutoff j) := by
    apply closure_minimal ?_ ((isClosed_tsupport _).prod (isClosed_tsupport _))
    intro z hz
    constructor
    · apply subset_tsupport
      intro ha
      exact hz (by simp [w, ha])
    · apply subset_tsupport
      intro hb
      exact hz (by simp [w, hb])
  refine {
    size := A.size * B.size
    chart := fun k ↦ charts (idx k).1 (idx k).2
    chart_mem_atlas := fun k ↦ hcharts (idx k).1 (idx k).2
    frame := fun k ↦ t (idx k).1 (idx k).2
    frame_mem_atlas := fun k ↦ ht (idx k).1 (idx k).2
    cutoff := fun k ↦ w (idx k).1 (idx k).2
    smooth_cutoff := fun k ↦ hmul.contMDiff.comp
      (((A.smooth_cutoff (idx k).1).comp hproj.1).prodMk_space
        ((B.smooth_cutoff (idx k).2).comp hproj.2))
    cutoff_nonneg := fun k z ↦ mul_nonneg (A.cutoff_nonneg _ _) (B.cutoff_nonneg _ _)
    compact_support := fun k ↦ ((A.compact_support (idx k).1).prod
      (B.compact_support (idx k).2)).of_isClosed_subset (isClosed_tsupport _)
        (hsupport (idx k).1 (idx k).2)
    support_subset := ?_
    sum_cutoff := ?_ }
  · intro k z hz
    have hz' := hsupport (idx k).1 (idx k).2 hz
    have hA := A.support_subset (idx k).1 hz'.1
    have hB := B.support_subset (idx k).2 hz'.2
    constructor
    · change z ∈ ((A.chart (idx k).1).prod (B.chart (idx k).2)).source ∩
        ((A.chart (idx k).1).prod (B.chart (idx k).2)) ⁻¹' Set.univ
      exact ⟨⟨hA.1, hB.1⟩, Set.mem_univ _⟩
    · rw [hbase]
      exact ⟨hA.2, hB.2⟩
  · intro z
    calc
      ∑ k : Fin (A.size * B.size), w (idx k).1 (idx k).2 z =
          ∑ p : Fin A.size × Fin B.size, w p.1 p.2 z :=
        idx.sum_comp (fun p : Fin A.size × Fin B.size ↦ w p.1 p.2 z)
      _ = (∑ i : Fin A.size, A.cutoff i z.1) * ∑ j : Fin B.size, B.cutoff j z.2 := by
        simp only [Fintype.sum_prod_type, w]
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
      _ = 1 := by rw [A.sum_cutoff, B.sum_cutoff, one_mul]

/-- Product localization retains the two original coordinate functions in the tensor basis. -/
theorem externalTensorPresentation_localizedFunction
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := m) (r := s) F)
    (i : Fin A.size) (j : Fin B.size)
    (u : smoothSections (n := n) (r := r) E)
    (v : smoothSections (n := m) (r := s) F) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    let C := externalTensorPresentation A B
    ∀ (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (a : Fin r) (b : Fin s),
      C.localizedFunction (finProdFinEquiv (i, j)) (externalTensorSection E F u v)
          (e.symm z) (finProdFinEquiv (a, b)) =
        A.localizedFunction i u z.1 a * B.localizedFunction j v z.2 b := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let C := externalTensorPresentation A B
  let k : Fin C.size := finProdFinEquiv (i, j)
  let result := exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s) E F
  let hframe := result.choose_spec.choose_spec.2.1 (A.frame i) (A.frame_mem_atlas i)
    (B.frame j) (B.frame_mem_atlas j)
  have hchart : C.chart k =
      ((A.chart i).prod (B.chart j)).trans e.symm.toHomeomorph.toOpenPartialHomeomorph := by
    simp only [C, k, externalTensorPresentation, Equiv.symm_apply_apply]
    rfl
  have hcutoff (x : M × N) : C.cutoff k x = A.cutoff i x.1 * B.cutoff j x.2 := by
    simp only [C, k, externalTensorPresentation, Equiv.symm_apply_apply]
  have hCframe : C.frame k = hframe.choose := by
    simp only [C, k, externalTensorPresentation, Equiv.symm_apply_apply]
  change ∀ (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
    (a : Fin r) (b : Fin s),
    C.localizedFunction k (externalTensorSection E F u v)
        (e.symm z) (finProdFinEquiv (a, b)) =
      A.localizedFunction i u z.1 a * B.localizedFunction j v z.2 b
  intro z a b
  have htarget : e.symm z ∈ (C.chart k).target ↔
      z.1 ∈ (A.chart i).target ∧ z.2 ∈ (B.chart j).target := by
    rw [hchart]
    simp only [mfld_simps]
    change (e (e.symm z)).1 ∈ (A.chart i).target ∧
      (e (e.symm z)).2 ∈ (B.chart j).target ↔ _
    rw [e.apply_symm_apply]
  have hinv : (C.chart k).symm (e.symm z) =
      ((A.chart i).symm z.1, (B.chart j).symm z.2) := by
    rw [hchart]
    simp only [mfld_simps]
    change ((A.chart i).symm (e (e.symm z)).1, (B.chart j).symm (e (e.symm z)).2) = _
    rw [e.apply_symm_apply]
  change C.localizedFunction k (externalTensorSection E F u v)
    (e.symm z) (finProdFinEquiv (a, b)) = _
  -- Off either factor chart both the product localization and the corresponding factor vanish.
  by_cases hA : z.1 ∈ (A.chart i).target
  · by_cases hB : z.2 ∈ (B.chart j).target
    · simp only [SmoothBundlePresentation.localizedFunction, ite_eq_left (htarget.mpr ⟨hA, hB⟩),
        ite_eq_left hA, ite_eq_left hB, hcutoff, hinv, sectionInChart]
      by_cases ha : A.cutoff i ((A.chart i).symm z.1) = 0
      · simp [ha]
      by_cases hb : B.cutoff j ((B.chart j).symm z.2) = 0
      · simp [hb]
      -- Nonzero partition weights put both vectors inside the exact selected tensor frame.
      have hAe := (A.support_subset i (subset_tsupport _ ha)).2
      have hBe := (B.support_subset j (subset_tsupport _ hb)).2
      have hpure := hframe.choose_spec.2.2
        ((A.chart i).symm z.1, (B.chart j).symm z.2) ⟨hAe, hBe⟩
        (u.val ((A.chart i).symm z.1)) (v.val ((B.chart j).symm z.2)) a b
      rw [hCframe]
      dsimp only [externalTensorSection]
      have hvalue := congrArg (fun x : M × N ↦
        (hframe.choose ⟨x, u.val x.1 ⊗ₜ[ℂ] v.val x.2⟩).2) hinv
      rw [hvalue]
      simp only [Complex.ofReal_mul]
      change ((A.cutoff i ((A.chart i).symm z.1) : ℂ) *
        (B.cutoff j ((B.chart j).symm z.2) : ℂ)) *
          (hframe.choose ⟨((A.chart i).symm z.1, (B.chart j).symm z.2),
            u.val ((A.chart i).symm z.1) ⊗ₜ[ℂ] v.val ((B.chart j).symm z.2)⟩).2
              (finProdFinEquiv (a, b)) = _
      rw [hpure]
      change _ = ((A.cutoff i ((A.chart i).symm z.1) : ℂ) *
        ((A.frame i) ⟨(A.chart i).symm z.1, u.val ((A.chart i).symm z.1)⟩).2 a) *
          ((B.cutoff j ((B.chart j).symm z.2) : ℂ) *
            ((B.frame j) ⟨(B.chart j).symm z.2, v.val ((B.chart j).symm z.2)⟩).2 b)
      ring
    · have hz : e.symm z ∉ (C.chart k).target := fun h ↦ hB (htarget.mp h).2
      simp only [SmoothBundlePresentation.localizedFunction, ite_eq_right hz, ite_eq_right hB,
        PiLp.zero_apply, mul_zero]
  · have hz : e.symm z ∉ (C.chart k).target := fun h ↦ hA (htarget.mp h).1
    simp only [SmoothBundlePresentation.localizedFunction, ite_eq_right hz, ite_eq_right hA,
      PiLp.zero_apply, zero_mul]

end AtiyahSinger
