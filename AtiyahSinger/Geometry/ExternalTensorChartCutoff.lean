/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ChartLocalization
public import AtiyahSinger.Geometry.ExternalTensorPresentation

/-!
# Product cutoff frames on the original external tensor bundle

Public module ID: M1229.

The same selected tensor atlas combines two compactly supported coordinate
cutoffs. This is the local extension data used to transport separated H1
approximations into the fixed geometric Sobolev spaces.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct SchwartzMap

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

variable {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
  {d : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m))}

/-- Two original cutoff frames give their separated cutoff in the selected tensor frame. -/
def externalTensorChartCutoff
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := s) F d) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
    BundleChartCutoff (r := r * s) (externalTensorFiber E F)
      ((c.prod d).trans
        (EuclideanSpace.finAddEquivProd
          (𝕜 := ℝ) (n := n) (m := m)).symm.toHomeomorph.toOpenPartialHomeomorph) := by
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
  let result := exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s) E F
  let hframe := result.choose_spec.choose_spec.2.1 A.frame A.frame_mem_atlas
    B.frame B.frame_mem_atlas
  let w : EuclideanSpace ℝ (Fin (n + m)) → ℝ :=
    fun z ↦ A.cutoff (e z).1 * B.cutoff (e z).2
  have hw : ContDiff ℝ ∞ w :=
    (A.smooth_cutoff.comp (contDiff_fst.comp e.contDiff)).mul
      (B.smooth_cutoff.comp (contDiff_snd.comp e.contDiff))
  have hK := (A.compact_support.prod B.compact_support).image e.symm.continuous
  have hsupport : tsupport w ⊆ e.symm '' (tsupport A.cutoff ×ˢ tsupport B.cutoff) := by
    apply closure_minimal ?_ hK.isClosed
    intro z hz
    refine ⟨e z, ⟨?_, ?_⟩, e.symm_apply_apply z⟩
    · apply subset_tsupport
      intro ha
      exact hz (by simp [w, ha])
    · apply subset_tsupport
      intro hb
      exact hz (by simp [w, hb])
  refine {
    frame := hframe.choose
    frame_mem_atlas := hframe.choose_spec.1
    cutoff := w
    smooth_cutoff := hw
    compact_support := hK.of_isClosed_subset (isClosed_tsupport w) hsupport
    support_subset := ?_ }
  intro z hz
  obtain ⟨p, hp, rfl⟩ := hsupport hz
  have hA := A.support_subset hp.1
  have hB := B.support_subset hp.2
  constructor
  · simp only [mfld_simps]
    change (e (e.symm p)).1 ∈ c.target ∧ (e (e.symm p)).2 ∈ d.target
    rw [e.apply_symm_apply]
    exact ⟨hA.1, hB.1⟩
  · rw [hframe.choose_spec.2.1]
    simp only [mfld_simps]
    change c.symm (e (e.symm p)).1 ∈ A.frame.baseSet ∧
      d.symm (e (e.symm p)).2 ∈ B.frame.baseSet
    rw [e.apply_symm_apply]
    exact ⟨hA.2, hB.2⟩

/-- A coordinate tensor extends to the same pointwise tensor of the two factor extensions. -/
theorem externalTensorChartCutoff_extendedFunction
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := s) F d)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (ψ : 𝓢(EuclideanSpace ℝ (Fin m), EuclideanSpace ℂ (Fin s)))
    (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r * s))))
    (hw : ∀ (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (i : Fin r) (j : Fin s),
      w ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm z)
          (finProdFinEquiv (i, j)) = φ z.1 i * ψ z.2 j) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
    ∀ (x : M) (y : N), (externalTensorChartCutoff A B).extendedFunction w (x, y) =
      A.extendedFunction φ x ⊗ₜ[ℂ] B.extendedFunction ψ y := by
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
  let L := externalTensorChartCutoff A B
  let result := exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s) E F
  let hframe := result.choose_spec.choose_spec.2.1 A.frame A.frame_mem_atlas
    B.frame B.frame_mem_atlas
  let t := hframe.choose
  let : MemTrivializationAtlas t := hframe.choose_spec.1
  let := L.frame_mem_atlas
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  have hsymmL (z : M × N) : L.frame.symmL ℂ z = t.symmL ℂ z := rfl
  have hcut (z : EuclideanSpace ℝ (Fin (n + m))) :
      L.cutoff z = A.cutoff (e z).1 * B.cutoff (e z).2 := rfl
  intro x y
  let q := (c.prod d).trans e.symm.toHomeomorph.toOpenPartialHomeomorph
  have hsrc : (x, y) ∈ q.source ↔ x ∈ c.source ∧ y ∈ d.source := by
    simp [q, mfld_simps]
  have hq : q (x, y) = e.symm (c x, d y) := rfl
  have hcutq : L.cutoff (q (x, y)) = A.cutoff (c x) * B.cutoff (d y) := by
    rw [hcut, hq, e.apply_symm_apply]
  change L.extendedFunction w (x, y) = _
  have hLvalue : L.extendedFunction w (x, y) = if (x, y) ∈ q.source then
      (L.cutoff (q (x, y)) : ℂ) • L.frame.symmL ℂ (x, y) (w (q (x, y))) else 0 := rfl
  rw [hLvalue]
  -- The extension is zero as soon as either original chart branch or cutoff vanishes.
  by_cases hx : x ∈ c.source
  · by_cases hy : y ∈ d.source
    · have hxy : (x, y) ∈ q.source := hsrc.mpr ⟨hx, hy⟩
      simp only [BundleChartCutoff.extendedFunction, ite_eq_left hxy,
        ite_eq_left hx, ite_eq_left hy]
      change (L.cutoff (q (x, y)) : ℂ) • L.frame.symmL ℂ (x, y) (w (q (x, y))) = _
      rw [hcutq, hsymmL, hq]
      by_cases ha : A.cutoff (c x) = 0
      · simp [ha]
      by_cases hb : B.cutoff (d y) = 0
      · simp [hb]
      have hAf : x ∈ A.frame.baseSet := by
        simpa only [Set.mem_preimage, c.left_inv hx] using
          (A.support_subset (subset_tsupport _ ha)).2
      have hBf : y ∈ B.frame.baseSet := by
        simpa only [Set.mem_preimage, d.left_inv hy] using
          (B.support_subset (subset_tsupport _ hb)).2
      have htf : (x, y) ∈ t.baseSet := by
        rw [hframe.choose_spec.2.1]
        exact ⟨hAf, hBf⟩
      -- In the selected tensor frame, inversion of the literal coordinate tensor is exact.
      have hinverse : t.symmL ℂ (x, y) (w (e.symm (c x, d y))) =
          A.frame.symmL ℂ x (φ (c x)) ⊗ₜ[ℂ] B.frame.symmL ℂ y (ψ (d y)) := by
        apply (t.linearEquivAt ℂ (x, y) htf).injective
        change (t ⟨(x, y), t.symmL ℂ (x, y) (w (e.symm (c x, d y)))⟩).2 =
          (t ⟨(x, y), A.frame.symmL ℂ x (φ (c x)) ⊗ₜ[ℂ]
            B.frame.symmL ℂ y (ψ (d y))⟩).2
        rw [t.symmL_apply htf, t.apply_mk_symm htf]
        apply PiLp.ext
        intro k
        obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
        rw [hframe.choose_spec.2.2 (x, y) ⟨hAf, hBf⟩,
          A.frame.symmL_apply hAf, A.frame.apply_mk_symm hAf,
          B.frame.symmL_apply hBf, B.frame.apply_mk_symm hBf]
        exact hw (c x, d y) i j
      rw [hinverse, Complex.ofReal_mul]
      exact (TensorProduct.smul_tmul_smul _ _ _ _).symm
    · have hxy : (x, y) ∉ q.source := fun h ↦ hy (hsrc.mp h).2
      simp only [BundleChartCutoff.extendedFunction, ite_eq_right hxy, ite_eq_right hy,
        TensorProduct.tmul_zero]
  · have hxy : (x, y) ∉ q.source := fun h ↦ hx (hsrc.mp h).1
    simp only [BundleChartCutoff.extendedFunction, ite_eq_right hxy, ite_eq_right hx,
      TensorProduct.zero_tmul]

/-- Localization in a selected tensor cutoff frame is exactly the coordinate tensor
of the two original localizations. -/
theorem externalTensorChartCutoff_localizedFunction
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := s) F d)
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
    ∀ (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (i : Fin r) (j : Fin s),
      (externalTensorChartCutoff A B).localizedFunction (externalTensorSection E F u v)
          (EuclideanSpace.finAddEquivProd.symm z) (finProdFinEquiv (i, j)) =
        A.localizedFunction u z.1 i * B.localizedFunction v z.2 j := by
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
  let C := externalTensorChartCutoff A B
  let q := (c.prod d).trans (EuclideanSpace.finAddEquivProd
    (𝕜 := ℝ) (n := n) (m := m)).symm.toHomeomorph.toOpenPartialHomeomorph
  let result := exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s) E F
  let hframe := result.choose_spec.choose_spec.2.1 A.frame A.frame_mem_atlas
    B.frame B.frame_mem_atlas
  have hcut (z : EuclideanSpace ℝ (Fin (n + m))) :
      C.cutoff z = A.cutoff (e z).1 * B.cutoff (e z).2 := rfl
  have hframeC : C.frame = hframe.choose := rfl
  intro z i j
  have ht : e.symm z ∈ q.target ↔ z.1 ∈ c.target ∧ z.2 ∈ d.target := by
    simp only [q, mfld_simps]
    change (e (e.symm z)).1 ∈ c.target ∧ (e (e.symm z)).2 ∈ d.target ↔ _
    rw [e.apply_symm_apply]
  have hi : q.symm (e.symm z) = (c.symm z.1, d.symm z.2) := by
    change (c.symm (e (e.symm z)).1, d.symm (e (e.symm z)).2) = _
    rw [e.apply_symm_apply]
  dsimp only [q] at ht hi
  change C.localizedFunction (externalTensorSection E F u v)
    (e.symm z) (finProdFinEquiv (i, j)) = _
  -- The same zero-extension branches are retained in each factor.
  by_cases hx : z.1 ∈ c.target
  · by_cases hy : z.2 ∈ d.target
    · simp only [BundleChartCutoff.localizedFunction, ite_eq_left (ht.mpr ⟨hx, hy⟩),
        ite_eq_left hx, ite_eq_left hy, hcut, e.apply_symm_apply, sectionInChart]
      by_cases ha : A.cutoff z.1 = 0
      · simp [ha]
      by_cases hb : B.cutoff z.2 = 0
      · simp [hb]
      have hA := (A.support_subset (subset_tsupport _ ha)).2
      have hB := (B.support_subset (subset_tsupport _ hb)).2
      have hpure := hframe.choose_spec.2.2 (c.symm z.1, d.symm z.2) ⟨hA, hB⟩
        (u.val (c.symm z.1)) (v.val (d.symm z.2)) i j
      rw [hframeC]
      dsimp only [externalTensorSection]
      have hvalue := congrArg (fun x : M × N ↦
        (hframe.choose ⟨x, u.val x.1 ⊗ₜ[ℂ] v.val x.2⟩).2) hi
      rw [hvalue, Complex.ofReal_mul]
      change ((A.cutoff z.1 : ℂ) * (B.cutoff z.2 : ℂ)) *
        (hframe.choose ⟨(c.symm z.1, d.symm z.2),
          u.val (c.symm z.1) ⊗ₜ[ℂ] v.val (d.symm z.2)⟩).2 (finProdFinEquiv (i, j)) = _
      rw [hpure]
      change _ = ((A.cutoff z.1 : ℂ) *
        (A.frame ⟨c.symm z.1, u.val (c.symm z.1)⟩).2 i) *
          ((B.cutoff z.2 : ℂ) * (B.frame ⟨d.symm z.2, v.val (d.symm z.2)⟩).2 j)
      ring
    · have hz : e.symm z ∉ q.target := fun h ↦ hy (ht.mp h).2
      dsimp only [q] at hz
      simp only [BundleChartCutoff.localizedFunction, ite_eq_right hz, ite_eq_right hy,
        PiLp.zero_apply, mul_zero]
  · have hz : e.symm z ∉ q.target := fun h ↦ hx (ht.mp h).1
    dsimp only [q] at hz
    simp only [BundleChartCutoff.localizedFunction, ite_eq_right hz, ite_eq_right hx,
      PiLp.zero_apply, zero_mul]

end AtiyahSinger
