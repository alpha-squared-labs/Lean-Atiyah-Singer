/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ExternalTensorH1Energy
public import AtiyahSinger.Analysis.ExternalTensorH1Global
public import AtiyahSinger.Analysis.HilbertTensorCompletion

/-!
# The two mixed tensor inclusions of geometric H1

Public module ID: M0613.

The exact product energy identity controls each mixed Hilbert tensor norm on
all finite sums of original smooth tensors. The natural H1-to-H0 inclusions
are contractions, so the common zeroth-order energy is bounded by either
mixed energy. Geometric H1 density then extends these literal tensor maps.
These are the bounded input maps for the two factorwise operator actions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory UniformSpace
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

variable [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
  [CompactSpace M] [CompactSpace N]

set_option maxHeartbeats 1000000 in
-- Extend the finite-sum tensor energy bounds to the completed mixed Sobolev spaces.
/-- Geometric product H1 maps contractively into each original mixed Sobolev tensor space. -/
theorem exists_externalTensorH1_mixed_maps
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
    let C := externalTensorPresentation A B
    ∃ L : C.SobolevSpace 1 →L[ℂ] Completion (A.SobolevSpace 1 ⊗[ℂ] B.SobolevSpace 0),
    ∃ R : C.SobolevSpace 1 →L[ℂ] Completion (A.SobolevSpace 0 ⊗[ℂ] B.SobolevSpace 1),
      ‖L‖ ≤ 1 ∧ ‖R‖ ≤ 1 ∧
        (∀ (u : smoothSections (n := n) (r := r) E)
            (v : smoothSections (n := m) (r := s) F),
          L (C.smoothToSobolev 1 (externalTensorSection E F u v)) =
            ↑(A.smoothToSobolev 1 u ⊗ₜ[ℂ] B.smoothToSobolev 0 v)) ∧
        (∀ (u : smoothSections (n := n) (r := r) E)
            (v : smoothSections (n := m) (r := s) F),
          R (C.smoothToSobolev 1 (externalTensorSection E F u v)) =
            ↑(A.smoothToSobolev 0 u ⊗ₜ[ℂ] B.smoothToSobolev 1 v)) := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
  let C := externalTensorPresentation A B
  let SE := smoothSections (n := n) (r := r) E
  let SF := smoothSections (n := m) (r := s) F
  let SG := smoothSections (n := n + m) (r := r * s) (externalTensorFiber E F)
  let bMap : SE →ₗ[ℂ] SF →ₗ[ℂ] SG :=
    LinearMap.mk₂ ℂ (externalTensorSection E F)
      (by
        intro u v w
        apply Subtype.ext
        funext z
        exact TensorProduct.add_tmul _ _ _)
      (by
        intro c u v
        apply Subtype.ext
        funext z
        exact (TensorProduct.smul_tmul' _ _ _).symm)
      (by
        intro u v w
        apply Subtype.ext
        funext z
        exact TensorProduct.tmul_add _ _ _)
      (by
        intro c u v
        apply Subtype.ext
        funext z
        exact TensorProduct.tmul_smul _ _ _)
  let T : SE ⊗[ℂ] SF →ₗ[ℂ] C.SobolevSpace 1 :=
    (C.smoothToSobolev 1).comp (TensorProduct.lift bMap)
  let J (a b : ℝ) : SE ⊗[ℂ] SF →ₗ[ℂ] A.SobolevSpace a ⊗[ℂ] B.SobolevSpace b :=
    TensorProduct.map (A.smoothToSobolev a) (B.smoothToSobolev b)
  have hT (u : SE) (v : SF) :
      T (u ⊗ₜ[ℂ] v) = C.smoothToSobolev 1 (externalTensorSection E F u v) := rfl
  have hJ (a b : ℝ) (u : SE) (v : SF) :
      J a b (u ⊗ₜ[ℂ] v) = A.smoothToSobolev a u ⊗ₜ[ℂ] B.smoothToSobolev b v := rfl
  -- Sesquilinearity extends the product identity to every finite tensor sum.
  have hpure (u u' : SE) (v v' : SF) :
      inner ℂ (T (u ⊗ₜ[ℂ] v)) (T (u' ⊗ₜ[ℂ] v')) =
        inner ℂ (J 1 0 (u ⊗ₜ[ℂ] v)) (J 1 0 (u' ⊗ₜ[ℂ] v')) +
        inner ℂ (J 0 1 (u ⊗ₜ[ℂ] v)) (J 0 1 (u' ⊗ₜ[ℂ] v')) -
        inner ℂ (J 0 0 (u ⊗ₜ[ℂ] v)) (J 0 0 (u' ⊗ₜ[ℂ] v')) := by
    simp only [hT, hJ, TensorProduct.inner_tmul]
    exact inner_smoothToSobolev_one_externalTensor A B u u' v v'
  have hinner (x y : SE ⊗[ℂ] SF) :
      inner ℂ (T x) (T y) = inner ℂ (J 1 0 x) (J 1 0 y) +
        inner ℂ (J 0 1 x) (J 0 1 y) - inner ℂ (J 0 0 x) (J 0 0 y) := by
    induction x using TensorProduct.inductionOn with
    | tmul u v =>
      induction y using TensorProduct.inductionOn with
      | tmul u' v' => exact hpure u u' v v'
      | add x y hx hy =>
        simp only [map_add, inner_add_right, hx, hy]
        ring
    | add x y hx hy =>
      simp only [map_add, inner_add_left, hx, hy]
      ring
  have henergy (z : SE ⊗[ℂ] SF) :
      ‖T z‖ ^ 2 = ‖J 1 0 z‖ ^ 2 + ‖J 0 1 z‖ ^ 2 - ‖J 0 0 z‖ ^ 2 := by
    have h := congrArg Complex.re (hinner z z)
    have hTnorm : (inner ℂ (T z) (T z)).re = ‖T z‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (T z)
    have h10 : (inner ℂ (J 1 0 z) (J 1 0 z)).re = ‖J 1 0 z‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (J 1 0 z)
    have h01 : (inner ℂ (J 0 1 z) (J 0 1 z)).re = ‖J 0 1 z‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (J 0 1 z)
    have h00 : (inner ℂ (J 0 0 z) (J 0 0 z)).re = ‖J 0 0 z‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (J 0 0 z)
    simpa only [Complex.add_re, Complex.sub_re, hTnorm, h10, h01, h00] using h
  let IA := A.sobolevInclusion 1 0 zero_le_one
  let IB := B.sobolevInclusion 1 0 zero_le_one
  -- The natural zeroth-order tensor maps are contractions on both mixed spaces.
  have h00left (z : SE ⊗[ℂ] SF) : ‖J 0 0 z‖ ≤ ‖J 1 0 z‖ := by
    let f := TensorProduct.mapL IA (ContinuousLinearMap.id ℂ (B.SobolevSpace 0))
    have hnorm : ‖f‖ ≤ 1 := by
      calc
        ‖f‖ ≤ ‖IA‖ * ‖ContinuousLinearMap.id ℂ (B.SobolevSpace 0)‖ :=
          TensorProduct.norm_mapL_le _ _
        _ ≤ 1 * 1 := mul_le_mul (A.norm_sobolevInclusion_le 1 0 zero_le_one)
          ContinuousLinearMap.norm_id_le (norm_nonneg _) (by norm_num)
        _ = 1 := one_mul 1
    have hcomm (z : SE ⊗[ℂ] SF) : f (J 1 0 z) = J 0 0 z := by
      induction z using TensorProduct.inductionOn with
      | tmul u v =>
        simp only [hJ, f, TensorProduct.mapL_tmul, IA,
          SmoothBundlePresentation.sobolevInclusion_smoothToSobolev,
          ContinuousLinearMap.id_apply]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [← hcomm]
    exact (f.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hnorm)
  have h00right (z : SE ⊗[ℂ] SF) : ‖J 0 0 z‖ ≤ ‖J 0 1 z‖ := by
    let f := TensorProduct.mapL (ContinuousLinearMap.id ℂ (A.SobolevSpace 0)) IB
    have hnorm : ‖f‖ ≤ 1 := by
      calc
        ‖f‖ ≤ ‖ContinuousLinearMap.id ℂ (A.SobolevSpace 0)‖ * ‖IB‖ :=
          TensorProduct.norm_mapL_le _ _
        _ ≤ 1 * 1 := mul_le_mul ContinuousLinearMap.norm_id_le
          (B.norm_sobolevInclusion_le 1 0 zero_le_one) (norm_nonneg _) (by norm_num)
        _ = 1 := one_mul 1
    have hcomm (z : SE ⊗[ℂ] SF) : f (J 0 1 z) = J 0 0 z := by
      induction z using TensorProduct.inductionOn with
      | tmul u v =>
        simp only [hJ, f, TensorProduct.mapL_tmul, IB,
          SmoothBundlePresentation.sobolevInclusion_smoothToSobolev,
          ContinuousLinearMap.id_apply]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [← hcomm]
    exact (f.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hnorm)
  have hleft (z : SE ⊗[ℂ] SF) : ‖J 1 0 z‖ ≤ ‖T z‖ := by
    have h := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h00right z)
    have he := henergy z
    nlinarith [norm_nonneg (T z), norm_nonneg (J 1 0 z)]
  have hright (z : SE ⊗[ℂ] SF) : ‖J 0 1 z‖ ≤ ‖T z‖ := by
    have h := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h00left z)
    have he := henergy z
    nlinarith [norm_nonneg (T z), norm_nonneg (J 0 1 z)]
  -- The domain is dense in the exact geometric H1 space, not merely in its L2 image.
  have hdense : DenseRange T := by
    apply (dense_span_externalTensorH1 (E := E) (F := F) C).mono
    change _ ≤ LinearMap.range T
    apply Submodule.span_le.mpr
    rintro z ⟨⟨u, v⟩, rfl⟩
    exact ⟨u ⊗ₜ[ℂ] v, hT u v⟩
  let Jc (a b : ℝ) : SE ⊗[ℂ] SF →ₗ[ℂ]
      Completion (A.SobolevSpace a ⊗[ℂ] B.SobolevSpace b) :=
    (Completion.toComplL (S := ℂ)).toLinearMap.comp (J a b)
  have hcLeft (z : SE ⊗[ℂ] SF) : ‖Jc 1 0 z‖ ≤ 1 * ‖T z‖ := by
    simpa only [Jc, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Completion.coe_toComplL, Completion.norm_coe, one_mul] using hleft z
  have hcRight (z : SE ⊗[ℂ] SF) : ‖Jc 0 1 z‖ ≤ 1 * ‖T z‖ := by
    simpa only [Jc, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Completion.coe_toComplL, Completion.norm_coe, one_mul] using hright z
  let L := (Jc 1 0).extendOfNorm T
  let R := (Jc 0 1).extendOfNorm T
  refine ⟨L, R, (Jc 1 0).opNorm_extendOfNorm_le hdense (by norm_num) hcLeft,
    (Jc 0 1).opNorm_extendOfNorm_le hdense (by norm_num) hcRight, ?_, ?_⟩
  · intro u v
    change L (T (u ⊗ₜ[ℂ] v)) = Jc 1 0 (u ⊗ₜ[ℂ] v)
    exact (Jc 1 0).extendOfNorm_eq hdense ⟨1, hcLeft⟩ (u ⊗ₜ[ℂ] v)
  · intro u v
    change R (T (u ⊗ₜ[ℂ] v)) = Jc 0 1 (u ⊗ₜ[ℂ] v)
    exact (Jc 0 1).extendOfNorm_eq hdense ⟨1, hcRight⟩ (u ⊗ₜ[ℂ] v)

end AtiyahSinger
