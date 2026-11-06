/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialOperator
public import AtiyahSinger.Analysis.GeometricProductCutoffRealization
public import AtiyahSinger.Geometry.SmoothTensorAtlas

/-!
# Tensoring a local PDO with a coefficient bundle

Public module ID: M0311.

The specified local Fourier piece is amplified in the original finite tensor
coordinates. Its Schwartz operator acts on each coefficient column by the
original operator. The original base chart and both cutoffs are retained, and
the coefficient frame is required on precisely their supports.

Source: the local coefficient construction in SG III.13. This supplementary
interface identifies the actual operator used on an associated kernel bundle;
it assumes no tensor product index formula or unregularized joint symbol bound.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap TensorProduct

/-- A Schwartz operator with a full symbol has its actual finite coefficient amplification.
The certificate includes the original coordinate columns, not only an abstract tensor map. -/
theorem exists_schwartz_tensorCoefficient {n r q : ℕ} (s : ℕ) (m : ℝ)
    (a : SymbolFunction n r q) (ha : IsSymbol Set.univ m a)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (hP : ∀ u x, P u x = quantize a u x) :
    ∃ Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (r * s))) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (q * s))),
      (∀ w x, Q w x = quantize (fun y ξ ↦ tensorIdentitySymbolMap r q s (a y ξ)) w x) ∧
      ∀ j : Fin s,
        ∃ D : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (r * s))) →L[ℂ]
            𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
          (∀ w x i, D w x i = w x (finProdFinEquiv (i, j))) ∧
          ∀ w x i, Q w x (finProdFinEquiv (i, j)) = P (D w) x i := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  -- Inject and project only the original finite coordinate columns.
  let J (d : ℕ) (j : Fin s) :
      EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin (d * s)) :=
    LinearMap.toContinuousLinearMap {
      toFun z := WithLp.toLp 2 (fun k ↦ z (finProdFinEquiv.symm k).1 *
        (EuclideanSpace.single j 1) (finProdFinEquiv.symm k).2)
      map_add' z z' := by
        ext k
        change (z _ + z' _) * _ = _
        exact add_mul _ _ _
      map_smul' c z := by
        ext k
        change (c * z _) * _ = _
        exact mul_assoc _ _ _ }
  let D (j : Fin s) : EuclideanSpace ℂ (Fin (r * s)) →L[ℂ] EuclideanSpace ℂ (Fin r) :=
    LinearMap.toContinuousLinearMap {
      toFun z := WithLp.toLp 2 (fun i ↦ z (finProdFinEquiv (i, j)))
      map_add' z z' := by ext i; rfl
      map_smul' c z := by ext i; rfl }
  have hJ (d : ℕ) (j : Fin s) (z : EuclideanSpace ℂ (Fin d)) (i : Fin d) (k : Fin s) :
      J d j z (finProdFinEquiv (i, k)) = z i * (EuclideanSpace.single j 1) k := by
    change z (finProdFinEquiv.symm (finProdFinEquiv (i, k))).1 *
      (EuclideanSpace.single j 1) (finProdFinEquiv.symm (finProdFinEquiv (i, k))).2 = _
    rw [Equiv.symm_apply_apply]
  let DS (j : Fin s) : 𝓢(X, EuclideanSpace ℂ (Fin (r * s))) →L[ℂ]
      𝓢(X, EuclideanSpace ℂ (Fin r)) := SchwartzMap.postcompCLM (D j)
  let JS (d : ℕ) (j : Fin s) : 𝓢(X, EuclideanSpace ℂ (Fin d)) →L[ℂ]
      𝓢(X, EuclideanSpace ℂ (Fin (d * s))) := SchwartzMap.postcompCLM (J d j)
  let Q := ∑ j : Fin s, (JS q j).comp (P.comp (DS j))
  have hcolumn (j : Fin s) (w : 𝓢(X, EuclideanSpace ℂ (Fin (r * s))))
      (x : X) (i : Fin q) : Q w x (finProdFinEquiv (i, j)) = P (DS j w) x i := by
    change (∑ k : Fin s, (JS q k).comp (P.comp (DS k))) w x
      (finProdFinEquiv (i, j)) = _
    simp only [sum_apply, ContinuousLinearMap.comp_apply,
      WithLp.ofLp_sum, Finset.sum_apply]
    change (∑ k : Fin s, J q k (P (DS k w) x) (finProdFinEquiv (i, j))) = _
    simp [hJ]
  have hsum (w : 𝓢(X, EuclideanSpace ℂ (Fin (r * s)))) :
      w = ∑ j : Fin s, JS r j (DS j w) := by
    apply SchwartzMap.ext
    intro x
    apply PiLp.ext
    intro k
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    simp only [sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
    change w x (finProdFinEquiv (i, j)) =
      ∑ k : Fin s, J r k (D k (w x)) (finProdFinEquiv (i, j))
    simp [hJ, D]
  -- Symbol growth makes each frequency integral integrable before finite summation.
  let α : SymbolFunction n (r * s) (q * s) :=
    fun y ξ ↦ tensorIdentitySymbolMap r q s (a y ξ)
  have hα : IsSymbol Set.univ m α :=
    isSymbol_continuousLinearMap m a ha ((tensorIdentitySymbolMap r q s).restrictScalars ℝ)
  have hInt {r' q' : ℕ} (β : SymbolFunction n r' q') (hβ : IsSymbol Set.univ m β)
      (w : 𝓢(X, EuclideanSpace ℂ (Fin r'))) (x : X) :
      Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        β x ξ (fourierSG w ξ)) := by
    have hg : (β x).HasTemperateGrowth := by
      refine ⟨?_, ?_⟩
      · have hs : ContDiff ℝ ∞ (Function.uncurry β) := by
          simpa only [Set.univ_prod_univ, contDiffOn_univ] using hβ.1
        exact hs.comp (contDiff_const.prodMk contDiff_id)
      · intro j
        obtain ⟨C, hC, hbound⟩ := hβ.2 {x} (Set.subset_univ _) isCompact_singleton 0 j
        refine ⟨⌈m - (j : ℝ)⌉₊, C, fun ξ ↦ ?_⟩
        have h := hbound x (Set.mem_singleton x) ξ
        simp only [symbolDerivative, norm_iteratedFDeriv_zero] at h
        apply h.trans
        apply mul_le_mul_of_nonneg_left _ hC
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil _)
    have hphase :
        (fun ξ : X ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))).HasTemperateGrowth := by
      simpa [Function.comp_def, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ x).hasTemperateGrowth
    have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let e : X ≃L[ℝ] X :=
      (LinearEquiv.smulOfNeZero ℝ X ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
    let v := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (FourierTransform.fourier w)
    exact (SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.id ℂ
        (EuclideanSpace ℂ (Fin r') →L[ℂ] EuclideanSpace ℂ (Fin q'))).flip
          (hphase.smul hg) v).integrable
  have hquantSum (w : Fin s → 𝓢(X, EuclideanSpace ℂ (Fin (r * s)))) (x : X) :
      quantize α (∑ j, w j) x = ∑ j, quantize α (w j) x := by
    have hf (ξ : X) : fourierSG (∑ j, w j) ξ = ∑ j, fourierSG (w j) ξ := by
      simp only [fourierSG, FourierTransform.fourier_sum, sum_apply]
    simp only [quantize, hf, map_sum, Finset.smul_sum]
    rw [integral_finsetSum _ (fun j _ ↦ hInt α hα (w j) x), Finset.smul_sum]
  refine ⟨Q, ?_, fun j ↦ ⟨DS j, fun _ _ _ ↦ rfl, hcolumn j⟩⟩
  intro w x
  -- Quantize each pure column and reconstruct the same full tensor-valued function.
  calc
    Q w x = ∑ j : Fin s, J q j (P (DS j w) x) := by
      simp [Q, JS]
    _ = ∑ j : Fin s, quantize α (JS r j (DS j w)) x := by
      apply Finset.sum_congr rfl
      intro j _
      apply PiLp.ext
      intro k
      obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective k
      rw [hJ, hP]
      exact (quantize_tensorIdentitySymbolMap a (DS j w) (EuclideanSpace.single j 1)
        (JS r j (DS j w)) (fun y i b ↦ hJ r j (DS j w y) i b) x i b).symm
    _ = quantize α (∑ j : Fin s, JS r j (DS j w)) x := (hquantSum _ x).symm
    _ = quantize α w x := congrArg (fun v ↦ quantize α v x) (hsum w).symm

section Atlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F W : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
  [TopologicalSpace (TotalSpace Unit W)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

attribute [local instance] ComplexBundle.tensorTopology

/-- Tensor a local piece with one specified coefficient frame, retaining both outer cutoffs. -/
def AtlasPseudodifferentialPiece.tensorCoefficient {m : ℝ}
    (L : AtlasPseudodifferentialPiece A B m) (K : SmoothComplexBundleAtlas (n := n) W)
    (j : K.Index)
    (hin : tsupport L.input.cutoff ⊆ L.chart.symm ⁻¹' (K.chart j).baseSet)
    (hout : tsupport L.output.cutoff ⊆ L.chart.symm ⁻¹' (K.chart j).baseSet) :
    AtlasPseudodifferentialPiece (tensorSmoothAtlas A K) (tensorSmoothAtlas B K) m := by
  have hbase (C : SmoothComplexBundleAtlas (n := n) E) (i : C.Index) :
      ((tensorSmoothAtlas C K).chart (i, j)).baseSet =
        (C.chart i).baseSet ∩ (K.chart j).baseSet :=
    (ComplexBundle.exists_tensor_trivialization (C.chart i) (K.chart j)
      (C.linear i) (K.linear j)).choose_spec.1
  have hbaseB : ((tensorSmoothAtlas B K).chart (L.output.frameIndex, j)).baseSet =
      (B.chart L.output.frameIndex).baseSet ∩ (K.chart j).baseSet :=
    (ComplexBundle.exists_tensor_trivialization (B.chart L.output.frameIndex) (K.chart j)
      (B.linear L.output.frameIndex) (K.linear j)).choose_spec.1
  refine {
    chart := L.chart
    chart_mem_atlas := L.chart_mem_atlas
    input := {
      frameIndex := (L.input.frameIndex, j)
      cutoff := L.input.cutoff
      smooth_cutoff := L.input.smooth_cutoff
      compact_support := L.input.compact_support
      support_subset := ?_ }
    output := {
      frameIndex := (L.output.frameIndex, j)
      cutoff := L.output.cutoff
      smooth_cutoff := L.output.smooth_cutoff
      compact_support := L.output.compact_support
      support_subset := ?_ }
    input_support_in_output_frame := ?_
    output_support_in_input_frame := ?_
    operator := (exists_schwartz_tensorCoefficient (K.rank j) m L.symbol
      L.isSymbol L.operator L.operator_apply).choose
    symbol := fun x ξ ↦ tensorIdentitySymbolMap _ _ (K.rank j) (L.symbol x ξ)
    isSymbol := isSymbol_continuousLinearMap m L.symbol L.isSymbol
      ((tensorIdentitySymbolMap _ _ (K.rank j)).restrictScalars ℝ)
    operator_apply := (exists_schwartz_tensorCoefficient (K.rank j) m L.symbol
      L.isSymbol L.operator L.operator_apply).choose_spec.1 }
  · intro x hx
    exact ⟨(L.input.support_subset hx).1,
      (hbase A L.input.frameIndex).symm ▸ ⟨(L.input.support_subset hx).2, hin hx⟩⟩
  · intro x hx
    exact ⟨(L.output.support_subset hx).1,
      hbaseB.symm ▸ ⟨(L.output.support_subset hx).2, hout hx⟩⟩
  · intro x hx
    exact hbaseB.symm ▸ ⟨L.input_support_in_output_frame hx, hin hx⟩
  · intro x hx
    exact (hbase A L.input.frameIndex).symm ▸
      ⟨L.output_support_in_input_frame hx, hout hx⟩

/-- Every original coefficient column of the tensor piece is acted on by the same local PDO. -/
theorem AtlasPseudodifferentialPiece.tensorCoefficient_operator_column {m : ℝ}
    (L : AtlasPseudodifferentialPiece A B m) (K : SmoothComplexBundleAtlas (n := n) W)
    (j : K.Index)
    (hin : tsupport L.input.cutoff ⊆ L.chart.symm ⁻¹' (K.chart j).baseSet)
    (hout : tsupport L.output.cutoff ⊆ L.chart.symm ⁻¹' (K.chart j).baseSet)
    (b : Fin (K.rank j)) :
    ∃ D : 𝓢(EuclideanSpace ℝ (Fin n),
          EuclideanSpace ℂ (Fin (A.rank L.input.frameIndex * K.rank j))) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank L.input.frameIndex))),
      (∀ w x i, D w x i = w x (finProdFinEquiv (i, b))) ∧
      ∀ w x i, (L.tensorCoefficient K j hin hout).operator w x (finProdFinEquiv (i, b)) =
        L.operator (D w) x i :=
  (exists_schwartz_tensorCoefficient (K.rank j) m L.symbol
    L.isSymbol L.operator L.operator_apply).choose_spec.2 b

end Atlas

end AtiyahSinger
