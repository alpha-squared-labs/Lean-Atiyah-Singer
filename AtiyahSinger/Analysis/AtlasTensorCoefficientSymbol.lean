/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialSymbol
public import AtiyahSinger.Analysis.AtlasTensorCoefficientPiece
public import AtiyahSinger.Analysis.TensorAtlasSymbol

/-!
# The transported cutoff symbol of a tensor coefficient piece

Public module ID: M0312.

Tensoring the piece tensors its original two-cutoff symbol representative
in the same fibers. The function identity is proved in the specified tensor
charts, including the support boundary, before passage to a principal quotient.
It does not identify an operator's full reduced symbol with that representative.
No homogeneity or covector-linearity assumption is used.

Source: the local coefficient calculation in SG III.13.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

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

set_option maxRecDepth 4096 in
/-- Tensoring a local piece tensors its transported two-cutoff representative in the same fibers. -/
theorem AtlasPseudodifferentialPiece.globalSymbolFunction_tensorCoefficient {m : ℝ}
    (L : AtlasPseudodifferentialPiece A B m) (K : SmoothComplexBundleAtlas (n := n) W)
    (j : K.Index)
    (hin : tsupport L.input.cutoff ⊆ L.chart.symm ⁻¹' (K.chart j).baseSet)
    (hout : tsupport L.output.cutoff ⊆ L.chart.symm ⁻¹' (K.chart j).baseSet) :
    (L.tensorCoefficient K j hin hout).globalSymbolFunction =
      tensorAtlasSymbol (W := W) L.globalSymbolFunction := by
  classical
  let R := L.tensorCoefficient K j hin hout
  let AT := tensorSmoothAtlas A K
  let BT := tensorSmoothAtlas B K
  have hbaseA : (AT.chart (L.input.frameIndex, j)).baseSet =
      (A.chart L.input.frameIndex).baseSet ∩ (K.chart j).baseSet :=
    (ComplexBundle.exists_tensor_trivialization (A.chart L.input.frameIndex) (K.chart j)
      (A.linear L.input.frameIndex) (K.linear j)).choose_spec.1
  have hbaseB : (BT.chart (L.output.frameIndex, j)).baseSet =
      (B.chart L.output.frameIndex).baseSet ∩ (K.chart j).baseSet :=
    (ComplexBundle.exists_tensor_trivialization (B.chart L.output.frameIndex) (K.chart j)
      (B.linear L.output.frameIndex) (K.linear j)).choose_spec.1
  funext x ξ
  apply TensorProduct.ext'
  intro u w
  change R.globalSymbolFunction x ξ (u ⊗ₜ[ℂ] w) =
    tensorAtlasSymbol L.globalSymbolFunction x ξ (u ⊗ₜ[ℂ] w)
  simp only [tensorAtlasSymbol, TensorProduct.map_tmul, LinearMap.id_apply]
  by_cases hx : x ∈ L.chart.source ∩ (A.chart L.input.frameIndex).baseSet ∩
      (B.chart L.output.frameIndex).baseSet
  · by_cases hk : x ∈ (K.chart j).baseSet
    · -- On the actual common frame domain, both tensor coordinates are prescribed.
      have hAT : x ∈ (AT.chart (L.input.frameIndex, j)).baseSet :=
        hbaseA.symm ▸ ⟨hx.1.2, hk⟩
      have hBT : x ∈ (BT.chart (L.output.frameIndex, j)).baseSet :=
        hbaseB.symm ▸ ⟨hx.2, hk⟩
      have hR : x ∈ R.chart.source ∩
          (AT.chart R.input.frameIndex).baseSet ∩ (BT.chart R.output.frameIndex).baseSet :=
        ⟨⟨hx.1.1, hAT⟩, hBT⟩
      dsimp only [AT, BT] at hR
      let eA := (A.frameLinearEquiv L.input.frameIndex x hx.1.2).trans
        (EuclideanSpace.equiv (Fin (A.rank L.input.frameIndex)) ℂ).symm.toLinearEquiv
      let eB := (B.frameLinearEquiv L.output.frameIndex x hx.2).trans
        (EuclideanSpace.equiv (Fin (B.rank L.output.frameIndex)) ℂ).symm.toLinearEquiv
      let eK := (K.frameLinearEquiv j x hk).trans
        (EuclideanSpace.equiv (Fin (K.rank j)) ℂ).symm.toLinearEquiv
      let eAT := (AT.frameLinearEquiv (L.input.frameIndex, j) x hAT).trans
        (EuclideanSpace.equiv (Fin (A.rank L.input.frameIndex * K.rank j)) ℂ).symm.toLinearEquiv
      let eBT := (BT.frameLinearEquiv (L.output.frameIndex, j) x hBT).trans
        (EuclideanSpace.equiv (Fin (B.rank L.output.frameIndex * K.rank j)) ℂ).symm.toLinearEquiv
      have hcoordA (v : E x) (z : W x) (i : Fin (A.rank L.input.frameIndex))
          (b : Fin (K.rank j)) :
          eAT (v ⊗ₜ[ℂ] z) (finProdFinEquiv (i, b)) = eA v i * eK z b := by
        change (tensorBundleChart A K L.input.frameIndex j ⟨x, v ⊗ₜ[ℂ] z⟩).2
          (finProdFinEquiv (i, b)) = (A.chart L.input.frameIndex ⟨x, v⟩).2 i *
            (K.chart j ⟨x, z⟩).2 b
        exact (ComplexBundle.exists_tensor_trivialization
          (A.chart L.input.frameIndex) (K.chart j)
          (A.linear L.input.frameIndex) (K.linear j)).choose_spec.2.2 x ⟨hx.1.2, hk⟩ v z i b
      have hcoordB (v : F x) (z : W x) (i : Fin (B.rank L.output.frameIndex))
          (b : Fin (K.rank j)) :
          eBT (v ⊗ₜ[ℂ] z) (finProdFinEquiv (i, b)) = eB v i * eK z b := by
        change (tensorBundleChart B K L.output.frameIndex j ⟨x, v ⊗ₜ[ℂ] z⟩).2
          (finProdFinEquiv (i, b)) = (B.chart L.output.frameIndex ⟨x, v⟩).2 i *
            (K.chart j ⟨x, z⟩).2 b
        exact (ComplexBundle.exists_tensor_trivialization
          (B.chart L.output.frameIndex) (K.chart j)
          (B.linear L.output.frameIndex) (K.linear j)).choose_spec.2.2 x ⟨hx.2, hk⟩ v z i b
      let τ : ℂ := ((L.output.cutoff (L.chart x) * L.input.cutoff (L.chart x) : ℝ) : ℂ)
      let a := L.symbol (L.chart x) (covectorInChart L.chart x ξ)
      have hLact : L.globalSymbolFunction x ξ u = τ • eB.symm (a (eA u)) := by
        simp only [globalSymbolFunction, dite_eq_left hx]
        rfl
      have hRact : R.globalSymbolFunction x ξ (u ⊗ₜ[ℂ] w) =
          τ • eBT.symm (tensorIdentitySymbolMap _ _ (K.rank j) a (eAT (u ⊗ₜ[ℂ] w))) := by
        simp only [globalSymbolFunction, dite_eq_left hR]
        rfl
      rw [hLact, hRact]
      apply eBT.injective
      rw [map_smul, LinearEquiv.apply_symm_apply]
      apply PiLp.ext
      intro k
      obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective k
      change τ * tensorIdentitySymbolMap _ _ (K.rank j) a (eAT (u ⊗ₜ[ℂ] w))
        (finProdFinEquiv (i, b)) = eBT ((τ • eB.symm (a (eA u))) ⊗ₜ[ℂ] w)
          (finProdFinEquiv (i, b))
      rw [tensorIdentitySymbolMap_apply _ (eA u) (eK w) _ (hcoordA u w), hcoordB,
        map_smul, LinearEquiv.apply_symm_apply]
      change τ * (a (eA u) i * eK w b) = (τ * a (eA u) i) * eK w b
      exact (mul_assoc _ _ _).symm
    · -- Outside the coefficient frame, the original output cutoff vanishes too.
      have hcut : L.output.cutoff (L.chart x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hz
        have h := hout hz
        change L.chart.symm (L.chart x) ∈ (K.chart j).baseSet at h
        rw [L.chart.left_inv hx.1.1] at h
        exact hk h
      have hnR : x ∉ R.chart.source ∩
          (AT.chart R.input.frameIndex).baseSet ∩ (BT.chart R.output.frameIndex).baseSet := by
        intro h
        exact hk (hbaseB ▸ h.2).2
      dsimp only [AT, BT] at hnR
      simp only [globalSymbolFunction, dite_eq_right hnR, dite_eq_left hx, LinearMap.zero_apply,
        hcut, zero_mul, Complex.ofReal_zero, zero_smul, TensorProduct.zero_tmul]
  · -- Failure of an original frame condition also invalidates its tensor frame.
    have hnR : x ∉ R.chart.source ∩
        (AT.chart R.input.frameIndex).baseSet ∩ (BT.chart R.output.frameIndex).baseSet := by
      intro h
      exact hx ⟨⟨h.1.1, (hbaseA ▸ h.1.2).1⟩, (hbaseB ▸ h.2).1⟩
    dsimp only [AT, BT] at hnR
    simp only [globalSymbolFunction, dite_eq_right hnR, dite_eq_right hx, LinearMap.zero_apply,
      TensorProduct.zero_tmul]

end AtiyahSinger
