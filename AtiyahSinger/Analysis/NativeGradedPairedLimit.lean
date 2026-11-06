/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedBlockCorrectedLimit
public import AtiyahSinger.Analysis.GradedBlockRealization
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Paired limits in the specified native graded coordinates

Public module ID: M0810.

Four paired approximation certificates determine operator-norm limits for the
specified graded realization and its specified reverse realization. The corner
witnesses remain internal: their smooth values identify the same two native
matrices on dense cores, and the original residuals correct the same two maps.

All native maps, coordinates, core inclusions, residuals and corner targets are
supplied. The reverse matrix retains its positive upper-right and negative
lower-left entries. In the associated sphere application it is the literal
metric adjoint of the original cutoff; this theorem does not choose an adjoint,
native model, cutoff, completion equivalence or parameter sequence.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter
open scoped Topology

variable {C₀₀ C₁₀ C₀₁ C₁₁ S₀₀ S₁₀ S₀₁ S₁₁ Nplus Nminus : Type*}
  [AddCommGroup C₀₀] [Module ℂ C₀₀] [AddCommGroup C₁₀] [Module ℂ C₁₀]
  [AddCommGroup C₀₁] [Module ℂ C₀₁] [AddCommGroup C₁₁] [Module ℂ C₁₁]
  [AddCommGroup S₀₀] [Module ℂ S₀₀] [AddCommGroup S₁₀] [Module ℂ S₁₀]
  [AddCommGroup S₀₁] [Module ℂ S₀₁] [AddCommGroup S₁₁] [Module ℂ S₁₁]
  [AddCommGroup Nplus] [Module ℂ Nplus] [AddCommGroup Nminus] [Module ℂ Nminus]
  {D₀₀ D₁₀ D₀₁ D₁₁ Dplus Dminus Xplus Xminus : Type*}
  [NormedAddCommGroup D₀₀] [NormedSpace ℂ D₀₀]
  [NormedAddCommGroup D₁₀] [NormedSpace ℂ D₁₀]
  [NormedAddCommGroup D₀₁] [NormedSpace ℂ D₀₁]
  [NormedAddCommGroup D₁₁] [NormedSpace ℂ D₁₁]
  [NormedAddCommGroup Dplus] [NormedSpace ℂ Dplus]
  [NormedAddCommGroup Dminus] [NormedSpace ℂ Dminus]
  [NormedAddCommGroup Xplus] [NormedSpace ℂ Xplus]
  [NormedAddCommGroup Xminus] [NormedSpace ℂ Xminus]
  {X₀₀ X₁₀ X₀₁ X₁₁ : Type*}
  [NormedAddCommGroup X₀₀] [InnerProductSpace ℂ X₀₀] [CompleteSpace X₀₀]
  [NormedAddCommGroup X₁₀] [InnerProductSpace ℂ X₁₀] [CompleteSpace X₁₀]
  [NormedAddCommGroup X₀₁] [InnerProductSpace ℂ X₀₁] [CompleteSpace X₀₁]
  [NormedAddCommGroup X₁₁] [InnerProductSpace ℂ X₁₁] [CompleteSpace X₁₁]

/-- Paired corner limits converge in the prescribed native graded coordinates.
Each corner pair supplies both smooth identities and both norm limits; the corrections
use the original two factored residuals. -/
theorem tendsto_conjugate_pair_of_native_corner_limits
    (j₀₀ : C₀₀ →ₗ[ℂ] D₀₀) (j₁₀ : C₁₀ →ₗ[ℂ] D₁₀)
    (j₀₁ : C₀₁ →ₗ[ℂ] D₀₁) (j₁₁ : C₁₁ →ₗ[ℂ] D₁₁)
    (s₀₀ : C₀₀ ≃ₗ[ℂ] S₀₀) (s₁₀ : C₁₀ ≃ₗ[ℂ] S₁₀)
    (s₀₁ : C₀₁ ≃ₗ[ℂ] S₀₁) (s₁₁ : C₁₁ ≃ₗ[ℂ] S₁₁)
    (out₀₀ : S₀₀ →ₗ[ℂ] X₀₀) (out₁₀ : S₁₀ →ₗ[ℂ] X₁₀)
    (out₀₁ : S₀₁ →ₗ[ℂ] X₀₁) (out₁₁ : S₁₁ →ₗ[ℂ] X₁₁)
    (sumPlus : (S₀₀ × S₁₁) →ₗ[ℂ] Nplus) (sumMinus : (S₁₀ × S₀₁) →ₗ[ℂ] Nminus)
    (nativePlusOne : Nplus →ₗ[ℂ] Dplus) (nativeMinusOne : Nminus →ₗ[ℂ] Dminus)
    (nativePlusZero : Nplus →ₗ[ℂ] Xplus) (nativeMinusZero : Nminus →ₗ[ℂ] Xminus)
    (phiPlus : Dplus ≃L[ℂ] WithLp 2 (D₀₀ × D₁₁))
    (phiMinus : Dminus ≃L[ℂ] WithLp 2 (D₁₀ × D₀₁))
    (psiPlus : Xplus ≃L[ℂ] WithLp 2 (X₀₀ × X₁₁))
    (psiMinus : Xminus ≃L[ℂ] WithLp 2 (X₁₀ × X₀₁))
    (K : ℕ → Nplus →ₗ[ℂ] Nminus) (Ka : ℕ → Nminus →ₗ[ℂ] Nplus)
    (R : ℕ → Dplus →L[ℂ] Xminus) (Ra : ℕ → Dminus →L[ℂ] Xplus)
    (qH₀ : ℕ → S₀₀ →ₗ[ℂ] S₁₀) (qH₀a : ℕ → S₁₀ →ₗ[ℂ] S₀₀)
    (qH₁ : ℕ → S₀₁ →ₗ[ℂ] S₁₁) (qH₁a : ℕ → S₁₁ →ₗ[ℂ] S₀₁)
    (qV₀ : ℕ → S₀₀ →ₗ[ℂ] S₀₁) (qV₀a : ℕ → S₀₁ →ₗ[ℂ] S₀₀)
    (qV₁ : ℕ → S₁₀ →ₗ[ℂ] S₁₁) (qV₁a : ℕ → S₁₁ →ₗ[ℂ] S₁₀)
    (BH₀ : D₀₀ →L[ℂ] X₁₀) (BH₀a : D₁₀ →L[ℂ] X₀₀)
    (BH₁ : D₀₁ →L[ℂ] X₁₁) (BH₁a : D₁₁ →L[ℂ] X₀₁)
    (BV₀ : D₀₀ →L[ℂ] X₀₁) (BV₀a : D₀₁ →L[ℂ] X₀₀)
    (BV₁ : D₁₀ →L[ℂ] X₁₁) (BV₁a : D₁₁ →L[ℂ] X₁₀)
    (J₀₀ : D₀₀ →L[ℂ] X₀₀) (J₁₀ : D₁₀ →L[ℂ] X₁₀)
    (J₀₁ : D₀₁ →L[ℂ] X₀₁) (J₁₁ : D₁₁ →L[ℂ] X₁₁)
    (W₀ : X₀₀ →L[ℂ] X₀₁) (W₁ : X₁₀ →L[ℂ] X₁₁)
    (hj₀₀ : DenseRange j₀₀) (hj₁₀ : DenseRange j₁₀)
    (hj₀₁ : DenseRange j₀₁) (hj₁₁ : DenseRange j₁₁)
    (hH₀ : ∃ (U : ℕ → D₀₀ →L[ℂ] X₁₀) (Ua : ℕ → D₁₀ →L[ℂ] X₀₀),
      (∀ m u, U m (j₀₀ u) = out₁₀ (qH₀ m (s₀₀ u))) ∧
      (∀ m v, Ua m (j₁₀ v) = out₀₀ (qH₀a m (s₁₀ v))) ∧
      Tendsto (fun m ↦ U m + (0 : X₀₀ →L[ℂ] X₁₀).comp J₀₀) atTop (𝓝 BH₀) ∧
      Tendsto (fun m ↦ Ua m + (0 : X₀₀ →L[ℂ] X₁₀).adjoint.comp J₁₀)
        atTop (𝓝 BH₀a))
    (hH₁ : ∃ (U : ℕ → D₀₁ →L[ℂ] X₁₁) (Ua : ℕ → D₁₁ →L[ℂ] X₀₁),
      (∀ m u, U m (j₀₁ u) = out₁₁ (qH₁ m (s₀₁ u))) ∧
      (∀ m v, Ua m (j₁₁ v) = out₀₁ (qH₁a m (s₁₁ v))) ∧
      Tendsto (fun m ↦ U m + (0 : X₀₁ →L[ℂ] X₁₁).comp J₀₁) atTop (𝓝 BH₁) ∧
      Tendsto (fun m ↦ Ua m + (0 : X₀₁ →L[ℂ] X₁₁).adjoint.comp J₁₁)
        atTop (𝓝 BH₁a))
    (hV₀ : ∃ (V : ℕ → D₀₀ →L[ℂ] X₀₁) (Va : ℕ → D₀₁ →L[ℂ] X₀₀),
      (∀ m u, V m (j₀₀ u) = out₀₁ (qV₀ m (s₀₀ u))) ∧
      (∀ m v, Va m (j₀₁ v) = out₀₀ (qV₀a m (s₀₁ v))) ∧
      Tendsto (fun m ↦ V m + W₀.comp J₀₀) atTop (𝓝 BV₀) ∧
      Tendsto (fun m ↦ Va m + W₀.adjoint.comp J₀₁) atTop (𝓝 BV₀a))
    (hV₁ : ∃ (V : ℕ → D₁₀ →L[ℂ] X₁₁) (Va : ℕ → D₁₁ →L[ℂ] X₁₀),
      (∀ m u, V m (j₁₀ u) = out₁₁ (qV₁ m (s₁₀ u))) ∧
      (∀ m v, Va m (j₁₁ v) = out₁₀ (qV₁a m (s₁₁ v))) ∧
      Tendsto (fun m ↦ V m + W₁.comp J₁₀) atTop (𝓝 BV₁) ∧
      Tendsto (fun m ↦ Va m + W₁.adjoint.comp J₁₁) atTop (𝓝 BV₁a)) :
    let cXE := WithLp.prodContinuousLinearEquiv 2 ℂ D₀₀ D₁₁
    let cXO := WithLp.prodContinuousLinearEquiv 2 ℂ D₁₀ D₀₁
    let cEven := WithLp.prodContinuousLinearEquiv 2 ℂ X₀₀ X₁₁
    let cOdd := WithLp.prodContinuousLinearEquiv 2 ℂ X₁₀ X₀₁
    (∀ u v, phiPlus (nativePlusOne (sumPlus (s₀₀ u, s₁₁ v))) =
      cXE.symm (j₀₀ u, j₁₁ v)) →
    (∀ u v, phiMinus (nativeMinusOne (sumMinus (s₁₀ u, s₀₁ v))) =
      cXO.symm (j₁₀ u, j₀₁ v)) →
    (∀ u v, psiPlus (nativePlusZero (sumPlus (s₀₀ u, s₁₁ v))) =
      cEven.symm (out₀₀ (s₀₀ u), out₁₁ (s₁₁ v))) →
    (∀ u v, psiMinus (nativeMinusZero (sumMinus (s₁₀ u, s₀₁ v))) =
      cOdd.symm (out₁₀ (s₁₀ u), out₀₁ (s₀₁ v))) →
    (∀ m s, R m (nativePlusOne s) = nativeMinusZero (K m s)) →
    (∀ m s, Ra m (nativeMinusOne s) = nativePlusZero (Ka m s)) →
    (∀ m a b, K m (sumPlus (a, b)) =
      sumMinus (qH₀ m a - qV₁a m b, qV₀ m a + qH₁a m b)) →
    (∀ m a b, Ka m (sumMinus (a, b)) =
      sumPlus (qH₀a m a + qV₀a m b, -qV₁ m a + qH₁ m b)) →
    let T := fun m ↦ psiMinus.toContinuousLinearMap.comp
      ((R m).comp phiPlus.symm.toContinuousLinearMap)
    let S := fun m ↦ psiPlus.toContinuousLinearMap.comp
      ((Ra m).comp phiMinus.symm.toContinuousLinearMap)
    let pE₀ := (ContinuousLinearMap.fst ℂ D₀₀ D₁₁).comp cXE.toContinuousLinearMap
    let pE₁ := (ContinuousLinearMap.snd ℂ D₀₀ D₁₁).comp cXE.toContinuousLinearMap
    let pO₀ := (ContinuousLinearMap.fst ℂ D₁₀ D₀₁).comp cXO.toContinuousLinearMap
    let pO₁ := (ContinuousLinearMap.snd ℂ D₁₀ D₀₁).comp cXO.toContinuousLinearMap
    let WE := cOdd.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inr ℂ X₁₀ X₀₁).comp (W₀.comp (J₀₀.comp pE₀))) +
      cOdd.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inl ℂ X₁₀ X₀₁).comp ((-W₁.adjoint).comp (J₁₁.comp pE₁)))
    let WO := cEven.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inl ℂ X₀₀ X₁₁).comp (W₀.adjoint.comp (J₀₁.comp pO₁))) +
      cEven.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inr ℂ X₀₀ X₁₁).comp ((-W₁).comp (J₁₀.comp pO₀)))
    Tendsto (fun m ↦ T m + WE) atTop (𝓝 (gradedBlockOperator BH₀ BV₀ BV₁a BH₁a)) ∧
      Tendsto (fun m ↦ S m + WO) atTop
        (𝓝 (cEven.symm.toContinuousLinearMap.comp
          (((BH₀a.coprod BV₀a).prod ((-BV₁).coprod BH₁)).comp cXO.toContinuousLinearMap))) := by
  intro cXE cXO cEven cOdd hPhiPlus hPhiMinus hPsiPlus hPsiMinus
    hR hRa hK hKa T S pE₀ pE₁ pO₀ pO₁ WE WO
  -- Keep both smooth values and both limits tied to each single corner-pair witness.
  obtain ⟨TH₀, SH₀, hTH₀, hSH₀, hlimH₀, hlimaH₀⟩ := hH₀
  obtain ⟨TH₁, SH₁, hTH₁, hSH₁, hlimH₁, hlimaH₁⟩ := hH₁
  obtain ⟨TV₀, SV₀, hTV₀, hSV₀, hlimV₀, hlimaV₀⟩ := hV₀
  obtain ⟨TV₁, SV₁, hTV₁, hSV₁, hlimV₁, hlimaV₁⟩ := hV₁
  -- The supplied section equivalences extend the original coordinate formulas to native cores.
  have hPsiPlusNative (a : S₀₀) (b : S₁₁) :
      psiPlus (nativePlusZero (sumPlus (a, b))) = cEven.symm (out₀₀ a, out₁₁ b) := by
    simpa only [LinearEquiv.apply_symm_apply] using hPsiPlus (s₀₀.symm a) (s₁₁.symm b)
  have hPsiMinusNative (a : S₁₀) (b : S₀₁) :
      psiMinus (nativeMinusZero (sumMinus (a, b))) = cOdd.symm (out₁₀ a, out₀₁ b) := by
    simpa only [LinearEquiv.apply_symm_apply] using hPsiMinus (s₁₀.symm a) (s₀₁.symm b)
  have hdenseE : DenseRange (fun p : C₀₀ × C₁₁ ↦ cXE.symm (j₀₀ p.1, j₁₁ p.2)) :=
    cXE.symm.surjective.denseRange.comp (hj₀₀.prodMap hj₁₁) cXE.symm.continuous
  have hdenseO : DenseRange (fun p : C₁₀ × C₀₁ ↦ cXO.symm (j₁₀ p.1, j₀₁ p.2)) :=
    cXO.symm.surjective.denseRange.comp (hj₁₀.prodMap hj₀₁) cXO.symm.continuous
  -- Identify the prescribed forward map using its actual native matrix and these same witnesses.
  have hT (m : ℕ) : T m = gradedBlockOperator (TH₀ m) (TV₀ m) (SV₁ m) (SH₁ m) := by
    exact conjugate_eq_gradedBlockOperator_of_dense_core
      j₀₀ j₁₁ s₀₀.toLinearMap s₁₁.toLinearMap out₁₀ out₀₁ sumPlus sumMinus
      nativePlusOne nativeMinusZero phiPlus psiMinus (K m) (R m)
      (qH₀ m) (qV₀ m) (qV₁a m) (qH₁a m) (TH₀ m) (TV₀ m) (SV₁ m) (SH₁ m)
      hdenseE hPhiPlus hPsiMinusNative (hR m) (hK m)
      (hTH₀ m) (hTV₀ m) (hSV₁ m) (hSH₁ m)
  have hS (m : ℕ) : S m =
      gradedBlockOperator (SH₀ m) (-TV₁ m) (-SV₀ m) (TH₁ m) := by
    -- The reverse matrix keeps its upper-right plus and lower-left minus signs.
    refine conjugate_eq_gradedBlockOperator_of_dense_core
      j₁₀ j₀₁ s₁₀.toLinearMap s₀₁.toLinearMap out₀₀ out₁₁ sumMinus sumPlus
      nativeMinusOne nativePlusZero phiMinus psiPlus (Ka m) (Ra m)
      (qH₀a m) (-qV₁ m) (-qV₀a m) (qH₁ m) (SH₀ m) (-TV₁ m) (-SV₀ m) (TH₁ m)
      hdenseO hPhiMinus hPsiPlusNative (hRa m) ?_ (hSH₀ m) ?_ ?_ (hTH₁ m)
    · intro a b
      exact (hKa m a b).trans (congrArg sumPlus
        (Prod.ext (sub_neg_eq_add (qH₀a m a) (qV₀a m b)).symm rfl))
    · intro u
      change -(TV₁ m (j₁₀ u)) = out₁₁ (-(qV₁ m (s₁₀ u)))
      exact (congrArg (fun w : X₁₁ ↦ -w) (hTV₁ m u)).trans
        (map_neg out₁₁ (qV₁ m (s₁₀ u))).symm
    · intro v
      change -(SV₀ m (j₀₁ v)) = out₀₀ (-(qV₀a m (s₀₁ v)))
      exact (congrArg (fun w : X₀₀ ↦ -w) (hSV₀ m v)).trans
        (map_neg out₀₀ (qV₀a m (s₀₁ v))).symm
  constructor
  · -- Correct the same forward map by the original residuals and domain inclusions.
    exact tendsto_gradedBlockOperator_add_factoredOffDiagonal
      T TH₀ TV₀ SV₁ SH₁ BH₀ BV₀ BV₁a BH₁a J₀₀ J₁₁ W₀ W₁.adjoint
      (0 : X₀₀ →L[ℂ] X₁₀) ((0 : X₀₁ →L[ℂ] X₁₁).adjoint)
      rfl (map_zero (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := X₀₁) (F := X₁₁)))
      hT hlimH₀ hlimV₀ hlimaV₁ hlimaH₁
  · -- The reverse correction uses the opposite residual order and literal residual adjoint.
    exact tendsto_gradedBlockOperator_reverse_add_factoredOffDiagonal
      S SH₀ TV₁ SV₀ TH₁ BH₀a BV₁ BV₀a BH₁ J₁₀ J₀₁ W₁ W₀.adjoint
      ((0 : X₀₀ →L[ℂ] X₁₀).adjoint) (0 : X₀₁ →L[ℂ] X₁₁)
      (map_zero (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := X₀₀) (F := X₁₀))) rfl
      hS hlimaH₀ hlimV₁ hlimaV₀ hlimH₁

end AtiyahSinger
