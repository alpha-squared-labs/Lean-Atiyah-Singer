/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedBlockOperator
public import Mathlib.Topology.DenseEmbedding

/-!
# A bounded realization in specified dense-core block coordinates

Public module ID: M0691.

The given native matrix formula and four corner realization identities determine
the same bounded operator in the specified source and target coordinates. Density
extends that identity from the given core. No operator, coordinate or corner is
chosen by this theorem.

This project supplement abstracts the two repeated realization arguments in P05.
It uses the existing signed graded block operator, whose upper-right entry is
negative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- A native matrix realization on the specified dense core determines its bounded block map.
All four corners and both coordinate equivalences are supplied as data. -/
theorem conjugate_eq_gradedBlockOperator_of_dense_core
    {C₀ : Type*} {C₁ : Type*} {S₀ : Type*} {S₁ : Type*}
    {T₀ : Type*} {T₁ : Type*} {NS : Type*} {NT : Type*}
    {D₀ : Type*} {D₁ : Type*} {Y₀ : Type*} {Y₁ : Type*} {XI : Type*} {YO : Type*}
    [AddCommGroup C₀] [Module ℂ C₀] [AddCommGroup C₁] [Module ℂ C₁]
    [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup T₀] [Module ℂ T₀] [AddCommGroup T₁] [Module ℂ T₁]
    [AddCommGroup NS] [Module ℂ NS] [AddCommGroup NT] [Module ℂ NT]
    [NormedAddCommGroup D₀] [NormedSpace ℂ D₀]
    [NormedAddCommGroup D₁] [NormedSpace ℂ D₁]
    [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀]
    [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    [NormedAddCommGroup XI] [NormedSpace ℂ XI]
    [NormedAddCommGroup YO] [NormedSpace ℂ YO]
    (j₀ : C₀ →ₗ[ℂ] D₀) (j₁ : C₁ →ₗ[ℂ] D₁)
    (s₀ : C₀ →ₗ[ℂ] S₀) (s₁ : C₁ →ₗ[ℂ] S₁)
    (out₀ : T₀ →ₗ[ℂ] Y₀) (out₁ : T₁ →ₗ[ℂ] Y₁)
    (sumIn : (S₀ × S₁) →ₗ[ℂ] NS) (sumOut : (T₀ × T₁) →ₗ[ℂ] NT)
    (nativeIn : NS →ₗ[ℂ] XI) (nativeOut : NT →ₗ[ℂ] YO)
    (phiIn : XI ≃L[ℂ] WithLp 2 (D₀ × D₁))
    (psiOut : YO ≃L[ℂ] WithLp 2 (Y₀ × Y₁))
    (K : NS →ₗ[ℂ] NT) (R : XI →L[ℂ] YO)
    (q₀₀ : S₀ →ₗ[ℂ] T₀) (q₁₀ : S₀ →ₗ[ℂ] T₁)
    (q₀₁ : S₁ →ₗ[ℂ] T₀) (q₁₁ : S₁ →ₗ[ℂ] T₁)
    (U : D₀ →L[ℂ] Y₀) (V : D₀ →L[ℂ] Y₁)
    (W : D₁ →L[ℂ] Y₀) (block₁₁ : D₁ →L[ℂ] Y₁) :
    let cI := WithLp.prodContinuousLinearEquiv 2 ℂ D₀ D₁
    let cO := WithLp.prodContinuousLinearEquiv 2 ℂ Y₀ Y₁
    DenseRange (fun p : C₀ × C₁ ↦ cI.symm (j₀ p.1, j₁ p.2)) →
    (∀ u v, phiIn (nativeIn (sumIn (s₀ u, s₁ v))) = cI.symm (j₀ u, j₁ v)) →
    (∀ a b, psiOut (nativeOut (sumOut (a, b))) = cO.symm (out₀ a, out₁ b)) →
    (∀ s, R (nativeIn s) = nativeOut (K s)) →
    (∀ a b, K (sumIn (a, b)) = sumOut (q₀₀ a - q₀₁ b, q₁₀ a + q₁₁ b)) →
    (∀ u, U (j₀ u) = out₀ (q₀₀ (s₀ u))) →
    (∀ u, V (j₀ u) = out₁ (q₁₀ (s₀ u))) →
    (∀ v, W (j₁ v) = out₀ (q₀₁ (s₁ v))) →
    (∀ v, block₁₁ (j₁ v) = out₁ (q₁₁ (s₁ v))) →
    psiOut.toContinuousLinearMap.comp (R.comp phiIn.symm.toContinuousLinearMap) =
      gradedBlockOperator U V W block₁₁ := by
  intro cI cO hdense hinput houtput hrealization hmodel hU hV hW hblock
  let realized : WithLp 2 (D₀ × D₁) →L[ℂ] WithLp 2 (Y₀ × Y₁) :=
    psiOut.toContinuousLinearMap.comp (R.comp phiIn.symm.toContinuousLinearMap)
  change realized = gradedBlockOperator U V W block₁₁
  -- Equality on the supplied dense core determines these two continuous maps.
  ext x
  refine hdense.induction_on x
    (isClosed_eq realized.continuous
      (gradedBlockOperator U V W block₁₁).continuous) ?_
  rintro ⟨u, v⟩
  let s : NS := sumIn (s₀ u, s₁ v)
  -- Cancel the exact source coordinate before applying the native realization.
  have hsource : phiIn.symm (cI.symm (j₀ u, j₁ v)) = nativeIn s :=
    (congrArg phiIn.symm (hinput u v)).symm.trans
      (phiIn.symm_apply_apply (nativeIn s))
  have hrealize : realized (cI.symm (j₀ u, j₁ v)) = psiOut (nativeOut (K s)) :=
    (congrArg (fun w : XI ↦ psiOut (R w)) hsource).trans
      (congrArg psiOut (hrealization s))
  -- The native matrix and the specified target sum use these same two sections.
  have hnative : psiOut (nativeOut (K s)) =
      cO.symm (out₀ (q₀₀ (s₀ u) - q₀₁ (s₁ v)),
        out₁ (q₁₀ (s₀ u) + q₁₁ (s₁ v))) :=
    (congrArg (fun w : NT ↦ psiOut (nativeOut w)) (hmodel (s₀ u) (s₁ v))).trans
      (houtput (q₀₀ (s₀ u) - q₀₁ (s₁ v)) (q₁₀ (s₀ u) + q₁₁ (s₁ v)))
  -- Identify both rows, retaining the negative upper-right block convention.
  have hfirst : out₀ (q₀₀ (s₀ u) - q₀₁ (s₁ v)) = U (j₀ u) + -(W (j₁ v)) := by
    calc
      _ = out₀ (q₀₀ (s₀ u)) - out₀ (q₀₁ (s₁ v)) := map_sub out₀ _ _
      _ = U (j₀ u) - W (j₁ v) :=
        congrArg₂ (fun a b : Y₀ ↦ a - b) (hU u).symm (hW v).symm
      _ = U (j₀ u) + -(W (j₁ v)) := sub_eq_add_neg _ _
  have hsecond : out₁ (q₁₀ (s₀ u) + q₁₁ (s₁ v)) =
      V (j₀ u) + block₁₁ (j₁ v) :=
    (map_add out₁ _ _).trans
      (congrArg₂ (fun a b : Y₁ ↦ a + b) (hV u).symm (hblock v).symm)
  change _ = cO.symm (U (j₀ u) + -(W (j₁ v)), V (j₀ u) + block₁₁ (j₁ v))
  exact hrealize.trans (hnative.trans (congrArg cO.symm (Prod.ext hfirst hsecond)))

end AtiyahSinger
