/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedBlockAlgebra
public import AtiyahSinger.Analysis.GradedBlockLimit

/-!
# Limits of graded blocks with specified factored corrections

Public module ID: M0686.

The same four corner families, two off-diagonal residuals and two inclusion maps
give an operator-norm limit for the corrected block family. The reverse formula
retains its two negative corners, the opposite residual order and the original
explicit target matrix.

The horizontal residuals are supplied together with their zero identities. This
allows a caller to retain a literal adjoint of zero without introducing Hilbert
space assumptions into the block argument. No family, residual or coordinate
equivalence is selected here. These are project-level consequences of the
existing graded block algebra and limit theorems, used by the index comparison assembly.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter
open scoped Topology

variable {E₀ E₁ F₀ F₁ G₀ G₁ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup F₀] [NormedSpace ℂ F₀]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [NormedAddCommGroup G₀] [NormedSpace ℂ G₀]
  [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]

/-- Correcting the actual block family by the specified factored off-diagonal maps
gives the matrix of its four original corner limits. -/
theorem tendsto_gradedBlockOperator_add_factoredOffDiagonal
    (T : ℕ → WithLp 2 (E₀ × E₁) →L[ℂ] WithLp 2 (F₀ × F₁))
    (U : ℕ → E₀ →L[ℂ] F₀) (V : ℕ → E₀ →L[ℂ] F₁)
    (W : ℕ → E₁ →L[ℂ] F₀) (Z : ℕ → E₁ →L[ℂ] F₁)
    (u : E₀ →L[ℂ] F₀) (v : E₀ →L[ℂ] F₁)
    (w : E₁ →L[ℂ] F₀) (z : E₁ →L[ℂ] F₁)
    (J₀ : E₀ →L[ℂ] G₀) (J₁ : E₁ →L[ℂ] G₁)
    (R₀ : G₀ →L[ℂ] F₁) (R₁ : G₁ →L[ℂ] F₀)
    (Q₀ : G₀ →L[ℂ] F₀) (Q₁ : G₁ →L[ℂ] F₁)
    (hQ₀ : Q₀ = 0) (hQ₁ : Q₁ = 0)
    (hT : ∀ m, T m = gradedBlockOperator (U m) (V m) (W m) (Z m))
    (hU : Tendsto (fun m ↦ U m + Q₀.comp J₀) atTop (𝓝 u))
    (hV : Tendsto (fun m ↦ V m + R₀.comp J₀) atTop (𝓝 v))
    (hW : Tendsto (fun m ↦ W m + R₁.comp J₁) atTop (𝓝 w))
    (hZ : Tendsto (fun m ↦ Z m + Q₁.comp J₁) atTop (𝓝 z)) :
    let cI := WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁
    let cO := WithLp.prodContinuousLinearEquiv 2 ℂ F₀ F₁
    let p₀ := (ContinuousLinearMap.fst ℂ E₀ E₁).comp cI.toContinuousLinearMap
    let p₁ := (ContinuousLinearMap.snd ℂ E₀ E₁).comp cI.toContinuousLinearMap
    Tendsto (fun m ↦ T m +
      (cO.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inr ℂ F₀ F₁).comp (R₀.comp (J₀.comp p₀))) +
      cO.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inl ℂ F₀ F₁).comp ((-R₁).comp (J₁.comp p₁)))))
      atTop (𝓝 (gradedBlockOperator u v w z)) := by
  intro cI cO p₀ p₁
  -- Remove only the two supplied zero horizontal residuals.
  have hU' : Tendsto U atTop (𝓝 u) := by
    simpa only [hQ₀, ContinuousLinearMap.zero_comp, add_zero] using hU
  have hZ' : Tendsto Z atTop (𝓝 z) := by
    simpa only [hQ₁, ContinuousLinearMap.zero_comp, add_zero] using hZ
  -- The correction uses these exact inclusion maps, projections and residuals.
  let correction : WithLp 2 (E₀ × E₁) →L[ℂ] WithLp 2 (F₀ × F₁) :=
    cO.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inr ℂ F₀ F₁).comp (R₀.comp (J₀.comp p₀))) +
    cO.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inl ℂ F₀ F₁).comp ((-R₁).comp (J₁.comp p₁)))
  have hcorrected (m : ℕ) : T m + correction =
      gradedBlockOperator (U m) (V m + R₀.comp J₀) (W m + R₁.comp J₁) (Z m) := by
    calc
      T m + correction =
          gradedBlockOperator (U m) (V m) (W m) (Z m) + correction :=
        congrArg (fun A ↦ A + correction) (hT m)
      _ = gradedBlockOperator (U m) (V m + R₀.comp J₀)
          (W m + R₁.comp J₁) (Z m) := by
        simpa only [correction, p₀, p₁, cI, cO, ContinuousLinearMap.comp_assoc,
          ContinuousLinearMap.neg_comp] using
          gradedBlockOperator_add_offDiagonal (U m) (V m) (W m) (Z m)
            (R₀.comp J₀) (R₁.comp J₁)
  -- Entrywise convergence now applies to the same corrected family.
  have hblocks : Tendsto (fun m ↦
      gradedBlockOperator (U m) (V m + R₀.comp J₀) (W m + R₁.comp J₁) (Z m))
      atTop (𝓝 (gradedBlockOperator u v w z)) :=
    tendsto_gradedBlockOperator U (fun m ↦ V m + R₀.comp J₀)
      (fun m ↦ W m + R₁.comp J₁) Z u v w z hU' hV hW hZ'
  exact Filter.Tendsto.congr (fun m ↦ (hcorrected m).symm) hblocks

/-- The reverse signed family converges with its original residual order and with
the positive upper-right and negative lower-left entries in the target matrix. -/
theorem tendsto_gradedBlockOperator_reverse_add_factoredOffDiagonal
    (T : ℕ → WithLp 2 (E₀ × E₁) →L[ℂ] WithLp 2 (F₀ × F₁))
    (U : ℕ → E₀ →L[ℂ] F₀) (V : ℕ → E₀ →L[ℂ] F₁)
    (W : ℕ → E₁ →L[ℂ] F₀) (Z : ℕ → E₁ →L[ℂ] F₁)
    (u : E₀ →L[ℂ] F₀) (v : E₀ →L[ℂ] F₁)
    (w : E₁ →L[ℂ] F₀) (z : E₁ →L[ℂ] F₁)
    (J₀ : E₀ →L[ℂ] G₀) (J₁ : E₁ →L[ℂ] G₁)
    (R₀ : G₀ →L[ℂ] F₁) (R₁ : G₁ →L[ℂ] F₀)
    (Q₀ : G₀ →L[ℂ] F₀) (Q₁ : G₁ →L[ℂ] F₁)
    (hQ₀ : Q₀ = 0) (hQ₁ : Q₁ = 0)
    (hT : ∀ m, T m = gradedBlockOperator (U m) (-V m) (-W m) (Z m))
    (hU : Tendsto (fun m ↦ U m + Q₀.comp J₀) atTop (𝓝 u))
    (hV : Tendsto (fun m ↦ V m + R₀.comp J₀) atTop (𝓝 v))
    (hW : Tendsto (fun m ↦ W m + R₁.comp J₁) atTop (𝓝 w))
    (hZ : Tendsto (fun m ↦ Z m + Q₁.comp J₁) atTop (𝓝 z)) :
    let cI := WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁
    let cO := WithLp.prodContinuousLinearEquiv 2 ℂ F₀ F₁
    let p₀ := (ContinuousLinearMap.fst ℂ E₀ E₁).comp cI.toContinuousLinearMap
    let p₁ := (ContinuousLinearMap.snd ℂ E₀ E₁).comp cI.toContinuousLinearMap
    Tendsto (fun m ↦ T m +
      (cO.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inl ℂ F₀ F₁).comp (R₁.comp (J₁.comp p₁))) +
      cO.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inr ℂ F₀ F₁).comp ((-R₀).comp (J₀.comp p₀)))))
      atTop (𝓝 (cO.symm.toContinuousLinearMap.comp
        (((u.coprod w).prod ((-v).coprod z)).comp cI.toContinuousLinearMap))) := by
  intro cI cO p₀ p₁
  -- Negate the two corrected corners without changing either inclusion map.
  have hVneg : Tendsto (fun m ↦ -V m + (-R₀).comp J₀) atTop (𝓝 (-v)) := by
    simpa only [ContinuousLinearMap.neg_comp, neg_add] using hV.neg
  have hWneg : Tendsto (fun m ↦ -W m + (-R₁).comp J₁) atTop (𝓝 (-w)) := by
    simpa only [ContinuousLinearMap.neg_comp, neg_add] using hW.neg
  let correctionForward : WithLp 2 (E₀ × E₁) →L[ℂ] WithLp 2 (F₀ × F₁) :=
    cO.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inr ℂ F₀ F₁).comp ((-R₀).comp (J₀.comp p₀))) +
    cO.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inl ℂ F₀ F₁).comp ((-(-R₁)).comp (J₁.comp p₁)))
  let correctionReverse : WithLp 2 (E₀ × E₁) →L[ℂ] WithLp 2 (F₀ × F₁) :=
    cO.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inl ℂ F₀ F₁).comp (R₁.comp (J₁.comp p₁))) +
    cO.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inr ℂ F₀ F₁).comp ((-R₀).comp (J₀.comp p₀)))
  have hforward : Tendsto (fun m ↦ T m + correctionForward) atTop
      (𝓝 (gradedBlockOperator u (-v) (-w) z)) :=
    tendsto_gradedBlockOperator_add_factoredOffDiagonal T U (fun m ↦ -V m)
      (fun m ↦ -W m) Z u (-v) (-w) z J₀ J₁ (-R₀) (-R₁) Q₀ Q₁
      hQ₀ hQ₁ hT hU hVneg hWneg hZ
  -- The original reverse correction lists the upper-right summand first.
  have hcorrection : correctionForward = correctionReverse := by
    dsimp only [correctionForward, correctionReverse]
    rw [neg_neg]
    exact add_comm _ _
  have htransport : Tendsto (fun m ↦ T m + correctionReverse) atTop
      (𝓝 (gradedBlockOperator u (-v) (-w) z)) :=
    Filter.Tendsto.congr
      (fun m ↦ congrArg (fun R ↦ T m + R) hcorrection) hforward
  -- Cancel only the double negation in the target's upper-right corner.
  have htarget : gradedBlockOperator u (-v) (-w) z =
      cO.symm.toContinuousLinearMap.comp
        (((u.coprod w).prod ((-v).coprod z)).comp cI.toContinuousLinearMap) := by
    exact congrArg (fun corner : E₁ →L[ℂ] F₀ ↦
      cO.symm.toContinuousLinearMap.comp
        (((u.coprod corner).prod ((-v).coprod z)).comp cI.toContinuousLinearMap))
      (neg_neg w)
  exact htarget ▸ htransport

end AtiyahSinger
