/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalHomogeneousSymbol
public import AtiyahSinger.Analysis.PseudodifferentialRegularity

/-!
# Quantization of homogeneous principal data

Public module ID: M0742.

D05/A02/A03: regularize smooth punctured homogeneous data and apply the existing
finite-presentation quantization. The regularization and quantization presentations
are separate choices. Varying only the former changes the operator by a smooth
kernel. Varying the latter is covered by the earlier one-order comparison instead.
These are interfaces for SG III.13 (13.5), not a general parameter topology or a
cosphere-bundle construction. The fixed-quantizer comparisons are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable {E F}
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

namespace QuantizationPresentation

variable (C A B : QuantizationPresentation (n := n) (r := r) (q := q) E F)

set_option linter.unusedSectionVars false in
/-- A fixed quantizer depends on the actual symbol function, not its certified order bound. -/
theorem toLinearMap_eq_of_symbol_eq {m l : ℝ}
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (p' : globalSymbolSpace (n := n) (r := r) (q := q) E F l) (h : p.val = p'.val) :
    C.toLinearMap p = C.toLinearMap p' := by
  /- Stage 1: h identifies the two actual cutoff coordinate symbols in each patch.
  The quantizeSchwartz_apply formula identifies the actions of their chosen Schwartz
  maps, regardless of the two order certificates. Extensionality gives identical maps.
  Stage 2: compose with the same input and output section maps and add the same finite
  family. Thus passing a symbol to another order never changes this quantizer's action. -/
  classical
  -- Compare the exact Schwartz actions before composing with the fixed section maps.
  have hpatch (Q : QuantizationPatch (n := n) (r := r) (q := q) E F) :
      (Q.toPiece p).operator = (Q.toPiece p').operator := by
    apply ContinuousLinearMap.ext
    intro u
    apply SchwartzMap.ext
    intro x
    calc
      (Q.toPiece p).operator u x = AtiyahSinger.quantize (Q.localSymbol p.val) u x :=
        (Q.toPiece p).operator_apply u x
      _ = AtiyahSinger.quantize (Q.localSymbol p'.val) u x := by rw [h]
      _ = (Q.toPiece p').operator u x := ((Q.toPiece p').operator_apply u x).symm
  -- The same finite family and the same localization/extension maps preserve this equality.
  unfold toLinearMap
  apply Finset.sum_congr rfl
  intro j _
  change ((C.patch j).output.extendLinearMap _).comp
    (((C.patch j).toPiece p).operator.toLinearMap.comp
      ((C.patch j).input.localizeLinearMap _)) = _
  rw [hpatch (C.patch j)]
  rfl

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

/-- Quantize the explicit regularized representative, keeping both auxiliary choices visible. -/
def quantizeHomogeneous (m : ℝ) (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) :
    PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m :=
  C.quantize μ (A.regularizedSymbol m a hs hh)

/-- The operator realizes precisely the regularized homogeneous principal class. -/
theorem principalSymbol_quantizeHomogeneous (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) :
    (C.quantizeHomogeneous A μ m a hs hh).principalSymbol =
      globalPrincipalSymbolClass E F m (A.regularizedSymbol m a hs hh) := by
  /- Apply principalSymbol_quantize to the chosen regularized global symbol.
  This identifies precisely the class displayed in the statement, retaining
  both the regularization presentation and the quantizer. -/
  exact C.principalSymbol_quantize μ (A.regularizedSymbol m a hs hh)

/-- With the quantizer fixed, changing regularization changes the operator by a smooth kernel. -/
theorem isSmoothingOperator_sub_quantizeHomogeneous (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a)
    (S : SmoothBundlePresentation (n := n) (r := r) E)
    (T : SmoothBundlePresentation (n := n) (r := q) F) :
    IsSmoothingOperator μ
      ((C.quantizeHomogeneous A μ m a hs hh).toLinearMap -
        (C.quantizeHomogeneous B μ m a hs hh).toLinearMap) := by
  /- Stage 1: the difference of the A and B representatives is a symbol of every
  real order by isGlobalSymbol_sub_regularizedSymbolFunction. Fixed-C linearity and
  toLinearMap_eq_of_symbol_eq identify each such quantization with the same displayed
  difference of section operators; the operator is not reselected at each order.
  Stage 2: apply isSmoothingOperator_iff_forall_isPseudodifferentialOperator with S,T.
  The resulting kernel is smooth for the fixed positive density. Keeping C fixed is
  essential here: changing quantization charts can instead introduce order-(m-1) terms. -/
  apply (isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ _ S T).mpr
  intro l
  let p := A.regularizedSymbol m a hs hh
  let pB := B.regularizedSymbol m a hs hh
  let d : globalSymbolSpace (n := n) (r := r) (q := q) E F l :=
    ⟨A.regularizedSymbolFunction a - B.regularizedSymbolFunction a,
      A.isGlobalSymbol_sub_regularizedSymbolFunction B m a hs hh l⟩
  -- The fixed quantizer preserves the actual difference at each available order.
  have hd : C.toLinearMap d = C.toLinearMap p - C.toLinearMap pB := by
    calc
      C.toLinearMap d = C.toLinearMap (p - pB) :=
        C.toLinearMap_eq_of_symbol_eq d (p - pB) rfl
      _ = C.toLinearMap p - C.toLinearMap pB :=
        (C.quantizationLinearMap (m := m)).map_sub p pB
  have hPDO := C.isPseudodifferentialOperator_toLinearMap μ d
  rw [hd] at hPDO
  exact hPDO

end QuantizationPresentation

end AtiyahSinger
