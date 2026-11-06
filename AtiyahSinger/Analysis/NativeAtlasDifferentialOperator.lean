/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPrincipalSymbol
public import AtiyahSinger.Analysis.GlobalDifferentialOperator
public import AtiyahSinger.Geometry.NativeSmoothAtlas
public import AtiyahSinger.Geometry.SmoothAtlasSections

/-!
# Native differential operators in the locally finite-rank atlas presentation

Public module ID: M0801.

D03: embed the original fixed-rank differential operators into the atlas
presentation while retaining every section value, base point and cotangent
vector. The section equivalence is the identity on the original dependent
functions, using the established equivalence of the two smoothness predicates.
The converted operator is the composite of this equivalence, the original
section map, and the inverse target equivalence. Its principal symbol equals
the original principal symbol as an entire dependent function.

This is a compatibility construction for the coordinate-independent symbol
of SG III.1.1--1.3, p.167. The canonical Euclidean/finite-product coordinate
equivalences cancel in local differential expressions. No new operator,
choice of fiber basis, metric, density, compactness or constant-rank assertion
about unrelated atlas bundles is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

/-- The identity on the original sections identifies the atlas and native smooth section spaces. -/
def nativeSmoothSectionLinearEquiv :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    (nativeSmoothComplexBundleAtlas (n := n) (r := r) E).smoothSections ≃ₗ[ℂ]
      smoothSections (n := n) (r := r) E :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  { toFun := fun s ↦
      ⟨s.val, (isSmoothSection_nativeSmoothComplexBundleAtlas_iff
        (n := n) (r := r) E s.val).mp s.property⟩
    invFun := fun s ↦
      ⟨s.val, (isSmoothSection_nativeSmoothComplexBundleAtlas_iff
        (n := n) (r := r) E s.val).mpr s.property⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

variable {E} {q : ℕ} {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]

namespace DifferentialOperator

variable {d : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F d)

-- Preserve the original manifold hypotheses; this coordinate transport needs no extra ones.
set_option linter.unusedSectionVars false in
/-- The original differential expression is retained under the identity section equivalences. -/
theorem isAtlasDifferentialOperator_native :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    IsAtlasDifferentialOperator
      (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
      (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) d
      ((nativeSmoothSectionLinearEquiv (n := n) (r := q) F).symm.toLinearMap.comp
        (P.toLinearMap.comp (nativeSmoothSectionLinearEquiv (n := n) (r := r) E).toLinearMap)) := by
  /- Stage 1: a chart in either converted atlas is indexed by an original
  designated native chart, with the same base set. The conversion to finite
  coordinates and the atlas expression's conversion back to Euclidean
  coordinates are inverse canonical linear maps. Therefore the local
  section coordinates are exactly the old sectionInChart coordinates.
  Stage 2: the two section equivalences preserve the original fiber values.
  At every common chart point choose the local coordinate differential
  expression supplied by P.isDifferentialOperator. Use the same open
  neighborhood, same coefficients and same order bound in the new
  predicate. Its pointwise output identity is the original identity after
  the coordinate cancellations; no derivatives of a changed frame occur.
  This covers all charts, including rank-zero charts and an empty base. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  intro c hc i j x hx
  let := i.property
  let := j.property
  -- Use the designated native charts and the original local differential expression.
  obtain ⟨U, hU, hxU, Q, hQ⟩ := P.isDifferentialOperator c hc i.val j.val x hx
  refine ⟨U, hU, hxU, Q, hQ.1, ?_⟩
  intro s y hy
  have hlocal := hQ.2 ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E) s) y hy
  -- The two model conversions cancel pointwise, before any derivative is taken.
  have hcoord :
      atlasSectionInChart (nativeSmoothComplexBundleAtlas (n := n) (r := r) E) c i s.val =
        sectionInChart E c i.val
          ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E) s).val := by
    funext z
    exact (EuclideanSpace.equiv (Fin r) ℂ).symm_apply_apply _
  rw [hcoord]
  -- Identity section transport also preserves the original target value in this chart.
  change (EuclideanSpace.equiv (Fin q) ℂ).symm
    ((EuclideanSpace.equiv (Fin q) ℂ)
      (j.val ⟨y, (P.toLinearMap
        ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E) s)).val y⟩).2) = _
  rw [(EuclideanSpace.equiv (Fin q) ℂ).symm_apply_apply]
  exact hlocal

/-- Regard the original operator as an atlas operator by explicit identity section transport. -/
def toAtlasDifferentialOperator :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    AtlasDifferentialOperator
      (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
      (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) d :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
  { toLinearMap :=
      (nativeSmoothSectionLinearEquiv (n := n) (r := q) F).symm.toLinearMap.comp
        (P.toLinearMap.comp (nativeSmoothSectionLinearEquiv (n := n) (r := r) E).toLinearMap)
    isAtlasDifferentialOperator := P.isAtlasDifferentialOperator_native }

set_option backward.isDefEq.respectTransparency false in
/-- The converted operator has exactly the original principal symbol on every original fiber. -/
theorem principalSymbol_toAtlasDifferentialOperator :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    P.toAtlasDifferentialOperator.principalSymbol = P.principalSymbol := by
  /- Stage 1: take any local coordinate expression for the converted
  operator. All designated native charts occur in its two atlases, and
  the section equivalences are identity on values. Cancelling the model
  equivalences identifies this expression with an expression for P on
  the same open set. The old HasPrincipalSymbol theorem therefore gives
  the atlas coordinate identity for P.principalSymbol itself.
  Stage 2: uniqueness of the atlas principal symbol identifies the newly
  selected symbol with this original dependent function. Both sides use
  the same actual real cotangent vector and complex-linear fiber map;
  there is no scalar, derivative, transpose or metric identification.
  The comparison includes zero covectors and order zero, rather than
  merely identifying symbols on the punctured cotangent bundle. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  have hσ : HasAtlasPrincipalSymbol A B d P.toAtlasDifferentialOperator.toLinearMap
      P.principalSymbol := by
    intro c hc i j U hU Q hQ x hx ξ v
    let := i.property
    let := j.property
    -- Every expression for the converted action is an expression for the same native action.
    have hnative : HasCoordinateExpression E F d P.toLinearMap c i.val j.val U Q := by
      refine ⟨hQ.1, ?_⟩
      intro s y hy
      let s' := (nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm s
      have hlocal := hQ.2 s' y hy
      have hcoords : atlasSectionInChart A c i s'.val =
          sectionInChart E c i.val s.val := by
        funext z
        exact (EuclideanSpace.equiv (Fin r) ℂ).symm_apply_apply _
      rw [hcoords] at hlocal
      change (EuclideanSpace.equiv (Fin q) ℂ).symm
        ((EuclideanSpace.equiv (Fin q) ℂ)
          (j.val ⟨y, (P.toLinearMap s).val y⟩).2) = _ at hlocal
      rw [(EuclideanSpace.equiv (Fin q) ℂ).symm_apply_apply] at hlocal
      exact hlocal
    have hnativeSymbol := LinearMap.congr_fun
      (P.hasPrincipalSymbol c hc i.val j.val U hU Q hnative x hx ξ) v
    -- Both canonical Euclidean/finite-coordinate conversions cancel on the original vectors.
    change (EuclideanSpace.equiv (Fin q) ℂ).symm
      ((EuclideanSpace.equiv (Fin q) ℂ) (j.val ⟨x, P.principalSymbol x ξ v⟩).2) =
        Q.principalSymbol (c x) (covectorInChart c x ξ)
          ((EuclideanSpace.equiv (Fin r) ℂ).symm
            ((EuclideanSpace.equiv (Fin r) ℂ) (i.val ⟨x, v⟩).2))
    rw [(EuclideanSpace.equiv (Fin q) ℂ).symm_apply_apply,
      (EuclideanSpace.equiv (Fin r) ℂ).symm_apply_apply]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      i.val.coe_linearMapAt_of_mem (hQ.1 hx).1.2,
      j.val.coe_linearMapAt_of_mem (hQ.1 hx).2] at hnativeSymbol
    exact hnativeSymbol
  -- Uniqueness compares the two entire dependent fiber-map families, including zero covectors.
  exact P.toAtlasDifferentialOperator.existsUnique_principalSymbol.unique
    P.toAtlasDifferentialOperator.hasAtlasPrincipalSymbol hσ

end DifferentialOperator

end AtiyahSinger
