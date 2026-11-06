/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.VariableRankDifferentialOperator
public import AtiyahSinger.Geometry.AtlasFrame
public import AtiyahSinger.Geometry.TangentConnectionExistence

/-!
# Smooth connections in a locally finite-rank complex bundle atlas

Public module ID: M1090.

A01: a smooth complex connection is specified by its smooth local matrix-valued
one-forms. Their overlap condition is expressed on the original fiber values of
the usual local formula d u + Gamma u. This is the standard connection-form
transformation law, equivalently tested on smooth sections and tangent vectors.
No norm, fixed global fiber rank, or family of higher derivative operators is
part of the definition. The first derivative is constructed from these data.

The inverse frames, section coordinates and tangent vectors all belong to the
original bundle. On a smooth Hausdorff second-countable manifold, local first
jets are realized by supported global smooth sections; thus the overlap test
does not weaken the usual gauge/base-coordinate transformation law. Existence
uses the ordinary smooth partition-of-unity construction for connections.
Sources: Spin Geometry II.4 and III.2, p.170, together with the standard local
connection-form description. The varying-rank atlas implementation is a project
supplement to the native fixed-model connection API.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  (A : SmoothComplexBundleAtlas (n := n) E)

/-- The local connection formula, returned to the original fiber through the original frame.
This is an implementation expression for the standard operation d u + Gamma u. -/
def atlasConnectionExpression
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (i : A.Index)
    (Γ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ] EuclideanSpace ℂ (Fin (A.rank i))))
    (u : A.smoothSections) (x : M) (hx : x ∈ (A.chart i).baseSet)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) : E x :=
  (A.frameLinearEquiv i x hx).symm
    ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ)
      (fderiv ℝ (atlasSectionInChart A c i u.val) (c x)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c x v) +
        Γ (c x)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c x v)
          (atlasSectionInChart A c i u.val (c x))))

/-- A smooth complex connection given by compatible local connection one-forms. -/
structure AtlasComplexConnection where
  /-- The complex endomorphism-valued real one-form in each original local frame. -/
  connectionForm :
    ∀ (_c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (i : A.Index),
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
        (EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ] EuclideanSpace ℂ (Fin (A.rank i)))
  /-- The coefficient function is smooth on precisely the valid coordinate/frame region. -/
  smooth_connectionForm :
    ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      c ∈ atlas (EuclideanSpace ℝ (Fin n)) M → ∀ i : A.Index,
        ContDiffOn ℝ ∞ (connectionForm c i)
          (c.target ∩ c.symm ⁻¹' (A.chart i).baseSet)
  /-- Local first derivatives give the same actual fiber vector on every overlap. -/
  compatible :
    ∀ (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      d ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ∀ (i j : A.Index) (u : A.smoothSections) (x : M)
        (hx : x ∈ c.source ∩ (A.chart i).baseSet)
        (hy : x ∈ d.source ∩ (A.chart j).baseSet)
        (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
        atlasConnectionExpression A c i (connectionForm c i) u x hx.2 v =
          atlasConnectionExpression A d j (connectionForm d j) u x hy.2 v

namespace AtlasComplexConnection

variable {A} (cov : AtlasComplexConnection A)

/-- The actual covariant derivative of the original section, in an actual tangent direction. -/
def covariantDerivative (u : A.smoothSections) (x : M)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) : E x :=
  atlasConnectionExpression A (chartAt (EuclideanSpace ℝ (Fin n)) x)
    (Classical.choose (A.covers x))
    (cov.connectionForm (chartAt (EuclideanSpace ℝ (Fin n)) x)
      (Classical.choose (A.covers x)))
    u x (Classical.choose_spec (A.covers x)) v

/-- Every valid original frame computes that same covariant derivative. -/
theorem covariantDerivative_eq (u : A.smoothSections)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index)
    (x : M) (hx : x ∈ c.source ∩ (A.chart i).baseSet)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    cov.covariantDerivative u x v =
      atlasConnectionExpression A c i (cov.connectionForm c i) u x hx.2 v := by
  /- The distinguished manifold chart contains x, and the selected original
  bundle chart contains x by A.covers. Apply the compatibility field to these
  two chosen charts and the displayed valid pair, with exactly u, x and v.
  No new connection or tangent identification enters this comparison. -/
  -- The selected original charts contain the same base point.
  exact cov.compatible (chartAt (EuclideanSpace ℝ (Fin n)) x) c
    (chart_mem_atlas _ x) hc (Classical.choose (A.covers x)) i u x
    ⟨mem_chart_source _ x, Classical.choose_spec (A.covers x)⟩ hx v

end AtlasComplexConnection

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]

include hM hT hSC in
/-- A locally finite-rank smooth complex bundle admits a smooth complex connection. -/
theorem nonempty_atlasComplexConnection : Nonempty (AtlasComplexConnection A) := by
  /- Stage 1: use a locally finite smooth partition subordinate to the actual
  frame cover. On each frame take the ordinary trivial connection; weight the
  local covariant derivatives and sum on the original fibers. The weights sum
  to one, so the Leibniz term has its required coefficient one.
  Stage 2: in any original frame the derivative of the smooth transition
  matrix gives the usual connection matrix. Local finiteness makes its sum
  smooth on that frame. Since all expressions represent the same fiberwise
  derivative, their overlap condition holds on every original section.
  Stage 3: collect these forms on every manifold/frame pair. The tangent
  argument remains real linear and the fiber action complex linear. There
  is no common rank requirement: only overlapping frames interact, and their
  ranks already agree by the original fiber equivalences. -/
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let V (i : A.Index) := EuclideanSpace ℂ (Fin (A.rank i))
  let e (i : A.Index) := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
  -- Original transition columns give rectangular linear maps even on disjoint charts.
  let column (i j : A.Index) (x : M) (a : Fin (A.rank i)) : V j :=
    (e j).symm ((A.chart j ((A.chart i).toPartialEquiv.symm
      (x, Pi.single a 1))).2)
  let T (i j : A.Index) (x : M) : V i →L[ℂ] V j :=
    ∑ a, (EuclideanSpace.proj a).smulRight (column i j x a)
  have hpoint (i : A.Index) (x : M) (hx : x ∈ (A.chart i).baseSet)
      (v : Fin (A.rank i) → ℂ) :
      (⟨x, (A.frameLinearEquiv i x hx).symm v⟩ : TotalSpace Unit E) =
        (A.chart i).toPartialEquiv.symm (x, v) := by
    exact TotalSpace.mk_cast (F := Unit) (E := E) ((A.chart i).proj_symm_apply' hx) _
  have hT (i j : A.Index) (x : M) (hi : x ∈ (A.chart i).baseSet)
      (hj : x ∈ (A.chart j).baseSet) (v : V i) :
      T i j x v = (e j).symm
        (A.frameLinearEquiv j x hj ((A.frameLinearEquiv i x hi).symm (e i v))) := by
    let R : V i →ₗ[ℂ] V j :=
      (e j).symm.toLinearMap.comp ((A.frameLinearEquiv j x hj).toLinearMap.comp
        ((A.frameLinearEquiv i x hi).symm.toLinearMap.comp (e i).toLinearMap))
    have hcol (a : Fin (A.rank i)) :
        column i j x a = R ((e i).symm (Pi.single a 1)) := by
      change (e j).symm (A.chart j ((A.chart i).toPartialEquiv.symm
        (x, Pi.single a 1))).2 = (e j).symm
          (A.frameLinearEquiv j x hj ((A.frameLinearEquiv i x hi).symm
            ((e i) ((e i).symm (Pi.single a 1)))))
      rw [(e i).apply_symm_apply, ← hpoint i x hi]
      rfl
    have hsum : ∑ a, v a • (e i).symm (Pi.single a 1) = v := by
      apply (e i).injective
      ext a
      simp only [map_sum, map_smul, ContinuousLinearEquiv.apply_symm_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change (∑ b, v b * (Pi.single b (1 : ℂ) : Fin (A.rank i) → ℂ) a) = v a
      simp [Pi.single_apply]
    change (∑ a, (EuclideanSpace.proj a).smulRight (column i j x a)) v = R v
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, hcol]
    change ∑ a, v a • R ((e i).symm (Pi.single a 1)) = R v
    simpa only [map_sum, map_smul] using congrArg R hsum
  have hTsmooth (i j : A.Index) :
      ContMDiffOn I 𝓘(ℝ, V i →L[ℂ] V j) ∞ (T i j)
        ((A.chart i).baseSet ∩ (A.chart j).baseSet) := by
    apply contMDiffOn_finsetSum
    intro a _
    have hc := ((e j).symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
      |>.comp_contMDiffOn (A.contMDiffOn_coordChange i j a)
    exact ((ContinuousLinearMap.smulRightL ℂ (V i) (V j)
      (EuclideanSpace.proj a)).restrictScalars ℝ).contMDiff.comp_contMDiffOn hc
  -- A section is differentiated in a chosen original frame before returning to its fiber.
  let coord (i : A.Index) (u : A.smoothSections) (x : M) : V i :=
    (e i).symm (A.chart i ⟨x, u.val x⟩).2
  have hcoordsmooth (i : A.Index) (u : A.smoothSections) :
      ContMDiffOn I 𝓘(ℝ, V i) ∞ (coord i u) (A.chart i).baseSet :=
    ((e i).symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
      (u.property i)
  have hchartDerivative (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index)
      (u : A.smoothSections) (x : M) (hx : x ∈ c.source ∩ (A.chart i).baseSet)
      (v : TangentSpace I x) :
      fderiv ℝ (atlasSectionInChart A c i u.val) (c x) (mfderiv I I c x v) =
        mvfderiv I (coord i u) x v := by
    have hu := ((hcoordsmooth i u).contMDiffAt
      ((A.chart i).open_baseSet.mem_nhds hx.2)).mdifferentiableAt (by simp)
    have hchart := mdifferentiable_of_mem_atlas (I := I) hc
    have hc' := hchart.mdifferentiableAt_symm (c.map_source hx.1)
    have hchain := mvfderiv_comp (I := I) (I' := I) (c x)
      (by simpa only [c.left_inv hx.1] using hu) hc'
    have hlocal : fderiv ℝ (atlasSectionInChart A c i u.val) (c x) =
        (mvfderiv I (coord i u) x).comp (mfderiv I I c.symm (c x)) := by
      dsimp only [I] at hchain
      rw [mvfderiv_eq_fderiv, c.left_inv hx.1] at hchain
      exact hchain
    rw [hlocal]
    change (mvfderiv I (coord i u) x)
      (((mfderiv I I c.symm (c x)).comp (mfderiv I I c x)) v) = _
    rw [hchart.symm_comp_deriv hx.1]
    rfl
  let D (i : A.Index) (u : A.smoothSections) (x : M)
      (v : TangentSpace I x) : E x :=
    if hx : x ∈ (A.chart i).baseSet then
      (A.frameLinearEquiv i x hx).symm (e i (mvfderiv I (coord i u) x v)) else 0
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun i : A.Index ↦ (A.chart i).baseSet) (fun i ↦ (A.chart i).open_baseSet) (by
      intro x _
      exact Set.mem_iUnion.mpr (A.covers x))
  let localForm (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (i j : A.Index) (z : EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] (V i →L[ℂ] V i) :=
    ((ContinuousLinearMap.compL ℂ (V i) (V j) (V i)
      (T j i (c.symm z))).restrictScalars ℝ).comp
        (fderiv ℝ (fun w ↦ T i j (c.symm w)) z)
  let Γ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (i : A.Index) (z : EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] (V i →L[ℂ] V i) :=
    ∑ᶠ j, ρ j (c.symm z) • localForm c i j z
  have hlocalsmooth (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i j : A.Index)
      (z : EuclideanSpace ℝ (Fin n))
      (hz : z ∈ c.target ∩ c.symm ⁻¹' ((A.chart i).baseSet ∩ (A.chart j).baseSet)) :
      ContDiffAt ℝ ∞ (localForm c i j) z := by
    have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
      (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1
    have hij := ((hTsmooth i j).contMDiffAt
      (((A.chart i).open_baseSet.inter (A.chart j).open_baseSet).mem_nhds hz.2)).comp
        z hsymm
    have hji := ((hTsmooth j i).contMDiffAt
      (((A.chart j).open_baseSet.inter (A.chart i).open_baseSet).mem_nhds
        ⟨hz.2.2, hz.2.1⟩)).comp z hsymm
    have hd : ContDiffAt ℝ ∞
        (fderiv ℝ (fun w ↦ T i j (c.symm w))) z :=
      (contMDiffAt_iff_contDiffAt.mp hij).fderiv_right (by simp)
    have hp := ((ContinuousLinearMap.compL ℂ (V i) (V j) (V i)).restrictScalars
      ℝ).contDiff.contDiffAt.comp z (contMDiffAt_iff_contDiffAt.mp hji)
    have hr := (ContinuousLinearMap.restrictScalarsL ℂ (V i →L[ℂ] V j)
      (V i →L[ℂ] V i) ℝ ℝ).contDiff.contDiffAt.comp z hp
    exact hr.clm_comp hd
  have hΓsmooth (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) :
      ContDiffOn ℝ ∞ (Γ c i) (c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) := by
    intro z hz
    have hx : c.symm z ∈ c.source := c.map_target hz.1
    have hs : ContMDiffAt I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] (V i →L[ℂ] V i)) ∞
        (fun x : M ↦ ∑ᶠ j, ρ j x • localForm c i j (c x)) (c.symm z) := by
      apply ρ.contMDiffAt_finsum
      intro j hj
      have hlocal := hlocalsmooth c hc i j (c (c.symm z)) (by
        rw [c.right_inv hz.1]
        exact ⟨hz.1, hz.2, hρ j hj⟩)
      exact hlocal.contMDiffAt.comp (c.symm z)
        (contMDiffAt_of_mem_maximalAtlas (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) hx)
    have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
      (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1
    have hcomp := hs.comp z hsymm
    have heq : Γ c i =ᶠ[nhds z]
        (fun w ↦ ∑ᶠ j, ρ j (c.symm w) • localForm c i j (c (c.symm w))) := by
      filter_upwards [c.open_target.mem_nhds hz.1] with w hw
      dsimp only [Γ]
      rw [c.right_inv hw]
    exact ((contMDiffAt_iff_contDiffAt.mp hcomp).congr_of_eventuallyEq heq).contDiffWithinAt
  have hlocalFormula (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i j : A.Index)
      (u : A.smoothSections) (x : M) (hx : x ∈ c.source ∩ (A.chart i).baseSet)
      (hj : x ∈ (A.chart j).baseSet) (v : TangentSpace I x) :
      (e i).symm (A.frameLinearEquiv i x hx.2 (D j u x v)) =
        fderiv ℝ (atlasSectionInChart A c i u.val) (c x) (mfderiv I I c x v) +
          localForm c i j (c x) (mfderiv I I c x v)
            (atlasSectionInChart A c i u.val (c x)) := by
    let a := atlasSectionInChart A c i u.val
    let b (z : EuclideanSpace ℝ (Fin n)) := T i j (c.symm z)
    let w := mfderiv I I c x v
    have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
      (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) (c.map_source hx.1)
    have ha : DifferentiableAt ℝ a (c x) := by
      have hs := ((hcoordsmooth i u).contMDiffAt
        ((A.chart i).open_baseSet.mem_nhds hx.2)).comp_of_eq hsymm (c.left_inv hx.1)
      exact (contMDiffAt_iff_contDiffAt.mp hs).differentiableAt (by simp)
    have hb : DifferentiableAt ℝ b (c x) := by
      have hs := ((hTsmooth i j).contMDiffAt
        (((A.chart i).open_baseSet.inter (A.chart j).open_baseSet).mem_nhds
          ⟨hx.2, hj⟩)).comp_of_eq hsymm (c.left_inv hx.1)
      exact (contMDiffAt_iff_contDiffAt.mp hs).differentiableAt (by simp)
    -- The original section coordinates obey the actual transition identity near x.
    have hnear : atlasSectionInChart A c j u.val =ᶠ[nhds (c x)]
        (fun z ↦ b z (a z)) := by
      have hpre : c.symm ⁻¹' ((A.chart i).baseSet ∩ (A.chart j).baseSet) ∈ nhds (c x) :=
        hsymm.continuousAt.preimage_mem_nhds (by
          rw [c.left_inv hx.1]
          exact ((A.chart i).open_baseSet.inter (A.chart j).open_baseSet).mem_nhds
            ⟨hx.2, hj⟩)
      filter_upwards [hpre] with z hz
      dsimp only [a, b, atlasSectionInChart]
      rw [hT i j (c.symm z) hz.1 hz.2]
      rw [(e i).apply_symm_apply]
      change (e j).symm (A.frameLinearEquiv j (c.symm z) hz.2 (u.val (c.symm z))) =
        (e j).symm (A.frameLinearEquiv j (c.symm z) hz.2
          ((A.frameLinearEquiv i (c.symm z) hz.1).symm
            (A.frameLinearEquiv i (c.symm z) hz.1 (u.val (c.symm z)))))
      rw [LinearEquiv.symm_apply_apply]
    let R := ContinuousLinearMap.restrictScalarsL ℂ (V i) (V j) ℝ ℝ
    have hr : HasFDerivAt (fun z ↦ (b z).restrictScalars ℝ)
        (R.comp (fderiv ℝ b (c x))) (c x) :=
      R.hasFDerivAt.comp (c x) hb.hasFDerivAt
    have hproduct := (hr.clm_apply ha.hasFDerivAt).fderiv
    have hderivative : fderiv ℝ (atlasSectionInChart A c j u.val) (c x) w =
        T i j x (fderiv ℝ a (c x) w) + fderiv ℝ b (c x) w (a (c x)) := by
      have hd := congrArg (fun L ↦ L w) (hnear.fderiv_eq.trans hproduct)
      change fderiv ℝ (atlasSectionInChart A c j u.val) (c x) w =
        b (c x) (fderiv ℝ a (c x) w) + fderiv ℝ b (c x) w (a (c x)) at hd
      simpa only [b, c.left_inv hx.1] using hd
    have hleft : (e i).symm (A.frameLinearEquiv i x hx.2 (D j u x v)) =
        T j i x (fderiv ℝ (atlasSectionInChart A c j u.val) (c x) w) := by
      rw [hT j i x hj hx.2, hchartDerivative c hc j u x ⟨hx.1, hj⟩ v]
      dsimp only [D]
      rw [dite_eq_left hj]
    have hinverse (t : V i) : T j i x (T i j x t) = t := by
      rw [hT i j x hx.2 hj, hT j i x hj hx.2,
        (e j).apply_symm_apply, LinearEquiv.symm_apply_apply,
        LinearEquiv.apply_symm_apply, (e i).symm_apply_apply]
    rw [hleft, hderivative, map_add, hinverse]
    dsimp only [localForm, a, b, w]
    rw [c.left_inv hx.1]
    rfl
  -- Each displayed expression is the same locally finite sum in the original fiber.
  have hexpression (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index)
      (u : A.smoothSections) (x : M) (hx : x ∈ c.source ∩ (A.chart i).baseSet)
      (v : TangentSpace I x) :
      atlasConnectionExpression A c i (Γ c i) u x hx.2 v =
        ∑ j ∈ ρ.finsupport x, (ρ j x : ℂ) • D j u x v := by
    let C : E x ≃ₗ[ℂ] V i :=
      (A.frameLinearEquiv i x hx.2).trans (e i).symm.toLinearEquiv
    let w := mfderiv I I c x v
    let du := fderiv ℝ (atlasSectionInChart A c i u.val) (c x) w
    let ucoord := atlasSectionInChart A c i u.val (c x)
    have hsum : (∑ j ∈ ρ.finsupport x, (ρ j x : ℂ)) = 1 := by
      simpa only [Complex.ofReal_sum, Complex.ofReal_one] using
        congrArg Complex.ofReal (ρ.sum_finsupport x (Set.mem_univ x))
    have hΓsum : Γ c i (c x) =
        ∑ j ∈ ρ.finsupport x, ρ j x • localForm c i j (c x) := by
      dsimp only [Γ]
      rw [c.left_inv hx.1]
      exact (ρ.sum_finsupport_smul_eq_finsum x (fun j _ ↦ localForm c i j (c x))).symm
    have heval : C (atlasConnectionExpression A c i (Γ c i) u x hx.2 v) =
        du + ∑ j ∈ ρ.finsupport x, (ρ j x : ℂ) • localForm c i j (c x) w ucoord := by
      change (e i).symm ((A.frameLinearEquiv i x hx.2)
        ((A.frameLinearEquiv i x hx.2).symm (e i (du + Γ c i (c x) w ucoord)))) = _
      rw [LinearEquiv.apply_symm_apply, (e i).symm_apply_apply, hΓsum]
      let ev : (EuclideanSpace ℝ (Fin n) →L[ℝ] (V i →L[ℂ] V i)) →ₗ[ℝ] V i := {
        toFun := fun L ↦ L w ucoord
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      simp only [Complex.coe_smul]
      change du + ev (∑ j ∈ ρ.finsupport x, ρ j x • localForm c i j (c x)) =
        du + ∑ j ∈ ρ.finsupport x, ρ j x • ev (localForm c i j (c x))
      rw [map_sum]
      simp only [map_smul]
    apply C.injective
    rw [heval]
    calc
      du + ∑ j ∈ ρ.finsupport x, (ρ j x : ℂ) • localForm c i j (c x) w ucoord =
          ∑ j ∈ ρ.finsupport x,
            (ρ j x : ℂ) • (du + localForm c i j (c x) w ucoord) := by
        simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul]
      _ = C (∑ j ∈ ρ.finsupport x, (ρ j x : ℂ) • D j u x v) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_smul]
        congr 1
        exact (hlocalFormula c hc i j u x hx
          (hρ j (subset_closure ((ρ.mem_finsupport x).mp hj))) v).symm
  refine ⟨{ connectionForm := Γ, smooth_connectionForm := hΓsmooth, compatible := ?_ }⟩
  intro c d hc hd i j u x hx hy v
  exact (hexpression c hc i u x hx v).trans (hexpression d hd j u x hy v).symm

end AtiyahSinger
