/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalDifferentialOperator
public import AtiyahSinger.Geometry.SmoothBundleMaps
public import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Smooth bundle maps are exactly zero-order differential operators

Public module ID: M1056.

D03/E01/UL03: SG III.13.4, p.248, identifies the exterior bundle map with a
zero-order differential operator. The statements here connect that assertion
with the actual existing section map and coordinate-operator definition.
Uniqueness of the fiber map uses globally extendible local test sections; it
is not inferred just from equality on an unspecified section space.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM

/-- The actual action of a smooth bundle map is a differential operator of order zero. -/
theorem isDifferentialOperator_smoothSectionMap (a : ∀ x, E x →ₗ[ℂ] F x)
    (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a) :
    IsDifferentialOperator (n := n) (r := r) (q := q) E F 0 (smoothSectionMap a ha) := by
  /- In each valid manifold chart and pair of bundle frames the only coefficient
  is the matrix of a and the only multiindex is zero. Its columns are smooth by
  ha, and its multiplication on section coordinates is the original fiber action.
  Restrict to the chart overlap to obtain the required local coordinate expression.
  No support, compactness, density, or ellipticity condition is used. -/
  classical
  intro c hc e he f hf x hx
  let H := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let W := EuclideanSpace ℂ (Fin q)
  let L (y : M) : V →L[ℂ] W :=
    ((f.linearMapAt ℂ y).comp ((a y).comp (e.symmL ℂ y).toLinearMap)).toContinuousLinearMap
  -- Assemble the actual coordinate map from the prescribed smooth matrix columns.
  have hL : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, V →L[ℂ] W) ∞ L
      (e.baseSet ∩ f.baseSet) := by
    have hsum : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, V →L[ℂ] W) ∞
        (fun y ↦ ∑ j : Fin r,
          ContinuousLinearMap.smulRightL ℂ V W (EuclideanSpace.proj j)
            ((f ⟨y, a y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2))
        (e.baseSet ∩ f.baseSet) := by
      apply contMDiffOn_finsetSum
      intro j _
      exact ((ContinuousLinearMap.smulRightL ℂ V W
        (EuclideanSpace.proj j)).restrictScalars ℝ).contMDiff.comp_contMDiffOn (ha e f j)
    apply hsum.congr
    intro y hy
    apply ContinuousLinearMap.ext
    intro v
    simp only [sum_apply]
    change L y v = ∑ j : Fin r, v j •
      (f ⟨y, a y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2
    have hexpand := congrArg (L y) ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr v)
    simpa [L, map_sum, map_smul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, f.coe_linearMapAt_of_mem hy.2] using hexpand.symm
  let U := c.source ∩ e.baseSet ∩ f.baseSet
  have hU : IsOpen U := (c.open_source.inter e.open_baseSet).inter f.open_baseSet
  have hsymm := contMDiffOn_symm_of_mem_maximalAtlas
    (I := 𝓘(ℝ, H)) (n := ∞) (IsManifold.subset_maximalAtlas hc)
  have hcoeff : ContDiffOn ℝ ∞ (fun z ↦ L (c.symm z)) (c '' U) := by
    apply ContMDiffOn.contDiffOn
    apply hL.comp (hsymm.mono ?_) ?_
    · rintro z ⟨y, hy, rfl⟩
      exact c.map_source hy.1.1
    · rintro z ⟨y, hy, rfl⟩
      change c.symm (c y) ∈ e.baseSet ∩ f.baseSet
      rw [c.left_inv hy.1.1]
      exact ⟨hy.1.2, hy.2⟩
  let Q : CoordinateDifferentialOperator n r q 0 (c '' U) :=
    { coefficient := fun _ _ z ↦ L (c.symm z)
      smooth_coefficient := fun _ _ ↦ hcoeff }
  -- Order zero has one coefficient and no derivative of the input section.
  refine ⟨U, hU, hx, Q, Set.Subset.rfl, ?_⟩
  intro s y hy
  have hcy : c.symm (c y) = y := c.left_inv hy.1.1
  have hsection : sectionInChart E c e s.val (c y) = (e ⟨y, s.val y⟩).2 := by
    unfold sectionInChart
    rw [hcy]
  change (f ⟨y, a y (s.val y)⟩).2 = Q.apply (sectionInChart E c e s.val) (c y)
  have happly : Q.apply (sectionInChart E c e s.val) (c y) =
      L (c.symm (c y)) (sectionInChart E c e s.val (c y)) := by
    simp [CoordinateDifferentialOperator.apply, Q]
  rw [happly, hcy, hsection]
  change (f ⟨y, a y (s.val y)⟩).2 =
    f.linearMapAt ℂ y (a y (e.symmL ℂ y (e ⟨y, s.val y⟩).2))
  rw [e.symmL_apply hy.1.2, e.symm_apply_apply_mk hy.1.2,
    f.coe_linearMapAt_of_mem hy.2]

variable [hT : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hT hSC hE hF

-- Retain the original second-countability and target-bundle hypotheses.
set_option linter.unusedSectionVars false in
/-- Every zero-order differential operator comes from one uniquely determined smooth fiber map. -/
theorem existsUnique_smoothBundleMap_of_order_zero
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F 0) :
    ∃! a : ∀ x, E x →ₗ[ℂ] F x,
      ∃ ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a,
        P.toLinearMap = smoothSectionMap a ha := by
  /- Stage 1: an order-zero coordinate expression contains only its zeroth
  coefficient. At each point it defines a linear fiber action giving the
  original operator on every smooth section. A smooth bump inside one
  original bundle frame realizes each fiber vector by a global smooth section.
  Stage 2: these test sections identify every local coefficient with that
  same fiber action. Its matrix columns are therefore smooth in every pair
  of frames, and the original section action is exactly smoothSectionMap.
  Stage 3: the same test sections separate any two proposed fiber maps,
  proving uniqueness on every fiber, also on a noncompact or empty base. -/
  classical
  let H := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let W := EuclideanSpace ℂ (Fin q)
  let emptyIndex : Fin 0 → Fin n := Fin.elim0
  have hzero {U : Set H} (Q : CoordinateDifferentialOperator n r q 0 U)
      (u : H → V) (z : H) :
      Q.apply u z = Q.coefficient 0 emptyIndex z (u z) := by
    simp [CoordinateDifferentialOperator.apply, emptyIndex]
    congr 2
  -- Each local zeroth coefficient already gives the full pointwise action of P.
  have hpoint (x : M) : ∃ b : E x →ₗ[ℂ] F x,
      ∀ s : smoothSections (n := n) (r := r) E, (P.toLinearMap s).val x = b (s.val x) := by
    let c := chartAt H x
    let e := trivializationAt V E x
    let f := trivializationAt W F x
    have hxE : x ∈ e.baseSet := mem_baseSet_trivializationAt _ E x
    have hxF : x ∈ f.baseSet := mem_baseSet_trivializationAt _ F x
    have hxC : x ∈ c.source := mem_chart_source H x
    obtain ⟨U, _, hxU, Q, hQ⟩ := P.isDifferentialOperator c (chart_mem_atlas H x)
      e f x ⟨⟨hxC, hxE⟩, hxF⟩
    let b : E x →ₗ[ℂ] F x := (f.symmL ℂ x).toLinearMap.comp
      ((Q.coefficient 0 emptyIndex (c x)).toLinearMap.comp (e.linearMapAt ℂ x))
    refine ⟨b, ?_⟩
    intro s
    have hactual := congrArg (f.symmL ℂ x) (hQ.2 s x hxU)
    rw [hzero] at hactual
    have hsection : sectionInChart E c e s.val (c x) = (e ⟨x, s.val x⟩).2 := by
      unfold sectionInChart
      rw [c.left_inv hxC]
    rw [hsection, f.symmL_apply hxF, f.symm_apply_apply_mk hxF] at hactual
    simpa only [b, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      e.coe_linearMapAt_of_mem hxE, f.symmL_apply hxF] using hactual
  choose a hact using hpoint
  -- A bump supported inside one original frame realizes every original fiber vector.
  have heval (x : M) (v : E x) :
      ∃ s : smoothSections (n := n) (r := r) E, s.val x = v := by
    let e := trivializationAt V E x
    have hxE : x ∈ e.baseSet := mem_baseSet_trivializationAt _ E x
    obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport
      (I := 𝓘(ℝ, H)) x).mem_iff.mp (e.open_baseSet.mem_nhds hxE)
    let w : V := (e ⟨x, v⟩).2
    let s (y : M) : E y := (χ y : ℂ) • e.symmL ℂ y w
    have hs : IsSmoothSection (n := n) (r := r) E s := by
      intro f hf y hy
      let := hf
      by_cases hye : y ∈ e.baseSet
      · -- In the supporting frame, the transition matrix and cutoff are both smooth.
        have htransition := IsSmoothComplexBundle.contMDiffOn_coordChange
          (n := n) (E := E) e f
        have hcolumn := ((ContinuousLinearMap.apply ℂ V w).restrictScalars
          ℝ).contMDiff.comp_contMDiffOn htransition
        have hscalar : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, ℂ) ∞ (fun z ↦ (χ z : ℂ)) :=
          Complex.ofRealCLM.contMDiff.comp χ.contMDiff
        have hmul : ContDiff ℝ ∞ (fun t : ℂ × V ↦ t.1 • t.2) := contDiff_smul
        have hlocal := hmul.contMDiff.comp_contMDiffOn
          (hscalar.contMDiffOn.prodMk_space hcolumn)
        have hsmooth : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, V) ∞
            (fun z ↦ (f ⟨z, s z⟩).2) (e.baseSet ∩ f.baseSet) := by
          apply hlocal.congr
          intro z hz
          change (f ⟨z, (χ z : ℂ) • e.symmL ℂ z w⟩).2 =
            (χ z : ℂ) • (e.coordChangeL ℂ f z) w
          calc
            _ = (χ z : ℂ) • (f ⟨z, e.symmL ℂ z w⟩).2 :=
              (f.linearEquivAt ℂ z hz.2).map_smul (χ z : ℂ) _
            _ = _ := by rw [e.symmL_apply hz.1, e.coordChangeL_apply f hz]
        exact (hsmooth.contMDiffAt
          ((e.open_baseSet.inter f.open_baseSet).mem_nhds ⟨hye, hy⟩)).contMDiffWithinAt
      · -- Off the supporting frame, the section is zero on an ambient neighborhood.
        have hyχ : y ∉ tsupport χ := fun h ↦ hye (hχ h)
        apply ContMDiffAt.contMDiffWithinAt
        apply (contMDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport (χ : M → ℝ)).isOpen_compl.mem_nhds hyχ,
          f.open_baseSet.mem_nhds hy] with z hz hfz
        change (f ⟨z, (χ z : ℂ) • e.symmL ℂ z w⟩).2 = 0
        rw [image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero, zero_smul]
        exact (f.linearEquivAt ℂ z hfz).map_zero
    refine ⟨⟨s, hs⟩, ?_⟩
    change (χ x : ℂ) • e.symmL ℂ x w = v
    rw [χ.eq_one, Complex.ofReal_one, one_smul, e.symmL_apply hxE]
    exact e.symm_apply_apply_mk hxE v
  -- Surjectivity of evaluation makes every local coefficient agree with this same a.
  have hmatrix (c : OpenPartialHomeomorph M H)
      (e : Trivialization V (π V E)) [MemTrivializationAtlas e]
      (f : Trivialization W (π W F)) [MemTrivializationAtlas f]
      (U : Set M) (Q : CoordinateDifferentialOperator n r q 0 (c '' U))
      (hQ : HasCoordinateExpression E F 0 P.toLinearMap c e f U Q)
      (y : M) (hy : y ∈ U) (v : E y) :
      (f ⟨y, a y v⟩).2 = Q.coefficient 0 emptyIndex (c y) (e ⟨y, v⟩).2 := by
    obtain ⟨s, hs⟩ := heval y v
    have hactual := hQ.2 s y hy
    rw [hzero, hact y s] at hactual
    have hsection : sectionInChart E c e s.val (c y) = (e ⟨y, v⟩).2 := by
      unfold sectionInChart
      rw [c.left_inv (hQ.1 hy).1.1, hs]
    rw [hsection, hs] at hactual
    exact hactual
  have ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a := by
    intro e he f hf j x hx
    let c := chartAt H x
    have hxC : x ∈ c.source := mem_chart_source H x
    obtain ⟨U, hU, hxU, Q, hQ⟩ := P.isDifferentialOperator c (chart_mem_atlas H x)
      e f x ⟨⟨hxC, hx.1⟩, hx.2⟩
    -- The chosen coefficient is smooth on its original coordinate domain.
    have hcoefficient : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, W) ∞
        (fun z ↦ Q.coefficient 0 emptyIndex z (EuclideanSpace.single j 1)) (c '' U) :=
      (((ContinuousLinearMap.apply ℂ W (EuclideanSpace.single j 1)).restrictScalars
        ℝ).contDiff.comp_contDiffOn (Q.smooth_coefficient 0 emptyIndex)).contMDiffOn
    have hchart := contMDiffOn_of_mem_maximalAtlas
      (I := 𝓘(ℝ, H)) (n := ∞) (IsManifold.subset_maximalAtlas (chart_mem_atlas H x))
    have hcompose := hcoefficient.comp
      (hchart.mono (fun y hy ↦ (hQ.1 hy).1.1)) (fun y hy ↦ ⟨y, hy, rfl⟩)
    have hlocal : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, W) ∞
        (fun y ↦ (f ⟨y, a y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2) U := by
      apply hcompose.congr
      intro y hy
      have h := hmatrix c e f U Q hQ y hy (e.symmL ℂ y (EuclideanSpace.single j 1))
      rw [e.symmL_apply (hQ.1 hy).1.2, e.apply_mk_symm (hQ.1 hy).1.2] at h
      simpa only [e.symmL_apply (hQ.1 hy).1.2, Function.comp_apply] using h
    exact (hlocal.contMDiffAt (hU.mem_nhds hxU)).contMDiffWithinAt
  refine ⟨a, ⟨ha, ?_⟩, ?_⟩
  · -- This identifies the original section action, including all fiber values.
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext x
    exact hact x s
  · -- The same test sections separate two proposed fiberwise maps at every point.
    intro b hb
    obtain ⟨hb, hPb⟩ := hb
    funext x
    apply LinearMap.ext
    intro v
    obtain ⟨s, hs⟩ := heval x v
    have h := congrArg
      (fun L : smoothSections (n := n) (r := r) E →ₗ[ℂ]
        smoothSections (n := n) (r := q) F ↦ (L s).val x) hPb
    change (P.toLinearMap s).val x = b x (s.val x) at h
    rw [hact x s, hs] at h
    exact h.symm

end AtiyahSinger
