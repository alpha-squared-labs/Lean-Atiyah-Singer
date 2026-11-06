/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedHodgeOperator

/-!
# Native finite bundles for graded differential forms

Public module ID: M1260.

On a Hausdorff smooth manifold, finite families of the original alternating
covariant tensors have one native smooth bundle model.
Its coordinate changes, smooth sections and orthogonal
metric are transported together. Taking the even and odd degrees up to the
actual tangent dimension gives the bundles required by the graded Hodge operator.
No new form carrier or unrelated grading replaces the original total forms.

Source: Lawson--Michelsohn, Spin Geometry, II.5 and III.5. The finite native
coordinate presentation is a project implementation of the ordinary direct sum.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold MeasureTheory Module Set
open scoped BigOperators DirectSum Manifold ContDiff ComplexConjugate Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  (g : SmoothTangentMetric (n := n) (M := M))

set_option maxHeartbeats 3600000 in
-- Keep the actual finite family, inverse tangent coordinates and metric in one construction.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- A finite family of actual differential forms admits a common native smooth bundle model. -/
theorem exists_finiteDifferentialForm_bundleModel {ι : Type} [Fintype ι] (degree : ι → ℕ) :
  ∃ (R : ℕ) (Z : VectorBundleCore ℂ M (EuclideanSpace ℂ (Fin R))
      (atlas (EuclideanSpace ℝ (Fin n)) M))
    (e : ((j : ι) → EuclideanSpace ℝ (Fin n) [⋀^Fin (degree j)]→L[ℝ] ℂ) ≃L[ℂ]
      EuclideanSpace ℂ (Fin R)),
    letI : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin R)))
    letI : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin R)))
    IsSmoothComplexBundle (n := n) (r := R) Z.Fiber ∧
    (∀ i, Z.baseSet i = i.val.source) ∧
    (∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (x : M) (_ : x ∈ c.source)
      (a : (j : ι) → DifferentialFormFiber (n := n) (degree j) x),
      (Z.localTriv ⟨c, hc⟩ ⟨x, e a⟩).2 = e (fun j ↦ (a j).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm (c x)))) ∧
    ∃ Φ : ((j : ι) → SmoothDifferentialForm (n := n) M (degree j)) ≃ₗ[ℂ]
        smoothSections (n := n) (r := R) Z.Fiber,
      (∀ u x, (Φ u).val x = e (fun j ↦ (u j).val x)) ∧
    ∃ metric : SmoothHermitianMetric (n := n) (r := R) Z.Fiber,
      ∀ x a b, metric.pairing x a b =
        ∑ j, differentialFormInner g (degree j) x (e.symm a j) (e.symm b j) := by
  classical
  have hfinite (p : ℕ) : FiniteDimensional ℂ
      (EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ) := by
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let L : (EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ) →ₗ[ℂ]
        ((Fin p → Fin n) → ℂ) :=
      { toFun := fun a i ↦ a (fun k ↦ b (i k))
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    refine FiniteDimensional.of_injective L ?_
    intro a c h
    have heq : a.toAlternatingMap = c.toAlternatingMap := by
      apply b.ext_alternating
      intro i hi
      exact congrFun h i
    ext v
    exact congrArg (fun f : EuclideanSpace ℝ (Fin n) [⋀^Fin p]→ₗ[ℝ] ℂ ↦ f v) heq
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let I₀ := 𝓘(ℝ, V)
  let W := (j : ι) → V [⋀^Fin (degree j)]→L[ℝ] ℂ
  let : ∀ j : ι, FiniteDimensional ℂ (V [⋀^Fin (degree j)]→L[ℝ] ℂ) :=
    fun j ↦ hfinite (degree j)
  let : FiniteDimensional ℂ W := inferInstance
  let R := Module.finrank ℂ W
  let e : W ≃L[ℂ] EuclideanSpace ℂ (Fin R) :=
    (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin R) ℂ).symm
  let T := tangentBundleCore I₀ M
  let C (L : V →L[ℝ] V) : (EuclideanSpace ℂ (Fin R)) →L[ℂ]
      EuclideanSpace ℂ (Fin R) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun a ↦ e (fun j ↦ (e.symm a j).compContinuousLinearMap L)
        map_add' := by
          intro a b
          rw [e.symm.map_add, ← e.map_add]
          apply congrArg e
          funext j
          ext v
          rfl
        map_smul' := by
          intro c a
          rw [e.symm.map_smul, RingHom.id_apply, ← e.map_smul]
          apply congrArg e
          funext j
          ext v
          rfl }
  have hCsmooth : ContDiff ℝ ∞ C := by
    -- Each finite coordinate is polynomial in the same inverse tangent map.
    let e₀ := EuclideanSpace.equiv (Fin R) ℂ
    let cols := (e₀.arrowCongr (ContinuousLinearEquiv.refl ℂ
      (EuclideanSpace ℂ (Fin R)))).trans (ContinuousLinearEquiv.piRing (Fin R))
    have hc : ContDiff ℝ ∞ (fun L ↦ cols (C L)) := by
      apply contDiff_pi.mpr
      intro i
      apply (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
      apply contDiff_pi.mpr
      intro j
      have hB : ContDiff ℝ ∞
          (ContinuousAlternatingMap.compContinuousLinearMapCLM :
            (V →L[ℝ] V) → (V [⋀^Fin (degree j)]→L[ℝ] ℂ) →L[ℝ]
              (V [⋀^Fin (degree j)]→L[ℝ] ℂ)) :=
        contDiff_iff_contDiffAt.mpr fun L ↦
          (ContinuousAlternatingMap.analyticAt_compContinuousLinearMapCLM L).contDiffAt
      exact hB.clm_apply contDiff_const
    convert (cols.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hc using 1
    funext L
    exact (cols.symm_apply_apply (C L)).symm
  let Z : VectorBundleCore ℂ M (EuclideanSpace ℂ (Fin R)) (atlas V M) :=
    { baseSet := T.baseSet
      isOpen_baseSet := T.isOpen_baseSet
      indexAt := T.indexAt
      mem_baseSet_at := T.mem_baseSet_at
      coordChange := fun i j x ↦ C (T.coordChange j i x)
      coordChange_self := by
        intro i x hx a
        change e (fun j ↦ (e.symm a j).compContinuousLinearMap (T.coordChange i i x)) = a
        have ht : T.coordChange i i x = ContinuousLinearMap.id ℝ V := by
          apply ContinuousLinearMap.ext
          intro v
          exact T.coordChange_self i x hx v
        rw [ht]
        have hid : (fun j ↦ (e.symm a j).compContinuousLinearMap
            (ContinuousLinearMap.id ℝ V)) = e.symm a := by
          funext j
          ext v
          rfl
        rw [hid, e.apply_symm_apply]
      continuousOn_coordChange := by
        intro i j
        exact hCsmooth.continuous.comp_continuousOn
          ((T.continuousOn_coordChange j i).mono (by
            intro x hx
            exact ⟨hx.2, hx.1⟩))
      coordChange_comp := by
        intro i j k x hx a
        change e (fun l ↦ ((e.symm (e (fun t ↦ (e.symm a t).compContinuousLinearMap
          (T.coordChange j i x)))) l).compContinuousLinearMap (T.coordChange k j x)) =
            e (fun l ↦ (e.symm a l).compContinuousLinearMap (T.coordChange k i x))
        rw [e.symm_apply_apply]
        apply congrArg e
        funext l
        ext v
        apply congrArg (e.symm a l)
        funext t
        exact T.coordChange_comp k j i x ⟨⟨hx.2, hx.1.2⟩, hx.1.1⟩ (v t) }
  let : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin R)))
  let : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦
    inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin R)))
  let : IsManifold I₀ (∞ + 1) M := by simpa using
    (inferInstance : IsManifold I₀ ∞ M)
  let : T.IsContMDiff I₀ ∞ := tangentBundleCore.isContMDiff (I := I₀) (M := M)
  let : IsSmoothComplexBundle (n := n) (r := R) Z.Fiber := by
    constructor
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    have hT := (T.contMDiffOn_coordChange I₀ j i (n := ∞))
    have hswap : T.baseSet i ∩ T.baseSet j ⊆ T.baseSet j ∩ T.baseSet i := by
      intro x hx
      exact ⟨hx.2, hx.1⟩
    have hcomp := hCsmooth.contMDiff.comp_contMDiffOn (hT.mono hswap)
    apply hcomp.congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro a
    exact Z.localTriv_coordChange_eq i j hx a
  have hderiv (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M)
      (x : M) (hx : x ∈ c.source) :
      T.coordChange ⟨c, hc⟩ (T.indexAt x) x = mfderiv I₀ I₀ c.symm (c x) := by
    have hd := (mdifferentiable_of_mem_atlas (I := I₀) hc).mdifferentiableAt_symm
      (c.map_source hx)
    simp only [mfderiv, ite_eq_left hd]
    suffices h : fderiv ℝ (chartAt V x ∘ c.symm) (c x) =
        (tangentSpaceCastModel I₀ (c.symm (c x))).symm.toContinuousLinearMap.comp
          ((fderiv ℝ (chartAt V x ∘ c.symm) (c x)).comp
            (tangentSpaceCastModel I₀ (c x)).toContinuousLinearMap) by
      simpa [T, I₀, tangentBundleCore_coordChange, tangentBundleCore_indexAt,
        writtenInExtChartAt, extChartAt, c.left_inv hx, mfld_simps] using h
    apply ContinuousLinearMap.ext
    intro v
    rfl
  -- The same finite family of actual tensors supplies every chart coordinate.
  have hchart (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M)
      (x : M) (hx : x ∈ c.source) (a : W) :
      (Z.localTriv ⟨c, hc⟩ ⟨x, e a⟩).2 =
        e (fun j ↦ (a j).compContinuousLinearMap (mfderiv I₀ I₀ c.symm (c x))) := by
    change e (fun j ↦ (e.symm (e a) j).compContinuousLinearMap
      (T.coordChange ⟨c, hc⟩ (T.indexAt x) x)) = _
    rw [e.symm_apply_apply, hderiv c hc x hx]
  have hsmooth (u : M → W) :
      (∀ j, IsSmoothDifferentialForm (fun x ↦ u x j)) ↔
        IsSmoothSection (n := n) (r := R) Z.Fiber (fun x ↦ e (u x)) := by
    constructor
    · intro hu
      rintro _ ⟨c, rfl⟩
      have hc := contMDiffOn_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I₀) (n := ∞) c.property)
      have hu' : ContDiffOn ℝ ∞
          (fun y j ↦ differentialFormInChart (fun x ↦ u x j) c.val y) c.val.target :=
        contDiffOn_pi.mpr fun j ↦ hu j c.val c.property
      have he := (e.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
        (hu'.contMDiffOn.comp hc (fun x hx ↦ c.val.map_source hx))
      apply he.congr
      intro x hx
      change (Z.localTriv c ⟨x, e (u x)⟩).2 =
        e (fun j ↦ differentialFormInChart (fun y ↦ u y j) c.val (c.val x))
      rw [hchart c.val c.property x hx]
      apply congrArg e
      funext j
      unfold differentialFormInChart
      rw [c.val.left_inv hx]
    · intro hu j c hc
      have hc' := contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I₀) (n := ∞) hc)
      have hlocal := hu (Z.localTriv ⟨c, hc⟩) ⟨⟨c, hc⟩, rfl⟩
      have he := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
        (hlocal.comp hc' (fun y hy ↦ c.map_target hy))
      have hej := (contDiffOn_pi.mp he.contDiffOn) j
      apply hej.congr
      intro y hy
      change differentialFormInChart (fun x ↦ u x j) c y =
        e.symm ((Z.localTriv ⟨c, hc⟩ ⟨c.symm y, e (u (c.symm y))⟩).2) j
      rw [hchart c hc (c.symm y) (c.map_target hy), e.symm_apply_apply]
      unfold differentialFormInChart
      rw [c.right_inv hy]
  let Φ : ((j : ι) → SmoothDifferentialForm (n := n) M (degree j)) ≃ₗ[ℂ]
      smoothSections (n := n) (r := R) Z.Fiber :=
    { toFun := fun u ↦ ⟨fun x ↦ e (fun j ↦ (u j).val x),
        (hsmooth _).mp (fun j ↦ (u j).property)⟩
      invFun := fun s j ↦ ⟨fun x ↦ e.symm (s.val x) j, ((hsmooth _).mpr (by
        simpa only [e.apply_symm_apply] using
          (show IsSmoothSection (n := n) (r := R) Z.Fiber s.val from s.property))) j⟩
      left_inv := by
        intro u
        funext j
        apply Subtype.ext
        funext x
        exact congrFun (e.symm_apply_apply (fun k ↦ (u k).val x)) j
      right_inv := by
        intro s
        apply Subtype.ext
        funext x
        exact e.apply_symm_apply (s.val x)
      map_add' := by
        intro u v
        apply Subtype.ext
        funext x
        exact e.map_add (fun j ↦ (u j).val x) (fun j ↦ (v j).val x)
      map_smul' := by
        intro a u
        apply Subtype.ext
        funext x
        exact e.map_smul a (fun j ↦ (u j).val x) }
  -- Local smooth sections recover constant vectors in each chosen frame near a point.
  have hloc (f : Trivialization (EuclideanSpace ℂ (Fin R))
      (π (EuclideanSpace ℂ (Fin R)) Z.Fiber)) [MemTrivializationAtlas f]
      (x : M) (hx : x ∈ f.baseSet) (a : EuclideanSpace ℂ (Fin R)) :
      ∃ s : smoothSections (n := n) (r := R) Z.Fiber,
        ∀ᶠ y in 𝓝 x, s.val y = f.symmL ℂ y a := by
    obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I₀) x).mem_iff.mp
      (f.open_baseSet.mem_nhds hx)
    let s : ∀ y, Z.Fiber y := fun y ↦ (b y : ℂ) • f.symmL ℂ y a
    have hs : IsSmoothSection (n := n) (r := R) Z.Fiber s := by
      intro q hq y hy
      let := hq
      by_cases hyb : y ∈ tsupport b
      · have hyf : y ∈ f.baseSet := hb hyb
        have ht := (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) f q).contMDiffAt
          ((f.open_baseSet.inter q.open_baseSet).mem_nhds ⟨hyf, hy⟩)
        have ha : ContDiff ℝ ∞
            (fun L : EuclideanSpace ℂ (Fin R) →L[ℂ] EuclideanSpace ℂ (Fin R) ↦ L a) :=
          (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
        have hscalar := Complex.ofRealCLM.contMDiff.comp b.contMDiff
        have hmul : ContDiff ℝ ∞
            (fun z : ℂ × EuclideanSpace ℂ (Fin R) ↦ z.1 • z.2) := contDiff_smul
        have hlocal := hmul.comp_contMDiffAt
          (hscalar.contMDiffAt.prodMk_space (ha.comp_contMDiffAt ht))
        apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [f.open_baseSet.mem_nhds hyf, q.open_baseSet.mem_nhds hy]
          with z hzf hzq
        change (q.linearEquivAt ℂ z hzq) ((b z : ℂ) • f.symmL ℂ z a) =
          (b z : ℂ) • f.coordChangeL ℂ q z a
        rw [map_smul, f.coordChangeL_apply q ⟨hzf, hzq⟩, f.symmL_apply hzf]
        rfl
      · apply (contMDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin R)))
          |>.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hyb,
          q.open_baseSet.mem_nhds hy] with z hzb hzq
        change (q.linearEquivAt ℂ z hzq) ((b z : ℂ) • f.symmL ℂ z a) = 0
        rw [image_eq_zero_of_notMem_tsupport hzb, Complex.ofReal_zero, zero_smul, map_zero]
    refine ⟨⟨s, hs⟩, ?_⟩
    filter_upwards [b.eventuallyEq_one] with y hy
    change (b y : ℂ) • f.symmL ℂ y a = f.symmL ℂ y a
    change b y = (1 : ℝ) at hy
    rw [hy, Complex.ofReal_one, one_smul]
  -- The orthogonal sum metric keeps each original normalized form pairing.
  let core (x : M) : InnerProductSpace.Core ℂ (Z.Fiber x) :=
    { inner := fun a b ↦ ∑ j, differentialFormInner g (degree j) x
        (e.symm a j) (e.symm b j)
      conj_inner_symm := by
        intro a b
        rw [map_sum]
        exact Finset.sum_congr rfl (fun j _ ↦
          (differentialFormInnerCore g (degree j) x).conj_inner_symm _ _)
      re_inner_nonneg := by
        intro a
        rw [map_sum]
        exact Finset.sum_nonneg (fun j _ ↦
          (differentialFormInnerCore g (degree j) x).re_inner_nonneg _)
      add_left := by
        intro a b c
        rw [e.symm.map_add, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ ↦
          (differentialFormInnerCore g (degree j) x).add_left _ _ _)
      smul_left := by
        intro a b c
        rw [e.symm.map_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ ↦
          (differentialFormInnerCore g (degree j) x).smul_left _ _ _)
      definite := by
        intro a ha
        apply e.symm.injective
        rw [e.symm.map_zero]
        have hs := congrArg Complex.re ha
        simp only [Complex.re_sum, Complex.zero_re] at hs
        have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) ↦
          (differentialFormInnerCore g (degree j) x).re_inner_nonneg (e.symm a j))).mp hs
        funext j
        apply (differentialFormInnerCore g (degree j) x).definite
        apply Complex.ext
        · exact hz j (Finset.mem_univ j)
        · have hi := congrArg Complex.im
            ((differentialFormInnerCore g (degree j) x).conj_inner_symm
              (e.symm a j) (e.symm a j))
          change -_ = _ at hi
          change _ = 0
          linarith }
  let metric : SmoothHermitianMetric (n := n) (r := R) Z.Fiber :=
    { toCore := core
      isSmoothBundle := inferInstance
      contMDiffOn_gram := by
        intro f hf i j x hx
        let := hf
        obtain ⟨u, hu⟩ := hloc f x hx (EuclideanSpace.single i 1)
        obtain ⟨v, hv⟩ := hloc f x hx (EuclideanSpace.single j 1)
        have hpair : ContMDiff I₀ 𝓘(ℝ, ℂ) ∞ (fun y ↦
            ∑ k, differentialFormInner g (degree k) y
              ((Φ.symm u k).val y) ((Φ.symm v k).val y)) :=
          contMDiff_finsetSum fun k _ ↦
            contMDiff_differentialFormInner g (degree k) (Φ.symm u k) (Φ.symm v k)
        apply (hpair.contMDiffAt.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [hu, hv] with y hyu hyv
        change (∑ k, differentialFormInner g (degree k) y
          (e.symm (f.symmL ℂ y _) k) (e.symm (f.symmL ℂ y _) k)) =
          ∑ k, differentialFormInner g (degree k) y (e.symm (u.val y) k) (e.symm (v.val y) k)
        rw [hyu, hyv] }
  exact ⟨R, Z, e, inferInstance, (fun _ ↦ rfl), hchart, Φ, (fun _ _ ↦ rfl),
    metric, fun _ _ _ ↦ rfl⟩

omit [T2Space M] in
/-- The original infinite-degree parity spaces are their finite actual homogeneous components. -/
theorem exists_finiteParityDifferentialForm_equiv :
    (∃ e : evenSmoothDifferentialForms (n := n) (M := M) ≃ₗ[ℂ]
        ((p : {p : Fin (n + 1) // Even p.val}) →
          SmoothDifferentialForm (n := n) M p.val.val),
      ∀ u p, e u p = u.val p.val.val) ∧
    (∃ e : oddSmoothDifferentialForms (n := n) (M := M) ≃ₗ[ℂ]
        ((p : {p : Fin (n + 1) // Odd p.val}) →
          SmoothDifferentialForm (n := n) M p.val.val),
      ∀ u p, e u p = u.val p.val.val) := by
  classical
  let F := SmoothDifferentialForm (n := n) M
  -- Alternating tensors above the tangent dimension vanish, not only their classes.
  have hhigh (p : ℕ) (hp : n < p) (u : F p) : u = 0 := by
    apply Subtype.ext
    funext x
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext_alternating
    intro v hv
    have hcard := Fintype.card_le_of_injective v hv
    simp only [Fintype.card_fin] at hcard
    omega
  -- Restriction and finite-support extension are inverse on either actual parity subspace.
  have hfinite (P : ℕ → Prop)
      (S : Submodule ℂ (TotalSmoothDifferentialForm (n := n) M))
      (hS : ∀ u, u ∈ S ↔ ∀ p, ¬P p → u p = 0) :
      ∃ e : S ≃ₗ[ℂ] ((p : {p : Fin (n + 1) // P p.val}) → F p.val.val),
        ∀ u p, e u p = u.val p.val.val := by
    let L : S →ₗ[ℂ] ((p : {p : Fin (n + 1) // P p.val}) → F p.val.val) :=
      { toFun := fun u p ↦ u.val p.val.val
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hL : Function.Bijective L := by
      constructor
      · intro u v huv
        apply Subtype.ext
        apply DFinsupp.ext
        intro p
        by_cases hp : p < n + 1
        · by_cases hP : P p
          · exact congrFun huv ⟨⟨p, hp⟩, hP⟩
          · rw [(hS u.val).mp u.property p hP, (hS v.val).mp v.property p hP]
        · rw [hhigh p (by omega) (u.val p), hhigh p (by omega) (v.val p)]
      · intro v
        let s := (Finset.range (n + 1)).filter P
        let u : TotalSmoothDifferentialForm (n := n) M := DFinsupp.mk s
          (fun p ↦ v ⟨⟨p.val, Finset.mem_range.mp (Finset.mem_filter.mp p.property).1⟩,
            (Finset.mem_filter.mp p.property).2⟩)
        have hu : u ∈ S := by
          apply (hS u).mpr
          intro p hp
          exact DFinsupp.mk_of_notMem (by simp [s, hp])
        refine ⟨⟨u, hu⟩, ?_⟩
        funext p
        change u p.val.val = v p
        simp only [u, DFinsupp.mk_apply]
        rw [dite_eq_left (show p.val.val ∈ s by
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr p.val.isLt, p.property⟩)]
    exact ⟨LinearEquiv.ofBijective L hL, fun _ _ ↦ rfl⟩
  constructor
  · exact hfinite Even (evenSmoothDifferentialForms (n := n) (M := M))
      (by
        intro u
        change (∀ p, Odd p → u p = 0) ↔ ∀ p, ¬Even p → u p = 0
        simp only [Nat.not_even_iff_odd])
  · exact hfinite Odd (oddSmoothDifferentialForms (n := n) (M := M))
      (by
        intro u
        change (∀ p, Even p → u p = 0) ↔ ∀ p, ¬Odd p → u p = 0
        simp only [Nat.not_odd_iff_even])

end AtiyahSinger
