/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialParametrix
public import AtiyahSinger.Analysis.HermitianMetricAdjointKernel
public import AtiyahSinger.Analysis.HermitianMetricDifferentialAdjoint
public import AtiyahSinger.Geometry.HodgeLaplacian
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Elliptic realization of the original Hodge Laplacian

Public module ID: M0739.

The original smooth alternating forms are transported to one consistent family
of finite native bundles. Their actual exterior derivatives have symbol `i` times
covector exterior multiplication; formal adjunction recovers the already selected
codifferentials for the same Riemannian volume density. The sum of the two genuine
operator compositions realizes the original Hodge Laplacian.

Nonzero-covector Koszul exactness and the induced positive fiber metrics prove
ellipticity in every degree, including degree zero and degrees above the dimension.
Homogeneous symbol calculus then supplies a two-sided smooth-kernel parametrix.
No orientation, connectedness, positive dimension, or nonempty-base assumption is added.

Sources: Lawson--Michelsohn, Spin Geometry, II.5 and III.5.5--5.6.
The native bundle and principal-symbol adapters below are project implementation
of these standard arguments, preserving the original objects and pairings.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold MeasureTheory Module Set
open scoped BigOperators Manifold ContDiff ComplexConjugate Topology

/-- Covector multiplication and insertion contract the actual alternating-form complex. -/
theorem alternatizeUncurryFin_smulRight_curryLeft_add {n p : ℕ}
    (ξ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ (Fin n))
    (α : EuclideanSpace ℝ (Fin n) [⋀^Fin (p + 1)]→L[ℝ] ℂ) :
    ContinuousAlternatingMap.alternatizeUncurryFin (ξ.smulRight (α.curryLeft v)) +
      (ContinuousAlternatingMap.alternatizeUncurryFin (ξ.smulRight α)).curryLeft v =
        ξ v • α := by
  apply ContinuousAlternatingMap.ext
  intro w
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, Matrix.vecCons,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply]
  conv_lhs => rhs; rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.removeNth_zero,
    Fin.tail_cons, Fin.cons_succ, Fin.val_succ, pow_succ, mul_neg_one,
    neg_smul]
  have hremove (i : Fin (p + 1)) :
      i.succ.removeNth (Fin.cons v w : Fin (p + 2) → EuclideanSpace ℝ (Fin n)) =
        (Fin.cons v (i.removeNth w) : Fin (p + 1) → EuclideanSpace ℝ (Fin n)) := by
    change Fin.cons v w ∘ i.succ.succAbove = Fin.cons v (i.removeNth w)
    exact Fin.cons_comp_succ_succAbove v w i
  simp only [hremove, Finset.sum_neg_distrib]
  abel


variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- The original exterior derivative obeys its actual scalar product rule. -/
theorem smoothFormExteriorDerivative_leibniz (p : ℕ) (φ : M → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ φ)
    (u v : SmoothDifferentialForm (n := n) M p)
    (hv : ∀ x, v.val x = φ x • u.val x) (x : M) :
    (show EuclideanSpace ℝ (Fin n) [⋀^Fin (p + 1)]→L[ℝ] ℂ from
      (smoothFormExteriorDerivative p v).val x) =
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((show EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ from
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ x).smulRight
            (show EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ from u.val x)) +
          φ x • (show EuclideanSpace ℝ (Fin n) [⋀^Fin (p + 1)]→L[ℝ] ℂ from
            (smoothFormExteriorDerivative p u).val x) := by
  -- Compare the original form values with their centered chart expressions.
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let c := chartAt X x
  have hcx : x ∈ c.source := mem_chart_source X x
  have hcy : c x ∈ c.target := c.map_source hcx
  have hcder : mfderiv I I c x = ContinuousLinearMap.id ℝ X := by
    change mfderiv I I (extChartAt I x) x = _
    exact mfderiv_extChartAt_self
  have hcsder : mfderiv I I c.symm (c x) = ContinuousLinearMap.id ℝ X := by
    have hcomp := mfderiv_comp x
      ((mdifferentiable_of_mem_atlas (I := I) (chart_mem_atlas X x)).mdifferentiableAt_symm hcy)
      ((mdifferentiable_of_mem_atlas (I := I) (chart_mem_atlas X x)).mdifferentiableAt hcx)
    have hid : mfderiv I I (c.symm ∘ c) x = ContinuousLinearMap.id ℝ X := by
      apply HasMFDerivAt.mfderiv
      exact (hasMFDerivAt_id x).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (c.open_source.mem_nhds hcx) (fun y hy ↦ c.left_inv hy))
    erw [hid, hcder, ContinuousLinearMap.comp_id] at hcomp
    exact hcomp.symm
  have hcoord (w : SmoothDifferentialForm (n := n) M p) :
      differentialFormInChart w.val c (c x) = w.val x := by
    erw [differentialFormInChart, c.left_inv hcx, hcsder]
    rfl
  have hd (w : SmoothDifferentialForm (n := n) M p) :
      (smoothFormExteriorDerivative p w).val x =
        extDeriv (differentialFormInChart w.val c) (c x) := by
    have hs :=
      (existsUnique_smoothFormExteriorDerivative (n := n) (M := M) p).exists.choose_spec w x
    change (smoothFormExteriorDerivative p w).val x = _ at hs
    rw [hs]
    change (extDeriv (differentialFormInChart w.val c) (c x)).compContinuousLinearMap
      (mfderiv I I c x) = _
    erw [hcder]
    rfl
  -- Apply the ordinary scalar product rule to these same local representatives.
  let f := fun y : X ↦ φ (c.symm y)
  let a := differentialFormInChart u.val c
  have ha : DifferentiableAt ℝ a (c x) :=
    ((u.property c (chart_mem_atlas X x)).contDiffAt (c.open_target.mem_nhds hcy)).differentiableAt
      (by simp)
  have hf : HasFDerivAt f (mfderiv I 𝓘(ℝ, ℝ) φ x) (c x) := by
    have hi := (mdifferentiable_of_mem_atlas (I := I)
      (chart_mem_atlas X x)).mdifferentiableAt_symm hcy
    have h := (hφ.mdifferentiable (by simp) (c.symm (c x))).hasMFDerivAt.comp (c x)
      hi.hasMFDerivAt
    have h' : HasFDerivAt f
        ((show X →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) φ (c.symm (c x))).comp
          (show X →L[ℝ] X from mfderiv I I c.symm (c x))) (c x) := h.hasFDerivAt
    erw [c.left_inv hcx, hcsder, ContinuousLinearMap.comp_id] at h'
    exact h'
  have hvcoord : differentialFormInChart v.val c = fun y ↦ f y • a y := by
    funext y
    apply ContinuousAlternatingMap.ext
    intro w
    change v.val (c.symm y) _ = φ (c.symm y) • u.val (c.symm y) _
    rw [hv]
    rfl
  rw [hd v, hd u, hvcoord]
  unfold extDeriv
  erw [(hf.smul ha.hasFDerivAt).fderiv]
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
  change f (c x) • ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ a (c x)) +
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((show X →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) φ x).smulRight (a (c x))) = _
  have haCoord : a (c x) = (show X [⋀^Fin p]→L[ℝ] ℂ from u.val x) := hcoord u
  erw [show f (c x) = φ x from congrArg φ (c.left_inv hcx), haCoord]
  exact add_comm _ _


variable [T2Space M]
  (g : SmoothTangentMetric (n := n) (M := M))

set_option maxHeartbeats 3600000 in
-- The original finite bundle, inverse frames and metric are transported together.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual form bundle admits native finite coordinates retaining sections and metric. -/
theorem exists_smoothDifferentialForm_bundleModel (p : ℕ) :
  ∃ (R : ℕ) (Z : VectorBundleCore ℂ M (EuclideanSpace ℂ (Fin R))
      (atlas (EuclideanSpace ℝ (Fin n)) M))
    (e : (EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ) ≃L[ℂ]
      EuclideanSpace ℂ (Fin R)),
    letI : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin R)))
    letI : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin R)))
    IsSmoothComplexBundle (n := n) (r := R) Z.Fiber ∧
    (∀ i, Z.baseSet i = i.val.source) ∧
    (∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (x : M) (_ : x ∈ c.source)
      (a : DifferentialFormFiber (n := n) p x),
      (Z.localTriv ⟨c, hc⟩ ⟨x, e a⟩).2 = e (a.compContinuousLinearMap
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm (c x)))) ∧
    ∃ Φ : SmoothDifferentialForm (n := n) M p ≃ₗ[ℂ]
        smoothSections (n := n) (r := R) Z.Fiber,
      (∀ u x, (Φ u).val x = e (u.val x)) ∧
    ∃ metric : SmoothHermitianMetric (n := n) (r := R) Z.Fiber,
      ∀ x a b, metric.pairing x a b =
        differentialFormInner g p x (e.symm a) (e.symm b) := by
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
  let W := V [⋀^Fin p]→L[ℝ] ℂ
  let : FiniteDimensional ℂ W := hfinite p
  let R := Module.finrank ℂ W
  let e : W ≃L[ℂ] EuclideanSpace ℂ (Fin R) :=
    (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin R) ℂ).symm
  let T := tangentBundleCore I₀ M
  let C (L : V →L[ℝ] V) : (EuclideanSpace ℂ (Fin R)) →L[ℂ]
      EuclideanSpace ℂ (Fin R) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun a ↦ e ((e.symm a).compContinuousLinearMap L)
        map_add' := by
          intro a b
          rw [e.symm.map_add, ← e.map_add]
          apply congrArg e
          ext v
          rfl
        map_smul' := by
          intro c a
          rw [e.symm.map_smul, RingHom.id_apply, ← e.map_smul]
          apply congrArg e
          ext v
          rfl }
  have hCsmooth : ContDiff ℝ ∞ C := by
    let B (L : V →L[ℝ] V) : W →L[ℝ] W :=
      ContinuousAlternatingMap.compContinuousLinearMapCLM L
    have hB : ContDiff ℝ ∞ B := contDiff_iff_contDiffAt.mpr fun L ↦
      (ContinuousAlternatingMap.analyticAt_compContinuousLinearMapCLM L).contDiffAt
    -- Complex linear maps are smooth exactly when their real coordinate columns are.
    let e₀ := EuclideanSpace.equiv (Fin R) ℂ
    let cols := (e₀.arrowCongr (ContinuousLinearEquiv.refl ℂ
      (EuclideanSpace ℂ (Fin R)))).trans (ContinuousLinearEquiv.piRing (Fin R))
    have hc : ContDiff ℝ ∞ (fun L ↦ cols (C L)) := by
      apply contDiff_pi.mpr
      intro i
      exact (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
        (hB.clm_apply contDiff_const)
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
        change e ((e.symm a).compContinuousLinearMap (T.coordChange i i x)) = a
        have ht : T.coordChange i i x = ContinuousLinearMap.id ℝ V := by
          apply ContinuousLinearMap.ext
          intro v
          exact T.coordChange_self i x hx v
        rw [ht]
        have hid : (e.symm a).compContinuousLinearMap (ContinuousLinearMap.id ℝ V) =
            e.symm a := by
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
        change e (((e.symm (e ((e.symm a).compContinuousLinearMap
          (T.coordChange j i x))))).compContinuousLinearMap (T.coordChange k j x)) =
            e ((e.symm a).compContinuousLinearMap (T.coordChange k i x))
        rw [e.symm_apply_apply]
        apply congrArg e
        ext v
        apply congrArg (e.symm a)
        funext l
        exact T.coordChange_comp k j i x ⟨⟨hx.2, hx.1.2⟩, hx.1.1⟩ (v l) }
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
  -- Identify the temporary core coordinates with the original differential-form coordinates.
  have hchart (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M)
      (x : M) (hx : x ∈ c.source) (a : DifferentialFormFiber (n := n) p x) :
      (Z.localTriv ⟨c, hc⟩ ⟨x, e a⟩).2 =
        e (a.compContinuousLinearMap (mfderiv I₀ I₀ c.symm (c x))) := by
    change e ((e.symm (e a)).compContinuousLinearMap
      (T.coordChange ⟨c, hc⟩ (T.indexAt x) x)) = _
    rw [e.symm_apply_apply, hderiv c hc x hx]
  have hsmooth (u : M → W) :
      IsSmoothDifferentialForm u ↔
        IsSmoothSection (n := n) (r := R) Z.Fiber (fun x ↦ e (u x)) := by
    constructor
    · intro hu
      rintro _ ⟨c, rfl⟩
      have hc := contMDiffOn_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I₀) (n := ∞) c.property)
      have he := (e.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
        ((hu c.val c.property).contMDiffOn.comp hc (fun x hx ↦ c.val.map_source hx))
      apply he.congr
      intro x hx
      change (Z.localTriv c ⟨x, e (u x)⟩).2 =
        e (differentialFormInChart u c.val (c.val x))
      exact (hchart c.val c.property x hx (u x)).trans (by
        unfold differentialFormInChart
        congr 2
        exact (congrArg u (c.val.left_inv hx)).symm)
    · intro hu c hc
      have hc' := contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I₀) (n := ∞) hc)
      have hlocal := hu (Z.localTriv ⟨c, hc⟩) ⟨⟨c, hc⟩, rfl⟩
      have he := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
        (hlocal.comp hc' (fun y hy ↦ c.map_target hy))
      apply he.contDiffOn.congr
      intro y hy
      change differentialFormInChart u c y =
        e.symm ((Z.localTriv ⟨c, hc⟩ ⟨c.symm y, e (u (c.symm y))⟩).2)
      have heq := congrArg e.symm (hchart c hc (c.symm y)
        (c.map_target hy) (u (c.symm y)))
      simp only [e.symm_apply_apply] at heq
      apply Eq.trans _ heq.symm
      unfold differentialFormInChart
      congr 2
      exact (c.right_inv hy).symm
  let Φ : SmoothDifferentialForm (n := n) M p ≃ₗ[ℂ]
      smoothSections (n := n) (r := R) Z.Fiber :=
    { toFun := fun u ↦ ⟨fun x ↦ e (u.val x), (hsmooth u.val).mp u.property⟩
      invFun := fun s ↦ ⟨fun x ↦ e.symm (s.val x), (hsmooth _).mpr (by
        simpa only [e.apply_symm_apply] using
          (show IsSmoothSection (n := n) (r := R) Z.Fiber s.val from s.property))⟩
      left_inv := by
        intro u
        apply Subtype.ext
        funext x
        exact e.symm_apply_apply (u.val x)
      right_inv := by
        intro s
        apply Subtype.ext
        funext x
        exact e.apply_symm_apply (s.val x)
      map_add' := by
        intro u v
        apply Subtype.ext
        funext x
        exact e.map_add (u.val x) (v.val x)
      map_smul' := by
        intro a u
        apply Subtype.ext
        funext x
        exact e.map_smul a (u.val x) }
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
  -- The transported metric has exactly the original pairing; no fiber norm is replaced.
  let core (x : M) : InnerProductSpace.Core ℂ (Z.Fiber x) :=
    { inner := fun a b ↦ differentialFormInner g p x (e.symm a) (e.symm b)
      conj_inner_symm := fun a b ↦ (differentialFormInnerCore g p x).conj_inner_symm _ _
      re_inner_nonneg := fun a ↦ (differentialFormInnerCore g p x).re_inner_nonneg _
      add_left := by
        intro a b c
        rw [e.symm.map_add]
        exact (differentialFormInnerCore g p x).add_left _ _ _
      smul_left := by
        intro a b c
        rw [e.symm.map_smul]
        exact (differentialFormInnerCore g p x).smul_left _ _ _
      definite := by
        intro a ha
        apply e.symm.injective
        exact ((differentialFormInnerCore g p x).definite _ ha).trans e.symm.map_zero.symm }
  let metric : SmoothHermitianMetric (n := n) (r := R) Z.Fiber :=
    { toCore := core
      isSmoothBundle := inferInstance
      contMDiffOn_gram := by
        intro f hf i j x hx
        let := hf
        obtain ⟨u, hu⟩ := hloc f x hx (EuclideanSpace.single i 1)
        obtain ⟨v, hv⟩ := hloc f x hx (EuclideanSpace.single j 1)
        have hpair := (contMDiff_differentialFormInner g p (Φ.symm u) (Φ.symm v)).contMDiffAt
          (x := x)
        apply (hpair.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [hu, hv] with y hyu hyv
        change differentialFormInner g p y (e.symm (f.symmL ℂ y _))
          (e.symm (f.symmL ℂ y _)) =
          differentialFormInner g p y (e.symm (u.val y)) (e.symm (v.val y))
        rw [hyu, hyv] }
  exact ⟨R, Z, e, inferInstance, (fun _ ↦ rfl), hchart, Φ, (fun _ _ ↦ rfl),
    metric, fun _ _ _ ↦ rfl⟩


variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

set_option maxHeartbeats 800000 in
-- The actual exterior derivatives are realized in a single family of native bundle models.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- The original Hodge Laplacian has a same-metric self-adjoint PDO realization
and a two-sided smooth-kernel parametrix on the original compact manifold. -/
theorem exists_smoothFormHodgeLaplacian_parametrix (degree : ℕ) :
    letI : IsSmoothPositiveMeasure (n := n) g.riemannianVolume :=
      g.isSmoothPositiveMeasure_riemannianVolume
    ∃ B : SmoothFiniteComplexBundle (n := n) M,
    ∃ Φ : SmoothDifferentialForm (n := n) M degree ≃ₗ[ℂ]
        smoothSections (n := n) (r := B.rank) B.Fiber,
    ∃ h : SmoothHermitianMetric (n := n) (r := B.rank) B.Fiber,
    ∃ L : PseudodifferentialOperator (n := n) (r := B.rank) (q := B.rank)
        B.Fiber B.Fiber g.riemannianVolume (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)),
      (∀ u v, h.sectionPairing g.riemannianVolume (Φ u) (Φ v) =
        smoothFormPairing g degree u v) ∧
      (∀ u, L.toLinearMap (Φ u) = Φ (smoothFormHodgeLaplacian g degree u)) ∧
      IsMetricFormalAdjoint h h g.riemannianVolume L.toLinearMap L.toLinearMap ∧
      ∃ R : PseudodifferentialOperator (n := n) (r := B.rank) (q := B.rank)
          B.Fiber B.Fiber g.riemannianVolume (-(((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))),
        IsParametrix g.riemannianVolume L.toLinearMap R.toLinearMap := by
  classical
  -- Stage 1: choose all degrees together, retaining the same sections and induced metrics.
  choose rank core coordinates hdata using
    (fun p : ℕ ↦ exists_smoothDifferentialForm_bundleModel g p)
  let normedGroup (p : ℕ) : ∀ x, NormedAddCommGroup ((core p).Fiber x) := fun _ ↦
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin (rank p))))
  let normedSpace (p : ℕ) : ∀ x, NormedSpace ℂ ((core p).Fiber x) := fun _ ↦
    inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin (rank p))))
  choose hSmooth hbase hchart sectionEquiv hsection metric hmetric using hdata
  let smoothBundle (p : ℕ) : IsSmoothComplexBundle (n := n) (r := rank p) (core p).Fiber :=
    hSmooth p
  have hdifferential (p : ℕ) :
      IsDifferentialOperator (n := n) (r := rank p) (q := rank (p + 1))
        (core p).Fiber (core (p + 1)).Fiber 1
        ((sectionEquiv (p + 1)).toLinearMap.comp
          ((smoothFormExteriorDerivative p).comp (sectionEquiv p).symm.toLinearMap)) := by
    let V := EuclideanSpace ℝ (Fin n)
    let I₀ := 𝓘(ℝ, V)
    let W := V [⋀^Fin p]→L[ℝ] ℂ
    let W' := V [⋀^Fin (p + 1)]→L[ℝ] ℂ
    let : FiniteDimensional ℂ W :=
      FiniteDimensional.of_injective (coordinates p).toLinearMap (coordinates p).injective
    let : FiniteDimensional ℂ W' :=
      FiniteDimensional.of_injective (coordinates (p + 1)).toLinearMap
        (coordinates (p + 1)).injective
    let r := rank p
    let q := rank (p + 1)
    let E := core p
    let F := core (p + 1)
    let e := coordinates p
    let f := coordinates (p + 1)
    let Φ := sectionEquiv p
    let Ψ := sectionEquiv (p + 1)
    have hΦ := hsection p
    have hΨ := hsection (p + 1)
    have hEc := hchart p
    have hFc := hchart (p + 1)
    have hEb := hbase p
    have hFb := hbase (p + 1)
    let S := EuclideanSpace ℂ (Fin r)
    let T := EuclideanSpace ℂ (Fin q)
    let D := Ψ.toLinearMap.comp ((smoothFormExteriorDerivative p).comp Φ.symm.toLinearMap)
    -- The exterior derivative is the alternating sum of the real coordinate derivatives.
    let K (j : Fin n) : W →L[ℂ] W' := LinearMap.toContinuousLinearMap
      { toFun := fun a ↦ ContinuousAlternatingMap.alternatizeUncurryFin
          ((EuclideanSpace.proj (𝕜 := ℝ) j).smulRight a)
        map_add' := by
          intro a b
          have heq : (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (a + b) =
              (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight a +
                (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight b := by
            apply ContinuousLinearMap.ext
            intro y
            change (y j : ℝ) • (a + b) = (y j : ℝ) • a + (y j : ℝ) • b
            exact smul_add _ _ _
          rw [heq, ContinuousAlternatingMap.alternatizeUncurryFin_add]
        map_smul' := by
          intro c a
          have heq : (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (c • a) =
              c • (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight a := by
            apply ContinuousLinearMap.ext
            intro y
            change (y j : ℝ) • (c • a) = c • ((y j : ℝ) • a)
            exact smul_comm _ _ _
          rw [heq, ContinuousAlternatingMap.alternatizeUncurryFin_smul]
          rfl }
    have hK (L : V →L[ℝ] W) :
        ContinuousAlternatingMap.alternatizeUncurryFin L =
          ∑ j : Fin n, K j (L (EuclideanSpace.single j 1)) := by
      have hL : L = ∑ j : Fin n,
          (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (L (EuclideanSpace.single j 1)) := by
        apply ContinuousLinearMap.ext
        intro y
        simp only [sum_apply]
        change L y = ∑ j : Fin n, y j • L (EuclideanSpace.single j 1)
        calc
          L y = L (∑ j : Fin n, y j • EuclideanSpace.single j 1) := by
            congr 1
            simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
              EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
              ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr y).symm
          _ = ∑ j : Fin n, y j • L (EuclideanSpace.single j 1) := by
            rw [map_sum]
            simp only [map_smul]
      conv_lhs => rw [hL]
      change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℂ)
        (∑ j, (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (L (EuclideanSpace.single j 1))) = _
      rw [map_sum]
      rfl
    have hEchart (u : SmoothDifferentialForm (n := n) M p)
        (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M) (y : M) (hy : y ∈ c.source) :
        (E.localTriv ⟨c, hc⟩ ⟨y, (Φ u).val y⟩).2 =
          e (differentialFormInChart u.val c (c y)) := by
      rw [hΦ]
      exact (hEc c hc y hy (u.val y)).trans (by
        unfold differentialFormInChart
        congr 2
        let u₀ : M → W := fun z ↦ u.val z
        exact (congrArg u₀ (c.left_inv hy)).symm)
    have hFchart (u : SmoothDifferentialForm (n := n) M (p + 1))
        (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M) (y : M) (hy : y ∈ c.source) :
        (F.localTriv ⟨c, hc⟩ ⟨y, (Ψ u).val y⟩).2 =
          f (differentialFormInChart u.val c (c y)) := by
      rw [hΨ]
      exact (hFc c hc y hy (u.val y)).trans (by
        unfold differentialFormInChart
        congr 2
        let u₀ : M → W' := fun z ↦ u.val z
        exact (congrArg u₀ (c.left_inv hy)).symm)
    have hd : IsDifferentialOperator (n := n) (r := r) (q := q) E.Fiber F.Fiber 1 D := by
      intro c hc i hi j hj x hx
      let := hi
      let := hj
      let ec := E.localTriv ⟨c, hc⟩
      let fc := F.localTriv ⟨c, hc⟩
      let : MemTrivializationAtlas ec := ⟨⟨c, hc⟩, rfl⟩
      let : MemTrivializationAtlas fc := ⟨⟨c, hc⟩, rfl⟩
      have hec : ec.baseSet = c.source := hEb ⟨c, hc⟩
      have hfc : fc.baseSet = c.source := hFb ⟨c, hc⟩
      let U := c.source ∩ i.baseSet ∩ j.baseSet
      let O := c.target ∩ c.symm ⁻¹' i.baseSet ∩ c.symm ⁻¹' j.baseSet
      have hO : IsOpen O := by
        convert (c.isOpen_inter_preimage_symm i.open_baseSet).inter
          (c.isOpen_inter_preimage_symm j.open_baseSet) using 1
        ext z
        simp only [O, Set.mem_inter_iff]
        tauto
      have hUO : c '' U ⊆ O := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨⟨c.map_source hy.1.1, by
          simpa only [Set.mem_preimage, c.left_inv hy.1.1] using hy.1.2⟩,
          by simpa only [Set.mem_preimage, c.left_inv hy.1.1] using hy.2⟩
      let A (z : V) : S →L[ℂ] W := e.symm.toContinuousLinearMap.comp
        (i.coordChangeL ℂ ec (c.symm z)).toContinuousLinearMap
      let B (z : V) : W' →L[ℂ] T :=
        (fc.coordChangeL ℂ j (c.symm z)).toContinuousLinearMap.comp f.toContinuousLinearMap
      have hA : ContDiffOn ℝ ∞ A O := by
        have htrans := IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) i ec
        have hcs := contMDiffOn_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I₀) (n := ∞) hc)
        have hbase := htrans.comp (hcs.mono (show O ⊆ c.target from fun _ hz ↦ hz.1.1)) (by
          intro z hz
          exact ⟨hz.1.2, hec ▸ c.map_target hz.1.1⟩)
        exact ((ContinuousLinearMap.compL ℂ S S W) e.symm.toContinuousLinearMap
          |>.restrictScalars ℝ).contDiff.comp_contDiffOn hbase.contDiffOn
      have hB : ContDiffOn ℝ ∞ B O := by
        have htrans := IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) fc j
        have hcs := contMDiffOn_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I₀) (n := ∞) hc)
        have hbase := htrans.comp (hcs.mono (show O ⊆ c.target from fun _ hz ↦ hz.1.1)) (by
          intro z hz
          exact ⟨hfc ▸ c.map_target hz.1.1, hz.2⟩)
        exact ((ContinuousLinearMap.compL ℂ W' T T).flip f.toContinuousLinearMap
          |>.restrictScalars ℝ).contDiff.comp_contDiffOn hbase.contDiffOn
      let C₀ (z : V) : S →L[ℂ] T :=
        ∑ a : Fin n, (B z).comp ((K a).comp (fderiv ℝ A z (EuclideanSpace.single a 1)))
      let C₁ (a : Fin n) (z : V) : S →L[ℂ] T := (B z).comp ((K a).comp (A z))
      have hC₀ : ContDiffOn ℝ ∞ C₀ O := by
        have hDA : ContDiffOn ℝ ∞ (fderiv ℝ A) O :=
          hA.fderiv_of_isOpen hO (by simp)
        apply ContDiffOn.sum
        intro a _
        have hDa := hDA.clm_apply (contDiffOn_const (c := EuclideanSpace.single a 1))
        have hinner :=
          ((ContinuousLinearMap.compL ℂ S W W' (K a)).restrictScalars ℝ).contDiff
            |>.comp_contDiffOn hDa
        let μ := (ContinuousLinearMap.compL ℂ S W' T).bilinearRestrictScalars ℝ
        exact (μ.contDiff.comp_contDiffOn hB).clm_apply hinner
      have hC₁ (a : Fin n) : ContDiffOn ℝ ∞ (C₁ a) O := by
        have hinner :=
          ((ContinuousLinearMap.compL ℂ S W W' (K a)).restrictScalars ℝ).contDiff
            |>.comp_contDiffOn hA
        let μ := (ContinuousLinearMap.compL ℂ S W' T).bilinearRestrictScalars ℝ
        exact (μ.contDiff.comp_contDiffOn hB).clm_apply hinner
      let Q : CoordinateDifferentialOperator n r q 1 (c '' U) :=
        { coefficient := Fin.cases (fun _ ↦ C₀)
            (fun b α z ↦ Complex.I • C₁ (α ⟨0, Nat.zero_lt_succ b.val⟩) z)
          smooth_coefficient := by
            intro b
            refine Fin.cases (fun _ ↦ hC₀.mono hUO) (fun b α ↦ ?_) b
            exact ((hC₁ (α ⟨0, Nat.zero_lt_succ b.val⟩)).mono hUO).const_smul Complex.I }
      have hQ (w : V → S) (z : V) : Q.apply w z = C₀ z (w z) +
          ∑ a : Fin n, C₁ a z (fderiv ℝ w z (EuclideanSpace.single a 1)) := by
        let reindex : (Fin 1 → Fin n) ≃ Fin n :=
          { toFun α := α 0
            invFun a := fun _ ↦ a
            left_inv α := by funext t; exact congrArg α (Subsingleton.elim (0 : Fin 1) t)
            right_inv _ := rfl }
        unfold CoordinateDifferentialOperator.apply
        rw [Fin.sum_univ_two]
        have hone : (1 : Fin 2) = (0 : Fin 1).succ := rfl
        rw [hone]
        simp only [Q, Fin.cases_zero, Fin.cases_succ, Fin.val_succ, Fin.val_zero, zero_add,
          pow_zero, one_smul, iteratedFDeriv_zero_apply, pow_one, Fintype.sum_unique,
          smul_apply, map_smul, smul_smul, neg_mul, Complex.I_mul_I, neg_neg]
        change C₀ z (w z) + (∑ α : Fin 1 → Fin n,
          C₁ (α 0) z (iteratedFDeriv ℝ 1 w z (fun t ↦ EuclideanSpace.single (α t) 1))) = _
        simp only [iteratedFDeriv_one_apply]
        exact congrArg (C₀ z (w z) + ·) (reindex.sum_comp
          (fun a ↦ C₁ a z (fderiv ℝ w z (EuclideanSpace.single a 1))))
      refine ⟨U, (c.open_source.inter i.open_baseSet).inter j.open_baseSet, hx, Q,
        (fun _ hy ↦ hy), ?_⟩
      intro s y hy
      let w := sectionInChart E.Fiber c i s.val
      have hz : c y ∈ O := hUO ⟨y, hy, rfl⟩
      have hw : ContDiffOn ℝ ∞ w O := by
        have hcs := contMDiffOn_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I₀) (n := ∞) hc)
        exact ((s.property i hi).comp (hcs.mono (show O ⊆ c.target from fun _ hz ↦ hz.1.1))
          (fun _ hz ↦ hz.1.2)).contDiffOn
      have hcoord : differentialFormInChart (Φ.symm s).val c =ᶠ[𝓝 (c y)]
          (fun z ↦ A z (w z)) := by
        filter_upwards [hO.mem_nhds hz] with z hzo
        have hzf : c.symm z ∈ ec.baseSet := hec ▸ c.map_target hzo.1.1
        have htr := coordChangeL_section_coordinates E.Fiber i ec s.val (c.symm z)
          ⟨hzo.1.2, hzf⟩
        have hcform := hEchart (Φ.symm s) c hc (c.symm z) (c.map_target hzo.1.1)
        rw [Φ.apply_symm_apply, c.right_inv hzo.1.1] at hcform
        apply e.injective
        change e (differentialFormInChart (Φ.symm s).val c z) =
          e (e.symm (i.coordChangeL ℂ ec (c.symm z) (w z)))
        rw [e.apply_symm_apply]
        exact hcform.symm.trans htr
      have hderiv : fderiv ℝ (differentialFormInChart (Φ.symm s).val c) (c y) =
          fderiv ℝ (fun z ↦ A z (w z)) (c y) := hcoord.fderiv_eq
      have hvalue : (j ⟨y, (D s).val y⟩).2 =
          B (c y) (ContinuousAlternatingMap.alternatizeUncurryFin
            (fderiv ℝ (fun z ↦ A z (w z)) (c y))) := by
        have htr := coordChangeL_section_coordinates F.Fiber fc j (D s).val y
          ⟨hfc ▸ hy.1.1, hy.2⟩
        have hcform := hFchart (smoothFormExteriorDerivative p (Φ.symm s)) c hc y hy.1.1
        change (fc ⟨y, (D s).val y⟩).2 = _ at hcform
        rw [smoothFormExteriorDerivative_inChart _ c hc (c y) (c.map_source hy.1.1)] at hcform
        change (fc ⟨y, (D s).val y⟩).2 =
          f (ContinuousAlternatingMap.alternatizeUncurryFin
            (fderiv ℝ (differentialFormInChart (Φ.symm s).val c) (c y))) at hcform
        rw [hderiv] at hcform
        rw [htr, hcform]
        change _ = fc.coordChangeL ℂ j (c.symm (c y)) _
        rw [c.left_inv hy.1.1]
        rfl
      rw [hvalue, hQ, hK, map_sum]
      have hAs := (hA.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
      have hws := (hw.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
      let res := ContinuousLinearMap.restrictScalarsL ℂ S W ℝ ℝ
      have hAs' := res.hasFDerivAt.comp (c y) hAs.hasFDerivAt
      have hder := (hAs'.clm_apply hws.hasFDerivAt).fderiv
      have hjets (a : Fin n) :
          fderiv ℝ (fun z ↦ A z (w z)) (c y) (EuclideanSpace.single a 1) =
            A (c y) (fderiv ℝ w (c y) (EuclideanSpace.single a 1)) +
            fderiv ℝ A (c y) (EuclideanSpace.single a 1) (w (c y)) := by
        exact congrArg (fun L : V →L[ℝ] W ↦ L (EuclideanSpace.single a 1)) hder
      simp only [hjets, map_add, Finset.sum_add_distrib, C₀, C₁,
        sum_apply, ContinuousLinearMap.comp_apply]
      abel
    exact hd
  -- Stage 2: identify the actual first-order symbol by its scalar commutator.
  let P (p : ℕ) : DifferentialOperator (n := n) (r := rank p) (q := rank (p + 1))
      (core p).Fiber (core (p + 1)).Fiber 1 :=
    ⟨_, hdifferential p⟩
  let wedge (p : ℕ) (ξ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
      (EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ) →ₗ[ℂ]
        (EuclideanSpace ℝ (Fin n) [⋀^Fin (p + 1)]→L[ℝ] ℂ) :=
    { toFun := fun a ↦ ContinuousAlternatingMap.alternatizeUncurryFin (ξ.smulRight a)
      map_add' := by
        intro a b
        have heq : ξ.smulRight (a + b) = ξ.smulRight a + ξ.smulRight b := by
          ext v w
          exact smul_add _ _ _
        rw [heq, ContinuousAlternatingMap.alternatizeUncurryFin_add]
      map_smul' := by
        intro c a
        have heq : ξ.smulRight (c • a) = c • ξ.smulRight a := by
          ext v w
          exact smul_comm _ _ _
        rw [heq, ContinuousAlternatingMap.alternatizeUncurryFin_smul]
        rfl }
  let A (p : ℕ) (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      (core p).Fiber x →ₗ[ℂ] (core (p + 1)).Fiber x :=
    (coordinates (p + 1)).toLinearMap.comp
      ((wedge p ξ).comp (coordinates p).symm.toLinearMap)
  have hP (p : ℕ) (u : SmoothDifferentialForm (n := n) M p) :
      (P p).toLinearMap (sectionEquiv p u) =
        sectionEquiv (p + 1) (smoothFormExteriorDerivative p u) := by
    change sectionEquiv (p + 1)
      (smoothFormExteriorDerivative p ((sectionEquiv p).symm (sectionEquiv p u))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hsymbol (p : ℕ) (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      (P p).principalSymbol x ξ = Complex.I • A p x ξ := by
    apply (P p).principalSymbol_eq_smul_of_leibniz (A p)
    intro φ hφ s t hst y
    let u := (sectionEquiv p).symm s
    let v := (sectionEquiv p).symm t
    have hu : sectionEquiv p u = s := (sectionEquiv p).apply_symm_apply s
    have hv : sectionEquiv p v = t := (sectionEquiv p).apply_symm_apply t
    have hvu (z : M) : v.val z = φ z • u.val z := by
      apply (coordinates p).injective
      change coordinates p (show EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ from
        v.val z) = coordinates p ((φ z : ℂ) •
          (show EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ from u.val z))
      exact (hsection p v z).symm.trans ((congrArg (fun w ↦ w.val z) hv).trans
        ((hst z).trans ((congrArg ((φ z : ℂ) • ·)
          ((congrArg (fun w ↦ w.val z) hu).symm.trans (hsection p u z))).trans
            ((coordinates p).map_smul (φ z : ℂ) _).symm)))
    have h := smoothFormExteriorDerivative_leibniz p φ hφ u v hvu y
    rw [← hv, ← hu, hP, hP, hsection, hsection, hsection]
    change coordinates (p + 1) ((smoothFormExteriorDerivative p v).val y) =
      coordinates (p + 1) (wedge p (mfderiv _ _ φ y)
        ((coordinates p).symm (coordinates p (u.val y)))) +
        (φ y : ℂ) • coordinates (p + 1) ((smoothFormExteriorDerivative p u).val y)
    rw [ContinuousLinearEquiv.symm_apply_apply]
    have hc := congrArg (coordinates (p + 1)) h
    exact hc.trans (((coordinates (p + 1)).map_add _ _).trans
      (congrArg (coordinates (p + 1) (wedge p (mfderiv _ _ φ y) (u.val y)) + ·)
        ((coordinates (p + 1)).map_smul (φ y : ℂ) _)))
  -- Stage 3: adjunction uses the same metric density and the original selected codifferential.
  have hpair (p : ℕ) (u v : SmoothDifferentialForm (n := n) M p) :
      (metric p).sectionPairing g.riemannianVolume (sectionEquiv p u) (sectionEquiv p v) =
        smoothFormPairing g p u v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      change (metric p).pairing x ((sectionEquiv p u).val x)
        ((sectionEquiv p v).val x) = differentialFormInner g p x (u.val x) (v.val x)
      rw [hmetric, hsection, hsection]
      erw [(coordinates p).symm_apply_apply, (coordinates p).symm_apply_apply]
  let : IsSmoothPositiveMeasure (n := n) g.riemannianVolume :=
    g.isSmoothPositiveMeasure_riemannianVolume
  let Q (p : ℕ) := (P p).metricFormalAdjoint (μ := g.riemannianVolume)
    (metric p) (metric (p + 1))
  have hQ (p : ℕ) (u : SmoothDifferentialForm (n := n) M (p + 1)) :
      (Q p).toLinearMap (sectionEquiv (p + 1) u) =
        sectionEquiv p (smoothFormCodifferential g p u) := by
    let δ : SmoothDifferentialForm (n := n) M (p + 1) →ₗ[ℂ]
        SmoothDifferentialForm (n := n) M p :=
      (sectionEquiv p).symm.toLinearMap.comp
        ((Q p).toLinearMap.comp (sectionEquiv (p + 1)).toLinearMap)
    have hδ (v : SmoothDifferentialForm (n := n) M (p + 1)) :
        (Q p).toLinearMap (sectionEquiv (p + 1) v) = sectionEquiv p (δ v) :=
      ((sectionEquiv p).apply_symm_apply _).symm
    have heq : δ = smoothFormCodifferential g p := by
      apply (existsUnique_smoothFormCodifferential g p).unique
      · intro v w _hv
        have hadj := (P p).isMetricFormalAdjoint_metricFormalAdjoint
          (μ := g.riemannianVolume) (metric p) (metric (p + 1))
          (sectionEquiv p v) (sectionEquiv (p + 1) w)
        change (metric (p + 1)).sectionPairing g.riemannianVolume
          ((P p).toLinearMap (sectionEquiv p v)) (sectionEquiv (p + 1) w) =
            (metric p).sectionPairing g.riemannianVolume (sectionEquiv p v)
              ((Q p).toLinearMap (sectionEquiv (p + 1) w)) at hadj
        rw [hP, hδ, hpair, hpair] at hadj
        exact hadj
      · exact (existsUnique_smoothFormCodifferential g p).exists.choose_spec
    rw [← heq]
    exact hδ u
  -- Stage 4: insertion contracts the nonzero-covector exterior symbol complex.
  have hsymbolExact (p : ℕ) (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) (hξ : ξ ≠ 0)
      (a : (core (p + 1)).Fiber x) (ha : (P (p + 1)).principalSymbol x ξ a = 0) :
      ∃ b : (core p).Fiber x, (P p).principalSymbol x ξ b = a := by
    let X := EuclideanSpace ℝ (Fin n)
    let ξ₀ : X →L[ℝ] ℝ := ξ
    obtain ⟨w, hw⟩ : ∃ w : X, ξ₀ w ≠ 0 := by
      by_contra h
      apply hξ
      apply ContinuousLinearMap.ext
      intro w
      exact not_ne_iff.mp (fun hw ↦ h ⟨w, hw⟩)
    let v := (ξ₀ w)⁻¹ • w
    have hv : ξ₀ v = 1 := by simp [v, hw]
    let α := (coordinates (p + 1)).symm a
    have hwedge : wedge (p + 1) ξ₀ α = 0 := by
      apply (coordinates (p + 2)).injective
      rw [map_zero]
      rw [hsymbol] at ha
      change Complex.I • coordinates (p + 2) (wedge (p + 1) ξ₀ α) = 0 at ha
      exact (smul_eq_zero.mp ha).resolve_left Complex.I_ne_zero
    have hα : wedge p ξ₀ (α.curryLeft v) = α := by
      have h := alternatizeUncurryFin_smulRight_curryLeft_add ξ₀ v α
      change wedge p ξ₀ (α.curryLeft v) +
        (wedge (p + 1) ξ₀ α).curryLeft v = ξ₀ v • α at h
      rw [hwedge, hv, one_smul] at h
      have hz : (0 : X [⋀^Fin (p + 2)]→L[ℝ] ℂ).curryLeft v = 0 := by ext w; rfl
      rw [hz, add_zero] at h
      exact h
    refine ⟨-Complex.I • coordinates p (α.curryLeft v), ?_⟩
    rw [hsymbol]
    change Complex.I • coordinates (p + 1)
      (wedge p ξ₀ ((coordinates p).symm (-Complex.I • coordinates p (α.curryLeft v)))) = a
    rw [map_smul, ContinuousLinearEquiv.symm_apply_apply, map_smul, map_smul, hα]
    simp only [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    exact (coordinates (p + 1)).apply_symm_apply a
  have hsymbolZero (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) (hξ : ξ ≠ 0)
      (a : (core 0).Fiber x) (ha : (P 0).principalSymbol x ξ a = 0) : a = 0 := by
    let X := EuclideanSpace ℝ (Fin n)
    let ξ₀ : X →L[ℝ] ℝ := ξ
    obtain ⟨w, hw⟩ : ∃ w : X, ξ₀ w ≠ 0 := by
      by_contra h
      apply hξ
      apply ContinuousLinearMap.ext
      intro w
      exact not_ne_iff.mp (fun hw ↦ h ⟨w, hw⟩)
    let α := (coordinates 0).symm a
    have hwedge : wedge 0 ξ₀ α = 0 := by
      apply (coordinates 1).injective
      rw [map_zero]
      rw [hsymbol] at ha
      change Complex.I • coordinates 1 (wedge 0 ξ₀ α) = 0 at ha
      exact (smul_eq_zero.mp ha).resolve_left Complex.I_ne_zero
    have heval := congrArg (fun β : X [⋀^Fin 1]→L[ℝ] ℂ ↦ β (fun _ ↦ w)) hwedge
    change (ContinuousAlternatingMap.alternatizeUncurryFin (ξ₀.smulRight α))
      (fun _ ↦ w) = 0 at heval
    rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply] at heval
    change (∑ i : Fin 1, (-1 : ℤ) ^ i.val •
      (ξ₀ w • α (i.removeNth (fun _ : Fin 1 ↦ w)))) = 0 at heval
    rw [Fin.sum_univ_one] at heval
    simp only [Fin.val_zero, pow_zero, one_smul] at heval
    apply (coordinates 0).symm.injective
    rw [map_zero]
    apply ContinuousAlternatingMap.ext
    intro v
    have heq : (0 : Fin 1).removeNth (fun _ ↦ w) = v := Subsingleton.elim _ _
    rw [heq] at heval
    exact (smul_eq_zero.mp heval).resolve_left hw
  -- Stage 5: compose and add the actual maps, preserving their literal real-order indices.
  let m : ℝ := ((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)
  let S : (p : ℕ) → globalSymbolSpace (n := n) (r := rank p) (q := rank p)
      (core p).Fiber (core p).Fiber m
    | 0 => globalSymbolSpaceComp (Q 0).principalGlobalSymbol (P 0).principalGlobalSymbol
    | p + 1 =>
        globalSymbolSpaceComp (P p).principalGlobalSymbol (Q p).principalGlobalSymbol +
          globalSymbolSpaceComp (Q (p + 1)).principalGlobalSymbol
            (P (p + 1)).principalGlobalSymbol
  let L : (p : ℕ) → PseudodifferentialOperator (n := n) (r := rank p) (q := rank p)
      (core p).Fiber (core p).Fiber g.riemannianVolume m
    | 0 => ((Q 0).toPseudodifferentialOperator g.riemannianVolume).comp
        ((P 0).toPseudodifferentialOperator g.riemannianVolume)
    | p + 1 =>
        (((P p).toPseudodifferentialOperator g.riemannianVolume).comp
          ((Q p).toPseudodifferentialOperator g.riemannianVolume)).add
            (((Q (p + 1)).toPseudodifferentialOperator g.riemannianVolume).comp
              ((P (p + 1)).toPseudodifferentialOperator g.riemannianVolume))
  have hL (p : ℕ) (u : SmoothDifferentialForm (n := n) M p) :
      (L p).toLinearMap (sectionEquiv p u) =
        sectionEquiv p (smoothFormHodgeLaplacian g p u) := by
    cases p with
    | zero =>
        change (Q 0).toLinearMap ((P 0).toLinearMap (sectionEquiv 0 u)) = _
        rw [hP, hQ]
        rfl
    | succ p =>
        change (P p).toLinearMap ((Q p).toLinearMap (sectionEquiv (p + 1) u)) +
          (Q (p + 1)).toLinearMap ((P (p + 1)).toLinearMap (sectionEquiv (p + 1) u)) = _
        rw [hP, hQ, hQ, hP, ← map_add]
        rfl
  have hLsymbol (p : ℕ) : (L p).principalSymbol =
      globalPrincipalSymbolClass (core p).Fiber (core p).Fiber m (S p) := by
    cases p with
    | zero =>
        change (((Q 0).toPseudodifferentialOperator g.riemannianVolume).comp
          ((P 0).toPseudodifferentialOperator g.riemannianVolume)).principalSymbol = _
        rw [PseudodifferentialOperator.principalSymbol_comp,
          DifferentialOperator.principalSymbol_toPseudodifferentialOperator,
          DifferentialOperator.principalSymbol_toPseudodifferentialOperator,
          globalPrincipalSymbolComp_class]
    | succ p =>
        change (PseudodifferentialOperator.add _ _).principalSymbol = _
        rw [PseudodifferentialOperator.principalSymbol_add,
          PseudodifferentialOperator.principalSymbol_comp,
          PseudodifferentialOperator.principalSymbol_comp]
        simp only [DifferentialOperator.principalSymbol_toPseudodifferentialOperator,
          globalPrincipalSymbolComp_class]
        rfl
  -- Stage 6: positivity and exactness give injective, hence bijective, Laplacian symbols.
  have helliptic (p : ℕ) : IsEllipticGlobalSymbol (core p).Fiber (core p).Fiber (S p).val := by
    intro x ξ hξ
    let : FiniteDimensional ℂ ((core p).Fiber x) := inferInstanceAs
      (FiniteDimensional ℂ (EuclideanSpace ℂ (Fin (rank p))))
    have hzero (a : (core p).Fiber x) (ha : (S p).val x ξ a = 0) : a = 0 := by
      cases p with
      | zero =>
          change (Q 0).principalSymbol x ξ ((P 0).principalSymbol x ξ a) = 0 at ha
          have he := (P 0).principalSymbol_metricFormalAdjoint_pairing
            (μ := g.riemannianVolume) (metric 0) (metric 1) x ξ a
            ((P 0).principalSymbol x ξ a)
          change (metric 1).pairing x ((P 0).principalSymbol x ξ a)
            ((P 0).principalSymbol x ξ a) =
              (metric 0).pairing x a ((Q 0).principalSymbol x ξ
                ((P 0).principalSymbol x ξ a)) at he
          rw [ha] at he
          have hz : (metric 0).pairing x a 0 = 0 := by
            let : InnerProductSpace.Core ℂ ((core 0).Fiber x) := (metric 0).toCore x
            exact InnerProductSpace.Core.inner_zero_right _
          exact hsymbolZero x ξ hξ a (((metric 1).toCore x).definite _ (he.trans hz))
      | succ p =>
          let d := (P (p + 1)).principalSymbol x ξ
          let δ := (Q p).principalSymbol x ξ
          change (P p).principalSymbol x ξ (δ a) +
            (Q (p + 1)).principalSymbol x ξ (d a) = 0 at ha
          have hadj := (P (p + 1)).principalSymbol_metricFormalAdjoint_pairing
            (μ := g.riemannianVolume) (metric (p + 1)) (metric (p + 2)) x ξ a (d a)
          have hadj' := (P p).principalSymbol_metricFormalAdjoint_pairing
            (μ := g.riemannianVolume) (metric p) (metric (p + 1)) x ξ (δ a) a
          let : InnerProductSpace.Core ℂ ((core (p + 1)).Fiber x) :=
            (metric (p + 1)).toCore x
          have he := congrArg (fun b ↦ (metric (p + 1)).pairing x a b) ha
          change (metric (p + 1)).pairing x a
            ((P p).principalSymbol x ξ (δ a) +
              (Q (p + 1)).principalSymbol x ξ (d a)) = _ at he
          rw [show (metric (p + 1)).pairing x a _ =
              (metric (p + 1)).pairing x a ((P p).principalSymbol x ξ (δ a)) +
                (metric (p + 1)).pairing x a ((Q (p + 1)).principalSymbol x ξ (d a)) from
            InnerProductSpace.Core.inner_add_right _ _ _,
            show (metric (p + 1)).pairing x a 0 = 0 from
              InnerProductSpace.Core.inner_zero_right _] at he
          have hsym : (metric (p + 1)).pairing x a
              ((P p).principalSymbol x ξ (δ a)) =
                conj ((metric p).pairing x (δ a) (δ a)) := by
            rw [← hadj']
            exact ((metric (p + 1)).toCore x).conj_inner_symm _ _ |>.symm
          rw [hsym, ← hadj] at he
          have hre := congrArg Complex.re he
          simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hre
          have hd : d a = 0 := by
            by_contra hd
            have hpos := (metric (p + 2)).pairing_self_pos x (d a) hd
            have hnonneg := ((metric p).toCore x).re_inner_nonneg (δ a)
            change 0 ≤ ((metric p).pairing x (δ a) (δ a)).re at hnonneg
            linarith
          have hδ : δ a = 0 := by
            by_contra hδ
            have hpos := (metric p).pairing_self_pos x (δ a) hδ
            have hnonneg := ((metric (p + 2)).toCore x).re_inner_nonneg (d a)
            change 0 ≤ ((metric (p + 2)).pairing x (d a) (d a)).re at hnonneg
            linarith
          obtain ⟨b, hb⟩ := hsymbolExact p x ξ hξ a hd
          have hpair' := (P p).principalSymbol_metricFormalAdjoint_pairing
            (μ := g.riemannianVolume) (metric p) (metric (p + 1)) x ξ b a
          change (metric (p + 1)).pairing x ((P p).principalSymbol x ξ b) a =
            (metric p).pairing x b (δ a) at hpair'
          rw [hb, hδ] at hpair'
          apply ((metric (p + 1)).toCore x).definite a
          exact hpair'.trans (by
            let : InnerProductSpace.Core ℂ ((core p).Fiber x) := (metric p).toCore x
            exact InnerProductSpace.Core.inner_zero_right _)
    have hinj : Function.Injective ((S p).val x ξ) :=
      (LinearMap.ker_eq_bot).mp (LinearMap.ker_eq_bot'.mpr hzero)
    exact ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩
  -- Stage 7: the same homogeneous symbol supplies a two-sided smoothing parametrix.
  have hhomogeneous (p : ℕ) :
      IsHomogeneousGlobalSymbol (core p).Fiber (core p).Fiber m (S p).val := by
    have hd (j : ℕ) (x : M)
        (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
        (hξ : ξ ≠ 0) (t : ℝ) (ht : 0 < t) :
        (P j).principalSymbolFunction x (t • ξ) =
          (t : ℂ) • (P j).principalSymbolFunction x ξ := by
      simpa only [Nat.cast_one, Real.rpow_one] using
        (P j).isHomogeneousGlobalSymbol_principalSymbolFunction x ξ hξ t ht
    have hq (j : ℕ) (x : M)
        (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
        (hξ : ξ ≠ 0) (t : ℝ) (ht : 0 < t) :
        (Q j).principalSymbolFunction x (t • ξ) =
          (t : ℂ) • (Q j).principalSymbolFunction x ξ := by
      simpa only [Nat.cast_one, Real.rpow_one] using
        (Q j).isHomogeneousGlobalSymbol_principalSymbolFunction x ξ hξ t ht
    intro x ξ hξ t ht
    cases p with
    | zero =>
        change ((Q 0).principalSymbolFunction x (t • ξ)).comp
          ((P 0).principalSymbolFunction x (t • ξ)) =
            ((t ^ m : ℝ) : ℂ) •
              ((Q 0).principalSymbolFunction x ξ).comp ((P 0).principalSymbolFunction x ξ)
        rw [hd 0 x ξ hξ t ht, hq 0 x ξ hξ t ht]
        ext a
        simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
          smul_smul, m, Nat.cast_one, one_add_one_eq_two, Real.rpow_two,
          Complex.ofReal_mul, pow_two]
    | succ p =>
        change ((P p).principalSymbolFunction x (t • ξ)).comp
            ((Q p).principalSymbolFunction x (t • ξ)) +
          ((Q (p + 1)).principalSymbolFunction x (t • ξ)).comp
            ((P (p + 1)).principalSymbolFunction x (t • ξ)) =
          ((t ^ m : ℝ) : ℂ) •
            (((P p).principalSymbolFunction x ξ).comp ((Q p).principalSymbolFunction x ξ) +
              ((Q (p + 1)).principalSymbolFunction x ξ).comp
                ((P (p + 1)).principalSymbolFunction x ξ))
        rw [hd p x ξ hξ t ht, hq p x ξ hξ t ht,
          hd (p + 1) x ξ hξ t ht, hq (p + 1) x ξ hξ t ht]
        ext a
        simp only [ContinuousLinearMap.comp_apply, smul_apply,
          add_apply, map_smul, smul_smul, m, Nat.cast_one, one_add_one_eq_two, Real.rpow_two,
          Complex.ofReal_mul, pow_two, smul_add]
  have hadjoint (p : ℕ) : IsMetricFormalAdjoint (metric p) (metric p) g.riemannianVolume
      (L p).toLinearMap (L p).toLinearMap := by
    have hd (j : ℕ) : IsMetricFormalAdjoint (metric j) (metric (j + 1))
        g.riemannianVolume (P j).toLinearMap (Q j).toLinearMap :=
      (P j).isMetricFormalAdjoint_metricFormalAdjoint (metric j) (metric (j + 1))
    cases p with
    | zero =>
        exact IsMetricFormalAdjoint.comp (metric 0) (metric 1) g.riemannianVolume
          (metric 0) (hd 0) (hd 0).symm
    | succ p =>
        exact (IsMetricFormalAdjoint.comp (metric (p + 1)) (metric p) g.riemannianVolume
          (metric (p + 1)) (hd p).symm (hd p)).add
          (IsMetricFormalAdjoint.comp (metric (p + 1)) (metric (p + 2)) g.riemannianVolume
            (metric (p + 1)) (hd (p + 1)) (hd (p + 1)).symm)
  have hparametrix (p : ℕ) :
      ∃ R : PseudodifferentialOperator (n := n) (r := rank p) (q := rank p)
          (core p).Fiber (core p).Fiber g.riemannianVolume (-m),
        IsParametrix g.riemannianVolume (L p).toLinearMap R.toLinearMap := by
    obtain ⟨T⟩ := nonempty_quantizationPresentation (n := n) (r := rank p) (q := rank p)
      (E := (core p).Fiber) (F := (core p).Fiber)
    apply exists_parametrix_of_homogeneous_principalSymbol g.riemannianVolume T T
      (L p) (S p).val (S p).property.isSmoothOffZeroGlobalSymbol (hhomogeneous p)
      (helliptic p)
    rw [hLsymbol]
    exact (T.regularizedSymbol_class_eq (S p) (hhomogeneous p)).symm
  let B : SmoothFiniteComplexBundle (n := n) M :=
    { rank := rank degree
      Fiber := (core degree).Fiber }
  obtain ⟨R, hR⟩ := hparametrix degree
  exact ⟨B, sectionEquiv degree, metric degree, L degree, hpair degree,
    hL degree, hadjoint degree, R, hR⟩


end AtiyahSinger
