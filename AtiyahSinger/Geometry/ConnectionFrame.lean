/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ConnectionExistence
public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Geometry.SmoothBundlePullback
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# The flat covariant derivative in a specified complex frame

Public module ID: M1142.

E01: the actual coordinate derivative in the supplied smooth frame on an
open submanifold. The frame, its original fiber inverse and the inherited
open-submanifold atlas determine the formula. The value outside that open
set is zero only to totalize the function; connection laws are asserted on
the open set. The relative existence theorem can then retain this same
formula on a closed exterior region, as required by SG III.13.3, p.246.

This is the usual frame-flat connection, not a chosen Hermitian connection.
An arbitrary specified frame need not be orthonormal for a specified metric.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (U : Opens M) (frame : ∀ x : U, E x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r))

/-- Differentiate in the specified open frame and return through the original inverse frame.
The tangent carriers on the open submanifold and ambient manifold use the same model. -/
def frameCovariantDerivative (s : ∀ x : M, E x) (x : M) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] E x := by
  classical
  exact if hx : x ∈ U then
    (((frame ⟨x, hx⟩).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin r))
        (fun y : U ↦ frame y (s y.val)) ⟨x, hx⟩)
  else 0

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

include hM hE

/-- The actual frame derivative is a smooth complex connection on its given open domain. -/
theorem frameCovariantDerivative_properties
    (hframe : IsSmoothBundleMap (n := n) (r := r) (q := r) (M := U)
      (E := (ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
      (F := Bundle.Trivial U (EuclideanSpace ℂ (Fin r)))
      (fun x ↦ (frame x).toLinearMap)) :
    IsCovariantDerivativeOn (EuclideanSpace ℂ (Fin r))
        (frameCovariantDerivative (n := n) (r := r) E U frame) (U : Set M) ∧
      ContMDiffCovariantDerivativeOn (EuclideanSpace ℂ (Fin r)) ∞
        (frameCovariantDerivative (n := n) (r := r) E U frame) (U : Set M) ∧
      IsComplexLinearConnectionOn (n := n) (r := r) E
        (frameCovariantDerivative (n := n) (r := r) E U frame) (U : Set M) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let F := EuclideanSpace ℂ (Fin r)
  let incl : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  have hinv := IsSmoothBundleMap.symm (n := n) (r := r) (q := r) (M := U)
    (E := (incl : U → M) *ᵖ E) (F := Bundle.Trivial U F) frame hframe
  let (x : M) : FiniteDimensional ℂ (E x) := VectorBundle.finiteDimensional ℂ F E x
  let e (b : M) := trivializationAt F E b
  let t := Bundle.Trivial.trivialization U F
  let : MemTrivializationAtlas t := ⟨rfl⟩
  let L (b : M) (y : U) : F →L[ℂ] F :=
    (frame y).toContinuousLinearEquiv.toContinuousLinearMap.comp ((e b).symmL ℂ y.val)
  let R (b : M) (y : U) : F →L[ℂ] F :=
    ((e b).continuousLinearMapAt ℂ y.val).comp
      (frame y).symm.toContinuousLinearEquiv.toContinuousLinearMap
  -- The original smooth frame and its inverse give smooth coordinate operator families.
  have hL (b : M) : ContMDiffOn I 𝓘(ℝ, F →L[ℂ] F) ∞ (L b)
      (Subtype.val ⁻¹' (e b).baseSet) := by
    let : MemTrivializationAtlas ((e b).pullback incl) :=
      ⟨⟨e b, inferInstance, rfl⟩⟩
    have hc (j : Fin r) := hframe ((e b).pullback incl) t j
    have hsum : ContMDiffOn I 𝓘(ℝ, F →L[ℂ] F) ∞
        (fun y : U ↦ ∑ j : Fin r,
          ContinuousLinearMap.smulRightL ℂ F F (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) j)
            (frame y ((e b).symmL ℂ y.val (EuclideanSpace.single j 1))))
        (Subtype.val ⁻¹' (e b).baseSet) := by
      apply contMDiffOn_finsetSum
      intro j _
      have hj : ContMDiffOn I 𝓘(ℝ, F) ∞
          (fun y : U ↦ frame y ((e b).symmL ℂ y.val (EuclideanSpace.single j 1)))
          (Subtype.val ⁻¹' (e b).baseSet) := by
        have hj := hc j
        simp only [t, Bundle.Trivial.trivialization_baseSet, Set.inter_univ,
          Bundle.Trivialization.pullback_baseSet] at hj
        apply hj.congr
        intro y hy
        change frame y ((e b).symmL ℂ y.val (EuclideanSpace.single j 1)) =
          frame y (((e b).pullback incl).symmL ℂ y (EuclideanSpace.single j 1))
        erw [(e b).symmL_apply (show y.val ∈ (e b).baseSet from hy),
          ((e b).pullback incl).symmL_apply hy]
        simp [Trivialization.symm_apply, hy, incl, Trivialization.pullback]
        rfl
      exact ((ContinuousLinearMap.smulRightL ℂ F F
        (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) j)).restrictScalars ℝ).contMDiff.comp_contMDiffOn hj
    apply hsum.congr
    intro y hy
    apply ContinuousLinearMap.ext
    intro v
    have hexpand := congrArg (L b y) ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr v)
    simpa [L, map_sum, map_smul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, PiLp.proj_apply] using! hexpand.symm
  have hR (b : M) : ContMDiffOn I 𝓘(ℝ, F →L[ℂ] F) ∞ (R b)
      (Subtype.val ⁻¹' (e b).baseSet) := by
    let : MemTrivializationAtlas ((e b).pullback incl) :=
      ⟨⟨e b, inferInstance, rfl⟩⟩
    have hc (j : Fin r) := hinv t ((e b).pullback incl) j
    have hsum : ContMDiffOn I 𝓘(ℝ, F →L[ℂ] F) ∞
        (fun y : U ↦ ∑ j : Fin r,
          ContinuousLinearMap.smulRightL ℂ F F (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) j)
            ((e b).continuousLinearMapAt ℂ y.val
              ((frame y).symm (EuclideanSpace.single j 1))))
        (Subtype.val ⁻¹' (e b).baseSet) := by
      apply contMDiffOn_finsetSum
      intro j _
      have hj : ContMDiffOn I 𝓘(ℝ, F) ∞
          (fun y : U ↦ (e b).continuousLinearMapAt ℂ y.val
            ((frame y).symm (EuclideanSpace.single j 1)))
          (Subtype.val ⁻¹' (e b).baseSet) := by
        have hj := hc j
        simp only [t, Bundle.Trivial.trivialization_baseSet, Set.univ_inter,
          Bundle.Trivialization.pullback_baseSet] at hj
        apply hj.congr
        intro y hy
        erw [(e b).continuousLinearMapAt_apply_of_mem ℂ
          (show y.val ∈ (e b).baseSet from hy)]
        simp only [Bundle.Trivial.trivialization_baseSet, Set.mem_univ,
          Trivialization.symmL_apply, LinearEquiv.coe_coe, Trivialization.pullback_apply]
        congr 3
        exact congrArg (frame y).symm
          (Bundle.Trivial.trivialization_symm_apply U F y (EuclideanSpace.single j 1)).symm
      exact ((ContinuousLinearMap.smulRightL ℂ F F
        (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) j)).restrictScalars ℝ).contMDiff.comp_contMDiffOn hj
    apply hsum.congr
    intro y hy
    apply ContinuousLinearMap.ext
    intro v
    have hexpand := congrArg (R b y) ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr v)
    simpa [R, map_sum, map_smul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, PiLp.proj_apply] using! hexpand.symm
  -- Extend coordinate functions only to express the same local derivative ambiently.
  let coordinates (σ : ∀ x, E x) (x : M) : F :=
    if hx : x ∈ U then frame ⟨x, hx⟩ (σ x) else 0
  have hcoordEq (b : M) (σ : ∀ x, E x) (y : U) (hy : y.val ∈ (e b).baseSet) :
      coordinates σ y.val = (L b y) (e b ⟨y.val, σ y.val⟩).2 := by
    simp only [coordinates, y.property, dite_eq_left, L, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    rw [(e b).symmL_apply hy, (e b).symm_apply_apply_mk hy]
    rfl
  have hcoordDiff (σ : ∀ x, E x) (x : M) (hx : x ∈ U)
      (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
        (fun y ↦ (⟨y, σ y⟩ : TotalSpace F E)) x) :
      MDifferentiableAt I 𝓘(ℝ, F) (coordinates σ) x := by
    let y : U := ⟨x, hx⟩
    have he : x ∈ (e x).baseSet := mem_baseSet_trivializationAt F E x
    have hLx := (hL x).contMDiffAt (x := y)
      (((e x).open_baseSet.preimage continuous_subtype_val).mem_nhds he)
    have hLreal := (ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ).contMDiff.contMDiffAt.comp
      y hLx
    have hσc := ((e x).mdifferentiableAt_section_iff I σ he).mp hσ
    have hσU := hσc.comp y
      ((contMDiff_subtype_val (n := (∞ : WithTop ℕ∞))).mdifferentiableAt (by simp))
    have hprod := (hLreal.mdifferentiableAt (by simp)).clm_apply hσU
    have hcoordU : MDifferentiableAt I 𝓘(ℝ, F)
        (fun z : U ↦ coordinates σ z.val) y := by
      apply hprod.congr_of_eventuallyEq
      filter_upwards [((e x).open_baseSet.preimage continuous_subtype_val).mem_nhds
        (show y ∈ Subtype.val ⁻¹' (e x).baseSet from he)]
        with z hz
      exact hcoordEq x σ z hz
    have hlocal := differentiableWithinAt_localInvariantProp (I := I) (I' := 𝓘(ℝ, F))
    exact (hlocal.liftPropAt_iff_comp_subtype_val (coordinates σ) y).mpr hcoordU
  have hcoordSmooth (σ : ∀ x, E x) (x : M) (hx : x ∈ U)
      (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) ∞
        (fun y ↦ (⟨y, σ y⟩ : TotalSpace F E)) x) :
      ContMDiffAt I 𝓘(ℝ, F) ∞ (coordinates σ) x := by
    let y : U := ⟨x, hx⟩
    have he : x ∈ (e x).baseSet := mem_baseSet_trivializationAt F E x
    have hLx := (hL x).contMDiffAt (x := y)
      (((e x).open_baseSet.preimage continuous_subtype_val).mem_nhds he)
    have hLreal := (ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ).contMDiff.contMDiffAt.comp
      y hLx
    have hσc := ((e x).contMDiffAt_section_iff he).mp hσ
    have hσU := hσc.comp y contMDiff_subtype_val.contMDiffAt
    have hprod := hLreal.clm_apply hσU
    apply (contMDiffAt_subtype_iff (x := y)).mp
    apply hprod.congr_of_eventuallyEq
    filter_upwards [((e x).open_baseSet.preimage continuous_subtype_val).mem_nhds
        (show y ∈ Subtype.val ⁻¹' (e x).baseSet from he)]
      with z hz
    exact hcoordEq x σ z hz
  -- Restriction to the inherited open atlas preserves the model tangent derivative.
  have hrestrict (f : M → F) (x : U)
      (hf : MDifferentiableAt I 𝓘(ℝ, F) f x.val) :
      mfderiv I 𝓘(ℝ, F) (fun y : U ↦ f y.val) x =
        mfderiv I 𝓘(ℝ, F) f x.val := by
    have hfU : MDifferentiableAt I 𝓘(ℝ, F) (fun y : U ↦ f y.val) x :=
      hf.comp x ((contMDiff_subtype_val (n := (∞ : WithTop ℕ∞))).mdifferentiableAt
        (by simp))
    rw [hfU.mfderiv_abuse, hf.mfderiv_abuse]
    have heq := (U.chartAt_subtype_val_symm_eventuallyEq
      (H := EuclideanSpace ℝ (Fin n)) (x := x)).fun_comp f
    simpa [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, I,
      Function.comp_def] using!
      (heq.symm.fderivWithin_eq_of_nhds (𝕜 := ℝ) (s := Set.univ))
  let inverseFrame (x : U) : F →L[ℝ] E x.val :=
    (frame x).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hformula (σ : ∀ x, E x) (x : M) (hx : x ∈ U)
      (hσ : MDifferentiableAt I 𝓘(ℝ, F) (coordinates σ) x) :
      frameCovariantDerivative (n := n) (r := r) E U frame σ x =
        (inverseFrame ⟨x, hx⟩).comp (mvfderiv I (coordinates σ) x) := by
    have hcoordU : (fun y : U ↦ frame y (σ y.val)) =
        (fun y : U ↦ coordinates σ y.val) := by
      funext y
      simp [coordinates, y.property]
    simp only [frameCovariantDerivative, hx, dite_eq_left]
    rw [hcoordU, hrestrict (coordinates σ) ⟨x, hx⟩ hσ]
    rfl
  have hadd (σ τ : ∀ x, E x) :
      coordinates (σ + τ) = coordinates σ + coordinates τ := by
    funext x
    by_cases hx : x ∈ U
    · simp [coordinates, hx, map_add]
    · simp [coordinates, hx]
  have hsmul (g : M → ℝ) (σ : ∀ x, E x) :
      coordinates (g • σ) = g • coordinates σ := by
    funext x
    by_cases hx : x ∈ U
    · change (if h : x ∈ U then frame ⟨x, h⟩ (g x • σ x) else 0) =
          g x • (if h : x ∈ U then frame ⟨x, h⟩ (σ x) else 0)
      simp only [hx, dite_eq_left]
      exact ((frame ⟨x, hx⟩).restrictScalars ℝ).map_smul (g x) (σ x)
    · simp [coordinates, hx]
  have hinverse (σ : ∀ x, E x) (x : M) (hx : x ∈ U) :
      inverseFrame ⟨x, hx⟩ (coordinates σ x) = σ x := by
    simp [inverseFrame, coordinates, hx]
  -- The model derivative supplies additivity and the real Leibniz rule.
  have hcov : IsCovariantDerivativeOn F
      (frameCovariantDerivative (n := n) (r := r) E U frame) (U : Set M) := by
    constructor
    · intro σ τ x hσ hτ hx
      have hσd := hcoordDiff σ x hx hσ
      have hτd := hcoordDiff τ x hx hτ
      have hsum : MDifferentiableAt I 𝓘(ℝ, F) (coordinates (σ + τ)) x := by
        rw [hadd]
        exact hσd.add hτd
      rw [hformula _ _ hx hsum, hformula _ _ hx hσd, hformula _ _ hx hτd,
        hadd, mvfderiv_add hσd hτd, ContinuousLinearMap.comp_add]
    · intro σ g x hσ hg hx
      have hσd := hcoordDiff σ x hx hσ
      have hproduct : MDifferentiableAt I 𝓘(ℝ, F) (coordinates (g • σ)) x := by
        rw [hsmul]
        exact hg.smul hσd
      rw [hformula _ _ hx hproduct, hformula _ _ hx hσd, hsmul,
        mvfderiv_smul hg hσd]
      ext v
      simp only [ContinuousLinearMap.comp_apply, add_apply,
        smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul]
      rw [hinverse σ x hx]
  refine ⟨hcov, ?_, ?_⟩
  · -- Smoothness is tested in the existing Hom-bundle atlas on the ambient manifold.
    constructor
    intro σ hσ x hx
    simp only [show (∞ : WithTop ℕ∞) + 1 = ∞ by simp] at hσ
    have hσx := (hσ x hx).contMDiffAt (U.isOpen.mem_nhds hx)
    have hσc := hcoordSmooth σ x hx hσx
    have hd := hσc.mfderiv_const (m := ∞) (by simp)
    let Rbar (z : M) : F →L[ℝ] F :=
      if hz : z ∈ U then (R x ⟨z, hz⟩).restrictScalars ℝ else 0
    have he : x ∈ (e x).baseSet := mem_baseSet_trivializationAt F E x
    have hRx := (hR x).contMDiffAt (x := (⟨x, hx⟩ : U))
      (((e x).open_baseSet.preimage continuous_subtype_val).mem_nhds he)
    have hRreal := (ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ).contMDiff.contMDiffAt.comp
      (⟨x, hx⟩ : U) hRx
    have hRbar : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) ∞ Rbar x := by
      apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
      simpa [Rbar] using! hRreal
    have hh := hRbar.clm_comp hd
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_hom_bundle _).mpr
    refine ⟨contMDiffAt_id, ?_⟩
    apply hh.congr_of_eventuallyEq
    filter_upwards [U.isOpen.mem_nhds hx, (e x).open_baseSet.mem_nhds he]
      with y hy hey
    have hσy := (hσ y hy).contMDiffAt (U.isOpen.mem_nhds hy)
    rw [hformula σ y hy (hcoordDiff σ y hy (hσy.mdifferentiableAt (by simp)))]
    have hRbarY : Rbar y = (R x ⟨y, hy⟩).restrictScalars ℝ := by
      dsimp only [Rbar]
      simp only [show y ∈ U from hy, dite_eq_left]
    rw [hRbarY]
    apply ContinuousLinearMap.ext
    intro v
    simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply]
    erw [(e x).continuousLinearMapAt_apply_of_mem ℝ hey]
    simp only [R]
    erw [(e x).continuousLinearMapAt_apply_of_mem ℂ hey]
    simp [inverseFrame, TangentBundle.continuousLinearMapAt_model_space,
      mvfderiv, NormedSpace.fromTangentSpace, tangentSpaceCastModel]
    rfl
  · -- A fixed complex scalar is a real continuous linear map on the coordinate model.
    intro σ x hσ hx c v
    have hσd := hcoordDiff σ x hx hσ
    let C : F →L[ℝ] F := (c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ
    have hcoordC : coordinates (fun y ↦ c • σ y) = C ∘ coordinates σ := by
      funext y
      by_cases hy : y ∈ U
      · simp [coordinates, hy, C, map_smul]
      · simp [coordinates, hy, C]
    have hCd : MDifferentiableAt I 𝓘(ℝ, F)
        (coordinates (fun y ↦ c • σ y)) x := by
      rw [hcoordC]
      exact C.mdifferentiableAt.comp x hσd
    rw [hformula _ _ hx hCd, hformula _ _ hx hσd, hcoordC,
      mvfderiv_comp x C.mdifferentiableAt hσd]
    have hCderiv : mvfderiv 𝓘(ℝ, F) C (coordinates σ x) = C := by
      rw [mvfderiv_eq_fderiv, C.fderiv]
      rfl
    rw [hCderiv]
    change (frame ⟨x, hx⟩).symm (c • (mvfderiv I (coordinates σ) x v)) =
      c • (frame ⟨x, hx⟩).symm (mvfderiv I (coordinates σ) x v)
    exact (frame ⟨x, hx⟩).symm.map_smul c _

end AtiyahSinger
