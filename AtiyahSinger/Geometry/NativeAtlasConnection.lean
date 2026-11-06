/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.NativeAtlasDifferentialOperator
public import AtiyahSinger.Geometry.AtlasComplexConnection
public import AtiyahSinger.Geometry.ComplexConnection

/-!
# The original native connection in its original atlas

Public module ID: M1304.

A01: over a Hausdorff smooth manifold, every supplied smooth complex native
connection admits local connection forms in the atlas of that same bundle.
Their d + Gamma action agrees with the
native connection on every original smooth section and tangent vector.
The section equivalence preserves all fiber values. This is the standard local
connection-form description underlying SG III.2, p.170, (2.1), not an assumption
that two independently selected higher-derivative families agree.

Only existence is asserted: coefficients outside valid chart domains have no
mathematical meaning and need not be unique. The theorem does not select a new
connection on the original bundle or alter its topology or smooth structure.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]

-- Preserve the original second-countability parameter; this local proof needs no use of it.
set_option linter.unusedSectionVars false in
include hT hSC in
/-- The given native complex connection has connection forms with the same original action. -/
theorem exists_atlasComplexConnection_native
    (covE : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℂ (Fin r)) E)
    (hcovE : CovariantDerivative.ContMDiffCovariantDerivative covE ∞)
    (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E covE) :
    letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∃ covA : AtlasComplexConnection (nativeSmoothComplexBundleAtlas (n := n) (r := r) E),
      ∀ (u : smoothSections (n := n) (r := r) E) (x : M)
        (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
        covA.covariantDerivative
          ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u) x v =
          covE u.val x v := by
  /- Stage 1: fix an original manifold chart and original native bundle frame.
  Apply covE to the local frame vectors using smooth supported extensions near
  each point. The native connection axioms give locality, so the resulting
  coefficients do not depend on the extension. Their tangent argument is real
  linear and hcomplex makes the fiber argument complex linear. The finite
  dimensional models give continuous linear maps in both arguments.
  Stage 2: subtract frame differentiation from covE. The real Leibniz terms
  cancel, so the difference is tensorial. Its values on the local constant
  frame sections and hcomplex identify a complex-linear fiber map. Its finite
  frame expansion gives the usual d + Gamma formula. Supported extensions
  and hcovE prove smoothness in the genuine native Hom/tangent coordinates.
  Total native chart functions merely give arbitrary values outside valid
  chart/frame domains. The section equivalence changes no fiber values.
  Stage 3: on chart overlaps both local expressions equal covE on the same
  original section and tangent vector. They therefore satisfy the atlas
  compatibility field. Its chosen-chart derivative consequently equals covE
  everywhere. The argument also covers rank zero and the empty base. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let H := EuclideanSpace ℝ (Fin n)
    let F := EuclideanSpace ℂ (Fin r)
    let := ComplexBundle.modelTopology F E
    let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
    let e (i : A.Index) := i.val
    let (i : A.Index) : MemTrivializationAtlas (e i) := i.property
    -- First compare the native derivative with differentiation in one original frame.
    let coordinates (i : A.Index) (σ : ∀ x, E x) (x : M) : F :=
      (e i).continuousLinearMapAt ℝ x (σ x)
    have hcoordinates (i : A.Index) (σ : ∀ x, E x) (x : M)
        (hx : x ∈ (e i).baseSet) :
        coordinates i σ =ᶠ[nhds x] (fun y ↦ (e i ⟨y, σ y⟩).2) := by
      filter_upwards [(e i).open_baseSet.mem_nhds hx] with y hy
      exact (e i).continuousLinearMapAt_apply_of_mem ℝ hy (σ y)
    have hcoordinateDiff (i : A.Index) (σ : ∀ x, E x) (x : M)
        (hx : x ∈ (e i).baseSet)
        (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
          (fun y ↦ (⟨y, σ y⟩ : TotalSpace F E)) x) :
        MDifferentiableAt I 𝓘(ℝ, F) (coordinates i σ) x :=
      (((e i).mdifferentiableAt_section_iff I σ hx).mp hσ).congr_of_eventuallyEq
        (hcoordinates i σ x hx)
    let flat (i : A.Index) (σ : ∀ x, E x) (x : M) : TangentSpace I x →L[ℝ] E x :=
      ((e i).symmL ℝ x).comp (mvfderiv I (coordinates i σ) x)
    have hflat (i : A.Index) : IsCovariantDerivativeOn F (flat i) (e i).baseSet := by
      constructor
      · intro σ τ x hσ hτ hx
        have hσc := hcoordinateDiff i σ x hx hσ
        have hτc := hcoordinateDiff i τ x hx hτ
        have hsum : coordinates i (σ + τ) = coordinates i σ + coordinates i τ := by
          funext y
          exact map_add ((e i).continuousLinearMapAt ℝ y) (σ y) (τ y)
        dsimp only [flat]
        rw [hsum, mvfderiv_add hσc hτc, ContinuousLinearMap.comp_add]
      · intro σ g x hσ hg hx
        have hσc := hcoordinateDiff i σ x hx hσ
        have hsmul : coordinates i (g • σ) = g • coordinates i σ := by
          funext y
          exact map_smul ((e i).continuousLinearMapAt ℝ y) (g y) (σ y)
        dsimp only [flat]
        rw [hsmul, mvfderiv_smul hg hσc]
        ext v
        simp only [ContinuousLinearMap.comp_apply, add_apply,
          smul_apply, ContinuousLinearMap.smulRight_apply,
          map_add, map_smul]
        change g x • (e i).symmL ℝ x (mvfderiv I (coordinates i σ) x v) +
          (e i).symmL ℝ x (mvfderiv I g x v • coordinates i σ x) = _
        rw [map_smul]
        change g x • (e i).symmL ℝ x (mvfderiv I (coordinates i σ) x v) +
          mvfderiv I g x v • (e i).symmL ℝ x
            ((e i).continuousLinearMapAt ℝ x (σ x)) = _
        rw [(e i).symmL_continuousLinearMapAt hx]
    -- The difference is tensorial on the original open frame domain.
    let difference (i : A.Index) (x : M) : E x →L[ℝ] TangentSpace I x →L[ℝ] E x :=
      (covE.isCovariantDerivativeOn (s := (e i).baseSet)).difference (hflat i) x
    have hdifference (i : A.Index) (σ : ∀ x, E x) (x : M)
        (hx : x ∈ (e i).baseSet)
        (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
          (fun y ↦ (⟨y, σ y⟩ : TotalSpace F E)) x) :
        difference i x (σ x) = covE σ x - flat i σ x := by
      exact IsCovariantDerivativeOn.difference_apply _ _ hx hσ
    let localSection (i : A.Index) (a : F) (x : M) : E x := (e i).symmL ℂ x a
    have hlocalCoordinates (i : A.Index) (a : F) (x : M)
        (hx : x ∈ (e i).baseSet) :
        coordinates i (localSection i a) =ᶠ[nhds x] (fun _ ↦ a) := by
      filter_upwards [(e i).open_baseSet.mem_nhds hx] with y hy
      dsimp only [coordinates, localSection]
      rw [(e i).symmL_apply hy,
        (e i).continuousLinearMapAt_apply_of_mem ℝ hy,
        (e i).apply_mk_symm hy]
    have hlocalSmooth (i : A.Index) (a : F) (x : M)
        (hx : x ∈ (e i).baseSet) :
        ContMDiffAt I (I.prod 𝓘(ℝ, F)) ∞
          (fun y ↦ (⟨y, localSection i a y⟩ : TotalSpace F E)) x := by
      apply ((e i).contMDiffAt_section_iff hx).mpr
      apply contMDiffAt_const.congr_of_eventuallyEq
      exact (hcoordinates i (localSection i a) x hx).symm.trans
        (hlocalCoordinates i a x hx)
    have hflatLocal (i : A.Index) (a : F) (x : M)
        (hx : x ∈ (e i).baseSet) : flat i (localSection i a) x = 0 := by
      dsimp only [flat]
      have hd := (hlocalCoordinates i a x hx).mfderiv_eq (I := I) (I' := 𝓘(ℝ, F))
      simp only [mvfderiv, hd, mfderiv_const, ContinuousLinearMap.comp_zero]
    have hdifferenceLocal (i : A.Index) (a : F) (x : M)
        (hx : x ∈ (e i).baseSet) :
        difference i x (localSection i a x) = covE (localSection i a) x := by
      rw [hdifference i (localSection i a) x hx
        ((hlocalSmooth i a x hx).mdifferentiableAt (by simp)), hflatLocal i a x hx,
        sub_zero]
    have hscalarMaps (i : A.Index) (x : M) (hx : x ∈ (e i).baseSet) (w : E x) :
        (e i).continuousLinearMapAt ℝ x w = (e i).continuousLinearMapAt ℂ x w :=
      ((e i).continuousLinearMapAt_apply_of_mem ℝ hx w).trans
        ((e i).continuousLinearMapAt_apply_of_mem ℂ hx w).symm
    have hcoordinateInverse (i : A.Index) (σ : ∀ x, E x) (x : M)
        (hx : x ∈ (e i).baseSet) :
        (e i).symmL ℂ x (coordinates i σ x) = σ x := by
      dsimp only [coordinates]
      rw [hscalarMaps i x hx, (e i).symmL_continuousLinearMapAt hx]
    -- Tensoriality and complex linearity identify the whole fiber map from its frame values.
    have hdifferenceComplex (i : A.Index) (x : M) (hx : x ∈ (e i).baseSet)
        (c : ℂ) (w : E x) : difference i x (c • w) = c • difference i x w := by
      let a := (e i).continuousLinearMapAt ℂ x w
      have ha : localSection i a x = w := (e i).symmL_continuousLinearMapAt hx w
      have hca : localSection i (c • a) = c • localSection i a := by
        funext y
        exact (e i).symmL ℂ y |>.map_smul c a
      have hcaValue : localSection i (c • a) x = c • w := by rw [hca, Pi.smul_apply, ha]
      rw [← hcaValue, hdifferenceLocal i (c • a) x hx, ← ha,
        hdifferenceLocal i a x hx]
      ext v
      rw [hca]
      exact hcomplex (localSection i a) x
        ((hlocalSmooth i a x hx).mdifferentiableAt (by simp)) (Set.mem_univ x) c v
    let fiberDifference (i : A.Index) (x : M) (hx : x ∈ (e i).baseSet) :
        F →ₗ[ℂ] (H →L[ℝ] F) := {
      toFun := fun a ↦ ((e i).continuousLinearMapAt ℂ x).restrictScalars ℝ |>.comp
        (difference i x ((e i).symmL ℂ x a))
      map_add' := by
        intro a b
        apply ContinuousLinearMap.ext
        intro v
        simp only [map_add, ContinuousLinearMap.comp_apply, add_apply]
      map_smul' := by
        intro c a
        apply ContinuousLinearMap.ext
        intro v
        change (e i).continuousLinearMapAt ℂ x
          (difference i x ((e i).symmL ℂ x (c • a)) v) =
            c • (e i).continuousLinearMapAt ℂ x
              (difference i x ((e i).symmL ℂ x a) v)
        rw [map_smul, hdifferenceComplex i x hx, smul_apply, map_smul] }
    let column (c : OpenPartialHomeomorph M H) (i : A.Index) (a : Fin r) (z : H) :
        H →L[ℝ] F :=
      ((e i).continuousLinearMapAt ℝ (c.symm z)).comp
        ((covE (localSection i (EuclideanSpace.single a 1)) (c.symm z)).comp
          (mfderiv I I c.symm z))
    let Γ (c : OpenPartialHomeomorph M H) (i : A.Index) (z : H) :
        H →L[ℝ] (F →L[ℂ] F) :=
      ∑ a : Fin r,
        ((ContinuousLinearMap.smulRightL ℂ F F (EuclideanSpace.proj a)).restrictScalars ℝ).comp
          (column c i a z)
    have hΓaction (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (i : A.Index) (σ : ∀ x, E x) (x : M)
        (hx : x ∈ c.source ∩ (e i).baseSet) (v : TangentSpace I x) :
        Γ c i (c x) (mfderiv I I c x v) (coordinates i σ x) =
          (e i).continuousLinearMapAt ℝ x (difference i x (σ x) v) := by
      let w : H := mfderiv I I c x v
      change Γ c i (c x) w (coordinates i σ x) = _
      let L := fiberDifference i x hx.2
      have hchart := mdifferentiable_of_mem_atlas (I := I) hc
      have hcolumn (a : Fin r) :
          column c i a (c x) w = L (EuclideanSpace.single a 1) v := by
        dsimp only [column]
        rw [c.left_inv hx.1]
        change (e i).continuousLinearMapAt ℝ x
          (covE (localSection i (EuclideanSpace.single a 1)) x
            (((mfderiv I I c.symm (c x)).comp (mfderiv I I c x)) v)) = _
        rw [hchart.symm_comp_deriv hx.1]
        change (e i).continuousLinearMapAt ℝ x
          (covE (localSection i (EuclideanSpace.single a 1)) x v) =
            (e i).continuousLinearMapAt ℂ x
              (difference i x (localSection i (EuclideanSpace.single a 1) x) v)
        rw [hdifferenceLocal i (EuclideanSpace.single a 1) x hx.2, hscalarMaps i x hx.2]
      have hsum := congrArg L ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr
        (coordinates i σ x))
      simp only [map_sum, map_smul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.basisFun_repr] at hsum
      have heval := congrArg (fun f : H →L[ℝ] F ↦ f v) hsum
      simp only [sum_apply, smul_apply] at heval
      dsimp only [Γ]
      simp only [sum_apply, ContinuousLinearMap.comp_apply]
      change (∑ a : Fin r, coordinates i σ x a •
        column c i a (c x) w) = _
      simp only [hcolumn]
      rw [heval]
      change (e i).continuousLinearMapAt ℂ x
        (difference i x ((e i).symmL ℂ x (coordinates i σ x)) v) = _
      rw [hcoordinateInverse i σ x hx.2, hscalarMaps i x hx.2]
    -- Local frame vectors may be globalized near a point under the original T2 hypothesis.
    have hlocalCovSmooth (i : A.Index) (a : F) (x : M)
        (hx : x ∈ (e i).baseSet) :
        ContMDiffAt I (I.prod 𝓘(ℝ, H →L[ℝ] F)) ∞
          (fun y ↦ (⟨y, covE (localSection i a) y⟩ :
            TotalSpace (H →L[ℝ] F) (fun z ↦ TangentSpace I z →L[ℝ] E z))) x := by
      obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
        ((e i).open_baseSet.mem_nhds hx)
      let σ := (ψ : M → ℝ) • localSection i a
      have hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
          (fun y ↦ (⟨y, σ y⟩ : TotalSpace F E)) := by
        exact ContMDiffOn.smul_section_of_tsupport ψ.contMDiff.contMDiffOn
          (e i).open_baseSet hψ (fun y hy ↦ (hlocalSmooth i a y hy).contMDiffWithinAt)
      have houtput := hcovE.contMDiff.contMDiff (by simpa using hσ.contMDiffOn)
      have houtputAt := (contMDiffOn_univ.mp houtput).contMDiffAt (x := x)
      apply houtputAt.congr_of_eventuallyEq
      filter_upwards [ψ.eventuallyEq_one.eventually_nhds, (e i).open_baseSet.mem_nhds hx]
        with y hψy hy
      congr 1
      apply (covE.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq
        ((hlocalSmooth i a y hy).mdifferentiableAt (by simp))
        (hσ.mdifferentiableAt (by simp)) Filter.univ_mem
      filter_upwards [hψy] with z hz
      change localSection i a z = (ψ : M → ℝ) z • localSection i a z
      rw [show (ψ : M → ℝ) z = 1 from hz, one_smul]
    have hcolumnSmooth (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (i : A.Index) (a : Fin r) (z : H)
        (hz : z ∈ c.target ∩ c.symm ⁻¹' (e i).baseSet) :
        ContDiffAt ℝ ∞ (column c i a) z := by
      let x := c.symm z
      let e₀ := trivializationAt F E x
      let t₀ := trivializationAt H (TangentSpace I) x
      have he₀ : x ∈ e₀.baseSet := mem_baseSet_trivializationAt F E x
      have ht₀ : x ∈ t₀.baseSet := mem_baseSet_trivializationAt H (TangentSpace I) x
      have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
        (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1
      have hout := ((contMDiffAt_hom_bundle _).mp
        (hlocalCovSmooth i (EuclideanSpace.single a 1) x hz.2)).2
      have hchange := contMDiffAt_coordChangeL (IB := I) (n := ∞) he₀ hz.2
      have hderivative := hsymm.mfderiv_const (m := ∞) (by simp)
      have hproduct := (hchange.comp z hsymm).clm_comp
        ((hout.comp z hsymm).clm_comp hderivative)
      apply (contMDiffAt_iff_contDiffAt.mp hproduct).congr_of_eventuallyEq
      have hnear := hsymm.continuousAt.preimage_mem_nhds
        (((e₀.open_baseSet.inter t₀.open_baseSet).inter (e i).open_baseSet).mem_nhds
          ⟨⟨he₀, ht₀⟩, hz.2⟩)
      filter_upwards [hnear] with w hw
      apply ContinuousLinearMap.ext
      intro v
      simp only [column, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
        TangentBundle.symmL_model_space, Function.comp_def]
      change (e i).continuousLinearMapAt ℝ (c.symm w)
        (covE (localSection i (EuclideanSpace.single a 1)) (c.symm w)
          (mfderiv I I c.symm w v)) =
            e₀.coordChangeL ℝ (e i) (c.symm w)
              (e₀.continuousLinearMapAt ℝ (c.symm w)
                (covE (localSection i (EuclideanSpace.single a 1)) (c.symm w)
                  (t₀.symmL ℝ (c.symm w) (t₀.continuousLinearMapAt ℝ (c.symm w)
                    (mfderiv I I c.symm w v)))))
      rw [t₀.symmL_continuousLinearMapAt hw.1.2]
      rw [e₀.coordChangeL_apply (e i) ⟨hw.1.1, hw.2⟩]
      rw [(e i).continuousLinearMapAt_apply_of_mem ℝ hw.2,
        e₀.continuousLinearMapAt_apply_of_mem ℝ hw.1.1,
        e₀.symm_apply_apply_mk hw.1.1]
    have hΓsmooth (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (i : A.Index) :
        ContDiffOn ℝ ∞ (Γ c i) (c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) := by
      intro z hz
      have hs : ContDiffAt ℝ ∞ (Γ c i) z := by
        apply ContDiffAt.sum
        intro a _
        exact contDiffAt_const.clm_comp (hcolumnSmooth c hc i a z hz)
      exact hs.contDiffWithinAt
    -- The identity section equivalence gives the same native smooth section and first jet.
    have hnativeSmooth (u : A.smoothSections) :
        ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
          (fun y ↦ (⟨y, u.val y⟩ : TotalSpace F E)) := by
      intro x
      let t := trivializationAt F E x
      have ht : x ∈ t.baseSet := mem_baseSet_trivializationAt F E x
      have hu := (isSmoothSection_nativeSmoothComplexBundleAtlas_iff
        (n := n) (r := r) E u.val).mp u.property
      exact (t.contMDiffAt_section_iff ht).mpr
        ((hu t inferInstance).contMDiffAt (t.open_baseSet.mem_nhds ht))
    have hatlasCoordinates (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (i : A.Index) (u : A.smoothSections) (x : M)
        (hx : x ∈ c.source ∩ (e i).baseSet) :
        atlasSectionInChart A c i u.val =ᶠ[nhds (c x)]
          (fun z ↦ coordinates i u.val (c.symm z)) := by
      have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
        (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) (c.map_source hx.1)
      have hnear := hsymm.continuousAt.preimage_mem_nhds (by
        rw [c.left_inv hx.1]
        exact (e i).open_baseSet.mem_nhds hx.2)
      filter_upwards [hnear] with z hz
      change (e i ⟨c.symm z, u.val (c.symm z)⟩).2 =
        (e i).continuousLinearMapAt ℝ (c.symm z) (u.val (c.symm z))
      exact ((e i).continuousLinearMapAt_apply_of_mem ℝ hz _).symm
    have hchartDerivative (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (i : A.Index) (u : A.smoothSections) (x : M)
        (hx : x ∈ c.source ∩ (e i).baseSet) (v : TangentSpace I x) :
        fderiv ℝ (atlasSectionInChart A c i u.val) (c x) (mfderiv I I c x v) =
          mvfderiv I (coordinates i u.val) x v := by
      have hu := hcoordinateDiff i u.val x hx.2
        ((hnativeSmooth u).mdifferentiableAt (by simp))
      have hchart := mdifferentiable_of_mem_atlas (I := I) hc
      have hc' := hchart.mdifferentiableAt_symm (c.map_source hx.1)
      have hchain := mvfderiv_comp (I := I) (I' := I) (c x)
        (by simpa only [c.left_inv hx.1] using hu) hc'
      have hlocal : fderiv ℝ (atlasSectionInChart A c i u.val) (c x) =
          (mvfderiv I (coordinates i u.val) x).comp (mfderiv I I c.symm (c x)) := by
        rw [(hatlasCoordinates c hc i u x hx).fderiv_eq]
        dsimp only [I] at hchain
        rw [mvfderiv_eq_fderiv, c.left_inv hx.1] at hchain
        exact hchain
      rw [hlocal]
      change (mvfderiv I (coordinates i u.val) x)
        (((mfderiv I I c.symm (c x)).comp (mfderiv I I c x)) v) = _
      rw [hchart.symm_comp_deriv hx.1]
      rfl
    -- The local formula is the supplied connection, so all overlap comparisons share it.
    have hexpression (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (i : A.Index) (u : A.smoothSections) (x : M)
        (hx : x ∈ c.source ∩ (A.chart i).baseSet) (v : TangentSpace I x) :
        atlasConnectionExpression A c i (Γ c i) u x hx.2 v = covE u.val x v := by
      have hvalue : atlasSectionInChart A c i u.val (c x) = coordinates i u.val x := by
        simpa only [c.left_inv hx.1] using
          (hatlasCoordinates c hc i u x hx).self_of_nhds
      have hd : (e i).continuousLinearMapAt ℝ x (difference i x (u.val x) v) =
          (e i).continuousLinearMapAt ℝ x (covE u.val x v) -
            mvfderiv I (coordinates i u.val) x v := by
        rw [hdifference i u.val x hx.2 ((hnativeSmooth u).mdifferentiableAt (by simp)),
          sub_apply, map_sub]
        change _ - (e i).continuousLinearMapAt ℝ x
          ((e i).symmL ℝ x (mvfderiv I (coordinates i u.val) x v)) = _
        rw [(e i).continuousLinearMapAt_symmL hx.2]
      let du : F := fderiv ℝ (atlasSectionInChart A c i u.val) (c x) (mfderiv I I c x v)
      let correction : F := Γ c i (c x) (mfderiv I I c x v)
        (atlasSectionInChart A c i u.val (c x))
      have hdu : du = mvfderiv I (coordinates i u.val) x v :=
        hchartDerivative c hc i u x hx v
      have hcorrection : correction =
          (e i).continuousLinearMapAt ℝ x (difference i x (u.val x) v) := by
        dsimp only [correction]
        rw [hvalue]
        exact hΓaction c hc i u.val x hx v
      apply (A.frameLinearEquiv i x hx.2).injective
      rw [atlasConnectionExpression, LinearEquiv.apply_symm_apply]
      change (EuclideanSpace.equiv (Fin r) ℂ) (du + correction) =
        (EuclideanSpace.equiv (Fin r) ℂ) (e i ⟨x, covE u.val x v⟩).2
      rw [hdu, hcorrection,
        ← (e i).continuousLinearMapAt_apply_of_mem ℝ hx.2]
      apply congrArg (EuclideanSpace.equiv (Fin r) ℂ)
      rw [hd]
      abel
    let covA : AtlasComplexConnection A := {
      connectionForm := Γ
      smooth_connectionForm := hΓsmooth
      compatible := by
        intro c d hc hd i j u x hx hy v
        exact (hexpression c hc i u x hx v).trans (hexpression d hd j u x hy v).symm }
    refine ⟨covA, ?_⟩
    intro u x v
    exact hexpression (chartAt H x) (chart_mem_atlas H x) (Classical.choose (A.covers x))
      ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u) x
      ⟨mem_chart_source H x, Classical.choose_spec (A.covers x)⟩ v

end AtiyahSinger
