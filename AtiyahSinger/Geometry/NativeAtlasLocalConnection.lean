/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.NativeAtlasConnection
public import AtiyahSinger.Geometry.SmoothSectionEvaluation

/-!
# Local consequences of the original atlas/native connection comparison

Public module ID: M1305.

On a Hausdorff smooth manifold, the difference of two connections is tensorial.
Global smooth sections realize
every original fiber value, so testing this difference on those sections also
determines its value on any section differentiable at the point. This supplies
the local connection comparison required by the covariant tensor recursion.
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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

local notation "MI" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "TM" => TangentSpace MI (M := M)
local notation "VF" => EuclideanSpace ℂ (Fin r)

/-- Local connections agreeing on global smooth sections agree on every differentiable germ.
Tensoriality of their difference requires only a smooth section with the same value. -/
theorem connection_eq_of_eq_smoothSections
    (D D' : (∀ x : M, E x) → ∀ x : M, TM x →L[ℝ] E x) (s : Set M)
    (hD : IsCovariantDerivativeOn VF D s) (hD' : IsCovariantDerivativeOn VF D' s)
    (hs : ∀ (u : smoothSections (n := n) (r := r) E) (x : M), x ∈ s →
      D u.val x = D' u.val x)
    (σ : ∀ x : M, E x) (x : M) (hx : x ∈ s)
    (hσ : MDifferentiableAt MI ((MI).prod 𝓘(ℝ, VF))
      (fun y ↦ (⟨y, σ y⟩ : TotalSpace VF E)) x) : D σ x = D' σ x := by
  obtain ⟨u, hu⟩ := exists_smoothSection_apply_eq (n := n) (r := r) x (σ x)
  let e := trivializationAt VF E x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt VF E x
  have husmooth : ContMDiffAt MI ((MI).prod 𝓘(ℝ, VF)) ∞
      (fun y ↦ (⟨y, u.val y⟩ : TotalSpace VF E)) x :=
    (e.contMDiffAt_section_iff he).mpr
      ((u.property e inferInstance).contMDiffAt (e.open_baseSet.mem_nhds he))
  -- The same difference map evaluates σ and u through the common original fiber value.
  have hdiffσ := IsCovariantDerivativeOn.difference_apply hD hD' hx hσ
  have hdiffu := IsCovariantDerivativeOn.difference_apply hD hD' hx
    (husmooth.mdifferentiableAt (by simp))
  rw [hu, hs u x hx, sub_self] at hdiffu
  exact sub_eq_zero.mp (hdiffσ.symm.trans hdiffu)

set_option backward.isDefEq.respectTransparency false in
/-- The prescribed native/atlas agreement gives the local formula on any differentiable section.
The frame and the base-chart derivative are exactly those of the supplied atlas. -/
theorem nativeConnection_eq_atlasExpression
    (covE : CovariantDerivative MI VF E) :
    letI := ComplexBundle.modelTopology VF E
    let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
    ∀ covA : AtlasComplexConnection A,
      (∀ (u : smoothSections (n := n) (r := r) E) (x : M) (v : TM x),
        covA.covariantDerivative
          ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u) x v =
            covE u.val x v) →
      ∀ (σ : ∀ x : M, E x) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (_hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index)
        (x : M) (hx : x ∈ c.source ∩ (A.chart i).baseSet),
        MDifferentiableAt MI ((MI).prod 𝓘(ℝ, VF))
          (fun y ↦ (⟨y, σ y⟩ : TotalSpace VF E)) x → ∀ v : TM x,
        covE σ x v = (A.frameLinearEquiv i x hx.2).symm
          ((EuclideanSpace.equiv (Fin r) ℂ)
            (fderiv ℝ (atlasSectionInChart A c i σ) (c x) (mfderiv MI MI c x v) +
              covA.connectionForm c i (c x) (mfderiv MI MI c x v)
                (atlasSectionInChart A c i σ (c x)))) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let H := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℂ (Fin r)
  let := ComplexBundle.modelTopology F E
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let e (i : A.Index) := i.val
  let (i : A.Index) : MemTrivializationAtlas (e i) := i.property
  change ∀ covA : AtlasComplexConnection A, _
  intro covA hA σ c hc i x hx hσ v
  change A.Index at i
  change x ∈ c.source ∩ (A.chart i).baseSet at hx
  let Γ : F →L[ℂ] F := covA.connectionForm c i (c x) (mfderiv I I c x v)
  change covE σ x v = (A.frameLinearEquiv i x hx.2).symm
    ((EuclideanSpace.equiv (Fin r) ℂ)
      (fderiv ℝ (atlasSectionInChart A c i σ) (c x) (mfderiv I I c x v) +
        covA.connectionForm c i (c x) (mfderiv I I c x v)
          (atlasSectionInChart A c i σ (c x))))
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
  have hatlasCoordinates (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
      (i : A.Index) (τ : ∀ x : M, E x) (x : M)
      (hx : x ∈ c.source ∩ (e i).baseSet) :
      atlasSectionInChart A c i τ =ᶠ[nhds (c x)]
        (fun z ↦ coordinates i τ (c.symm z)) := by
    have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
      (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) (c.map_source hx.1)
    have hnear := hsymm.continuousAt.preimage_mem_nhds (by
      rw [c.left_inv hx.1]
      exact (e i).open_baseSet.mem_nhds hx.2)
    filter_upwards [hnear] with z hz
    change (e i ⟨c.symm z, τ (c.symm z)⟩).2 =
      (e i).continuousLinearMapAt ℝ (c.symm z) (τ (c.symm z))
    exact ((e i).continuousLinearMapAt_apply_of_mem ℝ hz _).symm
  have hchartDerivative (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
      (i : A.Index) (τ : ∀ x : M, E x) (x : M)
      (hx : x ∈ c.source ∩ (e i).baseSet)
      (hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
        (fun y ↦ (⟨y, τ y⟩ : TotalSpace F E)) x)
      (v : TangentSpace I x) :
      fderiv ℝ (atlasSectionInChart A c i τ) (c x) (mfderiv I I c x v) =
        mvfderiv I (coordinates i τ) x v := by
    have hu := hcoordinateDiff i τ x hx.2
      hτ
    have hchart := mdifferentiable_of_mem_atlas (I := I) hc
    have hc' := hchart.mdifferentiableAt_symm (c.map_source hx.1)
    have hchain := mvfderiv_comp (I := I) (I' := I) (c x)
      (by simpa only [c.left_inv hx.1] using hu) hc'
    have hlocal : fderiv ℝ (atlasSectionInChart A c i τ) (c x) =
        (mvfderiv I (coordinates i τ) x).comp (mfderiv I I c.symm (c x)) := by
      rw [(hatlasCoordinates c hc i τ x hx).fderiv_eq]
      dsimp only [I] at hchain
      rw [mvfderiv_eq_fderiv, c.left_inv hx.1] at hchain
      exact hchain
    rw [hlocal]
    change (mvfderiv I (coordinates i τ) x)
      (((mfderiv I I c.symm (c x)).comp (mfderiv I I c x)) v) = _
    rw [hchart.symm_comp_deriv hx.1]
    rfl
  -- A smooth section with the same value determines the tensorial connection correction.
  obtain ⟨u, hu⟩ := exists_smoothSection_apply_eq (n := n) (r := r) x (σ x)
  have hud : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun y ↦ (⟨y, u.val y⟩ : TotalSpace F E)) x := by
    have ht : ContMDiffAt I (I.prod 𝓘(ℝ, F)) ∞
        (fun y ↦ (⟨y, u.val y⟩ : TotalSpace F E)) x :=
      ((e i).contMDiffAt_section_iff hx.2).mpr
        ((u.property (e i) inferInstance).contMDiffAt ((e i).open_baseSet.mem_nhds hx.2))
    exact ht.mdifferentiableAt (by simp)
  have hvalue (τ : ∀ y : M, E y) :
      atlasSectionInChart A c i τ (c x) = coordinates i τ x := by
    simpa only [c.left_inv hx.1] using
      (hatlasCoordinates c hc i τ x hx).self_of_nhds
  have huformula :
      (e i).continuousLinearMapAt ℝ x (covE u.val x v) =
        mvfderiv I (coordinates i u.val) x v +
          Γ (coordinates i u.val x) := by
    have h := hA u x v
    rw [covA.covariantDerivative_eq
      ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u) c hc i x hx v] at h
    have ht := congrArg (A.frameLinearEquiv i x hx.2) h
    rw [atlasConnectionExpression, LinearEquiv.apply_symm_apply] at ht
    change (EuclideanSpace.equiv (Fin r) ℂ)
        (fderiv ℝ (atlasSectionInChart A c i u.val) (c x) (mfderiv I I c x v) +
          covA.connectionForm c i (c x) (mfderiv I I c x v)
            (atlasSectionInChart A c i u.val (c x))) =
      (EuclideanSpace.equiv (Fin r) ℂ) (e i ⟨x, covE u.val x v⟩).2 at ht
    have heq := (EuclideanSpace.equiv (Fin r) ℂ).injective ht
    rw [hchartDerivative c hc i u.val x hx hud v, hvalue,
      ← (e i).continuousLinearMapAt_apply_of_mem ℝ hx.2] at heq
    exact heq.symm
  have hcorrection :
      (e i).continuousLinearMapAt ℝ x (difference i x (σ x) v) =
        Γ (coordinates i σ x) := by
    have hdiff := hdifference i u.val x hx.2 hud
    have heq := congrArg (fun L : TangentSpace I x →L[ℝ] E x ↦
      (e i).continuousLinearMapAt ℝ x (L v)) hdiff
    simp only [sub_apply, map_sub] at heq
    change _ = (e i).continuousLinearMapAt ℝ x (covE u.val x v) -
      (e i).continuousLinearMapAt ℝ x
        ((e i).symmL ℝ x (mvfderiv I (coordinates i u.val) x v)) at heq
    rw [(e i).continuousLinearMapAt_symmL hx.2, huformula, add_sub_cancel_left] at heq
    dsimp only [coordinates] at heq ⊢
    simpa only [hu] using heq
  -- The arbitrary differentiable section has that same correction, plus its own derivative.
  have hdiff := hdifference i σ x hx.2 hσ
  have heq := congrArg (fun L : TangentSpace I x →L[ℝ] E x ↦
    (e i).continuousLinearMapAt ℝ x (L v)) hdiff
  simp only [sub_apply, map_sub] at heq
  change _ = (e i).continuousLinearMapAt ℝ x (covE σ x v) -
    (e i).continuousLinearMapAt ℝ x
      ((e i).symmL ℝ x (mvfderiv I (coordinates i σ) x v)) at heq
  rw [(e i).continuousLinearMapAt_symmL hx.2, hcorrection] at heq
  apply (A.frameLinearEquiv i x hx.2).injective
  rw [LinearEquiv.apply_symm_apply]
  change (EuclideanSpace.equiv (Fin r) ℂ) (e i ⟨x, covE σ x v⟩).2 = _
  rw [← (e i).continuousLinearMapAt_apply_of_mem ℝ hx.2]
  apply congrArg (EuclideanSpace.equiv (Fin r) ℂ)
  rw [hchartDerivative c hc i σ x hx hσ v, hvalue]
  exact (eq_add_of_sub_eq heq.symm).trans (add_comm _ _)

end AtiyahSinger
