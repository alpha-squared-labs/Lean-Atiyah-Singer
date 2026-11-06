/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasConnectionDescent
public import AtiyahSinger.Geometry.AssociatedSpinSectionCoordinates
public import AtiyahSinger.Geometry.SmoothSpinorBundle

/-!
# Descent of connection forms in the original associated spin coordinates

Public module ID: M1443.

Forms in the original representation model descend through its actual principal
transitions and every chart of the selected associated atlas. Only the selected
principal charts need be associated charts; no converse is assumed. The local
formula retains the original representative fiber equivalence and its native
manifold derivative. No separation or global extension assumption is used.

Source: the associated connection construction, Spin Geometry II.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

set_option maxSynthPendingDepth 50

variable {n m : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : ContRepresentation ℂ (spinGroup (realSpinorQuadraticForm m)) W)
  (A : SmoothSpinPrincipalAtlas m 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) projection)
  (H : SmoothComplexBundleAtlas (n := n) (AssociatedVectorFiber hP ρ))

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "V" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 0 in
-- The associated-frame descent includes all coordinate transports and derivative comparisons.
/-- Gauge-compatible forms give the original derivative-plus-form formula in associated fibers. -/
theorem exists_associatedSpinConnection
    (hH : A.IsAssociatedVectorAtlas hP ρ H)
    (Ω : ∀ (_b x : M), TangentSpace I x →L[ℝ] (W →L[ℂ] W))
    (hsmooth : ∀ (c : OpenPartialHomeomorph M V), c ∈ atlas V M → ∀ b : M,
      ContDiffOn ℝ ∞ (fun z ↦ (Ω b (c.symm z)).comp (mfderiv I I c.symm z))
        (c.target ∩ c.symm ⁻¹' (A.trivialization b).baseSet))
    (hRdiff : ∀ (a b x : M), x ∈ (A.trivialization a).baseSet →
      x ∈ (A.trivialization b).baseSet →
      MDifferentiableAt I 𝓘(ℝ, W →L[ℂ] W)
        (fun y ↦ ρ ((A.trivialization b)
          ((A.trivialization a).toPartialEquiv.symm (y, 1))).2) x)
    (hgauge : ∀ (a b x : M), x ∈ (A.trivialization a).baseSet →
      x ∈ (A.trivialization b).baseSet → ∀ (X : TangentSpace I x) (w : W),
      let R := fun y ↦ ρ ((A.trivialization b)
        ((A.trivialization a).toPartialEquiv.symm (y, 1))).2
      Ω b x X (R x w) + mvfderiv I R x X w = R x (Ω a x X w)) :
    ∃ cov : AtlasComplexConnection H,
      ∀ (b x : M) (hx : x ∈ (A.trivialization b).baseSet)
        (u : H.smoothSections) (X : TangentSpace I x),
        let E := fun y (hy : y ∈ (A.trivialization b).baseSet) ↦
          associatedVectorFiberMkLinearEquiv hP ρ
            ((A.trivialization b).toPartialEquiv.symm (y, 1))
            ((A.trivialization b).proj_symm_apply' hy)
        let q := associatedSpinSectionCoordinates hP ρ A b u.val
        (E x hx).symm (cov.covariantDerivative u x X) =
          mvfderiv I q x X + Ω b x X (q x) := by
  classical
  have hassociated := hH
  choose good c hbase hchart using hH
  let F (b : M) := EuclideanSpace ℂ (Fin (H.rank (good b)))
  let C (b : M) : W ≃L[ℂ] F b :=
    (c b).toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin (H.rank (good b))) ℂ).symm
  let E (b x : M) (hx : x ∈ (A.trivialization b).baseSet) :
      W ≃ₗ[ℂ] AssociatedVectorFiber hP ρ x :=
    associatedVectorFiberMkLinearEquiv hP ρ
      ((A.trivialization b).toPartialEquiv.symm (x, 1))
      ((A.trivialization b).proj_symm_apply' hx)
  have hframe (b x : M) (hx : x ∈ (A.trivialization b).baseSet) (w : W) :
      H.frameLinearEquiv (good b) x ((hbase b).symm ▸ hx) (E b x hx w) = c b w := by
    have h := hchart b ((A.trivialization b).toPartialEquiv.symm (x, 1)) x
      ((A.trivialization b).proj_symm_apply' hx) hx w
    have hunit : (A.trivialization b) ((A.trivialization b).toPartialEquiv.symm (x, 1)) =
        (x, 1) := (A.trivialization b).apply_symm_apply' hx
    rw [hunit] at h
    change (H.chart (good b) ⟨x, associatedVectorFiberMk hP ρ
      ((A.trivialization b).toPartialEquiv.symm (x, 1))
      ((A.trivialization b).proj_symm_apply' hx) w⟩).2 = _
    simpa only [map_one, one_apply_eq_self] using h
  let R (a b : M) (y : M) : W →L[ℂ] W :=
    ρ ((A.trivialization b) ((A.trivialization a).toPartialEquiv.symm (y, 1))).2
  let T (a b : M) : (W →L[ℂ] W) →L[ℝ] (F a →L[ℂ] F b) :=
    ((C a).arrowCongr (C b)).toContinuousLinearMap.restrictScalars ℝ
  have htransition (a b x : M) (ha : x ∈ (A.trivialization a).baseSet)
      (hb : x ∈ (A.trivialization b).baseSet) :
      H.coordChangeL (good a) (good b) x = T a b (R a b x) := by
    apply ContinuousLinearMap.ext
    intro v
    have h := H.coordChangeL_apply (good a) (good b) x
      ⟨(hbase a).symm ▸ ha, (hbase b).symm ▸ hb⟩
      (E a x ha ((C a).symm v))
    change (EuclideanSpace.equiv (Fin (H.rank (good b))) ℂ).symm
        (H.frameLinearEquiv (good b) x ((hbase b).symm ▸ hb)
          (E a x ha ((C a).symm v))) =
      H.coordChangeL (good a) (good b) x
        ((EuclideanSpace.equiv (Fin (H.rank (good a))) ℂ).symm
          (H.frameLinearEquiv (good a) x ((hbase a).symm ▸ ha)
            (E a x ha ((C a).symm v)))) at h
    rw [hframe a x ha] at h
    have hsource : (EuclideanSpace.equiv (Fin (H.rank (good a))) ℂ).symm
        (c a ((C a).symm v)) = v := (C a).apply_symm_apply v
    have htarget : H.frameLinearEquiv (good b) x ((hbase b).symm ▸ hb)
        (E a x ha ((C a).symm v)) = c b (R a b x ((C a).symm v)) :=
      hchart b ((A.trivialization a).toPartialEquiv.symm (x, 1)) x
        ((A.trivialization a).proj_symm_apply' ha) hb _
    rw [hsource, htarget] at h
    exact h.symm
  let Γ (d : OpenPartialHomeomorph M V) (b : M) (z : V) :
      V →L[ℝ] (F b →L[ℂ] F b) :=
    (T b b).comp ((Ω b (d.symm z)).comp (mfderiv I I d.symm z))
  have hΓ (d : OpenPartialHomeomorph M V) (hd : d ∈ atlas V M)
      (b x : M) (hx : x ∈ d.source) (X : TangentSpace I x) (w : F b) :
      Γ d b (d x) (mfderiv I I d x X) w = C b (Ω b x X ((C b).symm w)) := by
    have hi := (mdifferentiable_of_mem_atlas («I» := I) hd).symm_comp_deriv hx
    change T b b (Ω b (d.symm (d x))
      (mfderiv I I d.symm (d x) (mfderiv I I d x X))) w = _
    have hv : (mfderiv I I d.symm (d x) (mfderiv I I d x X) : V) = X :=
      congrArg (fun L ↦ L X) hi
    have hp : (⟨d.symm (d x), mfderiv I I d.symm (d x) (mfderiv I I d x X)⟩ :
        TangentBundle I M) = ⟨x, X⟩ := TotalSpace.ext (d.left_inv hx) (heq_of_eq hv)
    have hΩ := congrArg (fun p : TangentBundle I M ↦ Ω b p.proj p.snd) hp
    rw [hΩ]
    rfl
  have hΓsmooth (d : OpenPartialHomeomorph M V) (hd : d ∈ atlas V M) (b : M) :
      ContDiffOn ℝ ∞ (Γ d b) (d.target ∩ d.symm ⁻¹' (H.chart (good b)).baseSet) := by
    rw [hbase b]
    exact contDiffOn_const.clm_comp (hsmooth d hd b)
  have hTderivative (a b x : M) (ha : x ∈ (A.trivialization a).baseSet)
      (hb : x ∈ (A.trivialization b).baseSet) (X : TangentSpace I x) :
      mvfderiv I (H.coordChangeL (good a) (good b)) x X =
        T a b (mvfderiv I (R a b) x X) := by
    have heq : H.coordChangeL (good a) (good b) =ᶠ[nhds x] fun y ↦ T a b (R a b y) := by
      filter_upwards [((A.trivialization a).open_baseSet.inter
        (A.trivialization b).open_baseSet).mem_nhds ⟨ha, hb⟩] with y hy
      exact htransition a b y hy.1 hy.2
    have hc := mvfderiv_comp («I» := 𝓘(ℝ, W →L[ℂ] W)) (I' := I) x
      (T a b).differentiableAt.mdifferentiableAt (hRdiff a b x ha hb)
    rw [mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hc
    have hD : mvfderiv I (H.coordChangeL (good a) (good b)) x =
        mvfderiv I (fun y ↦ T a b (R a b y)) x := by
      unfold mvfderiv
      rw [heq.mfderiv_eq]
      rfl
    rw [hD]
    exact congrArg (fun L ↦ L X) hc
  have hΓgauge (d e : OpenPartialHomeomorph M V) (hd : d ∈ atlas V M)
      (he : e ∈ atlas V M) (a b x : M)
      (hx : x ∈ d.source ∩ (H.chart (good a)).baseSet)
      (hy : x ∈ e.source ∩ (H.chart (good b)).baseSet)
      (X : TangentSpace I x) (v : F a) :
      Γ e b (e x) (mfderiv I I e x X) (H.coordChangeL (good a) (good b) x v) +
        (mvfderiv I (H.coordChangeL (good a) (good b)) x X) v =
          H.coordChangeL (good a) (good b) x (Γ d a (d x) (mfderiv I I d x X) v) := by
    have ha : x ∈ (A.trivialization a).baseSet := hbase a ▸ hx.2
    have hb : x ∈ (A.trivialization b).baseSet := hbase b ▸ hy.2
    rw [hΓ e he b x hy.1, hΓ d hd a x hx.1,
      htransition a b x ha hb, hTderivative a b x ha hb]
    change C b (Ω b x X ((C b).symm (C b (R a b x ((C a).symm v))))) +
      C b (mvfderiv I (R a b) x X ((C a).symm v)) =
        C b (R a b x ((C a).symm (C a (Ω a x X ((C a).symm v)))))
    rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply,
      ← map_add, hgauge a b x ha hb]
  obtain ⟨cov, hcov⟩ := exists_atlasComplexConnection_of_cover_forms H good
    (fun x ↦ ⟨x, (hbase x).symm ▸ A.mem_baseSet x⟩) Γ hΓsmooth hΓgauge
  refine ⟨cov, ?_⟩
  intro b x hx u X
  let q := associatedSpinSectionCoordinates hP ρ A b u.val
  have hq (y : M) (hy : y ∈ (A.trivialization b).baseSet) :
      c b (q y) = (H.chart (good b) ⟨y, u.val y⟩).2 := by
    have hf := hframe b y hy ((E b y hy).symm (u.val y))
    rw [LinearEquiv.apply_symm_apply] at hf
    simp only [q, associatedSpinSectionCoordinates, dite_eq_left hy]
    exact hf.symm
  have hqd : MDifferentiableAt I 𝓘(ℝ, W) q x :=
    ((contMDiffOn_associatedSpinSectionCoordinates hP ρ A H hassociated b u).contMDiffAt
      ((A.trivialization b).open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  let d := chartAt V x
  have hd : d ∈ atlas V M := chart_mem_atlas V x
  have hdx : x ∈ d.source := mem_chart_source V x
  have hderivative : fderiv ℝ (atlasSectionInChart H d (good b) u.val) (d x)
      (mfderiv I I d x X) = C b (mvfderiv I q x X) := by
    have hdif := mdifferentiable_of_mem_atlas («I» := I) hd
    have hdi := hdif.mdifferentiableAt_symm (d.map_source hdx)
    have hqd' : MDifferentiableAt I 𝓘(ℝ, W) q (d.symm (d x)) := by
      simpa only [d.left_inv hdx] using hqd
    have hchain := mvfderiv_comp («I» := I) (I' := I) (d x)
      (by simpa only [d.left_inv hdx] using hqd) hdi
    rw [mvfderiv_eq_fderiv, d.left_inv hdx] at hchain
    have hC := ((C b).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp (d x)
      (mdifferentiableAt_iff_differentiableAt.mp
        (hqd'.comp (d x) hdi)).hasFDerivAt
    have hlocal : atlasSectionInChart H d (good b) u.val =ᶠ[nhds (d x)]
        (fun z ↦ C b (q (d.symm z))) := by
      have hnear := hdi.continuousAt.preimage_mem_nhds (by
        rw [d.left_inv hdx]
        exact (A.trivialization b).open_baseSet.mem_nhds hx)
      filter_upwards [hnear] with z hz
      change (EuclideanSpace.equiv (Fin (H.rank (good b))) ℂ).symm
        (H.chart (good b) ⟨d.symm z, u.val (d.symm z)⟩).2 = _
      rw [← hq (d.symm z) hz]
      rfl
    have hDX : fderiv ℝ (q ∘ d.symm) (d x) (mfderiv I I d x X) =
        mvfderiv I q x X := by
      have h := congrArg (fun L ↦ L (mfderiv I I d x X)) hchain
      change fderiv ℝ (q ∘ d.symm) (d x) (mfderiv I I d x X) =
        mvfderiv I q x (((mfderiv I I d.symm (d x)).comp (mfderiv I I d x)) X) at h
      rw [hdif.symm_comp_deriv hdx] at h
      exact h
    have hC' := hC.fderiv
    change fderiv ℝ (fun z ↦ C b (q (d.symm z))) (d x) =
      ((C b).toContinuousLinearMap.restrictScalars ℝ).comp
        (fderiv ℝ (q ∘ d.symm) (d x)) at hC'
    rw [hlocal.fderiv_eq, hC']
    change C b (fderiv ℝ (q ∘ d.symm) (d x) (mfderiv I I d x X)) = _
    rw [hDX]
  have hvalue := hcov d hd b u x ⟨hdx, (hbase b).symm ▸ hx⟩ X
  apply (c b).injective
  have hleft := congrArg (H.frameLinearEquiv (good b) x ((hbase b).symm ▸ hx)) hvalue
  have hE := hframe b x hx ((E b x hx).symm (cov.covariantDerivative u x X))
  rw [LinearEquiv.apply_symm_apply] at hE
  rw [hE] at hleft
  unfold atlasConnectionExpression at hleft
  rw [LinearEquiv.apply_symm_apply, hderivative] at hleft
  have hcoordinate : atlasSectionInChart H d (good b) u.val (d x) = C b (q x) := by
    change (EuclideanSpace.equiv (Fin (H.rank (good b))) ℂ).symm
      (H.chart (good b) ⟨d.symm (d x), u.val (d.symm (d x))⟩).2 = _
    rw [d.left_inv hdx, ← hq x hx]
    rfl
  rw [hcoordinate, hΓ d hd b x hdx, ContinuousLinearEquiv.symm_apply_apply,
    ← map_add] at hleft
  exact hleft

end AtiyahSinger
