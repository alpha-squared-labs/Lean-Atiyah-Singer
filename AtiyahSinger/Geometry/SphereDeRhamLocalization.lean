/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EuclideanDeRham
public import AtiyahSinger.Geometry.OrthogonalSphere
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Localizing original sphere de Rham classes away from a point

Public module ID: M1428.

On a Hausdorff smooth manifold, the radial primitive in a full Euclidean
chart pulls back through a globally
smooth extension of that chart near the specified point. Subtracting its
actual exterior derivative leaves the original cohomology class unchanged
and makes its representative vanish near the point. The construction is the
localization step in the compact-support computation of sphere cohomology.

Source: the standard de Rham localization proof using the Poincaré lemma
and a smooth bump function, as in Bott--Tu, Chapter I.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter Set
open scoped ContDiff Manifold Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

set_option backward.isDefEq.respectTransparency false in
/-- In a full Euclidean chart, every closed positive-degree form is locally exact,
with a primitive defined smoothly on the entire original manifold. -/
theorem exists_smoothFormPrimitive_near_of_chart_target_univ (p : ℕ)
    (form : SmoothDifferentialForm (n := n) M (p + 1))
    (hclosed : smoothFormExteriorDerivative (n := n) (p + 1) form = 0)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (htarget : c.target = univ)
    (x : M) (hx : x ∈ c.source) :
    ∃ primitive : SmoothDifferentialForm (n := n) M p,
      ∀ᶠ y in 𝓝 x, (smoothFormExteriorDerivative (n := n) p primitive).val y = form.val y := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, V)
  let α : V → V [⋀^Fin (p + 1)]→L[ℝ] ℂ := differentialFormInChart form.val c
  -- The original coordinate derivative makes the same coefficients a closed Euclidean form.
  have hα : ContDiff ℝ ∞ α := by
    exact contDiffOn_univ.mp (htarget ▸ form.property c hc)
  have hαclosed (z : V) : extDeriv α z = 0 := by
    have h := smoothFormExteriorDerivative_inChart form c hc z (htarget.symm ▸ mem_univ z)
    rw [hclosed] at h
    exact h.symm.trans (by ext v; rfl)
  obtain ⟨η, hη, hdη⟩ := exists_smooth_euclideanFormPrimitive p α hα hαclosed
  -- The self-chart gives an original Euclidean smooth form with exactly this primitive.
  have hself (q : ℕ) (a : ∀ z : V, DifferentialFormFiber (n := n) q z) :
      differentialFormInChart a (OpenPartialHomeomorph.refl V) = a := by
    funext z
    change (a z).compContinuousLinearMap (mfderiv I I (id : V → V) z) = _
    rw [mfderiv_id]
    ext v
    rfl
  let primitiveV : SmoothDifferentialForm (n := n) V p := ⟨η, by
    intro a ha
    rw [chartedSpaceSelf_atlas.mp ha, hself]
    exact hη.contDiffOn⟩
  have hprimitiveV (z : V) :
      (smoothFormExteriorDerivative (n := n) p primitiveV).val z = α z := by
    have h := smoothFormExteriorDerivative_inChart primitiveV
      (OpenPartialHomeomorph.refl V) (chartedSpaceSelf_atlas.mpr rfl) z (mem_univ z)
    rw [hself, hself] at h
    exact h.trans (hdη z)
  -- A bump makes the coordinate map global while retaining it on a whole neighborhood of x.
  obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    (c.open_source.mem_nhds hx)
  let f (y : M) : V := b y • c y
  have hf : ContMDiff I I ∞ f := by
    intro y
    by_cases hy : y ∈ tsupport b
    · exact b.contMDiff.contMDiffAt.smul
        (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) (hb hy))
    · apply (contMDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hy] with z hz
      change b z • c z = 0
      rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  have hfc : f =ᶠ[𝓝 x] c := by
    filter_upwards [b.eventuallyEq_one] with y hy
    change b y • c y = c y
    change b y = (1 : ℝ) at hy
    rw [hy, one_smul]
  let primitive := smoothFormPullback f hf p primitiveV
  refine ⟨primitive, ?_⟩
  -- Pullback commutes with the selected exterior derivative; inverse chart derivatives cancel.
  have hd := LinearMap.congr_fun (smoothFormExteriorDerivative_pullback f hf p) primitiveV
  filter_upwards [eventually_eventuallyEq_nhds.mpr hfc, c.open_source.mem_nhds hx]
    with y hy hyc
  have heq : f y = c y := hy.self_of_nhds
  have hdf : mfderiv I I f y = mfderiv I I c y := by
    have h := hy.mfderiv_eq (I := I) (I' := I)
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ L v) h
  have hval := congrArg (fun a : SmoothDifferentialForm (n := n) M (p + 1) ↦ a.val y) hd
  change (smoothFormExteriorDerivative (n := n) p primitive).val y = _ at hval
  rw [hval, LinearMap.comp_apply, smoothFormPullback_apply, heq, hprimitiveV, hdf]
  change (differentialFormInChart form.val c (c y)).compContinuousLinearMap
    (mfderiv I I c y) = form.val y
  ext v
  change form.val (c.symm (c y))
    (fun i ↦ mfderiv I I c.symm (c y) (mfderiv I I c y (v i))) = form.val y v
  rw [c.left_inv hyc]
  have hinv := (mdifferentiable_of_mem_atlas (I := I) hc).symm_comp_deriv hyc
  apply congrArg (form.val y)
  funext i
  exact congrArg (fun L ↦ L (v i)) hinv

set_option backward.isDefEq.respectTransparency false in
/-- Every positive-degree sphere class has an original closed representative vanishing
near a chosen point, with compactly supported coefficients in the chart omitting that point. -/
theorem exists_sphereDeRhamRepresentative_compactSupport (r p : ℕ)
    (form : deRhamClosedForms (n := r) (M := OrthogonalSphere r) (p + 1))
    (x : OrthogonalSphere r) :
    ∃ representative : deRhamClosedForms (n := r) (M := OrthogonalSphere r) (p + 1),
      deRhamClass (n := r) (p + 1) representative = deRhamClass (n := r) (p + 1) form ∧
      (∀ᶠ y in 𝓝 x, representative.val.val y = 0) ∧
      HasCompactSupport (differentialFormInChart representative.val.val (stereographic' r x)) := by
  classical
  let S := OrthogonalSphere r
  let V := EuclideanSpace ℝ (Fin r)
  let d := smoothFormExteriorDerivative (n := r) (M := S) p
  -- Solve near x in its original full chart and subtract that global exact form.
  have hfull : (chartAt V x).target = univ := stereographic'_target (-x)
  obtain ⟨primitive, hprimitive⟩ := exists_smoothFormPrimitive_near_of_chart_target_univ p
    form.val form.property (chartAt V x) (chart_mem_atlas V x) hfull x (mem_chart_source V x)
  have hclosed : form.val - d primitive ∈ deRhamClosedForms (n := r) (M := S) (p + 1) := by
    change smoothFormExteriorDerivative (n := r) (p + 1) (form.val - d primitive) = 0
    have hform : smoothFormExteriorDerivative (n := r) (p + 1) form.val = 0 := form.property
    have hdd := LinearMap.congr_fun (smoothFormExteriorDerivative_comp (n := r) (M := S) p)
      primitive
    rw [map_sub, hform, show smoothFormExteriorDerivative (n := r) (p + 1) (d primitive) = 0
      from hdd, sub_self]
  let representative : deRhamClosedForms (n := r) (M := S) (p + 1) :=
    ⟨form.val - d primitive, hclosed⟩
  have hzero : ∀ᶠ y in 𝓝 x, representative.val.val y = 0 := by
    filter_upwards [hprimitive] with y hy
    change form.val.val y - (d primitive).val y = 0
    rw [hy, sub_self]
  refine ⟨representative, ?_, hzero, ?_⟩
  · -- Equality uses the actual incoming range in the original algebraic quotient.
    apply (Submodule.Quotient.eq _).mpr
    change ∃ a : SmoothDifferentialForm (n := r) S p,
      d a = representative.val - form.val
    refine ⟨-primitive, ?_⟩
    change d (-primitive) = (form.val - d primitive) - form.val
    rw [map_neg]
    abel
  · -- The support is a compact subset of the punctured sphere; its chart image is compact.
    let c := stereographic' r x
    let K : Set S := closure {y : S | representative.val.val y ≠ 0}
    have hK : IsCompact K := isClosed_closure.isCompact
    have hxK : x ∉ K := by
      intro hxK
      obtain ⟨y, hy, hyK⟩ := mem_closure_iff_nhds.mp hxK
        {y : S | representative.val.val y = 0} hzero
      exact hyK hy
    have hKc : K ⊆ c.source := by
      intro y hy
      change y ∈ (stereographic' r x).source
      rw [stereographic'_source]
      intro hyx
      exact hxK (show x ∈ K from (mem_singleton_iff.mp hyx) ▸ hy)
    have hImage : IsCompact (c '' K) := hK.image_of_continuousOn (c.continuousOn.mono hKc)
    apply hImage.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hImage.isClosed
    intro z hz
    have hzK : c.symm z ∈ K := by
      apply subset_closure
      intro hz0
      apply hz
      change (representative.val.val (c.symm z)).compContinuousLinearMap _ = 0
      rw [hz0]
      ext v
      rfl
    exact ⟨c.symm z, hzK,
      c.right_inv ((stereographic'_target (n := r) x).symm ▸ mem_univ z)⟩

end AtiyahSinger
