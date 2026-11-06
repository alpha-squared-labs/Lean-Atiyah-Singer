/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CompactSupportFormExtension
public import AtiyahSinger.Geometry.EuclideanTopFormGenerator
public import AtiyahSinger.Geometry.EuclideanTopFormPrimitive
public import AtiyahSinger.Geometry.SphereDeRhamExactLocalization
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Top-degree integration on the original sphere de Rham quotient

Public module ID: M1441.

Closed forms vanishing near a fixed point surject onto the original sphere
quotient. Their compactly supported native-chart integral has exactly the same
kernel: zero integral gives a compact primitive, and an original global
primitive can be adjusted to compact support. A normalized original top form
makes the integral surjective. Thus it descends to a linear equivalence on
the original quotient, retaining its actual value on every localized class.

Source: the compact-support de Rham computation of spheres, Bott--Tu, Chapter I.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

set_option maxHeartbeats 3000000 in
-- The two kernels and their common specified localized representatives are checked explicitly.
set_option maxRecDepth 5000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual top sphere quotient is identified by the native-chart integral of localized forms. -/
theorem exists_sphereTopDeRhamIntegral (n : ℕ) (pole : OrthogonalSphere (n + 1)) :
    ∃ e : DeRhamCohomology (n := n + 1) (OrthogonalSphere (n + 1)) (n + 1) ≃ₗ[ℂ] ℂ,
      ∀ u : deRhamClosedForms (n := n + 1) (M := OrthogonalSphere (n + 1)) (n + 1),
        (∀ᶠ y in 𝓝 pole, u.val.val y = 0) →
        e (deRhamClass (n := n + 1) (n + 1) u) =
          euclideanTopFormIntegral (n + 1)
            (differentialFormInChart u.val.val (stereographic' (n + 1) pole)) := by
  classical
  let S := OrthogonalSphere (n + 1)
  let V := EuclideanSpace ℝ (Fin (n + 1))
  let P := Fin (n + 1) → ℝ
  let I := 𝓘(ℝ, V)
  let c := stereographic' (n + 1) pole
  have hc : c ∈ atlas V S := ⟨pole, rfl⟩
  have hct : c.target = univ := stereographic'_target pole
  have hpole : pole ∉ c.source := by simp [c, stereographic'_source]
  let : AddCommGroup (SmoothDifferentialForm (n := n + 1) S (n + 1)) :=
    Submodule.addCommGroup (smoothDifferentialForms (n := n + 1) (M := S) (n + 1))
  let : AddCommGroup (deRhamClosedForms (n := n + 1) (M := S) (n + 1)) :=
    Submodule.addCommGroup (deRhamClosedForms (n := n + 1) (M := S) (n + 1))
  let C : Submodule ℂ (deRhamClosedForms (n := n + 1) (M := S) (n + 1)) := {
    carrier := {u | ∀ᶠ y in 𝓝 pole, u.val.val y = 0}
    zero_mem' := Filter.Eventually.of_forall (fun _ ↦ rfl)
    add_mem' := by
      intro u v hu hv
      filter_upwards [hu, hv] with y hyu hyv
      change u.val.val y + v.val.val y = 0
      rw [hyu, hyv, add_zero]
    smul_mem' := by
      intro z u hu
      filter_upwards [hu] with y hy
      change z • u.val.val y = 0
      rw [hy, smul_zero] }
  let : AddCommGroup C := Submodule.addCommGroup C
  let coeff (u : C) : V → V [⋀^Fin (n + 1)]→L[ℝ] ℂ :=
    differentialFormInChart u.val.val.val c
  have hsmooth (u : C) : ContDiff ℝ ∞ (coeff u) :=
    contDiffOn_univ.mp (hct ▸ u.val.val.property c hc)
  have hcompact (u : C) : HasCompactSupport (coeff u) := by
    let K : Set S := closure {y : S | u.val.val.val y ≠ 0}
    have hK : IsCompact K := isClosed_closure.isCompact
    have hpK : pole ∉ K := by
      intro h
      obtain ⟨y, hy, hyK⟩ := mem_closure_iff_nhds.mp h
        {y : S | u.val.val.val y = 0} u.property
      exact hyK hy
    have hKc : K ⊆ c.source := by
      intro y hy
      rw [stereographic'_source]
      intro hyp
      exact hpK (show pole ∈ K from (mem_singleton_iff.mp hyp) ▸ hy)
    have hi : IsCompact (c '' K) := hK.image_of_continuousOn (c.continuousOn.mono hKc)
    apply hi.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hi.isClosed
    intro z hz
    have hzK : c.symm z ∈ K := by
      apply subset_closure
      intro hz0
      apply hz
      change (u.val.val.val (c.symm z)).compContinuousLinearMap _ = 0
      rw [hz0]
      ext v
      rfl
    exact ⟨c.symm z, hzK, c.right_inv (hct.symm ▸ mem_univ z)⟩
  let E : P ≃L[ℝ] V := (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  let ev : (V [⋀^Fin (n + 1)]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    ContinuousAlternatingMap.apply ℝ V ℂ b
  have hint (u : C) : Integrable (fun x : P ↦ ev (coeff u (E x))) := by
    have hcont := ev.continuous.comp ((hsmooth u).continuous.comp E.continuous)
    exact hcont.integrable_of_hasCompactSupport
      (((hcompact u).comp_homeomorph E.toHomeomorph).comp_left ev.map_zero)
  have hcoeffAdd (u v : C) (y : V) : coeff (u + v) y = coeff u y + coeff v y := by
    ext w
    rfl
  have hcoeffSmul (z : ℂ) (u : C) (y : V) : coeff (z • u) y = z • coeff u y := by
    ext w
    rfl
  let L : C →ₗ[ℂ] ℂ := {
    toFun u := euclideanTopFormIntegral (n + 1) (coeff u)
    map_add' := by
      intro u v
      unfold euclideanTopFormIntegral
      simp_rw [hcoeffAdd]
      exact integral_add (hint u) (hint v)
    map_smul' := by
      intro z u
      unfold euclideanTopFormIntegral
      simp_rw [hcoeffSmul]
      exact integral_smul z _ }
  let Q := DeRhamCohomology (n := n + 1) S (n + 1)
  let classes : C →ₗ[ℂ] Q := (deRhamClass (n := n + 1) (n + 1)).comp C.subtype
  have hsurj : Function.Surjective classes := by
    intro a
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective
      ((deRhamExactForms (n := n + 1) (M := S) (n + 1)).comap
        (deRhamClosedForms (n := n + 1) (M := S) (n + 1)).subtype) a
    obtain ⟨v, hv, hnear, _⟩ := exists_sphereDeRhamRepresentative_compactSupport (n + 1) n u pole
    exact ⟨⟨v, hnear⟩, hv⟩
  -- Original exactness implies zero integral, using the same primitive adjusted at the pole.
  have hkerForward : LinearMap.ker classes ≤ LinearMap.ker L := by
    intro u hu
    change classes u = 0 at hu
    have h := (Submodule.Quotient.eq _).mp hu
    change ∃ primitive : SmoothDifferentialForm (n := n + 1) S n,
      smoothFormExteriorDerivative (n := n + 1) n primitive = u.val.val - 0 at h
    obtain ⟨primitive, hprimitive⟩ := h
    rw [sub_zero] at hprimitive
    obtain ⟨η, hη, hηc, hdη⟩ := exists_sphereExactForm_compactlySupported_primitive
      (n + 1) n u.val.val pole u.property primitive hprimitive
    change euclideanTopFormIntegral (n + 1) (coeff u) = 0
    have heq : coeff u = extDeriv η := funext (fun z ↦ (hdη z).symm)
    rw [heq, euclideanTopFormIntegral_extDeriv n η hη hηc]
  -- Conversely zero integral gives an actual compact primitive and its original zero extension.
  have hkerBackward : LinearMap.ker L ≤ LinearMap.ker classes := by
    intro u hu
    change euclideanTopFormIntegral (n + 1) (coeff u) = 0 at hu
    obtain ⟨η, hη, hηc, hdη⟩ := exists_smooth_compactlySupported_topFormPrimitive n
      (coeff u) (hsmooth u) (hcompact u) hu
    obtain ⟨primitive, hcoeff, _, hdoutside⟩ :=
      exists_smoothFormExtension_of_compactSupport n c hc hct η hη hηc
    have hdu : smoothFormExteriorDerivative (n := n + 1) n primitive = u.val.val := by
      apply Subtype.ext
      funext x
      by_cases hx : x ∈ c.source
      · have h := smoothFormExteriorDerivative_inChart primitive c hc (c x) (c.map_source hx)
        rw [hcoeff, hdη] at h
        have hval (a : SmoothDifferentialForm (n := n + 1) S (n + 1)) :
            (differentialFormInChart a.val c (c x)).compContinuousLinearMap
              (mfderiv I I c x) = a.val x := by
          ext v
          change a.val (c.symm (c x))
            (fun i ↦ mfderiv I I c.symm (c x) (mfderiv I I c x (v i))) = a.val x v
          rw [c.left_inv hx]
          apply congrArg (a.val x)
          funext i
          exact congrArg (fun L ↦ L (v i))
            ((mdifferentiable_of_mem_atlas (I := I) hc).symm_comp_deriv hx)
        have heq := congrArg (fun a : V [⋀^Fin (n + 1)]→L[ℝ] ℂ ↦
          a.compContinuousLinearMap (mfderiv I I c x)) h
        exact (hval _).symm.trans (heq.trans (hval u.val.val))
      · have hxp : x = pole := by
          simpa only [c, stereographic'_source, mem_compl_iff, mem_singleton_iff, not_not] using hx
        rw [hdoutside x hx, hxp]
        exact u.property.self_of_nhds.symm
    change classes u = 0
    apply (Submodule.Quotient.eq _).mpr
    change ∃ a : SmoothDifferentialForm (n := n + 1) S n,
      smoothFormExteriorDerivative (n := n + 1) n a = u.val.val - 0
    exact ⟨primitive, hdu.trans (sub_zero _).symm⟩
  -- A normalized compact top form supplies the nonzero class and every scalar multiple.
  have hLsurj : Function.Surjective L := by
    obtain ⟨α, hα, hαc, hαi⟩ := exists_smooth_compactlySupported_topForm_integral_one (n + 1)
    obtain ⟨form, hcoeff, hnear, _⟩ :=
      exists_smoothFormExtension_of_compactSupport (n + 1) c hc hct α hα hαc
    have hclosed : form ∈ deRhamClosedForms (n := n + 1) (M := S) (n + 1) := by
      change smoothFormExteriorDerivative (n := n + 1) (n + 1) form = 0
      apply Subtype.ext
      funext y
      apply ContinuousAlternatingMap.toAlternatingMap_injective
      apply (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.ext_alternating
      intro v hv
      have hcard := Fintype.card_le_of_injective v hv
      simp only [Fintype.card_fin] at hcard
      omega
    let u : C := ⟨⟨form, hclosed⟩, hnear pole hpole⟩
    have hLu : L u = 1 := by
      change euclideanTopFormIntegral (n + 1) (differentialFormInChart form.val c) = 1
      rw [hcoeff]
      exact hαi
    intro z
    refine ⟨z • u, ?_⟩
    rw [map_smul, hLu, smul_eq_mul, mul_one]
  -- Equal original classes have equal integrals; choose representatives only to descend this map.
  have hcongr (u v : C) (h : classes u = classes v) : L u = L v := by
    have hz : classes (u - v) = 0 := by rw [map_sub, h, sub_self]
    have hi : L (u - v) = 0 := hkerForward hz
    rw [map_sub] at hi
    exact sub_eq_zero.mp hi
  let rep (a : Q) : C := Classical.choose (hsurj a)
  have hrep (a : Q) : classes (rep a) = a := Classical.choose_spec (hsurj a)
  let l : Q →ₗ[ℂ] ℂ := {
    toFun a := L (rep a)
    map_add' := by
      intro a b
      have h := hcongr (rep (a + b)) (rep a + rep b) (by rw [hrep, map_add, hrep, hrep])
      exact h.trans (L.map_add _ _)
    map_smul' := by
      intro z a
      have h := hcongr (rep (z • a)) (z • rep a) (by rw [hrep, map_smul, hrep])
      exact h.trans (L.map_smul _ _) }
  have hl (u : C) : l (classes u) = L u := hcongr (rep (classes u)) u (hrep _)
  have hlbij : Function.Bijective l := by
    constructor
    · intro a b hab
      obtain ⟨u, rfl⟩ := hsurj a
      obtain ⟨v, rfl⟩ := hsurj b
      have hL : L (u - v) = 0 := by rw [map_sub, ← hl, ← hl, hab, sub_self]
      have hC : classes (u - v) = 0 := hkerBackward hL
      rw [map_sub] at hC
      exact sub_eq_zero.mp hC
    · intro z
      obtain ⟨u, hu⟩ := hLsurj z
      exact ⟨classes u, (hl u).trans hu⟩
  refine ⟨LinearEquiv.ofBijective l hlbij, ?_⟩
  intro u hu
  exact hl ⟨u, hu⟩

end AtiyahSinger
