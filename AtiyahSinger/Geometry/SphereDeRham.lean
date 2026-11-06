/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CompactSupportFormExtension
public import AtiyahSinger.Geometry.EuclideanCompactSupportPrimitive
public import AtiyahSinger.Geometry.OrthogonalSphereCotangent
public import AtiyahSinger.Geometry.SphereDeRhamLocalization
public import AtiyahSinger.Geometry.SphereTopDeRhamIntegral
public import AtiyahSinger.Geometry.SphereTopFormIntegralNaturality
public import Mathlib.RepresentationTheory.Basic

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Sphere de Rham cohomology and the orthogonal action

Public module ID: M1424.

E06: the cohomology groups below are the actual closed-form/exact-form quotients,
with the original sphere atlas and the inverse-pullback left action of O(r).
For positive r only degrees zero and r survive. The degree-zero action is
trivial, and the top-degree action is det in every positive dimension.
The zero-sphere is treated separately: its degree-zero group has dimension two.

SG II.5, p.125 supplies the de Rham quotient and Hodge context; III.13.7,
p.253 uses the sphere computation. Its claim that the top-degree action is
trivial in even dimension is incorrect for diag(g,1): that action is det.
The exact coordinate-quotient computation below is a project supplement; an
independent source for that precise formulation has not been located.
No Hodge operator, de Rham comparison theorem or analytic index formula is
assumed or constructed in this module.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff

set_option maxHeartbeats 800000 in
-- The quotient carries dependent manifold-form instances through both pullback compositions.
/-- The natural left orthogonal representation on the actual sphere de Rham cohomology. -/
def orthogonalSphereDeRhamRepresentation (r p : ℕ) :
    Representation ℂ (Matrix.orthogonalGroup (Fin r) ℝ)
      (DeRhamCohomology (n := r) (OrthogonalSphere r) p) where
  toFun A := deRhamPullback (fun x : OrthogonalSphere r ↦ A⁻¹ • x)
    (contMDiff_orthogonalSphere_smul r A⁻¹) p
  map_one' := by
    -- Identify the underlying smooth map first; its smoothness proofs are irrelevant.
    have hmap :
        (fun x : OrthogonalSphere r ↦
          (1 : Matrix.orthogonalGroup (Fin r) ℝ)⁻¹ • x) = id := by
      funext x
      simp only [inv_one, one_smul, id_eq]
    change deRhamPullback
      (fun x : OrthogonalSphere r ↦ (1 : Matrix.orthogonalGroup (Fin r) ℝ)⁻¹ • x)
      (contMDiff_orthogonalSphere_smul r 1⁻¹) p = LinearMap.id
    have hpullback (f g : OrthogonalSphere r → OrthogonalSphere r)
        (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin r))
          𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞ f)
        (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin r))
          𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞ g) (hfg : f = g) :
        deRhamPullback f hf p = deRhamPullback g hg p := by
      cases hfg
      rfl
    exact (hpullback _ id (contMDiff_orthogonalSphere_smul r 1⁻¹)
      contMDiff_id hmap).trans (deRhamPullback_id (n := r) (M := OrthogonalSphere r) p)
  map_mul' A B := by
    -- Inverse maps reverse group multiplication, and pullback reverses composition again.
    simpa only [mul_inv_rev, mul_smul, Function.comp_def, Module.End.mul_eq_comp] using
      (deRhamPullback_comp
        (fun x : OrthogonalSphere r ↦ A⁻¹ • x)
        (fun x : OrthogonalSphere r ↦ B⁻¹ • x)
        (contMDiff_orthogonalSphere_smul r A⁻¹)
        (contMDiff_orthogonalSphere_smul r B⁻¹) p)

open Set Function ContinuousAlternatingMap
open scoped Manifold ContDiff Topology

/-- A closed zero-form has locally constant scalar value.
This degree-zero Poincaré fact is shared by the sphere calculation and its natural action. -/
private theorem isLocallyConstant_closedZeroForm {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (u : deRhamClosedForms (n := n) (M := M) 0) :
    IsLocallyConstant (fun x ↦ u.val.val x 0) := by
  let V := EuclideanSpace ℝ (Fin n)
  let f : M → ℂ := fun x ↦ u.val.val x 0
  -- In degree zero, the original coordinate formula is the derivative of a scalar function.
  have hchart (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M) :
      DifferentiableOn ℝ (f ∘ c.symm) c.target ∧
        c.target.EqOn (fderiv ℝ (f ∘ c.symm)) 0 := by
    have hcoeff : differentialFormInChart u.val.val c =
        fun y ↦ constOfIsEmpty ℝ V (Fin 0) (f (c.symm y)) := by
      ext y v
      change u.val.val (c.symm y) _ = u.val.val (c.symm y) 0
      congr 1
      exact Subsingleton.elim _ _
    have hsmooth : ContDiffOn ℝ ∞ (f ∘ c.symm) c.target := by
      have h := (constOfIsEmptyLIE ℝ V ℂ (Fin 0)).symm.contDiff.comp_contDiffOn
        (u.val.property c hc)
      rw [hcoeff] at h
      exact h
    refine ⟨hsmooth.differentiableOn (by simp), ?_⟩
    intro y hy
    have h := smoothFormExteriorDerivative_inChart u.val c hc y hy
    have hu : smoothFormExteriorDerivative 0 u.val = 0 := u.property
    rw [hu] at h
    change 0 = extDeriv (differentialFormInChart u.val.val c) y at h
    rw [hcoeff, extDeriv_constOfIsEmpty] at h
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun z ↦ z (fun _ : Fin 1 ↦ v)) h.symm
  -- Vanishing coordinate derivatives make every fiber open in each original chart.
  intro t
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  let c := chartAt V x
  have hc : c ∈ atlas V M := chart_mem_atlas V x
  have ho : IsOpen (c.target ∩ (f ∘ c.symm) ⁻¹' t) :=
    c.open_target.isOpen_inter_preimage_of_fderiv_eq_zero
      (hchart c hc).1 (hchart c hc).2 t
  refine ⟨c.source ∩ c ⁻¹' (c.target ∩ (f ∘ c.symm) ⁻¹' t), ?_, ?_, ?_⟩
  · intro y hy
    change f y ∈ t
    simpa only [mem_preimage, Function.comp_apply, c.left_inv hy.1] using hy.2.2
  · exact c.continuousOn.isOpen_inter_preimage c.open_source ho
  · exact ⟨mem_chart_source V x, mem_chart_target V x, by
      change f (c.symm (c x)) ∈ t
      rw [c.left_inv (mem_chart_source V x)]
      exact hx⟩

/-- Positive-dimensional spheres have a one-dimensional degree-zero de Rham group. -/
theorem nonempty_deRhamCohomology_sphere_zero_equiv (r : ℕ) (hr : 0 < r) :
    Nonempty (DeRhamCohomology (n := r) (OrthogonalSphere r) 0 ≃ₗ[ℂ] ℂ) := by
  classical
  let S := OrthogonalSphere r
  let V := EuclideanSpace ℝ (Fin r)
  have hdim : 1 < Module.rank ℝ (OrthogonalSphereAmbient r) := by
    rw [← Module.finrank_eq_rank]
    have hd : Module.finrank ℝ (OrthogonalSphereAmbient r) = r + 1 := Fact.out
    rw [hd]
    exact_mod_cast (show 1 < r + 1 by omega)
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere hdim (0 : OrthogonalSphereAmbient r) 1)
  -- The original zero-form tensors realize every scalar as a smooth closed constant.
  let constForm (z : ℂ) : SmoothDifferentialForm (n := r) S 0 :=
    ⟨fun _ ↦ constOfIsEmpty ℝ V (Fin 0) z, by
      intro c hc
      convert (contDiffOn_const : ContDiffOn ℝ ∞
        (fun _ : V ↦ constOfIsEmpty ℝ V (Fin 0) z) c.target) using 1
      ext y v
      rfl⟩
  have hconstantClosed (z : ℂ) : constForm z ∈ deRhamClosedForms (n := r) (M := S) 0 := by
    change smoothFormExteriorDerivative 0 (constForm z) = 0
    apply Subtype.ext
    funext x
    have hspec : (smoothFormExteriorDerivative 0 (constForm z)).val x =
        differentialFormExteriorDerivative (constForm z).val x :=
      (existsUnique_smoothFormExteriorDerivative (n := r) (M := S) 0).exists.choose_spec
        (constForm z) x
    rw [hspec]
    have hcoeff : differentialFormInChart (constForm z).val (chartAt V x) =
        fun _ : V ↦ constOfIsEmpty ℝ V (Fin 0) z := by
      ext y v
      rfl
    dsimp only [differentialFormExteriorDerivative]
    rw [hcoeff]
    have hd : extDeriv (fun _ : V ↦ constOfIsEmpty ℝ V (Fin 0) z) (chartAt V x x) = 0 := by
      simp only [extDeriv, fderiv_const_apply]
      exact map_zero (alternatizeUncurryFinCLM ℝ V ℂ)
    exact congrArg (fun (form : V [⋀^Fin 1]→L[ℝ] ℂ) ↦
      form.compContinuousLinearMap (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (chartAt V x) x)) hd
  -- Connectedness makes evaluation at the specified north pole bijective on closed forms.
  let ev : deRhamClosedForms (n := r) (M := S) 0 →ₗ[ℂ] ℂ :=
    { toFun := fun u ↦ u.val.val (orthogonalSphereNorth r) 0
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hconst (u : deRhamClosedForms (n := r) (M := S) 0) (x : S)
      (v : Fin 0 → TangentSpace 𝓘(ℝ, V) x) : u.val.val x v = ev u := by
    change u.val.val x v = u.val.val (orthogonalSphereNorth r) 0
    have hv : v = 0 := Subsingleton.elim _ _
    rw [hv]
    exact (isLocallyConstant_closedZeroForm u).apply_eq_of_preconnectedSpace
      x (orthogonalSphereNorth r)
  have hbij : Function.Bijective ev := by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      funext x
      ext w
      rw [hconst, hconst, huv]
    · intro z
      exact ⟨⟨constForm z, hconstantClosed z⟩, rfl⟩
  -- There is no incoming differential in degree zero, so the exact subspace is zero.
  let Q := (deRhamExactForms (n := r) (M := S) 0).comap
    (deRhamClosedForms (n := r) (M := S) 0).subtype
  have hQ : Q = ⊥ := by
    ext u
    change u.val = 0 ↔ u = 0
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  exact ⟨(Q.quotEquivOfEqBot hQ).trans (LinearEquiv.ofBijective ev hbij)⟩


/-- Positive-dimensional spheres have a one-dimensional top de Rham group. -/
theorem nonempty_deRhamCohomology_sphere_top_equiv (r : ℕ) (hr : 0 < r) :
    Nonempty (DeRhamCohomology (n := r) (OrthogonalSphere r) r ≃ₗ[ℂ] ℂ) := by
  -- Integration descends through exactly the original closed-form/exact-form quotient.
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hr)
  obtain ⟨e, _⟩ := exists_sphereTopDeRhamIntegral n (orthogonalSphereNorth (n + 1))
  exact ⟨e⟩

set_option maxHeartbeats 2000000 in
-- The actual quotient is computed through the same native chart and compactly supported primitive.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The remaining degrees of positive-dimensional sphere cohomology vanish. -/
theorem subsingleton_deRhamCohomology_sphere (r p : ℕ) (hr : 0 < r)
    (hp0 : p ≠ 0) (hpr : p ≠ r) :
    Subsingleton (DeRhamCohomology (n := r) (OrthogonalSphere r) p) := by
  classical
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  let S := OrthogonalSphere r
  let V := EuclideanSpace ℝ (Fin r)
  let I := 𝓘(ℝ, V)
  by_cases hhigh : r < p
  · -- Above the actual tangent dimension, every alternating tensor is already zero.
    have hform (u : SmoothDifferentialForm (n := r) S p) : u = 0 := by
      apply Subtype.ext
      funext x
      apply ContinuousAlternatingMap.toAlternatingMap_injective
      apply (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.ext_alternating
      intro v hv
      have hcard := Fintype.card_le_of_injective v hv
      simp only [Fintype.card_fin] at hcard
      omega
    let : Subsingleton (SmoothDifferentialForm (n := r) S p) :=
      ⟨fun u v ↦ (hform u).trans (hform v).symm⟩
    infer_instance
  · obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp0
    have hp : p + 1 < r := by omega
    let x₀ : S := orthogonalSphereNorth r
    let c := stereographic' r x₀
    have hc : c ∈ atlas V S := ⟨x₀, rfl⟩
    have htarget : c.target = Set.univ := stereographic'_target x₀
    have hzero (form : deRhamClosedForms (n := r) (M := S) (p + 1)) :
        deRhamClass (n := r) (p + 1) form = 0 := by
      -- Local exactness first gives a cohomologous representative vanishing near the pole.
      obtain ⟨representative, hclass, hnear, hcompact⟩ :=
        exists_sphereDeRhamRepresentative_compactSupport r p form x₀
      let α : V → V [⋀^Fin (p + 1)]→L[ℝ] ℂ :=
        differentialFormInChart representative.val.val c
      have hα : ContDiff ℝ ∞ α :=
        contDiffOn_univ.mp (htarget ▸ representative.val.property c hc)
      have hdα (y : V) : extDeriv α y = 0 := by
        have h := smoothFormExteriorDerivative_inChart representative.val c hc y
          (htarget.symm ▸ Set.mem_univ y)
        have hclosed : smoothFormExteriorDerivative (n := r) (p + 1) representative.val = 0 :=
          representative.property
        rw [hclosed] at h
        exact h.symm.trans (by ext v; rfl)
      -- Compact-support Poincaré exactness gives a primitive that extends through the same chart.
      obtain ⟨η, hη, hηcompact, hdη⟩ :=
        exists_smooth_compactlySupported_euclideanFormPrimitive r p hp α hα hcompact hdα
      obtain ⟨primitive, hcoeff, _, hdoutside⟩ :=
        exists_smoothFormExtension_of_compactSupport p c hc htarget η hη hηcompact
      have hprimitive : smoothFormExteriorDerivative (n := r) p primitive = representative.val := by
        apply Subtype.ext
        funext x
        by_cases hx : x ∈ c.source
        · have h := smoothFormExteriorDerivative_inChart primitive c hc (c x) (c.map_source hx)
          rw [hcoeff, hdη] at h
          have hval (u : SmoothDifferentialForm (n := r) S (p + 1)) :
              (differentialFormInChart u.val c (c x)).compContinuousLinearMap
                (mfderiv I I c x) = u.val x := by
            ext v
            change u.val (c.symm (c x))
              (fun i ↦ mfderiv I I c.symm (c x) (mfderiv I I c x (v i))) = u.val x v
            rw [c.left_inv hx]
            apply congrArg (u.val x)
            funext i
            exact congrArg (fun L ↦ L (v i))
              ((mdifferentiable_of_mem_atlas (I := I) hc).symm_comp_deriv hx)
          have heq := congrArg (fun a : V [⋀^Fin (p + 1)]→L[ℝ] ℂ ↦
            a.compContinuousLinearMap (mfderiv I I c x)) h
          exact (hval _).symm.trans (heq.trans (hval representative.val))
        · have hxx : x = x₀ := by
            simpa only [c, stereographic'_source, Set.mem_compl_iff,
              Set.mem_singleton_iff, not_not] using hx
          rw [hdoutside x hx, hxx]
          exact hnear.self_of_nhds.symm
      -- The primitive lies in the original incoming differential range, hence the class is zero.
      rw [← hclass]
      apply (Submodule.Quotient.eq _).mpr
      change ∃ u : SmoothDifferentialForm (n := r) S p,
        smoothFormExteriorDerivative (n := r) p u = representative.val - 0
      exact ⟨primitive, hprimitive.trans (sub_zero _).symm⟩
    have hall (a : DeRhamCohomology (n := r) S (p + 1)) : a = 0 := by
      obtain ⟨form, rfl⟩ := Submodule.Quotient.mk_surjective
        ((deRhamExactForms (n := r) (M := S) (p + 1)).comap
          (deRhamClosedForms (n := r) (M := S) (p + 1)).subtype) a
      exact hzero form
    exact ⟨fun a b ↦ (hall a).trans (hall b).symm⟩

/-- The orthogonal action on degree-zero sphere cohomology is trivial, including S^0. -/
theorem orthogonalSphereDeRhamRepresentation_zero (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) :
    orthogonalSphereDeRhamRepresentation r 0 A = LinearMap.id := by
  classical
  -- The rank-zero group fixes both components; positive-rank spheres are connected.
  by_cases hr : r = 0
  · subst r
    have hA : A = 1 := Subsingleton.elim _ _
    rw [hA]
    exact (orthogonalSphereDeRhamRepresentation 0 0).map_one
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  let S := OrthogonalSphere r
  have hdim : 1 < Module.rank ℝ (OrthogonalSphereAmbient r) := by
    rw [← Module.finrank_eq_rank]
    have hd : Module.finrank ℝ (OrthogonalSphereAmbient r) = r + 1 := Fact.out
    rw [hd]
    exact_mod_cast (show 1 < r + 1 by omega)
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere hdim (0 : OrthogonalSphereAmbient r) 1)
  -- The actual inverse pullback fixes the scalar value of every closed zero-form.
  have hpull (u : deRhamClosedForms (n := r) (M := S) 0) :
      smoothFormPullback (fun x : S ↦ A⁻¹ • x)
        (contMDiff_orthogonalSphere_smul r A⁻¹) 0 u.val = u.val := by
    apply Subtype.ext
    funext x
    rw [smoothFormPullback_apply]
    ext v
    change u.val.val (A⁻¹ • x) _ = u.val.val x v
    calc
      _ = u.val.val (A⁻¹ • x) 0 := by congr 1; exact Subsingleton.elim _ _
      _ = u.val.val x 0 := (isLocallyConstant_closedZeroForm u).apply_eq_of_preconnectedSpace _ _
      _ = u.val.val x v := by congr 1; exact Subsingleton.elim _ _
  -- Descend that same representative identity through the original de Rham quotient.
  apply LinearMap.ext
  intro a
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective
    ((deRhamExactForms (n := r) (M := S) 0).comap
      (deRhamClosedForms (n := r) (M := S) 0).subtype) a
  change deRhamPullback (fun x : S ↦ A⁻¹ • x)
    (contMDiff_orthogonalSphere_smul r A⁻¹) 0 (deRhamClass 0 u) = deRhamClass 0 u
  rw [deRhamPullback_class _ _ 0 u (by rw [hpull]; exact u.property)]
  congr 1
  apply Subtype.ext
  exact hpull u


set_option maxHeartbeats 2000000 in
-- Compare the same localized classes through the actual integral equivalence and inverse pullback.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The top cohomology action of diag(A,1) is det(A) in every positive dimension. -/
theorem orthogonalSphereDeRhamRepresentation_top (r : ℕ) (hr : 0 < r)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) :
    orthogonalSphereDeRhamRepresentation r r A =
      (A.val.det : ℂ) • LinearMap.id := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hr)
  let S := OrthogonalSphere (n + 1)
  let V := EuclideanSpace ℝ (Fin (n + 1))
  let pole := orthogonalSphereNorth (n + 1)
  let f : S → S := fun x ↦ A⁻¹ • x
  have hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) ∞ f :=
    contMDiff_orthogonalSphere_smul (n + 1) A⁻¹
  obtain ⟨e, he⟩ := exists_sphereTopDeRhamIntegral n pole
  have hdetInv : (A⁻¹).val.det = A.val.det := by
    change A.val.conjTranspose.det = A.val.det
    rw [Matrix.det_conjTranspose, star_trivial]
  apply LinearMap.ext
  intro a
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective
    ((deRhamExactForms (n := n + 1) (M := S) (n + 1)).comap
      (deRhamClosedForms (n := n + 1) (M := S) (n + 1)).subtype) a
  -- Use the same localized original representative on both sides of the inverse-pullback action.
  obtain ⟨v, hv, hnear, _⟩ := exists_sphereDeRhamRepresentative_compactSupport (n + 1) n u pole
  change deRhamPullback f hf (n + 1) (deRhamClass (n + 1) u) =
    (A.val.det : ℂ) • deRhamClass (n + 1) u
  rw [← hv]
  have hclosed : smoothFormPullback f hf (n + 1) v.val ∈
      deRhamClosedForms (n := n + 1) (M := S) (n + 1) := by
    change smoothFormExteriorDerivative (n := n + 1) (n + 1)
      (smoothFormPullback f hf (n + 1) v.val) = 0
    have h := LinearMap.congr_fun (smoothFormExteriorDerivative_pullback f hf (n + 1)) v.val
    change smoothFormExteriorDerivative (n := n + 1) (n + 1)
      (smoothFormPullback f hf (n + 1) v.val) =
        smoothFormPullback f hf (n + 2)
          (smoothFormExteriorDerivative (n := n + 1) (n + 1) v.val) at h
    rw [show smoothFormExteriorDerivative (n := n + 1) (n + 1) v.val = 0 from v.property,
      _root_.map_zero] at h
    exact h
  let w : deRhamClosedForms (n := n + 1) (M := S) (n + 1) :=
    ⟨smoothFormPullback f hf (n + 1) v.val, hclosed⟩
  have hwnear : ∀ᶠ x in 𝓝 pole, w.val.val x = 0 := by
    have ht : Filter.Tendsto f (𝓝 pole) (𝓝 pole) := by
      have h := hf.continuous.continuousAt (x := pole)
      change Filter.Tendsto f (𝓝 pole) (𝓝 (A⁻¹ • orthogonalSphereNorth (n + 1))) at h
      rw [smul_orthogonalSphereNorth] at h
      exact h
    filter_upwards [ht.eventually hnear] with x hx
    change (smoothFormPullback f hf (n + 1) v.val).val x = 0
    rw [smoothFormPullback_apply, hx]
    ext z
    rfl
  change deRhamPullback f hf (n + 1) (deRhamClass (n + 1) v) =
    (A.val.det : ℂ) • deRhamClass (n + 1) v
  rw [deRhamPullback_class f hf (n + 1) v hclosed]
  -- The native-chart change of variables has sign det(A inverse) = det(A).
  apply e.injective
  calc
    e (deRhamClass (n + 1) w) = euclideanTopFormIntegral (n + 1)
        (differentialFormInChart w.val.val (stereographic' (n + 1) pole)) := he w hwnear
    _ = ((A⁻¹).val.det : ℂ) * euclideanTopFormIntegral (n + 1)
        (differentialFormInChart v.val.val (stereographic' (n + 1) pole)) :=
      euclideanTopFormIntegral_spherePullback (n + 1) A⁻¹ v.val
    _ = e ((A.val.det : ℂ) • deRhamClass (n + 1) v) := by
      rw [hdetInv, ← he v hnear, e.map_smul]
      rfl

/-- The two-point sphere has two independent degree-zero classes. -/
theorem nonempty_deRhamCohomology_zeroSphere_equiv :
    Nonempty (DeRhamCohomology (n := 0) (OrthogonalSphere 0) 0 ≃ₗ[ℂ] (ℂ × ℂ)) := by
  /- Evaluate a zero-form separately at the north and south point. Every
  function on this discrete two-point manifold is smooth and closed, and
  the exact degree-zero subspace is zero. These evaluations give the actual
  linear equivalence without identifying the two components. -/
  classical
  let X := OrthogonalSphere 0
  let V := EuclideanSpace ℝ (Fin 0)
  let north : X := orthogonalSphereNorth 0
  let south : X := ⟨WithLp.toLp 2 ((0 : V), (-1 : ℝ)), by simp⟩
  have hns : north ≠ south := by
    intro h
    have heq := congrArg (fun x : X ↦ x.val.snd) h
    norm_num [north, south, orthogonalSphereNorth] at heq
  have hpoints (x : X) : x = north ∨ x = south := by
    have hf : x.val.fst = 0 := Subsingleton.elim (α := V) _ _
    have hn : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have hs : x.val.snd ^ 2 = 1 := by
      have h := WithLp.prod_norm_sq_eq_of_L2 x.val
      rw [hn, hf, norm_zero] at h
      simpa only [Real.norm_eq_abs, sq_abs, zero_pow (by decide : 2 ≠ 0), zero_add,
        one_pow] using h.symm
    have hs' : x.val.snd = 1 ∨ x.val.snd = -1 := by
      have hmul : (x.val.snd - 1) * (x.val.snd + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hmul with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hs' with h | h
    · left
      apply Subtype.ext
      apply (WithLp.equiv 2 _).injective
      exact Prod.ext hf h
    · right
      apply Subtype.ext
      apply (WithLp.equiv 2 _).injective
      exact Prod.ext hf h
  -- Positive-degree tangent tensors vanish, so every zero-form is closed.
  have h1 (a : SmoothDifferentialForm (n := 0) X 1) : a = 0 := by
    apply Subtype.ext
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    apply (a.val x).map_coord_zero (0 : Fin 1)
    exact Subsingleton.elim (α := V) (v 0) 0
  let form (z : ℂ × ℂ) : SmoothDifferentialForm (n := 0) X 0 :=
    ⟨fun x ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ
      (TangentSpace 𝓘(ℝ, V) x) (Fin 0) (if x = north then z.1 else z.2), by
        intro c hc
        have hconst : differentialFormInChart (n := 0)
            (fun x ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ
              (TangentSpace 𝓘(ℝ, V) x) (Fin 0) (if x = north then z.1 else z.2)) c =
            fun _ ↦ differentialFormInChart (n := 0)
              (fun x ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ
                (TangentSpace 𝓘(ℝ, V) x) (Fin 0) (if x = north then z.1 else z.2)) c 0 := by
          funext y
          exact congrArg _ (Subsingleton.elim (α := V) y 0)
        rw [hconst]
        exact contDiffOn_const⟩
  let eF : deRhamClosedForms (n := 0) (M := X) 0 ≃ₗ[ℂ] (ℂ × ℂ) :=
    { toFun := fun a ↦ (a.val.val north 0, a.val.val south 0)
      invFun := fun z ↦ ⟨form z, h1 _⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply Subtype.ext
        funext x
        apply ContinuousAlternatingMap.ext
        intro v
        have hv : v = 0 := Subsingleton.elim _ _
        rcases hpoints x with rfl | rfl
        · simp [form, hv]
        · simp [form, hv, Ne.symm hns]
      right_inv := by
        intro z
        simp [form, Ne.symm hns]
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  -- No exact form enters degree zero in the original quotient.
  let Q := (deRhamExactForms (n := 0) (M := X) 0).comap
    (deRhamClosedForms (n := 0) (M := X) 0).subtype
  have hQ : Q = ⊥ := by
    ext a
    simp [Q, deRhamExactForms]
  exact ⟨(Q.quotEquivOfEqBot hQ).trans eF⟩

/-- All positive-degree de Rham groups of the zero-sphere vanish. -/
theorem subsingleton_deRhamCohomology_zeroSphere (p : ℕ) (hp : p ≠ 0) :
    Subsingleton (DeRhamCohomology (n := 0) (OrthogonalSphere 0) p) := by
  /- Every tangent space is zero. A positive-degree alternating multilinear
  form is zero, so both the closed-form space and its quotient are trivial. -/
  -- Every positive-degree tensor vanishes because every tangent vector is zero.
  have hp' : 0 < p := Nat.pos_of_ne_zero hp
  let i : Fin p := ⟨0, hp'⟩
  have hform (u : SmoothDifferentialForm (n := 0) (OrthogonalSphere 0) p) : u = 0 := by
    apply Subtype.ext
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    apply (u.val x).map_coord_zero i
    change (v i : EuclideanSpace ℝ (Fin 0)) = 0
    exact Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0)) (v i) 0
  let : Subsingleton (SmoothDifferentialForm (n := 0) (OrthogonalSphere 0) p) :=
    ⟨fun u v ↦ (hform u).trans (hform v).symm⟩
  -- Closed forms and their original quotient inherit this vanishing.
  infer_instance

end AtiyahSinger
