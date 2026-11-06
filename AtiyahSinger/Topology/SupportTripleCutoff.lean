/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportTripleHomotopy

/-!
# Global cutoff maps of a compact-support triple

Public module ID: M2192.

SG Appendix C.1 forms the graded tensor product after extending the boundary
maps over the compact control. For the noncompact Thom construction of C.13
and Karoubi IV.1.10, the input bundles need not carry global Hermitian metrics.
We instead multiply the original boundary isomorphism and its inverse by the
same interval-valued cutoff, zero on an open neighborhood of the control.
Both maps extend by zero, and their two composites are the cutoff squared
times the identity. Where the cutoff equals one they retain the original
boundary map and its actual inverse.

This reciprocal cutoff realization is a project supplement to the standard
graded tensor product construction. It replaces an auxiliary adjoint by the
given inverse, without assuming a global metric on an arbitrary bundle over
a locally compact Hausdorff space. It is intended for tensoring with the
specified exterior symbol whose square is minus the fiber norm squared.

The cutoff is supplied explicitly. Its existing existence theorem is
`exists_time_cutoff`; local compactness is needed there, not for the formulas
or their continuity once the cutoff is given. The formulas below retain
the original boundary and its inverse on the exterior.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

open scoped Classical in
/-- Multiply the given boundary map by the cutoff and set it to zero on the control. -/
def CompactSupportTriple.cutoffLinearMap (a : CompactSupportTriple E F)
    (ρ : C(X, I)) (x : X) : E x →ₗ[ℂ] F x :=
  if hx : x ∈ a.control then 0 else
    (((ρ x : ℝ) : ℂ)) • (a.boundary.linearEquiv ⟨x, hx⟩).toLinearMap

variable [T2Space X] [IsFiniteRank E] [IsFiniteRank F]

set_option backward.isDefEq.respectTransparency.types false in
/-- Vanishing near the compact control makes the prescribed extension continuous. -/
theorem CompactSupportTriple.continuous_cutoffLinearMap (a : CompactSupportTriple E F)
    (ρ : C(X, I)) (U : Set X) (hU : IsOpen U) (hcontrol : a.control ⊆ U)
    (hρ : ∀ x ∈ U, ρ x = 0) :
    Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, a.cutoffLinearMap ρ z.proj z.snd⟩ : TotalSpace Unit F)) := by
  /- Stage 1: the compact control is closed because X is Hausdorff. Its open
  complement and U cover X, hence their projection preimages cover the source
  total space. On U the specified formula is zero in every fiber, including
  points of U outside the control. The continuous zero section of F, composed
  with the projection of E, proves continuity on this part.
  Stage 2: on the control complement, the formula is the original continuous
  boundary map multiplied by the continuous scalar rho. Local finite linear
  charts make this scalar action jointly continuous on the same total topology.
  The two local formulas agree on the overlap because rho is zero there.
  Stage 3: glue over this actual open cover. No extension of a bundle across a
  compactification, global Hermitian metric, or paracompactness is used. -/
  classical
  -- Scalar multiplication is continuous in the original finite bundle charts.
  have hsmul : Continuous (fun p : ℂ × TotalSpace Unit F ↦
      (⟨p.2.proj, p.1 • p.2.snd⟩ : TotalSpace Unit F)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    obtain ⟨r, e, he, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := F) p.2.proj
    apply e.continuousAt_of_comp_left
      (f := fun q : ℂ × TotalSpace Unit F ↦ ⟨q.2.proj, q.1 • q.2.snd⟩)
      ((continuous_proj (E := F)).comp continuous_snd).continuousAt he
    have hcoord := ((e.toOpenPartialHomeomorph.continuousAt
      (e.mem_source.mpr he)).comp continuousAt_snd).snd
    apply (((continuous_proj (E := F)).comp continuous_snd).continuousAt.prodMk
      (continuousAt_fst.smul hcoord)).congr_of_eventuallyEq
    filter_upwards [(e.open_baseSet.preimage
      ((continuous_proj (E := F)).comp continuous_snd)).mem_nhds he] with q hq
    exact Prod.ext (e.proj_toFun _ (e.mem_source.mpr hq))
      ((hlinear q.2.proj hq).map_smul q.1 q.2.snd)
  -- On the exterior, use the original boundary through its native restriction topology.
  let R : Set (TotalSpace Unit E) := {z | z.proj ∉ a.control}
  let base (z : R) : (a.controlᶜ : Set X) := ⟨z.val.proj, z.property⟩
  have hbase : Continuous base :=
    ((continuous_proj (E := E)).comp continuous_subtype_val).subtype_mk _
  let restricted (z : R) : TotalSpace Unit (Restrict E a.controlᶜ) :=
    ⟨base z, z.val.snd⟩
  have hrestricted : Continuous restricted := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E
      (Subtype.val : (a.controlᶜ : Set X) → X)).continuous_iff]
    exact hbase.prodMk continuous_subtype_val
  have hout := (Pullback.continuous_lift Unit F
    (Subtype.val : (a.controlᶜ : Set X) → X)).comp
      (a.boundary.continuous_total.comp hrestricted)
  have hscalar : Continuous (fun z : R ↦ ((ρ z.val.proj : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp
      (ρ.continuous.comp ((continuous_proj (E := E)).comp continuous_subtype_val)))
  have hexterior : ContinuousOn (fun z : TotalSpace Unit E ↦
      (⟨z.proj, a.cutoffLinearMap ρ z.proj z.snd⟩ : TotalSpace Unit F)) R := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply (hsmul.comp (hscalar.prodMk hout)).congr
    intro z
    change (⟨z.val.proj, ((ρ z.val.proj : ℝ) : ℂ) •
      a.boundary.linearEquiv (base z) z.val.snd⟩ : TotalSpace Unit F) =
        ⟨z.val.proj, a.cutoffLinearMap ρ z.val.proj z.val.snd⟩
    simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right z.property]
    rfl
  -- Near the control the formula is identically the original zero section.
  have hzero (x : X) (hx : x ∈ U) (v : E x) : a.cutoffLinearMap ρ x v = 0 := by
    by_cases hxc : x ∈ a.control
    · simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_left hxc, LinearMap.zero_apply]
    · dsimp only [CompactSupportTriple.cutoffLinearMap]
      rw [dite_eq_right hxc]
      change ((ρ x : ℝ) : ℂ) • a.boundary.linearEquiv ⟨x, hxc⟩ v = 0
      rw [hρ x hx]
      simp
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z.proj ∈ U
  · apply ((continuous_zero_section F).comp (continuous_proj (E := E))).continuousAt
      |>.congr_of_eventuallyEq
    filter_upwards [(hU.preimage (continuous_proj (E := E))).mem_nhds hz] with w hw
    exact congrArg (TotalSpace.mk w.proj) (hzero w.proj hw w.snd)
  · have hzc : z.proj ∉ a.control := fun h ↦ hz (hcontrol h)
    exact hexterior.continuousAt
      ((a.isCompact_control.isClosed.isOpen_compl.preimage
        (continuous_proj (E := E))).mem_nhds hzc)

/-- The global bundle map has exactly the zero-extended cutoff fiber formula. -/
def CompactSupportTriple.cutoffHom (a : CompactSupportTriple E F)
    (ρ : C(X, I)) (U : Set X) (hU : IsOpen U) (hcontrol : a.control ⊆ U)
    (hρ : ∀ x ∈ U, ρ x = 0) : Hom E F where
  linearMap := a.cutoffLinearMap ρ
  continuous_total := a.continuous_cutoffLinearMap ρ U hU hcontrol hρ

set_option backward.isDefEq.respectTransparency.types false in
/-- Using the same cutoff on the inverse gives the same nonnegative scalar in both orders. -/
theorem CompactSupportTriple.cutoffHom_inverse_comp (a : CompactSupportTriple E F)
    (ρ : C(X, I)) (U : Set X) (hU : IsOpen U) (hcontrol : a.control ⊆ U)
    (hρ : ∀ x ∈ U, ρ x = 0) (x : X) :
    ((a.inverse.cutoffHom ρ U hU hcontrol hρ).linearMap x).comp
        ((a.cutoffHom ρ U hU hcontrol hρ).linearMap x) =
      (((ρ x : ℝ) : ℂ) ^ 2) • (LinearMap.id : E x →ₗ[ℂ] E x) ∧
    ((a.cutoffHom ρ U hU hcontrol hρ).linearMap x).comp
        ((a.inverse.cutoffHom ρ U hU hcontrol hρ).linearMap x) =
      (((ρ x : ℝ) : ℂ) ^ 2) • (LinearMap.id : F x →ₗ[ℂ] F x) := by
  /- Stage 1: inside the control, containment in U makes rho zero. Both cutoff
  maps are the zero map, so both composites and both scalar identities vanish.
  This does not require the two fiber ranks to agree on the control.
  Stage 2: outside the control, the two maps are rho times the original boundary
  equivalence and rho times its actual inverse. Complex linearity extracts the
  two scalar factors; the two inverse laws give identity in the respective
  source and target fibers. The same rho produces rho squared in both orders. -/
  classical
  by_cases hx : x ∈ a.control
  · -- The same cutoff vanishes on the control even when the two ranks differ there.
    have hzero : ρ x = 0 := hρ x (hcontrol hx)
    constructor <;> ext v <;>
      simp [CompactSupportTriple.cutoffHom, CompactSupportTriple.cutoffLinearMap,
        CompactSupportTriple.inverse, hx, hzero]
  · -- Both compositions use the original boundary inverse and the same scalar twice.
    constructor
    · apply LinearMap.ext
      intro v
      change a.inverse.cutoffLinearMap ρ x (a.cutoffLinearMap ρ x v) = _
      simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
        dite_eq_right hx]
      change ((ρ x : ℝ) : ℂ) • (a.boundary.linearEquiv ⟨x, hx⟩).symm
        (((ρ x : ℝ) : ℂ) • a.boundary.linearEquiv ⟨x, hx⟩ v) =
          (((ρ x : ℝ) : ℂ) ^ 2) • v
      rw [map_smul, LinearEquiv.symm_apply_apply, smul_smul, pow_two]
      rfl
    · apply LinearMap.ext
      intro v
      change a.cutoffLinearMap ρ x (a.inverse.cutoffLinearMap ρ x v) = _
      simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
        dite_eq_right hx]
      change ((ρ x : ℝ) : ℂ) • a.boundary.linearEquiv ⟨x, hx⟩
        (((ρ x : ℝ) : ℂ) • (a.boundary.linearEquiv ⟨x, hx⟩).symm v) =
          (((ρ x : ℝ) : ℂ) ^ 2) • v
      rw [map_smul, LinearEquiv.apply_symm_apply, smul_smul, pow_two]
      rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Where the cutoff equals one, both global maps are the prescribed boundary maps. -/
theorem CompactSupportTriple.cutoffHom_boundary (a : CompactSupportTriple E F)
    (ρ : C(X, I)) (U : Set X) (hU : IsOpen U) (hcontrol : a.control ⊆ U)
    (hρ : ∀ x ∈ U, ρ x = 0) (x : (a.controlᶜ : Set X)) (hx : ρ x = 1) :
    (a.cutoffHom ρ U hU hcontrol hρ).linearMap x =
        (a.boundary.linearEquiv x).toLinearMap ∧
      (a.inverse.cutoffHom ρ U hU hcontrol hρ).linearMap x =
        (a.boundary.linearEquiv x).symm.toLinearMap := by
  /- The exterior point selects the nonzero-control branch in each definition.
  The same interval equality rho(x)=1 makes both scalar factors one. The
  inverse triple has the original control and inverse boundary equivalence,
  so the second equality retains that specified inverse, without a new choice. -/
  classical
  have hxc : (x : X) ∉ a.control := x.property
  constructor
  · change a.cutoffLinearMap ρ x = _
    dsimp only [CompactSupportTriple.cutoffLinearMap]
    rw [dite_eq_right hxc, hx]
    change (1 : ℂ) • (a.boundary.linearEquiv x).toLinearMap = _
    rw [one_smul]
  · change a.inverse.cutoffLinearMap ρ x = _
    dsimp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse]
    rw [dite_eq_right hxc, hx]
    change (1 : ℂ) • (a.boundary.linearEquiv x).symm.toLinearMap = _
    rw [one_smul]

end AtiyahSinger.ComplexBundle
