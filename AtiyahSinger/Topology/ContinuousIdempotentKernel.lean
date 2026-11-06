/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.IdempotentHomotopy
public import AtiyahSinger.Topology.ModelBundleTopology

/-!
# Kernels of continuous bundle projections

Public module ID: M1744.

The kernel of a continuous idempotent endomorphism of a finite-dimensional
native complex vector bundle is locally a vector bundle in its original
subspace topology. In one original chart, the standard nearby-idempotent
intertwiner gives local linear identifications of the kernels. The proof
retains the original fiber norms and needs no metric or separation of the base.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X : Type*} [TopologicalSpace X]
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace V E)] [FiberBundle V E] [VectorBundle ℂ V E]
  (P : ∀ x : X, E x →L[ℂ] E x)

/-- The kernel consists of the original vectors killed by the specified endomorphism. -/
abbrev IdempotentKernel (x : X) : Type _ := LinearMap.ker (P x).toLinearMap

/-- The kernel total space has the subspace topology of the original native bundle. -/
@[reducible]
def idempotentKernelTopology : TopologicalSpace (TotalSpace Unit (IdempotentKernel E P)) :=
  TopologicalSpace.induced
    (fun z : TotalSpace Unit (IdempotentKernel E P) ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace V E)) inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A continuous idempotent has a locally finite-rank kernel with the original subspace topology. -/
theorem isFiniteRank_idempotentKernel
    (hP : Continuous (fun x ↦ (⟨x, P x⟩ : TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x))))
    (hPP : ∀ x, (P x).comp (P x) = P x) :
    let := idempotentKernelTopology V E P
    IsFiniteRank (IdempotentKernel E P) := by
  classical
  let := idempotentKernelTopology V E P
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  constructor
  intro x₀
  let e := trivializationAt V E x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt V E x₀
  let A (x : X) : V →L[ℂ] V :=
    (e.continuousLinearMapAt ℂ x).comp ((P x).comp (e.symmL ℂ x))
  have hA : ContinuousOn A e.baseSet := by
    let t := e.continuousLinearMap (RingHom.id ℂ) e
    exact (t.continuousOn.comp hP.continuousOn
      (fun x hx ↦ t.mem_source.mpr ⟨hx, hx⟩)).snd
  have hAA (x : X) (hx : x ∈ e.baseSet) : A x * A x = A x := by
    apply ContinuousLinearMap.ext
    intro v
    change e.continuousLinearMapAt ℂ x
      (P x (e.symmL ℂ x (e.continuousLinearMapAt ℂ x (P x (e.symmL ℂ x v))))) = _
    rw [e.symmL_continuousLinearMapAt hx]
    exact congrArg (e.continuousLinearMapAt ℂ x) (DFunLike.congr_fun (hPP x) (e.symmL ℂ x v))
  let T (x : X) : V →L[ℂ] V := idempotentIntertwiner (A x) (A x₀)
  have hT : ContinuousOn T e.baseSet := by
    dsimp only [T, idempotentIntertwiner]
    fun_prop
  have hT₀ : T x₀ = 1 := by
    dsimp only [T, idempotentIntertwiner]
    noncomm_ring [hAA x₀ hx₀]
  let U : Set X := e.baseSet ∩ {x | ‖T x - 1‖ < 1}
  have hU : IsOpen U :=
    ((hT.sub continuousOn_const).norm).isOpen_inter_preimage e.open_baseSet isOpen_Iio
  have hxU : x₀ ∈ U := by
    refine ⟨hx₀, ?_⟩
    change ‖T x₀ - 1‖ < 1
    rw [hT₀, sub_self, norm_zero]
    exact zero_lt_one
  have hunit (x : X) (hx : x ∈ U) : IsUnit (T x) :=
    isUnit_idempotentIntertwiner_of_norm_lt (A x) (A x₀) hx.2
  let L (x : X) : V →L[ℂ] V := Ring.inverse (T x)
  have hLT (x : X) (hx : x ∈ U) : L x * T x = 1 :=
    Ring.inverse_mul_cancel (T x) (hunit x hx)
  have hTL (x : X) (hx : x ∈ U) : T x * L x = 1 :=
    Ring.mul_inverse_cancel (T x) (hunit x hx)
  have hL : ContinuousOn L U := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_iff_continuousAt.mpr
    intro x
    obtain ⟨u, hu⟩ := hunit x.val x.property
    have hinv := NormedRing.inverse_continuousAt u
    rw [hu] at hinv
    exact hinv.comp_of_eq ((hT.comp_continuous continuous_subtype_val
      (fun x : U ↦ x.property.1)).continuousAt) rfl
  have hcomm (x : X) (hx : x ∈ U) : T x * A x₀ = A x * T x :=
    idempotentIntertwiner_mul (A x) (A x₀) (hAA x hx.1) (hAA x₀ hx₀)
  have hcommInv (x : X) (hx : x ∈ U) : A x₀ * L x = L x * A x := by
    calc
      _ = (L x * T x) * A x₀ * L x := by rw [hLT x hx, one_mul]
      _ = L x * (T x * A x₀) * L x := by noncomm_ring
      _ = L x * (A x * T x) * L x := by rw [hcomm x hx]
      _ = L x * A x * (T x * L x) := by noncomm_ring
      _ = _ := by rw [hTL x hx, mul_one]
  -- The complementary projections totalize the coordinate maps outside the chart domain.
  let K₀ := LinearMap.ker (A x₀).toLinearMap
  let correction (x : X) : E x →ₗ[ℂ] IdempotentKernel E P x :=
    (LinearMap.id - (P x).toLinearMap).codRestrict _ (by
      intro v
      change P x (v - P x v) = 0
      have hp : P x (P x v) = P x v := DFunLike.congr_fun (hPP x) v
      rw [map_sub, hp, sub_self])
  let correction₀ : V →ₗ[ℂ] K₀ :=
    (LinearMap.id - (A x₀).toLinearMap).codRestrict _ (by
      intro v
      change A x₀ (v - A x₀ v) = 0
      have hp : A x₀ (A x₀ v) = A x₀ v := DFunLike.congr_fun (hAA x₀ hx₀) v
      rw [map_sub, hp, sub_self])
  let back (x : X) : E x →ₗ[ℂ] K₀ :=
    correction₀.comp ((L x).toLinearMap.comp (e.continuousLinearMapAt ℂ x).toLinearMap)
  let front (x : X) : K₀ →ₗ[ℂ] IdempotentKernel E P x :=
    (correction x).comp ((e.symmL ℂ x).toLinearMap.comp
      ((T x).toLinearMap.comp K₀.subtype))
  have hback (x : X) (hx : x ∈ U) (v : IdempotentKernel E P x) :
      (back x v.val).val = L x (e.continuousLinearMapAt ℂ x v.val) := by
    have hz : A x (e.continuousLinearMapAt ℂ x v.val) = 0 := by
      change e.continuousLinearMapAt ℂ x
        (P x (e.symmL ℂ x (e.continuousLinearMapAt ℂ x v.val))) = 0
      have hv : P x v.val = 0 := v.property
      rw [e.symmL_continuousLinearMapAt hx.1, hv, map_zero]
    have hc := DFunLike.congr_fun (hcommInv x hx) (e.continuousLinearMapAt ℂ x v.val)
    change A x₀ (L x (e.continuousLinearMapAt ℂ x v.val)) =
      L x (A x (e.continuousLinearMapAt ℂ x v.val)) at hc
    change L x (e.continuousLinearMapAt ℂ x v.val) -
      A x₀ (L x (e.continuousLinearMapAt ℂ x v.val)) = _
    rw [hc, hz, map_zero, sub_zero]
  have hfront (x : X) (hx : x ∈ U) (v : K₀) :
      e.continuousLinearMapAt ℂ x (front x v).val = T x v.val := by
    have hc := DFunLike.congr_fun (hcomm x hx) v.val
    change T x (A x₀ v.val) = A x (T x v.val) at hc
    have hz : A x (T x v.val) = 0 := by
      have hv : A x₀ v.val = 0 := v.property
      rw [← hc, hv, map_zero]
    change e.continuousLinearMapAt ℂ x
      (e.symmL ℂ x (T x v.val) - P x (e.symmL ℂ x (T x v.val))) = _
    rw [map_sub, e.continuousLinearMapAt_symmL hx.1]
    exact sub_eq_self.mpr hz
  have hfrontback (x : X) (hx : x ∈ U) (v : IdempotentKernel E P x) :
      front x (back x v.val) = v := by
    apply Subtype.ext
    have hc : e.continuousLinearMapAt ℂ x (front x (back x v.val)).val =
        e.continuousLinearMapAt ℂ x v.val := by
      rw [hfront x hx, hback x hx]
      exact DFunLike.congr_fun (hTL x hx) (e.continuousLinearMapAt ℂ x v.val)
    have hs := congrArg (e.symmL ℂ x) hc
    rwa [e.symmL_continuousLinearMapAt hx.1, e.symmL_continuousLinearMapAt hx.1] at hs
  have hbackfront (x : X) (hx : x ∈ U) (v : K₀) :
      back x (front x v).val = v := by
    apply Subtype.ext
    rw [hback x hx, hfront x hx]
    exact DFunLike.congr_fun (hLT x hx) v.val
  -- Check both chart maps in the original induced total-space topology.
  have hinc : Continuous (fun z : TotalSpace Unit (IdempotentKernel E P) ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace V E)) := continuous_induced_dom
  have hb : Continuous (fun z : TotalSpace Unit (IdempotentKernel E P) ↦ z.proj) :=
    (FiberBundle.continuous_proj V E).comp hinc
  let source := (π Unit (IdempotentKernel E P)) ⁻¹' U
  have hcoords : ContinuousOn (fun z : TotalSpace Unit (IdempotentKernel E P) ↦
      e.continuousLinearMapAt ℂ z.proj z.snd.val) source := by
    have hc : ContinuousOn (fun z : TotalSpace Unit (IdempotentKernel E P) ↦
        (e (⟨z.proj, z.snd.val⟩ : TotalSpace V E)).2) source :=
      (e.continuousOn.comp hinc.continuousOn
        (fun z hz ↦ e.mem_source.mpr (show z.proj ∈ U from hz).1)).snd
    exact hc.congr (fun z hz ↦ e.continuousLinearMapAt_apply_of_mem ℂ hz.1 _)
  have hbackContinuous : ContinuousOn (fun z : TotalSpace Unit (IdempotentKernel E P) ↦
      back z.proj z.snd.val) source := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    change ContinuousOn (fun z : TotalSpace Unit (IdempotentKernel E P) ↦
      L z.proj (e.continuousLinearMapAt ℂ z.proj z.snd.val) -
        A x₀ (L z.proj (e.continuousLinearMapAt ℂ z.proj z.snd.val))) source
    have hc := (hL.comp hb.continuousOn (fun z hz ↦ hz)).clm_apply hcoords
    exact hc.sub ((A x₀).continuous.comp_continuousOn hc)
  have hfrontContinuous : ContinuousOn (fun z : X × K₀ ↦
      (⟨z.1, front z.1 z.2⟩ : TotalSpace Unit (IdempotentKernel E P))) (U ×ˢ Set.univ) := by
    have hi : Topology.IsInducing
        (fun z : TotalSpace Unit (IdempotentKernel E P) ↦
          (⟨z.proj, z.snd.val⟩ : TotalSpace V E)) := ⟨rfl⟩
    apply hi.continuousOn_iff.mpr
    have hc : ContinuousOn (fun z : X × K₀ ↦ T z.1 z.2.val) (U ×ˢ Set.univ) :=
      (hT.comp continuous_fst.continuousOn (fun z hz ↦ hz.1.1)).clm_apply
        (continuous_subtype_val.comp continuous_snd).continuousOn
    have hraw := e.continuousOn_symm.comp
      (continuous_fst.continuousOn.prodMk hc) (fun z hz ↦ ⟨hz.1.1, Set.mem_univ _⟩)
    apply hraw.congr
    intro z hz
    have hcoord : e (⟨z.1, (front z.1 z.2).val⟩ : TotalSpace V E) =
        (z.1, T z.1 z.2.val) := by
      apply Prod.ext
      · exact e.proj_toFun _ (e.mem_source.mpr hz.1.1)
      · exact (e.continuousLinearMapAt_apply_of_mem ℂ hz.1.1 _).symm.trans
          (hfront z.1 hz.1 z.2)
    exact congrArg (fun v : E z.1 ↦ (⟨z.1, v⟩ : TotalSpace V E))
      ((e.symm_apply_apply_mk hz.1.1 (front z.1 z.2).val).symm.trans
        (congrArg (e.symm z.1) (congrArg Prod.snd hcoord)))
  let t : Trivialization K₀ (π Unit (IdempotentKernel E P)) :=
    { toFun := fun z ↦ (z.proj, back z.proj z.snd.val)
      invFun := fun z ↦ ⟨z.1, front z.1 z.2⟩
      source := source
      target := U ×ˢ Set.univ
      baseSet := U
      open_source := hU.preimage hb
      open_target := hU.prod isOpen_univ
      open_baseSet := hU
      map_source' := fun _ hz ↦ ⟨hz, Set.mem_univ _⟩
      map_target' := fun _ hz ↦ hz.1
      left_inv' := fun z hz ↦ TotalSpace.ext rfl (heq_of_eq (hfrontback z.proj hz z.snd))
      right_inv' := fun z hz ↦ Prod.ext rfl (hbackfront z.1 hz.1 z.2)
      continuousOn_toFun := hb.continuousOn.prodMk hbackContinuous
      continuousOn_invFun := hfrontContinuous
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  let c : K₀ ≃L[ℂ] (Fin (Module.finrank ℂ K₀) → ℂ) :=
    (Module.finBasis ℂ K₀).equivFun.toContinuousLinearEquiv
  refine ⟨Module.finrank ℂ K₀, t.transFiberHomeomorph c.toHomeomorph, hxU, ?_⟩
  intro x hx
  constructor
  · intro v w
    change c (back x (v.val + w.val)) = c (back x v.val) + c (back x w.val)
    rw [map_add, map_add]
  · intro a v
    change c (back x (a • v.val)) = a • c (back x v.val)
    rw [map_smul, map_smul]

end AtiyahSinger.ComplexBundle
