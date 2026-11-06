/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.VerticalCotangentBundle
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.VectorBundle.Constructions

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Horizontal lifts and the actual cotangent splitting

Public module ID: M1467.

A smooth horizontal lift is a smooth linear right inverse of the original
submersion differential. For such a lift h, the splitting sends a covector xi
to (xi after h, xi restricted to ker df). Both factors retain their native
pullback and Hom-bundle topologies, with the same selected vertical atlas.

SG III.13, p.251, obtains this splitting from a metric on the total space.
A metric supplies a horizontal complement orthogonal to ker df. The standard
smooth partition-of-unity splitting used here supplies a possibly different
horizontal lift under the same compact-manifold hypotheses, and also applies
to Hausdorff paracompact total spaces. The independence statement compares
given lifts without imposing any extra global hypothesis on their existence.

The quotient in the book is identified with the vertical cotangent in the
preceding exact sequence. It is never silently treated as the vertical tangent.
The splitting and proper independence statements are proved for the supplied lifts.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff unitInterval

attribute [local instance] verticalTangentTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)

/-- A smooth horizontal lift, expressed as a right inverse of the original differential. -/
structure SmoothHorizontalLift where
  /-- Lift an actual base tangent vector to the original tangent fiber upstairs. -/
  lift : ∀ x : M, TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] TangentSpace 𝓘(ℝ, E) x
  /-- Smoothness uses the original pulled tangent bundle and original tangent total space. -/
  contMDiff_lift :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z : TotalSpace F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))) ↦
        (⟨z.proj, lift z.proj z.snd⟩ : TangentBundle 𝓘(ℝ, E) M))
  /-- The original differential sends each lifted vector back to that same vector. -/
  right_inv : ∀ x : M, Function.RightInverse (lift x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)

/-- A horizontal lift selected from smooth splitting over a Hausdorff paracompact source. -/
def smoothHorizontalLift [T2Space M] [ParacompactSpace M]
    (hf : Manifold.IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) : SmoothHorizontalLift f where
  lift := (exists_smooth_horizontalLift f hf).choose
  contMDiff_lift := (exists_smooth_horizontalLift f hf).choose_spec.1
  right_inv := (exists_smooth_horizontalLift f hf).choose_spec.2

local notation "V" => VerticalTangentModel E F
local notation "C" => fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ
local notation "B" => ((f : M → N) *ᵖ (fun y : N ↦ TangentSpace 𝓘(ℝ, F) y →L[ℝ] ℝ))
local notation "W" => VerticalCotangentFiber (E := E) (F := F) (f : M → N)

namespace SmoothHorizontalLift

/-- The actual splitting formula orders the base covector before the vertical covector. -/
def cotangentSplitMap (S : SmoothHorizontalLift f) :
    TotalSpace (E →L[ℝ] ℝ) C →
      TotalSpace ((F →L[ℝ] ℝ) × (V →L[ℝ] ℝ)) (B ×ᵇ W) :=
  fun z ↦ ⟨z.proj, z.snd.comp (S.lift z.proj),
    verticalCotangentRestriction (E := E) (F := F) f z.proj z.snd⟩

open Function Manifold Set Topology in
set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
/-- The specified cotangent split map is a smooth isomorphism for the original bundle atlases. -/
theorem exists_cotangentSplitHomeomorph
    (hf : Manifold.IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (S : SmoothHorizontalLift f) :
    letI := verticalTangentFiberBundle f hf
    letI := verticalTangentVectorBundle f hf
    letI := verticalTangentContMDiffVectorBundle f hf
    ∃ e : TotalSpace (E →L[ℝ] ℝ) C ≃ₜ
        TotalSpace ((F →L[ℝ] ℝ) × (V →L[ℝ] ℝ)) (B ×ᵇ W),
      (∀ z, e z = S.cotangentSplitMap f z) ∧
        ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℝ))
          (𝓘(ℝ, E).prod 𝓘(ℝ, (F →L[ℝ] ℝ) × (V →L[ℝ] ℝ))) ∞ e ∧
        ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, (F →L[ℝ] ℝ) × (V →L[ℝ] ℝ)))
          (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ e.symm := by
  classical
  have local_smooth_rightInverse
      {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {F G : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {V₀ W₀ : M → Type _}
    [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
    [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
    [∀ x, AddCommGroup (W₀ x)] [∀ x, Module ℝ (W₀ x)] [∀ x, TopologicalSpace (W₀ x)]
    [∀ x, IsTopologicalAddGroup (W₀ x)] [∀ x, ContinuousSMul ℝ (W₀ x)]
    [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W₀)]
    [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ 𝓘(ℝ, E)]
    [FiberBundle F W₀] [VectorBundle ℝ F W₀] [ContMDiffVectorBundle ∞ F W₀ 𝓘(ℝ, E)] (Q : ∀ x, W₀ x
      →L[ℝ] V₀ x)
      (hQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace F W₀ ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀)))
      (hsurjective : ∀ x, Surjective (Q x)) (x : M) :
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ∃ s : ∀ y, V₀ y →L[ℝ] W₀ y,
          ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
            (fun y ↦ TotalSpace.mk' (G →L[ℝ] F) y (s y)) U ∧
          ∀ y, y ∈ U → ∀ v, Q y (s y v) = v := by
    classical
    let a := trivializationAt F W₀ x
    let b := trivializationAt G V₀ x
    let A (y : M) : F →L[ℝ] G :=
      (b.continuousLinearMapAt ℝ y).comp ((Q y).comp (a.symmL ℝ y))
    let U := a.baseSet ∩ b.baseSet
    have hU : IsOpen U := a.open_baseSet.inter b.open_baseSet
    have hx : x ∈ U := ⟨mem_baseSet_trivializationAt _ _ _, mem_baseSet_trivializationAt _ _ _⟩
    have hA : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] G) ∞ A U := by
      intro y hy
      have heval (v : F) : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, G) ∞
          (fun z ↦ A z v) U y := by
        have hs : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
            (fun z ↦ (⟨z, a.symmL ℝ z v⟩ : TotalSpace F W₀)) y := by
          apply a.contMDiffAt_iff (a.mem_source.mpr hy.1) |>.mpr
          refine ⟨contMDiffAt_id, ?_⟩
          apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
          filter_upwards [a.open_baseSet.mem_nhds hy.1] with z hz
          rw [← a.continuousLinearMapAt_apply_of_mem ℝ hz]
          exact a.continuousLinearMapAt_symmL hz v
        have hq := hQ.contMDiffAt.comp y hs
        have hb := (b.contMDiffAt_iff (b.mem_source.mpr hy.2)).mp hq
        apply hb.2.contMDiffWithinAt.congr
        · intro z hz
          change (b.continuousLinearMapAt ℝ z) (Q z (a.symmL ℝ z v)) = _
          exact b.continuousLinearMapAt_apply_of_mem ℝ hz.2 _
        · exact b.continuousLinearMapAt_apply_of_mem ℝ hy.2 _
      rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
      apply contDiffWithinAt_clm_apply.mpr
      intro v
      have hv := heval v
      rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at hv
      exact hv
    -- Choose one right inverse at the center; nearby invertible corrections vary smoothly.
    have hsurj : Function.Surjective (A x) := by
      intro v
      obtain ⟨w, hw⟩ := hsurjective x (b.symmL ℝ x v)
      refine ⟨a.continuousLinearMapAt ℝ x w, ?_⟩
      change (b.continuousLinearMapAt ℝ x) (Q x (a.symmL ℝ x
        (a.continuousLinearMapAt ℝ x w))) = v
      erw [a.symmL_continuousLinearMapAt (R := ℝ) hx.1]
      rw [hw, b.continuousLinearMapAt_symmL hx.2]
    obtain ⟨R₀, hR₀⟩ := (A x).toLinearMap.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hsurj)
    let R : G →L[ℝ] F := R₀.toContinuousLinearMap
    let C₀ (y : M) : G →L[ℝ] G := (A y).comp R
    have hCx : C₀ x = ContinuousLinearMap.id ℝ G := by
      apply ContinuousLinearMap.ext
      intro v
      exact congrArg (fun L : G →ₗ[ℝ] G ↦ L v) hR₀
    have hC : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, G →L[ℝ] G) ∞ C₀ U :=
      hA.clm_comp contMDiffOn_const
    have hCAt := (hC x hx).contMDiffAt (hU.mem_nhds hx)
    have hinv : (C₀ x).IsInvertible := by
      rw [hCx]
      exact ⟨ContinuousLinearEquiv.refl ℝ G, rfl⟩
    have hevent : ∀ᶠ y in 𝓝 x, y ∈ U ∧ (C₀ y).IsInvertible :=
      Filter.inter_mem (hU.mem_nhds hx) (hCAt.continuousAt hinv.eventually_nhds)
    obtain ⟨U', hsub, hU'o, hx'⟩ := mem_nhds_iff.mp hevent
    let P (y : M) : G →L[ℝ] F := R.comp (C₀ y).inverse
    have hP : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, G →L[ℝ] F) ∞ P U' := by
      intro y hy
      have hCy := (hC y (hsub hy).1).contMDiffAt (hU.mem_nhds (hsub hy).1)
      have hInv := ((hsub hy).2.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp y hCy
      exact (contMDiffAt_const.clm_comp hInv).contMDiffWithinAt
    -- Transport this corrected matrix back through the same two original trivializations.
    let s (y : M) : V₀ y →L[ℝ] W₀ y :=
      (a.symmL ℝ y).comp ((P y).comp (b.continuousLinearMapAt ℝ y))
    let c := b.continuousLinearMap (RingHom.id ℝ) a
    have hs : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (G →L[ℝ] F) y (s y)) U' := by
      apply (c.contMDiffOn_section_iff hU'o (fun y hy ↦ (hsub hy).1.symm)).mpr
      apply hP.congr
      intro y hy
      ext v
      rw [show c = b.continuousLinearMap (RingHom.id ℝ) a from rfl,
        Trivialization.continuousLinearMap_apply]
      change (a.continuousLinearMapAt ℝ y)
        (a.symmL ℝ y (P y (b.continuousLinearMapAt ℝ y (b.symmL ℝ y v)))) = P y v
      rw [b.continuousLinearMapAt_symmL (hsub hy).1.2,
        a.continuousLinearMapAt_symmL (hsub hy).1.1]
    have hright (y : M) (hy : y ∈ U') (v : V₀ y) : Q y (s y v) = v := by
      have hinj : Function.Injective (b.continuousLinearMapAt ℝ y) := by
        intro u v huv
        have heq := congrArg (b.symmL ℝ y) huv
        exact (b.symmL_continuousLinearMapAt (R := ℝ) (hsub hy).1.2 u).symm.trans
          (heq.trans (b.symmL_continuousLinearMapAt (R := ℝ) (hsub hy).1.2 v))
      apply hinj
      change (A y) (R ((C₀ y).inverse (b.continuousLinearMapAt ℝ y v))) =
        b.continuousLinearMapAt ℝ y v
      change (C₀ y) ((C₀ y).inverse (b.continuousLinearMapAt ℝ y v)) =
        b.continuousLinearMapAt ℝ y v
      obtain ⟨e, he⟩ := (hsub hy).2
      rw [← he, ContinuousLinearMap.inverse_equiv]
      exact e.apply_symm_apply _
    exact ⟨U', hU'o, hx', s, hs, hright⟩
  have smooth_descent
      {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {F G : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {V₀ W₀ : M → Type _}
    [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
    [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
    [∀ x, AddCommGroup (W₀ x)] [∀ x, Module ℝ (W₀ x)] [∀ x, TopologicalSpace (W₀ x)]
    [∀ x, IsTopologicalAddGroup (W₀ x)] [∀ x, ContinuousSMul ℝ (W₀ x)]
    [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W₀)]
    [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ 𝓘(ℝ, E)]
    [FiberBundle F W₀] [VectorBundle ℝ F W₀] [ContMDiffVectorBundle ∞ F W₀ 𝓘(ℝ, E)]
      {H : Type _} [NormedAddCommGroup H] [NormedSpace ℝ H]
      {Z : M → Type _} [∀ x, AddCommGroup (Z x)] [∀ x, Module ℝ (Z x)]
      [∀ x, TopologicalSpace (Z x)] [∀ x, IsTopologicalAddGroup (Z x)]
      [∀ x, ContinuousSMul ℝ (Z x)] [TopologicalSpace (TotalSpace H Z)]
      [FiberBundle H Z] [VectorBundle ℝ H Z] [ContMDiffVectorBundle ∞ H Z 𝓘(ℝ, E)]
      (Q : ∀ x, W₀ x →L[ℝ] V₀ x) (D : ∀ x, V₀ x →L[ℝ] Z x)
      (hQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace F W₀ ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀)))
      (hsurjective : ∀ x, Surjective (Q x))
      (hDQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, H)) ∞
        (fun z : TotalSpace F W₀ ↦ (⟨z.proj, D z.proj (Q z.proj z.snd)⟩ : TotalSpace H Z))) :
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, H)) ∞
        (fun z : TotalSpace G V₀ ↦ (⟨z.proj, D z.proj z.snd⟩ : TotalSpace H Z)) := by
    intro z
    obtain ⟨U, hU, hz, s, hs, hright⟩ := local_smooth_rightInverse Q hQ hsurjective z.proj
    have hsAt := (hs z.proj hz).contMDiffAt (hU.mem_nhds hz)
    have htotal : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
        (fun w : TotalSpace G V₀ ↦ (⟨w.proj, s w.proj w.snd⟩ : TotalSpace F W₀)) z := by
      exact (hsAt.comp z (Bundle.contMDiffAt_proj V₀)).clm_bundle_apply contMDiffAt_id
    apply (hDQ.contMDiffAt.comp z htotal).congr_of_eventuallyEq
    filter_upwards [((FiberBundle.continuous_proj G V₀).continuousAt).preimage_mem_nhds
      (hU.mem_nhds hz)] with w hw
    change (⟨w.proj, D w.proj w.snd⟩ : TotalSpace H Z) =
      ⟨w.proj, D w.proj (Q w.proj (s w.proj w.snd))⟩
    rw [hright w.proj hw]
  have dual_smooth_criterion_first
      {E : Type _} {F : Type _} {G : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {M : Type _} {P : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace P] [ChartedSpace G P]
    {W₀ : M → Type _} [∀ x, AddCommGroup (W₀ x)] [∀ x, Module ℝ (W₀ x)]
    [∀ x, TopologicalSpace (W₀ x)] [TopologicalSpace (TotalSpace F W₀)]
    [FiberBundle F W₀] [VectorBundle ℝ F W₀] [ContMDiffVectorBundle ∞ F W₀ 𝓘(ℝ, E)]
   (b : P → M) (a : ∀ p, W₀ (b p) →L[ℝ] ℝ)
      (p : P) (hb : ContMDiffAt 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ b p)
      (heval : ∀ v : F, ContMDiffAt 𝓘(ℝ, G) 𝓘(ℝ, ℝ) ∞
        (fun q ↦ a q ((trivializationAt F W₀ (b p)).symmL ℝ (b q) v)) p) :
      ContMDiffAt 𝓘(ℝ, G) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
        (fun q ↦ (⟨b q, a q⟩ : TotalSpace (F →L[ℝ] ℝ) (fun x ↦ W₀ x →L[ℝ] ℝ))) p := by
    rw [contMDiffAt_hom_bundle]
    refine ⟨hb, ?_⟩
    rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
    apply contDiffWithinAt_clm_apply.mpr
    intro v
    have hv := heval v
    rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at hv
    have hscalar (x : M) :
        (trivializationAt ℝ (fun _ : M ↦ ℝ) (b p)).continuousLinearMapAt ℝ x =
          ContinuousLinearMap.id ℝ ℝ := by
      change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ x = _
      exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
    simp only [ContinuousLinearMap.inCoordinates,
      hscalar, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_apply,
      Function.comp_apply]
    convert! hv using 1
  have dual_smooth_criterion_second
      {E : Type _} {F : Type _} {G : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {M : Type _} {P : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace P] [ChartedSpace G P]
    {W₀ : M → Type _} [∀ x, AddCommGroup (W₀ x)] [∀ x, Module ℝ (W₀ x)]
    [∀ x, TopologicalSpace (W₀ x)] [TopologicalSpace (TotalSpace F W₀)]
    [FiberBundle F W₀] [VectorBundle ℝ F W₀] [ContMDiffVectorBundle ∞ F W₀ 𝓘(ℝ, E)]
   (b : P → M) (a : ∀ p, W₀ (b p) →L[ℝ] ℝ)
      (p : P) (hb : ContMDiffAt 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ b p)
      (heval : ∀ v : F, ContMDiffAt 𝓘(ℝ, G) 𝓘(ℝ, ℝ) ∞
        (fun q ↦ a q ((trivializationAt F W₀ (b p)).symmL ℝ (b q) v)) p) :
      ContMDiffAt 𝓘(ℝ, G) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
        (fun q ↦ (⟨b q, a q⟩ : TotalSpace (F →L[ℝ] ℝ) (fun x ↦ W₀ x →L[ℝ] ℝ))) p := by
    rw [contMDiffAt_hom_bundle]
    refine ⟨hb, ?_⟩
    rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
    apply contDiffWithinAt_clm_apply.mpr
    intro v
    have hv := heval v
    rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at hv
    have hscalar (x : M) :
        (trivializationAt ℝ (fun _ : M ↦ ℝ) (b p)).continuousLinearMapAt ℝ x =
          ContinuousLinearMap.id ℝ ℝ := by
      change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ x = _
      exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
    simp only [ContinuousLinearMap.inCoordinates,
      hscalar, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_apply,
      Function.comp_apply]
    convert! hv using 1
  have scalar_eval
      {E : Type _} {F : Type _} {G : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {M : Type _} {P : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace P] [ChartedSpace G P]
    {W₀ : M → Type _} [∀ x, AddCommGroup (W₀ x)] [∀ x, Module ℝ (W₀ x)]
    [∀ x, TopologicalSpace (W₀ x)] [TopologicalSpace (TotalSpace F W₀)]
    [FiberBundle F W₀] [VectorBundle ℝ F W₀] [ContMDiffVectorBundle ∞ F W₀ 𝓘(ℝ, E)]
   (b : P → M) (a : ∀ p, W₀ (b p) →L[ℝ] ℝ)
      (v : ∀ p, W₀ (b p)) (p : P)
      (ha : ContMDiffAt 𝓘(ℝ, G) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
        (fun q ↦ (⟨b q, a q⟩ : TotalSpace (F →L[ℝ] ℝ) (fun x ↦ W₀ x →L[ℝ] ℝ))) p)
      (hv : ContMDiffAt 𝓘(ℝ, G) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
        (fun q ↦ (⟨b q, v q⟩ : TotalSpace F W₀)) p) :
      ContMDiffAt 𝓘(ℝ, G) 𝓘(ℝ, ℝ) ∞ (fun q ↦ a q (v q)) p := by
    have h := ContMDiffAt.clm_bundle_apply (F₂ := ℝ) (E₂ := fun _ : M ↦ ℝ) ha hv
    exact (Bundle.contMDiffAt_totalSpace.mp h).2
  let := verticalTangentFiberBundle f hf
  let := verticalTangentVectorBundle f hf
  let := verticalTangentContMDiffVectorBundle f hf
  let X := TotalSpace (E →L[ℝ] ℝ) C
  let Y := TotalSpace ((F →L[ℝ] ℝ) × (V →L[ℝ] ℝ)) (B ×ᵇ W)
  let K := VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let T := ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F)))
  let (x : M) : AddCommGroup (B x) := by
    change AddCommGroup (TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] ℝ)
    infer_instance
  let (x : M) : Module ℝ (B x) := by
    change Module ℝ (TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] ℝ)
    infer_instance
  let (x : M) : IsTopologicalAddGroup (B x) := by
    change IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] ℝ)
    infer_instance
  let (x : M) : ContinuousSMul ℝ (B x) := by
    change ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] ℝ)
    infer_instance
  let (x : M) : T2Space (B x) := by
    change T2Space (TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] ℝ)
    infer_instance
  let (x : M) : FiniteDimensional ℝ (B x) := by
    change FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] ℝ)
    infer_instance
  let IX := 𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℝ)
  let IY := 𝓘(ℝ, E).prod 𝓘(ℝ, (F →L[ℝ] ℝ) × (V →L[ℝ] ℝ))
  let : ChartedSpace (E × (E →L[ℝ] ℝ)) X :=
    inferInstanceAs (ChartedSpace (ModelProd E (E →L[ℝ] ℝ)) X)
  let : IsManifold 𝓘(ℝ, E × (E →L[ℝ] ℝ)) ∞ X := by
    simpa only [modelWithCornersSelf_prod] using
      (inferInstance : IsManifold IX ∞ X)
  let a (x : M) : C x →L[ℝ] (B x × W x) :=
    (((S.lift x).lcomp ℝ).prod
      (verticalCotangentRestriction (E := E) (F := F) f x)).toContinuousLinearMap
  -- Evaluate each dual coordinate on a fixed vector in its original local frame.
  have hfirst : ContMDiff IX (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun z : X ↦ (⟨z.proj, z.snd.comp (S.lift z.proj)⟩ :
        TotalSpace (F →L[ℝ] ℝ) B)) := by
    intro z
    have hb : ContMDiffAt 𝓘(ℝ, E × (E →L[ℝ] ℝ)) 𝓘(ℝ, E) ∞
        (fun q : X ↦ q.proj) z := by
      simpa only [modelWithCornersSelf_prod] using
        (Bundle.contMDiffAt_proj C (p := z))
    have htarget : ContMDiffAt 𝓘(ℝ, E × (E →L[ℝ] ℝ))
        (𝓘(ℝ, F).prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
        (fun q : X ↦ (⟨f q.proj, q.snd.comp (S.lift q.proj)⟩ :
          TotalSpace (F →L[ℝ] ℝ) (fun y : N ↦ TangentSpace 𝓘(ℝ, F) y →L[ℝ] ℝ))) z := by
      apply dual_smooth_criterion_first (F := F) (W₀ := TangentSpace 𝓘(ℝ, F))
        (fun q : X ↦ f q.proj) (fun q ↦ q.snd.comp (S.lift q.proj)) z
        (f.contMDiff.contMDiffAt.comp z hb)
      intro v
      let t := trivializationAt F (TangentSpace 𝓘(ℝ, F)) (f z.proj)
      have hvN : ContMDiffAt 𝓘(ℝ, E × (E →L[ℝ] ℝ))
          (𝓘(ℝ, F).prod 𝓘(ℝ, F)) ∞
          (fun q : X ↦ (⟨f q.proj, t.symmL ℝ (f q.proj) v⟩ :
            TangentBundle 𝓘(ℝ, F) N)) z := by
        apply t.contMDiffAt_iff (t.mem_source.mpr (mem_baseSet_trivializationAt _ _ _)) |>.mpr
        refine ⟨f.contMDiff.contMDiffAt.comp z hb, ?_⟩
        apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
        filter_upwards [(f.contMDiff.contMDiffAt.comp z hb).continuousAt.preimage_mem_nhds
          (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))] with q hq
        change f q.proj ∈ t.baseSet at hq
        rw [← t.continuousLinearMapAt_apply_of_mem ℝ hq]
        exact t.continuousLinearMapAt_symmL hq v
      have hvT : ContMDiffAt 𝓘(ℝ, E × (E →L[ℝ] ℝ))
          (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
          (fun q : X ↦ (⟨q.proj, t.symmL ℝ (f q.proj) v⟩ : TotalSpace F T)) z := by
        apply Bundle.contMDiffAt_totalSpace.mpr
        exact ⟨hb, (Bundle.contMDiffAt_totalSpace.mp hvN).2⟩
      have hvM := S.contMDiff_lift.contMDiffAt.comp z hvT
      have hid : ContMDiffAt 𝓘(ℝ, E × (E →L[ℝ] ℝ)) IX ∞ (id : X → X) z := by
        simpa only [modelWithCornersSelf_prod] using
          (contMDiffAt_id : ContMDiffAt 𝓘(ℝ, E × (E →L[ℝ] ℝ))
            𝓘(ℝ, E × (E →L[ℝ] ℝ)) ∞ (id : X → X) z)
      exact scalar_eval (fun q : X ↦ q.proj) (fun q ↦ q.snd)
        (fun q ↦ S.lift q.proj (t.symmL ℝ (f q.proj) v)) z hid hvM
    have hpull : ContMDiffAt 𝓘(ℝ, E × (E →L[ℝ] ℝ))
        (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
        (fun q : X ↦ (⟨q.proj, q.snd.comp (S.lift q.proj)⟩ :
          TotalSpace (F →L[ℝ] ℝ) B)) z := by
      apply Bundle.contMDiffAt_totalSpace.mpr
      exact ⟨hb, (Bundle.contMDiffAt_totalSpace.mp htarget).2⟩
    simpa only [modelWithCornersSelf_prod] using hpull
  have hsecond : ContMDiff IX (𝓘(ℝ, E).prod 𝓘(ℝ, V →L[ℝ] ℝ)) ∞
      (fun z : X ↦ (⟨z.proj, verticalCotangentRestriction (E := E) (F := F) f z.proj z.snd⟩ :
        TotalSpace (V →L[ℝ] ℝ) W)) := by
    intro z
    have hb : ContMDiffAt 𝓘(ℝ, E × (E →L[ℝ] ℝ)) 𝓘(ℝ, E) ∞
        (fun q : X ↦ q.proj) z := by
      simpa only [modelWithCornersSelf_prod] using
        (Bundle.contMDiffAt_proj C (p := z))
    have hs : ContMDiffAt 𝓘(ℝ, E × (E →L[ℝ] ℝ))
        (𝓘(ℝ, E).prod 𝓘(ℝ, V →L[ℝ] ℝ)) ∞
        (fun q : X ↦ (⟨q.proj, verticalCotangentRestriction (E := E) (F := F) f q.proj q.snd⟩ :
          TotalSpace (V →L[ℝ] ℝ) W)) z := by
      apply dual_smooth_criterion_second (F := V) (W₀ := K) (fun q : X ↦ q.proj)
        (fun q ↦ verticalCotangentRestriction (E := E) (F := F) f q.proj q.snd) z hb
      intro v
      let t := trivializationAt V K z.proj
      have hvK : ContMDiffAt 𝓘(ℝ, E × (E →L[ℝ] ℝ))
          (𝓘(ℝ, E).prod 𝓘(ℝ, V)) ∞
          (fun q : X ↦ (⟨q.proj, t.symmL ℝ q.proj v⟩ : TotalSpace V K)) z := by
        apply t.contMDiffAt_iff (t.mem_source.mpr (mem_baseSet_trivializationAt _ _ _)) |>.mpr
        refine ⟨hb, ?_⟩
        apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
        filter_upwards [hb.continuousAt.preimage_mem_nhds
          (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))] with q hq
        rw [← t.continuousLinearMapAt_apply_of_mem ℝ hq]
        exact t.continuousLinearMapAt_symmL hq v
      have hvM := (smoothVerticalTangentInclusion f hf).contMDiff.contMDiffAt.comp z hvK
      have hid : ContMDiffAt 𝓘(ℝ, E × (E →L[ℝ] ℝ)) IX ∞ (id : X → X) z := by
        simpa only [modelWithCornersSelf_prod] using
          (contMDiffAt_id : ContMDiffAt 𝓘(ℝ, E × (E →L[ℝ] ℝ))
            𝓘(ℝ, E × (E →L[ℝ] ℝ)) ∞ (id : X → X) z)
      exact scalar_eval (fun q : X ↦ q.proj) (fun q ↦ q.snd)
        (fun q ↦ (t.symmL ℝ q.proj v).val) z hid hvM
    simpa only [modelWithCornersSelf_prod] using hs
  have hforward : ContMDiff IX IY ∞
      (fun z : X ↦ (⟨z.proj, a z.proj z.snd⟩ : Y)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj C, ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp (hfirst z)).2.prodMk_space
      (Bundle.contMDiffAt_totalSpace.mp (hsecond z)).2
  -- The inverse is the original derivative pullback plus the kernel component.
  let D (x : M) := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  let P (x : M) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] K x :=
    (ContinuousLinearMap.id ℝ _ - (S.lift x).comp (D x)).codRestrict
      (LinearMap.ker (D x).toLinearMap) (by
        intro v
        change D x (v - S.lift x (D x v)) = 0
        rw [map_sub, S.right_inv x, sub_self])
  let b (x : M) : (B x × W x) →L[ℝ] C x :=
    ((((D x).lcomp ℝ).comp (LinearMap.fst ℝ (B x) (W x))) +
      (((P x).lcomp ℝ).comp (LinearMap.snd ℝ (B x) (W x)))).toContinuousLinearMap
  have hleft (x : M) : Function.LeftInverse (b x) (a x) := by
    intro ξ
    ext w
    change ξ (S.lift x (D x w)) + ξ (w - S.lift x (D x w)) = ξ w
    rw [map_sub]
    ring
  have hright (x : M) : Function.RightInverse (b x) (a x) := by
    intro v
    apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro w
      change (show F →L[ℝ] ℝ from v.1) (D x (S.lift x w)) +
        v.2 (P x (S.lift x w)) = (show F →L[ℝ] ℝ from v.1) w
      have hp : P x (S.lift x w) = 0 := by
        apply Subtype.ext
        change S.lift x w - S.lift x (D x (S.lift x w)) = 0
        rw [S.right_inv x, sub_self]
      rw [S.right_inv x, hp, map_zero, add_zero]
    · ext w
      change (show F →L[ℝ] ℝ from v.1) (D x w.val) + v.2 (P x w.val) = v.2 w
      have hp : P x w.val = w := by
        apply Subtype.ext
        change w.val - S.lift x (D x w.val) = w.val
        rw [show D x w.val = 0 from w.property, map_zero, sub_zero]
      rw [show D x w.val = 0 from w.property, map_zero, zero_add, hp]
  -- A smooth bijective bundle map has a smooth inverse in these same finite-rank frames.
  have hbackward : ContMDiff IY IX ∞
      (fun z : Y ↦ (⟨z.proj, b z.proj z.snd⟩ : X)) := by
    apply smooth_descent (F := E →L[ℝ] ℝ) (G := (F →L[ℝ] ℝ) × (V →L[ℝ] ℝ))
      (H := E →L[ℝ] ℝ) (W₀ := C) (V₀ := B ×ᵇ W) (Z := C) a b hforward
      (fun x ↦ (hright x).surjective)
    apply contMDiff_id.congr
    intro z
    change (⟨z.proj, b z.proj (a z.proj z.snd)⟩ : X) = z
    exact congrArg (fun v ↦ (⟨z.proj, v⟩ : X)) (hleft z.proj z.snd)
  let e : X ≃ₜ Y :=
    { toFun := fun z ↦ ⟨z.proj, a z.proj z.snd⟩
      invFun := fun z ↦ ⟨z.proj, b z.proj z.snd⟩
      left_inv := fun z ↦ congrArg (fun v ↦ (⟨z.proj, v⟩ : X)) (hleft z.proj z.snd)
      right_inv := fun z ↦ congrArg (fun v ↦ (⟨z.proj, v⟩ : Y)) (hright z.proj z.snd)
      continuous_toFun := hforward.continuous
      continuous_invFun := hbackward.continuous }
  exact ⟨e, fun z ↦ rfl, hforward, hbackward⟩

/-- The homeomorphism selected with the exact split-map formula and its smooth inverse. -/
def cotangentSplitHomeomorph
    (hf : Manifold.IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (S : SmoothHorizontalLift f) :
    letI := verticalTangentFiberBundle f hf
    letI := verticalTangentVectorBundle f hf
    letI := verticalTangentContMDiffVectorBundle f hf
    TotalSpace (E →L[ℝ] ℝ) C ≃ₜ
      TotalSpace ((F →L[ℝ] ℝ) × (V →L[ℝ] ℝ)) (B ×ᵇ W) :=
  (exists_cotangentSplitHomeomorph f hf S).choose

open Function Set Topology in
set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
/-- Changing the horizontal lift gives a proper homotopy of the original inverse split maps. -/
theorem exists_cotangentSplit_properHomotopy
    (hf : Manifold.IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (S₀ S₁ : SmoothHorizontalLift f) :
    letI := verticalTangentFiberBundle f hf
    letI := verticalTangentVectorBundle f hf
    letI := verticalTangentContMDiffVectorBundle f hf
    ∃ H : ContinuousMap.Homotopy
        (⟨(S₀.cotangentSplitHomeomorph f hf).symm,
          (S₀.cotangentSplitHomeomorph f hf).symm.continuous⟩ :
          C(TotalSpace ((F →L[ℝ] ℝ) × (V →L[ℝ] ℝ)) (B ×ᵇ W),
            TotalSpace (E →L[ℝ] ℝ) C))
        (⟨(S₁.cotangentSplitHomeomorph f hf).symm,
          (S₁.cotangentSplitHomeomorph f hf).symm.continuous⟩ :
          C(TotalSpace ((F →L[ℝ] ℝ) × (V →L[ℝ] ℝ)) (B ×ᵇ W),
            TotalSpace (E →L[ℝ] ℝ) C)),
      IsProperMap H := by
  classical
  have continuous_combination_source {B₀ : Type _} {X : Type _} {F₀ : Type _}
      [TopologicalSpace B₀] [TopologicalSpace X]
      [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
      {V₀ : B₀ → Type _} [∀ b, AddCommGroup (V₀ b)] [∀ b, Module ℝ (V₀ b)]
      [∀ b, TopologicalSpace (V₀ b)] [TopologicalSpace (TotalSpace F₀ V₀)]
      [FiberBundle F₀ V₀] [VectorBundle ℝ F₀ V₀]
      (b : X → B₀) (u v : ∀ x, V₀ (b x)) (a c : X → ℝ)
      (hu : Continuous (fun x ↦ (⟨b x, u x⟩ : TotalSpace F₀ V₀)))
      (hv : Continuous (fun x ↦ (⟨b x, v x⟩ : TotalSpace F₀ V₀)))
      (ha : Continuous a) (hc : Continuous c) :
      Continuous (fun x ↦ (⟨b x, a x • u x + c x • v x⟩ : TotalSpace F₀ V₀)) := by
    have hb : Continuous b := (FiberBundle.continuous_proj F₀ V₀).comp hu
    rw [continuous_iff_continuousAt]
    intro x
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨hb.continuousAt, ?_⟩
    let e := trivializationAt F₀ V₀ (b x)
    have hu' := ((FiberBundle.continuousAt_totalSpace F₀ _ (x₀ := x)).mp hu.continuousAt).2
    have hv' := ((FiberBundle.continuousAt_totalSpace F₀ _ (x₀ := x)).mp hv.continuousAt).2
    have hn : ∀ᶠ y in 𝓝 x, b y ∈ e.baseSet :=
      hb.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F₀ V₀ (b x)))
    apply ((ha.continuousAt.smul hu').add (hc.continuousAt.smul hv')).congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    change (e ⟨b y, a y • u y + c y • v y⟩).2 =
      a y • (e ⟨b y, u y⟩).2 + c y • (e ⟨b y, v y⟩).2
    simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hy, map_add, map_smul]
  have continuous_combination_target {B₀ : Type _} {X : Type _} {F₀ : Type _}
      [TopologicalSpace B₀] [TopologicalSpace X]
      [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
      {V₀ : B₀ → Type _} [∀ b, AddCommGroup (V₀ b)] [∀ b, Module ℝ (V₀ b)]
      [∀ b, TopologicalSpace (V₀ b)] [TopologicalSpace (TotalSpace F₀ V₀)]
      [FiberBundle F₀ V₀] [VectorBundle ℝ F₀ V₀]
      (b : X → B₀) (u v : ∀ x, V₀ (b x)) (a c : X → ℝ)
      (hu : Continuous (fun x ↦ (⟨b x, u x⟩ : TotalSpace F₀ V₀)))
      (hv : Continuous (fun x ↦ (⟨b x, v x⟩ : TotalSpace F₀ V₀)))
      (ha : Continuous a) (hc : Continuous c) :
      Continuous (fun x ↦ (⟨b x, a x • u x + c x • v x⟩ : TotalSpace F₀ V₀)) := by
    have hb : Continuous b := (FiberBundle.continuous_proj F₀ V₀).comp hu
    rw [continuous_iff_continuousAt]
    intro x
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨hb.continuousAt, ?_⟩
    let e := trivializationAt F₀ V₀ (b x)
    have hu' := ((FiberBundle.continuousAt_totalSpace F₀ _ (x₀ := x)).mp hu.continuousAt).2
    have hv' := ((FiberBundle.continuousAt_totalSpace F₀ _ (x₀ := x)).mp hv.continuousAt).2
    have hn : ∀ᶠ y in 𝓝 x, b y ∈ e.baseSet :=
      hb.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F₀ V₀ (b x)))
    apply ((ha.continuousAt.smul hu').add (hc.continuousAt.smul hv')).congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    change (e ⟨b y, a y • u y + c y • v y⟩).2 =
      a y • (e ⟨b y, u y⟩).2 + c y • (e ⟨b y, v y⟩).2
    simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hy, map_add, map_smul]
  let := verticalTangentFiberBundle f hf
  let := verticalTangentVectorBundle f hf
  let := verticalTangentContMDiffVectorBundle f hf
  let X := TotalSpace (E →L[ℝ] ℝ) C
  let Y := TotalSpace ((F →L[ℝ] ℝ) × (V →L[ℝ] ℝ)) (B ×ᵇ W)
  let K := VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let (x : M) : AddCommGroup (B x) := by
    change AddCommGroup (TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] ℝ)
    infer_instance
  let (x : M) : Module ℝ (B x) := by
    change Module ℝ (TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] ℝ)
    infer_instance
  -- Stage 1: the inverse formula is determined by the original differential and lift.
  let D (x : M) := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  let a (h : ∀ x : M, TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] TangentSpace 𝓘(ℝ, E) x)
      (x : M) (ξ : C x) : B x × W x :=
    (ξ.comp (h x), verticalCotangentRestriction (E := E) (F := F) f x ξ)
  let P (h : ∀ x : M, TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] TangentSpace 𝓘(ℝ, E) x)
      (hr : ∀ x, RightInverse (h x) (D x)) (x : M) :
      TangentSpace 𝓘(ℝ, E) x →L[ℝ] K x :=
    (ContinuousLinearMap.id ℝ _ - (h x).comp (D x)).codRestrict
      (LinearMap.ker (D x).toLinearMap) (by
        intro w
        change D x (w - h x (D x w)) = 0
        rw [map_sub, hr x, sub_self])
  let b (h : ∀ x : M, TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] TangentSpace 𝓘(ℝ, E) x)
      (hr : ∀ x, RightInverse (h x) (D x)) (x : M) (v : B x × W x) : C x :=
    (show TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] ℝ from v.1).comp (D x) +
      v.2.comp (P h hr x)
  have hleft (h : ∀ x : M, TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] TangentSpace 𝓘(ℝ, E) x)
      (hr : ∀ x, RightInverse (h x) (D x)) (x : M) :
      LeftInverse (b h hr x) (a h x) := by
    intro ξ
    ext w
    change ξ (h x (D x w)) + ξ (w - h x (D x w)) = ξ w
    rw [map_sub]
    ring
  have hright (h : ∀ x : M, TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] TangentSpace 𝓘(ℝ, E) x)
      (hr : ∀ x, RightInverse (h x) (D x)) (x : M) :
      RightInverse (b h hr x) (a h x) := by
    intro v
    apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro w
      change (show F →L[ℝ] ℝ from v.1) (D x (h x w)) +
        v.2 (P h hr x (h x w)) = (show F →L[ℝ] ℝ from v.1) w
      have hp : P h hr x (h x w) = 0 := by
        apply Subtype.ext
        change h x w - h x (D x (h x w)) = 0
        rw [hr x, sub_self]
      rw [hr x, hp, map_zero, add_zero]
    · ext w
      change (show F →L[ℝ] ℝ from v.1) (D x w.val) + v.2 (P h hr x w.val) = v.2 w
      have hp : P h hr x w.val = w := by
        apply Subtype.ext
        change w.val - h x (D x w.val) = w.val
        rw [show D x w.val = 0 from w.property, map_zero, sub_zero]
      rw [show D x w.val = 0 from w.property, map_zero, zero_add, hp]
  let e₀ : X ≃ₜ Y := S₀.cotangentSplitHomeomorph f hf
  let e₁ : X ≃ₜ Y := S₁.cotangentSplitHomeomorph f hf
  have he (S : SmoothHorizontalLift f) (z : X) :
      S.cotangentSplitHomeomorph f hf z = (⟨z.proj, a S.lift z.proj z.snd⟩ : Y) :=
    (exists_cotangentSplitHomeomorph f hf S).choose_spec.1 z
  have heinv (S : SmoothHorizontalLift f) (z : Y) :
      (S.cotangentSplitHomeomorph f hf).symm z =
        (⟨z.proj, b S.lift S.right_inv z.proj z.snd⟩ : X) := by
    apply (S.cotangentSplitHomeomorph f hf).injective
    rw [Homeomorph.apply_symm_apply, he]
    exact (congrArg (fun v ↦ (⟨z.proj, v⟩ : Y)) (hright S.lift S.right_inv z.proj z.snd)).symm
  -- Stage 2: interpolate the supplied right inverses without introducing a new choice.
  let L (t : ℝ) (x : M) := (1 - t) • S₀.lift x + t • S₁.lift x
  have hL (t : ℝ) (x : M) : RightInverse (L t x) (D x) := by
    intro v
    change D x ((1 - t) • S₀.lift x v + t • S₁.lift x v) = v
    rw [map_add, map_smul, map_smul, S₀.right_inv x, S₁.right_inv x]
    module
  have ha (t : ℝ) (x : M) (ξ : C x) :
      a (L t) x ξ = (1 - t) • a S₀.lift x ξ + t • a S₁.lift x ξ := by
    apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro w
      change ξ ((1 - t) • S₀.lift x w + t • S₁.lift x w) =
        (1 - t) * ξ (S₀.lift x w) + t * ξ (S₁.lift x w)
      simp only [map_add, map_smul, smul_eq_mul]
    · change verticalCotangentRestriction (E := E) (F := F) f x ξ =
        (1 - t) • verticalCotangentRestriction (E := E) (F := F) f x ξ +
        t • verticalCotangentRestriction (E := E) (F := F) f x ξ
      module
  have hb (t : ℝ) (x : M) (v : B x × W x) :
      b (L t) (hL t) x v =
        (1 - t) • b S₀.lift S₀.right_inv x v + t • b S₁.lift S₁.right_inv x v := by
    have hp : P (L t) (hL t) x =
        (1 - t) • P S₀.lift S₀.right_inv x + t • P S₁.lift S₁.right_inv x := by
      ext w
      change w - ((1 - t) • S₀.lift x (D x w) + t • S₁.lift x (D x w)) =
        (1 - t) • (w - S₀.lift x (D x w)) + t • (w - S₁.lift x (D x w))
      module
    ext w
    change (show F →L[ℝ] ℝ from v.1) (D x w) + v.2 (P (L t) (hL t) x w) =
      (1 - t) * ((show F →L[ℝ] ℝ from v.1) (D x w) +
        v.2 (P S₀.lift S₀.right_inv x w)) +
      t * ((show F →L[ℝ] ℝ from v.1) (D x w) + v.2 (P S₁.lift S₁.right_inv x w))
    rw [hp]
    simp only [add_apply, smul_apply,
      map_add, map_smul, smul_eq_mul]
    ring
  let A : I × X → Y := fun p ↦ ⟨p.2.proj, a (L p.1) p.2.proj p.2.snd⟩
  let Q : I × Y → X := fun p ↦ ⟨p.2.proj, b (L p.1) (hL p.1) p.2.proj p.2.snd⟩
  have hcA : Continuous A := by
    have hc₀ : Continuous (fun p : I × X ↦
        (⟨p.2.proj, a S₀.lift p.2.proj p.2.snd⟩ : Y)) :=
      (e₀.continuous.comp continuous_snd).congr (fun p ↦ he S₀ p.2)
    have hc₁ : Continuous (fun p : I × X ↦
        (⟨p.2.proj, a S₁.lift p.2.proj p.2.snd⟩ : Y)) :=
      (e₁.continuous.comp continuous_snd).congr (fun p ↦ he S₁ p.2)
    exact (continuous_combination_target (F₀ := (F →L[ℝ] ℝ) × (V →L[ℝ] ℝ))
      (V₀ := B ×ᵇ W) (fun p : I × X ↦ p.2.proj)
      (fun p ↦ a S₀.lift p.2.proj p.2.snd) (fun p ↦ a S₁.lift p.2.proj p.2.snd)
      (fun p ↦ 1 - (p.1 : ℝ)) (fun p ↦ (p.1 : ℝ)) hc₀ hc₁
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
      (continuous_subtype_val.comp continuous_fst)).congr
        (fun p ↦ congrArg (fun v ↦ (⟨p.2.proj, v⟩ : Y)) (ha p.1 p.2.proj p.2.snd).symm)
  have hcQ : Continuous Q := by
    have hc₀ : Continuous (fun p : I × Y ↦
        (⟨p.2.proj, b S₀.lift S₀.right_inv p.2.proj p.2.snd⟩ : X)) :=
      (e₀.symm.continuous.comp continuous_snd).congr (fun p ↦ heinv S₀ p.2)
    have hc₁ : Continuous (fun p : I × Y ↦
        (⟨p.2.proj, b S₁.lift S₁.right_inv p.2.proj p.2.snd⟩ : X)) :=
      (e₁.symm.continuous.comp continuous_snd).congr (fun p ↦ heinv S₁ p.2)
    exact (continuous_combination_source (F₀ := E →L[ℝ] ℝ) (V₀ := C)
      (fun p : I × Y ↦ p.2.proj)
      (fun p ↦ b S₀.lift S₀.right_inv p.2.proj p.2.snd)
      (fun p ↦ b S₁.lift S₁.right_inv p.2.proj p.2.snd)
      (fun p ↦ 1 - (p.1 : ℝ)) (fun p ↦ (p.1 : ℝ)) hc₀ hc₁
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
      (continuous_subtype_val.comp continuous_fst)).congr
        (fun p ↦ congrArg (fun v ↦ (⟨p.2.proj, v⟩ : X)) (hb p.1 p.2.proj p.2.snd).symm)
  -- Stage 3: retain time to obtain a homeomorphism of the entire cylinders.
  let e : (I × Y) ≃ₜ (I × X) :=
    { toFun := fun p ↦ (p.1, Q p)
      invFun := fun p ↦ (p.1, A p)
      left_inv := by
        intro p
        apply Prod.ext
        · rfl
        · exact congrArg (fun v ↦ (⟨p.2.proj, v⟩ : Y))
            (hright (L p.1) (hL p.1) p.2.proj p.2.snd)
      right_inv := by
        intro p
        apply Prod.ext
        · rfl
        · exact congrArg (fun v ↦ (⟨p.2.proj, v⟩ : X))
            (hleft (L p.1) (hL p.1) p.2.proj p.2.snd)
      continuous_toFun := continuous_fst.prodMk hcQ
      continuous_invFun := continuous_fst.prodMk hcA }
  let H : ContinuousMap.Homotopy
      (⟨e₀.symm, e₀.symm.continuous⟩ : C(Y, X))
      (⟨e₁.symm, e₁.symm.continuous⟩ : C(Y, X)) :=
    { toFun := Q
      continuous_toFun := hcQ
      map_zero_left := by
        intro z
        change Q (0, z) = (S₀.cotangentSplitHomeomorph f hf).symm z
        rw [heinv S₀ z]
        change (⟨z.proj, b (L 0) (hL 0) z.proj z.snd⟩ : X) = _
        rw [hb]
        simp
      map_one_left := by
        intro z
        change Q (1, z) = (S₁.cotangentSplitHomeomorph f hf).symm z
        rw [heinv S₁ z]
        change (⟨z.proj, b (L 1) (hL 1) z.proj z.snd⟩ : X) = _
        rw [hb]
        simp }
  refine ⟨H, ?_⟩
  -- Compactness is used only for the time interval, never for either manifold.
  exact (isProperMap_snd_of_compactSpace (X := I) (Y := X)).comp e.isProperMap


end SmoothHorizontalLift

end AtiyahSinger
