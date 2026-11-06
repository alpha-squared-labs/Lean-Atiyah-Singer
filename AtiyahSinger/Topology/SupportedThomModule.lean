/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCoefficientRestriction
public import AtiyahSinger.Topology.HermitianSupportedThom
public import AtiyahSinger.Topology.SupportTensorAction
public import AtiyahSinger.Topology.ThomTensorCoefficient
public import AtiyahSinger.Topology.ThomNaturality

/-!
# The module formula for the supported K-theory Thom operator

Public module ID: M2216.

The same base cutoff and compact zero control are used before and after
right tensoring by an ungraded coefficient. Ordinary tensor reassociation
intertwines both original reciprocal blocks. Thus the coefficient action
commutes with the actual supported Thom map. Passing through the open
inclusion into the coefficient compactification handles compact-support
coefficients without a pullback along the nonproper bundle projection.

Sources: SG Appendix C.1; Karoubi IV.5.22(b). The comparison below retains
both the native support triples and the existing proper-graph action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle Topology
open scoped TensorProduct unitInterval

universe u v w

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace trivialTopology isFiniteRank_trivial
  IdempotentMatrix.fiberTotalSpaceTopology IdempotentMatrix.isFiniteRank_fiber

set_option maxHeartbeats 2000000 in
-- Normalize the reciprocal Thom blocks and their common right tensor coefficient.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The supported Thom operator commutes with coefficients from a compact base. -/
theorem supportedThomHom_complexKZeroCompactSupportAction
    {X : Type u} {B : Type v} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {E : X → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (f : C(X, B))
    (b : ComplexKZero B) (a : CompactSupportKZero X) :
    h.supportedThomHom (complexKZeroCompactSupportAction f b a) =
      complexKZeroCompactSupportAction
        (f.comp ⟨π Unit E, continuous_proj⟩) b (h.supportedThomHom a) := by
  classical
  have tensorRight_map
      {X : Type (max u w)} [TopologicalSpace X]
      {A B : X → Type w}
      [∀ x, AddCommGroup (A x)] [∀ x, Module ℂ (A x)]
      [∀ x, AddCommGroup (B x)] [∀ x, Module ℂ (B x)]
      [TopologicalSpace (TotalSpace Unit A)] [IsFiniteRank A]
      [TopologicalSpace (TotalSpace Unit B)] [IsFiniteRank B]
      (W : X → Type) [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
      [TopologicalSpace (TotalSpace Unit W)] [IsFiniteRank W]
      (a : CompactSupportTriple A B) (d : ∀ x, A x →ₗ[ℂ] B x)
      (hd : ∀ z : (a.controlᶜ : Set X), (a.boundary.linearEquiv z).toLinearMap = d z.val)
      (z : (a.controlᶜ : Set X)) :
      ∀ (v v' : A z.val ⊗[ℂ] W z.val) (_ : v = v'),
        (a.tensorRight W).boundary.linearEquiv z v =
          TensorProduct.map (d z.val) (LinearMap.id : W z.val →ₗ[ℂ] W z.val) v' := by
    intro v v' hv
    subst v'
    induction v using TensorProduct.inductionOn with
    | tmul r w =>
      change TensorProduct.congr (a.boundary.linearEquiv z)
        (LinearEquiv.refl ℂ (W z.val)) (r ⊗ₜ[ℂ] w) = _
      simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
        TensorProduct.map_tmul, LinearMap.id_apply]
      exact congrArg (fun y ↦ y ⊗ₜ[ℂ] w) (LinearMap.congr_fun (hd z) r)
    | add r s hr hs => simpa only [map_add] using congrArg₂ (· + ·) hr hs
  -- Install the given metric without changing the original complex module structure.
  let : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (h.toCore x).toNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
    InnerProductSpace.ofCore (h.toCore x).toCore
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let evenPart : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0
  let oddPart : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1
  obtain ⟨s, rfl⟩ := supportBundleTriple_compactSupportClass_surjective a
  have hs : s.datum.compactSupportClass = s.compactSupportClass :=
    compactSupportTriple_compactSupportClass_ofBoundary s.source s.target s.datum
  -- Fix one support representative and one cutoff for every coefficient bundle.
  obtain ⟨U, hU, hcontrol, L, hL, _hUL, ρ, hzero, hone⟩ :=
    exists_time_cutoff s.datum.control s.datum.isCompact_control
  have positive (W : FiniteBundle B) :
      h.supportedThomHom (complexKZeroCompactSupportAction f W.kZeroClass s.compactSupportClass) =
        complexKZeroCompactSupportAction (f.comp p) W.kZeroClass
          (h.supportedThomHom s.compactSupportClass) := by
    let Wp := W.pullback f
    let t := SupportBundleTriple.ofBoundary (s.source.tensor Wp) (s.target.tensor Wp)
      (s.datum.tensorRight Wp.Fiber)
    have hinput : t.compactSupportClass =
        complexKZeroCompactSupportAction f W.kZeroClass s.compactSupportClass := by
      rw [← compactSupportTriple_compactSupportClass_ofBoundary]
      rw [CompactSupportTriple.compactSupportClass_tensorRight_pullback, hs]
      rfl
    let S := fun x : X ↦ (s.source.Fiber x ⊗[ℂ] evenPart x) ×
      (s.target.Fiber x ⊗[ℂ] oddPart x)
    let T := fun x : X ↦ (s.target.Fiber x ⊗[ℂ] evenPart x) ×
      (s.source.Fiber x ⊗[ℂ] oddPart x)
    let S' := fun x : X ↦ ((s.source.Fiber x ⊗[ℂ] Wp.Fiber x) ⊗[ℂ] evenPart x) ×
      ((s.target.Fiber x ⊗[ℂ] Wp.Fiber x) ⊗[ℂ] oddPart x)
    let T' := fun x : X ↦ ((s.target.Fiber x ⊗[ℂ] Wp.Fiber x) ⊗[ℂ] evenPart x) ×
      ((s.source.Fiber x ⊗[ℂ] Wp.Fiber x) ⊗[ℂ] oddPart x)
    let sa : CompactSupportTriple (p *ᵖ S) (p *ᵖ T) :=
      supportedThomTriple E h.continuous_pairing s ρ U hU hcontrol hzero L hL hone
    let ta : CompactSupportTriple (p *ᵖ S') (p *ᵖ T') :=
      supportedThomTriple E h.continuous_pairing t ρ U hU hcontrol hzero L hL hone
    let coefficient := (f.comp p) *ᵖ W.Fiber
    let tc := sa.tensorRight coefficient
    have hsThom : h.supportedThomHom s.compactSupportClass = sa.compactSupportClass :=
      supportedThomHom_class E h.continuous_pairing s ρ U hU hcontrol hzero L hL hone
    have htThom : h.supportedThomHom t.compactSupportClass = ta.compactSupportClass :=
      supportedThomHom_class E h.continuous_pairing t ρ U hU hcontrol hzero L hL hone
    have hcThom : tc.compactSupportClass =
        complexKZeroCompactSupportAction (f.comp p) W.kZeroClass sa.compactSupportClass :=
      sa.compactSupportClass_tensorRight_pullback W.Fiber (f.comp p)
    -- The actual coefficient is moved through the two exterior parity factors with no sign.
    obtain ⟨u₀, hu₀, hu₁⟩ := exists_thomTensorCoefficient_iso
      s.source.Fiber s.target.Fiber evenPart oddPart Wp.Fiber
    obtain ⟨v₀, hv₀, hv₁⟩ := exists_thomTensorCoefficient_iso
      s.target.Fiber s.source.Fiber evenPart oddPart Wp.Fiber
    let u : Iso (p *ᵖ S') (fun z ↦ (p *ᵖ S) z ⊗[ℂ] coefficient z) :=
      (u₀.pullback p).trans ((pullbackTensorIso p).trans
        ((Iso.refl (p *ᵖ S)).tensor (pullbackCompIso (E := W.Fiber) f p)))
    let v : Iso (p *ᵖ T') (fun z ↦ (p *ᵖ T) z ⊗[ℂ] coefficient z) :=
      (v₀.pullback p).trans ((pullbackTensorIso p).trans
        ((Iso.refl (p *ᵖ T)).tensor (pullbackCompIso (E := W.Fiber) f p)))
    have humap (z : TotalSpace Unit E) (w : S' z.proj) :
        u.linearEquiv z w = u₀.linearEquiv z.proj w := by
      have hr : (pullbackCompIso (E := W.Fiber) f p).linearEquiv z =
          LinearEquiv.refl ℂ (W.Fiber (f z.proj)) :=
        LinearEquiv.ext (pullbackCompIso_apply f p z)
      change TensorProduct.congr (LinearEquiv.refl ℂ (S z.proj))
        ((pullbackCompIso (E := W.Fiber) f p).linearEquiv z) (u₀.linearEquiv z.proj w) = _
      rw [hr]
      erw [TensorProduct.congr_refl_refl]
      rfl
    have hvmap (z : TotalSpace Unit E) (w : T' z.proj) :
        v.linearEquiv z w = v₀.linearEquiv z.proj w := by
      have hr : (pullbackCompIso (E := W.Fiber) f p).linearEquiv z =
          LinearEquiv.refl ℂ (W.Fiber (f z.proj)) :=
        LinearEquiv.ext (pullbackCompIso_apply f p z)
      change TensorProduct.congr (LinearEquiv.refl ℂ (T z.proj))
        ((pullbackCompIso (E := W.Fiber) f p).linearEquiv z) (v₀.linearEquiv z.proj w) = _
      rw [hr]
      erw [TensorProduct.congr_refl_refl]
      rfl
    have hd (x : X) : t.datum.cutoffLinearMap ρ x =
        TensorProduct.map (s.datum.cutoffLinearMap ρ x) (LinearMap.id : Wp.Fiber x →ₗ[ℂ] _) := by
      by_cases hx : x ∈ s.datum.control
      · simp [CompactSupportTriple.cutoffLinearMap, t, CompactSupportTriple.tensorRight, hx]
      · apply TensorProduct.ext'
        intro a w
        have hc : t.datum.control = s.datum.control := rfl
        simp only [CompactSupportTriple.cutoffLinearMap, hc, dite_eq_right hx]
        change ((ρ x : ℝ) : ℂ) •
          (TensorProduct.congr (s.datum.boundary.linearEquiv ⟨x, hx⟩)
            (LinearEquiv.refl ℂ (Wp.Fiber x)) (a ⊗ₜ[ℂ] w)) =
          (((ρ x : ℝ) : ℂ) • s.datum.boundary.linearEquiv ⟨x, hx⟩ a) ⊗ₜ[ℂ] w
        rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.smul_tmul']
    have hd' (x : X) : t.datum.inverse.cutoffLinearMap ρ x =
        TensorProduct.map (s.datum.inverse.cutoffLinearMap ρ x)
          (LinearMap.id : Wp.Fiber x →ₗ[ℂ] _) := by
      by_cases hx : x ∈ s.datum.control
      · simp [CompactSupportTriple.cutoffLinearMap, t, CompactSupportTriple.tensorRight,
          CompactSupportTriple.inverse, hx]
      · apply TensorProduct.ext'
        intro a w
        have hc : t.datum.inverse.control = s.datum.control := rfl
        have hsc : s.datum.inverse.control = s.datum.control := rfl
        simp only [CompactSupportTriple.cutoffLinearMap, hc, hsc, dite_eq_right hx]
        change ((ρ x : ℝ) : ℂ) •
          (TensorProduct.congr (s.datum.boundary.linearEquiv ⟨x, hx⟩).symm
            (LinearEquiv.refl ℂ (Wp.Fiber x)) (a ⊗ₜ[ℂ] w)) =
          (((ρ x : ℝ) : ℂ) • (s.datum.boundary.linearEquiv ⟨x, hx⟩).symm a) ⊗ₜ[ℂ] w
        rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.smul_tmul']
    have symbol (x : X) (z : E x) :
        (v₀.linearEquiv x).toLinearMap.comp
            (thomTensorSymbol (t.datum.cutoffLinearMap ρ x)
              (t.datum.inverse.cutoffLinearMap ρ x) z) =
          (TensorProduct.map (thomTensorSymbol (s.datum.cutoffLinearMap ρ x)
            (s.datum.inverse.cutoffLinearMap ρ x) z) (LinearMap.id : Wp.Fiber x →ₗ[ℂ] _)).comp
              (u₀.linearEquiv x).toLinearMap := by
      rw [hd, hd']
      exact thomTensorSymbol_tensorRight (s.datum.cutoffLinearMap ρ x)
        (s.datum.inverse.cutoffLinearMap ρ x) z (u₀.linearEquiv x) (v₀.linearEquiv x)
        (hu₀ x) (hu₁ x) (hv₀ x) (hv₁ x)
    have symbol_apply (x : X) (z : E x) (w : S' x) :
        v₀.linearEquiv x
          (thomTensorSymbol (t.datum.cutoffLinearMap ρ x)
            (t.datum.inverse.cutoffLinearMap ρ x) z w) =
          TensorProduct.map (thomTensorSymbol (s.datum.cutoffLinearMap ρ x)
            (s.datum.inverse.cutoffLinearMap ρ x) z)
            (LinearMap.id : Wp.Fiber x →ₗ[ℂ] _) (u₀.linearEquiv x w) := by
      exact LinearMap.congr_fun (symbol x z) w
    have hta (z : (ta.controlᶜ : Set (TotalSpace Unit E))) :
        (ta.boundary.linearEquiv z).toLinearMap =
          thomTensorSymbol (t.datum.cutoffLinearMap ρ z.val.proj)
            (t.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd := rfl
    have hsa (z : (sa.controlᶜ : Set (TotalSpace Unit E))) :
        (sa.boundary.linearEquiv z).toLinearMap =
          thomTensorSymbol (s.datum.cutoffLinearMap ρ z.val.proj)
            (s.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd := rfl
    have htc := tensorRight_map coefficient sa
      (fun z ↦ thomTensorSymbol (s.datum.cutoffLinearMap ρ z.proj)
        (s.datum.inverse.cutoffLinearMap ρ z.proj) z.snd) hsa
    have hcomm (z : (ta.controlᶜ : Set (TotalSpace Unit E))) (w : (p *ᵖ S') z.val) :
        v.linearEquiv z.val (ta.boundary.linearEquiv z w) =
          tc.boundary.linearEquiv z (u.linearEquiv z.val w) := by
      apply Eq.trans (hvmap z.val (ta.boundary.linearEquiv z w))
      apply Eq.trans (congrArg (v₀.linearEquiv z.val.proj)
        (LinearMap.congr_fun (hta z) w))
      apply Eq.trans (symbol_apply z.val.proj z.val.snd w)
      have htcf := htc z (u.linearEquiv z.val w) (u₀.linearEquiv z.val.proj w)
        (humap z.val w)
      exact htcf.symm
    have htriple : ta.congr u v = tc := by
      change CompactSupportTriple.mk _ _ _ = CompactSupportTriple.mk _ _ _
      congr 1
      apply Iso.ext
      intro z
      apply LinearEquiv.ext
      intro w
      change v.linearEquiv z.val
        (ta.boundary.linearEquiv z ((u.linearEquiv z.val).symm w)) = tc.boundary.linearEquiv z w
      rw [hcomm, LinearEquiv.apply_symm_apply]
    have hclass : ta.compactSupportClass = tc.compactSupportClass := by
      rw [← ta.compactSupportClass_congr u v, htriple]
    rw [← hinput, htThom, hsThom, hclass, hcThom]
  -- Arbitrary compact coefficients are differences of actual finite bundle classes.
  obtain ⟨q, n, hq⟩ := exists_class_sub_trivial b
  let W := smallBundle (fun x ↦ q.fiber x)
  have hW : W.kZeroClass = kZeroClass (fun x ↦ q.fiber x) :=
    (kZeroClass_eq_of_iso (smallBundleIso (fun x ↦ q.fiber x))).symm
  rw [← hW] at hq
  rw [hq]
  simp only [map_sub, AddMonoidHom.sub_apply]
  exact congrArg₂ (· - ·) (positive W) (positive (FiniteBundle.trivial B n))

/-- The supported Thom operator commutes with the original compact-support graph action. -/
theorem supportedThomHom_action
    {X : Type u} {Y : Type v} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    {E : X → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (f : C(X, Y))
    (b : CompactSupportKZero Y) (a : CompactSupportKZero X) :
    h.supportedThomHom (compactSupportKZeroAction f b a) =
      compactSupportKZeroAction (f.comp ⟨π Unit E, continuous_proj⟩) b
        (h.supportedThomHom a) := by
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let j : C(Y, OnePoint Y) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
  have hj : IsOpenEmbedding j := OnePoint.isOpenEmbedding_coe
  let c := compactSupportKZeroOpenPushforward j hj b
  let e := compactSupportKZeroCompactEquiv (OnePoint Y)
  -- Extend this same coefficient into its compactification and use the compact-base formula.
  have hc := h.supportedThomHom_complexKZeroCompactSupportAction (j.comp f) (e c) a
  change h.supportedThomHom (compactSupportKZeroAction (j.comp f) (e.symm (e c)) a) =
    compactSupportKZeroAction ((j.comp f).comp p) (e.symm (e c))
      (h.supportedThomHom a) at hc
  rw [e.symm_apply_apply] at hc
  -- The coefficient-collapse square returns the original graph action on both total spaces.
  have hcomp : (j.comp f).comp p = j.comp (f.comp p) := rfl
  rw [hcomp, compactSupportKZeroAction_openPushforward_coefficient,
    compactSupportKZeroAction_openPushforward_coefficient] at hc
  exact hc

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
