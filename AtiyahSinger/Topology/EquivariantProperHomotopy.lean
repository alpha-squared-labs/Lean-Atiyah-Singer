/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportHomotopy
public import AtiyahSinger.Topology.EquivariantBundleHomotopy
public import AtiyahSinger.Topology.EquivariantSupportFunctoriality
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Proper equivariant homotopies on compact-support classes

Public module ID: M1799.

A proper homotopy supplies one compact control for the whole cylinder.
Equivariant bundle transport over that same cylinder fixes the two bundle
models before applying the original fixed-action boundary homotopy relation.
This proves naturality for the original support-triple presentation, without
an equivariant Bott theorem or a comparison with a different K-theory model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Set
open scoped unitInterval

attribute [local instance] isFiniteRank_pullback

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [ParacompactSpace X]
  [TopologicalSpace Y]
  [MulAction G X] [ContinuousSMul G X] [MulAction G Y] [ContinuousSMul G Y]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
-- Native cylinder pullbacks and both endpoint comparisons keep the same original fibers.
/-- A proper equivariant cylinder gives equal pullbacks on the original compact-support group. -/
theorem equivariantSupportTripleKZeroPullback_eq_of_proper_homotopy
    (f₀ f₁ : C(X, Y))
    (hf₀ : ∀ (g : G) (x : X), f₀ (g • x) = g • f₀ x)
    (hf₁ : ∀ (g : G) (x : X), f₁ (g • x) = g • f₁ x)
    (hp₀ : IsProperMap f₀) (hp₁ : IsProperMap f₁)
    (H : ContinuousMap.Homotopy f₀ f₁)
    (hH : ∀ (t : I) (g : G) (x : X), H (t, g • x) = g • H (t, x))
    (hp : IsProperMap H) :
    equivariantSupportTripleKZeroPullback f₀ hf₀ hp₀ =
      equivariantSupportTripleKZeroPullback f₁ hf₁ hp₁ := by
  classical
  let C := I × X
  let : MulAction G C := {
    smul g z := (z.1, g • z.2)
    one_smul z := Prod.ext rfl (one_smul G z.2)
    mul_smul g h z := Prod.ext rfl (mul_smul g h z.2) }
  let : ContinuousSMul G C :=
    ⟨(continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩
  let p (t : I) : C(X, C) := ⟨fun x ↦ (t, x), continuous_const.prodMk continuous_id⟩
  have hpe (t : I) (g : G) (x : X) : p t (g • x) = g • p t x := rfl
  have hpp (t : I) : IsProperMap (p t) :=
    isProperMap_of_isClosedMap_of_inj (p t).continuous
      (fun _ _ h ↦ congrArg Prod.snd h) (isClosedMap_prodMk_left t)
  have cylinder (a : EquivariantSupportBundleTriple G C) :
      (a.pullback (p 0) (hpe 0) (hpp 0)).kZeroClass =
        (a.pullback (p 1) (hpe 1) (hpp 1)).kZeroClass := by
    let pr : C(C, X) := ⟨Prod.snd, continuous_snd⟩
    have hpr (g : G) (z : C) : pr (g • z) = g • pr z := rfl
    -- Contract only the bundle parameter; compact-support pullback never uses this contraction.
    let J : ContinuousMap.Homotopy ((p 0).comp pr) (ContinuousMap.id C) := {
      toFun z := (z.1 * z.2.1, z.2.2)
      continuous_toFun :=
        (continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
          (continuous_snd.comp continuous_snd)
      map_zero_left z := Prod.ext (zero_mul z.1) rfl
      map_one_left z := Prod.ext (one_mul z.1) rfl }
    have hJ (t : I) (g : G) (z : C) : J (t, g • z) = g • J (t, z) := rfl
    have trivialize (B : FiniteBundle C) (ρ : EquivariantStructure G B.Fiber) :
        ∃ e : Iso ((pr : C → X) *ᵖ ((p 0 : X → C) *ᵖ B.Fiber)) B.Fiber,
          e.IsEquivariant ((ρ.pullback (p 0) (hpe 0)).pullback pr hpr) ρ := by
      obtain ⟨i, hi⟩ := ρ.exists_pullback_iso_of_homotopy ((p 0).comp pr)
        (ContinuousMap.id C) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) J hJ
      let c := pullbackCompIso (E := B.Fiber) (p 0) pr
      let e := c.trans (i.trans (pullbackIdIso (E := B.Fiber)))
      refine ⟨e, ?_⟩
      intro g z v
      have hc := ρ.pullbackCompIso_isEquivariant (p 0) (hpe 0) pr hpr g z v
      change c.linearEquiv (g • z) _ = (ρ.pullback ((p 0).comp pr) _).linearMap g z
        (c.linearEquiv z v) at hc
      change (pullbackIdIso (E := B.Fiber)).linearEquiv (g • z)
          (i.linearEquiv (g • z) (c.linearEquiv (g • z) _)) =
        ρ.linearMap g z ((pullbackIdIso (E := B.Fiber)).linearEquiv z
          (i.linearEquiv z (c.linearEquiv z v)))
      rw [pullbackIdIso_apply, pullbackIdIso_apply, hc]
      exact hi g z (c.linearEquiv z v)
    obtain ⟨e, he⟩ := trivialize a.1.source a.2.sourceAction
    obtain ⟨f, hf⟩ := trivialize a.1.target a.2.targetAction
    let E := a.1.source.pullback (p 0)
    let F := a.1.target.pullback (p 0)
    let ρE := a.2.sourceAction.pullback (p 0) (hpe 0)
    let ρF := a.2.targetAction.pullback (p 0) (hpe 0)
    -- Restrict the same cylinder isomorphisms to every time, with their exact vector actions.
    have slice (B : FiniteBundle C) (e : Iso ((pr : C → X) *ᵖ
        ((p 0 : X → C) *ᵖ B.Fiber)) B.Fiber) (t : I) :
        ∃ eₜ : Iso ((p 0 : X → C) *ᵖ B.Fiber) ((p t : X → C) *ᵖ B.Fiber),
          ∀ x v, eₜ.linearEquiv x v = e.linearEquiv (t, x) v := by
      let D := (p 0 : X → C) *ᵖ B.Fiber
      have hin : Continuous (fun z : TotalSpace Unit D ↦
          (⟨(t, z.proj), z.snd⟩ : TotalSpace Unit ((pr : C → X) *ᵖ D))) := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit D pr).continuous_iff]
        exact (continuous_const.prodMk continuous_proj).prodMk continuous_id
      refine ⟨{ linearEquiv := fun x ↦ e.linearEquiv (t, x)
                continuous_total := ?_
                continuous_symm := ?_ }, fun _ _ ↦ rfl⟩
      · rw [(inducing_pullbackTotalSpaceEmbedding Unit B.Fiber (p t)).continuous_iff]
        exact continuous_proj.prodMk (e.continuous_total.comp hin)
      · exact (Pullback.continuous_lift Unit D pr).comp
          (e.continuous_symm.comp (Pullback.continuous_lift Unit B.Fiber (p t)))
    choose es hes using slice a.1.source e
    choose fs hfs using slice a.1.target f
    have hesq (t : I) : (es t).IsEquivariant ρE
        (a.2.sourceAction.pullback (p t) (hpe t)) := by
      intro g x v
      change (es t).linearEquiv (g • x) (ρE.linearMap g x v) =
        (a.2.sourceAction.pullback (p t) (hpe t)).linearMap g x ((es t).linearEquiv x v)
      rw [hes, hes]
      exact he g (t, x) v
    have hfsq (t : I) : (fs t).IsEquivariant ρF
        (a.2.targetAction.pullback (p t) (hpe t)) := by
      intro g x v
      change (fs t).linearEquiv (g • x) (ρF.linearMap g x v) =
        (a.2.targetAction.pullback (p t) (hpe t)).linearMap g x ((fs t).linearEquiv x v)
      rw [hfs, hfs]
      exact hf g (t, x) v
    let A (t : I) := a.pullback (p t) (hpe t) (hpp t)
    let b (t : I) : CompactSupportTriple E.Fiber F.Fiber :=
      (A t).1.datum.congr (es t).symm (fs t).symm
    have hb (t : I) : (b t).IsEquivariant ρE ρF := by
      refine ⟨(A t).2.isEquivariant.invariant_control, ?_⟩
      intro g x v
      let gx : ((A t).1.datum.controlᶜ : Set X) :=
        ⟨g • x.val, fun h ↦ x.property ((A t).2.isEquivariant.invariant_control g x.val |>.mp h)⟩
      apply (fs t).linearEquiv (g • x.val) |>.injective
      change (fs t).linearEquiv (g • x.val)
        ((fs t).linearEquiv (g • x.val) |>.symm
          ((A t).1.datum.boundary.linearEquiv gx
            ((es t).linearEquiv (g • x.val) (ρE.linearMap g x.val v)))) = _
      rw [LinearEquiv.apply_symm_apply]
      have hs := hesq t g x.val v
      change (es t).linearEquiv (g • x.val) (ρE.linearMap g x.val v) =
        (A t).2.sourceAction.linearMap g x.val ((es t).linearEquiv x.val v) at hs
      rw [hs]
      have haeq := (A t).2.isEquivariant.boundary_intertwines g x
        ((es t).linearEquiv x.val v)
      rw [haeq]
      have ht := hfsq t g x.val
        (((fs t).linearEquiv x.val).symm
          ((A t).1.datum.boundary.linearEquiv x ((es t).linearEquiv x.val v)))
      change (fs t).linearEquiv (g • x.val) (ρF.linearMap g x.val _) =
        (A t).2.targetAction.linearMap g x.val
          ((fs t).linearEquiv x.val (((fs t).linearEquiv x.val).symm _)) at ht
      rw [LinearEquiv.apply_symm_apply] at ht
      exact ht.symm
    let B (t : I) := EquivariantSupportBundleTriple.ofBoundary E F (b t) ρE ρF (hb t)
    have hclass (t : I) : (B t).kZeroClass = (A t).kZeroClass := by
      apply equivariantSupportTripleKZero_generator_relations.1
      refine ⟨(A t).1.datum.control, (A t).1.datum.isCompact_control,
        (A t).2.isEquivariant.invariant_control, Subset.refl _, Subset.refl _,
        es t, fs t, hesq t, hfsq t, ?_⟩
      intro x v
      rw [(b t).enlarge_apply, (A t).1.datum.enlarge_apply]
      change (fs t).linearEquiv x.val ((fs t).linearEquiv x.val |>.symm
        ((A t).1.datum.boundary.linearEquiv x ((es t).linearEquiv x.val v))) = _
      exact (fs t).linearEquiv x.val |>.apply_symm_apply _
    -- Projection of the actual compact support is one invariant compact control for all times.
    let K : Set X := Prod.snd '' a.1.datum.control
    have hK : IsCompact K := a.1.datum.isCompact_control.image continuous_snd
    have hKi (g : G) (x : X) : g • x ∈ K ↔ x ∈ K := by
      constructor
      · rintro ⟨⟨t, y⟩, hy, hxy⟩
        have hy' : (t, g⁻¹ • y) ∈ a.1.datum.control :=
          (a.2.isEquivariant.invariant_control g⁻¹ (t, y)).mpr hy
        refine ⟨(t, g⁻¹ • y), hy', ?_⟩
        change g⁻¹ • y = x
        change y = g • x at hxy
        rw [hxy, inv_smul_smul]
      · rintro ⟨⟨t, y⟩, hy, rfl⟩
        exact ⟨(t, g • y), (a.2.isEquivariant.invariant_control g (t, y)).mpr hy, rfl⟩
    have hsub (t : I) : (b t).control ⊆ K := by
      intro x hx
      exact ⟨(t, x), hx, rfl⟩
    have hhom : (b 0).EquivariantlyHomotopic (b 1) ρE ρF := by
      let S := (Kᶜ : Set X)
      let v : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
      let q : C(I × S, S) := ⟨Prod.snd, continuous_snd⟩
      let r : C(I × S, C) :=
        ⟨fun z ↦ (z.1, z.2.val), continuous_fst.prodMk (v.continuous.comp continuous_snd)⟩
      let w : C((a.1.datum.controlᶜ : Set C), C) :=
        ⟨Subtype.val, continuous_subtype_val⟩
      let l : C(I × S, (a.1.datum.controlᶜ : Set C)) :=
        ⟨fun z ↦ ⟨r z, fun hz ↦ z.2.property ⟨r z, hz, rfl⟩⟩,
          r.continuous.subtype_mk _⟩
      -- Reassociate native pullbacks before composing the same transported boundary family.
      let L : Iso ((Prod.snd : I × S → S) *ᵖ (Restrict E.Fiber S))
          ((Prod.snd : I × S → S) *ᵖ (Restrict F.Fiber S)) :=
        (pullbackCompIso (E := E.Fiber) v q).trans
          ((pullbackCompIso (E := E.Fiber) pr r).symm.trans
            ((e.pullback r).trans
              ((pullbackCompIso (E := a.1.source.Fiber) w l).symm.trans
                ((Iso.pullback l a.1.datum.boundary).trans
                  ((pullbackCompIso (E := a.1.target.Fiber) w l).trans
                    ((f.pullback r).symm.trans
                      ((pullbackCompIso (E := F.Fiber) pr r).trans
                        (pullbackCompIso (E := F.Fiber) v q).symm)))))))
      have hL (z : I × S) (u : E.Fiber z.2.val) :
          L.linearEquiv z u = (f.linearEquiv (r z)).symm
            (a.1.datum.boundary.linearEquiv (l z) (e.linearEquiv (r z) u)) := by
        change ((pullbackCompIso (E := F.Fiber) v q).linearEquiv z).symm
          ((pullbackCompIso (E := F.Fiber) pr r).linearEquiv z
            ((f.linearEquiv (r z)).symm
              ((pullbackCompIso (E := a.1.target.Fiber) w l).linearEquiv z
                (a.1.datum.boundary.linearEquiv (l z)
                  (((pullbackCompIso (E := a.1.source.Fiber) w l).linearEquiv z).symm
                    (e.linearEquiv (r z)
                      (((pullbackCompIso (E := E.Fiber) pr r).linearEquiv z).symm
                        ((pullbackCompIso (E := E.Fiber) v q).linearEquiv z u)))))))) = _
        rw [pullbackCompIso_apply, pullbackCompIso_apply, pullbackCompIso_apply]
        have hiE (u : E.Fiber z.2.val) :
            ((pullbackCompIso (E := E.Fiber) pr r).linearEquiv z).symm u = u := by
          apply ((pullbackCompIso (E := E.Fiber) pr r).linearEquiv z).injective
          exact (((pullbackCompIso (E := E.Fiber) pr r).linearEquiv z).apply_symm_apply u).trans
            (pullbackCompIso_apply pr r z u).symm
        have hiA (u : a.1.source.Fiber (r z)) :
            ((pullbackCompIso (E := a.1.source.Fiber) w l).linearEquiv z).symm u = u := by
          apply ((pullbackCompIso (E := a.1.source.Fiber) w l).linearEquiv z).injective
          exact (((pullbackCompIso (E := a.1.source.Fiber) w l).linearEquiv z).apply_symm_apply
            u).trans (pullbackCompIso_apply w l z u).symm
        have hiF (u : F.Fiber z.2.val) :
            ((pullbackCompIso (E := F.Fiber) v q).linearEquiv z).symm u = u := by
          apply ((pullbackCompIso (E := F.Fiber) v q).linearEquiv z).injective
          exact (((pullbackCompIso (E := F.Fiber) v q).linearEquiv z).apply_symm_apply u).trans
            (pullbackCompIso_apply v q z u).symm
        rw [hiE, hiA, hiF]
      have hendpoint (t : I) (x : S) (u : E.Fiber x.val) :
          L.linearEquiv (t, x) u =
            ((b t).enlarge K hK (hsub t)).boundary.linearEquiv x u := by
        rw [hL, (b t).enlarge_apply]
        have heq : (es t).linearEquiv x.val = e.linearEquiv (t, x.val) :=
          LinearEquiv.ext (hes t x.val)
        have hfq : (fs t).linearEquiv x.val = f.linearEquiv (t, x.val) :=
          LinearEquiv.ext (hfs t x.val)
        let x' : ((a.1.datum.pullback (p t) (hpp t)).controlᶜ : Set X) :=
          ⟨x.val, fun h ↦ x.property (hsub t h)⟩
        change _ = ((fs t).linearEquiv x.val).symm
          ((a.1.datum.boundary.pullback (p t)).linearEquiv x'
            ((es t).linearEquiv x.val u))
        rw [RelativeTriple.pullback_apply, heq, hfq]
        rfl
      refine ⟨{ control := K
                isCompact_control := hK
                invariant_control := hKi
                left_control := hsub 0
                right_control := hsub 1
                homotopy := ⟨L, hendpoint 0, hendpoint 1⟩
                intertwines := ?_ }⟩
      intro t g x u
      rw [hL, hL]
      apply (f.linearEquiv (t, g • x.val)).injective
      change f.linearEquiv (t, g • x.val)
        ((f.linearEquiv (t, g • x.val)).symm
          (a.1.datum.boundary.linearEquiv (l (t, ⟨g • x.val,
            fun h ↦ x.property ((hKi g x.val).mp h)⟩))
            (e.linearEquiv (t, g • x.val) (ρE.linearMap g x.val u)))) =
        f.linearEquiv (t, g • x.val) (ρF.linearMap g x.val
          ((f.linearEquiv (t, x.val)).symm
            (a.1.datum.boundary.linearEquiv (l (t, x))
              (e.linearEquiv (t, x.val) u))))
      rw [LinearEquiv.apply_symm_apply]
      have heq := he g (t, x.val) u
      change e.linearEquiv (t, g • x.val) (ρE.linearMap g x.val u) =
        a.2.sourceAction.linearMap g (t, x.val) (e.linearEquiv (t, x.val) u) at heq
      rw [heq]
      have hboundary := a.2.isEquivariant.boundary_intertwines g (l (t, x))
        (e.linearEquiv (t, x.val) u)
      have hfq := hf g (t, x.val)
        ((f.linearEquiv (t, x.val)).symm
          (a.1.datum.boundary.linearEquiv (l (t, x))
            (e.linearEquiv (t, x.val) u)))
      change f.linearEquiv (t, g • x.val) (ρF.linearMap g x.val _) =
        a.2.targetAction.linearMap g (t, x.val)
          (f.linearEquiv (t, x.val) ((f.linearEquiv (t, x.val)).symm _)) at hfq
      rw [LinearEquiv.apply_symm_apply] at hfq
      exact hboundary.trans hfq.symm
    exact (hclass 0).symm.trans
      ((equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
        E F ρE ρF (b 0) (b 1) (hb 0) (hb 1) hhom).trans (hclass 1))
  -- Apply the cylinder identity to the actual proper pullback of each original generator.
  let h : C(C, Y) := H.toContinuousMap
  have he (g : G) (z : C) : h (g • z) = g • h z := hH z.1 g z.2
  have hzero : h.comp (p 0) = f₀ := ContinuousMap.ext H.apply_zero
  have hone : h.comp (p 1) = f₁ := ContinuousMap.ext H.apply_one
  apply AddMonoidHom.ext
  intro u
  have h₀ := DFunLike.congr_fun
    (equivariantSupportTripleKZeroPullback_comp h (p 0) he (hpe 0) hp (hpp 0)) u
  have h₁ := DFunLike.congr_fun
    (equivariantSupportTripleKZeroPullback_comp h (p 1) he (hpe 1) hp (hpp 1)) u
  have h₀' : equivariantSupportTripleKZeroPullback f₀ hf₀ hp₀ u =
      ((equivariantSupportTripleKZeroPullback (p 0) (hpe 0) (hpp 0)).comp
        (equivariantSupportTripleKZeroPullback h he hp)) u := by
    simpa only [hzero] using h₀
  have h₁' : equivariantSupportTripleKZeroPullback f₁ hf₁ hp₁ u =
      ((equivariantSupportTripleKZeroPullback (p 1) (hpe 1) (hpp 1)).comp
        (equivariantSupportTripleKZeroPullback h he hp)) u := by
    simpa only [hone] using h₁
  rw [h₀', h₁']
  obtain ⟨a, ha⟩ := equivariantSupportBundleTriple_kZeroClass_surjective
    (equivariantSupportTripleKZeroPullback h he hp u)
  change equivariantSupportTripleKZeroPullback (p 0) (hpe 0) (hpp 0) _ =
    equivariantSupportTripleKZeroPullback (p 1) (hpe 1) (hpp 1) _
  rw [← ha, equivariantSupportTripleKZeroPullback_apply,
    equivariantSupportTripleKZeroPullback_apply]
  exact cylinder a

end AtiyahSinger.ComplexBundle
