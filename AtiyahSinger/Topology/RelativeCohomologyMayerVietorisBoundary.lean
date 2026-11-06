/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyMayerVietoris
public import AtiyahSinger.Topology.RelativeCohomologyCup
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The relative cohomology Mayer–Vietoris boundary

Public module ID: M2067.

The connecting morphism of the original degreewise split cochain sequence
is transported through the specified open-union comparison. Exactness and
naturality retain those actual maps and their diagonal/difference signs.
Corrected lifts express the boundary by a cochain on the union pair, which
is needed for the supported cap connecting identity.

Source: Hatcher, Algebraic Topology, sections 2.1, 3.1 and 3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- The actual relative connecting map, with the inverse open-union comparison. -/
def relativeSingularCohomologyMayerVietorisBoundary
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p : ℕ) :
    relativeSingularCohomology R (A ∩ B) p ⟶
      relativeSingularCohomology R (A ∪ B) (p + 1) :=
  (shortExact_relativeSingularCochainMayerVietorisSequence R A B).δ p (p + 1) rfl ≫
    ModuleCat.ofHom (relativeUnionCohomologyEquiv R A B hA hB (p + 1)).symm.toLinearMap

/-- The three repeating exactness positions of the relative Mayer–Vietoris row,
using its native dual middle complex and the actual union comparison. -/
theorem exact_relativeSingularCohomologyMayerVietoris
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p : ℕ) :
    let S := relativeSingularCochainMayerVietorisSequence R A B
    let δ := relativeSingularCohomologyMayerVietorisBoundary R A B hA hB p
    Function.Exact
      (fun x ↦ homologyMap S.f p (relativeUnionCohomologyComparison R A B p x))
      (homologyMap S.g p) ∧
    Function.Exact (homologyMap S.g p) δ ∧
    Function.Exact δ (fun x ↦ homologyMap S.f (p + 1)
      (relativeUnionCohomologyComparison R A B (p + 1) x)) := by
  let S := relativeSingularCochainMayerVietorisSequence R A B
  let hS := shortExact_relativeSingularCochainMayerVietorisSequence R A B
  have hexact₁ := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hS.homology_exact₂ p)
  have hexact₂ := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hS.homology_exact₃ p (p + 1) rfl)
  have hexact₃ := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hS.homology_exact₁ p (p + 1) rfl)
  let e := relativeUnionCohomologyEquiv R A B hA hB (p + 1)
  refine ⟨?_, ?_, ?_⟩
  · -- Open-union excision supplies every class in the native first object.
    intro y
    rw [hexact₁ y]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨x, hx⟩ := (relativeUnionCohomologyComparison_bijective R A B hA hB p).2 a
      refine ⟨x, ?_⟩
      change homologyMap S.f p (relativeUnionCohomologyComparison R A B p x) = y
      rw [hx]
      exact ha
    · rintro ⟨x, hx⟩
      exact ⟨relativeUnionCohomologyComparison R A B p x, hx⟩
  · -- The boundary's final comparison is injective and preserves zero.
    exact hexact₂.comp_injective e.symm e.symm.injective (map_zero e.symm)
  · -- Exactness after the boundary is transported by the same specified equivalence.
    intro x
    change homologyMap S.f (p + 1) (e x) = 0 ↔
      ∃ y, e.symm (hS.δ p (p + 1) rfl y) = x
    rw [hexact₃ (e x)]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy, e.symm_apply_apply]⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, (e.eq_symm_apply).mp hy.symm |>.symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- Naturality unfolds both native cokernel maps and their dual short-complex projections.
/-- A map of the two subspace pairs commutes with the specified relative connecting map. -/
theorem relativeSingularCohomologyMayerVietorisBoundary_naturality
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y))
    {A B : Set X} {A' B' : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hA' : IsOpen A') (hB' : IsOpen B')
    (hfA : Set.MapsTo f A A') (hfB : Set.MapsTo f B B') (p : ℕ) :
    relativeSingularCohomologyMayerVietorisBoundary R A' B' hA' hB' p ≫
        relativeSingularCohomologyPullback R f
          (A := A ∪ B) (B := A' ∪ B')
          (fun _ hx ↦ hx.elim (fun ha ↦ Or.inl (hfA ha)) (fun hb ↦ Or.inr (hfB hb)))
          (p + 1) =
      relativeSingularCohomologyPullback R f
          (A := A ∩ B) (B := A' ∩ B')
          (fun _ hx ↦ ⟨hfA hx.1, hfB hx.2⟩) p ≫
        relativeSingularCohomologyMayerVietorisBoundary R A B hA hB p := by
  let G := relativeSingularMayerVietorisMap R f hfA hfB
  let D := singularCochainDualFunctor R
  let F := D.mapShortComplex.map (ShortComplex.opMap G)
  let J := D.map (relativeUnionSingularChainsToRelative R A B).op
  let J' := D.map (relativeUnionSingularChainsToRelative R A' B').op
  let fU := relativeSingularChainsMap R f
    (A := A ∪ B) (B := A' ∪ B')
    (fun _ hx ↦ hx.elim (fun ha ↦ Or.inl (hfA ha)) (fun hb ↦ Or.inr (hfB hb)))
  -- Naturality of the union quotient holds before dualization, on the same ambient chains.
  have hquot : G.τ₃ ≫ relativeUnionSingularChainsToRelative R A' B' =
      relativeUnionSingularChainsToRelative R A B ≫ fU := by
    apply (cancel_epi (relativeUnionSingularChainsProjection R A B)).mp
    simp [G, fU, relativeSingularMayerVietorisMap, relativeUnionSingularChainsToRelative,
      relativeUnionSingularChainsProjection, relativeSingularChainsMap,
      relativeSingularChainsProjection, ← Category.assoc]
    simp only [Category.assoc, cokernel.π_desc]
  have hcochain : J' ≫ F.τ₁ = D.map fU.op ≫ J := by
    change D.map (relativeUnionSingularChainsToRelative R A' B').op ≫ D.map G.τ₃.op =
      D.map fU.op ≫ D.map (relativeUnionSingularChainsToRelative R A B).op
    rw [← D.map_comp, ← D.map_comp]
    change D.map (G.τ₃ ≫ relativeUnionSingularChainsToRelative R A' B').op =
      D.map (relativeUnionSingularChainsToRelative R A B ≫ fU).op
    rw [hquot]
  have hcomparison : homologyMap J' (p + 1) ≫ homologyMap F.τ₁ (p + 1) =
      homologyMap (D.map fU.op) (p + 1) ≫ homologyMap J (p + 1) := by
    rw [← homologyMap_comp, ← homologyMap_comp, hcochain]
  let e := relativeUnionCohomologyEquiv R A B hA hB (p + 1)
  let e' := relativeUnionCohomologyEquiv R A' B' hA' hB' (p + 1)
  have hcancel (x : relativeUnionSingularCohomology R A' B' (p + 1)) :
      e (homologyMap (D.map fU.op) (p + 1) (e'.symm x)) =
        homologyMap F.τ₁ (p + 1) x := by
    have hc := congrArg (fun g ↦ g (e'.symm x)) hcomparison
    change homologyMap F.τ₁ (p + 1) (e' (e'.symm x)) =
      e (homologyMap (D.map fU.op) (p + 1) (e'.symm x)) at hc
    rw [e'.apply_symm_apply] at hc
    exact hc.symm
  -- The snake connecting morphism is natural; the comparison cancels by its actual inverse.
  have hδ := HomologySequence.δ_naturality F
    (shortExact_relativeSingularCochainMayerVietorisSequence R A' B')
    (shortExact_relativeSingularCochainMayerVietorisSequence R A B) p (p + 1) rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply e.injective
  change e (homologyMap (D.map fU.op) (p + 1)
      (e'.symm ((shortExact_relativeSingularCochainMayerVietorisSequence R A' B').δ
        p (p + 1) rfl x))) =
    e (e.symm ((shortExact_relativeSingularCochainMayerVietorisSequence R A B).δ
      p (p + 1) rfl (homologyMap F.τ₃ p x)))
  rw [hcancel, e.apply_symm_apply]
  exact congrArg (fun g ↦ g x) hδ

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A relative cocycle has a lift whose differential comes from an actual union-relative
cocycle, rather than just from the dual sum quotient. -/
theorem exists_relativeSingularCohomologyMayerVietoris_corrected_lift
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p : ℕ)
    (z : (relativeSingularCochains R (A ∩ B)).X p)
    (hz : (relativeSingularCochains R (A ∩ B)).d p (p + 1) z = 0) :
    let S := relativeSingularCochainMayerVietorisSequence R A B
    let J := (singularCochainDualFunctor R).map
      (relativeUnionSingularChainsToRelative R A B).op
    ∃ (b : S.X₂.X p) (γ : (relativeSingularCochains R (A ∪ B)).X (p + 1)),
      S.g.f p b = z ∧ (relativeSingularCochains R (A ∪ B)).d (p + 1) (p + 2) γ = 0 ∧
        S.f.f (p + 1) (J.f (p + 1) γ) = S.X₂.d p (p + 1) b := by
  let S := relativeSingularCochainMayerVietorisSequence R A B
  let hS := shortExact_relativeSingularCochainMayerVietorisSequence R A B
  let C := relativeSingularCochains R (A ∪ B)
  let J : C ⟶ S.X₁ := (singularCochainDualFunctor R).map
    (relativeUnionSingularChainsToRelative R A B).op
  have hseq (k : ℕ) := hS.map_of_exact
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) k)
  -- Lift the original cocycle through the degreewise surjective sum map.
  obtain ⟨b, hb⟩ := (hseq p).moduleCat_surjective_g z
  change S.X₂.X p at b
  change S.g.f p b = z at hb
  have hdb : S.g.f (p + 1) (S.X₂.d p (p + 1) b) = 0 := by
    have hc := congrArg (fun f ↦ f b) (S.g.comm p (p + 1))
    change S.X₃.d p (p + 1) (S.g.f p b) =
      S.g.f (p + 1) (S.X₂.d p (p + 1) b) at hc
    rw [← hc, hb]
    exact hz
  obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (hseq (p + 1)).exact (S.X₂.d p (p + 1) b) hdb
  change S.X₁.X (p + 1) at v
  change S.f.f (p + 1) v = S.X₂.d p (p + 1) b at hv
  have hvcycle : S.X₁.d (p + 1) (p + 2) v = 0 :=
    hS.d_eq_zero_of_f_eq_d_apply p (p + 1) b v hv (p + 2)
  let vc : S.X₁.cycles (p + 1) := S.X₁.cyclesMk v (p + 2) (by simp) hvcycle
  have hvc : S.X₁.iCycles (p + 1) vc = v := S.X₁.i_cyclesMk v (p + 2) _ hvcycle
  -- Open-union excision replaces this native cycle by a cohomologous union-relative cycle.
  let e := relativeUnionCohomologyEquiv R A B hA hB (p + 1)
  obtain ⟨gc, hgc⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ (p + 1))).mp inferInstance
    (e.symm (S.X₁.homologyπ (p + 1) vc))
  let γ := C.iCycles (p + 1) gc
  have hγ : C.d (p + 1) (p + 2) γ = 0 :=
    congrArg (fun f ↦ f gc) (C.iCycles_d (p + 1) (p + 2))
  have hclass : S.X₁.homologyπ (p + 1) vc =
      S.X₁.homologyπ (p + 1) (cyclesMap J (p + 1) gc) := by
    have hnat := congrArg (fun f ↦ f gc) (homologyπ_naturality J (p + 1))
    change e (C.homologyπ (p + 1) gc) =
      S.X₁.homologyπ (p + 1) (cyclesMap J (p + 1) gc) at hnat
    rw [hgc, e.apply_symm_apply] at hnat
    exact hnat
  -- Their difference is a coboundary. Correct the lift by its first-term primitive.
  let T := S.X₁.sc (p + 1)
  have hexact : (ShortComplex.mk T.toCycles T.homologyπ
      T.toCycles_comp_homologyπ).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ T.homologyIsCokernel
  have hzero : T.homologyπ (vc - cyclesMap J (p + 1) gc) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hclass
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexact _ hzero
  let adjustment := (S.X₁.xPrevIso (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl)).hom a
  have hadjustment : S.X₁.d p (p + 1) adjustment = v - J.f (p + 1) γ := by
    have h := congrArg (S.X₁.iCycles (p + 1)) ha
    have hleft := congrArg (fun f ↦ f a) T.toCycles_i
    have hright := congrArg (fun f ↦ f gc) (cyclesMap_i J (p + 1))
    change S.X₁.iCycles (p + 1) (cyclesMap J (p + 1) gc) = J.f (p + 1) γ at hright
    change S.X₁.iCycles (p + 1) (T.toCycles a) =
      S.X₁.iCycles (p + 1) (vc - cyclesMap J (p + 1) gc) at h
    rw [map_sub, hvc, hright] at h
    change S.X₁.iCycles (p + 1) (T.toCycles a) = S.X₁.dTo (p + 1) a at hleft
    rw [hleft] at h
    rw [S.X₁.dTo_eq (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl)] at h
    exact h
  refine ⟨b - S.f.f p adjustment, γ, ?_, hγ, ?_⟩
  · have hzero := congrArg (fun f ↦ f.f p adjustment) S.zero
    change S.g.f p (S.f.f p adjustment) = 0 at hzero
    rw [map_sub, hzero, sub_zero, hb]
  · have hc := congrArg (fun f ↦ f adjustment) (S.f.comm p (p + 1))
    change S.X₂.d p (p + 1) (S.f.f p adjustment) =
      S.f.f (p + 1) (S.X₁.d p (p + 1) adjustment) at hc
    rw [map_sub, hc, hadjustment, map_sub, hv, sub_sub_cancel]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A corrected lift computes the connecting map on the original relative cocycle classes. -/
theorem relativeSingularCohomologyMayerVietorisBoundary_cocycleClass
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p : ℕ)
    (z : relativeSingularCocycles R (A ∩ B) p)
    (b : (relativeSingularCochainMayerVietorisSequence R A B).X₂.X p)
    (γ : relativeSingularCocycles R (A ∪ B) (p + 1))
    (hb : (relativeSingularCochainMayerVietorisSequence R A B).g.f p b = z.val)
    (hboundary : (relativeSingularCochainMayerVietorisSequence R A B).f.f (p + 1)
        (((singularCochainDualFunctor R).map
          (relativeUnionSingularChainsToRelative R A B).op).f (p + 1) γ.val) =
      (relativeSingularCochainMayerVietorisSequence R A B).X₂.d p (p + 1) b) :
    relativeSingularCohomologyMayerVietorisBoundary R A B hA hB p
        (relativeSingularCocycleClass R (A ∩ B) p z) =
      relativeSingularCocycleClass R (A ∪ B) (p + 1) γ := by
  let S := relativeSingularCochainMayerVietorisSequence R A B
  let C := relativeSingularCochains R (A ∪ B)
  let J : C ⟶ S.X₁ := (singularCochainDualFunctor R).map
    (relativeUnionSingularChainsToRelative R A B).op
  let hS := shortExact_relativeSingularCochainMayerVietorisSequence R A B
  -- Relate the original concrete cocycle kernels to the canonical cycle objects.
  have hclosed (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (a : (D.sc k).moduleCatLeftHomologyData.K) : D.d k (k + 1) a.val = 0 := by
    have h : D.dFrom k a.val = 0 := a.property
    have h' := congrArg (D.xNextIso (show (ComplexShape.up ℕ).Rel k (k + 1) from rfl)).hom h
    rw [← ModuleCat.comp_apply, D.dFrom_comp_xNextIso, map_zero] at h'
    exact h'
  have hclass (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (a : (D.sc k).moduleCatLeftHomologyData.K) :
      D.homologyπ k (D.cyclesMk a.val (k + 1) (by simp) (hclosed D k a)) =
        (D.sc k).moduleCatHomologyIso.inv ((D.sc k).moduleCatToCycles.range.mkQ a) := by
    have heq : (D.cyclesMk a.val (k + 1) (by simp) (hclosed D k a) : D.cycles k) =
        (D.sc k).moduleCatCyclesIso.inv a := by
      apply (ModuleCat.mono_iff_injective (D.iCycles k)).mp inferInstance
      have hleft : D.iCycles k (D.cyclesMk a.val (k + 1) (by simp) (hclosed D k a)) = a.val :=
        D.i_cyclesMk a.val (k + 1) _ (hclosed D k a)
      have hright := congrArg (fun f ↦ f a) (D.sc k).moduleCatCyclesIso_inv_iCycles
      exact hleft.trans hright.symm
    rw [heq]
    exact congrArg (fun f ↦ f a) (D.sc k).moduleCatCyclesIso_inv_π
  let zc : S.X₃.cycles p := S.X₃.cyclesMk z.val (p + 1) (by simp) (hclosed S.X₃ p z)
  let gc : C.cycles (p + 1) :=
    C.cyclesMk γ.val (p + 2) (by simp) (hclosed C (p + 1) γ)
  -- The native connecting formula uses the differential of this very middle lift.
  have hd := hS.δ_apply p (p + 1) rfl z.val (hclosed S.X₃ p z) b hb
    (J.f (p + 1) γ.val) hboundary (p + 2) (by simp)
  have heq : (S.X₁.cyclesMk (J.f (p + 1) γ.val) (p + 2) (by simp)
      (hS.d_eq_zero_of_f_eq_d_apply p (p + 1) b _ hboundary (p + 2)) :
      S.X₁.cycles (p + 1)) = cyclesMap J (p + 1) gc := by
    apply (ModuleCat.mono_iff_injective (S.X₁.iCycles (p + 1))).mp inferInstance
    have hleft := S.X₁.i_cyclesMk (J.f (p + 1) γ.val) (p + 2) (by simp)
      (hS.d_eq_zero_of_f_eq_d_apply p (p + 1) b _ hboundary (p + 2))
    have hright := congrArg (fun f ↦ f gc) (cyclesMap_i J (p + 1))
    have hgc : C.iCycles (p + 1) gc = γ.val := C.i_cyclesMk γ.val (p + 2) _ _
    change S.X₁.iCycles (p + 1) (cyclesMap J (p + 1) gc) =
      J.f (p + 1) (C.iCycles (p + 1) gc) at hright
    rw [hgc] at hright
    exact hleft.trans hright.symm
  change hS.δ p (p + 1) rfl (S.X₃.homologyπ p zc) =
    S.X₁.homologyπ (p + 1) _ at hd
  rw [heq] at hd
  have hnat := congrArg (fun f ↦ f gc) (homologyπ_naturality J (p + 1))
  change homologyMap J (p + 1) (C.homologyπ (p + 1) gc) =
    S.X₁.homologyπ (p + 1) (cyclesMap J (p + 1) gc) at hnat
  let e := relativeUnionCohomologyEquiv R A B hA hB (p + 1)
  apply e.injective
  change e (e.symm (hS.δ p (p + 1) rfl
    (relativeSingularCocycleClass R (A ∩ B) p z))) =
      homologyMap J (p + 1) (relativeSingularCocycleClass R (A ∪ B) (p + 1) γ)
  rw [e.apply_symm_apply]
  have hzclass : S.X₃.homologyπ p zc = relativeSingularCocycleClass R (A ∩ B) p z :=
    hclass S.X₃ p z
  have hγclass : C.homologyπ (p + 1) gc =
      relativeSingularCocycleClass R (A ∪ B) (p + 1) γ := hclass C (p + 1) γ
  rw [← hzclass, ← hγclass, hd, hnat]

end AtiyahSinger
