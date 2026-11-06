/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologySequence
public import AtiyahSinger.Topology.RelativeCupCochainMap

/-!
# Connecting homomorphisms and the original relative cup action

Public module ID: M2070.

The connecting homomorphism is computed using actual cocycle lifts in the
degreewise split cochain sequence. Its compatibility with the ordinary-relative
action is the original cochain Leibniz identity, including the degree sign.

Source: Hatcher, Algebraic Topology, Section 3.2, the cup product and the
long exact sequence of a pair or triple.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Limits

universe u

variable (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The connecting map takes a lifted cocycle to the actual class of its coboundary. -/
theorem cohomologyBoundary_cocycleClass
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact) (k : ℕ)
    (c : (S.X₃.sc k).moduleCatLeftHomologyData.K) (b : S.X₂.X k)
    (hb : S.g.f k b = c.val)
    (a : (S.X₁.sc (k + 1)).moduleCatLeftHomologyData.K)
    (ha : S.f.f (k + 1) a.val = S.X₂.d k (k + 1) b) :
    hS.δ k (k + 1) rfl
        ((S.X₃.sc k).moduleCatHomologyIso.inv ((S.X₃.sc k).moduleCatToCycles.range.mkQ c)) =
      (S.X₁.sc (k + 1)).moduleCatHomologyIso.inv
        ((S.X₁.sc (k + 1)).moduleCatToCycles.range.mkQ a) := by
  let elt (M : ModuleCat.{u} R) (m : M) : singularCoefficient R ⟶ M :=
    ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap.smulRight m)
  have hclosed (C : CochainComplex (ModuleCat.{u} R) ℕ) (j : ℕ)
      (z : (C.sc j).moduleCatLeftHomologyData.K) : C.d j (j + 1) z.val = 0 := by
    have h : C.d j ((ComplexShape.up ℕ).next j) z.val = 0 := z.property
    exact (congrArg (fun i ↦ C.d j i z.val = 0) (CochainComplex.next ℕ j)).mp h
  have helt_closed (C : CochainComplex (ModuleCat.{u} R) ℕ) (j : ℕ)
      (z : (C.sc j).moduleCatLeftHomologyData.K) :
      elt (C.X j) z.val ≫ C.d j (j + 1) = 0 := by
    ext r
    change C.d j (j + 1) (r.down • z.val) = 0
    rw [map_smul, hclosed, smul_zero]
  let l₃ := S.X₃.liftCycles (elt _ c.val) (k + 1)
    (CochainComplex.next ℕ k) (helt_closed _ _ c)
  let l₁ := S.X₁.liftCycles (elt _ a.val) (k + 1 + 1)
    (CochainComplex.next ℕ (k + 1)) (helt_closed _ _ a)
  have hbc : elt _ b ≫ S.g.f k = elt _ c.val := by
    ext r
    change S.g.f k (r.down • b) = r.down • c.val
    rw [map_smul, hb]
  have hab : elt _ a.val ≫ S.f.f (k + 1) = elt _ b ≫ S.X₂.d k (k + 1) := by
    ext r
    change S.f.f (k + 1) (r.down • a.val) = S.X₂.d k (k + 1) (r.down • b)
    rw [map_smul, map_smul, ha]
  -- The categorical snake formula is evaluated on the unit of the original coefficient module.
  have hδ := congrArg (fun f ↦ f (ULift.up (1 : R)))
    (hS.δ_eq k (k + 1) rfl (elt _ c.val) (helt_closed _ _ c)
      (elt _ b) hbc (elt _ a.val) hab (k + 1 + 1) (CochainComplex.next ℕ (k + 1)))
  have hlift (C : CochainComplex (ModuleCat.{u} R) ℕ) (j : ℕ)
      (z : (C.sc j).moduleCatLeftHomologyData.K) :
      C.liftCycles (elt _ z.val) (j + 1) (CochainComplex.next ℕ j)
        (helt_closed _ _ z) (ULift.up (1 : R)) = (C.sc j).moduleCatCyclesIso.inv z := by
    apply (ModuleCat.mono_iff_injective (C.iCycles j)).mp inferInstance
    have hleft := congrArg (fun f ↦ f (ULift.up (1 : R)))
      (C.liftCycles_i (elt _ z.val) (j + 1) (CochainComplex.next ℕ j) (helt_closed _ _ z))
    have hright := congrArg (fun f ↦ f z) (C.sc j).moduleCatCyclesIso_inv_iCycles
    change C.iCycles j (C.liftCycles (elt _ z.val) (j + 1) (CochainComplex.next ℕ j)
      (helt_closed _ _ z) (ULift.up (1 : R))) = elt _ z.val (ULift.up (1 : R)) at hleft
    change C.iCycles j ((C.sc j).moduleCatCyclesIso.inv z) = z.val at hright
    rw [hleft, hright]
    exact one_smul R z.val
  change hS.δ k (k + 1) rfl (S.X₃.homologyπ k (l₃ (ULift.up (1 : R)))) =
    S.X₁.homologyπ (k + 1) (l₁ (ULift.up (1 : R))) at hδ
  dsimp only [l₃, l₁] at hδ
  rw [hlift, hlift] at hδ
  have hcπ := congrArg (fun f ↦ f c) (S.X₃.sc k).moduleCatCyclesIso_inv_π
  have haπ := congrArg (fun f ↦ f a) (S.X₁.sc (k + 1)).moduleCatCyclesIso_inv_π
  exact (congrArg (hS.δ k (k + 1) rfl) hcπ).symm.trans (hδ.trans haπ)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The triple connecting homomorphism obeys the original cup Leibniz sign. -/
theorem relativeSingularCohomologyTripleBoundary_action
    {X : Type u} [TopologicalSpace X] (A B : Set X) (hAB : A ⊆ B) (p q : ℕ)
    (a : singularCohomology R X p)
    (b : relativeSingularCohomology R ((Subtype.val : B → X) ⁻¹' A) q) :
    (shortExact_relativeSingularCochainTripleSequence R A B hAB).δ
        (p + q) (p + q + 1) rfl
      (relativeSingularCohomologyAction R ((Subtype.val : B → X) ⁻¹' A) p q
        (singularCohomologyPullback R
          (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X)) p a) b) =
      (-1 : R) ^ p •
        (eqToIso (congrArg (fun k ↦ relativeSingularCohomology R B k)
          (Nat.add_assoc p q 1).symm)).hom
          (relativeSingularCohomologyAction R B p (q + 1) a
            ((shortExact_relativeSingularCochainTripleSequence R A B hAB).δ
              q (q + 1) rfl b)) := by
  let S := relativeSingularCochainTripleSequence R A B hAB
  have hS : S.ShortExact := shortExact_relativeSingularCochainTripleSequence R A B hAB
  let C := singularCochains R X
  let A' : Set B := (Subtype.val : B → X) ⁻¹' A
  let i : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let G := (singularCochainsFunctor R).map (TopCat.ofHom i).op
  let cc (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (z : (D.sc k).moduleCatLeftHomologyData.K) : D.homology k :=
    (D.sc k).moduleCatHomologyIso.inv ((D.sc k).moduleCatToCycles.range.mkQ z)
  have hrep (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ) (z : D.homology k) :
      ∃ c : (D.sc k).moduleCatLeftHomologyData.K, cc D k c = z := by
    obtain ⟨c, hc⟩ := (D.sc k).moduleCatToCycles.range.mkQ_surjective
      ((D.sc k).moduleCatHomologyIso.hom z)
    refine ⟨c, ?_⟩
    dsimp only [cc]
    rw [hc]
    exact congrArg (fun f ↦ f z) (D.sc k).moduleCatHomologyIso.hom_inv_id
  have hclosed (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (z : (D.sc k).moduleCatLeftHomologyData.K) : D.d k (k + 1) z.val = 0 := by
    have h : D.d k ((ComplexShape.up ℕ).next k) z.val = 0 := z.property
    exact (congrArg (fun j ↦ D.d k j z.val = 0) (CochainComplex.next ℕ k)).mp h
  have hcycle (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ) (z : D.X k)
      (hz : D.d k (k + 1) z = 0) : z ∈ (D.sc k).g.hom.ker := by
    change D.d k ((ComplexShape.up ℕ).next k) z = 0
    exact (congrArg (fun j ↦ D.d k j z = 0) (CochainComplex.next ℕ k)).mpr hz
  -- Choose the same ordinary cocycle and an actual lifted relative cocycle.
  obtain ⟨α, hα⟩ := hrep C p a
  obtain ⟨β, hβ⟩ := hrep S.X₃ q b
  have hSn (k : ℕ) :
      (S.map (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) k)).ShortExact :=
    hS.map_of_exact _
  obtain ⟨β₂, hβ₂⟩ := (hSn q).moduleCat_surjective_g β.val
  change S.g.f q β₂ = β.val at hβ₂
  have hdb : S.g.f (q + 1) (S.X₂.d q (q + 1) β₂) = 0 := by
    have h := congrArg (fun f ↦ f β₂) (S.g.comm q (q + 1))
    change S.X₃.d q (q + 1) (S.g.f q β₂) =
      S.g.f (q + 1) (S.X₂.d q (q + 1) β₂) at h
    rw [← h, hβ₂, hclosed]
  obtain ⟨γ₁, hγ₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (hSn (q + 1)).exact (S.X₂.d q (q + 1) β₂) hdb
  change S.f.f (q + 1) γ₁ = S.X₂.d q (q + 1) β₂ at hγ₁
  have hγclosed : S.X₁.d (q + 1) (q + 1 + 1) γ₁ = 0 := by
    apply (hSn (q + 1 + 1)).moduleCat_injective_f
    rw [map_zero]
    change S.f.f (q + 1 + 1) (S.X₁.d (q + 1) (q + 1 + 1) γ₁) = 0
    have h := congrArg (fun f ↦ f γ₁) (S.f.comm (q + 1) (q + 1 + 1))
    change S.X₂.d (q + 1) (q + 1 + 1) (S.f.f (q + 1) γ₁) =
      S.f.f (q + 1 + 1) (S.X₁.d (q + 1) (q + 1 + 1) γ₁) at h
    rw [← h, hγ₁]
    exact congrArg (fun f ↦ f β₂) (S.X₂.d_comp_d q (q + 1) (q + 1 + 1))
  let γ : relativeSingularCocycles R B (q + 1) := ⟨γ₁, hcycle _ _ _ hγclosed⟩
  have hδβ : hS.δ q (q + 1) rfl (cc S.X₃ q β) = cc S.X₁ (q + 1) γ :=
    cohomologyBoundary_cocycleClass R S hS q β β₂ hβ₂ γ hγ₁
  let αB : singularCocycles R B p := ⟨G.f p α.val, by
    apply hcycle
    have h := congrArg (fun f ↦ f α.val) (G.comm p (p + 1))
    change (singularCochains R B).d p (p + 1) (G.f p α.val) =
      G.f (p + 1) (C.d p (p + 1) α.val) at h
    rw [h, hclosed, map_zero]⟩
  have hαB : singularCohomologyPullback R i p (cc C p α) =
      singularCocycleClass R B p αB := by
    let z : C.cycles p := (C.sc p).moduleCatCyclesIso.inv α
    let w : (singularCochains R B).cycles p :=
      ((singularCochains R B).sc p).moduleCatCyclesIso.inv αB
    have hmap : cyclesMap G p z = w := by
      apply (ModuleCat.mono_iff_injective ((singularCochains R B).iCycles p)).mp inferInstance
      have h := congrArg (fun f ↦ f z) (cyclesMap_i G p)
      have hz := congrArg (fun f ↦ f α) (C.sc p).moduleCatCyclesIso_inv_iCycles
      have hw := congrArg (fun f ↦ f αB)
        ((singularCochains R B).sc p).moduleCatCyclesIso_inv_iCycles
      change C.iCycles p z = α.val at hz
      change (singularCochains R B).iCycles p w = αB.val at hw
      change (singularCochains R B).iCycles p (cyclesMap G p z) = G.f p (C.iCycles p z) at h
      rw [h, hz, hw]
    have h := congrArg (fun f ↦ f z) (homologyπ_naturality G p)
    have hz := congrArg (fun f ↦ f α) (C.sc p).moduleCatCyclesIso_inv_π
    have hw := congrArg (fun f ↦ f αB) ((singularCochains R B).sc p).moduleCatCyclesIso_inv_π
    change C.homologyπ p z = cc C p α at hz
    change (singularCochains R B).homologyπ p w = singularCocycleClass R B p αB at hw
    change singularCohomologyPullback R i p (C.homologyπ p z) =
      (singularCochains R B).homologyπ p (cyclesMap G p z) at h
    rw [hmap, hz, hw] at h
    exact h
  -- Naturality supplies the lift of the product; Leibniz computes its coboundary.
  let βp := relativeSingularCocycleAction R A' p q αB β
  let β₂p := relativeSingularCochainAction R A p q α.val β₂
  let γp := relativeSingularCocycleAction R B p (q + 1) α γ
  let e : p + (q + 1) = p + q + 1 := (Nat.add_assoc p q 1).symm
  let γp' : relativeSingularCocycles R B (p + q + 1) := (-1 : R) ^ p • γp
  have hβp : S.g.f (p + q) β₂p = βp.val := by
    have h := relativeSingularCochainAction_natural R i A' A (fun _ hz ↦ hz) p q α.val β₂
    change S.g.f (p + q) β₂p =
      relativeSingularCochainAction R A' p q αB.val (S.g.f q β₂) at h
    rw [hβ₂] at h
    exact h
  have hγp : S.f.f (p + q + 1) γp'.val = S.X₂.d (p + q) (p + q + 1) β₂p := by
    have hnat := relativeSingularCochainAction_natural R (ContinuousMap.id X)
      A B (fun _ hz ↦ hAB hz) p (q + 1) α.val γ.val
    have hcid : (singularCochainsFunctor R).map (TopCat.ofHom (ContinuousMap.id X)).op = 𝟙 C :=
      (singularCochainsFunctor R).map_id _
    rw [hcid] at hnat
    change S.f.f (p + (q + 1)) γp.val =
      relativeSingularCochainAction R A p (q + 1) α.val (S.f.f (q + 1) γ.val) at hnat
    have hleib := relativeSingularCochainAction_leibniz R A p q α.val β₂
    rw [hclosed C p α] at hleib
    simp only [LinearMap.zero_apply, map_zero, zero_add] at hleib
    change S.X₂.d (p + q) (p + q + 1) β₂p =
      (-1 : R) ^ p • (S.X₂.XIsoOfEq e).hom
        (relativeSingularCochainAction R A p (q + 1) α.val (S.X₂.d q (q + 1) β₂)) at hleib
    change S.f.f (p + (q + 1)) ((-1 : R) ^ p • γp.val) = _
    rw [map_smul, hnat, hγ₁]
    exact hleib.symm
  have hδprod := cohomologyBoundary_cocycleClass R S hS (p + q) βp β₂p hβp γp' hγp
  change singularCocycleClass R X p α = a at hα
  change relativeSingularCocycleClass R A' q β = b at hβ
  change singularCohomologyPullback R i p (singularCocycleClass R X p α) =
    singularCocycleClass R B p αB at hαB
  change hS.δ q (q + 1) rfl (relativeSingularCocycleClass R A' q β) =
    relativeSingularCocycleClass R B (q + 1) γ at hδβ
  change hS.δ (p + q) (p + q + 1) rfl (relativeSingularCocycleClass R A' (p + q) βp) =
    relativeSingularCocycleClass R B (p + q + 1) γp' at hδprod
  rw [← hα, ← hβ, hαB, relativeSingularCohomologyAction_cocycleClass]
  rw [hδprod, hδβ]
  change relativeSingularCocycleClass R B (p + (q + 1)) ((-1 : R) ^ p • γp) =
    (-1 : R) ^ p • relativeSingularCohomologyAction R B p (q + 1)
      (singularCocycleClass R X p α) (relativeSingularCocycleClass R B (q + 1) γ)
  rw [map_smul]
  congr 1
  exact (relativeSingularCohomologyAction_cocycleClass R B p (q + 1) α γ).symm

end AtiyahSinger
