/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyMayerVietorisBoundary
public import AtiyahSinger.Topology.SingularHomologyMayerVietoris
public import AtiyahSinger.Topology.SmallRelativeHomology
public import AtiyahSinger.Topology.SupportedCapLocalization

/-!
# The cap Mayer–Vietoris connecting identity

Public module ID: M2055.

The two localized cap chains lift the original sum in ordinary homology.
Their boundary is the difference of the overlap cap, with sign `(-1)^(p+1)`.
Both sides use the same relative cycle and the original cochain differential.
The computation includes output degree zero.

Source: Hatcher, Algebraic Topology, section 3.3, the Mayer–Vietoris proof
of Poincaré duality. PoincareLib's dimension-three connecting proof was
consulted as a method reference; all maps here are the project's original
arbitrary-degree, arbitrary-coefficient singular maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 600000 in
-- The single representative computation tracks both chain quotients and four cap localizations.
/-- A corrected cochain lift computes the signed cap square on a common small representative. -/
theorem relativeSingularCapProduct_mayerVietoris_representative
    (U V A B : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : U ∪ V = Set.univ)
    (hAU : Aᶜ ⊆ U) (hBV : Bᶜ ⊆ V) (p q : ℕ)
    (c : (singularChains R X).X (p + (q + 1)))
    (c' : (singularChains R X).X ((p + 1) + q))
    (hc' : ((singularChains R X).XIsoOfEq
      ((Nat.add_assoc p q 1).symm.trans (Nat.add_right_comm p q 1))).hom c = c')
    (hcU : c ∈ ((smallSingularChainsInclusion R {U, A}).f (p + (q + 1))).hom.range)
    (hcV : c ∈ ((smallSingularChainsInclusion R {V, B}).f (p + (q + 1))).hom.range)
    (hcW : c' ∈ ((smallSingularChainsInclusion R {U ∩ V, A ∪ B}).f ((p + 1) + q)).hom.range)
    (z : relativeSingularCycles R (A ∩ B) (p + (q + 1)))
    (hz : z.val = (relativeSingularChainsProjection R (A ∩ B)).f (p + (q + 1)) c)
    (z' : relativeSingularCycles R (A ∪ B) ((p + 1) + q))
    (hz' : z'.val = (relativeSingularChainsProjection R (A ∪ B)).f ((p + 1) + q) c')
    (φ : relativeSingularCocycles R (A ∩ B) p)
    (α : (relativeSingularCochains R A).X p) (β : (relativeSingularCochains R B).X p)
    (γ : relativeSingularCocycles R (A ∪ B) (p + 1))
    (hφ : (relativeSingularCochainEquiv R A p α).val +
      (relativeSingularCochainEquiv R B p β).val =
        (relativeSingularCochainEquiv R (A ∩ B) p φ.val).val)
    (hα : (singularCochains R X).d p (p + 1) (relativeSingularCochainEquiv R A p α).val =
      (relativeSingularCochainEquiv R (A ∪ B) (p + 1) γ.val).val)
    (hβ : (singularCochains R X).d p (p + 1) (relativeSingularCochainEquiv R B p β).val =
      -(relativeSingularCochainEquiv R (A ∪ B) (p + 1) γ.val).val)
    (w : relativeSingularHomology R ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' (A ∪ B)) ((p + 1) + q))
    (hw : relativeSingularHomologyMap R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
        (A := (Subtype.val : ↥(U ∩ V) → X) ⁻¹' (A ∪ B)) (B := A ∪ B)
        (fun _ hx ↦ hx) ((p + 1) + q) w = relativeSingularCycleClass R (A ∪ B) ((p + 1) + q) z') :
    singularHomologyMayerVietorisBoundary R U V hU hV hcover q
        (relativeSingularCapProduct R (A ∩ B) p (q + 1)
          (relativeSingularCocycleClass R (A ∩ B) p φ)
          (relativeSingularCycleClass R (A ∩ B) (p + (q + 1)) z)) =
      (-1 : R) ^ (p + 1) • relativeSingularCapProduct R
        ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' (A ∪ B)) (p + 1) q
        (relativeSingularCohomologyPullback R
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          (fun _ hx ↦ hx) (p + 1) (relativeSingularCocycleClass R (A ∪ B) (p + 1) γ)) w := by
  let C := singularChains R X
  let S := singularMayerVietorisShortComplex R U V
  let hS := shortExact_singularMayerVietorisShortComplex R U V
  let I := Abelian.image.ι (singularSubspaceSumChains R U V)
  let sign := (-1 : R) ^ (p + 1)
  let a := singularLocalizedCap R U A p (q + 1) c hcU α
  let b := singularLocalizedCap R V B p (q + 1) c hcV β
  let fst := (biprod.fst : singularChains R U ⊞ singularChains R V ⟶ _)
  let snd := (biprod.snd : singularChains R U ⊞ singularChains R V ⟶ _)
  let inl := (biprod.inl : singularChains R U ⟶ singularChains R U ⊞ singularChains R V)
  let inr := (biprod.inr : singularChains R V ⟶ singularChains R U ⊞ singularChains R V)
  let middle := inl.f (q + 1) a + inr.f (q + 1) b
  let ambientCycle := relativeSingularCycleCap R (A ∩ B) p (q + 1) φ z
  have hW : (A ∪ B)ᶜ ⊆ U ∩ V := fun _ hx ↦
    ⟨hAU (fun h ↦ hx (Or.inl h)), hBV (fun h ↦ hx (Or.inr h))⟩
  obtain ⟨overlapCycle, hoverlap, hoverlapClass⟩ := exists_singularLocalizedCap_cycleClass R
    (U ∩ V) (A ∪ B) (hU.inter hV) (hA.union hB) hW (p + 1) q c' hcW z' hz' γ w hw
  -- The relative cycle's boundary lies in both vanishing regions.
  have hdc : C.d (p + (q + 1)) (p + q) c ∈
      ((singularSubspaceChains R (A ∩ B)).f (p + q)).hom.range := by
    let π := relativeSingularChainsProjection R (A ∩ B)
    have hclosed : (relativeSingularChains R (A ∩ B)).d
        (p + (q + 1)) (p + q) z.val = 0 := by
      have h : (relativeSingularChains R (A ∩ B)).dFrom (p + (q + 1)) z.val = 0 := z.property
      have hrel : (ComplexShape.down ℕ).Rel (p + (q + 1)) (p + q) := by dsimp; omega
      have heq := congrArg ((relativeSingularChains R (A ∩ B)).xNextIso hrel).hom h
      rw [← ModuleCat.comp_apply, dFrom_comp_xNextIso, map_zero] at heq
      exact heq
    have hπ := congrArg (fun f ↦ f c) (π.comm (p + (q + 1)) (p + q))
    change (relativeSingularChains R (A ∩ B)).d (p + (q + 1)) (p + q)
        (π.f (p + (q + 1)) c) = π.f (p + q) (C.d (p + (q + 1)) (p + q) c) at hπ
    have hzdc : π.f (p + q) (C.d (p + (q + 1)) (p + q) c) = 0 :=
      hπ.symm.trans (by rw [← hz]; exact hclosed)
    have hexact := (shortExact_singularSubspaceChains R (A ∩ B)).exact.map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) (p + q))
    exact (ShortComplex.moduleCat_exact_iff _).mp hexact _ hzdc
  rw [range_singularSubspaceChains_inter] at hdc
  have hzero (E : Set X) (η : (relativeSingularCochains R E).X p)
      (hE : C.d (p + (q + 1)) (p + q) c ∈ ((singularSubspaceChains R E).f (p + q)).hom.range) :
      singularCochainCap R X p q (relativeSingularCochainEquiv R E p η).val
        (C.d (p + (q + 1)) (p + q) c) = 0 := by
    obtain ⟨v, hv⟩ := hE
    rw [← hv]
    exact congrArg (fun f ↦ f v) (singularCochainCap_comp_subspace_eq_zero R E p q η)
  let overlapCap := singularCochainCap R X (p + 1) q
    (relativeSingularCochainEquiv R (A ∪ B) (p + 1) γ.val).val c'
  have hboundaryA : C.d (q + 1) q
      (singularCochainCap R X p (q + 1) (relativeSingularCochainEquiv R A p α).val c) =
        sign • overlapCap := by
    rw [singularCochainCap_boundary, hzero A α hdc.1, hα, hc']
    simp [sign, overlapCap, pow_succ]
  have hboundaryB : C.d (q + 1) q
      (singularCochainCap R X p (q + 1) (relativeSingularCochainEquiv R B p β).val c) =
        -(sign • overlapCap) := by
    rw [singularCochainCap_boundary, hzero B β hdc.2, hβ, hc']
    rw [map_neg, LinearMap.neg_apply]
    simp [sign, overlapCap, pow_succ]
  have hoverlapIncl : (singularSubspaceChains R (U ∩ V)).f q overlapCycle.val = overlapCap := by
    rw [hoverlap]
    exact singularSubspaceChains_singularLocalizedCap R (U ∩ V) (A ∪ B) (p + 1) q c' hcW γ.val
  have hfst : fst.f (q + 1) middle = a := by
    change fst.f (q + 1) (inl.f (q + 1) a + inr.f (q + 1) b) = a
    rw [map_add]
    have h₁ := congrArg (fun f ↦ f.f (q + 1) a) (biprod.inl_fst (X := singularChains R U)
      (Y := singularChains R V))
    have h₂ := congrArg (fun f ↦ f.f (q + 1) b) (biprod.inr_fst (X := singularChains R U)
      (Y := singularChains R V))
    change fst.f (q + 1) (inl.f (q + 1) a) = a at h₁
    change fst.f (q + 1) (inr.f (q + 1) b) = 0 at h₂
    rw [h₁, h₂, add_zero]
  have hsnd : snd.f (q + 1) middle = b := by
    change snd.f (q + 1) (inl.f (q + 1) a + inr.f (q + 1) b) = b
    rw [map_add]
    have h₁ := congrArg (fun f ↦ f.f (q + 1) a) (biprod.inl_snd (X := singularChains R U)
      (Y := singularChains R V))
    have h₂ := congrArg (fun f ↦ f.f (q + 1) b) (biprod.inr_snd (X := singularChains R U)
      (Y := singularChains R V))
    change snd.f (q + 1) (inl.f (q + 1) a) = 0 at h₁
    change snd.f (q + 1) (inr.f (q + 1) b) = b at h₂
    rw [h₁, h₂, zero_add]
  -- The two cap lifts have exactly the signed overlap boundary in the original sequence.
  have hboundary : S.f.f q (sign • overlapCycle.val) = S.X₂.d (q + 1) q middle := by
    have hext {x y : S.X₂.X q} (hx : fst.f q x = fst.f q y)
        (hy : snd.f q x = snd.f q y) : x = y := by
      have hsplit (t : S.X₂.X q) : inl.f q (fst.f q t) + inr.f q (snd.f q t) = t :=
        congrArg (fun f ↦ f.f q t)
          (biprod.total (X := singularChains R U) (Y := singularChains R V))
      rw [← hsplit x, hx, hy, hsplit y]
    have hinj (E : Set X) : Function.Injective ((singularSubspaceChains R E).f q) := by
      let : IsSplitMono ((singularSubspaceChains R E).f q) :=
        isSplitMono_singularChainsMap_of_injective R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(E, X)) Subtype.val_injective q
      exact (ModuleCat.mono_iff_injective _).mp inferInstance
    apply hext
    · apply hinj U
      have hdiff : S.f ≫ fst ≫ singularSubspaceChains R U = singularSubspaceChains R (U ∩ V) := by
        simp [S, fst, singularMayerVietorisShortComplex, singularSubspaceChains, ← Functor.map_comp]
        rfl
      have hd := congrArg (fun f ↦ f middle) (fst.comm (q + 1) q)
      have hi := congrArg (fun f ↦ f a) ((singularSubspaceChains R U).comm (q + 1) q)
      change (singularChains R U).d (q + 1) q (fst.f (q + 1) middle) =
        fst.f q (S.X₂.d (q + 1) q middle) at hd
      rw [← hd, hfst]
      have hl := congrArg (fun f ↦ f.f q (sign • overlapCycle.val)) hdiff
      change (singularSubspaceChains R U).f q (fst.f q (S.f.f q (sign • overlapCycle.val))) =
        (singularSubspaceChains R (U ∩ V)).f q (sign • overlapCycle.val) at hl
      rw [hl, map_smul, hoverlapIncl]
      change C.d (q + 1) q ((singularSubspaceChains R U).f (q + 1) a) =
        (singularSubspaceChains R U).f q ((singularChains R U).d (q + 1) q a) at hi
      rw [← hi, singularSubspaceChains_singularLocalizedCap]
      exact hboundaryA.symm
    · apply hinj V
      have hdiff : S.f ≫ snd ≫ singularSubspaceChains R V = -singularSubspaceChains R (U ∩ V) := by
        simp [S, snd, singularMayerVietorisShortComplex, singularSubspaceChains, ← Functor.map_comp]
        rfl
      have hd := congrArg (fun f ↦ f middle) (snd.comm (q + 1) q)
      have hi := congrArg (fun f ↦ f b) ((singularSubspaceChains R V).comm (q + 1) q)
      change (singularChains R V).d (q + 1) q (snd.f (q + 1) middle) =
        snd.f q (S.X₂.d (q + 1) q middle) at hd
      rw [← hd, hsnd]
      have hl := congrArg (fun f ↦ f.f q (sign • overlapCycle.val)) hdiff
      change (singularSubspaceChains R V).f q (snd.f q (S.f.f q (sign • overlapCycle.val))) =
        -((singularSubspaceChains R (U ∩ V)).f q (sign • overlapCycle.val)) at hl
      rw [hl, map_smul, hoverlapIncl]
      change C.d (q + 1) q ((singularSubspaceChains R V).f (q + 1) b) =
        (singularSubspaceChains R V).f q ((singularChains R V).d (q + 1) q b) at hi
      rw [← hi, singularSubspaceChains_singularLocalizedCap]
      exact hboundaryB.symm
  -- Inclusion of the lifted sum is exactly cap with the original relative cocycle.
  have hsum : I.f (q + 1) (S.g.f (q + 1) middle) = ambientCycle.val := by
    have hfac := congrArg (fun f ↦ f.f (q + 1) middle)
      (Abelian.image.fac (singularSubspaceSumChains R U V))
    change I.f (q + 1) (S.g.f (q + 1) middle) =
      (singularSubspaceSumChains R U V).f (q + 1) middle at hfac
    have hdesc := congrArg (fun f ↦ f.f (q + 1) middle)
      (biprod.desc_eq (f := singularSubspaceChains R U) (g := singularSubspaceChains R V))
    change (singularSubspaceSumChains R U V).f (q + 1) middle =
      (singularSubspaceChains R U).f (q + 1) (fst.f (q + 1) middle) +
      (singularSubspaceChains R V).f (q + 1) (snd.f (q + 1) middle) at hdesc
    rw [hfac, hdesc, hfst, hsnd, singularSubspaceChains_singularLocalizedCap,
      singularSubspaceChains_singularLocalizedCap]
    change singularCochainCap R X p (q + 1) _ c + singularCochainCap R X p (q + 1) _ c =
      relativeSingularCochainCap R (A ∩ B) p (q + 1) φ.val z.val
    rw [hz, relativeSingularCochainCap_projection, ← LinearMap.add_apply, ← map_add, hφ]
  let sumCycle : (S.X₃.sc (q + 1)).moduleCatLeftHomologyData.K := ⟨S.g.f (q + 1) middle, by
    change S.X₃.dFrom (q + 1) _ = 0
    apply (ModuleCat.mono_iff_injective (I.next (q + 1))).mp inferInstance
    have hd := congrArg (fun f ↦ f (S.g.f (q + 1) middle)) (I.comm_from (q + 1))
    change C.dFrom (q + 1) (I.f (q + 1) (S.g.f (q + 1) middle)) =
      I.next (q + 1) (S.X₃.dFrom (q + 1) (S.g.f (q + 1) middle)) at hd
    have hclosed : C.dFrom (q + 1) ambientCycle.val = 0 := ambientCycle.property
    rw [← hd, hsum, hclosed, map_zero]⟩
  have hclass := homologyMap_cycleClass R S.X₃ C I (q + 1) sumCycle ambientCycle hsum
  change homologyMap I (q + 1)
    ((S.X₃.sc (q + 1)).moduleCatHomologyIso.inv
      ((S.X₃.sc (q + 1)).moduleCatToCycles.range.mkQ sumCycle)) =
        singularCycleClass R X (q + 1) ambientCycle at hclass
  have hδ := homologyConnecting_cycleClass R S hS q sumCycle middle rfl
    (sign • overlapCycle) hboundary
  let : IsIso (homologyMap I (q + 1)) :=
    isIso_homologyMap_singularMayerVietorisImageInclusion R U V hU hV hcover (q + 1)
  rw [relativeSingularCapProduct_cycleClass]
  change (inv (homologyMap I (q + 1)) ≫ hS.δ (q + 1) q rfl)
    (singularCycleClass R X (q + 1) ambientCycle) = _
  rw [← hclass]
  change hS.δ (q + 1) q rfl
    (inv (homologyMap I (q + 1)) (homologyMap I (q + 1) _)) = _
  rw [← ModuleCat.comp_apply, IsIso.hom_inv_id, ModuleCat.id_apply, hδ]
  change singularCycleClass R ↥(U ∩ V) q (sign • overlapCycle) = _
  rw [map_smul, hoverlapClass]

end AtiyahSinger
