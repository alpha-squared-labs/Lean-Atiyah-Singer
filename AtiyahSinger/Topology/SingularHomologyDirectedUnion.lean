/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactRelativeLocalHomology

/-!
# Singular homology of directed open unions

Public module ID: M2145.

Every original singular homology class over a directed open cover comes from one
stage, and an equality of stage classes holds at a common later stage. The proof
uses the compact images of the finitely many singular simplices in a cycle and
in a boundary primitive. It works over any commutative coefficient ring and
does not require separation or local compactness.

These are the finite-stage facts used in the directed-union part of the local
Poincaré duality argument (Hatcher, *Algebraic Topology*, section 3.3).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Topology

universe u v

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]
variable {ι : Type v} [Nonempty ι] (U : ι → Set X)
variable (hU : ∀ i, IsOpen (U i)) (hdir : Directed (· ⊆ ·) U)
variable (hcover : ⋃ i, U i = Set.univ)

include hU hdir hcover

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem exists_singularChain_directedUnion_stage
    (k : ℕ) (c : (singularChains R X).X k) :
    ∃ (i : ι) (d : (singularChains R (U i)).X k),
      (singularSubspaceChains R (U i)).f k d = c := by
  obtain ⟨K, hK, b, hb⟩ := exists_isCompact_singularChain_support R k c
  obtain ⟨i, hi⟩ := hK.elim_directed_cover U hU (by rw [hcover]; exact Set.subset_univ K)
    hdir
  let f : C(K, U i) :=
    ⟨fun x ↦ ⟨x.val, hi x.property⟩, continuous_subtype_val.subtype_mk _⟩
  have hmap : (singularChainsFunctor R).map (TopCat.ofHom f) ≫
      singularSubspaceChains R (U i) = singularSubspaceChains R K := by
    simp only [singularSubspaceChains, ← Functor.map_comp]
    rfl
  exact ⟨i, ((singularChainsFunctor R).map (TopCat.ofHom f)).f k b,
    (congrArg (fun f ↦ f.f k b) hmap).trans hb⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every class of a directed open union is represented in one of its stages. -/
theorem singularHomologyMap_directedUnion_jointly_surjective
    (k : ℕ) (c : singularHomology R X k) :
    ∃ (i : ι) (d : singularHomology R (U i) k),
      singularHomologyMap R ⟨Subtype.val, continuous_subtype_val⟩ k d = c := by
  let C := singularChains R X
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ k)).mp inferInstance c
  obtain ⟨i, b, hb⟩ := exists_singularChain_directedUnion_stage R U hU hdir hcover k
    (C.iCycles k z)
  let D := singularChains R (U i)
  let f := singularSubspaceChains R (U i)
  let j := (ComplexShape.down ℕ).next k
  -- Injectivity on the original simplex generators detects that the lifted chain is a cycle.
  have hmono : Function.Injective (f.f j) := by
    let : IsSplitMono (f.f j) := isSplitMono_singularChainsMap_of_injective R
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X)) Subtype.val_injective j
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  have hcycle : D.d k j b = 0 := by
    apply hmono
    rw [map_zero]
    have hcomm := congrArg (fun g ↦ g b) (f.comm k j)
    have hzero := congrArg (fun g ↦ g z) (C.iCycles_d k j)
    exact hcomm.symm.trans ((congrArg (fun a ↦ C.d k j a) hb).trans hzero)
  let w : D.cycles k := (D.sc k).moduleCatCyclesIso.inv ⟨b, hcycle⟩
  have hw : D.iCycles k w = b :=
    congrArg (fun g ↦ g ⟨b, hcycle⟩) (D.sc k).moduleCatCyclesIso_inv_iCycles
  have hwz : HomologicalComplex.cyclesMap f k w = z := by
    apply (ModuleCat.mono_iff_injective (C.iCycles k)).mp inferInstance
    exact (congrArg (fun g ↦ g w) (HomologicalComplex.cyclesMap_i f k)).trans
      ((congrArg (fun a ↦ f.f k a) hw).trans hb)
  -- The original homology projection carries this same lifted cycle to the requested class.
  refine ⟨i, D.homologyπ k w, ?_⟩
  exact (congrArg (fun g ↦ g w) (HomologicalComplex.homologyπ_naturality f k)).trans
    ((congrArg (fun a ↦ C.homologyπ k a) hwz).trans hz)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A stage class which vanishes in the union already vanishes in a later stage. -/
theorem singularHomologyMap_directedUnion_eventually_eq_zero
    (i : ι) (k : ℕ) (c : singularHomology R (U i) k)
    (hc : singularHomologyMap R (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X))
      k c = 0) :
    ∃ (j : ι) (hij : U i ⊆ U j),
      singularHomologyMap R
        (⟨fun x ↦ ⟨x.val, hij x.property⟩, continuous_subtype_val.subtype_mk _⟩ :
          C(U i, U j)) k c = 0 := by
  let C := singularChains R X
  let D := singularChains R (U i)
  let f := singularSubspaceChains R (U i)
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (D.homologyπ k)).mp inferInstance c
  let w := HomologicalComplex.cyclesMap f k z
  have hw : C.homologyπ k w = 0 := by
    have h := congrArg (fun g ↦ g z) (HomologicalComplex.homologyπ_naturality f k)
    exact h.symm.trans ((congrArg (fun a ↦ singularHomologyMap R
      ⟨Subtype.val, continuous_subtype_val⟩ k a) hz).trans hc)
  -- A zero homology class has an actual finite boundary primitive in the original complex.
  let S := ShortComplex.mk (C.sc k).toCycles (C.homologyπ k)
    (C.sc k).toCycles_comp_homologyπ
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel S (C.sc k).homologyIsCokernel
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS w hw
  let l := (ComplexShape.down ℕ).prev k
  obtain ⟨j₀, b₀, hb₀⟩ := exists_singularChain_directedUnion_stage R U hU hdir hcover l b
  obtain ⟨j, hij, hj₀j⟩ := hdir i j₀
  let a : C(U i, U j) :=
    ⟨fun x ↦ ⟨x.val, hij x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let a₀ : C(U j₀, U j) :=
    ⟨fun x ↦ ⟨x.val, hj₀j x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let F := (singularChainsFunctor R).map (TopCat.ofHom a)
  let F₀ := (singularChainsFunctor R).map (TopCat.ofHom a₀)
  let E := singularChains R (U j)
  let g := singularSubspaceChains R (U j)
  have hFg : F ≫ g = f := by
    simp only [F, f, g, singularSubspaceChains, ← Functor.map_comp]
    rfl
  have hF₀g : F₀ ≫ g = singularSubspaceChains R (U j₀) := by
    simp only [F₀, g, singularSubspaceChains, ← Functor.map_comp]
    rfl
  let b' := F₀.f l b₀
  have hb' : g.f l b' = b := (congrArg (fun a ↦ a.f l b₀) hF₀g).trans hb₀
  -- At the common stage, chain inclusion detects the very same boundary equation.
  have hboundary : E.d l k b' = E.iCycles k (HomologicalComplex.cyclesMap F k z) := by
    have hmono : Function.Injective (g.f k) := by
      let : IsSplitMono (g.f k) := isSplitMono_singularChainsMap_of_injective R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U j, X)) Subtype.val_injective k
      exact (ModuleCat.mono_iff_injective _).mp inferInstance
    apply hmono
    calc
      g.f k (E.d l k b') = C.d l k b :=
        (congrArg (fun a ↦ a b') (g.comm l k)).symm.trans
          (congrArg (fun a ↦ C.d l k a) hb')
      _ = C.iCycles k w :=
        (congrArg (fun a ↦ a b) (C.sc k).toCycles_i).symm.trans
          (congrArg (fun a ↦ C.iCycles k a) hb)
      _ = f.f k (D.iCycles k z) :=
        congrArg (fun a ↦ a z) (HomologicalComplex.cyclesMap_i f k)
      _ = g.f k (E.iCycles k (HomologicalComplex.cyclesMap F k z)) := by
        exact (congrArg (fun a ↦ a.f k (D.iCycles k z)) hFg).symm.trans
          (congrArg (fun a ↦ g.f k a)
            (congrArg (fun a ↦ a z) (HomologicalComplex.cyclesMap_i F k)).symm)
  have hzboundary : (E.sc k).toCycles b' = HomologicalComplex.cyclesMap F k z := by
    apply (ModuleCat.mono_iff_injective (E.iCycles k)).mp inferInstance
    exact (congrArg (fun a ↦ a b') (E.sc k).toCycles_i).trans hboundary
  refine ⟨j, hij, ?_⟩
  rw [← hz]
  change HomologicalComplex.homologyMap F k (D.homologyπ k z) = 0
  exact (congrArg (fun a ↦ a z) (HomologicalComplex.homologyπ_naturality F k)).trans
    ((congrArg (fun a ↦ E.homologyπ k a) hzboundary.symm).trans
      (congrArg (fun a ↦ a b') (E.sc k).toCycles_comp_homologyπ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Equality of two stage classes in the union is detected at a common later stage. -/
theorem singularHomologyMap_directedUnion_eventually_eq
    (i j : ι) (k : ℕ) (c : singularHomology R (U i) k) (d : singularHomology R (U j) k)
    (hcd : singularHomologyMap R (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X)) k c =
      singularHomologyMap R (⟨Subtype.val, continuous_subtype_val⟩ : C(U j, X)) k d) :
    ∃ (l : ι) (hil : U i ⊆ U l) (hjl : U j ⊆ U l),
      singularHomologyMap R
          (⟨fun x ↦ ⟨x.val, hil x.property⟩, continuous_subtype_val.subtype_mk _⟩ :
            C(U i, U l)) k c =
        singularHomologyMap R
          (⟨fun x ↦ ⟨x.val, hjl x.property⟩, continuous_subtype_val.subtype_mk _⟩ :
            C(U j, U l)) k d := by
  have hcomp {Y Z T : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
      [TopologicalSpace T] (a : C(Y, Z)) (b : C(Z, T)) :
      singularHomologyMap R a k ≫ singularHomologyMap R b k =
        singularHomologyMap R (b.comp a) k := by
    simp only [singularHomologyMap, ← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    rfl
  -- Bring both representatives to one stage, where their difference maps to zero.
  obtain ⟨m, him, hjm⟩ := hdir i j
  let a : C(U i, U m) :=
    ⟨fun x ↦ ⟨x.val, him x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let b : C(U j, U m) :=
    ⟨fun x ↦ ⟨x.val, hjm x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let e : C(U m, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let z := singularHomologyMap R a k c - singularHomologyMap R b k d
  have hz : singularHomologyMap R e k z = 0 := by
    change singularHomologyMap R e k
      (singularHomologyMap R a k c - singularHomologyMap R b k d) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    exact (congrArg (fun f ↦ f c) (hcomp a e)).trans
      (hcd.trans (congrArg (fun f ↦ f d) (hcomp b e)).symm)
  obtain ⟨l, hml, hl⟩ :=
    singularHomologyMap_directedUnion_eventually_eq_zero R U hU hdir hcover m k z hz
  let f : C(U m, U l) :=
    ⟨fun x ↦ ⟨x.val, hml x.property⟩, continuous_subtype_val.subtype_mk _⟩
  have heq : singularHomologyMap R f k (singularHomologyMap R a k c) =
      singularHomologyMap R f k (singularHomologyMap R b k d) := by
    apply sub_eq_zero.mp
    exact (map_sub (singularHomologyMap R f k).hom _ _).symm.trans hl
  refine ⟨l, him.trans hml, hjm.trans hml, ?_⟩
  exact (congrArg (fun g ↦ g c) (hcomp a f)).symm.trans
    (heq.trans (congrArg (fun g ↦ g d) (hcomp b f)))

end AtiyahSinger
