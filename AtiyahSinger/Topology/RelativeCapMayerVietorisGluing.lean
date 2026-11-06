/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCapMayerVietoris
public import AtiyahSinger.Topology.RelativeCohomologyMayerVietorisBiprod

/-!
# The relative cap connecting square on arbitrary classes

Public module ID: M2056.

Correct the original cochain lift, choose one relative cycle small for the
common four-set refinement, and apply the native signed connecting computation.
The overlap class is specified by its actual relative excision image.
No injectivity of the inclusion on absolute homology is assumed.

Source: Hatcher, Algebraic Topology, section 3.3, the supported cap gluing argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- The gluing proof retains the native dual biproduct and the relative degree transports.
/-- The actual relative cap products commute with the Mayer–Vietoris boundaries
with the original cap sign. -/
theorem relativeSingularCapProduct_mayerVietoris
    (U V A B : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : U ∪ V = Set.univ)
    (hAU : Aᶜ ⊆ U) (hBV : Bᶜ ⊆ V) (p q : ℕ)
    (φ₀ : relativeSingularCohomology R (A ∩ B) p)
    (z₀ : relativeSingularHomology R (A ∩ B) (p + (q + 1)))
    (w : relativeSingularHomology R ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' (A ∪ B)) ((p + 1) + q))
    (hw : relativeSingularHomologyMap R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
        (A := (Subtype.val : ↥(U ∩ V) → X) ⁻¹' (A ∪ B)) (B := A ∪ B)
        (fun _ hx ↦ hx) ((p + 1) + q) w =
      (eqToIso (congrArg (relativeSingularHomology R (A ∪ B))
        ((Nat.add_assoc p q 1).symm.trans (Nat.add_right_comm p q 1)))).hom
          (relativeSingularHomologyInclusion R (A ∩ B) (A ∪ B)
            (Set.inter_subset_left.trans Set.subset_union_left) (p + (q + 1)) z₀)) :
    singularHomologyMayerVietorisBoundary R U V hU hV hcover q
        (relativeSingularCapProduct R (A ∩ B) p (q + 1) φ₀ z₀) =
      (-1 : R) ^ (p + 1) • relativeSingularCapProduct R
        ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' (A ∪ B)) (p + 1) q
        (relativeSingularCohomologyPullback R
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          (fun _ hx ↦ hx) (p + 1)
          (relativeSingularCohomologyMayerVietorisBoundary R A B hA hB p φ₀)) w := by
  let D := singularCochainDualFunctor R
  let inc (E : Set X) := D.map (relativeSingularChainsProjection R E).op
  let res {E F : Set X} (h : E ⊆ F) :=
    D.map ((relativeSingularChainsFunctor R X).map (homOfLE h)).op
  have hres {E F : Set X} (h : E ⊆ F) : res h ≫ inc E = inc F := by
    have hq : relativeSingularChainsProjection R E ≫
        (relativeSingularChainsFunctor R X).map (homOfLE h) =
          relativeSingularChainsProjection R F := by
      simp [relativeSingularChainsFunctor, relativeSingularChainsMap,
        relativeSingularChainsProjection]
    change D.map _ ≫ D.map _ = D.map _
    rw [← D.map_comp]
    change D.map (relativeSingularChainsProjection R E ≫
      (relativeSingularChainsFunctor R X).map (homOfLE h)).op = D.map _
    rw [hq]
  -- Choose an actual cocycle and correct its native middle lift to a union-relative cocycle.
  obtain ⟨φ, hφq⟩ := (relativeSingularCoboundaries R (A ∩ B) p).mkQ_surjective
    (((relativeSingularCochains R (A ∩ B)).sc p).moduleCatHomologyIso.hom φ₀)
  have hφclass : relativeSingularCocycleClass R (A ∩ B) p φ = φ₀ := by
    change ((relativeSingularCochains R (A ∩ B)).sc p).moduleCatHomologyIso.inv
      ((relativeSingularCoboundaries R (A ∩ B) p).mkQ φ) = φ₀
    rw [hφq]
    exact congrArg (fun f ↦ f φ₀)
      ((relativeSingularCochains R (A ∩ B)).sc p).moduleCatHomologyIso.hom_inv_id
  have hφclosed : (relativeSingularCochains R (A ∩ B)).d p (p + 1) φ.val = 0 := by
    have h : (relativeSingularCochains R (A ∩ B)).dFrom p φ.val = 0 := φ.property
    have hh := congrArg ((relativeSingularCochains R (A ∩ B)).xNextIso rfl).hom h
    rw [← ModuleCat.comp_apply, dFrom_comp_xNextIso, map_zero] at hh
    exact hh
  obtain ⟨b, γ₀, hb, hγclosed, hboundary⟩ :=
    exists_relativeSingularCohomologyMayerVietoris_corrected_lift R A B hA hB p φ.val hφclosed
  let γ : relativeSingularCocycles R (A ∪ B) (p + 1) := ⟨γ₀, by
    change (relativeSingularCochains R (A ∪ B)).dFrom (p + 1) γ₀ = 0
    rw [dFrom_eq (r := show (ComplexShape.up ℕ).Rel (p + 1) (p + 2) from rfl),
      ModuleCat.comp_apply, hγclosed, map_zero]⟩
  let S := relativeSingularCochainMayerVietorisSequence R A B
  let J := D.map (relativeUnionSingularChainsToRelative R A B).op
  let e := relativeSingularCochainMayerVietorisMiddleIso R A B
  let tA := e.hom ≫ (biprod.fst : relativeSingularCochains R A ⊞ relativeSingularCochains R B ⟶ _)
  let tB := e.hom ≫ (biprod.snd : relativeSingularCochains R A ⊞ relativeSingularCochains R B ⟶ _)
  let α := tA.f p b
  let β := tB.f p b
  have hsum : tA ≫ res (Set.inter_subset_left : A ∩ B ⊆ A) +
      tB ≫ res (Set.inter_subset_right : A ∩ B ⊆ B) = S.g := by
    have h := relativeSingularCochainMayerVietorisMiddleIso_hom_sum R A B
    rw [biprod.desc_eq, Preadditive.comp_add, ← Category.assoc, ← Category.assoc] at h
    exact h
  have hsumAmbient : tA ≫ inc A + tB ≫ inc B = S.g ≫ inc (A ∩ B) := by
    have h := congrArg (fun f ↦ f ≫ inc (A ∩ B)) hsum
    simpa only [Preadditive.add_comp, Category.assoc, hres] using h
  have hφ : (relativeSingularCochainEquiv R A p α).val +
      (relativeSingularCochainEquiv R B p β).val =
        (relativeSingularCochainEquiv R (A ∩ B) p φ.val).val := by
    have h := congrArg (fun f ↦ f.f p b) hsumAmbient
    change (inc A).f p α + (inc B).f p β = (inc (A ∩ B)).f p (S.g.f p b) at h
    rw [hb] at h
    exact h
  have hfirst : J ≫ S.f ≫ tA = res (Set.subset_union_left : A ⊆ A ∪ B) := by
    have h := congrArg (fun f ↦ f ≫
      (biprod.fst : relativeSingularCochains R A ⊞ relativeSingularCochains R B ⟶ _))
      (relativeSingularCochainMayerVietorisMiddleIso_comparison_difference R A B)
    simpa only [Category.assoc, biprod.lift_fst] using h
  have hsecond : J ≫ S.f ≫ tB = -res (Set.subset_union_right : B ⊆ A ∪ B) := by
    have h := congrArg (fun f ↦ f ≫
      (biprod.snd : relativeSingularCochains R A ⊞ relativeSingularCochains R B ⟶ _))
      (relativeSingularCochainMayerVietorisMiddleIso_comparison_difference R A B)
    simpa only [Category.assoc, biprod.lift_snd] using h
  have hα : (singularCochains R X).d p (p + 1) (relativeSingularCochainEquiv R A p α).val =
      (relativeSingularCochainEquiv R (A ∪ B) (p + 1) γ.val).val := by
    have hd := congrArg (fun f ↦ f.f (p + 1) γ₀) hfirst
    change tA.f (p + 1) (S.f.f (p + 1) (J.f (p + 1) γ₀)) =
      (res (Set.subset_union_left : A ⊆ A ∪ B)).f (p + 1) γ₀ at hd
    rw [hboundary] at hd
    have hc := congrArg (fun f ↦ f b) (tA.comm p (p + 1))
    change (relativeSingularCochains R A).d p (p + 1) α =
      tA.f (p + 1) (S.X₂.d p (p + 1) b) at hc
    have hi := congrArg (fun f ↦ f α) ((inc A).comm p (p + 1))
    change (singularCochains R X).d p (p + 1) ((inc A).f p α) =
      (inc A).f (p + 1) ((relativeSingularCochains R A).d p (p + 1) α) at hi
    rw [hc, hd] at hi
    exact hi.trans (congrArg (fun f ↦ f.f (p + 1) γ₀) (hres Set.subset_union_left))
  have hβ : (singularCochains R X).d p (p + 1) (relativeSingularCochainEquiv R B p β).val =
      -(relativeSingularCochainEquiv R (A ∪ B) (p + 1) γ.val).val := by
    have hd := congrArg (fun f ↦ f.f (p + 1) γ₀) hsecond
    change tB.f (p + 1) (S.f.f (p + 1) (J.f (p + 1) γ₀)) =
      -((res (Set.subset_union_right : B ⊆ A ∪ B)).f (p + 1) γ₀) at hd
    rw [hboundary] at hd
    have hc := congrArg (fun f ↦ f b) (tB.comm p (p + 1))
    change (relativeSingularCochains R B).d p (p + 1) β =
      tB.f (p + 1) (S.X₂.d p (p + 1) b) at hc
    have hi := congrArg (fun f ↦ f β) ((inc B).comm p (p + 1))
    change (singularCochains R X).d p (p + 1) ((inc B).f p β) =
      (inc B).f (p + 1) ((relativeSingularCochains R B).d p (p + 1) β) at hi
    rw [hc, hd, map_neg] at hi
    exact hi.trans (congrArg Neg.neg
      (congrArg (fun f ↦ f.f (p + 1) γ₀) (hres Set.subset_union_right)))
  have hδ := relativeSingularCohomologyMayerVietorisBoundary_cocycleClass R A B hA hB p
    φ b γ hb hboundary
  -- One four-set refinement controls both localized lifts and their overlap boundary.
  let 𝒰 : Set (Set X) := {U ∩ V, U ∩ B, A ∩ V, A ∩ B}
  have hopen : ∀ E ∈ 𝒰, IsOpen E := by
    intro E hE
    simp only [𝒰, Set.mem_insert_iff, Set.mem_singleton_iff] at hE
    rcases hE with rfl | rfl | rfl | rfl
    · exact hU.inter hV
    · exact hU.inter hB
    · exact hA.inter hV
    · exact hA.inter hB
  have hcov : ⋃₀ 𝒰 = Set.univ := by
    classical
    apply Set.eq_univ_of_forall
    intro x
    by_cases hxA : x ∈ A
    · by_cases hxB : x ∈ B
      · exact Set.mem_sUnion.mpr ⟨A ∩ B, by simp [𝒰], hxA, hxB⟩
      · exact Set.mem_sUnion.mpr ⟨A ∩ V, by simp [𝒰], hxA, hBV hxB⟩
    · by_cases hxB : x ∈ B
      · exact Set.mem_sUnion.mpr ⟨U ∩ B, by simp [𝒰], hAU hxA, hxB⟩
      · exact Set.mem_sUnion.mpr ⟨U ∩ V, by simp [𝒰], hAU hxA, hBV hxB⟩
  obtain ⟨c, hc, z, hz, hzclass⟩ := exists_small_relativeSingularCycle_representative R
    𝒰 (A ∩ B) hopen hcov (p + (q + 1)) z₀
  have hrefU : ∀ E ∈ 𝒰, ∃ F ∈ ({U, A} : Set (Set X)), E ⊆ F := by
    intro E hE
    simp only [𝒰, Set.mem_insert_iff, Set.mem_singleton_iff] at hE
    rcases hE with rfl | rfl | rfl | rfl
    · exact ⟨U, by simp, Set.inter_subset_left⟩
    · exact ⟨U, by simp, Set.inter_subset_left⟩
    · exact ⟨A, by simp, Set.inter_subset_left⟩
    · exact ⟨A, by simp, Set.inter_subset_left⟩
  have hrefV : ∀ E ∈ 𝒰, ∃ F ∈ ({V, B} : Set (Set X)), E ⊆ F := by
    intro E hE
    simp only [𝒰, Set.mem_insert_iff, Set.mem_singleton_iff] at hE
    rcases hE with rfl | rfl | rfl | rfl
    · exact ⟨V, by simp, Set.inter_subset_right⟩
    · exact ⟨B, by simp, Set.inter_subset_right⟩
    · exact ⟨V, by simp, Set.inter_subset_right⟩
    · exact ⟨B, by simp, Set.inter_subset_right⟩
  have hrefW : ∀ E ∈ 𝒰, ∃ F ∈ ({U ∩ V, A ∪ B} : Set (Set X)), E ⊆ F := by
    intro E hE
    simp only [𝒰, Set.mem_insert_iff, Set.mem_singleton_iff] at hE
    rcases hE with rfl | rfl | rfl | rfl
    · exact ⟨U ∩ V, by simp, Set.Subset.rfl⟩
    · exact ⟨A ∪ B, by simp, Set.inter_subset_right.trans Set.subset_union_right⟩
    · exact ⟨A ∪ B, by simp, Set.inter_subset_left.trans Set.subset_union_left⟩
    · exact ⟨A ∪ B, by simp, Set.inter_subset_left.trans Set.subset_union_left⟩
  have hcU := range_smallSingularChainsInclusion_le_of_refinement R 𝒰 {U, A} hrefU _ hc
  have hcV := range_smallSingularChainsInclusion_le_of_refinement R 𝒰 {V, B} hrefV _ hc
  have hcW₀ := range_smallSingularChainsInclusion_le_of_refinement R 𝒰 {U ∩ V, A ∪ B} hrefW _ hc
  -- Restrict that same relative cycle and transport only its equal degree index.
  let F := relativeSingularChainsMap R (ContinuousMap.id X)
    (A := A ∩ B) (B := A ∪ B) (fun _ hx ↦ Or.inl hx.1)
  let zr : relativeSingularCycles R (A ∪ B) (p + (q + 1)) := ⟨F.f _ z.val, by
    change (relativeSingularChains R (A ∪ B)).dFrom _ (F.f _ z.val) = 0
    have heq := congrArg (fun f ↦ f z.val) (F.comm_from (p + (q + 1)))
    change (relativeSingularChains R (A ∪ B)).dFrom _ (F.f _ z.val) =
      F.next _ ((relativeSingularChains R (A ∩ B)).dFrom _ z.val) at heq
    have hzclosed : (relativeSingularChains R (A ∩ B)).dFrom _ z.val = 0 := z.property
    rw [heq, hzclosed, map_zero]⟩
  let hdeg := (Nat.add_assoc p q 1).symm.trans (Nat.add_right_comm p q 1)
  let c' := ((singularChains R X).XIsoOfEq hdeg).hom c
  let z' : relativeSingularCycles R (A ∪ B) ((p + 1) + q) :=
    (eqToIso (congrArg (relativeSingularCycles R (A ∪ B)) hdeg)).hom zr
  have hval {i j : ℕ} (h : i = j) (a : relativeSingularCycles R (A ∪ B) i) :
      ((eqToIso (congrArg (relativeSingularCycles R (A ∪ B)) h)).hom a).val =
        ((relativeSingularChains R (A ∪ B)).XIsoOfEq h).hom a.val := by
    subst j
    rfl
  have hclass {i j : ℕ} (h : i = j) (a : relativeSingularCycles R (A ∪ B) i) :
      relativeSingularCycleClass R (A ∪ B) j
          ((eqToIso (congrArg (relativeSingularCycles R (A ∪ B)) h)).hom a) =
        (eqToIso (congrArg (relativeSingularHomology R (A ∪ B)) h)).hom
          (relativeSingularCycleClass R (A ∪ B) i a) := by
    subst j
    rfl
  have hπ : relativeSingularChainsProjection R (A ∩ B) ≫ F =
      relativeSingularChainsProjection R (A ∪ B) := by
    simp [F, relativeSingularChainsMap, relativeSingularChainsProjection]
  have hz' : z'.val = (relativeSingularChainsProjection R (A ∪ B)).f ((p + 1) + q) c' := by
    have hπeq {i j : ℕ} (h : i = j) (v : (singularChains R X).X i) :
        ((relativeSingularChains R (A ∪ B)).XIsoOfEq h).hom
            ((relativeSingularChainsProjection R (A ∪ B)).f i v) =
          (relativeSingularChainsProjection R (A ∪ B)).f j
            (((singularChains R X).XIsoOfEq h).hom v) := by subst j; rfl
    change ((eqToIso (congrArg (relativeSingularCycles R (A ∪ B)) hdeg)).hom zr).val = _
    rw [hval]
    change ((relativeSingularChains R (A ∪ B)).XIsoOfEq hdeg).hom (F.f _ z.val) = _
    rw [hz]
    have hπc := congrArg (fun f ↦ f.f (p + (q + 1)) c) hπ
    change F.f (p + (q + 1))
      ((relativeSingularChainsProjection R (A ∩ B)).f (p + (q + 1)) c) =
        (relativeSingularChainsProjection R (A ∪ B)).f (p + (q + 1)) c at hπc
    rw [hπc]
    exact hπeq hdeg c
  have hcW : c' ∈ ((smallSingularChainsInclusion R {U ∩ V, A ∪ B}).f ((p + 1) + q)).hom.range := by
    have htrans {i j : ℕ} (h : i = j) (v : (singularChains R X).X i)
        (hv : v ∈ ((smallSingularChainsInclusion R {U ∩ V, A ∪ B}).f i).hom.range) :
        ((singularChains R X).XIsoOfEq h).hom v ∈
          ((smallSingularChainsInclusion R {U ∩ V, A ∪ B}).f j).hom.range := by
      subst j
      exact hv
    exact htrans hdeg c hcW₀
  have hzr := homologyMap_cycleClass R _ _ F (p + (q + 1)) z zr rfl
  change relativeSingularHomologyInclusion R (A ∩ B) (A ∪ B)
      (Set.inter_subset_left.trans Set.subset_union_left) (p + (q + 1))
        (relativeSingularCycleClass R (A ∩ B) (p + (q + 1)) z) =
      relativeSingularCycleClass R (A ∪ B) (p + (q + 1)) zr at hzr
  have hw' : relativeSingularHomologyMap R
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
      (A := (Subtype.val : ↥(U ∩ V) → X) ⁻¹' (A ∪ B)) (B := A ∪ B)
      (fun _ hx ↦ hx) ((p + 1) + q) w = relativeSingularCycleClass R (A ∪ B) ((p + 1) + q) z' := by
    rw [hw]
    change _ = relativeSingularCycleClass R (A ∪ B) ((p + 1) + q)
      ((eqToIso (congrArg (relativeSingularCycles R (A ∪ B)) hdeg)).hom zr)
    rw [hclass hdeg, ← hzr, hzclass]
  have hcap := relativeSingularCapProduct_mayerVietoris_representative R U V A B hU hV hA hB
    hcover hAU hBV p q c c' rfl hcU hcV hcW z hz z' hz' φ α β γ hφ hα hβ w hw'
  rw [hφclass, hzclass] at hcap
  rw [hφclass] at hδ
  rw [hδ]
  exact hcap

end AtiyahSinger
