/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologySequenceCup
public import AtiyahSinger.Topology.RestrictedCohomologyThomCup
public import AtiyahSinger.Topology.SimplexLocalHomology
public import AtiyahSinger.Topology.SupportedCohomologyThom

/-!
# Thom multiplication on an original relative support pair

Public module ID: M2096.

The relative statement compares the ordinary Thom map with its restriction to
the complement of the base support. The intermediate target is the actual
quotient by the sum of the two subspace chain images. Its degreewise split
sequence permits the original right-cup cochain maps to be compared before the
open-union cohomology equivalence is applied.

Source: Hatcher, Algebraic Topology, section 3.2 and Corollary 4D.9; the fixed
support formulation retains the project's original two-relative cup product.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Limits HomologicalComplex Opposite

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original relative inclusion followed by quotienting by both subspace chain images. -/
def relativeUnionSingularChainSequence (A B : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) := by
  let f := relativeSingularChainsMap R
    (ContinuousMap.subtypeVal B) (A := (Subtype.val : B → X) ⁻¹' A) (B := A)
    (fun _ hx ↦ hx)
  let Q := relativeUnionSingularChainsProjection R B A
  have hkill (S : Set X) (hS : S = A ∨ S = B) : singularSubspaceChains R S ≫ Q = 0 := by
    rcases hS with hS | hS
    · subst S
      have h := congrArg (fun g ↦
        (biprod.inr : singularChains R A ⟶ singularChains R B ⊞ singularChains R A) ≫ g)
        (cokernel.condition (singularSubspaceSumChains R B A))
      simpa only [Q, relativeUnionSingularChainsProjection, singularSubspaceSumChains,
        biprod.inr_desc_assoc, comp_zero] using h
    · subst S
      have h := congrArg (fun g ↦
        (biprod.inl : singularChains R B ⟶ singularChains R B ⊞ singularChains R A) ≫ g)
        (cokernel.condition (singularSubspaceSumChains R B A))
      simpa only [Q, relativeUnionSingularChainsProjection, singularSubspaceSumChains,
        biprod.inl_desc_assoc, comp_zero] using h
  let g := cokernel.desc (singularSubspaceChains R A) Q (hkill A (Or.inl rfl))
  have hpair : relativeSingularChainsProjection R ((Subtype.val : B → X) ⁻¹' A) ≫ f =
      singularSubspaceChains R B ≫ relativeSingularChainsProjection R A := by
    simp [f, relativeSingularChainsMap, relativeSingularChainsProjection,
      singularSubspaceChains, cokernel.map, ContinuousMap.subtypeVal]
  refine ShortComplex.mk f g ?_
  apply (cancel_epi
    (relativeSingularChainsProjection R ((Subtype.val : B → X) ⁻¹' A))).mp
  rw [← Category.assoc, hpair, Category.assoc]
  exact (congrArg (fun t ↦ singularSubspaceChains R B ≫ t)
    (cokernel.π_desc (singularSubspaceChains R A) Q (hkill A (Or.inl rfl)))).trans
      (hkill B (Or.inr rfl))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The relative inclusion has cokernel the joint quotient, in every chain degree. -/
theorem shortExact_relativeUnionSingularChainSequence (A B : Set X) :
    (relativeUnionSingularChainSequence R A B).ShortExact := by
  let S := relativeUnionSingularChainSequence R A B
  let i := ContinuousMap.subtypeVal B
  have hmono (k : ℕ) : Mono (S.f.f k) := by
    let : IsSplitMono (S.f.f k) :=
      isSplitMono_relativeSingularChainsMap_preimage R i Subtype.val_injective A k
    infer_instance
  have : Mono S.f := HomologicalComplex.mono_of_mono_f _ hmono
  have hproj : relativeSingularChainsProjection R A ≫ S.g =
      relativeUnionSingularChainsProjection R B A := by
    dsimp [S, relativeUnionSingularChainSequence, relativeSingularChainsProjection]
    exact cokernel.π_desc _ _ _
  have : Epi S.g := epi_of_epi_fac hproj
  have hpair : relativeSingularChainsProjection R ((Subtype.val : B → X) ⁻¹' A) ≫
      S.f = singularSubspaceChains R B ≫ relativeSingularChainsProjection R A := by
    simp [S, relativeUnionSingularChainSequence, relativeSingularChainsMap,
      relativeSingularChainsProjection, singularSubspaceChains, cokernel.map,
      ContinuousMap.subtypeVal]
  -- The cokernel kills both original subspace images and no additional generators.
  have hcolimit : IsColimit (CokernelCofork.ofπ S.g S.zero) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro T t ht
    have hBt : singularSubspaceChains R B ≫
        (relativeSingularChainsProjection R A ≫ t) = 0 := by
      rw [← Category.assoc, ← hpair, Category.assoc, ht, comp_zero]
    have hAt : singularSubspaceChains R A ≫
        (relativeSingularChainsProjection R A ≫ t) = 0 := by
      rw [← Category.assoc]
      exact (congrArg (fun f ↦ f ≫ t) (cokernel.condition (singularSubspaceChains R A))).trans
        zero_comp
    have hsum : singularSubspaceSumChains R B A ≫
        (relativeSingularChainsProjection R A ≫ t) = 0 := by
      apply biprod.hom_ext'
      · simpa only [singularSubspaceSumChains, biprod.inl_desc_assoc, comp_zero] using hBt
      · simpa only [singularSubspaceSumChains, biprod.inr_desc_assoc, comp_zero] using hAt
    refine ⟨cokernel.desc (singularSubspaceSumChains R B A)
      (relativeSingularChainsProjection R A ≫ t) hsum, ?_⟩
    apply (cancel_epi (relativeSingularChainsProjection R A)).mp
    rw [← Category.assoc, hproj]
    exact cokernel.π_desc _ _ _
  exact { exact := ShortComplex.exact_of_g_is_cokernel S hcolimit }

/-- The restriction from the A-relative cochains to B, with joint kernel in order B, A. -/
def relativeUnionSingularCochainSequence (A B : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  (relativeUnionSingularChainSequence R A B).op.map (singularCochainDualFunctor R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The joint relative restriction sequence is short exact over any commutative ring. -/
theorem shortExact_relativeUnionSingularCochainSequence (A B : Set X) :
    (relativeUnionSingularCochainSequence R A B).ShortExact := by
  let S := relativeUnionSingularChainSequence R A B
  apply shortExact_singularCochainDual_of_degreewiseSplit R S
  intro n
  let ev := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let T := S.map ev
  have hT : T.ShortExact :=
    (shortExact_relativeUnionSingularChainSequence R A B).map_of_exact ev
  -- The actual relative inclusion is split degreewise by retaining the B-simplices.
  let split : SplitMono (S.f.f n) :=
    (isSplitMono_relativeSingularChainsMap_preimage R (ContinuousMap.subtypeVal B)
      Subtype.val_injective A n).exists_splitMono.some
  exact ShortComplex.Splitting.ofExactOfRetraction T hT.exact
    split.retraction split.id hT.epi_g

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem shortExact_extendCochainSequence
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact) (r : ℕ) :
    (S.map ((ComplexShape.embeddingUp'Add (1 : ℕ) r).extendFunctor
      (ModuleCat.{u} R))).ShortExact := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let T := S.map (e.extendFunctor (ModuleCat.{u} R))
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let Tn := T.map (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n)
  by_cases hn : r ≤ n
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
    let Sp := S.map (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) p)
    let i : Tn ≅ Sp := ShortComplex.isoMk
      (S.X₁.extendXIso e (i := p) rfl) (S.X₂.extendXIso e (i := p) rfl)
      (S.X₃.extendXIso e (i := p) rfl) (by
        change _ ≫ S.f.f p = (extendMap S.f e).f (p + r) ≫ _
        rw [extendMap_f S.f e (i := p) (i' := p + r) rfl]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]) (by
        change _ ≫ S.g.f p = (extendMap S.g e).f (p + r) ≫ _
        rw [extendMap_f S.g e (i := p) (i' := p + r) rfl]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    exact (ShortComplex.shortExact_iff_of_iso i).mpr (hS.map_of_exact _)
  · have hz (C : CochainComplex (ModuleCat.{u} R) ℕ) : IsZero ((C.extend e).X n) :=
      C.isZero_extend_X e n (by
        intro p hp
        change p + r = n at hp
        omega)
    exact
      { mono_f := (hz S.X₁).mono _
        epi_g := (hz S.X₃).epi _
        exact := Tn.exact_of_isZero_X₂ (hz S.X₂) }


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem supportedThomUnionCup_bijective (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (r : ℕ) (c : relativeSingularCocycles R A r)
    (cB : relativeSingularCocycles R ((Subtype.val : B → X) ⁻¹' A) r)
    (hcB : cB.val = (relativeUnionSingularCochainSequence R A B).g.f r c.val)
    (hX : ∀ n, Function.Bijective (homologyMap (relativeSingularCochainCupMap R A r c) n))
    (hBcup : ∀ n, Function.Bijective (homologyMap
      (relativeSingularCochainCupMap R ((Subtype.val : B → X) ⁻¹' A) r cB) n))
    (p : ℕ) : Function.Bijective (fun a : relativeSingularCohomology R B p ↦
      relativeSingularCohomologyUnionCup R B A hB hA p r a
        (relativeSingularCocycleClass R A r c)) := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let C := relativeSingularCochains R B
  let D := relativeUnionSingularCochains R B A
  let T := relativeUnionSingularCochainSequence R A B
  let IA := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let IB := (singularSubspaceCochainsSequence R B).f
  let J := (singularCochainDualFunctor R).map (relativeUnionSingularChainsProjection R B A).op
  -- Lift the original right-cup map through the joint kernel and compare both exact rows.
  have hcomparison : ∃ F : C.extend e ⟶ D,
      F ≫ T.f = extendMap IB e ≫ relativeSingularCochainCupMap R A r c ∧
        ∀ n, IsIso (homologyMap F n) := by
    let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
      ComplexShape.embeddingUp'Add (1 : ℕ) r
    let S₀ := singularSubspaceCochainsSequence R B
    let S := S₀.map (e.extendFunctor (ModuleCat.{u} R))
    let T := relativeUnionSingularCochainSequence R A B
    have hS : S.ShortExact := shortExact_extendCochainSequence R S₀
      (shortExact_singularSubspaceCochains R B) r
    have hT : T.ShortExact := shortExact_relativeUnionSingularCochainSequence R A B
    let F₂ := relativeSingularCochainCupMap R A r c
    let F₃ := relativeSingularCochainCupMap R ((Subtype.val : B → X) ⁻¹' A) r cB
    have h₂₃ : F₂ ≫ T.g = S.g ≫ F₃ := by
      change relativeSingularCochainCupMap R A r c ≫
        (relativeUnionSingularCochainSequence R A B).g =
          extendMap (singularSubspaceCochainsSequence R B).g
            (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫
              relativeSingularCochainCupMap R ((Subtype.val : B → X) ⁻¹' A) r cB
      let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
        ComplexShape.embeddingUp'Add (1 : ℕ) r
      apply HomologicalComplex.Hom.ext
      funext n
      by_cases hn : r ≤ n
      · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
        simp only [HomologicalComplex.comp_f, relativeSingularCochainCupMap_f]
        rw [extendMap_f _ e (i := p) (i' := p + r) rfl]
        change
          (((singularCochains R X).extendXIso e (i := p) rfl).hom ≫
            ModuleCat.ofHom ((relativeSingularCochainAction R A p r).flip c.val)) ≫
              (relativeUnionSingularCochainSequence R A B).g.f (p + r) =
          ((((singularCochains R X).extendXIso e (i := p) rfl).hom ≫
            (singularSubspaceCochainsSequence R B).g.f p ≫
              ((singularCochains R B).extendXIso e (i := p) rfl).inv) ≫
            ((singularCochains R B).extendXIso e (i := p) rfl).hom ≫
              ModuleCat.ofHom
                ((relativeSingularCochainAction R ((Subtype.val : B → X) ⁻¹' A) p r).flip cB.val))
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        have h := relativeSingularCochainAction_natural R (ContinuousMap.subtypeVal B)
          ((Subtype.val : B → X) ⁻¹' A) A (fun _ hx ↦ hx) p r
          (((singularCochains R X).extendXIso e (i := p) rfl).hom a) c.val
        change (relativeUnionSingularCochainSequence R A B).g.f (p + r)
          (relativeSingularCochainAction R A p r
            (((singularCochains R X).extendXIso e (i := p) rfl).hom a) c.val) =
          relativeSingularCochainAction R ((Subtype.val : B → X) ⁻¹' A) p r
            ((singularSubspaceCochainsSequence R B).g.f p
              (((singularCochains R X).extendXIso e (i := p) rfl).hom a))
            ((relativeUnionSingularCochainSequence R A B).g.f r c.val) at h
        rw [← hcB] at h
        exact h
      · exact ((singularCochains R X).isZero_extend_X e n (by
          intro p hp
          change p + r = n at hp
          omega)).eq_of_src _ _
    have hzero : (S.f ≫ F₂) ≫ T.g = 0 := by
      rw [Category.assoc, h₂₃, ← Category.assoc, S.zero, zero_comp]
    have := hT.mono_f
    let F := hT.exact.lift (S.f ≫ F₂) hzero
    have hF : F ≫ T.f = S.f ≫ F₂ := hT.exact.lift_f _ hzero
    let φ : S ⟶ T := { τ₁ := F, τ₂ := F₂, τ₃ := F₃, comm₁₂ := hF, comm₂₃ := h₂₃ }
    refine ⟨F, hF, ?_⟩
    intro n
    have h₂ (j : ℕ) : IsIso (homologyMap φ.τ₂ j) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (hX j)
    have h₃ (j : ℕ) : IsIso (homologyMap φ.τ₃ j) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (hBcup j)
    change IsIso (homologyMap φ.τ₁ n)
    -- The whole extended pair sequence is compared, including the genuine zero endpoint.
    open HomologySequence ComposableArrows CategoryTheory.Abelian in
    cases n with
    | zero =>
      apply isIso_of_isIso_of_mono (mapComposableArrows₂ φ 0)
        (composableArrows₂_exact hS 0) (composableArrows₂_exact hT 0)
      · have := hS.mono_f
        apply mono_homologyMap_of_mono_of_not_rel
        simp
      · have := hT.mono_f
        apply mono_homologyMap_of_mono_of_not_rel
        simp
      · exact h₂ 0
      · change Mono (homologyMap φ.τ₃ 0)
        have := h₃ 0
        infer_instance
    | succ j =>
      apply isIso_of_epi_of_isIso_of_isIso_of_mono
        (composableArrows₅_exact hS j (j + 1) rfl).δ₀
        (composableArrows₅_exact hT j (j + 1) rfl).δ₀
        (δ₀Functor.map (mapComposableArrows₅ φ hS hT j (j + 1) rfl))
      · exact (h₂ j).epi_of_iso
      · exact h₃ j
      · exact h₂ (j + 1)
      · exact (h₃ (j + 1)).mono_of_iso
  obtain ⟨F, hF, hFIso⟩ := hcomparison
  have hproj : T.f ≫ IA = J := by
    change (singularCochainDualFunctor R).map (relativeUnionSingularChainSequence R A B).g.op ≫
      (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op =
        (singularCochainDualFunctor R).map (relativeUnionSingularChainsProjection R B A).op
    rw [← Functor.map_comp, ← op_comp]
    congr 1
    apply congrArg Quiver.Hom.op
    dsimp [T, relativeUnionSingularCochainSequence, relativeUnionSingularChainSequence,
      relativeSingularChainsProjection]
    exact cokernel.π_desc _ _ _
  -- Injecting the kernel lift into ordinary cochains recovers exactly the joint AW formula.
  have hcochain (α : C.X p) :
      F.f (p + r) ((C.extendXIso e (i := p) rfl).inv α) =
        relativeUnionSingularCochainCup R B A p r α c.val := by
    apply (relativeUnionSingularCochainEquiv R B A (p + r)).injective
    apply Subtype.ext
    have heq : F ≫ J = extendMap IB e ≫ relativeSingularCochainCupMap R A r c ≫ IA := by
      rw [← hproj, ← Category.assoc, hF, Category.assoc]
    have hv := congrArg (fun t ↦ t.f (p + r) ((C.extendXIso e (i := p) rfl).inv α)) heq
    change J.f (p + r) (F.f (p + r) ((C.extendXIso e (i := p) rfl).inv α)) =
      IA.f (p + r) ((relativeSingularCochainCupMap R A r c).f (p + r)
        ((extendMap IB e).f (p + r) ((C.extendXIso e (i := p) rfl).inv α))) at hv
    rw [relativeSingularCochainCupMap_f, extendMap_f IB e (i := p) (i' := p + r) rfl] at hv
    change J.f (p + r) (F.f (p + r) ((C.extendXIso e (i := p) rfl).inv α)) =
      IA.f (p + r) (relativeSingularCochainAction R A p r
        (((singularCochains R X).extendXIso e (i := p) rfl).hom
          (((singularCochains R X).extendXIso e (i := p) rfl).inv
            (IB.f p ((C.extendXIso e (i := p) rfl).hom
              ((C.extendXIso e (i := p) rfl).inv α))))) c.val) at hv
    rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at hv
    have haction : IA.f (p + r) (relativeSingularCochainAction R A p r (IB.f p α) c.val) =
        singularCochainCup R X p r (IB.f p α) (IA.f r c.val) :=
      congrArg Subtype.val ((relativeSingularCochainEquiv R A (p + r)).apply_symm_apply _)
    have hjoint : J.f (p + r) (relativeUnionSingularCochainCup R B A p r α c.val) =
        singularCochainCup R X p r (IB.f p α) (IA.f r c.val) :=
      congrArg Subtype.val ((relativeUnionSingularCochainEquiv R B A (p + r)).apply_symm_apply _)
    exact hv.trans (haction.trans hjoint.symm)
  -- The same source cocycle and the same canonical cycle quotients compute its class.
  have hclass (a : relativeSingularCohomology R B p) :
      homologyMap F (p + r) ((C.extendHomologyIso e (j := p) rfl).inv a) =
        relativeUnionCohomologyComparison R B A (p + r)
          (relativeSingularCohomologyUnionCup R B A hB hA p r a
            (relativeSingularCocycleClass R A r c)) := by
    obtain ⟨α, hα⟩ := (C.sc p).moduleCatToCycles.range.mkQ_surjective
      ((C.sc p).moduleCatHomologyIso.hom a)
    have ha : relativeSingularCocycleClass R B p α = a := by
      change (C.sc p).moduleCatHomologyIso.inv ((C.sc p).moduleCatToCycles.range.mkQ α) = a
      rw [hα]
      exact congrArg (fun t ↦ t a) (C.sc p).moduleCatHomologyIso.hom_inv_id
    let α' := (C.sc p).moduleCatCyclesIso.inv α
    let αe := (C.extendCyclesIso e (j := p) rfl).inv α'
    let β := relativeUnionSingularCocycleCup R B A p r α c
    let β' := (D.sc (p + r)).moduleCatCyclesIso.inv β
    have hαi : C.iCycles p α' = α.val :=
      congrArg (fun t ↦ t α) (C.sc p).moduleCatCyclesIso_inv_iCycles
    have hβi : D.iCycles (p + r) β' = β.val :=
      congrArg (fun t ↦ t β) (D.sc (p + r)).moduleCatCyclesIso_inv_iCycles
    have hei : (C.extend e).iCycles (p + r) αe = (C.extendXIso e (i := p) rfl).inv α.val := by
      have h := congrArg (fun t ↦ t α') (C.extendCyclesIso_inv_iCycles e (j := p) rfl)
      change (C.extend e).iCycles (p + r) αe = (C.extendXIso e (i := p) rfl).inv
        (C.iCycles p α') at h
      rw [hαi] at h
      exact h
    have hcycle : cyclesMap F (p + r) αe = β' := by
      apply (ModuleCat.mono_iff_injective (D.iCycles (p + r))).mp inferInstance
      have h := congrArg (fun t ↦ t αe) (cyclesMap_i F (p + r))
      change D.iCycles (p + r) (cyclesMap F (p + r) αe) =
        F.f (p + r) ((C.extend e).iCycles (p + r) αe) at h
      rw [h, hei, hβi]
      exact hcochain α.val
    have hαπ : C.homologyπ p α' = relativeSingularCocycleClass R B p α :=
      congrArg (fun t ↦ t α) (C.sc p).moduleCatCyclesIso_inv_π
    have hβπ : D.homologyπ (p + r) β' = (D.sc (p + r)).moduleCatHomologyIso.inv
        ((D.sc (p + r)).moduleCatToCycles.range.mkQ β) :=
      congrArg (fun t ↦ t β) (D.sc (p + r)).moduleCatCyclesIso_inv_π
    have heπ : (C.extendHomologyIso e (j := p) rfl).inv (C.homologyπ p α') =
        (C.extend e).homologyπ (p + r) αe :=
      congrArg (fun t ↦ t α') (C.homologyπ_extendHomologyIso_inv e (j := p) rfl)
    have hmap := congrArg (fun t ↦ t αe) (homologyπ_naturality F (p + r))
    change homologyMap F (p + r) ((C.extend e).homologyπ (p + r) αe) =
      D.homologyπ (p + r) (cyclesMap F (p + r) αe) at hmap
    rw [hcycle, hβπ] at hmap
    rw [← ha, relativeSingularCohomologyUnionCup_cocycleClass]
    rw [← hαπ, heπ]
    exact hmap
  let f (a : relativeSingularCohomology R B p) :=
    relativeSingularCohomologyUnionCup R B A hB hA p r a (relativeSingularCocycleClass R A r c)
  have hcomparison := relativeUnionCohomologyComparison_bijective R B A hB hA (p + r)
  apply (hcomparison.of_comp_iff' f).mp
  have hfun : relativeUnionCohomologyComparison R B A (p + r) ∘ f =
      homologyMap F (p + r) ∘ (C.extendHomologyIso e (j := p) rfl).inv :=
    funext fun a ↦ (hclass a).symm
  rw [hfun]
  have := hFIso (p + r)
  exact (ConcreteCategory.bijective_of_isIso (homologyMap F (p + r))).comp
    (ConcreteCategory.bijective_of_isIso (C.extendHomologyIso e (j := p) rfl).inv)

/-- The same right-cup equivalences on a space and an open subspace induce the relative one
through their exact-sequence comparison, as used in coordinate Thom products. -/
theorem relativeSingularCohomologyUnionCup_bijective_of_cupMap
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (r : ℕ) (c : relativeSingularCocycles R A r)
    (cB : relativeSingularCocycles R ((Subtype.val : B → X) ⁻¹' A) r)
    (hcB : cB.val = (relativeUnionSingularCochainSequence R A B).g.f r c.val)
    (hX : ∀ n, Function.Bijective (homologyMap (relativeSingularCochainCupMap R A r c) n))
    (hBcup : ∀ n, Function.Bijective (homologyMap
      (relativeSingularCochainCupMap R ((Subtype.val : B → X) ⁻¹' A) r cB) n))
    (p : ℕ) : Function.Bijective (fun a : relativeSingularCohomology R B p ↦
      relativeSingularCohomologyUnionCup R B A hB hA p r a
        (relativeSingularCocycleClass R A r c)) :=
  supportedThomUnionCup_bijective R A B hA hB r c cB hcB hX hBcup p

variable (r : ℕ) (E : X → Type u)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Projection is an equivalence on the original pair over any subset of the base. -/
theorem relativeSingularCohomologyPullback_bundleProjection_bijective
    (S : Set X) (p : ℕ) : Function.Bijective
      (relativeSingularCohomologyPullback R (bundleProjection r E)
        (A := (bundleProjection r E) ⁻¹' S) (B := S) (fun _ hx ↦ hx) p) := by
  let F := EuclideanSpace ℝ (Fin r)
  let := RealBundle.isFiniteRank_of_vectorBundle F E
  let pr := bundleProjection r E
  let s := bundleZeroSection r E
  have hpr (k : ℕ) : IsIso (singularCohomologyPullback R pr k) :=
    isIso_singularCohomologyPullback_of_homotopyInverse R pr s
      ⟨RealBundle.scalingHomotopy F E⟩ ⟨ContinuousMap.Homotopy.refl _⟩ k
  let prS : C(pr ⁻¹' S, S) :=
    ⟨fun z ↦ ⟨pr z.val, z.property⟩, (pr.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let sS : C(S, pr ⁻¹' S) :=
    ⟨fun x ↦ ⟨s x.val, x.property⟩, (s.continuous.comp continuous_subtype_val).subtype_mk _⟩
  -- Fiberwise scaling retains the original base point at every time, hence retains S.
  have hsub : (sS.comp prS).Homotopic (ContinuousMap.id (pr ⁻¹' S)) := by
    refine ⟨{ toFun := fun z ↦
                ⟨⟨z.2.val.proj, (z.1 : ℝ) • z.2.val.snd⟩, z.2.property⟩
              continuous_toFun := ?_
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · exact ((RealBundle.scalingHomotopy F E).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    · intro z
      apply Subtype.ext
      change (⟨z.val.proj, (0 : ℝ) • z.val.snd⟩ : TotalSpace F E) = ⟨z.val.proj, 0⟩
      simp only [zero_smul]
    · intro z
      apply Subtype.ext
      change (⟨z.val.proj, (1 : ℝ) • z.val.snd⟩ : TotalSpace F E) = z.val
      simp only [one_smul]
      rcases z with ⟨⟨x, v⟩, hz⟩
      rfl
  have hbase : (prS.comp sS).Homotopic (ContinuousMap.id S) :=
    ⟨ContinuousMap.Homotopy.refl _⟩
  have hprS (k : ℕ) : IsIso (singularCohomologyPullback R prS k) :=
    isIso_singularCohomologyPullback_of_homotopyInverse R prS sS hsub hbase k
  let := isIso_relativeSingularCohomologyPullback_of_absolute R pr
    (A := pr ⁻¹' S) (B := S) (fun _ hx ↦ hx) hpr hprS p
  exact ConcreteCategory.bijective_of_isIso
    (relativeSingularCohomologyPullback R pr (A := pr ⁻¹' S) (B := S) (fun _ hx ↦ hx) p)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original pullback-then-two-relative-cup Thom map is bijective on every compact support. -/
theorem supportedCohomologyThomMap_bijective [T2Space X]
    (o : CohomologyOrientation R r E) (K : TopologicalSpace.Compacts X) (p : ℕ) :
    Function.Bijective (supportedCohomologyThomMap R r E o K p) := by
  let S := (K : Set X)ᶜ
  let A := bundleNonzero r E
  let B := (bundleProjection r E) ⁻¹' S
  let t := cohomologyThomClass R r E o
  let T := relativeUnionSingularCochainSequence R A B
  -- Use an actual cocycle for the specified Thom class and restrict that same cocycle.
  obtain ⟨c, hc⟩ := (relativeSingularCoboundaries R A r).mkQ_surjective
    (((relativeSingularCochains R A).sc r).moduleCatHomologyIso.hom t)
  have hct : relativeSingularCocycleClass R A r c = t := by
    change ((relativeSingularCochains R A).sc r).moduleCatHomologyIso.inv
      ((relativeSingularCoboundaries R A r).mkQ c) = t
    rw [hc]
    exact congrArg (fun f ↦ f t)
      ((relativeSingularCochains R A).sc r).moduleCatHomologyIso.hom_inv_id
  let cB : relativeSingularCocycles R (bundleNonzeroOver r E S) r := ⟨T.g.f r c.val, by
    change T.X₃.dFrom r (T.g.f r c.val) = 0
    have h := congrArg (fun f ↦ f c.val) (T.g.comm_from r)
    change T.X₃.dFrom r (T.g.f r c.val) = T.g.next r (T.X₂.dFrom r c.val) at h
    have hclosed : T.X₂.dFrom r c.val = 0 := c.property
    rw [h, hclosed, map_zero]⟩
  have hcBclass : relativeSingularCocycleClass R (bundleNonzeroOver r E S) r cB =
      relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
        (A := bundleNonzeroOver r E S) (B := A) (fun _ hx ↦ hx) r t := by
    have h := homologyMap_cycleClass R T.X₂ T.X₃ T.g r c cB rfl
    change relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
      (A := bundleNonzeroOver r E S) (B := A) (fun _ hx ↦ hx) r
        (relativeSingularCocycleClass R A r c) =
      relativeSingularCocycleClass R (bundleNonzeroOver r E S) r cB at h
    rw [hct] at h
    exact h.symm
  have ht (x : X) : relativeSingularCohomologyPullback R (bundleFiberInclusion r E x)
      (A := {v : E x | v ≠ 0}) (B := A) (fun _ hv ↦ hv) r t = o.fiberClass x :=
    (existsUnique_cohomologyThomClass R r E o).exists.choose_spec x
  have hgen (x : X) : Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R (bundleFiberInclusion r E x)
        (A := {v : E x | v ≠ 0}) (B := A) (fun _ hv ↦ hv) r
          (relativeSingularCocycleClass R A r c)) := by
    rw [hct, ht]
    exact o.is_generator x
  have hgenB (x : X) (hx : x ∈ S) : Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R (bundleFiberInclusionOver r E S x hx)
        (A := {v : E x | v ≠ 0}) (B := bundleNonzeroOver r E S) (fun _ hv ↦ hv) r
          (relativeSingularCocycleClass R (bundleNonzeroOver r E S) r cB)) := by
    rw [hcBclass, ← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    change Function.Bijective (fun a : R ↦ a • relativeSingularCohomologyPullback R
      (bundleFiberInclusion r E x) (A := {v : E x | v ≠ 0}) (B := A) (fun _ hv ↦ hv) r t)
    rw [ht]
    exact o.is_generator x
  -- The two complete cochain comparisons yield the actual joint-relative cup bijection.
  have hGlobal := relativeSingularCochainCupMap_bijective_of_bundle_generator R r E c hgen
  have hRestricted := relativeSingularCochainCupMap_bijective_of_bundleTotalOver_generator
    R r E S cB hgenB
  have hOpen := isOpen_supportedCohomologyThomSubspaces r E K
  have hcup := supportedThomUnionCup_bijective R A B hOpen.2 hOpen.1 r c cB rfl
    hGlobal hRestricted p
  rw [hct] at hcup
  -- Finally retain the original relative projection and the proved support-complement equality.
  have hpull := relativeSingularCohomologyPullback_bundleProjection_bijective R r E S p
  let i := eqToIso (congrArg (fun C ↦ relativeSingularCohomology R C (p + r))
    (supportedCohomologyThomSupport_compl r E K))
  have hi := ConcreteCategory.bijective_of_isIso i.hom
  exact hi.comp (hcup.comp hpull)

end AtiyahSinger
