/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.CochainProduct
public import AtiyahSinger.Topology.RelativeCohomologySequence
public import AtiyahSinger.Topology.SingularSmallChainsHomotopy
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# Small relative cochains and singular Čech descent

Public module ID: M2123.

The augmentation for an open cover uses the original small singular chains.
Their relative quotient retains the same subspace condition and coefficients.
The comparison to the original relative cochains comes from subdivision and
the two exact sequences of actual cochains, so it works over every commutative
coefficient ring. No acyclicity assumption on the cover is part of this comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-! ## Values on the original simplex generators -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Values on simplices which vanish on the relative simplices define a unique linear
cochain on the actual relative simplicial-chain cokernel. -/
def simplicialRelativeCochainOfValues {S T : SSet.{u}} (i : S ⟶ T) (q : ℕ)
    (F : T.obj (op ⦋q⦌) → ULift.{u} R)
    (hF : ∀ σ : S.obj (op ⦋q⦌), F (i.app (op ⦋q⦌) σ) = 0) :
    (cokernel (SSet.chainComplexMap i (singularCoefficient.{u} R))).X q ⟶
      singularCoefficient.{u} R := by
  let φ : (T.chainComplex (singularCoefficient.{u} R)).X q ⟶ singularCoefficient.{u} R :=
    Sigma.desc fun σ ↦ ModuleCat.ofHom
      ((ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap.smulRight (F σ))
  have hzero : (SSet.chainComplexMap i (singularCoefficient.{u} R)).f q ≫ φ = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, SSet.ι_chainComplexMap_f]
    simp [φ, SSet.ιChainComplex, hF σ]
  let Q := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) q)
    (SSet.chainComplexMap i (singularCoefficient.{u} R))
  exact (CokernelCofork.IsColimit.desc' Q φ hzero).val

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The descended cochain has exactly its prescribed values on the original generators. -/
theorem simplicialRelativeCochainOfValues_apply_generator {S T : SSet.{u}}
    (i : S ⟶ T) (q : ℕ) (F : T.obj (op ⦋q⦌) → ULift.{u} R)
    (hF : ∀ σ : S.obj (op ⦋q⦌), F (i.app (op ⦋q⦌) σ) = 0)
    (σ : T.obj (op ⦋q⦌)) (a : ULift.{u} R) :
    simplicialRelativeCochainOfValues R i q F hF
      ((cokernel.π (SSet.chainComplexMap i (singularCoefficient.{u} R))).f q
        (T.ιChainComplex (R := singularCoefficient.{u} R) σ a)) = a.down • F σ := by
  let Q := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) q)
    (SSet.chainComplexMap i (singularCoefficient.{u} R))
  change (show (cokernel (SSet.chainComplexMap i (singularCoefficient.{u} R))).X q ⟶
    singularCoefficient.{u} R from (CokernelCofork.IsColimit.desc' Q _ _).val) _ = _
  erw [← ModuleCat.comp_apply, (CokernelCofork.IsColimit.desc' Q _ _).property]
  change (T.ιChainComplex (R := singularCoefficient.{u} R) σ ≫ _) a = _
  simp only [SSet.ιChainComplex, Sigma.ι_comp_desc]
  rfl

/-- Every cochain of a simplicial pair vanishes on its original relative generators. -/
theorem simplicialRelativeCochain_apply_relative_generator {S T : SSet.{u}}
    (i : S ⟶ T) (q : ℕ)
    (c : (cokernel (SSet.chainComplexMap i (singularCoefficient.{u} R))).X q ⟶
      singularCoefficient.{u} R) (σ : S.obj (op ⦋q⦌)) (a : ULift.{u} R) :
    c ((cokernel.π (SSet.chainComplexMap i (singularCoefficient.{u} R))).f q
      (T.ιChainComplex (R := singularCoefficient.{u} R) (i.app (op ⦋q⦌) σ) a)) = 0 := by
  have hzero := congrArg (fun f ↦ f.f q) (cokernel.condition
    (SSet.chainComplexMap i (singularCoefficient.{u} R)))
  change (SSet.chainComplexMap i (singularCoefficient.{u} R)).f q ≫
    (cokernel.π (SSet.chainComplexMap i (singularCoefficient.{u} R))).f q = 0 at hzero
  rw [← SSet.ι_chainComplexMap_f]
  exact congrArg (fun f : singularCoefficient.{u} R ⟶ singularCoefficient.{u} R ↦ f a) (by
    simpa only [Category.assoc, zero_comp, comp_zero] using
      congrArg (fun f ↦ S.ιChainComplex (R := singularCoefficient.{u} R) σ ≫ f ≫ c) hzero)

set_option backward.isDefEq.respectTransparency false in
/-- Equality of relative cochains is tested on the original simplex generators. -/
theorem simplicialRelativeCochain_ext {S T : SSet.{u}} (i : S ⟶ T) (q : ℕ)
    (c d : (cokernel (SSet.chainComplexMap i (singularCoefficient.{u} R))).X q ⟶
      singularCoefficient.{u} R)
    (h : ∀ σ : T.obj (op ⦋q⦌),
      c ((cokernel.π (SSet.chainComplexMap i (singularCoefficient.{u} R))).f q
        (T.ιChainComplex (R := singularCoefficient.{u} R) σ (ULift.up 1))) =
      d ((cokernel.π (SSet.chainComplexMap i (singularCoefficient.{u} R))).f q
        (T.ιChainComplex (R := singularCoefficient.{u} R) σ (ULift.up 1)))) : c = d := by
  apply (cancel_epi ((cokernel.π (SSet.chainComplexMap i (singularCoefficient.{u} R))).f q)).mp
  apply SSet.chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have ha : a = a.down • (ULift.up (1 : R) : ULift.{u} R) := by
    apply ULift.ext
    simp
  change c ((cokernel.π (SSet.chainComplexMap i (singularCoefficient.{u} R))).f q
      (T.ιChainComplex (R := singularCoefficient.{u} R) σ a)) =
    d ((cokernel.π (SSet.chainComplexMap i (singularCoefficient.{u} R))).f q
      (T.ιChainComplex (R := singularCoefficient.{u} R) σ a))
  rw [ha]
  simp only [map_smul, h σ]

/-- The pullback of the specified family to the actual relative subspace. -/
def smallSingularSubspaceCover (𝒰 : Set (Set X)) (A : Set X) : Set (Set A) :=
  (fun U : Set X ↦ (Subtype.val : A → X) ⁻¹' U) '' 𝒰

/-- The original subspace inclusion, restricted to the simplices small for the same cover. -/
def smallSingularSubspaceSet (𝒰 : Set (Set X)) (A : Set X) :
    (smallSingularSet (smallSingularSubspaceCover 𝒰 A)).toSSet ⟶
      (smallSingularSet 𝒰).toSSet where
  app n := ↾fun σ ↦ ⟨(TopCat.toSSet.map (TopCat.ofHom
    (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))).app n σ.val, by
      obtain ⟨V, ⟨U, hU, rfl⟩, hσ⟩ := σ.property
      refine ⟨U, hU, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact hσ ⟨t, rfl⟩⟩
  naturality _ _ _ := rfl

/-- The actual small subspace-chain inclusion. -/
def smallSingularSubspaceChains (𝒰 : Set (Set X)) (A : Set X) :
    smallSingularChains R (smallSingularSubspaceCover 𝒰 A) ⟶ smallSingularChains R 𝒰 :=
  SSet.chainComplexMap (smallSingularSubspaceSet 𝒰 A) (singularCoefficient R)

/-- Relative small chains are the cokernel of the same small subspace inclusion. -/
abbrev smallRelativeSingularChains (𝒰 : Set (Set X)) (A : Set X) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  cokernel (smallSingularSubspaceChains R 𝒰 A)

/-- The canonical comparison keeps every original small relative simplex. -/
def smallRelativeSingularChainsInclusion (𝒰 : Set (Set X)) (A : Set X) :
    smallRelativeSingularChains R 𝒰 A ⟶ relativeSingularChains R A :=
  cokernel.map (smallSingularSubspaceChains R 𝒰 A) (singularSubspaceChains R A)
    (smallSingularChainsInclusion R (smallSingularSubspaceCover 𝒰 A))
    (smallSingularChainsInclusion R 𝒰) (by
      dsimp only [smallSingularSubspaceChains, smallSingularChainsInclusion,
        singularSubspaceChains, singularChainsFunctor]
      change ((SSet.chainComplexFunctor.{u} (ModuleCat.{u} R)).obj
          (singularCoefficient.{u} R)).map _ ≫
          ((SSet.chainComplexFunctor.{u} (ModuleCat.{u} R)).obj
            (singularCoefficient.{u} R)).map _ =
        ((SSet.chainComplexFunctor.{u} (ModuleCat.{u} R)).obj
          (singularCoefficient.{u} R)).map _ ≫
          ((SSet.chainComplexFunctor.{u} (ModuleCat.{u} R)).obj
            (singularCoefficient.{u} R)).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl)

/-- The actual relative small cochains are the algebraic dual of the relative small chains. -/
abbrev smallRelativeSingularCochains (𝒰 : Set (Set X)) (A : Set X) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (singularCochainDualFunctor R).obj (op (smallRelativeSingularChains R 𝒰 A))

/-- Restriction of the original relative cochains to the same small relative simplices. -/
def smallRelativeSingularCochainsRestriction (𝒰 : Set (Set X)) (A : Set X) :
    relativeSingularCochains R A ⟶ smallRelativeSingularCochains R 𝒰 A :=
  (singularCochainDualFunctor R).map (smallRelativeSingularChainsInclusion R 𝒰 A).op

/-- The original small subspace inclusion splits in each degree on simplex generators. -/
theorem isSplitMono_smallSingularSubspaceChains
    (𝒰 : Set (Set X)) (A : Set X) (n : ℕ) :
    IsSplitMono ((smallSingularSubspaceChains R 𝒰 A).f n) := by
  classical
  let P := smallSingularSet (smallSingularSubspaceCover 𝒰 A)
  let Q := smallSingularSet 𝒰
  let f := smallSingularSubspaceSet 𝒰 A
  have hf : Function.Injective (f.app (op ⦋n⦌)) := by
    intro σ τ h
    apply Subtype.ext
    apply ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌)).injective
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    exact congrArg (fun η ↦ (TopCat.of X).toSSetObjEquiv (op ⦋n⦌) η.val t) h
  let r : (smallSingularChains R 𝒰).X n ⟶
      (smallSingularChains R (smallSingularSubspaceCover 𝒰 A)).X n :=
    Sigma.desc fun τ ↦
      if h : τ ∈ Set.range (f.app (op ⦋n⦌)) then
        P.toSSet.ιChainComplex h.choose else 0
  refine ⟨⟨r, ?_⟩⟩
  apply SSet.chainComplex_hom_ext
  intro σ
  change P.toSSet.ιChainComplex σ ≫
      (SSet.chainComplexMap f (singularCoefficient R)).f n ≫ r = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  have hmem : f.app (op ⦋n⦌) σ ∈ Set.range (f.app (op ⦋n⦌)) := ⟨σ, rfl⟩
  have hchoose : hmem.choose = σ := hf hmem.choose_spec
  simp only [SSet.ιChainComplex, r, colimit.ι_desc, Cofan.mk_pt,
    Cofan.mk_ι_app, hmem, ↓reduceDIte, hchoose]
  exact (Category.comp_id _).symm

/-- Small relative cochains, small ambient cochains and small subspace cochains form
the same exact pair sequence over arbitrary coefficients. -/
theorem shortExact_smallSingularSubspaceCochains
    (𝒰 : Set (Set X)) (A : Set X) :
    ((ShortComplex.cokernelSequence (smallSingularSubspaceChains R 𝒰 A)).op.map
      (singularCochainDualFunctor R)).ShortExact := by
  apply shortExact_singularCochainDual_of_degreewiseSplit
  intro n
  let F := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let split := (isSplitMono_smallSingularSubspaceChains R 𝒰 A n).exists_splitMono.some
  exact ShortComplex.Splitting.ofExactOfRetraction _
    ((ShortComplex.cokernelSequence_exact _).map F) split.retraction split.id
    (by change Epi ((cokernel.π (smallSingularSubspaceChains R 𝒰 A)).f n); infer_instance)

/-- The actual inclusion of small chains for an open cover is a chain homotopy equivalence. -/
theorem homotopyEquivalences_smallSingularChainsInclusion (𝒰 : Set (Set X))
    (hOpen : ∀ U ∈ 𝒰, IsOpen U) (hCover : ⋃₀ 𝒰 = Set.univ) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
      (smallSingularChainsInclusion R 𝒰) := by
  let i := smallSingularChainsInclusion R 𝒰
  let S := ShortComplex.cokernelSequence i
  have hsplit (n : ℕ) :
      (S.map (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)).Splitting := by
    let F := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n
    let split := (isSplitMono_smallSingularChainsInclusion R 𝒰 n).exists_splitMono.some
    exact ShortComplex.Splitting.ofExactOfRetraction _
      ((ShortComplex.cokernelSequence_exact i).map F) split.retraction split.id
      (by change Epi ((cokernel.π i).f n); infer_instance)
  obtain ⟨h⟩ := contractible_cokernel_smallSingularChains R 𝒰 hOpen hCover
  exact homotopyEquivalences_of_degreewiseSplit_of_contractibleCokernel S hsplit h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restricting to small relative simplices for an open cover preserves the original
relative cohomology over every commutative coefficient ring. -/
theorem isIso_homologyMap_smallRelativeSingularCochainsRestriction
    (𝒰 : Set (Set X)) (A : Set X)
    (hOpen : ∀ U ∈ 𝒰, IsOpen U) (hCover : ⋃₀ 𝒰 = Set.univ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (smallRelativeSingularCochainsRestriction R 𝒰 A) k) := by
  -- Subdivision gives absolute comparisons for both X and the same relative subspace A.
  let 𝒱 := smallSingularSubspaceCover 𝒰 A
  have hVOpen : ∀ V ∈ 𝒱, IsOpen V := by
    rintro _ ⟨U, hU, rfl⟩
    exact (hOpen U hU).preimage continuous_subtype_val
  have hVCover : ⋃₀ 𝒱 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.val ∈ ⋃₀ 𝒰 := hCover.symm ▸ Set.mem_univ _
    obtain ⟨U, hU, hxU⟩ := Set.mem_sUnion.mp hx
    exact Set.mem_sUnion.mpr ⟨_, ⟨U, hU, rfl⟩, hxU⟩
  let D := singularCochainDualFunctor R
  let S := (ShortComplex.cokernelSequence (smallSingularSubspaceChains R 𝒰 A)).op.map D
  let F := smallSingularChainsInclusion R 𝒰
  let G := smallSingularChainsInclusion R 𝒱
  let P := smallRelativeSingularChainsInclusion R 𝒰 A
  let φ : singularSubspaceCochainsSequence R A ⟶ S :=
    { τ₁ := D.map P.op
      τ₂ := D.map F.op
      τ₃ := D.map G.op
      comm₁₂ := by
        change D.map P.op ≫ D.map (cokernel.π _).op =
          D.map (relativeSingularChainsProjection R A).op ≫ D.map F.op
        rw [← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp]
        congr 1
        apply congrArg Quiver.Hom.op
        simp [P, F, smallRelativeSingularChainsInclusion,
          relativeSingularChainsProjection, cokernel.map]
      comm₂₃ := by
        change D.map F.op ≫ D.map (smallSingularSubspaceChains R 𝒰 A).op =
          D.map (singularSubspaceChains R A).op ≫ D.map G.op
        rw [← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp]
        congr 1
        apply congrArg Quiver.Hom.op
        exact (by
          change SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _ =
            SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _
          simp only [SSet.chainComplexMap, ← Functor.map_comp]
          rfl) }
  have hSB := shortExact_singularSubspaceCochains R A
  have hSA := shortExact_smallSingularSubspaceCochains R 𝒰 A
  have h₂ (j : ℕ) : IsIso (HomologicalComplex.homologyMap φ.τ₂ j) :=
    isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences R F
      (homotopyEquivalences_smallSingularChainsInclusion R 𝒰 hOpen hCover) j
  have h₃ (j : ℕ) : IsIso (HomologicalComplex.homologyMap φ.τ₃ j) :=
    isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences R G
      (homotopyEquivalences_smallSingularChainsInclusion R 𝒱 hVOpen hVCover) j
  change IsIso (HomologicalComplex.homologyMap φ.τ₁ k)
  -- Compare the actual pair sequences, retaining the zero endpoint in degree zero.
  open HomologySequence ComposableArrows CategoryTheory.Abelian in
  cases k with
  | zero =>
    apply isIso_of_isIso_of_mono (mapComposableArrows₂ φ 0)
      (composableArrows₂_exact hSB 0) (composableArrows₂_exact hSA 0)
    · have := hSB.mono_f
      apply mono_homologyMap_of_mono_of_not_rel
      simp
    · have := hSA.mono_f
      apply mono_homologyMap_of_mono_of_not_rel
      simp
    · exact h₂ 0
    · change Mono (HomologicalComplex.homologyMap φ.τ₃ 0)
      have := h₃ 0
      infer_instance
  | succ j =>
    apply isIso_of_epi_of_isIso_of_isIso_of_mono
      (composableArrows₅_exact hSB j (j + 1) rfl).δ₀
      (composableArrows₅_exact hSA j (j + 1) rfl).δ₀
      (δ₀Functor.map (mapComposableArrows₅ φ hSB hSA j (j + 1) rfl))
    · exact (h₂ j).epi_of_iso
    · exact h₃ j
    · exact h₂ (j + 1)
    · exact (h₃ (j + 1)).mono_of_iso

/-! ## Cochains on finite intersections -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Relative cochains on arbitrary subsets, with pullback along their inclusions. -/
def relativeSingularCochainsPresheaf (A : Set X) :
    (Set X)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj U := relativeSingularCochains R ((Subtype.val : U.unop → X) ⁻¹' A)
  map {U V} h :=
    (singularCochainDualFunctor R).map (relativeSingularChainsMap R
      (⟨fun x ↦ ⟨x.val, (leOfHom h.unop) x.property⟩,
        continuous_subtype_val.subtype_mk _⟩ : C(V.unop, U.unop))
      (fun _ hx ↦ hx)).op
  map_id U := by
    have h : relativeSingularChainsMap R
        (⟨fun x : U.unop ↦ ⟨x.val, x.property⟩,
          continuous_subtype_val.subtype_mk _⟩ : C(U.unop, U.unop))
        (A := (Subtype.val : U.unop → X) ⁻¹' A) (fun _ hx ↦ hx) = 𝟙 _ := by
      apply (cancel_epi (relativeSingularChainsProjection R _)).mp
      simp only [relativeSingularChainsMap, relativeSingularChainsProjection,
        cokernel.map, cokernel.π_desc, Category.comp_id]
      change (singularChainsFunctor R).map (𝟙 (TopCat.of U.unop)) ≫ _ = _
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [h]
    exact (singularCochainDualFunctor R).map_id _
  map_comp {U V W} f g := by
    rw [← Functor.map_comp, ← op_comp, ← relativeSingularChainsMap_comp]
    rfl

variable {ι : Type u}

/-- A singular simplex in a specified cover subspace is the same original small simplex. -/
def smallSingularSetOfSubspace (𝒰 : Set (Set X)) (V : Set X)
    (hV : ∃ U ∈ 𝒰, V ⊆ U) :
    (TopCat.toSSet.obj (TopCat.of V)) ⟶ (smallSingularSet 𝒰).toSSet where
  app n := ↾fun σ ↦ ⟨(TopCat.toSSet.map (TopCat.ofHom
    (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)))).app n σ, by
      obtain ⟨U, hU, hVU⟩ := hV
      refine ⟨U, hU, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact hVU (((TopCat.of V).toSSetObjEquiv n σ) t).property⟩
  naturality _ _ _ := rfl

/-- A subspace contained in a cover member maps to the actual small relative chains. -/
def smallRelativeSingularChainsSubspaceMap (𝒰 : Set (Set X)) (A V : Set X)
    (hV : ∃ U ∈ 𝒰, V ⊆ U) :
    relativeSingularChains R ((Subtype.val : V → X) ⁻¹' A) ⟶
      smallRelativeSingularChains R 𝒰 A := by
  let B := (Subtype.val : V → X) ⁻¹' A
  let g : C(B, A) := ⟨fun x ↦ ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let fS := smallSingularSetOfSubspace 𝒰 V hV
  let gS : (TopCat.toSSet.obj (TopCat.of B)) ⟶
      (smallSingularSet (smallSingularSubspaceCover 𝒰 A)).toSSet :=
    { app n := ↾fun σ ↦ ⟨(TopCat.toSSet.map (TopCat.ofHom g)).app n σ, by
        obtain ⟨U, hU, hVU⟩ := hV
        refine ⟨(Subtype.val : A → X) ⁻¹' U, ⟨U, hU, rfl⟩, ?_⟩
        rintro _ ⟨t, rfl⟩
        exact hVU (((TopCat.of B).toSSetObjEquiv n σ) t).val.property⟩
      naturality _ _ _ := rfl }
  exact cokernel.map (singularSubspaceChains R B) (smallSingularSubspaceChains R 𝒰 A)
    (SSet.chainComplexMap gS (singularCoefficient R))
    (SSet.chainComplexMap fS (singularCoefficient R)) (by
      change SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _ =
        SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _
      simp only [SSet.chainComplexMap, ← CategoryTheory.Functor.map_comp]
      rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The comparison sends each relative generator to the same original small generator. -/
theorem smallRelativeSingularChainsSubspaceMap_apply_generator
    (𝒰 : Set (Set X)) (A V : Set X) (hV : ∃ U ∈ 𝒰, V ⊆ U)
    (n : ℕ) (σ : (TopCat.toSSet.obj (TopCat.of V)).obj (op ⦋n⦌)) (a : ULift.{u} R) :
    (smallRelativeSingularChainsSubspaceMap R 𝒰 A V hV).f n
      ((relativeSingularChainsProjection R ((Subtype.val : V → X) ⁻¹' A)).f n
        ((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
          (R := singularCoefficient R) σ a)) =
      (cokernel.π (smallSingularSubspaceChains R 𝒰 A)).f n
        ((smallSingularSet 𝒰).toSSet.ιChainComplex (R := singularCoefficient R)
          ((smallSingularSetOfSubspace 𝒰 V hV).app (op ⦋n⦌) σ) a) := by
  have hp : relativeSingularChainsProjection R ((Subtype.val : V → X) ⁻¹' A) ≫
      smallRelativeSingularChainsSubspaceMap R 𝒰 A V hV =
      SSet.chainComplexMap (smallSingularSetOfSubspace 𝒰 V hV) (singularCoefficient R) ≫
        cokernel.π (smallSingularSubspaceChains R 𝒰 A) := by
    simp [relativeSingularChainsProjection, smallRelativeSingularChainsSubspaceMap,
      cokernel.map]
  have h := congrArg (fun F ↦ F.f n
    ((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
      (R := singularCoefficient R) σ a)) hp
  change _ = (((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex σ ≫
    (SSet.chainComplexMap (smallSingularSetOfSubspace 𝒰 V hV)
      (singularCoefficient R)).f n) ≫
        (cokernel.π (smallSingularSubspaceChains R 𝒰 A)).f n) a at h
  rw [SSet.ι_chainComplexMap_f] at h
  exact h

/-- The subset on which all specified cover members meet. -/
def singularCechIntersection (U : ι → Set X) {n : ℕ} (a : Fin n → ι) : Set X :=
  {x | ∀ i, x ∈ U (a i)}

/-- The singular Čech cosimplicial cochains: products of actual relative cochains on
the specified finite intersections, with the original restriction maps. -/
def singularCechCosimplicialCochains (U : ι → Set X) (A : Set X) :
    CosimplicialObject (CochainComplex (ModuleCat.{u} R) ℕ) where
  obj n := cochainFamilyProduct R (fun a : Fin (n.len + 1) → ι ↦
    (relativeSingularCochainsPresheaf R A).obj (op (singularCechIntersection U a)))
  map {n m} f := cochainFamilyProductMap R
    (fun a : Fin (m.len + 1) → ι ↦ a ∘ f.toOrderHom)
    (fun a ↦ (relativeSingularCochainsPresheaf R A).map
      (homOfLE (show singularCechIntersection U a ⊆
        singularCechIntersection U (a ∘ f.toOrderHom) from fun _ hx _i ↦ hx _)).op)
  map_id n := by
    ext q c
    funext a
    change ((relativeSingularCochainsPresheaf R A).map (𝟙 _)).f q (c a) = c a
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp {n m k} f g := by
    ext q c
    funext a
    let h₁ : singularCechIntersection U (a ∘ g.toOrderHom) ⊆
        singularCechIntersection U ((a ∘ g.toOrderHom) ∘ f.toOrderHom) :=
      fun _ hx _i ↦ hx _
    let h₂ : singularCechIntersection U a ⊆
        singularCechIntersection U (a ∘ g.toOrderHom) := fun _ hx _i ↦ hx _
    exact congrArg (fun F ↦ F.f q (c ((a ∘ g.toOrderHom) ∘ f.toOrderHom)))
      ((relativeSingularCochainsPresheaf R A).map_comp (homOfLE h₁).op (homOfLE h₂).op)

/-- Restriction of small relative cochains to each specified cover member. -/
def singularCechAugmentation (U : ι → Set X) (A : Set X) :
    smallRelativeSingularCochains R (Set.range U) A ⟶
      (singularCechCosimplicialCochains R U A).obj ⦋0⦌ where
  f q := ModuleCat.ofHom
    { toFun := fun c a ↦ (((singularCochainDualFunctor R).map
        (smallRelativeSingularChainsSubspaceMap R (Set.range U) A
          (singularCechIntersection U a) ⟨U (a 0), ⟨a 0, rfl⟩, fun _ hx ↦ hx 0⟩).op).f q) c
      map_add' := by intros; ext; exact map_add _ _ _
      map_smul' := by intros; ext; exact map_smul _ _ _ }
  comm' p q _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    exact congrArg (fun F ↦ F c) ((((singularCochainDualFunctor R).map
      (smallRelativeSingularChainsSubspaceMap R (Set.range U) A
        (singularCechIntersection U a) ⟨U (a 0), ⟨a 0, rfl⟩, fun _ hx ↦ hx 0⟩).op)).comm p q)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The comparison to small cochains followed by a Čech component is the original
relative cochain pullback along that same subspace inclusion. -/
theorem smallRelativeSingularCochainsRestriction_cechAugmentation_projection
    (U : ι → Set X) (A : Set X) (a : Fin 1 → ι) :
    smallRelativeSingularCochainsRestriction R (Set.range U) A ≫
      singularCechAugmentation R U A ≫ cochainFamilyProductProjection R
        (fun b : Fin 1 → ι ↦ (relativeSingularCochainsPresheaf R A).obj
          (op (singularCechIntersection U b))) a =
      (singularCochainDualFunctor R).map (relativeSingularChainsMap R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(singularCechIntersection U a, X))
        (A := (Subtype.val : singularCechIntersection U a → X) ⁻¹' A)
        (B := A) (fun _ hx ↦ hx)).op := by
  let V := singularCechIntersection U a
  let hv : ∃ W ∈ Set.range U, V ⊆ W := ⟨U (a 0), ⟨a 0, rfl⟩, fun _ hx ↦ hx 0⟩
  let j := smallRelativeSingularChainsSubspaceMap R (Set.range U) A V hv
  let f : C(V, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hchain : j ≫ smallRelativeSingularChainsInclusion R (Set.range U) A =
      relativeSingularChainsMap R f
        (A := (Subtype.val : V → X) ⁻¹' A) (B := A) (fun _ hx ↦ hx) := by
    apply (cancel_epi (relativeSingularChainsProjection R _)).mp
    simp only [j, smallRelativeSingularChainsSubspaceMap, smallRelativeSingularChainsInclusion,
      relativeSingularChainsMap, relativeSingularChainsProjection, cokernel.map, cokernel.π_desc]
    rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc,
      ← Category.assoc]
    congr 1
    change ((SSet.chainComplexFunctor.{u} (ModuleCat.{u} R)).obj
        (singularCoefficient.{u} R)).map _ ≫
        ((SSet.chainComplexFunctor.{u} (ModuleCat.{u} R)).obj
          (singularCoefficient.{u} R)).map _ =
      ((SSet.chainComplexFunctor.{u} (ModuleCat.{u} R)).obj
        (singularCoefficient.{u} R)).map _
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  let D := singularCochainDualFunctor R
  have hp : singularCechAugmentation R U A ≫ cochainFamilyProductProjection R
      (fun b : Fin 1 → ι ↦ (relativeSingularCochainsPresheaf R A).obj
        (op (singularCechIntersection U b))) a = D.map j.op := by
    ext q c
    rfl
  rw [hp]
  change D.map (smallRelativeSingularChainsInclusion R (Set.range U) A).op ≫
    D.map j.op = _
  rw [← D.map_comp, ← op_comp, hchain]

/-- The augmented Čech family starts with actual small relative cochains, followed by
products of actual relative cochains on nonempty tuples of cover members. -/
def singularCechCochains (U : ι → Set X) (A : Set X) (i : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  match i with
  | 0 => smallRelativeSingularCochains R (Set.range U) A
  | n + 1 => (singularCechCosimplicialCochains R U A).obj ⦋n⦌

/-- The augmentation and the usual alternating restriction differentials. -/
def singularCechDifferential (U : ι → Set X) (A : Set X) (i : ℕ) :
    singularCechCochains R U A i ⟶ singularCechCochains R U A (i + 1) :=
  match i with
  | 0 => singularCechAugmentation R U A
  | n + 1 => AlgebraicTopology.AlternatingCofaceMapComplex.objD
      (singularCechCosimplicialCochains R U A) n

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The positive Čech differential is the alternating sum of the specified restrictions. -/
theorem singularCechDifferential_succ_apply (U : ι → Set X) (A : Set X) (n q : ℕ)
    (c : (singularCechCochains R U A (n + 1)).X q) (a : Fin (n + 2) → ι) :
    (singularCechDifferential R U A (n + 1)).f q c a =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        ((relativeSingularCochainsPresheaf R A).map
          (homOfLE (show singularCechIntersection U a ⊆
            singularCechIntersection U (a ∘ (SimplexCategory.δ j).toOrderHom) from
              fun _ hx _i ↦ hx _)).op).f q
          (c (a ∘ (SimplexCategory.δ j).toOrderHom)) := by
  let ev : (singularCechCochains R U A (n + 1) ⟶
      singularCechCochains R U A (n + 2)) →+
      ((relativeSingularCochainsPresheaf R A).obj (op (singularCechIntersection U a))).X q :=
    { toFun := fun f ↦ f.f q c a
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ev (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
      (singularCechCosimplicialCochains R U A).δ j) = _
  rw [map_sum]
  simp only [map_zsmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The augmented Čech restriction differentials compose to zero. -/
theorem singularCechDifferential_comp (U : ι → Set X) (A : Set X) (i : ℕ) :
    singularCechDifferential R U A i ≫ singularCechDifferential R U A (i + 1) = 0 := by
  cases i with
  | succ n =>
    exact AlgebraicTopology.AlternatingCofaceMapComplex.d_squared
      (singularCechCosimplicialCochains R U A) n
  | zero =>
    -- Restricting to an intersection through either of its cover members keeps
    -- the same original relative simplex. The two augmented cofaces therefore agree.
    have hres (V W : Set X) (hWV : W ⊆ V)
        (hV : ∃ T ∈ Set.range U, V ⊆ T) (hW : ∃ T ∈ Set.range U, W ⊆ T) :
        relativeSingularChainsMap R
          (⟨fun x ↦ ⟨x.val, hWV x.property⟩,
            continuous_subtype_val.subtype_mk _⟩ : C(W, V))
          (A := (Subtype.val : W → X) ⁻¹' A) (B := (Subtype.val : V → X) ⁻¹' A)
          (fun _ hx ↦ hx) ≫ smallRelativeSingularChainsSubspaceMap R (Set.range U) A V hV =
          smallRelativeSingularChainsSubspaceMap R (Set.range U) A W hW := by
      apply (cancel_epi (relativeSingularChainsProjection R _)).mp
      simp only [relativeSingularChainsMap, smallRelativeSingularChainsSubspaceMap,
        relativeSingularChainsProjection, cokernel.map, cokernel.π_desc]
      rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc,
        ← Category.assoc]
      congr 1
      change ((SSet.chainComplexFunctor.{u} (ModuleCat.{u} R)).obj
          (singularCoefficient.{u} R)).map _ ≫
          ((SSet.chainComplexFunctor.{u} (ModuleCat.{u} R)).obj
            (singularCoefficient.{u} R)).map _ =
        ((SSet.chainComplexFunctor.{u} (ModuleCat.{u} R)).obj
          (singularCoefficient.{u} R)).map _
      rw [← CategoryTheory.Functor.map_comp]
      rfl
    change singularCechAugmentation R U A ≫
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (singularCechCosimplicialCochains R U A) 0 = 0
    rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
    change singularCechAugmentation R U A ≫
      (∑ j : Fin 2, (-1 : ℤ) ^ j.val • (singularCechCosimplicialCochains R U A).δ j) = 0
    rw [Fin.sum_univ_two]
    simp only [
      Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
      ← sub_eq_add_neg, Preadditive.comp_sub, sub_eq_zero]
    ext q c
    funext a
    let V₀ := singularCechIntersection U (a ∘ (SimplexCategory.δ (0 : Fin 2)).toOrderHom)
    let V₁ := singularCechIntersection U (a ∘ (SimplexCategory.δ (1 : Fin 2)).toOrderHom)
    let W := singularCechIntersection U a
    let h₀ : W ⊆ V₀ := fun _ hx _i ↦ hx _
    let h₁ : W ⊆ V₁ := fun _ hx _i ↦ hx _
    let hw : ∃ T ∈ Set.range U, W ⊆ T := ⟨U (a 0), ⟨a 0, rfl⟩, fun _ hx ↦ hx 0⟩
    let hv₀ : ∃ T ∈ Set.range U, V₀ ⊆ T :=
      ⟨U (a ((SimplexCategory.δ (0 : Fin 2)).toOrderHom 0)), ⟨_, rfl⟩, fun _ hx ↦ hx 0⟩
    let hv₁ : ∃ T ∈ Set.range U, V₁ ⊆ T :=
      ⟨U (a ((SimplexCategory.δ (1 : Fin 2)).toOrderHom 0)), ⟨_, rfl⟩, fun _ hx ↦ hx 0⟩
    let D := singularCochainDualFunctor R
    have h₀' := congrArg (fun F ↦ (D.map F.op).f q c) (hres V₀ W h₀ hv₀ hw)
    have h₁' := congrArg (fun F ↦ (D.map F.op).f q c) (hres V₁ W h₁ hv₁ hw)
    exact h₀'.trans h₁'.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restrictions to cover members determine every actual small relative cochain. -/
theorem singularCechAugmentation_injective (U : ι → Set X) (A : Set X) (q : ℕ) :
    Function.Injective ((singularCechAugmentation R U A).f q) := by
  intro c d h
  change (smallRelativeSingularChains R (Set.range U) A).X q ⟶ singularCoefficient R at c d
  apply (cancel_epi ((cokernel.π (smallSingularSubspaceChains R (Set.range U) A)).f q)).mp
  apply SSet.chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  -- Choose a cover member for this entire original simplex, then lift it to that subspace.
  obtain ⟨W, ⟨i, rfl⟩, hσ⟩ := σ.property
  let a : Fin 1 → ι := fun _ ↦ i
  let V := singularCechIntersection U a
  let hv : ∃ W ∈ Set.range U, V ⊆ W := ⟨U i, ⟨i, rfl⟩, fun _ hx ↦ hx 0⟩
  let τ := ((TopCat.of V).toSSetObjEquiv (op ⦋q⦌)).symm
    (⟨fun t ↦ ⟨((TopCat.of X).toSSetObjEquiv (op ⦋q⦌) σ.val) t,
      fun _ ↦ hσ ⟨t, rfl⟩⟩,
      (((TopCat.of X).toSSetObjEquiv (op ⦋q⦌) σ.val).continuous).subtype_mk _⟩ : C(_, V))
  have hlift : (smallSingularSetOfSubspace (Set.range U) V hv).app (op ⦋q⦌) τ = σ :=
    Subtype.ext rfl
  let j := smallRelativeSingularChainsSubspaceMap R (Set.range U) A V hv
  have hcd : j.f q ≫ c = j.f q ≫ d := congrArg (fun z ↦ z a) h
  have hval := congrArg (fun f ↦ f
    ((relativeSingularChainsProjection R ((Subtype.val : V → X) ⁻¹' A)).f q
      ((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
        (R := singularCoefficient R) τ r))) hcd
  change c (j.f q _) = d (j.f q _) at hval
  dsimp only [j] at hval
  rw [smallRelativeSingularChainsSubspaceMap_apply_generator, hlift] at hval
  exact hval

/-! ## The simplexwise contraction of each augmented row -/

private abbrev CechSurvivingSimplex (U : ι → Set X) (A : Set X) (q : ℕ) : Type u :=
  {σ : (smallSingularSet (Set.range U)).obj (op ⦋q⦌) //
    ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋q⦌) σ.val) ⊆ A}

private abbrev CechIndex (U : ι → Set X) (A : Set X) (q : ℕ)
    (σ : CechSurvivingSimplex U A q) : Type u :=
  {i : ι // Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋q⦌) σ.val.val) ⊆ U i}

private abbrev cechValues (U : ι → Set X) (A : Set X) (q n : ℕ) : Type u :=
  ∀ σ : CechSurvivingSimplex U A q, (Fin n → CechIndex U A q σ) → ULift.{u} R

private def cechSimplexLift (U : ι → Set X) (A : Set X) (q n : ℕ)
    (σ : CechSurvivingSimplex U A q) (a : Fin n → CechIndex U A q σ) :
    (TopCat.toSSet.obj (TopCat.of (singularCechIntersection U (fun j ↦ (a j).val)))).obj
      (op ⦋q⦌) :=
  ((TopCat.of (singularCechIntersection U (fun j ↦ (a j).val))).toSSetObjEquiv
    (op ⦋q⦌)).symm
      ⟨fun t ↦ ⟨((TopCat.of X).toSSetObjEquiv (op ⦋q⦌) σ.val.val) t,
        fun j ↦ (a j).property ⟨t, rfl⟩⟩,
        (((TopCat.of X).toSSetObjEquiv (op ⦋q⦌) σ.val.val).continuous).subtype_mk _⟩

set_option backward.isDefEq.respectTransparency false in
private def cechToValues (U : ι → Set X) (A : Set X) (q n : ℕ) :
    (singularCechCochains R U A n).X q → cechValues R U A q n :=
  match n with
  | 0 => fun c σ _a ↦
      (show (smallRelativeSingularChains R (Set.range U) A).X q ⟶
        singularCoefficient.{u} R from c)
      ((cokernel.π (smallSingularSubspaceChains R (Set.range U) A)).f q
      ((smallSingularSet (Set.range U)).toSSet.ιChainComplex
        (R := singularCoefficient.{u} R) σ.val (ULift.up 1)))
  | n + 1 => fun c σ a ↦
      (show (relativeSingularChains R
        ((Subtype.val : singularCechIntersection U (fun j ↦ (a j).val) → X) ⁻¹' A)).X q ⟶
          singularCoefficient.{u} R from c (fun j ↦ (a j).val))
      ((relativeSingularChainsProjection R
        ((Subtype.val : singularCechIntersection U (fun j ↦ (a j).val) → X) ⁻¹' A)).f q
          ((TopCat.toSSet.obj (TopCat.of
            (singularCechIntersection U (fun j ↦ (a j).val)))).ιChainComplex
              (R := singularCoefficient.{u} R) (cechSimplexLift U A q (n + 1) σ a) (ULift.up 1)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def cechFromValues (U : ι → Set X) (A : Set X) (q n : ℕ) :
    cechValues R U A q n → (singularCechCochains R U A n).X q :=
  match n with
  | 0 => by
    classical
    intro F
    let data (σ : (smallSingularSet (Set.range U)).obj (op ⦋q⦌)) : ULift.{u} R :=
      if h : ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋q⦌) σ.val) ⊆ A then
        F ⟨σ, h⟩ Fin.elim0 else 0
    exact simplicialRelativeCochainOfValues R (smallSingularSubspaceSet (Set.range U) A)
      q data (by
        intro τ
        have hA : Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋q⦌)
            ((smallSingularSubspaceSet (Set.range U) A).app (op ⦋q⦌) τ).val) ⊆ A := by
          rintro _ ⟨t, rfl⟩
          exact (((TopCat.of A).toSSetObjEquiv (op ⦋q⦌) τ.val) t).property
        exact dite_eq_right (not_not.mpr hA))
  | n + 1 => by
    classical
    intro F a
    let V := singularCechIntersection U a
    let hv : ∃ W ∈ Set.range U, V ⊆ W := ⟨U (a 0), ⟨a 0, rfl⟩, fun _ hx ↦ hx 0⟩
    let ambient (τ : (TopCat.toSSet.obj (TopCat.of V)).obj (op ⦋q⦌)) :
        (smallSingularSet (Set.range U)).obj (op ⦋q⦌) :=
      (smallSingularSetOfSubspace (Set.range U) V hv).app (op ⦋q⦌) τ
    let data (τ : (TopCat.toSSet.obj (TopCat.of V)).obj (op ⦋q⦌)) : ULift.{u} R :=
      if h : ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋q⦌) (ambient τ).val) ⊆ A then
        F ⟨ambient τ, h⟩ (fun j ↦ ⟨a j, by
          rintro _ ⟨t, rfl⟩
          exact (((TopCat.of V).toSSetObjEquiv (op ⦋q⦌) τ) t).property j⟩)
      else 0
    let B := (Subtype.val : V → X) ⁻¹' A
    let i := TopCat.toSSet.map (TopCat.ofHom
      (⟨Subtype.val, continuous_subtype_val⟩ : C(B, V)))
    exact simplicialRelativeCochainOfValues R i q data (by
      intro τ
      have hA : Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋q⦌)
          (ambient (i.app (op ⦋q⦌) τ)).val) ⊆ A := by
        rintro _ ⟨t, rfl⟩
        exact (((TopCat.of B).toSSetObjEquiv (op ⦋q⦌) τ) t).property
      exact dite_eq_right (not_not.mpr hA))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cechToValues_fromValues (U : ι → Set X) (A : Set X) (q n : ℕ)
    (F : cechValues R U A q n) :
    cechToValues R U A q n (cechFromValues R U A q n F) = F := by
  classical
  cases n with
  | zero =>
    funext σ a
    dsimp only [cechToValues, cechFromValues]
    erw [simplicialRelativeCochainOfValues_apply_generator]
    rw [one_smul, dite_eq_left σ.property]
    congr 1
    funext j
    exact Fin.elim0 j
  | succ n =>
    funext σ a
    dsimp only [cechToValues, cechFromValues]
    erw [simplicialRelativeCochainOfValues_apply_generator]
    have hambient : (smallSingularSetOfSubspace (Set.range U)
        (singularCechIntersection U (fun j ↦ (a j).val))
        ⟨U (a 0).val, ⟨(a 0).val, rfl⟩, fun _ hx ↦ hx 0⟩).app (op ⦋q⦌)
          (cechSimplexLift U A q (n + 1) σ a) = σ.val := Subtype.ext rfl
    simp only [hambient, dite_eq_left σ.property, one_smul]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cechToValues_injective (U : ι → Set X) (A : Set X) (q n : ℕ) :
    Function.Injective (cechToValues R U A q n) := by
  classical
  cases n with
  | zero =>
    intro c d h
    apply simplicialRelativeCochain_ext R (smallSingularSubspaceSet (Set.range U) A) q
    intro τ
    by_cases hτ : ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋q⦌) τ.val) ⊆ A
    · exact congrFun (congrFun h ⟨τ, hτ⟩) Fin.elim0
    · have hA := not_not.mp hτ
      let τA := ((TopCat.of A).toSSetObjEquiv (op ⦋q⦌)).symm
        (⟨fun t ↦ ⟨((TopCat.of X).toSSetObjEquiv (op ⦋q⦌) τ.val) t, hA ⟨t, rfl⟩⟩,
          (((TopCat.of X).toSSetObjEquiv (op ⦋q⦌) τ.val).continuous).subtype_mk _⟩ : C(_, A))
      obtain ⟨V, hV, hτV⟩ := τ.property
      let γ : (smallSingularSet (smallSingularSubspaceCover (Set.range U) A)).obj (op ⦋q⦌) :=
        ⟨τA, (by
          refine ⟨(Subtype.val : A → X) ⁻¹' V, ⟨V, hV, rfl⟩, ?_⟩
          rintro _ ⟨t, rfl⟩
          exact hτV ⟨t, rfl⟩)⟩
      have hγ : (smallSingularSubspaceSet (Set.range U) A).app (op ⦋q⦌) γ = τ :=
        Subtype.ext rfl
      have hc := simplicialRelativeCochain_apply_relative_generator R
        (smallSingularSubspaceSet (Set.range U) A) q c γ (ULift.up 1)
      have hd := simplicialRelativeCochain_apply_relative_generator R
        (smallSingularSubspaceSet (Set.range U) A) q d γ (ULift.up 1)
      rw [hγ] at hc hd
      exact hc.trans hd.symm
  | succ n =>
    intro c d h
    funext a
    let V := singularCechIntersection U a
    let B := (Subtype.val : V → X) ⁻¹' A
    let i := TopCat.toSSet.map (TopCat.ofHom
      (⟨Subtype.val, continuous_subtype_val⟩ : C(B, V)))
    apply simplicialRelativeCochain_ext R i q
    intro τ
    let hv : ∃ W ∈ Set.range U, V ⊆ W := ⟨U (a 0), ⟨a 0, rfl⟩, fun _ hx ↦ hx 0⟩
    let σ₀ := (smallSingularSetOfSubspace (Set.range U) V hv).app (op ⦋q⦌) τ
    by_cases hτ : ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋q⦌) σ₀.val) ⊆ A
    · let σ : CechSurvivingSimplex U A q := ⟨σ₀, hτ⟩
      let b : Fin (n + 1) → CechIndex U A q σ := fun j ↦ ⟨a j, by
        rintro _ ⟨t, rfl⟩
        exact (((TopCat.of V).toSSetObjEquiv (op ⦋q⦌) τ) t).property j⟩
      have hlift : cechSimplexLift U A q (n + 1) σ b = τ := rfl
      have hcd := congrFun (congrFun h σ) b
      dsimp only [cechToValues] at hcd
      rw [hlift] at hcd
      exact hcd
    · have hA : Set.range ((TopCat.of V).toSSetObjEquiv (op ⦋q⦌) τ) ⊆ B := by
        rintro _ ⟨t, rfl⟩
        exact (not_not.mp hτ) ⟨t, rfl⟩
      let γ := ((TopCat.of B).toSSetObjEquiv (op ⦋q⦌)).symm
        (⟨fun t ↦ ⟨((TopCat.of V).toSSetObjEquiv (op ⦋q⦌) τ) t, hA ⟨t, rfl⟩⟩,
          (((TopCat.of V).toSSetObjEquiv (op ⦋q⦌) τ).continuous).subtype_mk _⟩ : C(_, B))
      have hγ : i.app (op ⦋q⦌) γ = τ := rfl
      have hc := simplicialRelativeCochain_apply_relative_generator R i q
        (c a) γ (ULift.up 1)
      have hd := simplicialRelativeCochain_apply_relative_generator R i q
        (d a) γ (ULift.up 1)
      rw [hγ] at hc hd
      exact hc.trans hd.symm

private def cechValuesDifferential (U : ι → Set X) (A : Set X) (q n : ℕ)
    (F : cechValues R U A q n) : cechValues R U A q (n + 1) :=
  fun σ a ↦ ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val • F σ (a ∘ j.succAbove)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cechToValues_differential (U : ι → Set X) (A : Set X) (q n : ℕ)
    (c : (singularCechCochains R U A n).X q) :
    cechToValues R U A q (n + 1) ((singularCechDifferential R U A n).f q c) =
      cechValuesDifferential R U A q n (cechToValues R U A q n c) := by
  cases n with
  | zero =>
    funext σ a
    dsimp only [cechValuesDifferential]
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul]
    let V := singularCechIntersection U (fun j ↦ (a j).val)
    let hv : ∃ W ∈ Set.range U, V ⊆ W :=
      ⟨U (a 0).val, ⟨(a 0).val, rfl⟩, fun _ hx ↦ hx 0⟩
    let τ := cechSimplexLift U A q 1 σ a
    have hsmall : (smallSingularSetOfSubspace (Set.range U) V hv).app (op ⦋q⦌) τ =
        σ.val := Subtype.ext rfl
    have h := congrArg
      (fun z ↦ (show (smallRelativeSingularChains R (Set.range U) A).X q ⟶
        singularCoefficient.{u} R from c) z)
      (smallRelativeSingularChainsSubspaceMap_apply_generator R (Set.range U) A V hv
        q τ (ULift.up 1))
    rw [hsmall] at h
    exact h
  | succ n =>
    funext σ a
    let W := singularCechIntersection U (fun j ↦ (a j).val)
    let B := (Subtype.val : W → X) ⁻¹' A
    let τ := cechSimplexLift U A q (n + 2) σ a
    let ev : (relativeSingularCochains R B).X q →+ ULift.{u} R :=
      { toFun := fun z ↦ (show (relativeSingularChains R B).X q ⟶
          singularCoefficient.{u} R from z)
            ((relativeSingularChainsProjection R B).f q
              ((TopCat.toSSet.obj (TopCat.of W)).ιChainComplex
                (R := singularCoefficient.{u} R) τ (ULift.up 1)))
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    change ev ((singularCechDifferential R U A (n + 1)).f q c (fun j ↦ (a j).val)) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        cechToValues R U A q (n + 1) c σ (a ∘ j.succAbove)
    rw [singularCechDifferential_succ_apply, map_sum]
    simp only [map_zsmul]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    let V := singularCechIntersection U (fun k ↦ (a (j.succAbove k)).val)
    let C := (Subtype.val : V → X) ⁻¹' A
    let f : C(W, V) := ⟨fun x ↦ ⟨x.val, fun k ↦ x.property (j.succAbove k)⟩,
      continuous_subtype_val.subtype_mk _⟩
    let hf : Set.MapsTo f B C := fun _ hx ↦ hx
    have hp : relativeSingularChainsProjection R B ≫ relativeSingularChainsMap R f hf =
        (singularChainsFunctor R).map (TopCat.ofHom f) ≫
          relativeSingularChainsProjection R C := by
      simp [relativeSingularChainsProjection, relativeSingularChainsMap, cokernel.map]
    have h := congrArg (fun F ↦ F.f q
      ((TopCat.toSSet.obj (TopCat.of W)).ιChainComplex
        (R := singularCoefficient.{u} R) τ (ULift.up 1))) hp
    change _ = (((TopCat.toSSet.obj (TopCat.of W)).ιChainComplex
      (R := singularCoefficient.{u} R) τ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
          (singularCoefficient.{u} R)).f q) ≫ (relativeSingularChainsProjection R C).f q)
            (ULift.up 1) at h
    rw [SSet.ι_chainComplexMap_f] at h
    have hlift : (TopCat.toSSet.map (TopCat.ofHom f)).app (op ⦋q⦌) τ =
        cechSimplexLift U A q (n + 1) σ (a ∘ j.succAbove) := rfl
    rw [hlift] at h
    exact congrArg
      (fun z ↦ (show (relativeSingularChains R C).X q ⟶ singularCoefficient.{u} R from
        c (fun k ↦ (a (j.succAbove k)).val)) z) h

private theorem cechValues_exact (U : ι → Set X) (A : Set X) (q n : ℕ)
    (c : cechValues R U A q (n + 1))
    (hc : cechValuesDifferential R U A q (n + 1) c = 0) :
    ∃ b : cechValues R U A q n, cechValuesDifferential R U A q n b = c := by
  classical
  have hex (σ : CechSurvivingSimplex U A q) : Nonempty (CechIndex U A q σ) := by
    obtain ⟨W, ⟨i, rfl⟩, hσ⟩ := σ.val.property
    exact ⟨⟨i, hσ⟩⟩
  let k (σ : CechSurvivingSimplex U A q) : CechIndex U A q σ := Classical.choice (hex σ)
  let b : cechValues R U A q n := fun σ a ↦ c σ (Fin.cons (k σ) a)
  refine ⟨b, ?_⟩
  funext σ a
  have h := congrFun (congrFun hc σ) (Fin.cons (k σ) a)
  change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
    c σ (Fin.cons (k σ) a ∘ j.succAbove)) = 0 at h
  rw [Fin.sum_univ_succ] at h
  have h₀ : Fin.cons (k σ) a ∘ (0 : Fin (n + 2)).succAbove = a := by
    funext j
    simp
  have h₁ (j : Fin (n + 1)) : Fin.cons (k σ) a ∘ j.succ.succAbove =
      Fin.cons (k σ) (a ∘ j.succAbove) := Fin.cons_comp_succ_succAbove _ _ _
  simp only [Fin.val_zero, pow_zero, one_smul, h₀, Fin.val_succ, h₁, pow_succ,
    mul_neg_one, neg_smul] at h
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every augmented Čech row of the original relative cochains is exact.
The contraction chooses one cover member for each entire small simplex; it is
degreewise and makes no assertion that those choices commute with faces. -/
theorem singularCechDifferential_exact (U : ι → Set X) (A : Set X) (i q : ℕ) :
    Function.Exact ((singularCechDifferential R U A i).f q)
      ((singularCechDifferential R U A (i + 1)).f q) := by
  /- Identify each actual quotient cochain with its values on surviving original
  small simplices. For each such simplex its covering indices form a nonempty
  set. Prepending one chosen index contracts that elementary augmented row.
  The generator computations above transport this contraction to the actual
  Čech restrictions, without requiring a choice compatible with vertical faces. -/
  have hzero (n : ℕ) : cechToValues R U A q n 0 = 0 := by
    cases n <;> rfl
  intro c
  constructor
  · intro hc
    have hclosed : cechValuesDifferential R U A q (i + 1)
        (cechToValues R U A q (i + 1) c) = 0 := by
      rw [← cechToValues_differential, hc]
      exact hzero _
    obtain ⟨b, hb⟩ := cechValues_exact R U A q i
      (cechToValues R U A q (i + 1) c) hclosed
    refine ⟨cechFromValues R U A q i b, ?_⟩
    apply cechToValues_injective R U A q (i + 1)
    rw [cechToValues_differential, cechToValues_fromValues, hb]
  · rintro ⟨b, rfl⟩
    exact congrArg (fun f ↦ f.f q b) (singularCechDifferential_comp R U A i)

end AtiyahSinger
