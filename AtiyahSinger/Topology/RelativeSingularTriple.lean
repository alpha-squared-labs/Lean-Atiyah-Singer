/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularFunctoriality
public import AtiyahSinger.Topology.RelativeSingularMayerVietoris
public import AtiyahSinger.Topology.SingularHomologyAugmentation
public import AtiyahSinger.Topology.SingularHomologyContraction
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The original relative singular chain sequence of a triple

Public module ID: M2095.

For nested subspaces `A ⊆ B ⊆ X`, the original quotients form the short exact
sequence `C(B,A) → C(X,A) → C(X,B)`. Its connecting map is used in the
Euclidean local-homology suspension without replacing the given simplex or
introducing a separate reduced-homology model.

Source: Hatcher, Algebraic Topology, section 2.1, the long exact sequence of a triple.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- An explicit homotopy inverse makes the original singular-homology map invertible. -/
theorem isIso_singularHomologyMap_of_homotopyInverse
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (g : C(Y, X))
    (hX : (g.comp f).Homotopic (ContinuousMap.id X))
    (hY : (f.comp g).Homotopic (ContinuousMap.id Y)) (k : ℕ) :
    IsIso (singularHomologyMap R f k) := by
  have hcomp {Z W : Type u} [TopologicalSpace Z] [TopologicalSpace W]
      (a : C(Z, W)) (b : C(W, Z))
      (h : (b.comp a).Homotopic (ContinuousMap.id Z)) :
      singularHomologyMap R a k ≫ singularHomologyMap R b k = 𝟙 _ := by
    change homologyMap ((singularChainsFunctor R).map (TopCat.ofHom a)) k ≫
      homologyMap ((singularChainsFunctor R).map (TopCat.ofHom b)) k = _
    rw [← homologyMap_comp, ← Functor.map_comp]
    exact (singularHomologyMap_eq_of_homotopic R h k).trans
      (by simp [singularHomologyMap])
  exact ⟨singularHomologyMap R g k, hcomp f g hX, hcomp g f hY⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Inverse maps of pairs induce inverse maps on the original relative homology. -/
theorem isIso_relativeSingularHomologyMap_of_inverse
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (g : C(Y, X))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B A)
    (hX : g.comp f = ContinuousMap.id X) (hY : f.comp g = ContinuousMap.id Y)
    (k : ℕ) : IsIso (relativeSingularHomologyMap R f hf k) := by
  have hcomp {Z W : Type u} [TopologicalSpace Z] [TopologicalSpace W]
      (a : C(Z, W)) (b : C(W, Z)) {S : Set Z} {T : Set W}
      (ha : Set.MapsTo a S T) (hb : Set.MapsTo b T S)
      (h : b.comp a = ContinuousMap.id Z) :
      relativeSingularHomologyMap R a ha k ≫ relativeSingularHomologyMap R b hb k =
        𝟙 _ := by
    change homologyMap (relativeSingularChainsMap R a ha) k ≫
      homologyMap (relativeSingularChainsMap R b hb) k = _
    rw [← homologyMap_comp, ← relativeSingularChainsMap_comp]
    generalize_proofs at *
    generalize hfun : b.comp a = c at *
    clear hfun
    subst c
    simp [relativeSingularChainsMap, cokernel.map]
  exact ⟨relativeSingularHomologyMap R g hg k, hcomp f g hf hg hX, hcomp g f hg hf hY⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- With an empty subspace, the original relative chain projection is an isomorphism. -/
theorem isIso_relativeSingularChainsProjection_of_isEmpty (A : Set X) [IsEmpty A] :
    IsIso (relativeSingularChainsProjection R A) := by
  have hz : singularSubspaceChains R A = 0 := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply SSet.chainComplex_hom_ext
    intro σ
    exact isEmptyElim (((TopCat.of A).toSSetObjEquiv _ σ)
      (Convexity.StdSimplex.single 0))
  change IsIso (cokernel.π (singularSubspaceChains R A))
  rw [hz]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Relative degree-zero homology vanishes in a path-connected space with nonempty subspace. -/
theorem subsingleton_relativeSingularHomology_zero
    [PathConnectedSpace X] (A : Set X) (hA : A.Nonempty) :
    Subsingleton (relativeSingularHomology R A 0) := by
  obtain ⟨a, ha⟩ := hA
  let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let s : C(PUnit.{u + 1}, A) := ContinuousMap.const _ ⟨a, ha⟩
  have : IsIso (singularHomologyMap R (i.comp s) 0) :=
    IsIso.of_isIso_fac_right (singularHomologyMap_augmentation R (i.comp s))
  have hcomp : singularHomologyMap R s 0 ≫ singularHomologyMap R i 0 =
      singularHomologyMap R (i.comp s) 0 := by
    change homologyMap ((singularChainsFunctor R).map (TopCat.ofHom s)) 0 ≫
      homologyMap ((singularChainsFunctor R).map (TopCat.ofHom i)) 0 = _
    rw [← homologyMap_comp, ← Functor.map_comp]
    rfl
  have : Epi (singularHomologyMap R i 0) := epi_of_epi_fac hcomp
  let q := homologyMap (relativeSingularChainsProjection R A) 0
  have : Epi (relativeSingularChainsProjection R A) := by
    dsimp [relativeSingularChainsProjection]
    infer_instance
  have : Epi q := epi_homologyMap_of_epi_of_not_rel _ 0 (by simp)
  have hzero : q = 0 := by
    apply (cancel_epi (singularHomologyMap R i 0)).mp
    change homologyMap (singularSubspaceChains R A) 0 ≫
      homologyMap (relativeSingularChainsProjection R A) 0 = _
    rw [← homologyMap_comp]
    simp [relativeSingularChainsProjection]
  exact ModuleCat.isZero_iff_subsingleton.mp (IsZero.of_epi_eq_zero q hzero)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual quotient-chain sequence of the nested subspaces `A ⊆ B`. -/
def relativeSingularTripleSequence (A B : Set X) (hAB : A ⊆ B) :
    ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) where
  X₁ := relativeSingularChains R ((Subtype.val : B → X) ⁻¹' A)
  X₂ := relativeSingularChains R A
  X₃ := relativeSingularChains R B
  f := relativeSingularChainsMap R
    (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X)) (fun _ hx ↦ hx)
  g := relativeSingularChainsMap R (ContinuousMap.id X) (fun _ hx ↦ hAB hx)
  zero := by
    apply (cancel_epi
      (relativeSingularChainsProjection R ((Subtype.val : B → X) ⁻¹' A))).mp
    simp [relativeSingularChainsMap, relativeSingularChainsProjection,
      singularSubspaceChains, cokernel.map, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The nested original chain quotients form a short exact sequence in every degree. -/
theorem shortExact_relativeSingularTripleSequence (A B : Set X) (hAB : A ⊆ B) :
    (relativeSingularTripleSequence R A B hAB).ShortExact := by
  let S := relativeSingularTripleSequence R A B hAB
  let i : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hmono (k : ℕ) : Mono (S.f.f k) := by
    let : IsSplitMono (S.f.f k) :=
      isSplitMono_relativeSingularChainsMap_preimage R i Subtype.val_injective A k
    infer_instance
  have : Mono S.f := HomologicalComplex.mono_of_mono_f _ hmono
  have hproj : relativeSingularChainsProjection R A ≫ S.g =
      relativeSingularChainsProjection R B := by
    simp [S, relativeSingularTripleSequence, relativeSingularChainsMap,
      relativeSingularChainsProjection]
  have : Epi (relativeSingularChainsProjection R B) := by
    dsimp [relativeSingularChainsProjection]
    infer_instance
  have : Epi S.g := epi_of_epi_fac hproj
  have hpair : relativeSingularChainsProjection R ((Subtype.val : B → X) ⁻¹' A) ≫
      S.f = singularSubspaceChains R B ≫ relativeSingularChainsProjection R A := by
    simp [S, relativeSingularTripleSequence, relativeSingularChainsMap,
      relativeSingularChainsProjection, singularSubspaceChains, cokernel.map]
  -- The iterated quotient kills precisely the original B-chains.
  have hcolimit : IsColimit (CokernelCofork.ofπ S.g S.zero) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro T t ht
    have hBt : singularSubspaceChains R B ≫
        (relativeSingularChainsProjection R A ≫ t) = 0 := by
      rw [← Category.assoc, ← hpair, Category.assoc, ht, comp_zero]
    refine ⟨cokernel.desc (singularSubspaceChains R B)
      (relativeSingularChainsProjection R A ≫ t) hBt, ?_⟩
    apply (cancel_epi (relativeSingularChainsProjection R A)).mp
    rw [← Category.assoc, hproj]
    exact cokernel.π_desc _ _ _
  exact { exact := ShortComplex.exact_of_g_is_cokernel S hcolimit }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A map inducing homology isomorphisms on the ambient spaces and subspaces does so on pairs. -/
theorem isIso_relativeSingularHomologyMap_of_absolute
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B)
    (hX : ∀ k : ℕ, IsIso (singularHomologyMap R f k))
    (hA : ∀ k : ℕ, IsIso (singularHomologyMap R
      (⟨fun x ↦ ⟨f x, hf x.property⟩,
        (f.continuous.comp continuous_subtype_val).subtype_mk _⟩ : C(A, B)) k))
    (k : ℕ) : IsIso (relativeSingularHomologyMap R f hf k) := by
  let SA := ShortComplex.mk (singularSubspaceChains R A)
    (relativeSingularChainsProjection R A) (cokernel.condition _)
  let SB := ShortComplex.mk (singularSubspaceChains R B)
    (relativeSingularChainsProjection R B) (cokernel.condition _)
  let fA : C(A, B) := ⟨fun x ↦ ⟨f x, hf x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let φ : SA ⟶ SB :=
    { τ₁ := (singularChainsFunctor R).map (TopCat.ofHom fA)
      τ₂ := (singularChainsFunctor R).map (TopCat.ofHom f)
      τ₃ := relativeSingularChainsMap R f hf
      comm₁₂ := by
        dsimp [SA, SB]
        simp only [singularSubspaceChains, ← Functor.map_comp]
        rfl
      comm₂₃ := by
        simp [SA, SB, relativeSingularChainsMap, relativeSingularChainsProjection] }
  -- The five-lemma comparison retains the two original pair projections.
  exact HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ
    (shortExact_singularSubspaceChains R A) (shortExact_singularSubspaceChains R B) k
    (hA k).epi_of_iso (hX k) (fun j _ ↦ hA j) (fun j _ ↦ (hX j).mono_of_iso)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A nonempty contractible subspace of a contractible space has zero relative homology. -/
theorem subsingleton_relativeSingularHomology_of_contractible
    (A : Set X) [ContractibleSpace X] [ContractibleSpace A] (k : ℕ) :
    Subsingleton (relativeSingularHomology R A k) := by
  let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hmap (j : ℕ) : IsIso (singularHomologyMap R i j) := by
    cases j with
    | zero =>
      -- Both degree-zero augmentations identify the same connected point class.
      have h := singularHomologyMap_augmentation R i
      exact IsIso.of_isIso_fac_right h
    | succ j =>
      let := subsingleton_singularHomology_of_contractible R A (j + 1) (by omega)
      let := subsingleton_singularHomology_of_contractible R X (j + 1) (by omega)
      exact (ConcreteCategory.isIso_iff_bijective _).mpr
        ⟨Function.injective_of_subsingleton _, fun z ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  have hquasi : QuasiIso (singularSubspaceChains R A) := by
    rw [quasiIso_iff]
    intro j
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact hmap j
  have hacyclic := (shortExact_singularSubspaceChains R A).acyclic_X₃ hquasi
  exact ModuleCat.isZero_iff_subsingleton.mp
    ((HomologicalComplex.exactAt_iff_isZero_homology _ k).mp (hacyclic k))

end AtiyahSinger
