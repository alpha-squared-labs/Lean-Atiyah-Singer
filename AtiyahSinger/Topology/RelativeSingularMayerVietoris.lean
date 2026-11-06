/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularOpenExcision
public import AtiyahSinger.Topology.RelativeUnionCochains
public import AtiyahSinger.Topology.SingularHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exact sequences for the original relative singular homology

Public module ID: M2092.

The short exact sequence of an actual subspace inclusion and its original
cokernel gives the long exact sequence of a pair. Open excision then gives
the Mayer–Vietoris vanishing criterion, retaining the given singular complexes
and coefficient module. These are the usual arguments of Hatcher, Section 2.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite Topology
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- The actual subspace inclusion and relative quotient form a short exact sequence. -/
theorem shortExact_singularSubspaceChains (A : Set X) :
    (ShortComplex.mk (singularSubspaceChains R A)
      (relativeSingularChainsProjection R A) (cokernel.condition _)).ShortExact := by
  -- A subspace inclusion injects the original simplex generators in every degree.
  have hmono (n : ℕ) : Mono ((singularSubspaceChains R A).f n) := by
    let : IsSplitMono ((singularSubspaceChains R A).f n) :=
      isSplitMono_singularChainsMap_of_injective R
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) Subtype.val_injective n
    exact inferInstance
  have : Mono (singularSubspaceChains R A) :=
    HomologicalComplex.mono_of_mono_f _ hmono
  -- The quotient is the specified categorical cokernel, not a replacement complex.
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }

/-- The long exact sequence of the original pair gives relative vanishing. -/
theorem relativeSingularHomology_subsingleton_of_absolute
    (A : Set X) (j : ℕ) [Subsingleton (singularHomology R X (j + 1))]
    [Subsingleton (singularHomology R A j)] :
    Subsingleton (relativeSingularHomology R A (j + 1)) := by
  -- The relative group lies between the indicated two zero absolute groups.
  have h := (shortExact_singularSubspaceChains R A).homology_exact₃ (j + 1) j rfl
  apply ModuleCat.isZero_iff_subsingleton.mp
  exact h.isZero_X₂
    ((ModuleCat.isZero_iff_subsingleton.mpr inferInstance).eq_of_src _ _)
    ((ModuleCat.isZero_iff_subsingleton.mpr inferInstance).eq_of_tgt _ _)

/-- Vanishing of the subspace and relative groups forces absolute vanishing. -/
theorem singularHomology_subsingleton_of_relative
    (A : Set X) (k : ℕ) [Subsingleton (singularHomology R A k)]
    [Subsingleton (relativeSingularHomology R A k)] :
    Subsingleton (singularHomology R X k) := by
  -- Exactness at the ambient group uses the actual inclusion and quotient maps.
  have h := (shortExact_singularSubspaceChains R A).homology_exact₂ k
  apply ModuleCat.isZero_iff_subsingleton.mp
  exact h.isZero_X₂
    ((ModuleCat.isZero_iff_subsingleton.mpr inferInstance).eq_of_src _ _)
    ((ModuleCat.isZero_iff_subsingleton.mpr inferInstance).eq_of_tgt _ _)

/-- The open-cover Mayer–Vietoris vanishing criterion for ordinary singular homology. -/
theorem singularHomology_subsingleton_of_openCover
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (j : ℕ) [Subsingleton (singularHomology R U (j + 1))]
    [Subsingleton (singularHomology R V (j + 1))]
    [Subsingleton (singularHomology R (U ∩ V : Set X) j)] :
    Subsingleton (singularHomology R X (j + 1)) := by
  let f : C(V, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let A : Set V := f ⁻¹' U
  -- The subspace inside V is canonically the original intersection U ∩ V.
  let e : TopCat.of A ≅ TopCat.of (U ∩ V : Set X) :=
    { hom := TopCat.ofHom
        ⟨fun x ↦ ⟨x.val.val, x.property, x.val.property⟩,
          (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
      inv := TopCat.ofHom
        ⟨fun x ↦ ⟨⟨x.val, x.property.2⟩, x.property.1⟩,
          (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext x; rfl }
  let eH : singularHomology R A j ≅ singularHomology R (U ∩ V : Set X) j :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R)
      (ComplexShape.down ℕ) j).mapIso ((singularChainsFunctor R).mapIso e)
  have : Subsingleton (singularHomology R A j) :=
    ((ConcreteCategory.isIso_iff_bijective eH.hom).mp inferInstance).injective.subsingleton
  have : Subsingleton (relativeSingularHomology R A (j + 1)) :=
    relativeSingularHomology_subsingleton_of_absolute R A j
  -- Open excision identifies (V,V ∩ U) with (X,U), including their actual forward map.
  have hRange : Uᶜ ⊆ Set.range f := by
    intro x hx
    have hUV : x ∈ U ∪ V := hcover.symm ▸ Set.mem_univ x
    exact ⟨⟨x, hUV.resolve_left hx⟩, rfl⟩
  have hexc {A' : Set V} {B' : Set X}
      (hA : A' = (f ⁻¹' Uᶜ)ᶜ) (hB : B' = Uᶜᶜ) (hf : Set.MapsTo f A' B') :
      HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
        (relativeSingularChainsMap R f hf) := by
    subst A' B'
    exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding R f
      hV.isOpenEmbedding_subtypeVal Uᶜ hU.isClosed_compl hRange
  obtain ⟨equiv, _⟩ := hexc (A' := A) (B' := U)
    (by simp [A]) (compl_compl U).symm (fun _ hx ↦ hx)
  have : Subsingleton (relativeSingularHomology R U (j + 1)) :=
    ((ConcreteCategory.isIso_iff_bijective (equiv.toHomologyIso (j + 1)).inv).mp
      inferInstance).injective.subsingleton
  exact singularHomology_subsingleton_of_relative R U (j + 1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Chains supported in both subspaces are exactly the chains supported in their intersection. -/
theorem range_singularSubspaceChains_inter (A B : Set X) (n : ℕ) :
    ((singularSubspaceChains R (A ∩ B)).f n).hom.range =
      ((singularSubspaceChains R A).f n).hom.range ⊓
        ((singularSubspaceChains R B).f n).hom.range := by
  classical
  let S := TopCat.toSSet.obj (TopCat.of X)
  let inc (U : Set X) := TopCat.toSSet.map
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
  let incl (U V : Set X) (h : U ⊆ V) :=
    (singularChainsFunctor R).map
      (TopCat.ofHom (⟨fun x ↦ ⟨x.val, h x.property⟩,
        continuous_subtype_val.subtype_mk _⟩ : C(U, V)))
  have hinc (U V : Set X) (h : U ⊆ V) :
      incl U V h ≫ singularSubspaceChains R V = singularSubspaceChains R U := by
    simp only [incl, singularSubspaceChains, ← Functor.map_comp]
    rfl
  apply le_antisymm
  · -- Every intersection simplex is a simplex of each of the two original subspaces.
    rintro z ⟨c, rfl⟩
    exact ⟨⟨(incl (A ∩ B) A Set.inter_subset_left).f n c,
      congrArg (fun f ↦ f.f n c) (hinc _ _ Set.inter_subset_left)⟩,
      ⟨(incl (A ∩ B) B Set.inter_subset_right).f n c,
        congrArg (fun f ↦ f.f n c) (hinc _ _ Set.inter_subset_right)⟩⟩
  · -- Retain precisely the ambient generators contained in A. This fixes every A-chain.
    let p : (singularChains R X).X n ⟶ (singularChains R X).X n :=
      Sigma.desc fun σ : S.obj (op ⦋n⦌) ↦
        if Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) ⊆ A then
          S.ιChainComplex σ else 0
    have hp : (singularSubspaceChains R A).f n ≫ p =
        (singularSubspaceChains R A).f n := by
      apply SSet.chainComplex_hom_ext
      intro σ
      have hσ : Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌)
          ((inc A).app (op ⦋n⦌) σ)) ⊆ A := by
        rintro _ ⟨t, rfl⟩
        exact ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌) σ t).property
      change _ ≫ (SSet.chainComplexMap (inc A) (singularCoefficient R)).f n ≫ p =
        _ ≫ (SSet.chainComplexMap (inc A) (singularCoefficient R)).f n
      rw [← Category.assoc, SSet.ι_chainComplexMap_f]
      simp [p, SSet.ιChainComplex, hσ]
      rfl
    -- Applied to B-chains, the same selector factors through actual intersection simplices.
    let lift (σ : (TopCat.toSSet.obj (TopCat.of B)).obj (op ⦋n⦌))
        (hσ : Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌)
          ((inc B).app (op ⦋n⦌) σ)) ⊆ A) :
        (TopCat.toSSet.obj (TopCat.of ↥(A ∩ B))).obj (op ⦋n⦌) :=
      ((TopCat.of ↥(A ∩ B)).toSSetObjEquiv (op ⦋n⦌)).symm
        ⟨fun t ↦ ⟨((TopCat.of B).toSSetObjEquiv (op ⦋n⦌) σ t).val,
          hσ ⟨t, rfl⟩, ((TopCat.of B).toSSetObjEquiv (op ⦋n⦌) σ t).property⟩,
          (continuous_subtype_val.comp
            ((TopCat.of B).toSSetObjEquiv (op ⦋n⦌) σ).continuous).subtype_mk _⟩
    let g : (singularChains R B).X n ⟶ (singularChains R ↥(A ∩ B)).X n :=
      Sigma.desc fun σ ↦
        if hσ : Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌)
            ((inc B).app (op ⦋n⦌) σ)) ⊆ A then
          (TopCat.toSSet.obj (TopCat.of ↥(A ∩ B))).ιChainComplex (lift σ hσ) else 0
    have hg : (singularSubspaceChains R B).f n ≫ p =
        g ≫ (singularSubspaceChains R (A ∩ B)).f n := by
      apply SSet.chainComplex_hom_ext
      intro σ
      change _ ≫ (SSet.chainComplexMap (inc B) (singularCoefficient R)).f n ≫ p = _
      rw [← Category.assoc, SSet.ι_chainComplexMap_f]
      dsimp only [g]
      rw [← Category.assoc]
      simp only [p, SSet.ιChainComplex, Sigma.ι_comp_desc]
      split_ifs with hσ
      · change _ = _ ≫ (SSet.chainComplexMap (inc (A ∩ B)) (singularCoefficient R)).f n
        erw [SSet.ι_chainComplexMap_f]
        rfl
      · simp
    rintro z ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨g b, ?_⟩
    have hfix : p z = z := by
      rw [← ha]
      exact congrArg (fun f ↦ f a) hp
    rw [← hfix, ← hb]
    exact congrArg (fun f ↦ f b) hg.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The diagonal and difference sequence of the original relative chain quotients.
Its last object is the quotient by the sum of subspace chains, before open excision. -/
def relativeSingularMayerVietorisShortComplex (A B : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) := by
  let q := relativeUnionSingularChainsProjection R A B
  have hA : singularSubspaceChains R A ≫ q = 0 := by
    have h := congrArg
      (fun f ↦ (biprod.inl : singularChains R A ⟶
        singularChains R A ⊞ singularChains R B) ≫ f)
      (cokernel.condition (singularSubspaceSumChains R A B))
    simpa only [singularSubspaceSumChains, biprod.inl_desc_assoc, comp_zero] using! h
  have hB : singularSubspaceChains R B ≫ q = 0 := by
    have h := congrArg
      (fun f ↦ (biprod.inr : singularChains R B ⟶
        singularChains R A ⊞ singularChains R B) ≫ f)
      (cokernel.condition (singularSubspaceSumChains R A B))
    simpa only [singularSubspaceSumChains, biprod.inr_desc_assoc, comp_zero] using! h
  let a := (relativeSingularChainsFunctor R X).map (homOfLE (Set.inter_subset_left (s := A)
    (t := B)))
  let b := (relativeSingularChainsFunctor R X).map (homOfLE (Set.inter_subset_right (s := A)
    (t := B)))
  let c := cokernel.desc (singularSubspaceChains R A) q hA
  let d := cokernel.desc (singularSubspaceChains R B) q hB
  refine ShortComplex.mk (biprod.lift a b) (biprod.desc c (-d)) ?_
  rw [biprod.lift_desc, Preadditive.comp_neg, add_neg_eq_zero]
  apply (cancel_epi (relativeSingularChainsProjection R (A ∩ B))).mp
  simp [a, b, c, d, relativeSingularChainsFunctor, relativeSingularChainsMap,
    relativeSingularChainsProjection, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The relative Mayer–Vietoris diagonal and difference sequence is degreewise short exact. -/
theorem shortExact_relativeSingularMayerVietorisShortComplex (A B : Set X) :
    (relativeSingularMayerVietorisShortComplex R A B).ShortExact := by
  let S := relativeSingularMayerVietorisShortComplex R A B
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let D := S.map (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
  let q (U : Set X) := (relativeSingularChainsProjection R U).f n
  let qsum := (relativeUnionSingularChainsProjection R A B).f n
  let i (U : Set X) := (singularSubspaceChains R U).f n
  let fst := (biprod.fst : relativeSingularChains R A ⊞ relativeSingularChains R B ⟶
    relativeSingularChains R A).f n
  let snd := (biprod.snd : relativeSingularChains R A ⊞ relativeSingularChains R B ⟶
    relativeSingularChains R B).f n
  let inl := (biprod.inl : relativeSingularChains R A ⟶
    relativeSingularChains R A ⊞ relativeSingularChains R B).f n
  let inr := (biprod.inr : relativeSingularChains R B ⟶
    relativeSingularChains R A ⊞ relativeSingularChains R B).f n
  have hsplit (z : D.X₂) : inl (fst z) + inr (snd z) = z := by
    exact congrArg (fun f ↦ f.f n z)
      (biprod.total (X := relativeSingularChains R A) (Y := relativeSingularChains R B))
  have hext {z w : D.X₂} (hf : fst z = fst w) (hs : snd z = snd w) : z = w := by
    rw [← hsplit z, hf, hs, hsplit w]
  -- The actual relative projections are surjective, with precisely the subspace chain kernels.
  have hsurj (U : Set X) : Function.Surjective (q U) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hker (U : Set X) (x : (singularChains R X).X n) :
      q U x = 0 ↔ x ∈ (i U).hom.range := by
    have h := (shortExact_singularSubspaceChains R U).exact.map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
    exact (SetLike.ext_iff.mp h.moduleCat_range_eq_ker x).symm
  have hkerSum (x : (singularChains R X).X n) :
      qsum x = 0 ↔ x ∈ ((singularSubspaceSumChains R A B).f n).hom.range := by
    have h := (ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk (singularSubspaceSumChains R A B)
        (relativeUnionSingularChainsProjection R A B) (cokernel.condition _))
      (cokernelIsCokernel _)).map
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
    exact (SetLike.ext_iff.mp h.moduleCat_range_eq_ker x).symm
  have hdiagA (x : (singularChains R X).X n) :
      fst (D.f (q (A ∩ B) x)) = q A x := by
    have h : relativeSingularChainsProjection R (A ∩ B) ≫ S.f ≫ biprod.fst =
        relativeSingularChainsProjection R A := by
      simp [S, relativeSingularMayerVietorisShortComplex, relativeSingularChainsFunctor,
        relativeSingularChainsMap, relativeSingularChainsProjection]
    exact congrArg (fun f ↦ f.f n x) h
  have hdiagB (x : (singularChains R X).X n) :
      snd (D.f (q (A ∩ B) x)) = q B x := by
    have h : relativeSingularChainsProjection R (A ∩ B) ≫ S.f ≫ biprod.snd =
        relativeSingularChainsProjection R B := by
      simp [S, relativeSingularMayerVietorisShortComplex, relativeSingularChainsFunctor,
        relativeSingularChainsMap, relativeSingularChainsProjection]
    exact congrArg (fun f ↦ f.f n x) h
  have hdiffA (x : (singularChains R X).X n) : D.g (inl (q A x)) = qsum x := by
    have h : relativeSingularChainsProjection R A ≫ biprod.inl ≫ S.g =
        relativeUnionSingularChainsProjection R A B := by
      simp [S, relativeSingularMayerVietorisShortComplex, relativeSingularChainsProjection]
    exact congrArg (fun f ↦ f.f n x) h
  have hdiffB (x : (singularChains R X).X n) : D.g (inr (q B x)) = -qsum x := by
    have h : relativeSingularChainsProjection R B ≫ biprod.inr ≫ S.g =
        -relativeUnionSingularChainsProjection R A B := by
      simp [S, relativeSingularMayerVietorisShortComplex, relativeSingularChainsProjection]
    exact congrArg (fun f ↦ f.f n x) h
  have hkill (U : Set X) (x : (singularChains R U).X n) : q U (i U x) = 0 :=
    (hker U _).mpr ⟨x, rfl⟩
  -- Jointly zero projections mean that an ambient representative belongs to both chain images.
  have hmono : Function.Injective D.f := by
    have hz (z : D.X₁) (hz : D.f z = 0) : z = 0 := by
      obtain ⟨x, rfl⟩ := hsurj (A ∩ B) z
      apply (hker (A ∩ B) x).mpr
      rw [range_singularSubspaceChains_inter]
      exact ⟨(hker A x).mp (by rw [← hdiagA, hz, map_zero]),
        (hker B x).mp (by rw [← hdiagB, hz, map_zero])⟩
    intro z w h
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, h, sub_self]
  -- Every sum-quotient class has a representative in the first summand.
  have hepi : Function.Surjective D.g := by
    intro z
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective qsum).mp inferInstance z
    exact ⟨inl (q A x), (hdiffA x).trans hx⟩
  refine ShortComplex.ShortExact.mk' ?_
    ((ModuleCat.mono_iff_injective _).mpr hmono)
    ((ModuleCat.epi_iff_surjective _).mpr hepi)
  -- Equality in the sum quotient lets us correct two representatives by subspace chains.
  apply D.moduleCat_exact_iff.mpr
  intro z hz
  obtain ⟨x, hx⟩ := hsurj A (fst z)
  obtain ⟨y, hy⟩ := hsurj B (snd z)
  have hrep : inl (q A x) + inr (q B y) = z := by rw [hx, hy, hsplit]
  have hxy : qsum (x - y) = 0 := by
    rw [← hrep, map_add, hdiffA, hdiffB] at hz
    change qsum.hom (x - y) = 0
    rw [qsum.hom.map_sub, sub_eq_add_neg]
    exact hz
  obtain ⟨t, ht⟩ := (hkerSum (x - y)).mp hxy
  let a := (biprod.fst : singularChains R A ⊞ singularChains R B ⟶
    singularChains R A).f n t
  let b := (biprod.snd : singularChains R A ⊞ singularChains R B ⟶
    singularChains R B).f n t
  have hsum : i A a + i B b = x - y := by
    have h := congrArg (fun f ↦ f.f n t)
      (biprod.desc_eq (f := singularSubspaceChains R A) (g := singularSubspaceChains R B))
    exact h.symm.trans ht
  refine ⟨q (A ∩ B) (x - i A a), ?_⟩
  apply hext
  · rw [hdiagA, map_sub, hkill, sub_zero, hx]
  · have hcorrect : x - i A a = y + i B b := by
      rw [← (eq_sub_iff_add_eq.mp hsum)]
      abel
    rw [hdiagB, hcorrect, map_add, hkill, add_zero, hy]

/-- For open A and B, the canonical sum-quotient map to the union-relative chains is a
chain homotopy equivalence. The same comparison induces isomorphisms on homology
and on dual cohomology. -/
theorem homotopyEquivalences_relativeUnionSingularChainsToRelative
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
      (relativeUnionSingularChainsToRelative R A B) := by
  let Z := ↥(A ∪ B)
  let UA : Set Z := (Subtype.val : Z → X) ⁻¹' A
  let UB : Set Z := (Subtype.val : Z → X) ⁻¹' B
  have hOpen : ∀ U ∈ ({UA, UB} : Set (Set Z)), IsOpen U := by
    intro U hU
    have hc : U = UA ∨ U = UB := by simpa using hU
    rcases hc with hU | hU
    · rw [hU]
      exact hA.preimage continuous_subtype_val
    · rw [hU]
      exact hB.preimage continuous_subtype_val
  have hCover : ⋃₀ ({UA, UB} : Set (Set Z)) = Set.univ := by
    rw [Set.sUnion_pair]
    ext x
    exact iff_true_intro x.property
  obtain ⟨hSmall⟩ := contractible_cokernel_smallSingularChains R {UA, UB} hOpen hCover
  let eA : A ≃ₜ UA :=
    { toFun := fun x ↦ ⟨⟨x.val, Or.inl x.property⟩, x.property⟩
      invFun := fun x ↦ ⟨x.val.val, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let eB : B ≃ₜ UB :=
    { toFun := fun x ↦ ⟨⟨x.val, Or.inr x.property⟩, x.property⟩
      invFun := fun x ↦ ⟨x.val.val, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let EA := (singularChainsFunctor R).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of A) (Y := TopCat.of UA) eA)
  let EB := (singularChainsFunctor R).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of B) (Y := TopCat.of UB) eB)
  let E := biprod.mapIso EA EB
  let i₀ := biprod.desc (singularSubspaceChains R UA) (singularSubspaceChains R UB)
  let i := E.hom ≫ i₀
  let j := singularSubspaceChains R (A ∪ B)
  have hAmap : EA.hom ≫ singularSubspaceChains R UA ≫ j = singularSubspaceChains R A := by
    change (singularChainsFunctor R).map _ ≫ (singularChainsFunctor R).map _ ≫
      (singularChainsFunctor R).map _ = (singularChainsFunctor R).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  have hBmap : EB.hom ≫ singularSubspaceChains R UB ≫ j = singularSubspaceChains R B := by
    change (singularChainsFunctor R).map _ ≫ (singularChainsFunctor R).map _ ≫
      (singularChainsFunctor R).map _ = (singularChainsFunctor R).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  have hfactor : i ≫ j = singularSubspaceSumChains R A B := by
    apply biprod.hom_ext'
    · simpa [i, E, i₀, singularSubspaceSumChains] using hAmap
    · simpa [i, E, i₀, singularSubspaceSumChains] using hBmap
  -- Both changes of source preserve the actual quotient of the union's singular chains.
  let e₀ := cokernelIsoOfDegreewiseRangeEq (smallSingularChainsInclusion R {UA, UB}) i₀
    (range_smallSingularChainsInclusion_pair R UA UB)
  have h₀ : Homotopy (𝟙 (cokernel i₀)) 0 := by
    have H := (hSmall.compLeft e₀.inv).compRight e₀.hom
    simpa only [Category.comp_id, e₀.inv_hom_id, comp_zero, zero_comp] using H
  let e₁ := cokernelEpiComp E.hom i₀
  have h₁ : Homotopy (𝟙 (cokernel i)) 0 := by
    have H := (h₀.compLeft e₁.hom).compRight e₁.inv
    simpa only [Category.comp_id, e₁.hom_inv_id, comp_zero, zero_comp] using H
  have hj (n : ℕ) : IsSplitMono (j.f n) :=
    isSplitMono_singularChainsMap_of_injective R
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(A ∪ B), X)) Subtype.val_injective n
  obtain ⟨T, hT⟩ := homotopyEquivalences_cokernel_desc_of_contractible i j hj h₁
  let Q := cokernelIsoOfEq hfactor
  have hforward : Q.hom ≫ relativeUnionSingularChainsToRelative R A B = T.hom := by
    rw [hT]
    apply (cancel_epi (cokernel.π (i ≫ j))).mp
    rw [← Category.assoc, π_comp_cokernelIsoOfEq_hom, cokernel.π_desc]
    simp [relativeUnionSingularChainsToRelative, j]
  let S := (HomotopyEquiv.ofIso Q.symm).trans T
  refine ⟨S, ?_⟩
  change Q.inv ≫ T.hom = relativeUnionSingularChainsToRelative R A B
  rw [← hforward, ← Category.assoc, Q.inv_hom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- For open A and B, classes in H_k(X,A) and H_k(X,B) with the same image in
H_k(X,A ∪ B) lift to one class in H_k(X,A ∩ B) under the original inclusion maps. -/
theorem exists_relativeSingularHomology_inter_of_compatible
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (k : ℕ)
    (a : relativeSingularHomology R A k) (b : relativeSingularHomology R B k)
    (h : relativeSingularHomologyInclusion R A (A ∪ B) Set.subset_union_left k a =
      relativeSingularHomologyInclusion R B (A ∪ B) Set.subset_union_right k b) :
    ∃ c : relativeSingularHomology R (A ∩ B) k,
      relativeSingularHomologyInclusion R (A ∩ B) A Set.inter_subset_left k c = a ∧
      relativeSingularHomologyInclusion R (A ∩ B) B Set.inter_subset_right k c = b := by
  let S := relativeSingularMayerVietorisShortComplex R A B
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) k
  let inl : relativeSingularChains R A ⟶ S.X₂ := biprod.inl
  let inr : relativeSingularChains R B ⟶ S.X₂ := biprod.inr
  let fst : S.X₂ ⟶ relativeSingularChains R A := biprod.fst
  let snd : S.X₂ ⟶ relativeSingularChains R B := biprod.snd
  let cmp := relativeUnionSingularChainsToRelative R A B
  -- Excision compares the sum quotient with the actual relative group of the open union.
  obtain ⟨e, he⟩ := homotopyEquivalences_relativeUnionSingularChainsToRelative R A B hA hB
  have : IsIso (F.map cmp) := by
    change IsIso (HomologicalComplex.homologyMap cmp k)
    dsimp only [cmp]
    erw [← he]
    exact inferInstanceAs (IsIso (e.toHomologyIso k).hom)
  have hcompA : F.map inl ≫ F.map S.g ≫ F.map cmp =
      relativeSingularHomologyInclusion R A (A ∪ B) Set.subset_union_left k := by
    rw [← F.map_comp, ← F.map_comp]
    have hchain : inl ≫ S.g ≫ cmp = (relativeSingularChainsFunctor R X).map
        (homOfLE (Set.subset_union_left (s := A) (t := B))) := by
      apply (cancel_epi (relativeSingularChainsProjection R A)).mp
      simp [S, inl, cmp, relativeSingularMayerVietorisShortComplex,
        relativeUnionSingularChainsToRelative, relativeSingularChainsFunctor,
        relativeSingularChainsMap, relativeSingularChainsProjection]
    rw [hchain]
    rfl
  have hcompB : F.map inr ≫ F.map S.g ≫ F.map cmp =
      -relativeSingularHomologyInclusion R B (A ∪ B) Set.subset_union_right k := by
    rw [← F.map_comp, ← F.map_comp]
    have hchain : inr ≫ S.g ≫ cmp = -(relativeSingularChainsFunctor R X).map
        (homOfLE (Set.subset_union_right (s := A) (t := B))) := by
      apply (cancel_epi (relativeSingularChainsProjection R B)).mp
      simp [S, inr, cmp, relativeSingularMayerVietorisShortComplex,
        relativeUnionSingularChainsToRelative, relativeSingularChainsFunctor,
        relativeSingularChainsMap, relativeSingularChainsProjection]
    rw [hchain, F.map_neg]
    rfl
  -- Form the pair of classes in the homology of the same chain biproduct.
  let z : F.obj S.X₂ := F.map inl a + F.map inr b
  have hz : F.map S.g z = 0 := by
    apply ((ConcreteCategory.isIso_iff_bijective (F.map cmp)).mp inferInstance).injective
    rw [map_zero]
    dsimp only [z]
    rw [map_add, map_add]
    change (F.map inl ≫ F.map S.g ≫ F.map cmp) a +
      (F.map inr ≫ F.map S.g ≫ F.map cmp) b = 0
    rw [hcompA, hcompB]
    change relativeSingularHomologyInclusion R A (A ∪ B) Set.subset_union_left k a +
      -relativeSingularHomologyInclusion R B (A ∪ B) Set.subset_union_right k b = 0
    rw [h, add_neg_cancel]
  obtain ⟨c, hc⟩ : ∃ c : relativeSingularHomology R (A ∩ B) k, F.map S.f c = z :=
    (ShortComplex.moduleCat_exact_iff _).mp
      ((shortExact_relativeSingularMayerVietorisShortComplex R A B).homology_exact₂ k) z hz
  refine ⟨c, ?_, ?_⟩
  · -- The first projection of the diagonal is the original inclusion into A.
    have hproj : F.map S.f ≫ F.map fst =
        relativeSingularHomologyInclusion R (A ∩ B) A Set.inter_subset_left k := by
      rw [← F.map_comp]
      simp only [S, fst, relativeSingularMayerVietorisShortComplex, biprod.lift_fst]
      rfl
    have hinl : F.map inl ≫ F.map fst = 𝟙 _ := by
      rw [← F.map_comp]
      simp [inl, fst]
    have hinr : F.map inr ≫ F.map fst = 0 := by
      rw [← F.map_comp]
      simp [inr, fst]
    have hh := congrArg (fun x ↦ F.map fst x) hc
    change (F.map S.f ≫ F.map fst) c = F.map fst z at hh
    rw [hproj] at hh
    refine hh.trans ?_
    change F.map fst (F.map inl a + F.map inr b) = a
    rw [map_add]
    change (F.map inl ≫ F.map fst) a + (F.map inr ≫ F.map fst) b = a
    rw [hinl, hinr]
    exact add_zero a
  · -- The second projection has the same positive normalization as the first.
    have hproj : F.map S.f ≫ F.map snd =
        relativeSingularHomologyInclusion R (A ∩ B) B Set.inter_subset_right k := by
      rw [← F.map_comp]
      simp only [S, snd, relativeSingularMayerVietorisShortComplex, biprod.lift_snd]
      rfl
    have hinl : F.map inl ≫ F.map snd = 0 := by
      rw [← F.map_comp]
      simp [inl, snd]
    have hinr : F.map inr ≫ F.map snd = 𝟙 _ := by
      rw [← F.map_comp]
      simp [inr, snd]
    have hh := congrArg (fun x ↦ F.map snd x) hc
    change (F.map S.f ≫ F.map snd) c = F.map snd z at hh
    rw [hproj] at hh
    refine hh.trans ?_
    change F.map snd (F.map inl a + F.map inr b) = b
    rw [map_add]
    change (F.map inl ≫ F.map snd) a + (F.map inr ≫ F.map snd) b = b
    rw [hinl, hinr]
    exact zero_add b

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The degree-k relative inclusion maps are jointly injective when
H_(k+1)(X,A ∪ B) vanishes. -/
theorem relativeSingularHomologyInclusion_inter_jointly_injective
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (k : ℕ)
    [Subsingleton (relativeSingularHomology R (A ∪ B) (k + 1))] :
    Function.Injective (fun c : relativeSingularHomology R (A ∩ B) k ↦
      (relativeSingularHomologyInclusion R (A ∩ B) A Set.inter_subset_left k c,
        relativeSingularHomologyInclusion R (A ∩ B) B Set.inter_subset_right k c)) := by
  let S := relativeSingularMayerVietorisShortComplex R A B
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) k
  let inl : relativeSingularChains R A ⟶ S.X₂ := biprod.inl
  let inr : relativeSingularChains R B ⟶ S.X₂ := biprod.inr
  let fst : S.X₂ ⟶ relativeSingularChains R A := biprod.fst
  let snd : S.X₂ ⟶ relativeSingularChains R B := biprod.snd
  -- The preceding term is the original union group by the specified chain homotopy equivalence.
  obtain ⟨e, _⟩ := homotopyEquivalences_relativeUnionSingularChainsToRelative R A B hA hB
  let eH : S.X₃.homology (k + 1) ≅ relativeSingularHomology R (A ∪ B) (k + 1) :=
    e.toHomologyIso (k + 1)
  have hzero : IsZero (S.X₃.homology (k + 1)) :=
    IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr inferInstance) eH
  have hmono : Mono (F.map S.f) :=
    ((shortExact_relativeSingularMayerVietorisShortComplex R A B).homology_exact₁
      (k + 1) k rfl).mono_g (hzero.eq_of_src _ _)
  -- The two projections of the chain diagonal remain the actual relative inclusions.
  have hprojA : F.map S.f ≫ F.map fst =
      relativeSingularHomologyInclusion R (A ∩ B) A Set.inter_subset_left k := by
    rw [← F.map_comp]
    simp only [S, fst, relativeSingularMayerVietorisShortComplex, biprod.lift_fst]
    rfl
  have hprojB : F.map S.f ≫ F.map snd =
      relativeSingularHomologyInclusion R (A ∩ B) B Set.inter_subset_right k := by
    rw [← F.map_comp]
    simp only [S, snd, relativeSingularMayerVietorisShortComplex, biprod.lift_snd]
    rfl
  have htotal : F.map fst ≫ F.map inl + F.map snd ≫ F.map inr = 𝟙 (F.obj S.X₂) := by
    rw [← F.map_comp, ← F.map_comp, ← F.map_add]
    have hchain : fst ≫ inl + snd ≫ inr = 𝟙 S.X₂ := biprod.total
    exact (congrArg (fun f ↦ F.map f) hchain).trans (F.map_id _)
  have hext {z w : F.obj S.X₂} (hf : F.map fst z = F.map fst w)
      (hs : F.map snd z = F.map snd w) : z = w := by
    have hz : F.map inl (F.map fst z) + F.map inr (F.map snd z) = z :=
      congrArg (fun f ↦ f z) htotal
    have hw : F.map inl (F.map fst w) + F.map inr (F.map snd w) = w :=
      congrArg (fun f ↦ f w) htotal
    rw [← hz, hf, hs, hw]
  intro c d hcd
  apply (ModuleCat.mono_iff_injective _).mp hmono
  apply hext
  · change (F.map S.f ≫ F.map fst) c = (F.map S.f ≫ F.map fst) d
    rw [hprojA]
    exact congrArg Prod.fst hcd
  · change (F.map S.f ≫ F.map snd) c = (F.map S.f ≫ F.map snd) d
    rw [hprojB]
    exact congrArg Prod.snd hcd

/-- Relative Mayer–Vietoris propagates vanishing from the two subspaces and their union. -/
theorem relativeSingularHomology_subsingleton_inter
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (k : ℕ)
    [Subsingleton (relativeSingularHomology R A k)]
    [Subsingleton (relativeSingularHomology R B k)]
    [Subsingleton (relativeSingularHomology R (A ∪ B) (k + 1))] :
    Subsingleton (relativeSingularHomology R (A ∩ B) k) :=
  (relativeSingularHomologyInclusion_inter_jointly_injective R A B hA hB k).subsingleton

end AtiyahSinger
