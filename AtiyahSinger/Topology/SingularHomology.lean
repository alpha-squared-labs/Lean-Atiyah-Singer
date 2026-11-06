/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularCohomology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Singular homology and normalized rational coefficient change

Public module ID: M2141.

D11 / E03. Ordinary and relative homology are the homology of the original
singular chains and their original relative cokernels. All induced maps use
the specified continuous maps of pairs. The integer-to-rational coefficient
map sends each original simplex with integer coefficient a to the very same
simplex with coefficient (a : ℚ). Its defining generator formula, and the
relative cokernel square, determine the maps uniquely.

Restriction of scalars is used only to place those maps in ModuleCat ℤ.
The canonical homology comparison returns to the original rational homology
object; no new chain or homology theory is selected. In particular these
maps do not multiply orientation classes by an arbitrary rational unit.

Sources: Hatcher, Algebraic Topology, sections 2.1 and 3.3, especially the
coefficient discussion on p.235. The unique universal constructions below
are implementation certificates for the standard coefficient homomorphism.
The proofs retain the original generators, quotient projections and homology comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R]

/-- Ordinary singular homology of the original chain complex. -/
abbrev singularHomology (X : Type u) [TopologicalSpace X] (n : ℕ) : ModuleCat.{u} R :=
  (singularChains R X).homology n

/-- Relative singular homology of the original quotient by subspace chains. -/
abbrev relativeSingularHomology {X : Type u} [TopologicalSpace X]
    (A : Set X) (n : ℕ) : ModuleCat.{u} R :=
  (relativeSingularChains R A).homology n

/-- The homology map induced by the given continuous map of the original spaces. -/
def singularHomologyMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) : singularHomology R X n ⟶ singularHomology R Y n :=
  HomologicalComplex.homologyMap ((singularChainsFunctor R).map (TopCat.ofHom f)) n

/-- The relative homology map induced by the given continuous map of pairs. -/
def relativeSingularHomologyMap {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (n : ℕ) :
    relativeSingularHomology R A n ⟶ relativeSingularHomology R B n :=
  HomologicalComplex.homologyMap (relativeSingularChainsMap R f hf) n

/-- Enlarging the subspace induces the original covariant quotient map on homology. -/
def relativeSingularHomologyInclusion {X : Type u} [TopologicalSpace X]
    (A B : Set X) (h : A ⊆ B) (n : ℕ) :
    relativeSingularHomology R A n ⟶ relativeSingularHomology R B n :=
  relativeSingularHomologyMap R (ContinuousMap.id X) (fun _ hx ↦ h hx) n

section RationalCoefficients

local notation "ℚRes" => ModuleCat.restrictScalars (Int.castRingHom ℚ)
local notation "ℚResC" => Functor.mapHomologicalComplex
  (ModuleCat.restrictScalars (Int.castRingHom ℚ)) (ComplexShape.down ℕ)

/-- Coefficient inclusion uniquely extends the identical-simplex formula to a chain map. -/
theorem existsUnique_singularChainsRationalization
    (X : Type u) [TopologicalSpace X] :
    ∃! f : singularChains ℤ X ⟶ (ℚResC).obj (singularChains ℚ X),
      ∀ (n : ℕ) (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) (a : ℤ),
        f.f n ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := singularCoefficient ℤ) σ (ULift.up a)) =
        (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := singularCoefficient ℚ) σ (ULift.up (a : ℚ)) := by
  /- Stage 1: extend a ↦ (a : ℚ) on each original simplex summand using
  the coproduct universal property. Restriction of scalars makes this
  an actual integer-linear map with the required values.
  Stage 2: each differential is the alternating sum of the same faces.
  Integer inclusion preserves addition and signs, so the degreewise
  maps commute with every differential, including the zero boundary
  in degree zero. They form a chain map on the original complexes.
  Stage 3: coproduct extensionality in each degree proves uniqueness.
  No choice of homology generators or rational scaling occurs. -/
  classical
  let S := TopCat.toSSet.obj (TopCat.of X)
  -- Include the coefficient on each original free simplex summand.
  let coefficient : singularCoefficient ℤ ⟶ (ℚRes).obj (singularCoefficient ℚ) :=
    ModuleCat.ofHom
      { toFun := fun a ↦ ULift.up (a.down : ℚ)
        map_add' := by
          intro a b
          apply ULift.ext
          simp
        map_smul' := by
          intro a b
          apply ULift.ext
          simp }
  let component (n : ℕ) : (singularChains ℤ X).X n ⟶
      (ℚRes).obj ((singularChains ℚ X).X n) :=
    Sigma.desc fun σ : S.obj (op ⦋n⦌) ↦
      coefficient ≫ (ℚRes).map (S.ιChainComplex (R := singularCoefficient ℚ) σ)
  have heval (n : ℕ) (σ : S.obj (op ⦋n⦌)) (a : ℤ) :
      component n (S.ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up a)) =
        S.ιChainComplex (R := singularCoefficient ℚ) σ (ULift.up (a : ℚ)) := by
    change (Sigma.ι (fun _ : S.obj (op ⦋n⦌) ↦ singularCoefficient ℤ) σ ≫
      Sigma.desc (fun τ : S.obj (op ⦋n⦌) ↦ coefficient ≫
        (ℚRes).map (S.ιChainComplex (R := singularCoefficient ℚ) τ))) (ULift.up a) = _
    rw [Sigma.ι_comp_desc]
    rfl
  -- The original boundary is the alternating sum of the same faces in both coefficient rings.
  let F : singularChains ℤ X ⟶ (ℚResC).obj (singularChains ℚ X) :=
    { f := component
      comm' := by
        intro n m hnm
        change m + 1 = n at hnm
        subst n
        apply Sigma.hom_ext
        intro σ
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        change (singularChains ℚ X).d (m + 1) m
          (component (m + 1)
            (S.ιChainComplex (R := singularCoefficient ℤ) σ a)) =
          component m ((singularChains ℤ X).d (m + 1) m
            (S.ιChainComplex (R := singularCoefficient ℤ) σ a))
        have ha : a = ULift.up a.down := rfl
        rw [ha, heval]
        change (S.ιChainComplex (R := singularCoefficient ℚ) σ ≫
          (S.chainComplex (singularCoefficient ℚ)).d (m + 1) m) (ULift.up (a.down : ℚ)) =
          component m ((S.ιChainComplex (R := singularCoefficient ℤ) σ ≫
            (S.chainComplex (singularCoefficient ℤ)).d (m + 1) m) (ULift.up a.down))
        rw [SSet.ιChainComplex_d, SSet.ιChainComplex_d]
        simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
          LinearMap.sum_apply, LinearMap.smul_apply]
        let zterm (i : Fin (m + 2)) : (singularChains ℤ X).X m :=
          S.ιChainComplex (R := singularCoefficient ℤ) (S.δ i σ) (ULift.up a.down)
        let qterm (i : Fin (m + 2)) : (ℚRes).obj ((singularChains ℚ X).X m) :=
          S.ιChainComplex (R := singularCoefficient ℚ) (S.δ i σ) (ULift.up (a.down : ℚ))
        change (∑ i : Fin (m + 2), (-1 : ℤ) ^ i.val • qterm i) =
          (component m).hom (∑ i : Fin (m + 2), (-1 : ℤ) ^ i.val • zterm i)
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_zsmul]
        exact congrArg (fun z ↦ ((-1 : ℤ) ^ i.val) • z) (heval m (S.δ i σ) a.down).symm }
  refine ⟨F, heval, ?_⟩
  -- Every original coproduct summand fixes the entire chain map uniquely.
  intro G hG
  apply HomologicalComplex.Hom.ext
  funext n
  apply Sigma.hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (hG n σ a.down).trans (heval n σ a.down).symm

/-- The actual coefficient inclusion on singular chains, fixed on every original simplex. -/
def singularChainsRationalization (X : Type u) [TopologicalSpace X] :
    singularChains ℤ X ⟶ (ℚResC).obj (singularChains ℚ X) :=
  Classical.choose (existsUnique_singularChainsRationalization X).exists

/-- The ordinary coefficient map descends uniquely through the original relative quotient. -/
theorem existsUnique_relativeSingularChainsRationalization
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    ∃! f : relativeSingularChains ℤ A ⟶ (ℚResC).obj (relativeSingularChains ℚ A),
      relativeSingularChainsProjection ℤ A ≫ f =
        singularChainsRationalization X ≫
          (ℚResC).map (relativeSingularChainsProjection ℚ A) := by
  /- Stage 1: a simplex contained in A is sent to the same simplex
  over ℚ, whose image in C_*(X,A;ℚ) is zero. Thus the displayed map
  annihilates the original inclusion C_*(A;ℤ) → C_*(X;ℤ).
  Stage 2: apply the cokernel universal property in integer-module
  chain complexes. Restriction of scalars changes no vectors or
  differentials, so the target is precisely the original rational
  relative complex with restricted scalars. The cokernel projection
  is an epimorphism, proving uniqueness of this factorization. -/
  have hordinarySquare {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
      (g : C(Y, Z)) :
      (singularChainsFunctor ℤ).map (TopCat.ofHom g) ≫ singularChainsRationalization Z =
        singularChainsRationalization Y ≫ (ℚResC).map
          ((singularChainsFunctor ℚ).map (TopCat.ofHom g)) := by
    have heval (W : Type u) [TopologicalSpace W] :=
      Classical.choose_spec (existsUnique_singularChainsRationalization W).exists
    have hmap (R : Type) [CommRing R] (n : ℕ)
        (σ : (TopCat.toSSet.obj (TopCat.of Y)).obj (op ⦋n⦌)) (a : ULift.{u} R) :
        ((singularChainsFunctor R).map (TopCat.ofHom g)).f n
          ((TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex
            (R := singularCoefficient R) σ a) =
          (TopCat.toSSet.obj (TopCat.of Z)).ιChainComplex
            (R := singularCoefficient R)
            ((TopCat.toSSet.map (TopCat.ofHom g)).app (op ⦋n⦌) σ) a := by
      change ((TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex σ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom g))
          (singularCoefficient R)).f n) a = _
      rw [SSet.ι_chainComplexMap_f]
    apply HomologicalComplex.Hom.ext
    funext n
    apply Sigma.hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    let τ := (TopCat.toSSet.map (TopCat.ofHom g)).app (op ⦋n⦌) σ
    have h₁ := congrArg ((singularChainsRationalization Z).f n) (hmap ℤ n σ a)
    have h₂ := heval Z n τ a.down
    have h₃ := hmap ℚ n σ (ULift.up (a.down : ℚ))
    have h₄ := congrArg (((singularChainsFunctor ℚ).map (TopCat.ofHom g)).f n)
      (heval Y n σ a.down)
    exact h₁.trans (h₂.trans (h₃.symm.trans h₄.symm))
  -- The ordinary coefficient map annihilates the given subspace after quotient projection.
  let q := singularChainsRationalization X ≫
    (ℚResC).map (relativeSingularChainsProjection ℚ A)
  have hzero : singularSubspaceChains ℤ A ≫ q = 0 := by
    have h := hordinarySquare (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))
    change singularSubspaceChains ℤ A ≫ singularChainsRationalization X =
      singularChainsRationalization A ≫ (ℚResC).map (singularSubspaceChains ℚ A) at h
    dsimp only [q]
    rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp]
    rw [show singularSubspaceChains ℚ A ≫ relativeSingularChainsProjection ℚ A = 0 from
      cokernel.condition (singularSubspaceChains ℚ A), Functor.map_zero, comp_zero]
  -- Factor through the original integer cokernel and use its epimorphic projection for uniqueness.
  refine ⟨cokernel.desc (singularSubspaceChains ℤ A) q hzero, ?_, ?_⟩
  · exact cokernel.π_desc (singularSubspaceChains ℤ A) q hzero
  · intro F hF
    apply (cancel_epi (relativeSingularChainsProjection ℤ A)).mp
    exact hF.trans (cokernel.π_desc (singularSubspaceChains ℤ A) q hzero).symm

/-- The actual relative coefficient inclusion, using the prescribed quotient square. -/
def relativeSingularChainsRationalization {X : Type u} [TopologicalSpace X]
    (A : Set X) :
    relativeSingularChains ℤ A ⟶ (ℚResC).obj (relativeSingularChains ℚ A) :=
  Classical.choose (existsUnique_relativeSingularChainsRationalization A).exists

/-- The canonical integer-linear coefficient map into the original rational homology. -/
def singularHomologyRationalization (X : Type u) [TopologicalSpace X] (n : ℕ) :
    singularHomology ℤ X n ⟶ (ℚRes).obj (singularHomology ℚ X n) :=
  HomologicalComplex.homologyMap (singularChainsRationalization X) n ≫
    (((singularChains ℚ X).sc n).mapHomologyIso ℚRes).hom

/-- Relative coefficient inclusion, with the canonical restriction-of-scalars comparison. -/
def relativeSingularHomologyRationalization {X : Type u} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    relativeSingularHomology ℤ A n ⟶ (ℚRes).obj (relativeSingularHomology ℚ A n) :=
  HomologicalComplex.homologyMap (relativeSingularChainsRationalization A) n ≫
    (((relativeSingularChains ℚ A).sc n).mapHomologyIso ℚRes).hom

/-- Changing coefficients commutes with the specified original map of pairs. -/
theorem relativeSingularHomologyRationalization_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (n : ℕ)
    (c : relativeSingularHomology ℤ A n) :
    relativeSingularHomologyRationalization B n
        (relativeSingularHomologyMap ℤ f hf n c) =
      relativeSingularHomologyMap ℚ f hf n
        (relativeSingularHomologyRationalization A n c) := by
  /- Stage 1: on a generator a·σ both composites are (a : ℚ)·(f ∘ σ).
  Uniqueness of the coefficient chain maps gives the ordinary square.
  Stage 2: use the prescribed cokernel squares and their epimorphic
  projections to obtain the relative square for the same A, B and f.
  Stage 3: apply homology and the natural restriction-of-scalars
  comparison. Evaluating at c gives precisely the displayed equality. -/
  have hordinarySquare {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
      (g : C(Y, Z)) :
      (singularChainsFunctor ℤ).map (TopCat.ofHom g) ≫ singularChainsRationalization Z =
        singularChainsRationalization Y ≫ (ℚResC).map
          ((singularChainsFunctor ℚ).map (TopCat.ofHom g)) := by
    have heval (W : Type u) [TopologicalSpace W] :=
      Classical.choose_spec (existsUnique_singularChainsRationalization W).exists
    have hmap (R : Type) [CommRing R] (n : ℕ)
        (σ : (TopCat.toSSet.obj (TopCat.of Y)).obj (op ⦋n⦌)) (a : ULift.{u} R) :
        ((singularChainsFunctor R).map (TopCat.ofHom g)).f n
          ((TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex
            (R := singularCoefficient R) σ a) =
          (TopCat.toSSet.obj (TopCat.of Z)).ιChainComplex
            (R := singularCoefficient R)
            ((TopCat.toSSet.map (TopCat.ofHom g)).app (op ⦋n⦌) σ) a := by
      change ((TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex σ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom g))
          (singularCoefficient R)).f n) a = _
      rw [SSet.ι_chainComplexMap_f]
    apply HomologicalComplex.Hom.ext
    funext n
    apply Sigma.hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    let τ := (TopCat.toSSet.map (TopCat.ofHom g)).app (op ⦋n⦌) σ
    have h₁ := congrArg ((singularChainsRationalization Z).f n) (hmap ℤ n σ a)
    have h₂ := heval Z n τ a.down
    have h₃ := hmap ℚ n σ (ULift.up (a.down : ℚ))
    have h₄ := congrArg (((singularChainsFunctor ℚ).map (TopCat.ofHom g)).f n)
      (heval Y n σ a.down)
    exact h₁.trans (h₂.trans (h₃.symm.trans h₄.symm))
  -- Compare the original pair maps after the original epimorphic quotient projection.
  let PZ := relativeSingularChainsMap ℤ f hf
  let PQ := relativeSingularChainsMap ℚ f hf
  let FA := relativeSingularChainsRationalization A
  let FB := relativeSingularChainsRationalization B
  have hprojection (R : Type) [CommRing R] :
      relativeSingularChainsProjection R A ≫ relativeSingularChainsMap R f hf =
        (singularChainsFunctor R).map (TopCat.ofHom f) ≫
          relativeSingularChainsProjection R B := by
    simp [relativeSingularChainsProjection, relativeSingularChainsMap]
  have hFA : relativeSingularChainsProjection ℤ A ≫ FA =
      singularChainsRationalization X ≫ (ℚResC).map (relativeSingularChainsProjection ℚ A) :=
    Classical.choose_spec (existsUnique_relativeSingularChainsRationalization A).exists
  have hFB : relativeSingularChainsProjection ℤ B ≫ FB =
      singularChainsRationalization Y ≫ (ℚResC).map (relativeSingularChainsProjection ℚ B) :=
    Classical.choose_spec (existsUnique_relativeSingularChainsRationalization B).exists
  have hsquare : PZ ≫ FB = FA ≫ (ℚResC).map PQ := by
    apply (cancel_epi (relativeSingularChainsProjection ℤ A)).mp
    rw [← Category.assoc, hprojection ℤ, Category.assoc, hFB, ← Category.assoc,
      hordinarySquare f, Category.assoc, ← Functor.map_comp, ← hprojection ℚ,
      Functor.map_comp, ← Category.assoc, ← hFA, Category.assoc]
  -- Homology respects the square, and its native scalar-restriction comparison is natural.
  have hmap := congrArg (fun F ↦ HomologicalComplex.homologyMap F n) hsquare
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
  have hvalue := congrArg (fun F ↦ F c) hmap
  change HomologicalComplex.homologyMap FB n (HomologicalComplex.homologyMap PZ n c) =
    HomologicalComplex.homologyMap ((ℚResC).map PQ) n
      (HomologicalComplex.homologyMap FA n c) at hvalue
  have hnat := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℚ)
      (ComplexShape.down ℕ) n).map PQ) ℚRes
  have hnatValue := congrArg (fun F ↦ F (HomologicalComplex.homologyMap FA n c)) hnat
  change (((relativeSingularChains ℚ B).sc n).mapHomologyIso ℚRes).hom
    (HomologicalComplex.homologyMap ((ℚResC).map PQ) n
      (HomologicalComplex.homologyMap FA n c)) =
        relativeSingularHomologyMap ℚ f hf n
          (relativeSingularHomologyRationalization A n c) at hnatValue
  exact (congrArg (((relativeSingularChains ℚ B).sc n).mapHomologyIso ℚRes).hom hvalue).trans
    hnatValue

end RationalCoefficients

end AtiyahSinger
