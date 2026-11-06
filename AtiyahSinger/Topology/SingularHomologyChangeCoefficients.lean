/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularHomology

/-!
# Integral coefficient change on the original singular chains

Public module ID: M2143.

The integer coefficient homomorphism into an arbitrary commutative ring
acts on the same original singular simplices. The map descends through the
specified relative quotient and its induced map uses the canonical homology
comparison for restriction of scalars. No tensor model, coefficient
injectivity, nonzero-ring hypothesis or independent generator is selected.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R]


local notation "RRes" => ModuleCat.restrictScalars (Int.castRingHom R)
local notation "RResC" => Functor.mapHomologicalComplex
  (ModuleCat.restrictScalars (Int.castRingHom R)) (ComplexShape.down ℕ)

/-- The coefficient homomorphism uniquely extends the identical-simplex formula to a chain map. -/
theorem existsUnique_singularChainsChangeCoefficients
    (X : Type u) [TopologicalSpace X] :
    ∃! f : singularChains ℤ X ⟶ (RResC).obj (singularChains R X),
      ∀ (n : ℕ) (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) (a : ℤ),
        f.f n ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := singularCoefficient ℤ) σ (ULift.up a)) =
        (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := singularCoefficient R) σ (ULift.up (a : R)) := by
  /- Stage 1: extend a ↦ (a : R) on each original simplex summand using
  the coproduct universal property. Restriction of scalars makes this
  an actual integer-linear map with the required values.
  Stage 2: each differential is the alternating sum of the same faces.
  The coefficient homomorphism preserves addition and signs, so the degreewise
  maps commute with every differential, including the zero boundary
  in degree zero. They form a chain map on the original complexes.
  Stage 3: coproduct extensionality in each degree proves uniqueness.
  No choice of homology generators or target-ring scaling occurs. -/
  classical
  let S := TopCat.toSSet.obj (TopCat.of X)
  -- Map the coefficient on each original free simplex summand.
  let coefficientMap : singularCoefficient ℤ →ₛₗ[Int.castRingHom R]
      singularCoefficient R :=
    { toFun := fun a ↦ ULift.up (a.down : R)
      map_add' := by
        intro a b
        apply ULift.ext
        simp
      map_smul' := by
        intro a b
        apply ULift.ext
        simp }
  let coefficient : singularCoefficient ℤ ⟶ (RRes).obj (singularCoefficient R) :=
    ModuleCat.semilinearMapAddEquiv (Int.castRingHom R)
      (singularCoefficient ℤ) (singularCoefficient R) coefficientMap
  let component (n : ℕ) : (singularChains ℤ X).X n ⟶
      (RRes).obj ((singularChains R X).X n) :=
    Sigma.desc fun σ : S.obj (op ⦋n⦌) ↦
      coefficient ≫ (RRes).map (S.ιChainComplex (R := singularCoefficient R) σ)
  have heval (n : ℕ) (σ : S.obj (op ⦋n⦌)) (a : ℤ) :
      component n (S.ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up a)) =
        S.ιChainComplex (R := singularCoefficient R) σ (ULift.up (a : R)) := by
    change (Sigma.ι (fun _ : S.obj (op ⦋n⦌) ↦ singularCoefficient ℤ) σ ≫
      Sigma.desc (fun τ : S.obj (op ⦋n⦌) ↦ coefficient ≫
        (RRes).map (S.ιChainComplex (R := singularCoefficient R) τ))) (ULift.up a) = _
    rw [Sigma.ι_comp_desc]
    rfl
  -- The original boundary is the alternating sum of the same faces in both coefficient rings.
  let F : singularChains ℤ X ⟶ (RResC).obj (singularChains R X) :=
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
        change (singularChains R X).d (m + 1) m
          (component (m + 1)
            (S.ιChainComplex (R := singularCoefficient ℤ) σ a)) =
          component m ((singularChains ℤ X).d (m + 1) m
            (S.ιChainComplex (R := singularCoefficient ℤ) σ a))
        have ha : a = ULift.up a.down := rfl
        rw [ha, heval]
        change (S.ιChainComplex (R := singularCoefficient R) σ ≫
          (S.chainComplex (singularCoefficient R)).d (m + 1) m) (ULift.up (a.down : R)) =
          component m ((S.ιChainComplex (R := singularCoefficient ℤ) σ ≫
            (S.chainComplex (singularCoefficient ℤ)).d (m + 1) m) (ULift.up a.down))
        rw [SSet.ιChainComplex_d, SSet.ιChainComplex_d]
        simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
          LinearMap.sum_apply, LinearMap.smul_apply]
        let zterm (i : Fin (m + 2)) : (singularChains ℤ X).X m :=
          S.ιChainComplex (R := singularCoefficient ℤ) (S.δ i σ) (ULift.up a.down)
        let qterm (i : Fin (m + 2)) : (RRes).obj ((singularChains R X).X m) :=
          S.ιChainComplex (R := singularCoefficient R) (S.δ i σ) (ULift.up (a.down : R))
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

/-- The coefficient map on singular chains, fixed on every original simplex. -/
def singularChainsChangeCoefficients (X : Type u) [TopologicalSpace X] :
    singularChains ℤ X ⟶ (RResC).obj (singularChains R X) :=
  Classical.choose (existsUnique_singularChainsChangeCoefficients R X).exists

/-- Coefficient change commutes with the original continuous map on chains. -/
theorem singularChainsChangeCoefficients_naturality
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (g : C(Y, Z)) :
    (singularChainsFunctor ℤ).map (TopCat.ofHom g) ≫ singularChainsChangeCoefficients R Z =
      singularChainsChangeCoefficients R Y ≫ (RResC).map
        ((singularChainsFunctor R).map (TopCat.ofHom g)) := by
  have heval (W : Type u) [TopologicalSpace W] :=
    Classical.choose_spec (existsUnique_singularChainsChangeCoefficients R W).exists
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
  have h₁ := congrArg ((singularChainsChangeCoefficients R Z).f n) (hmap ℤ n σ a)
  have h₂ := heval Z n τ a.down
  have h₃ := hmap R n σ (ULift.up (a.down : R))
  have h₄ := congrArg (((singularChainsFunctor R).map (TopCat.ofHom g)).f n)
    (heval Y n σ a.down)
  exact h₁.trans (h₂.trans (h₃.symm.trans h₄.symm))

/-- The ordinary coefficient map descends uniquely through the original relative quotient. -/
theorem existsUnique_relativeSingularChainsChangeCoefficients
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    ∃! f : relativeSingularChains ℤ A ⟶ (RResC).obj (relativeSingularChains R A),
      relativeSingularChainsProjection ℤ A ≫ f =
        singularChainsChangeCoefficients R X ≫
          (RResC).map (relativeSingularChainsProjection R A) := by
  /- Stage 1: a simplex contained in A is sent to the same simplex
  over R, whose image in C_*(X,A;R) is zero. Thus the displayed map
  annihilates the original inclusion C_*(A;ℤ) → C_*(X;ℤ).
  Stage 2: apply the cokernel universal property in integer-module
  chain complexes. Restriction of scalars changes no vectors or
  differentials, so the target is precisely the original target-ring
  relative complex with restricted scalars. The cokernel projection
  is an epimorphism, proving uniqueness of this factorization. -/
  -- The ordinary coefficient map annihilates the given subspace after quotient projection.
  let q := singularChainsChangeCoefficients R X ≫
    (RResC).map (relativeSingularChainsProjection R A)
  have hzero : singularSubspaceChains ℤ A ≫ q = 0 := by
    have h := singularChainsChangeCoefficients_naturality R
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))
    change singularSubspaceChains ℤ A ≫ singularChainsChangeCoefficients R X =
      singularChainsChangeCoefficients R A ≫ (RResC).map (singularSubspaceChains R A) at h
    dsimp only [q]
    rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp]
    rw [show singularSubspaceChains R A ≫ relativeSingularChainsProjection R A = 0 from
      cokernel.condition (singularSubspaceChains R A), Functor.map_zero, comp_zero]
  -- Factor through the original integer cokernel and use its epimorphic projection for uniqueness.
  refine ⟨cokernel.desc (singularSubspaceChains ℤ A) q hzero, ?_, ?_⟩
  · exact cokernel.π_desc (singularSubspaceChains ℤ A) q hzero
  · intro F hF
    apply (cancel_epi (relativeSingularChainsProjection ℤ A)).mp
    exact hF.trans (cokernel.π_desc (singularSubspaceChains ℤ A) q hzero).symm

/-- The relative coefficient map, using the prescribed quotient square. -/
def relativeSingularChainsChangeCoefficients {X : Type u} [TopologicalSpace X]
    (A : Set X) :
    relativeSingularChains ℤ A ⟶ (RResC).obj (relativeSingularChains R A) :=
  Classical.choose (existsUnique_relativeSingularChainsChangeCoefficients R A).exists

/-- The canonical integer-linear coefficient map into the original target-ring homology. -/
def singularHomologyChangeCoefficients (X : Type u) [TopologicalSpace X] (n : ℕ) :
    singularHomology ℤ X n ⟶ (RRes).obj (singularHomology R X n) :=
  HomologicalComplex.homologyMap (singularChainsChangeCoefficients R X) n ≫
    (((singularChains R X).sc n).mapHomologyIso RRes).hom

/-- Relative coefficient change, with the canonical restriction-of-scalars comparison. -/
def relativeSingularHomologyChangeCoefficients {X : Type u} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    relativeSingularHomology ℤ A n ⟶ (RRes).obj (relativeSingularHomology R A n) :=
  HomologicalComplex.homologyMap (relativeSingularChainsChangeCoefficients R A) n ≫
    (((relativeSingularChains R A).sc n).mapHomologyIso RRes).hom

/-- Changing coefficients commutes with the specified original map of pairs. -/
theorem relativeSingularHomologyChangeCoefficients_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (n : ℕ)
    (c : relativeSingularHomology ℤ A n) :
    relativeSingularHomologyChangeCoefficients R B n
        (relativeSingularHomologyMap ℤ f hf n c) =
      relativeSingularHomologyMap R f hf n
        (relativeSingularHomologyChangeCoefficients R A n c) := by
  /- Stage 1: on a generator a·σ both composites are (a : R)·(f ∘ σ).
  Uniqueness of the coefficient chain maps gives the ordinary square.
  Stage 2: use the prescribed cokernel squares and their epimorphic
  projections to obtain the relative square for the same A, B and f.
  Stage 3: apply homology and the natural restriction-of-scalars
  comparison. Evaluating at c gives precisely the displayed equality. -/
  -- Compare the original pair maps after the original epimorphic quotient projection.
  let PZ := relativeSingularChainsMap ℤ f hf
  let PQ := relativeSingularChainsMap R f hf
  let FA := relativeSingularChainsChangeCoefficients R A
  let FB := relativeSingularChainsChangeCoefficients R B
  have hprojection (R : Type) [CommRing R] :
      relativeSingularChainsProjection R A ≫ relativeSingularChainsMap R f hf =
        (singularChainsFunctor R).map (TopCat.ofHom f) ≫
          relativeSingularChainsProjection R B := by
    simp [relativeSingularChainsProjection, relativeSingularChainsMap]
  have hFA : relativeSingularChainsProjection ℤ A ≫ FA =
      singularChainsChangeCoefficients R X ≫ (RResC).map (relativeSingularChainsProjection R A) :=
    Classical.choose_spec (existsUnique_relativeSingularChainsChangeCoefficients R A).exists
  have hFB : relativeSingularChainsProjection ℤ B ≫ FB =
      singularChainsChangeCoefficients R Y ≫ (RResC).map (relativeSingularChainsProjection R B) :=
    Classical.choose_spec (existsUnique_relativeSingularChainsChangeCoefficients R B).exists
  have hsquare : PZ ≫ FB = FA ≫ (RResC).map PQ := by
    apply (cancel_epi (relativeSingularChainsProjection ℤ A)).mp
    rw [← Category.assoc, hprojection ℤ, Category.assoc, hFB, ← Category.assoc,
      singularChainsChangeCoefficients_naturality R f, Category.assoc, ← Functor.map_comp,
      ← hprojection R,
      Functor.map_comp, ← Category.assoc, ← hFA, Category.assoc]
  -- Homology respects the square, and its native scalar-restriction comparison is natural.
  have hmap := congrArg (fun F ↦ HomologicalComplex.homologyMap F n) hsquare
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
  have hvalue := congrArg (fun F ↦ F c) hmap
  change HomologicalComplex.homologyMap FB n (HomologicalComplex.homologyMap PZ n c) =
    HomologicalComplex.homologyMap ((RResC).map PQ) n
      (HomologicalComplex.homologyMap FA n c) at hvalue
  have hnat := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.down ℕ) n).map PQ) RRes
  have hnatValue := congrArg (fun F ↦ F (HomologicalComplex.homologyMap FA n c)) hnat
  change (((relativeSingularChains R B).sc n).mapHomologyIso RRes).hom
    (HomologicalComplex.homologyMap ((RResC).map PQ) n
      (HomologicalComplex.homologyMap FA n c)) =
        relativeSingularHomologyMap R f hf n
          (relativeSingularHomologyChangeCoefficients R A n c) at hnatValue
  exact (congrArg (((relativeSingularChains R B).sc n).mapHomologyIso RRes).hom hvalue).trans
    hnatValue



end AtiyahSinger
