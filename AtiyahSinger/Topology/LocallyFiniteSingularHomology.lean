/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.LocallyFiniteSingularChains

/-!
# Locally finite homology, compact-relative restriction and rationalization

Public module ID: M1953.

Locally finite singular homology is the actual homology of the original
locally finite coefficient complex. Restriction at each compact subset is
induced by its specified finite truncation and the original relative chain
quotient. The support inclusion law retains those same maps and complements.

Integer-to-rational coefficient change is the pointwise map on the very same
singular simplices. It preserves the actual local-finiteness condition and
commutes with the finite alternating-face boundary. Restriction of scalars
and the canonical homology comparison only express this map in ModuleCat.
The compact-relative comparison commutes with the original rationalization
of relative singular homology, without a change of orientation or scale.

Sources: the standard locally finite singular-chain construction of
Borel--Moore homology; Hatcher, Algebraic Topology, sections 2.1 and 3.3,
for singular coefficients and compact-relative homology. The explicit
comparisons on these existing chain objects are project supplements.
No identification with an inverse limit of relative homology groups, no
fundamental class, and no duality theorem is asserted merely by these
definitions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite TopologicalSpace
open scoped Simplicial

universe u

variable (R : Type) [CommRing R]

/-- Locally finite singular homology, computed from the actual locally finite chain complex. -/
abbrev locallyFiniteSingularHomology (X : Type u) [TopologicalSpace X] (n : ℕ) :
    ModuleCat.{u} R :=
  (locallyFiniteSingularChains R X).homology n

/-- Restriction to the original compact-relative homology is induced by the actual chain map. -/
def locallyFiniteSingularHomologyRestriction {X : Type u} [TopologicalSpace X]
    (K : Compacts X) (n : ℕ) :
    locallyFiniteSingularHomology R X n ⟶
      relativeSingularHomology R ((K : Set X)ᶜ) n :=
  HomologicalComplex.homologyMap (locallyFiniteSingularChainsRestriction R X K) n

/-- The original complement inclusion makes restrictions at two compact controls commute. -/
theorem locallyFiniteSingularHomologyRestriction_inclusion
    {X : Type u} [TopologicalSpace X] {K L : Compacts X} (h : K ≤ L) (n : ℕ) :
    locallyFiniteSingularHomologyRestriction R L n ≫
        relativeSingularHomologyInclusion R ((L : Set X)ᶜ) ((K : Set X)ᶜ)
          (Set.compl_subset_compl.mpr h) n =
      locallyFiniteSingularHomologyRestriction R K n := by
  /- Apply the original degree-n homology functor to
  locallyFiniteSingularChainsRestriction_inclusion. Its map of the displayed
  pair inclusion is exactly relativeSingularHomologyInclusion by definition.
  The two homology restrictions therefore preserve the same compact sets
  and original finite-truncation quotient maps. -/
  -- Apply the actual homology functor to the original chain-map square.
  change HomologicalComplex.homologyMap (locallyFiniteSingularChainsRestriction R X L) n ≫
      HomologicalComplex.homologyMap
        (relativeSingularChainsMap R (ContinuousMap.id X)
          (show Set.MapsTo (ContinuousMap.id X) ((L : Set X)ᶜ) ((K : Set X)ᶜ)
            from fun _ hx ↦ (Set.compl_subset_compl.mpr h) hx)) n =
    HomologicalComplex.homologyMap (locallyFiniteSingularChainsRestriction R X K) n
  rw [← HomologicalComplex.homologyMap_comp,
    locallyFiniteSingularChainsRestriction_inclusion R X h]

section RationalCoefficients

variable (X : Type u) [TopologicalSpace X]

local notation "S" => TopCat.toSSet.obj (TopCat.of X)
local notation "ℚRes" => ModuleCat.restrictScalars (Int.castRingHom ℚ)
local notation "ℚResC" => Functor.mapHomologicalComplex
  (ModuleCat.restrictScalars (Int.castRingHom ℚ)) (ComplexShape.down ℕ)

/-- Pointwise integer inclusion preserves the original locally finite simplex-image family. -/
theorem isLocallyFiniteSingularChain_intCast (n : ℕ)
    (c : locallyFiniteSingularChainModule ℤ X n) :
    IsLocallyFiniteSingularChain ℚ X n (fun σ ↦ (c.val σ : ℚ)) := by
  /- A nonzero rational image has a nonzero original integer coefficient.
  The new active simplex-image family is therefore a subfamily of the
  original locally finite family. Keep the original neighborhoods and
  finite active controls; the simplex maps and their images do not change. -/
  -- Keep the original neighborhood and restrict its finite active family.
  intro x
  obtain ⟨U, hU, hfinite⟩ := c.property x
  refine ⟨U, hU, ((hfinite.image Subtype.val).preimage
    Subtype.val_injective.injOn).subset ?_⟩
  intro σ hσ
  have hc : c.val σ.val ≠ 0 := by
    intro hzero
    exact σ.property (by simp [hzero])
  exact ⟨⟨σ.val, hc⟩, hσ, rfl⟩

/-- The actual pointwise coefficient inclusion on the original locally finite chain modules. -/
def locallyFiniteSingularChainRationalization (n : ℕ) :
    (locallyFiniteSingularChains ℤ X).X n ⟶
      (ℚRes).obj ((locallyFiniteSingularChains ℚ X).X n) :=
  ModuleCat.ofHom
    { toFun := fun c ↦ ⟨fun σ ↦ (c.val σ : ℚ),
        isLocallyFiniteSingularChain_intCast X n c⟩
      map_add' := by
        intro c d
        apply Subtype.ext
        funext σ
        change ((c.val σ + d.val σ : ℤ) : ℚ) = (c.val σ : ℚ) + (d.val σ : ℚ)
        exact Int.cast_add _ _
      map_smul' := by
        intro a c
        apply Subtype.ext
        funext σ
        change ((a * c.val σ : ℤ) : ℚ) = (a : ℚ) * (c.val σ : ℚ)
        exact Int.cast_mul _ _ }

/-- The actual coefficient inclusion commutes with the original locally finite boundary. -/
theorem locallyFiniteSingularChainRationalization_comm (i j : ℕ) :
    locallyFiniteSingularChainRationalization X i ≫
        (ℚRes).map ((locallyFiniteSingularChains ℚ X).d i j) =
      (locallyFiniteSingularChains ℤ X).d i j ≫
        locallyFiniteSingularChainRationalization X j := by
  /- In adjacent degrees, each original face coefficient is a finite sum
  by the actual local-finiteness certificate. Integer inclusion preserves
  these finite sums, multiplication and the fixed alternating signs.
  Hence the two composites agree on every original simplex coefficient.
  In all other degrees both original differentials are zero. Restriction
  of scalars changes only the scalar action, not coefficients or faces. -/
  classical
  -- Adjacent degrees reduce to the original finite alternating face sums.
  by_cases hij : j + 1 = i
  · subst i
    simp only [locallyFiniteSingularChains, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    funext τ
    change (∑ i : Fin (j + 2), ∑ᶠ σ : (S).obj (op ⦋j + 1⦌),
      if (S).map (SimplexCategory.δ i).op σ = τ then
        (-1 : ℚ) ^ i.val * (c.val σ : ℚ) else 0) =
      ((∑ i : Fin (j + 2), ∑ᶠ σ : (S).obj (op ⦋j + 1⦌),
        if (S).map (SimplexCategory.δ i).op σ = τ then
          (-1 : ℤ) ^ i.val * c.val σ else 0 : ℤ) : ℚ)
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    -- Each face fiber has finite support, so coefficient change commutes with its sum.
    have hfinite := locallyFiniteSingularBoundaryFunction_finite_support ℤ X j c i τ
    rw [show (↑(∑ᶠ σ : (S).obj (op ⦋j + 1⦌),
        if (S).map (SimplexCategory.δ i).op σ = τ then
          (-1 : ℤ) ^ i.val * c.val σ else 0) : ℚ) =
      ∑ᶠ σ : (S).obj (op ⦋j + 1⦌),
        ((if (S).map (SimplexCategory.δ i).op σ = τ then
          (-1 : ℤ) ^ i.val * c.val σ else 0 : ℤ) : ℚ) from
      map_finsum (Int.castAddHom ℚ) hfinite]
    congr 1
    funext σ
    split_ifs <;> simp
  -- The original complex shape makes both other differentials zero.
  · have hshape : ¬ (ComplexShape.down ℕ).Rel i j := hij
    rw [(locallyFiniteSingularChains ℚ X).shape i j hshape,
      (locallyFiniteSingularChains ℤ X).shape i j hshape, Functor.map_zero]
    exact Eq.trans Limits.comp_zero (Eq.symm Limits.zero_comp)

/-- The actual same-simplex integer-to-rational chain map for locally finite chains. -/
def locallyFiniteSingularChainsRationalization :
    locallyFiniteSingularChains ℤ X ⟶ (ℚResC).obj (locallyFiniteSingularChains ℚ X) where
  f n := locallyFiniteSingularChainRationalization X n
  comm' i j _ := locallyFiniteSingularChainRationalization_comm X i j

/-- The coefficient map on locally finite homology, with its scalar-restriction comparison. -/
def locallyFiniteSingularHomologyRationalization (n : ℕ) :
    locallyFiniteSingularHomology ℤ X n ⟶
      (ℚRes).obj (locallyFiniteSingularHomology ℚ X n) :=
  HomologicalComplex.homologyMap (locallyFiniteSingularChainsRationalization X) n ≫
    (((locallyFiniteSingularChains ℚ X).sc n).mapHomologyIso ℚRes).hom

/-- The same compact-relative restriction commutes with the original coefficient inclusion. -/
theorem locallyFiniteSingularHomologyRationalization_restriction
    (K : Compacts X) (n : ℕ) (c : locallyFiniteSingularHomology ℤ X n) :
    relativeSingularHomologyRationalization ((K : Set X)ᶜ) n
        (locallyFiniteSingularHomologyRestriction ℤ K n c) =
      locallyFiniteSingularHomologyRestriction ℚ K n
        (locallyFiniteSingularHomologyRationalization X n c) := by
  /- Stage 1: on the same finite set of active original simplices meeting K,
  restriction forms the sum of their original relative generator images.
  Pointwise integer inclusion gives exactly the same rational sum. The
  prescribed generator and cokernel formulas for the existing relative
  rationalization therefore identify both composites at chain level.
  Stage 2: apply homology and the natural scalar-restriction homology
  comparison. Its source and target are precisely the actual original
  rational complexes. Evaluating this square at c gives the assertion,
  without replacing its compact support or rescaling any local generator. -/
  classical
  -- Use the prescribed chain maps and their original quotient square.
  let IZ := locallyFiniteSingularChainsRestriction ℤ X K
  let IQ := locallyFiniteSingularChainsRestriction ℚ X K
  let LF := locallyFiniteSingularChainsRationalization X
  let RF := relativeSingularChainsRationalization ((K : Set X)ᶜ)
  have hprojection : relativeSingularChainsProjection ℤ ((K : Set X)ᶜ) ≫ RF =
      singularChainsRationalization X ≫
        (ℚResC).map (relativeSingularChainsProjection ℚ ((K : Set X)ᶜ)) :=
    Classical.choose_spec
      (existsUnique_relativeSingularChainsRationalization ((K : Set X)ᶜ)).exists
  -- First identify coefficient change on each original relative simplex generator.
  let generator (R : Type) [CommRing R] (k : ℕ) (σ : (S).obj (op ⦋k⦌)) :
      R →ₗ[R] (relativeSingularChains R ((K : Set X)ᶜ)).X k :=
    ((relativeSingularChainsProjection R ((K : Set X)ᶜ)).f k).hom.comp
      (((S).ιChainComplex (R := singularCoefficient R) σ).hom.comp
        (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).symm.toLinearMap)
  have hgen (k : ℕ) (σ : (S).obj (op ⦋k⦌)) (a : ℤ) :
      RF.f k (generator ℤ k σ a) = generator ℚ k σ (a : ℚ) := by
    have h := congrArg (fun f ↦ f.f k
      ((S).ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up a))) hprojection
    have heval :=
      Classical.choose_spec (existsUnique_singularChainsRationalization X).exists k σ a
    change RF.f k (generator ℤ k σ a) =
      (relativeSingularChainsProjection ℚ ((K : Set X)ᶜ)).f k
        ((singularChainsRationalization X).f k
          ((S).ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up a))) at h
    exact h.trans (congrArg
      ((relativeSingularChainsProjection ℚ ((K : Set X)ᶜ)).f k) heval)
  -- Local finiteness on K makes the restriction a finite sum of those generators.
  have hsquare : IZ ≫ RF = LF ≫ (ℚResC).map IQ := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    let term (σ : (S).obj (op ⦋k⦌)) :
        (relativeSingularChains ℤ ((K : Set X)ᶜ)).X k :=
      if (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ) ∩
          (K : Set X)).Nonempty then generator ℤ k σ (z.val σ) else 0
    have hfinite : (Function.support term).Finite := by
      apply (locallyFiniteSingularChainModule_finite_meeting ℤ X K k z).subset
      intro σ hσ
      change term σ ≠ 0 at hσ
      simp only [term] at hσ
      split_ifs at hσ with hmeet
      · refine ⟨?_, hmeet⟩
        intro hz0
        simp [hz0] at hσ
      · exact (hσ rfl).elim
    change RF.f k (∑ᶠ σ, term σ) =
      ∑ᶠ σ : (S).obj (op ⦋k⦌),
        if (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ) ∩
            (K : Set X)).Nonempty then generator ℚ k σ (z.val σ : ℚ) else 0
    rw [map_finsum _ hfinite]
    congr 1
    funext σ
    simp only [term]
    split_ifs
    · exact hgen k σ (z.val σ)
    · exact map_zero _
  -- Apply homology, then its canonical restriction-of-scalars comparison.
  have hmap := congrArg (fun F ↦ HomologicalComplex.homologyMap F n) hsquare
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
  have hvalue := congrArg (fun F ↦ F c) hmap
  change HomologicalComplex.homologyMap RF n (HomologicalComplex.homologyMap IZ n c) =
    HomologicalComplex.homologyMap ((ℚResC).map IQ) n
      (HomologicalComplex.homologyMap LF n c) at hvalue
  have hnat := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℚ)
      (ComplexShape.down ℕ) n).map IQ) ℚRes
  have hnatValue := congrArg (fun F ↦ F (HomologicalComplex.homologyMap LF n c)) hnat
  change (((relativeSingularChains ℚ ((K : Set X)ᶜ)).sc n).mapHomologyIso ℚRes).hom
    (HomologicalComplex.homologyMap ((ℚResC).map IQ) n
      (HomologicalComplex.homologyMap LF n c)) =
      locallyFiniteSingularHomologyRestriction ℚ K n
        (locallyFiniteSingularHomologyRationalization X n c) at hnatValue
  exact (congrArg (((relativeSingularChains ℚ ((K : Set X)ᶜ)).sc n).mapHomologyIso ℚRes).hom
    hvalue).trans hnatValue

end RationalCoefficients

end AtiyahSinger
