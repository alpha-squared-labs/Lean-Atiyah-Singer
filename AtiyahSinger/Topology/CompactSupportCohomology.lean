/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularCohomology
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
public import Mathlib.Topology.Sets.Compacts

/-!
# Compactly supported singular cohomology

Public module ID: M1656.

D11: Hatcher section 3.3, printed pp.242--245, defines H_c^n(X;R) as
the directed colimit of H^n(X,X\K;R) over compact subsets K. This module
uses precisely those relative singular cochain complexes and their
original restriction maps. The ordinary target is the same singular
cohomology constructed from the original free singular chains.

Neither separation nor local compactness is needed for this colimit
definition. The compact-space comparison requires only CompactSpace.
No arbitrary continuous-map pullback on compact supports is asserted;
proper pullbacks, open extensions, cup products and locally finite
fundamental-class pairings are developed in their respective modules.

The integral construction recorded as PR13 uses the same standard
filtered-colimit model. This implementation uses mathlib's
filtered colimits and the variable-coefficient relative complex.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- Complementing compact supports gives the actual reversed inclusion diagram of subspaces. -/
def compactSupportComplementFunctor : Compacts X ⥤ (Set X)ᵒᵖ where
  obj K := op ((K : Set X)ᶜ)
  map f := (homOfLE (Set.compl_subset_compl.mpr (leOfHom f))).op

/-- The directed diagram K ↦ H^n(X,X\K;R) with its original relative restriction maps. -/
def compactSupportCohomologyFunctor (n : ℕ) : Compacts X ⥤ ModuleCat.{u} R :=
  compactSupportComplementFunctor X ⋙ relativeSingularCohomologyFunctor R X n

/-- Compactly supported singular cohomology, with the standard filtered-colimit definition. -/
abbrev compactSupportCohomology (n : ℕ) : ModuleCat.{u} R :=
  colimit (compactSupportCohomologyFunctor R X n)

/-- The original compact-support representative map from H^n(X,X\K;R). -/
def compactSupportCohomologyClass (K : Compacts X) (n : ℕ) :
    relativeSingularCohomology R ((K : Set X)ᶜ) n ⟶ compactSupportCohomology R X n :=
  colimit.ι (compactSupportCohomologyFunctor R X n) K

/-- Forgetting compact support uses the same canonical relative-to-ordinary cohomology maps. -/
def compactSupportCohomologyToOrdinary (n : ℕ) :
    compactSupportCohomology R X n ⟶ singularCohomology R X n :=
  colimit.desc (compactSupportCohomologyFunctor R X n)
    { pt := singularCohomology R X n
      ι := Functor.whiskerLeft (compactSupportComplementFunctor X)
        (relativeSingularCohomologyToOrdinaryNatTrans R X n) }

/-- Every compactly supported class has a representative supported in some compact set. -/
theorem compactSupportCohomology_exists_representative (n : ℕ)
    (a : compactSupportCohomology R X n) :
    ∃ (K : Compacts X) (b : relativeSingularCohomology R ((K : Set X)ᶜ) n),
      compactSupportCohomologyClass R X K n b = a := by
  /- Stage 1: finite unions and the empty compact set make Compacts X
  a filtered category. The forgetful functor from R-modules preserves
  this filtered colimit.
  Stage 2: in the underlying type colimit every element comes from
  one component. Transport that representative through the canonical
  comparison with our categorical colimit. The resulting map is the
  same colimit injection used in compactSupportCohomologyClass. -/
  -- The underlying module colimit is the same filtered colimit of types.
  let F := compactSupportCohomologyFunctor R X n
  -- Use the native colimit construction at the original space universe.
  have : PreservesColimit F (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
    preservesColimit_of_preserves_colimit_cocone
      (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
      (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _))
  have : PreservesColimit F (forget (ModuleCat.{u} R)) :=
    comp_preservesColimit (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      (forget AddCommGrpCat.{u})
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (ModuleCat.{u} R)) (colimit.isColimit F)) a

/-- Equality of compact-support representatives is detected at one common larger compact set. -/
theorem compactSupportCohomologyClass_eq_iff {n : ℕ} {K L : Compacts X}
    (a : relativeSingularCohomology R ((K : Set X)ᶜ) n)
    (b : relativeSingularCohomology R ((L : Set X)ᶜ) n) :
    compactSupportCohomologyClass R X K n a = compactSupportCohomologyClass R X L n b ↔
      ∃ (P : Compacts X) (hK : K ≤ P) (hL : L ≤ P),
        (compactSupportCohomologyFunctor R X n).map (homOfLE hK) a =
          (compactSupportCohomologyFunctor R X n).map (homOfLE hL) b := by
  /- Stage 1: use preservation of filtered colimits by the module
  forgetful functor to express both classes in the same type colimit.
  Stage 2: the filtered-colimit equivalence relation identifies two
  representatives exactly when they agree after maps to a common
  object. Translate those maps back into inclusions of compact sets.
  Conversely the cocone identity identifies any such common images.
  This criterion uses equality in relative cohomology, not equality
  of arbitrarily chosen cochains or representatives of cocycles. -/
  -- Use the equality relation of the preserved filtered colimit on the actual injections.
  let F := compactSupportCohomologyFunctor R X n
  -- Use the native colimit construction at the original space universe.
  have : PreservesColimit F (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
    preservesColimit_of_preserves_colimit_cocone
      (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
      (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _))
  have : PreservesColimit F (forget (ModuleCat.{u} R)) :=
    comp_preservesColimit (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      (forget AddCommGrpCat.{u})
  have h := Types.FilteredColimit.isColimit_eq_iff (F ⋙ forget (ModuleCat.{u} R))
    (isColimitOfPreserves (forget (ModuleCat.{u} R)) (colimit.isColimit F))
      (xi := a) (xj := b)
  constructor
  · intro hab
    obtain ⟨P, f, g, hfg⟩ := h.mp hab
    exact ⟨P, leOfHom f, leOfHom g, hfg⟩
  · rintro ⟨P, hK, hL, hab⟩
    exact h.mpr ⟨P, homOfLE hK, homOfLE hL, hab⟩

/-- On a compact space the canonical map forgetting supports is an isomorphism. -/
theorem isIso_compactSupportCohomologyToOrdinary [CompactSpace X] (n : ℕ) :
    IsIso (compactSupportCohomologyToOrdinary R X n) := by
  /- Stage 1: the full compact space is the terminal support, so the
  directed colimit is canonically H^n(X,X\X;R)=H^n(X,∅;R).
  Stage 2: the canonical empty-relative map is an isomorphism because
  the empty subspace has zero singular chains. Its composite with
  the terminal-support comparison is exactly the original cocone map
  compactSupportCohomologyToOrdinary. No Hausdorff or manifold
  condition is used. -/
  -- The original injection at the terminal compact support is an isomorphism.
  let F := compactSupportCohomologyFunctor R X n
  have : IsIso (colimit.ι F (⊤ : Compacts X)) := isIso_ι_of_isTerminal isTerminalTop F
  have hEmpty : IsIso
      (relativeSingularCohomologyToOrdinary R ((⊤ : Compacts X) : Set X)ᶜ n) := by
    have hset : ((⊤ : Compacts X) : Set X)ᶜ = ∅ := Set.compl_univ
    rw [hset]
    exact isIso_relativeSingularCohomologyToOrdinary_empty R X n
  -- The given forget-support map composes with that injection to the empty-pair comparison.
  have hleg : colimit.ι F (⊤ : Compacts X) ≫
      compactSupportCohomologyToOrdinary R X n =
        relativeSingularCohomologyToOrdinary R ((⊤ : Compacts X) : Set X)ᶜ n := by
    exact colimit.ι_desc _ _
  have : IsIso (colimit.ι F (⊤ : Compacts X) ≫
      compactSupportCohomologyToOrdinary R X n) := by
    rw [hleg]
    exact hEmpty
  exact IsIso.of_isIso_comp_left (colimit.ι F (⊤ : Compacts X))
    (compactSupportCohomologyToOrdinary R X n)

/-- The compact-space comparison, using the original canonical map that forgets support. -/
def compactSupportCohomologyIso [CompactSpace X] (n : ℕ) :
    compactSupportCohomology R X n ≅ singularCohomology R X n := by
  letI := isIso_compactSupportCohomologyToOrdinary R X n
  exact asIso (compactSupportCohomologyToOrdinary R X n)

end AtiyahSinger
