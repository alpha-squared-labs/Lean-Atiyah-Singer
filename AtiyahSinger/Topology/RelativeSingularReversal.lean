/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularCohomology
public import AtiyahSinger.Topology.SingularReversal
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Signed reversal on the original relative singular chains

Public module ID: M2094.

Naturality of signed reversal and its specified cone homotopy along the actual
subspace inclusion allows both to descend through the original chain cokernel.
The quotient projection intertwines the absolute and relative operators and
every component of the same homotopy. No closedness hypothesis, replacement
quotient model, or injectivity of the cohomology forgetful map is used.

This is the relative version of the standard reversal argument for graded
commutativity of singular cup products.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X] (A : Set X)

/-- Signed reversal descends along the actual subspace-chain inclusion. -/
def relativeSingularReversal : relativeSingularChains R A ⟶ relativeSingularChains R A :=
  cokernel.map (singularSubspaceChains R A) (singularSubspaceChains R A)
    (singularReversal R A) (singularReversal R X)
    (singularReversal_naturality R (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))

/-- Projection to the relative quotient commutes with the same signed reversal. -/
theorem relativeSingularChainsProjection_reversal :
    relativeSingularChainsProjection R A ≫ relativeSingularReversal R A =
      singularReversal R X ≫ relativeSingularChainsProjection R A := by
  simp [relativeSingularReversal, relativeSingularChainsProjection]

/-- The original cone homotopy descends degreewise through the same subspace quotient. -/
def relativeSingularReversalHomotopyComponent (n m : ℕ) :
    (relativeSingularChains R A).X n ⟶ (relativeSingularChains R A).X m :=
  (CokernelCofork.IsColimit.desc'
    (isColimitOfHasCokernelOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
      (singularSubspaceChains R A))
    ((singularReversalHomotopy R X).hom n m ≫ (relativeSingularChainsProjection R A).f m)
    (by
      -- Naturality keeps the very same subspace chain inside the same subspace after homotopy.
      have hnat := singularReversalHomotopy_naturality R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) n m
      change (singularSubspaceChains R A).f n ≫
        ((singularReversalHomotopy R X).hom n m ≫
          (relativeSingularChainsProjection R A).f m) = 0
      change (singularSubspaceChains R A).f n ≫ (singularReversalHomotopy R X).hom n m =
        (singularReversalHomotopy R A).hom n m ≫ (singularSubspaceChains R A).f m at hnat
      rw [← Category.assoc, hnat, Category.assoc]
      have hz : (singularSubspaceChains R A).f m ≫
          (relativeSingularChainsProjection R A).f m = 0 :=
        congrArg (fun f ↦ f.f m) (cokernel.condition (singularSubspaceChains R A))
      rw [hz, comp_zero])).val

/-- Each descended homotopy component is characterized by the original quotient projection. -/
theorem relativeSingularChainsProjection_reversalHomotopyComponent (n m : ℕ) :
    (relativeSingularChainsProjection R A).f n ≫
        relativeSingularReversalHomotopyComponent R A n m =
      (singularReversalHomotopy R X).hom n m ≫
        (relativeSingularChainsProjection R A).f m := by
  exact (CokernelCofork.IsColimit.desc'
    (isColimitOfHasCokernelOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
      (singularSubspaceChains R A)) _ _).property

/-- The specified singular reversal homotopy descends to the actual relative chain complex. -/
def relativeSingularReversalHomotopy :
    Homotopy (𝟙 (relativeSingularChains R A)) (relativeSingularReversal R A) where
  hom := relativeSingularReversalHomotopyComponent R A
  zero n m hnm := by
    have : Epi ((relativeSingularChainsProjection R A).f n) :=
      epi_of_isColimit_cofork (isColimitOfHasCokernelOfPreservesColimit
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
        (singularSubspaceChains R A))
    apply (cancel_epi ((relativeSingularChainsProjection R A).f n)).mp
    rw [relativeSingularChainsProjection_reversalHomotopyComponent,
      (singularReversalHomotopy R X).zero n m hnm, zero_comp, comp_zero]
  comm n := by
    let q := relativeSingularChainsProjection R A
    let T := relativeSingularReversalHomotopyComponent R A
    -- The absolute homotopy equation is transported through the same epimorphic projection.
    have hnull : Homotopy.nullHomotopicMap (singularReversalHomotopy R X).hom =
        𝟙 (singularChains R X) - singularReversal R X := by
      ext m : 1
      have hm := (singularReversalHomotopy R X).comm m
      change 𝟙 ((singularChains R X).X m) =
        (Homotopy.nullHomotopicMap (singularReversalHomotopy R X).hom).f m +
          (singularReversal R X).f m at hm
      exact eq_sub_iff_add_eq.mpr hm.symm
    have hnullT : Homotopy.nullHomotopicMap T =
        𝟙 (relativeSingularChains R A) - relativeSingularReversal R A := by
      apply (cancel_epi q).mp
      rw [Homotopy.comp_nullHomotopicMap]
      have hfamily : (fun i j ↦ q.f i ≫ T i j) =
          (fun i j ↦ (singularReversalHomotopy R X).hom i j ≫ q.f j) :=
        funext fun i ↦ funext fun j ↦
          relativeSingularChainsProjection_reversalHomotopyComponent R A i j
      rw [hfamily, ← Homotopy.nullHomotopicMap_comp, hnull,
        Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id]
      rw [relativeSingularChainsProjection_reversal]
    have hn := congrArg (fun f ↦ f.f n) hnullT
    change (Homotopy.nullHomotopicMap T).f n =
      𝟙 ((relativeSingularChains R A).X n) - (relativeSingularReversal R A).f n at hn
    change 𝟙 ((relativeSingularChains R A).X n) =
      (Homotopy.nullHomotopicMap T).f n + (relativeSingularReversal R A).f n
    exact (eq_sub_iff_add_eq.mp hn).symm

/-- Quotient projection intertwines every component of the absolute and relative homotopies. -/
theorem relativeSingularChainsProjection_reversalHomotopy (n m : ℕ) :
    (relativeSingularChainsProjection R A).f n ≫
        (relativeSingularReversalHomotopy R A).hom n m =
      (singularReversalHomotopy R X).hom n m ≫
        (relativeSingularChainsProjection R A).f m :=
  relativeSingularChainsProjection_reversalHomotopyComponent R A n m

end AtiyahSinger
