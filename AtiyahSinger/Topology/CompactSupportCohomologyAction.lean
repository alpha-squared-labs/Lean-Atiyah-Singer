/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyHomeomorph
public import AtiyahSinger.Topology.CompactSupportCohomologyRationalization
public import AtiyahSinger.Topology.RelativeCohomologyCup

/-!
# Ordinary cohomology acting on the original compact-support colimit

Public module ID: M1657.

D11. The ordinary-relative cup product at each original compact support K
is followed by that same support's colimit injection. Descending these
bilinear maps gives H^p(X;R) acting on H_c^q(X;R), with support retained
in the second factor. The data map is this actual colimit descent, not a
chosen operation specified only by algebraic laws.

Sources: Hatcher, Algebraic Topology, section 3.2, pp.209--210, for the
ordinary-relative product, and section 3.3, pp.242--245, for compact
supports. The stated support descent and its compatibility laws are the
standard assembly of these constructions. No separation, local compactness,
nonempty-space or positive-degree assumption is required. Naturality is
stated for the existing actual homeomorphism pullback; an arbitrary
continuous map need not preserve compact support.

The ordinary unit acts as identity. This does not give a unit in compactly
supported cohomology on a general noncompact space. Integer-to-rational
compatibility uses the original coefficient maps on the same supports,
without assuming that rational classes have integral lifts. Mathematical
proofs retain the original colimit, maps, support choices and cup order.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- Ordinary cohomology acts through the actual relative products and support colimit maps. -/
def compactSupportCohomologyAction (p q : ℕ) :
    singularCohomology R X p →ₗ[R] compactSupportCohomology R X q →ₗ[R]
      compactSupportCohomology R X (p + q) := by
  -- Flip each bilinear leg so the original compact-support colimit is its domain.
  let leg (K : Compacts X) : relativeSingularCohomology R ((K : Set X)ᶜ) q ⟶
      ModuleCat.of R (singularCohomology R X p →ₗ[R]
        compactSupportCohomology R X (p + q)) :=
    ModuleCat.ofHom (((relativeSingularCohomologyAction R ((K : Set X)ᶜ) p q).compr₂
      (compactSupportCohomologyClass R X K (p + q)).hom).flip)
  let descended : compactSupportCohomology R X q ⟶
      ModuleCat.of R (singularCohomology R X p →ₗ[R]
        compactSupportCohomology R X (p + q)) :=
    colimit.desc (compactSupportCohomologyFunctor R X q)
      { pt := ModuleCat.of R (singularCohomology R X p →ₗ[R]
          compactSupportCohomology R X (p + q))
        ι :=
          { app := leg
            naturality := by
              intro K L f
              apply ModuleCat.hom_ext
              apply LinearMap.ext
              intro b
              apply LinearMap.ext
              intro a
              -- The identity map of X gives exactly the original support transition.
              have hId : singularCohomologyPullback R (ContinuousMap.id X) p a = a := by
                change (singularCohomologyFunctor R p).map
                    (𝟙 (Opposite.op (TopCat.of X))) a = a
                rw [CategoryTheory.Functor.map_id]
                rfl
              have hAction := relativeSingularCohomologyPullback_action R
                (ContinuousMap.id X)
                (show Set.MapsTo (ContinuousMap.id X) ((L : Set X)ᶜ)
                    ((K : Set X)ᶜ) from
                  fun _ hx ↦ (Set.compl_subset_compl.mpr (leOfHom f)) hx) p q a b
              rw [hId] at hAction
              change compactSupportCohomologyClass R X L (p + q)
                  (relativeSingularCohomologyAction R ((L : Set X)ᶜ) p q a
                    ((compactSupportCohomologyFunctor R X q).map f b)) =
                compactSupportCohomologyClass R X K (p + q)
                  (relativeSingularCohomologyAction R ((K : Set X)ᶜ) p q a b)
              -- Relative naturality followed by the original cocone identifies the legs.
              exact (congrArg (compactSupportCohomologyClass R X L (p + q))
                hAction.symm).trans
                  (congrArg
                    (fun g ↦ g (relativeSingularCohomologyAction R ((K : Set X)ᶜ)
                      p q a b))
                    (colimit.w (compactSupportCohomologyFunctor R X (p + q)) f)) } }
  -- Restore the ordinary-first order while retaining both linear structures.
  exact descended.hom.flip

/-- The action retains the same compact support and the original relative cup representative. -/
theorem compactSupportCohomologyAction_representative (K : Compacts X) (p q : ℕ)
    (a : singularCohomology R X p)
    (b : relativeSingularCohomology R ((K : Set X)ᶜ) q) :
    compactSupportCohomologyAction R X p q a (compactSupportCohomologyClass R X K q b) =
      compactSupportCohomologyClass R X K (p + q)
        (relativeSingularCohomologyAction R ((K : Set X)ᶜ) p q a b) := by
  /- Evaluate the defining colimit descent on its original K-th
  injection, then evaluate the resulting linear map at a. The two
  flips restore the original ordinary-relative factor order. The
  target injection remains exactly K, not a chosen larger support. -/
  -- Give the defining cocone explicit types before evaluating its original leg.
  let leg (K : Compacts X) : relativeSingularCohomology R ((K : Set X)ᶜ) q ⟶
      ModuleCat.of R (singularCohomology R X p →ₗ[R]
        compactSupportCohomology R X (p + q)) :=
    ModuleCat.ofHom (((relativeSingularCohomologyAction R ((K : Set X)ᶜ) p q).compr₂
      (compactSupportCohomologyClass R X K (p + q)).hom).flip)
  let cocone : Cocone (compactSupportCohomologyFunctor R X q) :=
    { pt := ModuleCat.of R (singularCohomology R X p →ₗ[R]
        compactSupportCohomology R X (p + q))
      ι :=
        { app := leg
          naturality := by
            intro K L f
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro b
            apply LinearMap.ext
            intro a
            -- The identity map of X gives exactly the original support transition.
            have hId : singularCohomologyPullback R (ContinuousMap.id X) p a = a := by
              change (singularCohomologyFunctor R p).map
                  (𝟙 (Opposite.op (TopCat.of X))) a = a
              rw [CategoryTheory.Functor.map_id]
              rfl
            have hAction := relativeSingularCohomologyPullback_action R
              (ContinuousMap.id X)
              (show Set.MapsTo (ContinuousMap.id X) ((L : Set X)ᶜ)
                  ((K : Set X)ᶜ) from
                fun _ hx ↦ (Set.compl_subset_compl.mpr (leOfHom f)) hx) p q a b
            rw [hId] at hAction
            change compactSupportCohomologyClass R X L (p + q)
                (relativeSingularCohomologyAction R ((L : Set X)ᶜ) p q a
                  ((compactSupportCohomologyFunctor R X q).map f b)) =
              compactSupportCohomologyClass R X K (p + q)
                (relativeSingularCohomologyAction R ((K : Set X)ᶜ) p q a b)
            -- Relative naturality followed by the original cocone identifies the legs.
            exact (congrArg (compactSupportCohomologyClass R X L (p + q))
              hAction.symm).trans
                (congrArg
                  (fun g ↦ g (relativeSingularCohomologyAction R ((K : Set X)ᶜ)
                    p q a b))
                  (colimit.w (compactSupportCohomologyFunctor R X (p + q)) f)) } }
  have hleg := colimit.ι_desc cocone K
  -- Its value is the same relative action followed by the same support injection.
  exact congrArg (fun f ↦ f b a) hleg

/-- The original ordinary cup associates with its action on compactly supported classes. -/
theorem compactSupportCohomologyAction_assoc (p q r : ℕ)
    (a : singularCohomology R X p) (b : singularCohomology R X q)
    (c : compactSupportCohomology R X r) :
    (eqToIso (by rw [Nat.add_assoc]) :
        compactSupportCohomology R X ((p + q) + r) ≅
          compactSupportCohomology R X (p + (q + r))).hom
      (compactSupportCohomologyAction R X (p + q) r
        (singularCohomologyCup R X p q a b) c) =
    compactSupportCohomologyAction R X p (q + r) a
      (compactSupportCohomologyAction R X q r b c) := by
  /- Stage 1: represent c on one original compact support K. Both
  iterations retain K by the representative formula, so no support
  comparison or multiplication of arbitrary lifts is needed.
  Stage 2: apply relativeSingularCohomologyAction_assoc on that same
  pair and pass through its original colimit injection. The only
  transport is the displayed reassociation of p+q+r. -/
  -- Equality of degrees commutes with the same compact-support injection.
  have htransport (K : Compacts X) {i j : ℕ} (h : i = j)
      (d : relativeSingularCohomology R ((K : Set X)ᶜ) i) :
      (eqToIso (congrArg (fun k ↦ compactSupportCohomology R X k) h)).hom
          (compactSupportCohomologyClass R X K i d) =
        compactSupportCohomologyClass R X K j
          ((eqToIso (congrArg
            (fun k ↦ relativeSingularCohomology R ((K : Set X)ᶜ) k) h)).hom d) := by
    subst j
    rfl
  -- Both iterated actions retain the same representative and its original support.
  obtain ⟨K, γ, hγ⟩ := compactSupportCohomology_exists_representative R X r c
  rw [← hγ, compactSupportCohomologyAction_representative,
    compactSupportCohomologyAction_representative,
    compactSupportCohomologyAction_representative, htransport K (Nat.add_assoc p q r)]
  exact congrArg (compactSupportCohomologyClass R X K (p + (q + r)))
    (relativeSingularCohomologyAction_assoc R ((K : Set X)ᶜ) p q r a b γ)

/-- The ordinary constant-one class acts as identity on the original compact-support classes. -/
theorem compactSupportCohomologyAction_one (q : ℕ)
    (b : compactSupportCohomology R X q) :
    (eqToIso (by rw [Nat.zero_add]) :
        compactSupportCohomology R X (0 + q) ≅ compactSupportCohomology R X q).hom
      (compactSupportCohomologyAction R X 0 q (singularCohomologyOne R X) b) = b := by
  /- Choose an original relative representative at K. The ordinary
  constant-one class acts as identity on that very relative class by
  relativeSingularCohomologyAction_one. Its original injection gives
  the desired result, including q=0 and empty X. No compact-support
  unit class is introduced or assumed. -/
  -- Retain the original support while transporting the equality 0 + q = q.
  obtain ⟨K, β, hβ⟩ := compactSupportCohomology_exists_representative R X q b
  have htransport {i j : ℕ} (h : i = j)
      (d : relativeSingularCohomology R ((K : Set X)ᶜ) i) :
      (eqToIso (congrArg (fun k ↦ compactSupportCohomology R X k) h)).hom
          (compactSupportCohomologyClass R X K i d) =
        compactSupportCohomologyClass R X K j
          ((eqToIso (congrArg
            (fun k ↦ relativeSingularCohomology R ((K : Set X)ᶜ) k) h)).hom d) := by
    subst j
    rfl
  rw [← hβ, compactSupportCohomologyAction_representative, htransport (Nat.zero_add q)]
  -- Only the ordinary unit is used; no compact-support unit is introduced.
  exact congrArg (compactSupportCohomologyClass R X K q)
    (relativeSingularCohomologyAction_one R ((K : Set X)ᶜ) q β)

/-- Forgetting support sends the action to the original ordinary cup product. -/
theorem compactSupportCohomologyToOrdinary_action (p q : ℕ)
    (a : singularCohomology R X p) (b : compactSupportCohomology R X q) :
    compactSupportCohomologyToOrdinary R X (p + q)
        (compactSupportCohomologyAction R X p q a b) =
      singularCohomologyCup R X p q a (compactSupportCohomologyToOrdinary R X q b) := by
  /- Stage 1: evaluate both sides on an original K-relative
  representative. The forget-support cocone there is exactly the
  original relative-to-ordinary map.
  Stage 2: relativeSingularCohomologyToOrdinary_action identifies the
  values, retaining a and the same relative representative. Descent
  gives equality on Hc; no injectivity of forgetting support is used. -/
  -- The forget-support cocone is the original relative-to-ordinary map at each support.
  have hforget (K : Compacts X) (i : ℕ)
      (d : relativeSingularCohomology R ((K : Set X)ᶜ) i) :
      compactSupportCohomologyToOrdinary R X i (compactSupportCohomologyClass R X K i d) =
        relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) i d := by
    have hleg : compactSupportCohomologyClass R X K i ≫
        compactSupportCohomologyToOrdinary R X i =
          relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) i := colimit.ι_desc _ K
    exact congrArg (fun f ↦ f d) hleg
  obtain ⟨K, β, hβ⟩ := compactSupportCohomology_exists_representative R X q b
  rw [← hβ, compactSupportCohomologyAction_representative, hforget, hforget]
  -- Equality holds already on this representative; forgetting need not be injective.
  exact relativeSingularCohomologyToOrdinary_action R ((K : Set X)ᶜ) p q a β

variable {X}

/-- The existing pullback by the same homeomorphism preserves the ordinary-supported action. -/
theorem compactSupportCohomologyHomeomorphPullback_action
    {Y : Type u} [TopologicalSpace Y] (e : X ≃ₜ Y) (p q : ℕ)
    (a : singularCohomology R Y p) (b : compactSupportCohomology R Y q) :
    compactSupportCohomologyHomeomorphPullback R e (p + q)
        (compactSupportCohomologyAction R Y p q a b) =
      compactSupportCohomologyAction R X p q
        (singularCohomologyPullback R ⟨e, e.continuous⟩ p a)
        (compactSupportCohomologyHomeomorphPullback R e q b) := by
  /- Stage 1: represent b at K. The existing homeomorphism pullback
  uses the exact inverse-image support homeomorphCompactPreimage e K
  and the relative pullback along e, not an arbitrary equivalence.
  Stage 2: relativeSingularCohomologyPullback_action on these same
  complement pairs identifies the products. The original injections
  and representative formulas give the stated colimit equality. -/
  -- Pull back the same representative to the exact inverse-image compact support.
  obtain ⟨K, β, hβ⟩ := compactSupportCohomology_exists_representative R Y q b
  let L := homeomorphCompactPreimage e K
  let f : C(X, Y) := ⟨e, e.continuous⟩
  have hf : Set.MapsTo f ((L : Set X)ᶜ) ((K : Set Y)ᶜ) := fun _ hx ↦ hx
  have hleg (i : ℕ) (d : relativeSingularCohomology R ((K : Set Y)ᶜ) i) :
      homeomorphCompactSupportCohomologyLeg R e K i d =
        compactSupportCohomologyClass R X L i
          (relativeSingularCohomologyPullback R f hf i d) := rfl
  rw [← hβ, compactSupportCohomologyAction_representative,
    compactSupportCohomologyHomeomorphPullback_representative,
    compactSupportCohomologyHomeomorphPullback_representative, hleg, hleg,
    compactSupportCohomologyAction_representative]
  exact congrArg (compactSupportCohomologyClass R X L (p + q))
    (relativeSingularCohomologyPullback_action R f hf p q a β)

/-- The actual integer-to-rational coefficient maps preserve the ordinary-supported action. -/
theorem compactSupportCohomologyRationalization_action (X : Type u) [TopologicalSpace X]
    (p q : ℕ) (a : singularCohomology ℤ X p) (b : compactSupportCohomology ℤ X q) :
    compactSupportCohomologyRationalization X (p + q)
        (compactSupportCohomologyAction ℤ X p q a b) =
      compactSupportCohomologyAction ℚ X p q (singularCohomologyRationalization X p a)
        (compactSupportCohomologyRationalization X q b) := by
  /- Stage 1: retain an original integral representative for b at K.
  The compact-support coefficient map keeps this same K and uses the
  original relative coefficient map.
  Stage 2: the relative action is the original cochain coefficient
  product, and the ring map Z -> Q preserves that multiplication.
  Its existing relative-action compatibility and both representative
  formulas give the equality after the same rational K injection.
  No tensor-cohomology isomorphism or integral lift of a rational
  class is asserted. The claim quantifies exactly the integral inputs. -/
  -- Change coefficients on the same integral representative and compact support.
  obtain ⟨K, β, hβ⟩ := compactSupportCohomology_exists_representative ℤ X q b
  rw [← hβ, compactSupportCohomologyAction_representative,
    compactSupportCohomologyRationalization_representative,
    compactSupportCohomologyRationalization_representative]
  -- The original relative product preserves the ordinary-first factor order.
  exact (congrArg (compactSupportCohomologyClass ℚ X K (p + q))
    (relativeSingularCohomologyRationalization_action ((K : Set X)ᶜ) p q a β)).trans
      (compactSupportCohomologyAction_representative ℚ X K p q
        (singularCohomologyRationalization X p a)
        (relativeSingularCohomologyRationalization ((K : Set X)ᶜ) q β)).symm

end AtiyahSinger
