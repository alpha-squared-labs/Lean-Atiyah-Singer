/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportFunctoriality
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Compactly supported K-theory in nonpositive degrees

Public module ID: M2222.

The standard suspension definition realizes Kc^{-n}(X) as Kc⁰(X × ℝⁿ), using
the actual coordinate space `Fin n → ℝ`. The parameter n is the number of real
suspensions and denotes degree -n. This does not identify all degrees with Kc⁰(X)
or assume a periodicity theorem in order to define the groups.

Proper pullback is the existing degree-zero pullback along f × id. The degree-zero
comparison is the existing homeomorphism transport along X × ℝ⁰ → X; its inverse
inserts the unique empty coordinate tuple. Thus these constructions retain both
the original compact-support groups and the specified coordinate maps.

Sources: Lawson--Michelsohn, Spin Geometry, I.9; Karoubi, K-Theory, II.4,
the suspension definition of negative K-groups. This module gives their proper
functoriality and the degree-zero comparison. It does not assert a long exact
sequence, suspension compatibility of boundary maps, or a Thom isomorphism.
The proofs retain these original product maps and the empty-coordinate comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- Compactly supported K^{-n}(X), defined by n actual real suspension coordinates. -/
abbrev CompactSupportK (n : ℕ) (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] : Type _ :=
  CompactSupportKZero (X × (Fin n → ℝ))

variable {X Y Z : Type*}
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]

/-- Proper pullback in degree -n uses the same map on X and the identity on ℝⁿ. -/
def compactSupportKPullback (n : ℕ) (f : C(X, Y)) (hf : IsProperMap f) :
    CompactSupportK n Y →+ CompactSupportK n X :=
  compactSupportKZeroPullback (f.prodMap (ContinuousMap.id (Fin n → ℝ)))
    (hf.prodMap isProperMap_id)

/-- The specified coordinate comparison Kc^{-0}(X) ≃ Kc⁰(X), without a Bott choice. -/
def compactSupportKZeroDegreeEquiv (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] :
    CompactSupportK 0 X ≃+ CompactSupportKZero X :=
  compactSupportKZeroHomeomorphEquiv (Homeomorph.prodUnique X (Fin 0 → ℝ))

/-- Identity induces identity in every nonpositive compact-support degree. -/
theorem compactSupportKPullback_id (n : ℕ) :
    compactSupportKPullback n (ContinuousMap.id X) isProperMap_id =
      AddMonoidHom.id (CompactSupportK n X) := by
  /- The product of the identity on X with the identity on its n real coordinates
  is the identity on the same product space. Apply compactSupportKZeroPullback_id
  to that locally compact Hausdorff space. No periodicity or coordinate change
  enters the argument, including when n = 0 or X is empty. -/
  change compactSupportKZeroPullback (ContinuousMap.id (X × (Fin n → ℝ)))
    isProperMap_id = _
  exact compactSupportKZeroPullback_id

/-- Proper pullbacks compose contravariantly in every nonpositive degree. -/
theorem compactSupportKPullback_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z))
    (hf : IsProperMap f) (hg : IsProperMap g) :
    compactSupportKPullback n (g.comp f) (hg.comp hf) =
      (compactSupportKPullback n f hf).comp (compactSupportKPullback n g hg) := by
  /- Stage 1: the product maps f × id and g × id are proper because f and g are
  proper. Their composite is literally (g ∘ f) × id on every pair (x,t).
  Stage 2: apply compactSupportKZeroPullback_comp to these same product maps.
  Proof irrelevance identifies their properness certificates; it does not replace
  the underlying coordinate maps or the original compact-support pullbacks. -/
  exact compactSupportKZeroPullback_comp
    (f.prodMap (ContinuousMap.id (Fin n → ℝ)))
    (g.prodMap (ContinuousMap.id (Fin n → ℝ)))
    (hf.prodMap isProperMap_id) (hg.prodMap isProperMap_id)

/-- The degree-zero coordinate comparison commutes with the original proper pullback. -/
theorem compactSupportKZeroDegreeEquiv_pullback (f : C(X, Y)) (hf : IsProperMap f)
    (a : CompactSupportK 0 Y) :
    compactSupportKZeroDegreeEquiv X (compactSupportKPullback 0 f hf a) =
      compactSupportKZeroPullback f hf (compactSupportKZeroDegreeEquiv Y a) := by
  /- Stage 1: the inverse coordinate comparison sends x to (x, the empty tuple).
  Composing it with f × id is the same continuous map as first applying f and
  then inserting that empty tuple in Y × ℝ⁰. Both insertions are homeomorphisms
  onto the respective products and hence proper.
  Stage 2: expand the specified homeomorphism transport as inverse pullback.
  Apply proper-pullback composition to this commuting square. The two resulting
  expressions are the displayed comparisons with exactly the original Kc⁰ map. -/
  let jX : C(X, X × (Fin 0 → ℝ)) :=
    ⟨(Homeomorph.prodUnique X (Fin 0 → ℝ)).symm,
      (Homeomorph.prodUnique X (Fin 0 → ℝ)).symm.continuous⟩
  let jY : C(Y, Y × (Fin 0 → ℝ)) :=
    ⟨(Homeomorph.prodUnique Y (Fin 0 → ℝ)).symm,
      (Homeomorph.prodUnique Y (Fin 0 → ℝ)).symm.continuous⟩
  let hX := (Homeomorph.prodUnique X (Fin 0 → ℝ)).symm.isProperMap
  let hY := (Homeomorph.prodUnique Y (Fin 0 → ℝ)).symm.isProperMap
  -- Both routes insert the same empty coordinate tuple beside f x.
  have hsquare : (f.prodMap (ContinuousMap.id (Fin 0 → ℝ))).comp jX = jY.comp f := rfl
  change compactSupportKZeroPullback jX hX
      (compactSupportKZeroPullback (f.prodMap (ContinuousMap.id (Fin 0 → ℝ)))
        (hf.prodMap isProperMap_id) a) =
    compactSupportKZeroPullback f hf (compactSupportKZeroPullback jY hY a)
  have hleft := compactSupportKZeroPullback_comp jX
    (f.prodMap (ContinuousMap.id (Fin 0 → ℝ))) hX (hf.prodMap isProperMap_id)
  have hright := compactSupportKZeroPullback_comp f jY hf hY
  -- The two properness certificates concern definitionally the same composite map.
  have hcomp := hleft.symm.trans hright
  exact DFunLike.congr_fun hcomp a

end AtiyahSinger
