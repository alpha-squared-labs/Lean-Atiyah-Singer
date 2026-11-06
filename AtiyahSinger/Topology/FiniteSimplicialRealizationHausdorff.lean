/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactHausdorffAttachment
public import AtiyahSinger.Topology.SimplicialBoundaryRealization
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.Topology.Category.TopCat.Limits.Products

/-!
# Hausdorffness of finite simplicial realizations

Public module ID: M1857.

The original realization of a finite simplicial set is Hausdorff. The finite
skeleton attaches finitely many standard simplices along their original closed
boundary embeddings. Realization preserves the actual coproducts and pushouts;
compact Hausdorff closed attachment therefore applies at every stage.

This is the usual finite CW realization argument, performed on the existing
`SSet.toTop` object. It supplies the separation hypothesis needed to use finite
realizations as compact Hausdorff test sources for singular homology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Convexity Topology

open scoped Simplicial

universe u

namespace SSet

/-- The original geometric realization of a finite simplicial set is Hausdorff. -/
theorem t2Space_toTop_of_finite (X : SSet.{u}) [X.Finite] : T2Space |X| := by
  classical
  let i : ((⊥ : X.Subcomplex) : SSet.{u}) ⟶ X := (⊥ : X.Subcomplex).ι
  -- The realization of a coproduct is the actual disjoint union. Record its
  -- inverse on each original injection, so subsequent squares retain the same maps.
  let e {J : Type u} (A : J → SSet.{u}) : |(∐ A : SSet.{u})| ≃ₜ (Σ j, |A j|) :=
    TopCat.homeoOfIso (PreservesCoproduct.iso SSet.toTop A ≪≫
      TopCat.sigmaIsoSigma (fun j ↦ SSet.toTop.obj (A j)))
  have he {J : Type u} (A : J → SSet.{u}) (j : J) (x : |A j|) :
      (e A).symm ⟨j, x⟩ = SSet.toTop.map (Sigma.ι A j) x := by
    change (PreservesCoproduct.iso SSet.toTop A).inv
      ((TopCat.sigmaIsoSigma (fun j ↦ SSet.toTop.obj (A j))).inv ⟨j, x⟩) = _
    rw [TopCat.sigmaIsoSigma_inv_apply, PreservesCoproduct.inv_hom]
    exact congrArg (fun f ↦ f x) (ι_comp_sigmaComparison SSet.toTop A j)
  have hstep (n : ℕ) (h : T2Space |(skeletonOfMono i n : SSet.{u})|) :
      T2Space |(skeletonOfMono i (n + 1) : SSet.{u})| := by
    let := h
    let J := relativeCellComplexOfMono.Cell i n
    let : Finite J := Finite.of_injective (fun c : J ↦ c.simplex) (by
      intro a b hab
      exact relativeCellComplexOfMono.Cell.ext hab)
    let A : J → SSet.{u} := fun _ ↦ boundary n
    let B : J → SSet.{u} := fun _ ↦ Δ[n]
    let : CompactSpace |(boundary.{u} n : SSet)| := compactSpace_toTop_of_finite _
    let : T2Space (StdSimplex ℝ (Fin (n + 1))) :=
      (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space
    let : CompactSpace |(Δ[n] : SSet.{u})| :=
      (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
    let : T2Space |(Δ[n] : SSet.{u})| :=
      (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
    let : CompactSpace |(∐ A : SSet.{u})| := (e A).symm.compactSpace
    let : CompactSpace |(∐ B : SSet.{u})| := (e B).symm.compactSpace
    let : T2Space |(∐ B : SSet.{u})| := (e B).symm.t2Space
    let : CompactSpace |(skeletonOfMono i n : SSet.{u})| := compactSpace_toTop_of_finite _
    let l := SSet.toTop.map (relativeCellComplexOfMono.l i n)
    let t := SSet.toTop.map (relativeCellComplexOfMono.t i n)
    -- The realized attaching map is the disjoint union of the original
    -- realized boundary inclusions, hence injective and closed by compactness.
    let f : (Σ j, |A j|) → (Σ j, |B j|) :=
      Sigma.map id (fun _ ↦ SSet.toTop.map (boundary.{u} n).ι)
    have hf : Function.Injective f :=
      Function.injective_id.sigma_map (fun _ ↦ (isClosedEmbedding_toTop_boundary n).injective)
    have hsquare (z : Σ j, |A j|) : l ((e A).symm z) = (e B).symm (f z) := by
      rcases z with ⟨j, x⟩
      rw [he]
      change l (SSet.toTop.map (Sigma.ι A j) x) =
        (e B).symm ⟨j, SSet.toTop.map (boundary.{u} n).ι x⟩
      rw [he]
      have hmap : SSet.toTop.map (Sigma.ι A j) ≫ l =
          SSet.toTop.map (boundary.{u} n).ι ≫ SSet.toTop.map (Sigma.ι B j) := by
        dsimp only [l, relativeCellComplexOfMono.l]
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (fun g ↦ SSet.toTop.map g) (Sigma.ι_map _ j)
      exact congrArg (fun g ↦ g x) hmap
    have hl : IsClosedEmbedding l := by
      apply l.hom.continuous.isClosedEmbedding
      intro x y hxy
      apply (e A).injective
      apply hf
      apply (e B).symm.injective
      rw [← hsquare, ← hsquare, Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
      exact hxy
    let : T2Space (pushout l t : TopCat.{u}) :=
      TopCat.t2Space_pushout_of_isClosedEmbedding l t hl
    -- The actual skeleton square, with its two original attaching maps,
    -- identifies this Hausdorff pushout with the next realized skeleton.
    let square := ((relativeCellComplexOfMono.isPushout i n).flip).map SSet.toTop
    exact (TopCat.homeoOfIso square.isoPushout).symm.t2Space
  have hskeleton (n : ℕ) : T2Space |(skeletonOfMono i n : SSet.{u})| := by
    induction n with
    | zero =>
      -- The initial skeleton realizes to the empty space.
      have hempty := (Subcomplex.isInitialBot (X := X)).isInitialObj SSet.toTop _
      let : T2Space |((⊥ : X.Subcomplex) : SSet.{u})| :=
        (TopCat.homeoOfIso (hempty.uniqueUpToIso TopCat.isInitialPEmpty)).symm.t2Space
      exact (TopCat.homeoOfIso (SSet.toTop.mapIso (relativeCellComplex X).isoBot)).symm.t2Space
    | succ n hn => exact hstep n hn
  -- Finite nondegenerate simplices give a bound at which the skeleton is the
  -- entire original simplicial set; only this final equality is transported.
  obtain ⟨d, hd⟩ := X.hasDimensionLT_of_finite
  let := hd
  have htop : skeletonOfMono i d = ⊤ := by
    apply (Subcomplex.eq_top_iff_of_hasDimensionLT _ d).mpr
    intro n hn x hx
    rw [skeletonOfMono_obj_eq_top i hn]
    trivial
  let := hskeleton d
  exact (TopCat.homeoOfIso (SSet.toTop.mapIso
    (Subcomplex.eqToIso htop ≪≫ Subcomplex.topIso X))).t2Space

end SSet
