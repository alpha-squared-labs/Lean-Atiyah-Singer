/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSymbol
public import AtiyahSinger.Geometry.AssociatedSphereProductChart

/-!
# The actual vertical covector in associated product charts

Public module ID: M0107.

The vertical frequency of the original flattened product chart is the sphere
chart coordinate of one specified covector. That covector is obtained by
restricting the original covector along the derivative of the inverse principal
trivialization in the sphere direction. It depends on that trivialization and
the original covector, but not on either of the coordinate charts.

This exact identity lets a fixed sphere partition recover its full symbol at
one common vertical covector. It does not remove the mixed horizontal block
or identify a general PDO symbol with a homogeneous representative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The vertical part of every original product-chart covector is a common sphere covector. -/
theorem covectorInChart_associatedSphereProductChart_snd
    (b : B) (c : OpenPartialHomeomorph B (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) B)
    (d : OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)))
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)) :
    let X := EuclideanSpace ℝ (Fin n)
    let Y := EuclideanSpace ℝ (Fin r)
    let Z := AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)
    letI : ChartedSpace (X × Y) (B × OrthogonalSphere r) := prodChartedSpace X B Y _
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let t := (associatedSphereTrivialization S b).toOpenPartialHomeomorph
    let CP := associatedSphereProductChart S b c d
    ∀ z : Z, z ∈ CP.source →
      ∀ ξ : TangentSpace (𝓡 (n + r)) z →L[ℝ] ℝ,
        (EuclideanSpace.finAddEquivProd (n := n) (m := r) (covectorInChart CP z ξ)).2 =
          covectorInChart d (t z).2
            (ξ.comp ((mfderiv 𝓘(ℝ, X × Y) (𝓡 (n + r)) t.symm (t z)).comp
              (ContinuousLinearMap.inr ℝ X Y))) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin r)
  let H := EuclideanSpace ℝ (Fin (n + r))
  let Z := AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)
  let I := 𝓘(ℝ, X × Y)
  let K := 𝓡 (n + r)
  let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let : ChartedSpace (X × Y) (B × OrthogonalSphere r) := prodChartedSpace X B Y _
  let : IsManifold I ∞ (B × OrthogonalSphere r) := by
    dsimp only [I]
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod B (OrthogonalSphere r)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let e := linearModelDiffeomorph split.symm Z
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  let t := (associatedSphereTrivialization S b).toOpenPartialHomeomorph
  let CP := associatedSphereProductChart S b c d
  change ∀ z : Z, z ∈ CP.source → ∀ ξ, _
  intro z hz ξ
  have hzt : z ∈ t.source := hz.1.1
  have hxc : (t z).1 ∈ c.source := hz.1.2.1
  have hyd : (t z).2 ∈ d.source := hz.1.2.2
  let a : X →L[ℝ] X := mfderiv (𝓡 n) (𝓡 n) c.symm (c (t z).1)
  let v : Y →L[ℝ] Y := mfderiv (𝓡 r) (𝓡 r) d.symm (d (t z).2)
  let J : X × Y →L[ℝ] H := mfderiv I K t.symm (t z)
  have hc' := mdifferentiableAt_atlas_symm (I := 𝓡 n) hc (c.map_source hxc)
  have hd' := mdifferentiableAt_atlas_symm (I := 𝓡 r) hd (d.map_source hyd)
  -- The same inverse principal trivialization is smooth in the flattened total model.
  have ht : MDifferentiableAt I K t.symm (t z) := by
    have h := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
    have hi : ContMDiffOn ((𝓡 n).prod (𝓡 r)) K ∞ t.symm t.target :=
      e.contMDiff.comp_contMDiffOn h.2
    rw [← modelWithCornersSelf_prod] at hi
    exact (hi.contMDiffAt (t.open_target.mem_nhds (t.map_source hzt))).mdifferentiableAt
      (by simp)
  have hf : MDifferentiableAt I I (Prod.map c.symm d.symm)
      (c (t z).1, d (t z).2) := by
    dsimp only [I]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hc'.prodMap hd'
  -- Differentiate the original inverse product chart; the mixed total derivative remains J.
  have hderiv : mfderiv K K CP.symm (CP z) =
      J.comp ((a.prodMap v).comp split.toContinuousLinearMap) := by
    have he : MDifferentiableAt K I split (split.symm (c (t z).1, d (t z).2)) :=
      split.toContinuousLinearMap.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
    have hf' : MDifferentiableAt I I (Prod.map c.symm d.symm)
        (split (split.symm (c (t z).1, d (t z).2))) := by
      simpa only [split.apply_symm_apply] using hf
    have hvalue : (Prod.map c.symm d.symm)
        (split (split.symm (c (t z).1, d (t z).2))) = t z := by
      simp only [split.apply_symm_apply, Prod.map_apply, c.left_inv hxc, d.left_inv hyd]
    have ht' : MDifferentiableAt I K t.symm
        ((Prod.map c.symm d.symm) (split (split.symm (c (t z).1, d (t z).2)))) := by
      rw [hvalue]
      exact ht
    have hcomp := mfderiv_comp (split.symm (c (t z).1, d (t z).2)) hf' he
    have hcomp' := mfderiv_comp (split.symm (c (t z).1, d (t z).2)) ht' (hf'.comp _ he)
    change mfderiv K K CP.symm (CP z) = _ at hcomp'
    rw [hcomp', hcomp, hvalue]
    have hederiv : mfderiv K I split (split.symm (c (t z).1, d (t z).2)) =
        split.toContinuousLinearMap :=
      split.toContinuousLinearMap.hasFDerivAt.hasMFDerivAt.mfderiv
    rw [hederiv, split.apply_symm_apply]
    have hprod : mfderiv I I (Prod.map c.symm d.symm) (c (t z).1, d (t z).2) =
        a.prodMap v := by
      dsimp only [I]
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact mfderiv_prodMap hc' hd'
    rw [hprod]
    simp only [Function.comp_apply]
    rw [hvalue]
  -- The original last r basis vectors select precisely the sphere restriction of J.
  have hinr (j : Fin r) : split (EuclideanSpace.single (Fin.natAdd n j) 1) =
      (0, EuclideanSpace.single j 1) := by
    apply Prod.ext
    · ext i
      change EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ) (Fin.castAdd r i) = _
      simp only [PiLp.single_apply, PiLp.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      omega
    · ext i
      change EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ) (Fin.natAdd n i) = _
      simp
  ext j
  change ξ ((mfderiv K K CP.symm (CP z))
    (EuclideanSpace.single (Fin.natAdd n j) 1)) = ξ (J (0, v (EuclideanSpace.single j 1)))
  rw [hderiv]
  change ξ (J ((a.prodMap v) (split (EuclideanSpace.single (Fin.natAdd n j) 1)))) = _
  rw [hinr]
  change ξ (J (a 0, v (EuclideanSpace.single j 1))) = _
  rw [map_zero]

end AtiyahSinger
