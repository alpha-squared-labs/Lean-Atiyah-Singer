/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OrthogonalGroupManifold
public import AtiyahSinger.Geometry.OrthogonalSphereCotangent
public import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# The original sphere and cotangent actions of the orthogonal Lie group

Public module ID: M1333.

The Cayley atlas supplies the group parameter missing from the earlier
entrywise smooth families. These instances use the original `diag(A,1)` sphere
action and its original inverse-differential cotangent lift. Neither the sphere
atlas nor the Hom-bundle topology is replaced. Both constructions include rank
zero. The adapters below reuse the existing parametric smoothness statements;
their smoothness follows from those statements and the group atlas.

Source: the orthogonal action in SG III.13, pp.251--252. This is the concrete
Lie-action specialization required by the smooth equivariant analytic interfaces.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff Matrix.Norms.L2Operator

/-- The original block action is a joint smooth action of the original orthogonal Lie group. -/
instance orthogonalSphereContMDiffSMul (r : ℕ) :
    ContMDiffSMul 𝓘(ℝ, OrthogonalGroupModel r) (𝓡 r) ∞
      (Matrix.orthogonalGroup (Fin r) ℝ) (OrthogonalSphere r) where
  contMDiff_smul := by
    let := lieGroup_orthogonalGroup r
    -- Assemble the actual entries in the Pi model used by the original family theorem.
    have hEntries := (contMDiff_orthogonalGroup_iff
      𝓘(ℝ, OrthogonalGroupModel r) r ∞ id).mp contMDiff_id
    have hMatrix : ContMDiff 𝓘(ℝ, OrthogonalGroupModel r)
        𝓘(ℝ, Fin r → Fin r → ℝ) ∞
        (fun A : Matrix.orthogonalGroup (Fin r) ℝ ↦ fun i j ↦ A.val i j) :=
      contMDiff_pi_space.mpr fun i ↦ contMDiff_pi_space.mpr (hEntries i)
    -- Specialize the existing family, retaining exactly its native sphere action.
    simpa only [Set.univ_prod_univ, contMDiffOn_univ] using
      contMDiffOn_orthogonalSphere_parametric_smul 𝓘(ℝ, OrthogonalGroupModel r) r
        (fun A : Matrix.orthogonalGroup (Fin r) ℝ ↦ A.val) Set.univ
        hMatrix.contMDiffOn (fun A ↦ A.property)

/-- The original inverse-differential cotangent lift is jointly smooth. -/
instance orthogonalSphereCotangentContMDiffSMul (r : ℕ) :
    ContMDiffSMul 𝓘(ℝ, OrthogonalGroupModel r)
      ((𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞ (Matrix.orthogonalGroup (Fin r) ℝ)
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) where
  contMDiff_smul := by
    let := lieGroup_orthogonalGroup r
    -- Use the same group atlas and the same original matrix entries as on the sphere.
    have hEntries := (contMDiff_orthogonalGroup_iff
      𝓘(ℝ, OrthogonalGroupModel r) r ∞ id).mp contMDiff_id
    have hMatrix : ContMDiff 𝓘(ℝ, OrthogonalGroupModel r)
        𝓘(ℝ, Fin r → Fin r → ℝ) ∞
        (fun A : Matrix.orthogonalGroup (Fin r) ℝ ↦ fun i j ↦ A.val i j) :=
      contMDiff_pi_space.mpr fun i ↦ contMDiff_pi_space.mpr (hEntries i)
    -- The earlier lift already differentiates the inverse and keeps the original covector.
    simpa only [Set.univ_prod_univ, contMDiffOn_univ] using
      contMDiffOn_orthogonalSphereCotangent_parametric_smul
        𝓘(ℝ, OrthogonalGroupModel r) r
        (fun A : Matrix.orthogonalGroup (Fin r) ℝ ↦ A.val) Set.univ
        hMatrix.contMDiffOn (fun A ↦ A.property)

end AtiyahSinger
