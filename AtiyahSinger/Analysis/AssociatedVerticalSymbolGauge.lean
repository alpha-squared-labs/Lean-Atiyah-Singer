/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantFullSymbolCovariance
public import AtiyahSinger.Geometry.AssociatedSphereVerticalCotangent
public import AtiyahSinger.Geometry.OrthogonalSmoothAction
public import AtiyahSinger.Topology.AssociatedEquivariantBundle

/-!
# Gauge independence of the original vertical full-symbol value

Public module ID: M0225.

Restrict one original total covector along the actual sphere fiber inclusion.
Changing its principal representative transforms this covector by the inverse
differential action. The original full-symbol covariance therefore identifies
the resulting output in the same associated vector fiber. This is the gauge
compatibility needed to combine saturated finite patch symbols; it does not
assume that the original full symbol is homogeneous.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

variable {n r d e : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  {F F' : OrthogonalSphere r → Type*}
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin d)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin d)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin d)) F]
  [∀ y, NormedAddCommGroup (F' y)] [∀ y, NormedSpace ℂ (F' y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin e)) F')]
  [FiberBundle (EuclideanSpace ℂ (Fin e)) F']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin e)) F']
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (τ : letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Full-symbol fixedness identifies its vertical value under the actual gauge transformation. -/
theorem associatedSphereVerticalSymbol_gauge_eq
    (q : GlobalSymbolFunction (n := r) F F')
    (hq : ∀ g : G, equivariantGlobalSymbolLinearMap IG σ τ g q = q)
    (p : P) (g : G) (y : OrthogonalSphere r) :
    letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
    letI := associatedSphereChartedSpace S
    let i₁ := associatedBundleMk G P (OrthogonalSphere r) (MulOpposite.op g • p)
    let i₂ := associatedBundleMk G P (OrthogonalSphere r) p
    ∀ (ξ : X × Y →L[ℝ] ℝ) (u : F y),
      associatedEquivariantFiberMk S.toIsPrincipalBundle τ (MulOpposite.op g • p) y
          (associatedBundleMk_smul p g y)
          (q y (ξ.comp (mfderiv (𝓡 r) 𝓘(ℝ, X × Y) i₁ y)) u) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle τ p (g • y) rfl
          (q (g • y) (ξ.comp (mfderiv (𝓡 r) 𝓘(ℝ, X × Y) i₂ (g • y)))
            (σ.linearMap g y u)) := by
  let := modelTopology (EuclideanSpace ℂ (Fin d)) F
  let := modelTopology (EuclideanSpace ℂ (Fin e)) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓘(ℝ, X × Y)
  let i₁ := associatedBundleMk G P (OrthogonalSphere r) (MulOpposite.op g • p)
  let i₂ := associatedBundleMk G P (OrthogonalSphere r) p
  let a := Diffeomorph.smul (M := OrthogonalSphere r) IG (𝓡 r) ∞ g
  change ∀ (ξ : X × Y →L[ℝ] ℝ) (u : F y), _
  intro ξ u
  let η₁ := ξ.comp (mfderiv (𝓡 r) I i₁ y)
  let η₂ := ξ.comp (mfderiv (𝓡 r) I i₂ (g • y))
  -- Differentiate the original equality [p g,y] = [p,g y] before applying any symbol.
  have hd : mfderiv (𝓡 r) I i₁ y =
      (mfderiv (𝓡 r) I i₂ (g • y)).comp (mfderiv (𝓡 r) (𝓡 r) a y) := by
    have hi : i₁ = i₂ ∘ a := funext (fun z ↦ associatedBundleMk_smul p g z)
    rw [hi]
    exact mfderiv_comp y
      ((smoothAssociatedSphereFiberInclusion S p).contMDiff.mdifferentiable (by simp) _)
      (a.mdifferentiable (by simp) y)
  have hη : (cotangentDiffeomorphMap a ⟨y, η₁⟩).snd = η₂ := by
    ext v
    change ξ (mfderiv (𝓡 r) I i₁ y (mfderiv (𝓡 r) (𝓡 r) a.symm (a y) v)) =
      ξ (mfderiv (𝓡 r) I i₂ (g • y) v)
    rw [hd]
    have hinv := (a.toOpenPartialHomeomorph_mdifferentiable (by simp)).comp_symm_deriv
      (show a y ∈ a.toHomeomorph.toOpenPartialHomeomorph.target from Set.mem_univ (a y))
    change (mfderiv (𝓡 r) (𝓡 r) a (a.symm (a y))).comp
      (mfderiv (𝓡 r) (𝓡 r) a.symm (a y)) = ContinuousLinearMap.id ℝ Y at hinv
    rw [a.symm_apply_apply] at hinv
    exact congrArg (fun L : Y →L[ℝ] Y ↦ ξ (mfderiv (𝓡 r) I i₂ (g • y) (L v))) hinv
  -- Fixedness acts on the same restricted covector, including the zero section.
  have hcov := (equivariantGlobalSymbolLinearMap_eq_iff_forall IG σ τ q).mp
    (fun k z η ↦ congrArg (fun b : GlobalSymbolFunction (n := r) F F' ↦ b z η) (hq k))
  have hqval : q (g • y) η₂ (σ.linearMap g y u) = τ.linearMap g y (q y η₁ u) := by
    have h := hcov g y η₁ u
    change q (g • y) (cotangentDiffeomorphMap a ⟨y, η₁⟩).snd (σ.linearMap g y u) = _ at h
    rw [hη] at h
    exact h
  -- The original quotient convention now gives equality inside one actual output fiber.
  change associatedEquivariantFiberMk S.toIsPrincipalBundle τ (MulOpposite.op g • p) y
      (associatedBundleMk_smul p g y) (q y η₁ u) =
    associatedEquivariantFiberMk S.toIsPrincipalBundle τ p (g • y) rfl
      (q (g • y) η₂ (σ.linearMap g y u))
  rw [hqval]
  apply Subtype.ext
  let : MulAction G (TotalSpace Unit F') := τ.toMulAction
  exact associatedBundleMk_smul p g (⟨y, q y η₁ u⟩ : TotalSpace Unit F')

end AtiyahSinger
