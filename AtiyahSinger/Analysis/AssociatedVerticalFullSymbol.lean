/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedVerticalSymbolGauge

/-!
# The actual descended vertical full symbol

Public module ID: M0221.

A fixed sphere full symbol has one linear action on every original associated
fiber and every original total covector. Its value is obtained by restricting
that covector along the actual sphere inclusion and then applying the original
symbol. The quotient construction gives this formula for every principal
representative, without making a continuous choice of representatives. This
result asserts the algebraic full-symbol action; continuity and quantitative
ellipticity are separate obligations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere lieGroup_orthogonalGroup
  associatedEquivariantFiberAddCommGroup associatedEquivariantFiberModule

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
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- One linear associated symbol has the original fiber-restriction formula in every gauge. -/
theorem existsUnique_associatedSphereVerticalFullSymbol
    (q : GlobalSymbolFunction (n := r) F F')
    (hq : ∀ g : G, equivariantGlobalSymbolLinearMap IG σ τ g q = q) :
    letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
    letI := associatedSphereChartedSpace S
    let D := AssociatedEquivariantFiber S.toIsPrincipalBundle σ
    let D' := AssociatedEquivariantFiber S.toIsPrincipalBundle τ
    ∃! a : ∀ z : Z, (X × Y →L[ℝ] ℝ) → D z →ₗ[ℂ] D' z,
      ∀ (p : P) (y : OrthogonalSphere r) {z : Z}
        (hz : associatedBundleMk G P (OrthogonalSphere r) p y = z)
        (ξ : X × Y →L[ℝ] ℝ) (u : F y),
        a z ξ (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y hz u) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle τ p y hz
            (q y (ξ.comp (mfderiv (𝓡 r) 𝓘(ℝ, X × Y)
              (associatedBundleMk G P (OrthogonalSphere r) p) y)) u) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin d)) F
  let := modelTopology (EuclideanSpace ℂ (Fin e)) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
  let := associatedSphereChartedSpace S
  let : MulAction G (TotalSpace Unit F) := σ.toMulAction
  let : MulAction G (TotalSpace Unit F') := τ.toMulAction
  let D := AssociatedEquivariantFiber S.toIsPrincipalBundle σ
  let D' := AssociatedEquivariantFiber S.toIsPrincipalBundle τ
  let I := 𝓘(ℝ, X × Y)
  let value (ξ : X × Y →L[ℝ] ℝ) (p : P) (w : TotalSpace Unit F) : TotalSpace Unit F' :=
    ⟨w.proj, q w.proj (ξ.comp (mfderiv (𝓡 r) I
      (associatedBundleMk G P (OrthogonalSphere r) p) w.proj)) w.snd⟩
  -- The proved gauge square makes the actual quotient value independent of representatives.
  have hvalue (ξ : X × Y →L[ℝ] ℝ) (p : P) (g : G) (w : TotalSpace Unit F) :
      associatedBundleMk G P (TotalSpace Unit F') (MulOpposite.op g • p)
          (value ξ (MulOpposite.op g • p) w) =
        associatedBundleMk G P (TotalSpace Unit F') p (value ξ p (g • w)) := by
    exact congrArg Subtype.val
      (associatedSphereVerticalSymbol_gauge_eq S σ τ q hq p g w.proj ξ w.snd)
  let Q (ξ : X × Y →L[ℝ] ℝ) : AssociatedBundle G P (TotalSpace Unit F) →
      AssociatedBundle G P (TotalSpace Unit F') := Quotient.lift
    (fun w : P × TotalSpace Unit F ↦
      associatedBundleMk G P (TotalSpace Unit F') w.1 (value ξ w.1 w.2)) (by
      intro w w' h
      obtain ⟨g, rfl⟩ := h
      exact ((hvalue ξ w.1 g (g⁻¹ • w.2)).trans
        (congrArg (fun v ↦ associatedBundleMk G P (TotalSpace Unit F') w.1
          (value ξ w.1 v)) (smul_inv_smul g w.2))).symm)
  have hprojection (ξ : X × Y →L[ℝ] ℝ) (w : AssociatedBundle G P (TotalSpace Unit F)) :
      associatedEquivariantProjection τ (Q ξ w) = associatedEquivariantProjection σ w := by
    induction w using Quotient.inductionOn with
    | h w => rfl
  let a (z : Z) (ξ : X × Y →L[ℝ] ℝ) (u : D z) : D' z :=
    ⟨Q ξ u.val, (hprojection ξ u.val).trans u.property⟩
  have hformula (p : P) (y : OrthogonalSphere r) {z : Z}
      (hz : associatedBundleMk G P (OrthogonalSphere r) p y = z)
      (ξ : X × Y →L[ℝ] ℝ) (u : F y) :
      a z ξ (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y hz u) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle τ p y hz
          (q y (ξ.comp (mfderiv (𝓡 r) I
            (associatedBundleMk G P (OrthogonalSphere r) p) y)) u) := rfl
  -- Every original representative gives bijective linear coordinates on its quotient fiber.
  have hlinear (z : Z) (ξ : X × Y →L[ℝ] ℝ) : IsLinearMap ℂ (a z ξ) := by
    let p := (Quotient.out z).1
    let y := (Quotient.out z).2
    have hz : associatedBundleMk G P (OrthogonalSphere r) p y = z := Quotient.out_eq z
    have hE := associatedEquivariantFiberMk_isLinear S.toIsPrincipalBundle σ p y hz
    have hF := associatedEquivariantFiberMk_isLinear S.toIsPrincipalBundle τ p y hz
    have hsurj := (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ p y hz).2
    constructor
    · intro u v
      obtain ⟨u₀, rfl⟩ := hsurj u
      obtain ⟨v₀, rfl⟩ := hsurj v
      rw [← hE.map_add, hformula, hformula, hformula, map_add, hF.map_add]
    · intro c u
      obtain ⟨u₀, rfl⟩ := hsurj u
      rw [← hE.map_smul, hformula, hformula, map_smul, hF.map_smul]
  refine ⟨fun z ξ ↦ IsLinearMap.mk' (a z ξ) (hlinear z ξ), ?_, ?_⟩
  · exact hformula
  · intro b hb
    funext z ξ
    apply LinearMap.ext
    intro u
    let p := (Quotient.out z).1
    let y := (Quotient.out z).2
    have hz : associatedBundleMk G P (OrthogonalSphere r) p y = z := Quotient.out_eq z
    obtain ⟨u₀, rfl⟩ :=
      (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ p y hz).2 u
    exact hb p y hz ξ u₀

end AtiyahSinger
