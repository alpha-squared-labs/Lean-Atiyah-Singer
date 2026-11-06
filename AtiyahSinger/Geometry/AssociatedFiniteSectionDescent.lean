/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSectionSmoothness

/-!
# Smooth sections of the original associated finite section family

An upstairs smooth section whose restriction to each full fiber belongs to the
specified finite family is the evaluation of a unique smooth section of the
original associated coefficient bundle. Principal transitivity proves global
existence without a continuous global principal section. Smoothness follows
from the previously proved detection theorem in the prescribed atlases.

SG III.13.6 applies this to the actual vertical kernel and adjoint kernel.
The full-fiber family condition is retained explicitly, before defining any
vertical operator or computing the upstairs index.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  {E : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (E y)]
  [∀ y, Module ℂ (E y)] [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (A : SmoothComplexBundleAtlas (n := r) E)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) E)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "V" => Fin ρ.dimension → ℂ
local notation "C" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in
-- Keep the original quotient representatives and their dependent base fibers in the descent.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full associated finite section family has exactly its original smooth coefficient
sections. -/
theorem existsUnique_smoothAssociatedCoefficient
    (s : V →ₗ[ℂ] A.smoothSections) (hs : Function.Injective s)
    (a : Hom (((associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle) :
        Z → B) *ᵖ C) D)
    (ha : ∀ (p : P) (y : OrthogonalSphere r) (v : V),
      a.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((s v).val y)) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let q := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    ∀ w : (associatedSphereSmoothBundleAtlas S A σ hσ).smoothSections,
      (∀ p : P, ∃ v : V, ∀ y : OrthogonalSphere r,
        w.val (associatedBundleMk G P (OrthogonalSphere r) p y) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((s v).val y)) →
      ∃! u : (associatedOrthogonalRepresentationAtlas S ρ).smoothSections,
        ∀ z : Z, a.linearMap z (u.val (q z)) = w.val z := by
  classical
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let q := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let AC := associatedOrthogonalRepresentationAtlas S ρ
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  dsimp only
  intro w hw
  let p (b : B) : P := (S.trivialization b).toPartialEquiv.symm (b, 1)
  have hp (b : B) : projection (p b) = b :=
    (S.trivialization b).proj_symm_apply' (S.mem_baseSet b)
  let v (b : B) : V := (hw (p b)).choose
  have hv (b : B) := (hw (p b)).choose_spec
  let u (b : B) : C b :=
    associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation (p b) (hp b) (v b)
  -- Principal transitivity gives a representative with the chosen p over each fixed base point.
  have heq (z : Z) : a.linearMap z (u (q z)) = w.val z := by
    obtain ⟨⟨p', y'⟩, hrep⟩ := Quotient.exists_rep z
    have hp' : projection p' = q z := congrArg q hrep
    obtain ⟨g, hg, _⟩ := S.toIsPrincipalBundle.existsUnique_smul
      (p (q z)) p' ((hp (q z)).trans hp'.symm)
    let y := g • y'
    have hz : associatedBundleMk G P (OrthogonalSphere r) (p (q z)) y = z :=
      (associatedBundleMk_smul (p (q z)) g y').symm.trans
        ((congrArg (fun p' ↦ associatedBundleMk G P (OrthogonalSphere r) p' y') hg).trans
          hrep)
    have hformula (z' : Z)
        (hz' : associatedBundleMk G P (OrthogonalSphere r) (p (q z)) y = z')
        (hpz : projection (p (q z)) = q z') :
        a.linearMap z'
            (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation
              (p (q z)) hpz (v (q z))) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ (p (q z)) y hz'
            ((s (v (q z))).val y) := by
      subst z'
      exact ha (p (q z)) y (v (q z))
    have hwformula (z' : Z)
        (hz' : associatedBundleMk G P (OrthogonalSphere r) (p (q z)) y = z') :
        w.val z' = associatedEquivariantFiberMk S.toIsPrincipalBundle σ
          (p (q z)) y hz' ((s (v (q z))).val y) := by
      subst z'
      exact hv (q z) y
    exact (hformula z hz (hp (q z))).trans (hwformula z hz).symm
  have hu : AC.IsSmoothSection u := by
    apply (isSmoothSection_associatedEvaluation_iff S A σ hσ ρ s hs a ha u).mp
    have heqFun : (fun z : Z ↦ a.linearMap z (u (q z))) = w.val := funext heq
    rw [heqFun]
    exact w.property
  refine ⟨⟨u, hu⟩, heq, ?_⟩
  -- Uniqueness is injectivity into full fiber sections, rather than a single-point evaluation.
  intro u' hu'
  apply Subtype.ext
  funext b
  obtain ⟨v', hv'⟩ := (associatedVectorFiberMk_bijective S.toIsPrincipalBundle
    ρ.representation (p b) (hp b)).2 (u'.val b)
  have hvv : v' = v b := by
    apply hs
    apply Subtype.ext
    funext y
    apply (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ (p b) y rfl).1
    have h := hu' (associatedBundleMk G P (OrthogonalSphere r) (p b) y)
    have hqb : q (associatedBundleMk G P (OrthogonalSphere r) (p b) y) = b := hp b
    have hval : u'.val (q (associatedBundleMk G P (OrthogonalSphere r) (p b) y)) =
        associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation (p b) rfl v' := by
      have htransport (b' : B) (hb' : b' = b) :
          u'.val b' = associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation
            (p b) ((hp b).trans hb'.symm) v' := by
        subst b'
        exact hv'.symm
      exact htransport _ hqb
    rw [hval, ha] at h
    exact h.trans (hv b y)
  exact hv'.symm.trans (congrArg
    (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation (p b) (hp b)) hvv)

end AtiyahSinger

