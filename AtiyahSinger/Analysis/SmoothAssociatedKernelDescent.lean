/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedFiniteSectionDescent

/-!
# Smooth descent of the specified finite kernel

The original finite representation coordinates on a sphere operator's kernel
identify its entire associated smooth kernel family with smooth sections of
that same associated representation bundle. The proof keeps the supplied
kernel coordinates and all principal representatives. It makes no claim about
an upstairs elliptic operator, which still requires a horizontal construction.

This is the vertical coefficient identification in SG III.13.6; it applies
separately to the fiber operator and to its formal adjoint.
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
  {W : Type*} [AddCommGroup W] [Module ℂ W]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "V" => Fin ρ.dimension → ℂ
local notation "C" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Full-fiber smooth kernel sections are exactly the smooth associated kernel coefficients. -/
theorem exists_smoothAssociatedKernelDescent
    (T : A.smoothSections →ₗ[ℂ] W)
    (e : V ≃ₗ[ℂ] T.ker)
    (he : ∀ (g : G) (y : OrthogonalSphere r) (v : V),
      (e (ρ.representation g v)).val.val (g • y) =
        σ.linearMap g y ((e v).val.val y)) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let q := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    ∃ a : Hom ((q : Z → B) *ᵖ C) D,
      (∀ (p : P) (y : OrthogonalSphere r) (v : V),
        a.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
            (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((e v).val.val y)) ∧
      ∀ w : (associatedSphereSmoothBundleAtlas S A σ hσ).smoothSections,
        (∀ p : P, ∃ t : A.smoothSections, T t = 0 ∧
          ∀ y : OrthogonalSphere r,
            w.val (associatedBundleMk G P (OrthogonalSphere r) p y) =
              associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl (t.val y)) ↔
        ∃! u : (associatedOrthogonalRepresentationAtlas S ρ).smoothSections,
          ∀ z : Z, a.linearMap z (u.val (q z)) = w.val z := by
  classical
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let q := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let s : V →ₗ[ℂ] A.smoothSections := T.ker.subtype.comp e.toLinearMap
  have hs : Function.Injective s := Subtype.val_injective.comp e.injective
  obtain ⟨a, ha, _, _⟩ := exists_associatedSectionEvaluation S.toIsPrincipalBundle
    A σ ρ s he
  refine ⟨a, ha, ?_⟩
  intro w
  constructor
  · intro hw
    -- The same kernel coordinates turn each actual fiber kernel into the finite family.
    apply existsUnique_smoothAssociatedCoefficient S A σ hσ ρ s hs a ha w
    intro p
    obtain ⟨t, ht, hwt⟩ := hw p
    let k : T.ker := ⟨t, ht⟩
    refine ⟨e.symm k, ?_⟩
    intro y
    have hsval : (s (e.symm k)).val = t.val :=
      congrArg (fun x : T.ker ↦ x.val.val) (e.apply_symm_apply k)
    change w.val _ = associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl
      ((s (e.symm k)).val y)
    rw [hsval]
    exact hwt y
  · rintro ⟨u, hu, _⟩ p
    -- Recover coordinates at p itself; no global principal section is chosen.
    obtain ⟨v, hv⟩ := (associatedVectorFiberMk_bijective S.toIsPrincipalBundle
      ρ.representation p rfl).2 (u.val (projection p))
    refine ⟨(e v).val, (e v).property, ?_⟩
    intro y
    have h := hu (associatedBundleMk G P (OrthogonalSphere r) p y)
    change a.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
      (u.val (projection p)) = _ at h
    rw [← hv, ha] at h
    exact h.symm

end AtiyahSinger
