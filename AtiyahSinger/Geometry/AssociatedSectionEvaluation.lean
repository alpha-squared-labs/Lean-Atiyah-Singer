/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FiniteSectionEvaluation
public import AtiyahSinger.Topology.AssociatedConstantFiber
public import AtiyahSinger.Topology.AssociatedEquivariantMaps

/-!
# Evaluation of the actual associated section representation

Public module ID: M1066.

A finite equivariant family of smooth sections gives an evaluation map from
the pullback of its original associated representation bundle to the original
associated varying-fiber bundle. Every principal representative retains the
formula [p,v] at [p,y] maps to [p,s(v)(y)]. Over a full fiber its image consists
of precisely the specified section family. Injectivity concerns sections on
that full fiber, not evaluation at a single point.

This is the coefficient evaluation in SG III.13.6. The result constructs the
actual continuous map. `SmoothAssociatedSectionEvaluation` establishes
smoothness in the prescribed orthogonal principal atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] trivialTopology isFiniteRank_trivial
  associatedEquivariantFiberAddCommGroup associatedEquivariantFiberModule
  associatedEquivariantTotalTopology associatedVectorFiberAddCommGroup
  associatedVectorFiberModule associatedVectorTotalTopology isFiniteRank_pullback

variable {n : ℕ} {G P B Y : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original associated coefficient evaluates as exactly the specified family of sections. -/
theorem exists_associatedSectionEvaluation (hP : IsPrincipalBundle G projection)
    (A : SmoothComplexBundleAtlas (n := n) E) (σ : EquivariantStructure G E)
    (ρ : FiniteContinuousRepresentation G)
    (s : (Fin ρ.dimension → ℂ) →ₗ[ℂ] A.smoothSections)
    (hsg : ∀ (g : G) (y : Y) (v : Fin ρ.dimension → ℂ),
      (s (ρ.representation g v)).val (g • y) = σ.linearMap g y ((s v).val y)) :
    let q := associatedBundleProjection (F := Y) hP
    ∃ a : Hom ((q : AssociatedBundle G P Y → B) *ᵖ
        (AssociatedVectorFiber hP ρ.representation)) (AssociatedEquivariantFiber hP σ),
      (∀ (p : P) (y : Y) (v : Fin ρ.dimension → ℂ),
        a.linearMap (associatedBundleMk G P Y p y)
            (associatedVectorFiberMk hP ρ.representation p rfl v) =
          associatedEquivariantFiberMk hP σ p y rfl ((s v).val y)) ∧
      (∀ (p : P) (w : ∀ y : Y, E y),
        (∃ v : AssociatedVectorFiber hP ρ.representation (projection p),
          ∀ y : Y, a.linearMap (associatedBundleMk G P Y p y) v =
            associatedEquivariantFiberMk hP σ p y rfl (w y)) ↔
          ∃ v : Fin ρ.dimension → ℂ, (s v).val = w) ∧
      (Function.Injective s → ∀ (p : P),
        Function.Injective (fun v : AssociatedVectorFiber hP ρ.representation (projection p) ↦
          fun y : Y ↦ a.linearMap (associatedBundleMk G P Y p y) v)) := by
  let τ := EquivariantStructure.ofFiniteRepresentation (X := Y) ρ
  obtain ⟨f, hf, _⟩ := exists_finiteSectionEvaluation A s
  have hfg : f.IsEquivariant τ σ := by
    intro g y v
    change f.linearMap (g • y) (ρ.representation g v) =
      σ.linearMap g y (f.linearMap y v)
    rw [hf, hf]
    exact hsg g y v
  obtain ⟨e, he⟩ := exists_associatedConstantFiber_iso (Y := Y) hP ρ
  let d := associatedEquivariantHom hP τ σ f hfg
  let a := d.comp e.symm.toHom
  -- Both descents use this very principal point, so no rank-only identification intervenes.
  have ha (p : P) (y : Y) (v : Fin ρ.dimension → ℂ) :
      a.linearMap (associatedBundleMk G P Y p y)
          (associatedVectorFiberMk hP ρ.representation p rfl v) =
        associatedEquivariantFiberMk hP σ p y rfl ((s v).val y) := by
    change d.linearMap _ ((e.linearEquiv _).symm _) = _
    rw [← he p y v, LinearEquiv.symm_apply_apply]
    rw [associatedEquivariantHom_apply, hf]
  refine ⟨a, ha, ?_, ?_⟩
  · -- Every coefficient has unique coordinates at p; the full image is the original family.
    intro p w
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨v, rfl⟩ := (associatedVectorFiberMk_bijective hP ρ.representation p rfl).2 u
      refine ⟨v, funext fun y ↦ ?_⟩
      apply (associatedEquivariantFiberMk_bijective hP σ p y rfl).1
      exact (ha p y v).symm.trans (hu y)
    · rintro ⟨v, rfl⟩
      exact ⟨associatedVectorFiberMk hP ρ.representation p rfl v, fun y ↦ ha p y v⟩
  · -- Faithfulness of the section coordinates gives injectivity over the entire associated fiber.
    intro hs p u v huv
    obtain ⟨u₀, rfl⟩ := (associatedVectorFiberMk_bijective hP ρ.representation p rfl).2 u
    obtain ⟨v₀, rfl⟩ := (associatedVectorFiberMk_bijective hP ρ.representation p rfl).2 v
    apply congrArg (associatedVectorFiberMk hP ρ.representation p rfl)
    apply hs
    apply Subtype.ext
    funext y
    apply (associatedEquivariantFiberMk_bijective hP σ p y rfl).1
    exact (ha p y u₀).symm.trans ((congrFun huv y).trans (ha p y v₀))

end AtiyahSinger
