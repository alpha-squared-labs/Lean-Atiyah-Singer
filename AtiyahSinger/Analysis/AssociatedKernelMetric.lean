/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantL2
public import AtiyahSinger.Analysis.GlobalPseudodifferentialOperator
public import AtiyahSinger.Geometry.AssociatedRepresentationMetric
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# The original integral metric on an associated full-kernel representation

Public module ID: M0101.

The specified finite coordinates of the full smooth sphere kernel inherit
exactly its given integral inner product. The original unitary L2 action proves
invariance of that same Gram form. It therefore descends to a smooth metric on
the actual associated coefficient bundle, with the full integral pairing at
every specified principal representative. This applies to the original sphere
operator and to its actual metric formal adjoint without changing either kernel.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (F F' : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)

variable
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber)
  (hσ : σ.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r))
  (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
  (hk : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ (g : Matrix.orthogonalGroup (Fin r) ℝ) (y : OrthogonalSphere r) (u v : F.Fiber y),
      k.pairing (g • y) (σ.linearMap g y u) (σ.linearMap g y v) = k.pairing y u v)
  (ν : Measure (OrthogonalSphere r)) [IsSmoothPositiveMeasure (n := r) ν]
  (hν : ∀ g : Matrix.orthogonalGroup (Fin r) ℝ,
    Measure.map (fun y : OrthogonalSphere r ↦ g • y) ν = ν)

include hk hν in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 800000 in
-- Descend the original integral kernel pairing through the same associated representation.
/-- The same full sphere-kernel representation has its original integral associated metric. -/
theorem PseudodifferentialOperator.exists_associatedKernelMetric {d : ℝ}
    (Q : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν d)
    (ρ : FiniteContinuousRepresentation G)
    (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] Q.toLinearMap.ker)
    (he : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ (g : G) (v : Fin ρ.dimension → ℂ),
        (e (ρ.representation g v)).val = σ.smoothSectionRepresentation IG hσ g (e v).val) :
    ∃ c : InnerProductSpace.Core ℂ (Fin ρ.dimension → ℂ),
      Continuous (fun z : (Fin ρ.dimension → ℂ) × (Fin ρ.dimension → ℂ) ↦
        c.inner z.1 z.2) ∧
      (∀ (g : G) (u v : Fin ρ.dimension → ℂ),
        c.inner (ρ.representation g u) (ρ.representation g v) = c.inner u v) ∧
      (∀ u v, c.inner u v = ∫ y, k.pairing y ((e u).val.val y) ((e v).val.val y) ∂ν) ∧
      ∃ l : ContinuousHermitianMetric
          (AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation),
        (associatedOrthogonalRepresentationAtlas S ρ).IsSmoothHermitianMetric l ∧
        ∀ (p : P) (b : B) (hp : projection p = b) (u v : Fin ρ.dimension → ℂ),
          (l.toCore b).inner
            (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp u)
            (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp v) =
              ∫ y, k.pairing y ((e u).val.val y) ((e v).val.val y) ∂ν := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let j := (k.smoothToL2 ν).comp (Q.toLinearMap.ker.subtype.comp e.toLinearMap)
  have hj : Function.Injective j :=
    (k.smoothToL2_injective ν).comp (Subtype.val_injective.comp e.injective)
  -- Pull back the actual completion inner product along the full kernel inclusion.
  let c : InnerProductSpace.Core ℂ (Fin ρ.dimension → ℂ) := {
    inner u v := inner ℂ (j u) (j v)
    conj_inner_symm u v := inner_conj_symm _ _
    re_inner_nonneg u := inner_self_nonneg
    add_left u v w := by rw [j.map_add, inner_add_left]
    smul_left u v a := by rw [j.map_smul, inner_smul_left]
    definite u hu := hj ((inner_self_eq_zero.mp hu).trans j.map_zero.symm) }
  have hcontinuous : Continuous (fun z : (Fin ρ.dimension → ℂ) ×
      (Fin ρ.dimension → ℂ) ↦ c.inner z.1 z.2) :=
    (j.continuous_of_finiteDimensional.comp continuous_fst).inner
      (j.continuous_of_finiteDimensional.comp continuous_snd)
  let R := k.l2IsometryRepresentation ν IG σ hσ hk hν
  have haction (g : G) (u : Fin ρ.dimension → ℂ) :
      j (ρ.representation g u) = R g (j u) := by
    change k.smoothToL2 ν (e (ρ.representation g u)).val =
      R g (k.smoothToL2 ν (e u).val)
    rw [he]
    exact (k.l2IsometryRepresentation_smoothToL2 ν IG σ hσ hk hν g (e u).val).symm
  have hinv (g : G) (u v : Fin ρ.dimension → ℂ) :
      c.inner (ρ.representation g u) (ρ.representation g v) = c.inner u v := by
    change inner ℂ (j (ρ.representation g u)) (j (ρ.representation g v)) = _
    rw [haction, haction]
    exact (R g).inner_map_map (j u) (j v)
  have hpair (u v : Fin ρ.dimension → ℂ) :
      c.inner u v = ∫ y, k.pairing y ((e u).val.val y) ((e v).val.val y) ∂ν :=
    k.inner_smoothToL2 ν (e u).val (e v).val
  -- Descend this same integral Gram form on every original principal representative.
  obtain ⟨l, hl, hrepresentative⟩ :=
    exists_associatedRepresentationMetric S ρ c hcontinuous hinv
  refine ⟨c, hcontinuous, hinv, hpair, l, hl, ?_⟩
  intro p b hp u v
  exact (hrepresentative p b hp u v).trans (hpair u v)

end AtiyahSinger
