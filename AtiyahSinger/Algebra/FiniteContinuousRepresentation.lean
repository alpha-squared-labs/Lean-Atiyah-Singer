/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Finite-dimensional continuous complex representations

Public module ID: M0025.

Finite representations are presented on the fixed models Fin n → ℂ. Besides
mathlib's `ContRepresentation`, joint continuity of the group action is an
explicit field: `ContRepresentation` alone only makes each individual action
operator continuous. Coordinate changes conjugate the actual operators, and
direct sum uses the specified ordered Fin-addition coordinates.

SG III.9, printed pp.211--212, uses finite complex representations to construct
R(G). This file supplies the representations and their actual isomorphisms;
the additive Grothendieck group is constructed separately. No unitarity,
compactness, decomposition into irreducibles or tensor multiplication is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A finite-dimensional complex representation with a jointly continuous action. -/
structure FiniteContinuousRepresentation where
  /-- Dimension of the specified standard complex vector space. -/
  dimension : ℕ
  /-- The actual linear group action on that standard model. -/
  representation : ContRepresentation ℂ G (Fin dimension → ℂ)
  /-- Continuity in both the group element and vector, not just in the vector. -/
  continuous_action :
    Continuous (fun p : G × (Fin dimension → ℂ) ↦ representation p.1 p.2)

namespace FiniteContinuousRepresentation

variable {G}

/-- Two finite presentations are isomorphic by an actual continuous linear intertwiner. -/
def IsEquivalent (ρ σ : FiniteContinuousRepresentation G) : Prop :=
  Nonempty (ContRepresentation.Equiv ρ.representation σ.representation)

/-- Present an original action in explicitly supplied continuous linear coordinates. -/
def ofEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ρ : ContRepresentation ℂ G E)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    {n : ℕ} (e : E ≃L[ℂ] (Fin n → ℂ)) : FiniteContinuousRepresentation G where
  dimension := n
  representation :=
    .ofMonoidHom (e.conjContinuousAlgEquiv.toMonoidHom.comp ρ.toMonoidHom)
  continuous_action :=
    e.continuous.comp (hρ.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))

/-- The ordered direct sum, expressed in the fixed Fin-addition coordinates. -/
def directSum (ρ σ : FiniteContinuousRepresentation G) : FiniteContinuousRepresentation G :=
  let e : (Fin (ρ.dimension + σ.dimension) → ℂ) ≃L[ℂ]
      (Fin ρ.dimension → ℂ) × (Fin σ.dimension → ℂ) :=
    (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin ρ.dimension ⊕ Fin σ.dimension ↦ ℂ)
      finSumFinEquiv.symm).trans
      (ContinuousLinearEquiv.sumPiEquivProdPi ℂ (Fin ρ.dimension) (Fin σ.dimension) (fun _ ↦ ℂ))
  let τ : ContRepresentation ℂ G ((Fin ρ.dimension → ℂ) × (Fin σ.dimension → ℂ)) :=
    .ofMonoidHom
      { toFun := fun g ↦ (ρ.representation g).prodMap (σ.representation g)
        map_one' := by
          ext x <;> simp
        map_mul' := by
          intro g h
          ext x <;> simp [map_mul] }
  ofEquiv τ
    ((ρ.continuous_action.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      (σ.continuous_action.comp (continuous_fst.prodMk continuous_snd.snd))) e.symm

end FiniteContinuousRepresentation

end AtiyahSinger
