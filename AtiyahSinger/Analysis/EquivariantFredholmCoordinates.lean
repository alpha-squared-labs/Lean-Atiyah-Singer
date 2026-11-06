/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteRepresentationCoefficients
public import AtiyahSinger.Analysis.EquivariantFredholmIndex

/-!
# Evaluating the full Fredholm index in specified finite coordinates

Public module ID: M0508.

Finite kernel and actual quotient coordinates determine the original
representation-valued Fredholm index when they intertwine the given actions.
This applies to graph realizations of the geometric product operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {G E F : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 600000 in
-- Normalize the two finite actions through the supplied, universe-polymorphic quotient coordinates.
/-- Specified equivariant coordinates compute the full original Fredholm index. -/
theorem equivariantFredholmIndex_eq_of_coordinates
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (T : E →L[ℂ] F) (hTg : ∀ g, T.comp (ρ g) = (σ g).comp T) (hT : T.IsFredholm)
    (κ χ : FiniteContinuousRepresentation G)
    (e : (Fin κ.dimension → ℂ) ≃ₗ[ℂ] T.ker)
    (f : (Fin χ.dimension → ℂ) ≃ₗ[ℂ] (F ⧸ T.range))
    (he : ∀ g v, (e (κ.representation g v)).val = ρ g (e v).val)
    (hf : ∀ g v, f (χ.representation g (f.symm (T.range.mkQ v))) = T.range.mkQ (σ g v)) :
    equivariantFredholmIndex ρ σ hρ hσ T hTg hT =
      finiteRepresentationClass κ - finiteRepresentationClass χ := by
  classical
  let : FiniteDimensional ℂ T.ker := hT.finite_ker
  let : FiniteDimensional ℂ (F ⧸ T.range) := hT.finite_coker
  let : IsClosed (T.range : Set F) := hT.isClosed_range
  let RK := equivariantKernelRepresentation ρ σ T hTg
  let RC := equivariantCokernelRepresentation ρ σ T hTg
  have he' (g : G) (v : Fin κ.dimension → ℂ) : e (κ.representation g v) = RK g (e v) :=
    Subtype.ext (he g v)
  have hf' (g : G) (v : Fin χ.dimension → ℂ) : f (χ.representation g v) = RC g (f v) := by
    obtain ⟨w, hw⟩ := T.range.mkQ_surjective (f v)
    have hv : v = f.symm (T.range.mkQ w) := by rw [hw, f.symm_apply_apply]
    rw [hv, hf, f.apply_symm_apply]
    rfl
  -- Normalize both original finite representations before taking their difference.
  change representationClass RK
      (continuous_equivariantKernelRepresentation ρ σ T hTg hρ) -
    representationClass RC
      (continuous_equivariantCokernelRepresentation ρ σ T hTg hσ) = _
  exact congrArg₂ (· - ·)
    (representationClass_eq_finiteRepresentationClass_of_equiv RK
      (continuous_equivariantKernelRepresentation ρ σ T hTg hρ)
      κ e.toContinuousLinearEquiv he')
    (representationClass_eq_finiteRepresentationClass_of_equiv RC
      (continuous_equivariantCokernelRepresentation ρ σ T hTg hσ)
      χ f.toContinuousLinearEquiv hf')

end AtiyahSinger
