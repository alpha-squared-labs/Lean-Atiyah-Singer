/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationGrothendieckGroup

/-!
# Finite representations from separating continuous coefficients

Public module ID: M0026.

A finite-dimensional algebraic representation admits its actual continuous
finite coordinates if a separating family of linear coefficients is continuous
on each orbit. The proof uses the Hausdorff product topology of the coefficients
and finite-basis reconstruction for joint continuity. This standard finite
dimensional fact is used for the original smooth kernel and quotient-cokernel;
it requires neither an invariant inner product nor a topology on their ambient
infinite-dimensional section spaces.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- Separating continuous matrix coefficients give an actual finite continuous presentation. -/
theorem exists_finiteContinuousRepresentation_of_coefficients
    {G W I : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (R : Representation ℂ G W) (J : W →ₗ[ℂ] (I → ℂ)) (hJ : Function.Injective J)
    (hcoeff : ∀ (i : I) (w : W), Continuous (fun g : G ↦ J (R g w) i)) :
    ∃ ρ : FiniteContinuousRepresentation G,
      ∃ e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] W,
        ∀ (g : G) (v : Fin ρ.dimension → ℂ), e (ρ.representation g v) = R g (e v) := by
  classical
  let d := Module.finrank ℂ W
  let e : (Fin d → ℂ) ≃ₗ[ℂ] W := (Module.finBasis ℂ W).equivFun.symm
  let S : Representation ℂ G (Fin d → ℂ) :=
    { toFun := fun g ↦ e.symm.toLinearMap.comp ((R g).comp e.toLinearMap)
      map_one' := by
        ext v
        simp
      map_mul' := by
        intro g h
        ext v
        simp [map_mul] }
  -- The coefficient map embeds the finite model into a Hausdorff product space.
  let L := J.comp e.toLinearMap
  have hL : Function.Injective L := hJ.comp e.injective
  have horbit (v : Fin d → ℂ) : Continuous (fun g : G ↦ S g v) := by
    apply (L.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hL)).isEmbedding
      |>.continuous_iff.mpr
    change Continuous (fun g ↦ J (e (e.symm (R g (e v)))))
    simp only [LinearEquiv.apply_symm_apply]
    apply continuous_pi
    intro i
    exact hcoeff i (e v)
  -- A finite basis turns orbit continuity into continuity in the vector as well.
  have hjoint : Continuous (fun p : G × (Fin d → ℂ) ↦ S p.1 p.2) := by
    have hsum : Continuous (fun p : G × (Fin d → ℂ) ↦
        ∑ i : Fin d, p.2 i • S p.1 (Pi.single i 1)) := by
      apply continuous_finsetSum
      intro i _
      exact ((continuous_apply i).comp continuous_snd).smul
        ((horbit (Pi.single i 1)).comp continuous_fst)
    apply hsum.congr
    intro p
    simp_rw [← (S p.1).map_smul]
    rw [← map_sum]
    congr 1
    ext i
    simp [Pi.single_apply]
  let ρ : FiniteContinuousRepresentation G :=
    { dimension := d
      representation := .ofMonoidHom
        { toFun := fun g ↦ (S g).toContinuousLinearMap
          map_one' := by
            apply ContinuousLinearMap.ext
            intro v
            exact congrArg (fun T ↦ T v) S.map_one
          map_mul' := by
            intro g h
            apply ContinuousLinearMap.ext
            intro v
            exact congrArg (fun T ↦ T v) (S.map_mul g h) }
      continuous_action := hjoint }
  refine ⟨ρ, e, ?_⟩
  intro g v
  exact e.apply_symm_apply (R g (e v))

/-- Specified equivariant finite coordinates identify the original representation class. -/
theorem representationClass_eq_finiteRepresentationClass_of_equiv
    {G W : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (S : ContRepresentation ℂ G W) (hS : Continuous (fun p : G × W ↦ S p.1 p.2))
    (χ : FiniteContinuousRepresentation G) (c : (Fin χ.dimension → ℂ) ≃L[ℂ] W)
    (hc : ∀ g v, c (χ.representation g v) = S g (c v)) :
    representationClass S hS = finiteRepresentationClass χ := by
  -- Use these same coordinates, then identify the two actions by the identity intertwiner.
  rw [representationClass_ofEquiv S hS c.symm]
  apply finiteRepresentationClass_eq_of_isEquivalent
  refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
  intro g
  apply ContinuousLinearMap.ext
  intro v
  change Fin χ.dimension → ℂ at v
  change c.symm (S g (c v)) = χ.representation g v
  exact (congrArg c.symm (hc g v)).symm.trans (c.symm_apply_apply _)

end AtiyahSinger
