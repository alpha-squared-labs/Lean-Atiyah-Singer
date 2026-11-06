/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularHomology
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Vanishing for the original algebraic dual cochains

Public module ID: M2089.

Over a field, an algebraic functional on a subspace extends to the whole space.
Consequently, exactness of a chain complex in one degree implies exactness of
its actual algebraic dual in the same degree. This is the vanishing case of the
universal coefficient theorem, applied without replacing the singular complexes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite

universe u

variable (K : Type) [Field K]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Over a field, homology vanishing implies vanishing of the original dual cochain homology. -/
theorem subsingleton_singularCochainDualHomology_of_subsingleton
    (C : ChainComplex (ModuleCat.{u} K) ℕ) (n : ℕ) [Subsingleton (C.homology n)] :
    Subsingleton (((singularCochainDualFunctor K).obj (op C)).homology n) := by
  let D := (singularCochainDualFunctor K).obj (op C)
  have hexact : (C.sc n).Exact :=
    (C.exactAt_iff_isZero_homology n).mpr (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)
  apply ModuleCat.isZero_iff_subsingleton.mp
  apply (D.exactAt_iff_isZero_homology n).mp
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro φ hφ
  change C.X n ⟶ singularCoefficient K at φ
  change C.d ((ComplexShape.down ℕ).prev n) n ≫ φ = 0 at hφ
  change ∃ ψ : C.X ((ComplexShape.down ℕ).next n) ⟶ singularCoefficient K,
    C.d n ((ComplexShape.down ℕ).next n) ≫ ψ = φ
  let d := (C.d n ((ComplexShape.down ℕ).next n)).hom
  -- A dual cocycle vanishes on boundaries, hence on every cycle by exactness.
  have hker : d.ker ≤ φ.hom.ker := by
    intro z hz
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexact z hz
    change φ z = 0
    rw [← hw]
    exact congrArg (fun f ↦ f w) hφ
  -- Factor the functional through the boundary image, then extend it linearly.
  let f : d.range →ₗ[K] singularCoefficient K :=
    (d.ker.liftQ φ.hom hker).comp d.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := f.exists_extend
  refine ⟨ModuleCat.ofHom g, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hvalue := LinearMap.congr_fun hg (d.rangeRestrict z)
  change g (d z) = φ z
  calc
    g (d z) = f (d.rangeRestrict z) := hvalue
    _ = φ z := by
      exact congrArg (d.ker.liftQ φ.hom hker)
        (d.quotKerEquivRange_symm_apply_image z (by exact ⟨z, rfl⟩))

/-- Relative singular homology vanishing over a field also kills the original cohomology. -/
theorem subsingleton_relativeSingularCohomology_of_subsingleton_homology
    {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ)
    [Subsingleton (relativeSingularHomology K A n)] :
    Subsingleton (relativeSingularCohomology K A n) :=
  subsingleton_singularCochainDualHomology_of_subsingleton K (relativeSingularChains K A) n

end AtiyahSinger
