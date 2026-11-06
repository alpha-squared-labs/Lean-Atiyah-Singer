/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentNormalBundle
public import AtiyahSinger.Topology.BottEuclidean
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The specified Bott coordinate on the tangent bundle of Euclidean space

Public module ID: M1827.

The actual tangent bundle of real Euclidean n-space is sent to complex n-space
by (x,v) mapped to x + I*v, with base coordinates first and tangent coordinates
second. This is SG III.12's ordered complex structure and the identification
used before Definition III.13.1. The integer coordinate then uses the existing
positive Bott equivalence, rather than choosing an abstract generator of Kc.

Both constructions preserve the native tangent topology. No stabilization or
embedding independence is claimed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped ContDiff Manifold

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold

/-- The original Euclidean tangent space in ordered base-plus-imaginary-tangent coordinates. -/
def euclideanTangentComplexHomeomorph (n : ℕ) :
    TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ≃ₜ
      (Fin n → ℂ) := by
  let e : EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ) :=
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).toHomeomorph
  let c : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ≃ₜ (Fin n → ℂ) :=
    { toFun := fun p i ↦ Complex.equivRealProdCLM.symm (e p.1 i, e p.2 i)
      invFun := fun z ↦ (e.symm (fun i ↦ (z i).re), e.symm (fun i ↦ (z i).im))
      left_inv := fun p ↦ by
        apply Prod.ext
        · simp
        · simp
      right_inv := fun z ↦ by
        funext i
        apply Complex.ext <;> simp
      continuous_toFun := continuous_pi fun i ↦
        Complex.equivRealProdCLM.symm.continuous.comp
          (((continuous_apply i).comp (e.continuous.comp continuous_fst)).prodMk
            ((continuous_apply i).comp (e.continuous.comp continuous_snd)))
      continuous_invFun :=
        (e.symm.continuous.comp (continuous_pi fun i ↦
          Complex.continuous_re.comp (continuous_apply i))).prodMk
        (e.symm.continuous.comp (continuous_pi fun i ↦
          Complex.continuous_im.comp (continuous_apply i))) }
  exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))).trans c

/-- The integer Bott coordinate using the actual Euclidean tangent map and positive Bott class. -/
def euclideanTangentKZeroEquivInt (n : ℕ) :
    letI := (tangentBundle_topology (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))).1
    letI := ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    CompactSupportKZero
      (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) ≃+ ℤ := by
  letI := (tangentBundle_topology (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin n))).1
  letI := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
  exact (compactSupportKZeroHomeomorphEquiv (euclideanTangentComplexHomeomorph n)).trans
    (bottEuclideanClassEquivInt n)

end AtiyahSinger
