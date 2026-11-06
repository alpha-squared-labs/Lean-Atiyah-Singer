/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexConnection
public import AtiyahSinger.Geometry.CotangentMetric

/-!
# Smooth Clifford modules and contraction with a covariant derivative

Public module ID: M1385.

S02. On the supplied finite-rank complex vector bundle, this structure
records a real-linear cotangent action whose square is minus the metric.
Its smoothness fields require both the original smooth bundle transitions
and the Clifford action in those same supplied charts.
This is the usual Clifford-module structure, expressed by its generators
and quadratic relation, rather than a new assumed differential operator.
Smoothness is tested in the original manifold and bundle charts, with the
cotangent variable pulled back by the derivative of the manifold chart.

The contraction is an actual finite sum on the original tangent fiber and
its continuous dual. Its raw model basis need not be a smooth global frame;
basis independence permits checking the sum in genuine smooth local frames.
There is no orientation, spin lift, Hermitian compatibility or compactness
assumption. The construction applies in every dimension, including zero.

Source: Lawson--Michelsohn, Spin Geometry, II.5 (5.0) and Lemma 5.1,
pp.112--113. A smooth Clifford module alone is not the stronger Dirac bundle
of Definition 5.2; that definition also imposes metric and connection
compatibility. The canonical tangent spin realization remains separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  (E : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (g : SmoothCotangentMetric (n := n) (M := M))

/-- A smooth complex module over the real cotangent Clifford algebra for the given metric. -/
structure SmoothCliffordModule where
  /-- The cotangent argument is real linear and each action is complex linear. -/
  clifford : ∀ x : M, CotangentFiber (n := n) x →ₗ[ℝ] Module.End ℂ (E x)
  /-- The negative Clifford convention uses the same supplied cotangent metric. -/
  clifford_sq (x : M) (ξ : CotangentFiber (n := n) x) (v : E x) :
    clifford x ξ (clifford x ξ v) = -(g.inner x ξ ξ : ℂ) • v
  /-- In original charts, the actual pulled-back cotangent action is jointly smooth. -/
  contDiffOn_clifford
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e]
      (v : EuclideanSpace ℂ (Fin r)) :
    ContDiffOn ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        e.linearMapAt ℂ (c.symm z.1)
          (clifford (c.symm z.1)
            ((innerSL ℝ z.2).comp
              (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c (c.symm z.1)))
            (e.symmL ℂ (c.symm z.1) v)))
      ((c.target ∩ c.symm ⁻¹' e.baseSet) ×ˢ Set.univ)
  /-- The original complex-linear bundle atlas has real-smooth transition maps. -/
  isSmoothBundle : IsSmoothComplexBundle (n := n) (r := r) E

namespace SmoothCliffordModule

variable {E g} (C : SmoothCliffordModule (n := n) (r := r) E g)

/-- Contract an E-valued one-form by the actual Clifford multiplication. -/
def contract (x : M)
    (a : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] E x) : E x :=
  ∑ j : Fin n, C.clifford x (EuclideanSpace.proj j) (a (EuclideanSpace.single j 1))

/-- The contraction has the same value in every basis and its genuine dual basis. -/
theorem contract_eq_sum_basis (x : M)
    (a : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] E x)
    (b : Module.Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) :
    C.contract x a =
      ∑ j : Fin n, C.clifford x (b.coord j).toContinuousLinearMap (a (b j)) := by
  /- Stage 1: expand the vectors of b and their dual covectors in the raw
  model basis and dual basis. Continuity of all these linear maps follows
  from finite dimensionality; no moving basis is asserted to be smooth.
  Stage 2: real linearity of the cotangent action and a, together with
  complex linearity of each action, allows exchanging the finite sums.
  The inverse change-of-basis matrices cancel, leaving exactly contract.
  Thus a genuine local smooth frame may be used to analyze the same sum. -/
  change EuclideanSpace ℝ (Fin n) →L[ℝ] E x at a
  change Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) at b
  let c : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →ₗ[ℝ] Module.End ℂ (E x) := C.clifford x
  change (∑ j : Fin n, c (EuclideanSpace.proj j) (a (EuclideanSpace.single j 1))) =
    ∑ j : Fin n, c (b.coord j).toContinuousLinearMap (a (b j))
  -- Expand each genuine dual covector in the original coordinate covectors.
  have hraw (v : EuclideanSpace ℝ (Fin n)) :
      ∑ k : Fin n, EuclideanSpace.proj k v • EuclideanSpace.single k 1 = v := by
    simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr,
      EuclideanSpace.proj, PiLp.proj_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  have hdual (j : Fin n) : (b.coord j).toContinuousLinearMap =
      ∑ k : Fin n, b.coord j (EuclideanSpace.single k 1) • EuclideanSpace.proj k := by
    ext v
    simp only [sum_apply, smul_apply, smul_eq_mul]
    conv_lhs => rw [← hraw v]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  -- Exchange the finite sums and recombine each column using the same basis b.
  symm
  calc
    _ = ∑ j : Fin n, ∑ k : Fin n,
        b.coord j (EuclideanSpace.single k 1) •
          c (EuclideanSpace.proj k) (a (b j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hdual j, map_sum]
      simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
    _ = ∑ k : Fin n, ∑ j : Fin n,
        b.coord j (EuclideanSpace.single k 1) •
          c (EuclideanSpace.proj k) (a (b j)) := Finset.sum_comm
    _ = ∑ k : Fin n, c (EuclideanSpace.proj k)
        (a (∑ j : Fin n, b.coord j (EuclideanSpace.single k 1) • b j)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [map_sum, map_smul, LinearMap.map_smul_of_tower]
    _ = ∑ k : Fin n, c (EuclideanSpace.proj k) (a (EuclideanSpace.single k 1)) := by
      simp only [Module.Basis.coord_apply, b.sum_repr]

end SmoothCliffordModule

end AtiyahSinger
