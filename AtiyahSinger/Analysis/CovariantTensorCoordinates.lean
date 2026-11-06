/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.IteratedCovariantDerivative
public import AtiyahSinger.Geometry.TensorContraction

/-!
# Coordinate contraction of the original covariant tensors

Public module ID: M0428.

The original recursively defined pairing can be evaluated in any tangent
basis together with its actual dual basis. This supplies the algebraic part
of the atlas/native covariant norm comparison without imposing new metrics
or norms on the original Hom fibers. Sources: SG III.2 (2.1), expanded using
the standard full tensor contraction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Module
open scoped BigOperators Manifold ContDiff

set_option maxSynthPendingDepth 40

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "TM" => TangentSpace I (M := M)

/-- Any tangent basis and its dual compute one slot of the original full tensor metric.
The value pairing in all remaining slots is the unchanged native recursive pairing. -/
theorem iteratedCovariantPairing_succ_re_eq_sum_basis
    (g : SmoothCotangentMetric (n := n) (M := M))
    (h : SmoothHermitianMetric (n := n) (r := r) E) (k : ℕ) (x : M)
    (b : Basis (Fin n) ℝ (TM x))
    (a d : TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E k x) :
    (iteratedCovariantPairing g h (k + 1) x a d).re =
      ∑ i : Fin n, ∑ j : Fin n,
        g.inner x (LinearMap.toContinuousLinearMap (b.coord i))
          (LinearMap.toContinuousLinearMap (b.coord j)) *
        (iteratedCovariantPairing g h k x (a (b i)) (d (b j))).re := by
  classical
  let p (i : Fin n) : CotangentFiber (n := n) x := EuclideanSpace.proj i
  let t (i : Fin n) : TM x := EuclideanSpace.single i 1
  have hrec (j : ℕ)
      (u v : TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E j x) :
      (iteratedCovariantPairing g h (j + 1) x u v).re =
        ∑ i : Fin n, ∑ l : Fin n,
          g.inner x (p i) (p l) * (iteratedCovariantPairing g h j x (u (t i)) (v (t l))).re := by
    change (∑ i : Fin n, ∑ l : Fin n,
      (g.inner x (p i) (p l) : ℂ) * iteratedCovariantPairing g h j x (u (t i)) (v (t l))).re = _
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  -- Every remaining-slot pairing is real bilinear on the actual native tensor fiber.
  have hform (j : ℕ) :
      ∃ B : LinearMap.BilinForm ℝ (CovariantTensorFiber (n := n) (r := r) E j x),
        ∀ u v, B u v = (iteratedCovariantPairing g h j x u v).re := by
    induction j with
    | zero =>
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      let P : E x →ₗ[ℝ] E x →ₗ[ℝ] ℂ :=
        LinearMap.mk₂ ℝ (h.pairing x)
          (fun u v w ↦ (h.toCore x).add_left u v w)
          (by
            intro c u v
            change (h.toCore x).inner (c • u) v = c • (h.toCore x).inner u v
            rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
              InnerProductSpace.Core.inner_smul_ofReal_left]
            simp [Algebra.smul_def, mul_comm])
          (fun u v w ↦ InnerProductSpace.Core.inner_add_right u v w)
          (by
            intro c u v
            change (h.toCore x).inner u (c • v) = c • (h.toCore x).inner u v
            rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
              InnerProductSpace.Core.inner_smul_ofReal_right]
            simp [Algebra.smul_def, mul_comm])
      exact ⟨P.compr₂ Complex.reLm, fun _ _ ↦ rfl⟩
    | succ j ih =>
      obtain ⟨B, hB⟩ := ih
      let C : LinearMap.BilinForm ℝ
          (TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E j x) :=
        LinearMap.mk₂ ℝ
          (fun u v ↦ ∑ i : Fin n, ∑ l : Fin n,
            g.inner x (p i) (p l) *
              B (u (t i)) (v (t l)))
          (by
            intro u v w
            simp only [add_apply, map_add, LinearMap.add_apply,
              mul_add, Finset.sum_add_distrib])
          (by
            intro c u v
            simp only [smul_apply, map_smul, LinearMap.smul_apply,
              smul_eq_mul, mul_left_comm _ c, Finset.mul_sum])
          (by
            intro u v w
            simp only [add_apply, map_add, mul_add,
              Finset.sum_add_distrib])
          (by
            intro c u v
            simp only [smul_apply, map_smul, smul_eq_mul,
              mul_left_comm _ c, Finset.mul_sum])
      refine ⟨C, ?_⟩
      change ∀ u v : TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E j x,
        C u v = (iteratedCovariantPairing g h (j + 1) x u v).re
      intro u v
      change (∑ i : Fin n, ∑ l : Fin n,
          g.inner x (p i) (p l) *
            B (u (t i)) (v (t l))) = _
      simp only [hB, hrec]
  obtain ⟨B, hB⟩ := hform k
  -- Apply basis independence to the same maps, with the given cotangent bilinear form.
  let Gc : LinearMap.BilinForm ℝ (CotangentFiber (n := n) x) :=
    (ContinuousLinearMap.coeLM ℝ).comp (g.inner x).toLinearMap
  let G : LinearMap.BilinForm ℝ (Module.Dual ℝ (TM x)) :=
    Gc.compl₁₂ LinearMap.toContinuousLinearMap.toLinearMap
      LinearMap.toContinuousLinearMap.toLinearMap
  let e : Basis (Fin n) ℝ (TM x) := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have he (i : Fin n) : LinearMap.toContinuousLinearMap (e.coord i) =
      p i := by
    ext v
    rfl
  have heval (i : Fin n) : e i = t i := by
    exact EuclideanSpace.basisFun_apply (Fin n) ℝ i
  have hGeval (v w : Module.Dual ℝ (TM x)) : G v w =
      g.inner x (LinearMap.toContinuousLinearMap v) (LinearMap.toContinuousLinearMap w) := rfl
  have hinv := sum_tensor_pairing_basis_eq e b G B a.toLinearMap d.toLinearMap
  simpa only [hGeval, he, heval, hB, ContinuousLinearMap.coe_coe,
    hrec] using hinv

end AtiyahSinger
