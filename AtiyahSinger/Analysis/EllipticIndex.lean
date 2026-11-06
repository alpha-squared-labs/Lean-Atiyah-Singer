/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EllipticCokernel

import AtiyahSinger.Analysis.PseudodifferentialAdjointCokernel

/-!
# The Sobolev index equals the smooth analytic index

Public module ID: M0449.

A07: SG III.5.2(ii), (5.1)-(5.2), and Corollary 5.3. The natural kernel and
cokernel comparisons identify the index of each real-order bounded realization
with the index of the original smooth section map. This implies independence of
Sobolev order and of finite presentations. The bilinear transpose formula is
metric-free; the separate Hermitian section states smooth weak-adjoint regularity,
the actual quotient map, and the formal-adjoint index formula.
The proofs retain the original differential section map and every specified
Sobolev presentation. The Hermitian formulas use the PDO comparison for the same smooth operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

namespace DifferentialOperator

variable {m : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- SG III.5.3: every bounded Sobolev realization has the original smooth analytic index. -/
theorem index_sobolevExtension_eq_analyticIndex (hP : P.IsElliptic) (s : ℝ) :
    (P.sobolevExtension A B s).index = P.analyticIndex hP := by
  /- Stage 1: the bounded realization is Fredholm. Its kernel and cokernel have
  finite dimension and are identified with the smooth kernel and cokernel by the
  natural equivalences. Finiteness transfers to the latter spaces.
  Stage 2: apply the kernel-minus-cokernel formula to both actual linear maps.
  Substitute the two dimension comparisons. The right side is the existing
  algebraic analyticIndex of P.toLinearMap, not a newly chosen Sobolev index. -/
  -- The natural kernel and cokernel comparisons refer to the same differential map.
  rw [LinearMap.index_eq_finrank_sub, P.analyticIndex_eq_finrank_sub hP,
    P.finrank_ker_sobolevExtension μ A B hP s,
    P.finrank_coker_sobolevExtension μ A B hP s]

/-- SG III.5.2(ii): changing real Sobolev order and finite presentations preserves the index. -/
theorem index_sobolevExtension_eq (hP : P.IsElliptic)
    (A' : SmoothBundlePresentation (n := n) (r := r) E)
    (B' : SmoothBundlePresentation (n := n) (r := q) F) (s t : ℝ) :
    (P.sobolevExtension A B s).index = (P.sobolevExtension A' B' t).index := by
  /- Compare each side with the same smooth analyticIndex using the preceding
  theorem. The two Sobolev spaces may have different orders and different norms;
  no equality of their carriers or operator-norm-continuous path is assumed.
  The equality also uses no fiber metric, since neither displayed map requires one. -/
  -- Both realizations compute the index of the same original smooth map.
  rw [P.index_sobolevExtension_eq_analyticIndex μ A B hP s,
    P.index_sobolevExtension_eq_analyticIndex μ A' B' hP t]

/-- SG (5.2) in its metric-free convention: use the actual bilinear formal transpose. -/
theorem analyticIndex_eq_finrank_ker_sub_finrank_ker_formalTranspose (hP : P.IsElliptic) :
    P.analyticIndex hP = (Module.finrank ℂ P.toLinearMap.ker : ℤ) -
      Module.finrank ℂ (P.formalTranspose μ).ker := by
  /- Choose finite Sobolev presentations and one real order. Express the bounded
  Fredholm index as kernel dimension minus cokernel dimension. The kernel
  comparison and the opposite-order transpose comparison identify both terms
  with the displayed smooth kernels. Finally apply the Sobolev/smooth index equality.
  This is the convention on E* and F* in SG (5.1)-(5.2), with no Hermitian choice. -/
  -- Choose presentations only to invoke the proved natural comparisons.
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  rw [← P.index_sobolevExtension_eq_analyticIndex μ A B hP 0,
    LinearMap.index_eq_finrank_sub, P.finrank_ker_sobolevExtension μ A B hP 0,
    P.finrank_coker_eq_finrank_ker_formalTranspose μ A B hP 0]

end DifferentialOperator

end AtiyahSinger

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  [hEH : IsSmoothHermitianBundle (n := n) (r := r) E]
  [hFH : IsSmoothHermitianBundle (n := n) (r := q) F]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hEH hFH hμ

namespace DifferentialOperator

variable {m : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The opposite-order weak Hermitian formal-adjoint kernel consists of smooth sections. -/
theorem existsUnique_smooth_of_sobolevFormalAdjoint_eq_zero (hP : P.IsElliptic)
    (s : ℝ) (v : B.SobolevSpace (-(s - m)))
    (hv : P.sobolevFormalAdjoint μ A B s v = 0) :
    ∃! w : smoothSections (n := n) (r := q) F,
      B.smoothToSobolev (-(s - m)) w = v ∧ (P.formalAdjoint μ).toLinearMap w = 0 := by
  /- Stage 1: the specified Hermitian Sobolev duality converts the weak adjoint
  equation into the weak transpose equation. Elliptic transpose regularity gives
  its smooth covector representative; inverse metric duality yields the same v.
  Stage 2: the smooth extension identity and injectivity of the embedding show
  that its differential adjoint image is zero and establish uniqueness. -/
  -- Metric duality carries the specified weak adjoint zero to a weak transpose zero.
  have htrans : P.sobolevTranspose μ A B s
      (B.sobolevHermitianDual (-(s - m)) v) = 0 := by
    rw [P.sobolevTranspose_hermitian, hv, map_zero]
  obtain ⟨β, hβ, _⟩ := P.existsUnique_smooth_of_sobolevTranspose_eq_zero
    μ A B hP s (B.sobolevHermitianDual (-(s - m)) v) htrans
  let w := (smoothHermitianDualEquiv F).symm β
  have hw : B.smoothToSobolev (-(s - m)) w = v := by
    apply (B.sobolevHermitianDual (-(s - m))).injective
    rw [B.sobolevHermitianDual_smooth]
    simpa only [w, LinearEquiv.apply_symm_apply] using hβ.1
  -- The original adjoint action and faithful embedding identify the same smooth zero.
  have hPw : (P.formalAdjoint μ).toLinearMap w = 0 := by
    apply A.smoothToSobolev_injective (-s)
    rw [map_zero, ← P.sobolevFormalAdjoint_smooth, hw]
    exact hv
  refine ⟨w, ⟨hw, hPw⟩, ?_⟩
  intro z hz
  exact B.smoothToSobolev_injective (-(s - m)) (hz.1.trans hw.symm)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The smooth formal-adjoint kernel maps bijectively to the actual Sobolev cokernel. -/
theorem bijective_ker_formalAdjoint_to_sobolevCoker (hP : P.IsElliptic) (s : ℝ) :
    Function.Bijective
      ((P.sobolevExtension A B s).range.mkQ.comp
        ((B.smoothToSobolev (s - m)).comp (P.formalAdjoint μ).toLinearMap.ker.subtype)) := by
  /- Stage 1: a differential parametrix applies to its actual PDO realization.
  The proved PDO adjoint-kernel quotient comparison then gives bijectivity on
  smooth sections, since the two formal adjoints have exactly the same section map.
  Stage 2: compose with the natural Sobolev cokernel equivalence. Its class formula
  gives precisely the displayed quotient map at the original target order. -/
  -- The PDO realization and its differential source share both actual smooth maps.
  obtain ⟨Q, hQ⟩ := P.exists_parametrix μ hP
  have hadj := P.formalAdjoint_eq_of_toLinearMap_eq
    (P.toPseudodifferentialOperator μ) rfl
  have hbij := PseudodifferentialOperator.bijective_ker_formalAdjoint_to_coker_of_isParametrix
    (P.toPseudodifferentialOperator μ) A B Q hQ
  rw [hadj] at hbij
  -- Compose the natural smooth quotient map with the natural Sobolev quotient equivalence.
  let e := P.sobolevCokerEquiv μ A B hP s
  have hmaps : (P.sobolevExtension A B s).range.mkQ.comp
      ((B.smoothToSobolev (s - m)).comp (P.formalAdjoint μ).toLinearMap.ker.subtype) =
      e.toLinearMap.comp
        (P.toLinearMap.range.mkQ.comp (P.formalAdjoint μ).toLinearMap.ker.subtype) := by
    ext v
    exact (P.sobolevCokerMap_mkQ μ A B s v.val).symm
  rw [hmaps]
  exact e.bijective.comp hbij

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Every Sobolev index has the familiar two smooth Hermitian-kernel expression. -/
theorem index_sobolevExtension_eq_finrank_ker_sub_finrank_ker_formalAdjoint
    (hP : P.IsElliptic) (s : ℝ) :
    (P.sobolevExtension A B s).index = (Module.finrank ℂ P.toLinearMap.ker : ℤ) -
      Module.finrank ℂ (P.formalAdjoint μ).toLinearMap.ker := by
  /- Use the Hermitian index formula for the original PDO realization and its
  actual differential parametrix. The differential and PDO Sobolev extensions
  agree on every specified presentation, and uniqueness of the integral adjoint
  identifies their smooth adjoint kernels. The comparison keeps the original metrics and
  density. -/
  -- Use one two-sided parametrix of the original differential section map.
  obtain ⟨Q, hQ⟩ := P.exists_parametrix μ hP
  have hindex := (P.toPseudodifferentialOperator μ)
    |>.index_sobolevExtension_eq_finrank_ker_sub_finrank_ker_formalAdjoint_of_isParametrix
      A B Q hQ s
  -- The two adjoints agree as actual maps by their common integral characterization.
  rw [P.sobolevExtension_toPseudodifferentialOperator μ A B s,
    P.formalAdjoint_eq_of_toLinearMap_eq (P.toPseudodifferentialOperator μ) rfl] at hindex
  exact hindex

end DifferentialOperator

end AtiyahSinger
