/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalTranspose
public import AtiyahSinger.Analysis.Parametrix

/-!
# Transpose calculus and the exchange of parametrix errors

Public module ID: M0638.

Consequences of the bilinear pairing identity in SG III.(3.18),
the global transpose theorem 3.17(iv), and the parametrix identities in III.4.
Composition reverses the actual bundle directions. A right smoothing error for P
becomes a left smoothing error for its transpose; no dual of a dual is identified
with the original bundle. The algebraic pairing identities precede the analytic
smoothing transfer. The identity and smoothing-error formulas are proved below;
the PDO composition formula uses the actual global composition theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F G : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin k)) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin k)) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin k)) G]
  [MeasurableSpace M] {μ : Measure M}

/-- The identity on dual sections has exactly the identity pairing. -/
theorem isFormalTranspose_id :
    IsFormalTranspose (n := n) (r := r) (q := r) (E := E) (F := E) μ
      LinearMap.id LinearMap.id := by
  /- Both sides of the defining identity are the same integral of evaluation.
  No integrability, compactness, or nondegeneracy assertion is needed here. -/
  intro α u
  rfl

/-- Two pairing identities compose with the covector maps in the reverse order. -/
theorem IsFormalTranspose.comp
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (R : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := k) G)
    (T : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
      smoothSections (n := n) (r := r) (DualBundle E))
    (U : smoothSections (n := n) (r := k) (DualBundle G) →ₗ[ℂ]
      smoothSections (n := n) (r := q) (DualBundle F))
    (hT : IsFormalTranspose μ P T) (hU : IsFormalTranspose μ R U) :
    IsFormalTranspose μ (R.comp P) (T.comp U) := by
  /- Pair T(U α) with u. First apply hT to U α and u, then hU to α and P u.
  The result is the pairing of α with R(P u). This is substitution in two
  integral equalities, so no analytic assumptions beyond their meaning are used. -/
  intro α u
  exact (hT (U α) u).trans (hU α (P u))

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  [hG : IsSmoothComplexBundle (n := n) (r := k) G]
  [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ in
/-- Subtraction preserves the bilinear transpose identity on smooth sections. -/
theorem IsFormalTranspose.sub
    (P P' : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F)
    (T T' : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
      smoothSections (n := n) (r := r) (DualBundle E))
    (hT : IsFormalTranspose μ P T) (hT' : IsFormalTranspose μ P' T') :
    IsFormalTranspose μ (P - P') (T - T') := by
  /- Evaluation of smooth vector and covector sections is smooth and hence
  integrable against the finite positive smooth density on compact M. Split
  both integrals of differences, use hT and hT', and reassemble the difference.
  Integrability is essential for this use of subtraction under the integral. -/
  intro α u
  have _sourceSmooth := hE
  have _targetSmooth := hF
  -- Compactness makes each original smooth evaluation integrable for the same density.
  have hTu : Integrable (fun x ↦ (T α).val x (u.val x)) μ :=
    integrable_dualSection_eval E μ ((dualSectionsEquiv E).symm (T α)) u
  have hT'u : Integrable (fun x ↦ (T' α).val x (u.val x)) μ :=
    integrable_dualSection_eval E μ ((dualSectionsEquiv E).symm (T' α)) u
  have hPu : Integrable (fun x ↦ α.val x ((P u).val x)) μ :=
    integrable_dualSection_eval F μ ((dualSectionsEquiv F).symm α) (P u)
  have hP'u : Integrable (fun x ↦ α.val x ((P' u).val x)) μ :=
    integrable_dualSection_eval F μ ((dualSectionsEquiv F).symm α) (P' u)
  -- Expand the two differences and use the two specified pairing identities.
  change (∫ x, ((T α).val x - (T' α).val x) (u.val x) ∂μ) =
    ∫ x, α.val x ((P u).val x - (P' u).val x) ∂μ
  simp only [sub_apply, map_sub]
  rw [integral_sub hTu hT'u, integral_sub hPu hP'u, hT α u, hT' α u]

include hM hT2 hSC hC hBorel hE hF hμ in
/-- Any specified formal transpose of a smooth-kernel map has the swapped dual kernel. -/
theorem IsFormalTranspose.isSmoothingOperator
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (T : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
      smoothSections (n := n) (r := r) (DualBundle E))
    (hT : IsFormalTranspose μ P T) (hP : IsSmoothingOperator μ P) :
    IsSmoothingOperator μ T := by
  /- Choose the actual smooth kernel K of P. Fubini gives the formal transpose
  identity for K.transpose. Uniqueness against smooth primal tests identifies
  T with its integral map, which supplies the required smooth-kernel witness. -/
  obtain ⟨K, rfl⟩ := hP
  -- The same kernel witness supplies the swapped kernel and its genuine pairing identity.
  refine ⟨K.transpose, ?_⟩
  exact IsFormalTranspose.unique (K.toLinearMap μ) (K.transpose.toLinearMap μ) T
    K.isFormalTranspose_toLinearMap hT

namespace PseudodifferentialOperator

/-- The transpose of the actual identity is the identity on the actual dual bundle. -/
theorem formalTranspose_id :
    (PseudodifferentialOperator.id (n := n) (r := r) (E := E) μ).formalTranspose.toLinearMap =
      LinearMap.id := by
  /- The identity section map has the identity pairing. Compare it with the
  specified PDO transpose by uniqueness. The equality concerns section maps,
  so no equality of chosen finite PDO representations is required. -/
  -- Uniqueness compares the same identity action and its original bilinear pairing.
  exact IsFormalTranspose.unique LinearMap.id _ LinearMap.id
    (PseudodifferentialOperator.id (n := n) (r := r) (E := E) μ
      |>.isFormalTranspose_formalTransposeLinearMap) isFormalTranspose_id

/-- Global PDO transposition reverses actual composition, at arbitrary real orders. -/
theorem formalTranspose_comp {l m : ℝ}
    (R : PseudodifferentialOperator (n := n) (r := q) (q := k) F G μ l)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m) :
    (R.comp P).formalTranspose.toLinearMap =
      P.formalTranspose.toLinearMap.comp R.formalTranspose.toLinearMap := by
  /- Compose the two defining pairing identities in the reverse order by
  IsFormalTranspose.comp. Uniqueness compares that composite with the transpose
  of R.comp P. The equality uses actual maps G* -> E*, avoiding order casts. -/
  apply IsFormalTranspose.unique (R.toLinearMap.comp P.toLinearMap)
    (R.comp P).formalTranspose.toLinearMap
    (P.formalTranspose.toLinearMap.comp R.formalTranspose.toLinearMap)
    (R.comp P).isFormalTranspose_formalTransposeLinearMap
  exact IsFormalTranspose.comp P.toLinearMap R.toLinearMap
    P.formalTranspose.toLinearMap R.formalTranspose.toLinearMap
    P.isFormalTranspose_formalTransposeLinearMap R.isFormalTranspose_formalTransposeLinearMap

variable {m l : ℝ}
  (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ l)

/-- The transpose of a right smoothing error is the left error on the dual target bundle. -/
theorem isSmoothingOperator_formalTranspose_comp_sub_id
    (hQ : IsSmoothingOperator μ (P.toLinearMap.comp Q.toLinearMap - LinearMap.id)) :
    IsSmoothingOperator μ
      (Q.formalTranspose.toLinearMap.comp P.formalTranspose.toLinearMap - LinearMap.id) := by
  /- Stage 1: composition and subtraction of the pairing identities show that
  Q^t P^t-I is a formal transpose of P Q-I. The former acts on F*, the latter on F.
  Stage 2: apply the smooth-kernel transpose transfer to hQ. Only the displayed
  right error is used; no assumption about Q P-I, or about l=-m, is necessary. -/
  -- Compose the two pairing identities on actual section maps in reverse order.
  have hcomp := IsFormalTranspose.comp Q.toLinearMap P.toLinearMap
    Q.formalTranspose.toLinearMap P.formalTranspose.toLinearMap
    Q.isFormalTranspose_formalTransposeLinearMap P.isFormalTranspose_formalTransposeLinearMap
  -- Subtract the actual identity pairing before transferring the original smoothing witness.
  have herror := hcomp.sub _ LinearMap.id _ LinearMap.id isFormalTranspose_id
  exact herror.isSmoothingOperator _ _ hQ

/-- The same two transposed maps form a parametrix pair, with the residuals exchanged. -/
theorem isParametrix_formalTranspose
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    IsParametrix μ P.formalTranspose.toLinearMap Q.formalTranspose.toLinearMap := by
  /- The preceding theorem sends hQ.2 to the left error Q^t P^t-I on F*.
  Apply it with P and Q interchanged to send hQ.1 to the right error P^t Q^t-I
  on E*. Combine these two witnesses in the order required by IsParametrix. -/
  -- Transposition exchanges the two residuals while retaining these same P and Q.
  exact ⟨P.isSmoothingOperator_formalTranspose_comp_sub_id Q hQ.2,
    Q.isSmoothingOperator_formalTranspose_comp_sub_id P hQ.1⟩

end PseudodifferentialOperator

end AtiyahSinger
