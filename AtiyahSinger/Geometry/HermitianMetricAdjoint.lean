/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianMetricDual

/-!
# Fiber adjoints for explicit Hermitian metrics

Public module ID: M1271.

D02/D05: finite-rank adjunction for the original normed fibers, with metrics passed
as data. The characterization k(Tu,v)=h(u,T†v) fixes the order of every weight.
Sources: SG III.3.11 and III.5 pp.194–195; the explicit-data formulas are project
comparisons of the standard Hermitian adjoint. No base compactness is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

namespace SmoothHermitianMetric

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

/-- The fiber adjoint exists uniquely for the two specified positive forms. -/
theorem existsUnique_adjoint (x : M) (T : E x →L[ℂ] F x) :
    ∃! S : F x →L[ℂ] E x, ∀ (u : E x) (v : F x),
      k.pairing x (T u) v = h.pairing x u (S v) := by
  /- Compose the k metric dual, precomposition by T, and the inverse h
  metric dual. Two conjugate-linear maps make the resulting map complex-linear.
  Finite dimension gives continuity, and positivity of h gives uniqueness. -/
  let : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  -- The two conjugate-linear metric identifications cancel around dual precomposition.
  let S₀ : F x →ₗ[ℂ] E x := {
    toFun := fun v ↦ (h.dualEquiv x).symm ((k.dual x v).comp T)
    map_add' := by
      intro v w
      rw [k.dual_add, ContinuousLinearMap.add_comp, map_add]
    map_smul' := by
      intro c v
      rw [k.dual_smul, ContinuousLinearMap.smul_comp, map_smulₛₗ]
      simp }
  let S : F x →L[ℂ] E x := S₀.toContinuousLinearMap
  have hS (u : E x) (v : F x) : h.pairing x (S v) u = k.pairing x v (T u) := by
    exact (h.pairing_dualEquiv_symm x ((k.dual x v).comp T) u).trans
      (k.dual_apply x v (T u))
  have hS' (u : E x) (v : F x) : k.pairing x (T u) v = h.pairing x u (S v) := by
    have hc := congrArg (starRingEnd ℂ) (hS u v)
    simpa only [pairing, (h.toCore x).conj_inner_symm,
      (k.toCore x).conj_inner_symm] using hc.symm
  refine ⟨S, hS', ?_⟩
  intro R hR
  -- The original positive source form separates the candidate values.
  apply ContinuousLinearMap.ext
  intro v
  let : InnerProductSpace.Core ℂ (E x) := h.toCore x
  have hz : (h.toCore x).inner (R v - S v) (R v - S v) = 0 := by
    rw [InnerProductSpace.Core.inner_sub_right]
    change h.pairing x (R v - S v) (R v) - h.pairing x (R v - S v) (S v) = 0
    rw [← hR, ← hS', sub_self]
  exact sub_eq_zero.mp ((h.toCore x).definite _ hz)

/-- The continuous linear adjoint for explicit metrics, using the original fiber topologies. -/
def adjoint (x : M) (T : E x →L[ℂ] F x) : F x →L[ℂ] E x :=
  Classical.choose (h.existsUnique_adjoint k x T).exists

/-- The defining fiber adjunction identity. -/
theorem pairing_adjoint (x : M) (T : E x →L[ℂ] F x) (u : E x) (v : F x) :
    h.pairing x u (h.adjoint k x T v) = k.pairing x (T u) v := by
  /- Read off the evaluation property of the chosen unique adjoint, with
  the equality reversed to put the original metric on the displayed left side. -/
  exact ((Classical.choose_spec (h.existsUnique_adjoint k x T).exists) u v).symm

/-- A candidate satisfying the metric identity equals the adjoint. -/
theorem adjoint_eq (x : M) (T : E x →L[ℂ] F x) (S : F x →L[ℂ] E x)
    (hS : ∀ u v, k.pairing x (T u) v = h.pairing x u (S v)) : h.adjoint k x T = S := by
  /- Both S and the selected map satisfy the same nondegenerate pairing
  identity. Apply the uniqueness part of existsUnique_adjoint to identify them. -/
  exact (h.existsUnique_adjoint k x T).unique
    (Classical.choose_spec (h.existsUnique_adjoint k x T).exists) hS

/-- The zero fiber map has zero adjoint. -/
theorem adjoint_zero (x : M) : h.adjoint k x 0 = 0 := by
  /- The zero map in the reversed direction satisfies the zero pairing
  identity by sesquilinearity. Uniqueness then gives the asserted map equality. -/
  apply h.adjoint_eq k x
  intro u v
  let : InnerProductSpace.Core ℂ (E x) := h.toCore x
  let : InnerProductSpace.Core ℂ (F x) := k.toCore x
  exact (InnerProductSpace.Core.inner_zero_left v).trans
    (InnerProductSpace.Core.inner_zero_right u).symm

/-- Fiber adjunction preserves addition. -/
theorem adjoint_add (x : M) (S T : E x →L[ℂ] F x) :
    h.adjoint k x (S + T) = h.adjoint k x S + h.adjoint k x T := by
  /- Pair the sum with arbitrary vectors. Additivity in both slots and
  the two adjunction identities show that the sum of adjoints is the required
  candidate, and nondegeneracy identifies it uniquely. -/
  apply h.adjoint_eq k x
  intro u v
  let : InnerProductSpace.Core ℂ (E x) := h.toCore x
  change k.pairing x (S u + T u) v =
    h.pairing x u (h.adjoint k x S v + h.adjoint k x T v)
  calc
    k.pairing x (S u + T u) v = k.pairing x (S u) v + k.pairing x (T u) v :=
      (k.toCore x).add_left _ _ _
    _ = h.pairing x u (h.adjoint k x S v) + h.pairing x u (h.adjoint k x T v) := by
      rw [h.pairing_adjoint, h.pairing_adjoint]
    _ = h.pairing x u (h.adjoint k x S v + h.adjoint k x T v) :=
      (InnerProductSpace.Core.inner_add_right _ _ _).symm

/-- Fiber adjunction conjugates the complex scalar. -/
theorem adjoint_smul (x : M) (c : ℂ) (T : E x →L[ℂ] F x) :
    h.adjoint k x (c • T) = conj c • h.adjoint k x T := by
  /- The scalar appears in the conjugate-linear first slot of k and in
  the linear second slot of h. It therefore becomes conj c in the reversed map;
  apply the defining identity and uniqueness. -/
  apply h.adjoint_eq k x
  intro u v
  let : InnerProductSpace.Core ℂ (E x) := h.toCore x
  change k.pairing x (c • T u) v = h.pairing x u (conj c • h.adjoint k x T v)
  calc
    k.pairing x (c • T u) v = conj c * k.pairing x (T u) v :=
      (k.toCore x).smul_left _ _ _
    _ = conj c * h.pairing x u (h.adjoint k x T v) := by rw [h.pairing_adjoint]
    _ = h.pairing x u (conj c • h.adjoint k x T v) :=
      (InnerProductSpace.Core.inner_smul_right _ _).symm

/-- Double adjunction recovers the original fiber map. -/
theorem adjoint_adjoint (x : M) (T : E x →L[ℂ] F x) :
    k.adjoint h x (h.adjoint k x T) = T := by
  /- Conjugate the original adjunction equation and swap its arguments.
  Hermitian symmetry makes T an adjoint of T† with the metrics reversed,
  and uniqueness proves equality of the continuous linear maps. -/
  apply k.adjoint_eq h x
  intro v u
  have hc := congrArg (starRingEnd ℂ) (h.pairing_adjoint k x T u v)
  simpa only [pairing, (h.toCore x).conj_inner_symm,
    (k.toCore x).conj_inner_symm] using hc

/-- The identity is self-adjoint for one metric. -/
theorem adjoint_id (x : M) :
    h.adjoint h x (ContinuousLinearMap.id ℂ (E x)) = ContinuousLinearMap.id ℂ (E x) := by
  /- The identity on the fiber satisfies h(u,v)=h(u,v). It is therefore
  the unique adjoint relative to the same metric on source and target. -/
  apply h.adjoint_eq h x
  intro u v
  rfl

/-- Changing both metrics gives the exact two-sided conjugation formula. -/
theorem adjoint_change (h' : SmoothHermitianMetric (n := n) (r := r) E)
    (k' : SmoothHermitianMetric (n := n) (r := q) F)
    (x : M) (T : E x →L[ℂ] F x) :
    h'.adjoint k' x T = (h'.change h x).toContinuousLinearMap.comp
      ((h.adjoint k x T).comp (k.change k' x).toContinuousLinearMap) := by
  /- Write k'(Tu,v)=k(Tu,B_F v), use the old adjunction, and convert the
  h pairing to h' by applying B_E⁻¹ to its second slot. Uniqueness yields
  B_E⁻¹ T† B_F, with no commutation of the three factors. -/
  apply h'.adjoint_eq k' x
  intro u v
  change k'.pairing x (T u) v =
    h'.pairing x u (h'.change h x (h.adjoint k x T (k.change k' x v)))
  rw [h'.pairing_change, h.pairing_adjoint, k.pairing_change]

/-- Adjunction is compatible with metric duality and ordinary dual precomposition. -/
theorem dual_adjoint (x : M) (T : E x →L[ℂ] F x) (v : F x) :
    h.dual x (h.adjoint k x T v) = (k.dual x v).comp T := by
  /- Evaluate on u, conjugate the adjunction equation, and use Hermitian
  symmetry. This yields h(T†v,u)=k(v,Tu), the ordinary linear-dual pullback. -/
  ext u
  change h.dual x (h.adjoint k x T v) u = k.dual x v (T u)
  rw [h.dual_apply, k.dual_apply]
  have hc := congrArg (starRingEnd ℂ) (h.pairing_adjoint k x T u v)
  simpa only [pairing, (h.toCore x).conj_inner_symm,
    (k.toCore x).conj_inner_symm] using hc

/-- Bijectivity of the fiber map is equivalent to bijectivity of its adjoint. -/
theorem bijective_adjoint_iff (x : M) (T : E x →L[ℂ] F x) :
    Function.Bijective (h.adjoint k x T) ↔ Function.Bijective T := by
  /- The same metric dual equivalences identify adjunction with algebraic
  dual precomposition. In finite dimension every algebraic functional is
  continuous for the original norm. Bijectivity is preserved by those
  equivalences, and algebraic duality detects bijectivity of T. -/
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  -- Pass to the algebraic dual through finite-dimensional continuity, preserving values.
  let H : E x ≃ Module.Dual ℂ (E x) :=
    (h.dualEquiv x).toEquiv.trans LinearMap.toContinuousLinearMap.symm.toEquiv
  let K : F x ≃ Module.Dual ℂ (F x) :=
    (k.dualEquiv x).toEquiv.trans LinearMap.toContinuousLinearMap.symm.toEquiv
  have he : (fun α ↦ T.toLinearMap.dualMap α) =
      H ∘ (h.adjoint k x T) ∘ K.symm := by
    funext α
    apply LinearMap.ext
    intro u
    have hv := congrArg (fun β : DualBundle E x ↦ β u)
      (h.dual_adjoint k x T (K.symm α))
    change _ = h.dual x (h.adjoint k x T (K.symm α)) u
    rw [hv]
    exact (congrArg (fun β : Module.Dual ℂ (F x) ↦ β (T u))
      (K.apply_symm_apply α)).symm
  have hdual : Function.Bijective T.toLinearMap.dualMap ↔
      Function.Bijective (h.adjoint k x T) := by
    have hb := Iff.of_eq (congrArg
      (fun f : Module.Dual ℂ (F x) → Module.Dual ℂ (E x) ↦ Function.Bijective f) he)
    exact hb.trans ((Equiv.comp_bijective _ H).trans (K.symm.bijective_comp _))
  exact hdual.symm.trans LinearMap.dualMap_bijective_iff

/-- Kernel orthogonality is expressed by the actual metric, not an installed inner product. -/
theorem adjoint_apply_eq_zero_iff (x : M) (T : E x →L[ℂ] F x) (v : F x) :
    h.adjoint k x T v = 0 ↔ ∀ u : E x, k.pairing x (T u) v = 0 := by
  /- Use adjunction in each direction. If all right pairings vanish,
  take u=T†v. Definiteness of h forces that vector to be zero, proving
  the reverse implication without a closed-range hypothesis. -/
  constructor
  · intro hz u
    rw [← h.pairing_adjoint k x T u v, hz]
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    exact InnerProductSpace.Core.inner_zero_right u
  · intro hv
    apply (h.toCore x).definite
    exact (h.pairing_adjoint k x T (h.adjoint k x T v) v).trans
      (hv (h.adjoint k x T v))

/-- Adjoint of an inverse is the inverse of the adjoint. -/
theorem adjoint_inverse (x : M) (T : E x ≃L[ℂ] F x) :
    k.adjoint h x T.symm.toContinuousLinearMap =
      (h.adjoint k x T.toContinuousLinearMap).inverse := by
  /- Adjoint the two inverse identities. The resulting maps are mutual
  inverses, so the library's totalized inverse agrees with this genuine
  adjoint inverse. The input is an actual equivalence, not an arbitrary map. -/
  let A := h.adjoint k x T.toContinuousLinearMap
  let B := k.adjoint h x T.symm.toContinuousLinearMap
  -- Dual evaluation of the two composites reduces to the original inverse identities.
  have hAB : A.comp B = ContinuousLinearMap.id ℂ (E x) := by
    ext u
    apply (h.bijective_dual x).1
    ext v
    have h₁ := congrArg (fun α : DualBundle E x ↦ α v)
      (h.dual_adjoint k x T.toContinuousLinearMap (B u))
    have h₂ := congrArg (fun α : DualBundle F x ↦ α (T v))
      (k.dual_adjoint h x T.symm.toContinuousLinearMap u)
    exact h₁.trans (h₂.trans (congrArg (h.dual x u) (T.symm_apply_apply v)))
  have hBA : B.comp A = ContinuousLinearMap.id ℂ (F x) := by
    ext v
    apply (k.bijective_dual x).1
    ext u
    have h₁ := congrArg (fun α : DualBundle F x ↦ α u)
      (k.dual_adjoint h x T.symm.toContinuousLinearMap (A v))
    have h₂ := congrArg (fun α : DualBundle E x ↦ α (T.symm u))
      (h.dual_adjoint k x T.toContinuousLinearMap v)
    exact h₁.trans (h₂.trans (congrArg (k.dual x v) (T.apply_symm_apply u)))
  exact (ContinuousLinearMap.inverse_eq hAB hBA).symm

variable {a : ℕ} {G : M → Type*}
  [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) G]

/-- Adjunction reverses composition and uses the middle metric consistently. -/
theorem adjoint_comp (l : SmoothHermitianMetric (n := n) (r := a) G)
    (x : M) (T : E x →L[ℂ] F x) (S : F x →L[ℂ] G x) :
    h.adjoint l x (S.comp T) = (h.adjoint k x T).comp (k.adjoint l x S) := by
  /- Apply adjunction first to S and then to T. The common middle
  metric k cancels from the defining equation, and uniqueness identifies
  the reverse-order composite as the adjoint of S composed with T. -/
  apply h.adjoint_eq l x
  intro u w
  change l.pairing x (S (T u)) w = h.pairing x u
    (h.adjoint k x T (k.adjoint l x S w))
  rw [h.pairing_adjoint, k.pairing_adjoint]

end SmoothHermitianMetric

end AtiyahSinger
