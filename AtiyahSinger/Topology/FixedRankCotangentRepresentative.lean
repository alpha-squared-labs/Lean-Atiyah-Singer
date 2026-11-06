/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CotangentRepresentative

/-!
# Fixed-rank representatives in positive cotangent dimension

Public module ID: M1859.

On a compact positive-dimensional manifold, an off-zero cotangent isomorphism
forces its two original bundles to have equal rank at each base point. Adding
the same complement of the source to both sides then gives a single fixed rank
without assuming connectedness. This is the stabilization step in the project
supplement to SG III.13 Lemma 13.3; the zero-dimensional case is excluded because
its original source and target ranks need not agree.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [CompactSpace M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial isFiniteRank_pullback
  IdempotentMatrix.fiberTotalSpaceTopology IdempotentMatrix.isFiniteRank_fiber

set_option maxHeartbeats 800000 in

/-- One common stabilization gives a fixed-rank homogeneous representative in positive dimension. -/
theorem exists_fixedRank_homogeneous_cotangent_representative (hn : 0 < n)
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
    ∃ E F : FiniteBundle M, ∃ r : ℕ,
      (∀ x : M, Module.finrank ℂ (E.Fiber x) = r) ∧
      (∀ x : M, Module.finrank ℂ (F.Fiber x) = r) ∧
      ∃ a : CompactSupportTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
        a.control = cotangentZeroSet ∧
        (∀ (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ), 0 < t →
          ∀ (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ)
            (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ),
            a.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
              a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩) ∧
        a.compactSupportClass = u := by
  classical
  obtain ⟨E, F, a, ha, hhom, hclass⟩ := exists_homogeneous_cotangent_representative u
  -- A nonzero covector tests equality of the two ranks at each original base point.
  have hrank (x : M) : Module.finrank ℂ (E.Fiber x) = Module.finrank ℂ (F.Fiber x) := by
    let i : Fin n := ⟨0, hn⟩
    let ξ : CotangentFiber (n := n) x := EuclideanSpace.proj i
    have hξ : ξ ≠ 0 := by
      intro h
      have h' := congrArg (fun L : CotangentFiber (n := n) x ↦
        L (EuclideanSpace.single i 1)) h
      change (EuclideanSpace.single i (1 : ℝ)) i = 0 at h'
      simp at h'
    have hz : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ := by
      simpa only [ha, cotangentZeroSet, Set.mem_compl_iff, Set.mem_ofPred_eq] using hξ
    exact (a.boundary.linearEquiv ⟨⟨x, ξ⟩, hz⟩).finrank_eq
  -- The same complement makes the source trivial and the target of the same fixed rank.
  obtain ⟨p, ⟨j⟩⟩ := exists_complement_bundle (E := E.Fiber)
  let C : FiniteBundle M := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
  let P := E.sum C
  let Q := F.sum C
  have hP (x : M) : Module.finrank ℂ (P.Fiber x) = p.size := by
    exact (j.linearEquiv x).finrank_eq.trans (Module.finrank_fin_fun ℂ)
  have hQ (x : M) : Module.finrank ℂ (Q.Fiber x) = p.size := by
    let := finite_fiber (E := E.Fiber) x
    let := finite_fiber (E := F.Fiber) x
    let := finite_fiber (E := C.Fiber) x
    change Module.finrank ℂ (F.Fiber x × C.Fiber x) = p.size
    rw [Module.finrank_prod, ← hrank x, ← Module.finrank_prod]
    exact hP x
  let πM := cotangentProjection (n := n) (M := M)
  -- Pullback and sum carry distinct induced topologies; compare them by the actual identity.
  let compare (J K : FiniteBundle M) :
      Iso ((J.sum K).pullback πM).Fiber ((J.pullback πM).sum (K.pullback πM)).Fiber :=
    { linearEquiv z := LinearEquiv.refl ℂ (J.Fiber (πM z) × K.Fiber (πM z))
      continuous_total := by
        apply continuous_induced_rng.mpr
        apply Continuous.prodMk
        · rw [(inducing_pullbackTotalSpaceEmbedding Unit J.Fiber πM).continuous_iff]
          exact (Pullback.continuous_proj Unit (J.sum K).Fiber πM).prodMk
            (continuous_sum_fst.comp (Pullback.continuous_lift Unit (J.sum K).Fiber πM))
        · rw [(inducing_pullbackTotalSpaceEmbedding Unit K.Fiber πM).continuous_iff]
          exact (Pullback.continuous_proj Unit (J.sum K).Fiber πM).prodMk
            (continuous_sum_snd.comp (Pullback.continuous_lift Unit (J.sum K).Fiber πM))
      continuous_symm := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (J.sum K).Fiber πM).continuous_iff]
        apply ((Pullback.continuous_proj Unit J.Fiber πM).comp continuous_sum_fst).prodMk
        apply continuous_induced_rng.mpr
        exact ((Pullback.continuous_lift Unit J.Fiber πM).comp continuous_sum_fst).prodMk
          ((Pullback.continuous_lift Unit K.Fiber πM).comp continuous_sum_snd) }
  let identity := CompactSupportTriple.ofIso (Iso.refl ((πM : _ → M) *ᵖ C.Fiber))
  let b := (a.sum identity).congr (compare E C).symm (compare F C).symm
  have hb : b.control = cotangentZeroSet := by
    change a.control ∪ ∅ = cotangentZeroSet
    simpa only [Set.union_empty] using ha
  refine ⟨P, Q, p.size, hP, hQ, b, hb, ?_, ?_⟩
  · -- The comparison is fiberwise identity, so the original ray law also fixes the summand.
    intro x ξ t ht hξ htξ
    apply LinearEquiv.ext
    intro v
    have hz : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ := by
      simpa only [ha, ← hb] using hξ
    have htz : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ := by
      simpa only [ha, ← hb] using htξ
    let a' := a.enlarge _ (a.isCompact_control.union identity.isCompact_control)
      Set.subset_union_left
    let i' := identity.enlarge _ (a.isCompact_control.union identity.isCompact_control)
      Set.subset_union_right
    change (RelativeTriple.sum a'.boundary i'.boundary).linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ v =
      (RelativeTriple.sum a'.boundary i'.boundary).linearEquiv ⟨⟨x, ξ⟩, hξ⟩ v
    refine (RelativeTriple.sum_apply a'.boundary i'.boundary ⟨⟨x, t • ξ⟩, htξ⟩ v).trans ?_
    refine Eq.trans ?_
      (RelativeTriple.sum_apply a'.boundary i'.boundary ⟨⟨x, ξ⟩, hξ⟩ v).symm
    have hstep (η : CotangentFiber (n := n) x)
        (hη : (⟨x, η⟩ : CotangentTotalSpace) ∈ a'.controlᶜ) :
        (a'.boundary.linearEquiv ⟨⟨x, η⟩, hη⟩ v.1,
          i'.boundary.linearEquiv ⟨⟨x, η⟩, hη⟩ v.2) =
        (a.boundary.linearEquiv ⟨⟨x, η⟩, fun h ↦ hη (Or.inl h)⟩ v.1, v.2) := by
      exact Prod.ext (a.enlarge_apply _ _ _ _ _)
        (identity.enlarge_apply _ _ _ _ _)
    refine (hstep (t • ξ) htξ).trans (Eq.trans ?_ (hstep ξ hξ).symm)
    rw [hhom x ξ t ht hz htz]
    rfl
  · -- Adding a globally invertible identity triple changes no compact-support K class.
    change ((a.sum identity).congr _ _).compactSupportClass = u
    rw [CompactSupportTriple.compactSupportClass_congr,
      CompactSupportTriple.compactSupportClass_sum,
      CompactSupportTriple.compactSupportClass_ofIso, add_zero]
    exact hclass

end AtiyahSinger
