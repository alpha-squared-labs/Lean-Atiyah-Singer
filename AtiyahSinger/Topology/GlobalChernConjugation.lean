/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectiveConjugation
public import AtiyahSinger.Topology.VariableRankChern

/-!
# Conjugation and the global integral Chern classes

Public module ID: M1866.

A continuous conjugate-linear involution on the original bundle forces its kth
integral Chern class to equal its signed value. The proof transports the actual
involution through the specified universe-compatible model and its rank strata,
then applies the fixed-rank projective comparison. No bound on the locally varying
rank and no compatibility of the supplied metric with conjugation is required.
This is the bridge used for the odd Chern classes of real complexifications.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u v

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A continuous conjugate-linear involution fixes the signed global Chern classes. -/
theorem globalChernClass_eq_neg_one_pow_smul_of_conjugateLinear_involution
    (J : ∀ x, E x ≃ₗ⋆[ℂ] E x) (hJ : ∀ x, Function.Involutive (J x))
    (hcontinuous : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, J z.proj z.snd⟩ : TotalSpace Unit E))) (k : ℕ) :
    globalChernClass E h k = (-1 : ℤ) ^ k • globalChernClass E h k := by
  -- Transport the original involution and its total-space continuity through the specified iso.
  let M := CohomologyModel E
  let := cohomologyModelTopology E
  let := isFiniteRank_cohomologyModel E
  let e := cohomologyModelIso E
  let JM (x : X) : M x ≃ₗ⋆[ℂ] M x :=
    (e.linearEquiv x).trans ((J x).trans (e.linearEquiv x).symm)
  have hJM (x : X) : Function.Involutive (JM x) := by
    intro a
    dsimp [JM]
    rw [LinearEquiv.apply_symm_apply, hJ x, LinearEquiv.symm_apply_apply]
  have hcM : Continuous (fun z : TotalSpace Unit M ↦
      (⟨z.proj, JM z.proj z.snd⟩ : TotalSpace Unit M)) :=
    e.continuous_symm.comp (hcontinuous.comp e.continuous_total)
  -- The actual clopen rank strata detect equality, including the empty strata and rank zero.
  apply (singularCohomologyPullback_rankStrata_bijective ℤ M (2 * k)).injective
  funext r
  let S := rankStratum M r
  let i : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let A := Restrict M S
  let := isFiniteRank_restrict (E := M) (S : Set X)
  let hA := rankHermitianMetric M (cohomologyModelMetric E h) r
  let JA (x : S) : A x ≃ₗ⋆[ℂ] A x := JM x.val
  have hcA : Continuous (fun z : TotalSpace Unit A ↦
      (⟨z.proj, JA z.proj z.snd⟩ : TotalSpace Unit A)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit M i).continuous_iff]
    exact (Pullback.continuous_proj Unit M i).prodMk
      (hcM.comp (Pullback.continuous_lift Unit M i))
  -- Use the same restricted vectors and topology in the native constant-rank presentation.
  let : ∀ x, NormedAddCommGroup (A x) := hA.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (A x) := hA.fiberInnerProductSpace
  let V := EuclideanSpace ℂ (Fin r)
  let := nativeModelTopology A V
  let := hA.nativeFiberBundle r (fun x ↦ x.property)
  let := hA.nativeVectorBundle r (fun x ↦ x.property)
  have hcNative : Continuous (fun z : TotalSpace V A ↦
      (⟨z.proj, JA z.proj z.snd⟩ : TotalSpace V A)) :=
    (nativeModelTotalHomeomorph A V).symm.continuous.comp
      (hcA.comp (nativeModelTotalHomeomorph A V).continuous)
  have hspec := (existsUnique_globalChernClass E h k).exists.choose_spec r
  change singularCohomologyPullback ℤ i (2 * k) (globalChernClass E h k) =
    chernClass r A (hA.nativeModelMetric r) k at hspec
  change singularCohomologyPullback ℤ i (2 * k) (globalChernClass E h k) =
    singularCohomologyPullback ℤ i (2 * k) ((-1 : ℤ) ^ k • globalChernClass E h k)
  rw [map_zsmul, hspec]
  exact chernClass_eq_neg_one_pow_smul_of_conjugateLinear_involution r A
    (hA.nativeModelMetric r) JA (fun x ↦ hJM x.val) hcNative k

end AtiyahSinger.ComplexBundle
