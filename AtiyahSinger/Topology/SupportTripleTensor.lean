/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTensorRestriction
public import AtiyahSinger.Topology.SupportBundleTriple

/-!
# Tensoring the original support triple by a finite bundle

Public module ID: M2199.

A bundle E acts on relative and compact-support triples by tensoring both
original bundles on the left. The boundary is precisely id_E tensor the old
boundary, transported through the vector-preserving restriction comparisons.
The compact control remains the original control, with its original compactness
certificate. No compactness or global rank bound is imposed on E or the base.

Sources: SG I.9 for bundle multiplication and relative triples; KA II.5.11
and II.5.14, pp.96--97, for the relative module and the explicit boundary
formula id_E tensor alpha; ASI I, Section 2, for equivariant tensor actions.
The same-base constructors and restriction comparisons are project supplements
to the external-product formula. The unchanged chosen control need not be
minimal; a zero-rank tensor factor can shrink the actual support. This module
constructs tensor triples; the induced K-module action is developed in
`SupportTensorAction`.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

variable {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F H : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
  [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H]
  {A : Set X}

attribute [local instance] tensorTopology isFiniteRank_tensor isFiniteRank_restrict

/-- Tensor the original relative boundary with the identity of the specified left bundle. -/
def RelativeTriple.tensorLeft (a : RelativeTriple F H A) :
    RelativeTriple (fun x ↦ E x ⊗[ℂ] F x) (fun x ↦ E x ⊗[ℂ] H x) A :=
  (restrictTensorIso (E := E) (F := F) A).trans
    (((Iso.refl (Restrict E A)).tensor a).trans
      (restrictTensorIso (E := E) (F := H) A).symm)

/-- On pure vectors, the boundary keeps the left factor and applies exactly the old boundary. -/
theorem RelativeTriple.tensorLeft_tmul (a : RelativeTriple F H A)
    (x : A) (u : E x) (v : F x) :
    (a.tensorLeft E).linearEquiv x (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] a.linearEquiv x v := by
  /- Stage 1: both restriction/tensor comparisons preserve the actual tensor
  vector in the original fiber, including the inverse target comparison.
  Stage 2: the middle tensor isomorphism is the original Iso.tensor of the
  identity on E and a. Its algebraic TensorProduct.congr formula sends the
  pure vector to u tensor a(v), with the same original base point. -/
  exact TensorProduct.congr_tmul (LinearEquiv.refl ℂ (E x)) (a.linearEquiv x) u v

/-- Tensoring on the left changes only the bundles and boundary, retaining the original control. -/
def CompactSupportTriple.tensorLeft (a : CompactSupportTriple F H) :
    CompactSupportTriple (fun x ↦ E x ⊗[ℂ] F x) (fun x ↦ E x ⊗[ℂ] H x) where
  control := a.control
  isCompact_control := a.isCompact_control
  boundary := a.boundary.tensorLeft E

/-- Package the actual tensor bundles and original-control boundary data. -/
@[reducible]
def SupportBundleTriple.tensorLeft (E : FiniteBundle X) (a : SupportBundleTriple X) :
    SupportBundleTriple X :=
  SupportBundleTriple.ofBoundary (E.tensor a.source) (E.tensor a.target)
    (a.datum.tensorLeft E.Fiber)

end AtiyahSinger.ComplexBundle
