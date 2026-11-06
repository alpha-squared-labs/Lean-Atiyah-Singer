/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleSum

/-!
# Restrictions of continuous bundles

Public module ID: M1592.

D07/K01/K02. Restriction means mathlib pullback along the subtype inclusion.
Nested restrictions retain their induced topology, and their comparisons keep the
same fiber vector. No closedness or compactness is required in this module.
Sources: SG I.9.1–9.3; Karoubi I.1–I.2 and II.2.7.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {G : X → Type*} [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit G)]

/-- Restriction is the actual pullback to the subspace. -/
abbrev Restrict (E : X → Type*) (A : Set X) : A → Type _ :=
  (Subtype.val : A → X) *ᵖ E

/-- Restrictions preserve locally finite rank. -/
theorem isFiniteRank_restrict [IsFiniteRank E] (A : Set X) :
    IsFiniteRank (Restrict E A) := by
  /- Pull the local linear trivializations back along the continuous subtype inclusion.
  The subspace may be neither open nor closed; inverse images of chart domains are open. -/
  exact isFiniteRank_pullback (E := E) (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))

attribute [local instance] isFiniteRank_restrict

/-- Restrict the actual fiber maps to a subspace. -/
def Hom.restrict (a : Hom E F) (A : Set X) : Hom (Restrict E A) (Restrict F A) :=
  a.pullback ⟨Subtype.val, continuous_subtype_val⟩

/-- Restrict both directions of a bundle isomorphism. -/
def Iso.restrict (e : Iso E F) (A : Set X) : Iso (Restrict E A) (Restrict F A) :=
  e.pullback ⟨Subtype.val, continuous_subtype_val⟩

/-- Restriction keeps the original fiber action. -/
theorem Hom.restrict_apply (a : Hom E F) (A : Set X) (x : A) (v : E x) :
    (a.restrict A).linearMap x v = a.linearMap x v := by
  /- Unfold the pullback along the inclusion. Its fiber over x is the original fiber
  over x.val, and the map on that fiber is unchanged. -/
  rfl

/-- Restriction commutes with composition. -/
theorem Hom.restrict_comp (a : Hom E F) (b : Hom F G) (A : Set X) :
    (b.comp a).restrict A = (b.restrict A).comp (a.restrict A) := by
  /- Evaluate the two bundle maps at each subspace point and vector. Both composites
  apply a and then b in the original fiber, so bundle-map extensionality applies. -/
  exact Hom.pullback_comp (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) a b

/-- An isomorphism restricts with its specified inverse. -/
theorem Iso.restrict_symm (e : Iso E F) (A : Set X) :
    e.symm.restrict A = (e.restrict A).symm := by
  /- Both restricted structures use the inverse of the same original
  fiber linear equivalence, so they agree by definition. -/
  rfl

/-- Nested restriction has a canonical vector-preserving comparison. -/
theorem exists_restrict_subset_iso (A B : Set X) (h : B ⊆ A) :
    ∃ e : Iso ((Set.inclusion h) *ᵖ (Restrict E A)) (Restrict E B),
      ∀ x v, e.linearEquiv x v = v := by
  /- Both fibers are E(x). In the iterated induced topology the extra A coordinate is
  the continuous inclusion of B. Remove this redundant coordinate in both directions. -/
  exact exists_pullback_comp_iso (E := E)
    (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))
    (⟨Set.inclusion h, continuous_inclusion h⟩ : C(B, A))

/-- Compare iterated restriction with direct restriction. -/
def restrictSubsetIso (A B : Set X) (h : B ⊆ A) :
    Iso ((Set.inclusion h) *ᵖ (Restrict E A)) (Restrict E B) :=
  (exists_restrict_subset_iso (E := E) A B h).choose

/-- The comparison retains each vector. -/
theorem restrictSubsetIso_apply (A B : Set X) (h : B ⊆ A) (x : B) (v : E x) :
    (restrictSubsetIso (E := E) A B h).linearEquiv x v = v := by
  /- Use the vector identity in the existence statement that selected the comparison.
  No arbitrary fiber automorphism is introduced by the choice. -/
  exact (exists_restrict_subset_iso (E := E) A B h).choose_spec x v

/-- Restrict a boundary isomorphism further along a subset inclusion. -/
def Iso.restrictTo {A B : Set X} (e : Iso (Restrict E A) (Restrict F A))
    (h : B ⊆ A) : Iso (Restrict E B) (Restrict F B) :=
  (restrictSubsetIso A B h).symm.trans
    ((e.pullback ⟨Set.inclusion h, continuous_inclusion h⟩).trans
      (restrictSubsetIso A B h))

/-- Further restriction evaluates the same boundary map. -/
theorem Iso.restrictTo_apply {A B : Set X} (e : Iso (Restrict E A) (Restrict F A))
    (h : B ⊆ A) (x : B) (v : E x) :
    (e.restrictTo h).linearEquiv x v = e.linearEquiv (Set.inclusion h x) v := by
  /- The two nested-restriction comparisons keep vectors fixed. Between them the
  pullback evaluates e at the included subspace point, which gives the formula. -/
  -- The source comparison's inverse is identity because its specified forward map is identity.
  have hinv : ((restrictSubsetIso (E := E) A B h).linearEquiv x).symm v = v := by
    have hforward := restrictSubsetIso_apply (E := E) A B h x
      (((restrictSubsetIso (E := E) A B h).linearEquiv x).symm v)
    exact hforward.symm.trans
      (((restrictSubsetIso (E := E) A B h).linearEquiv x).apply_symm_apply v)
  change (restrictSubsetIso (E := F) A B h).linearEquiv x
    (e.linearEquiv (Set.inclusion h x)
      (((restrictSubsetIso (E := E) A B h).linearEquiv x).symm v)) = _
  exact (restrictSubsetIso_apply (E := F) A B h x _).trans
    (congrArg (e.linearEquiv (Set.inclusion h x)) hinv)

/-- A global isomorphism remains unchanged by successive restriction. -/
theorem Iso.restrict_restrictTo (e : Iso E F) {A B : Set X} (h : B ⊆ A) :
    (e.restrict A).restrictTo h = e.restrict B := by
  /- Apply isomorphism extensionality and the formula for further restriction.
  The global fiber equivalence is evaluated at the same point on each side. -/
  apply Iso.ext
  intro x
  apply LinearEquiv.ext
  intro v
  exact Iso.restrictTo_apply (e.restrict A) h x v

attribute [local instance] sumTopology

/-- Restriction commutes with direct sum by the identity on pairs. -/
theorem exists_restrict_sum_iso (A : Set X) :
    ∃ e : Iso (Restrict (E ×ᵇ F) A) ((Restrict E A) ×ᵇ (Restrict F A)),
      ∀ x v, e.linearEquiv x v = v := by
  /- Both induced total topologies record the same base point and the two original
  fiber components. The identity on each pair is continuous in both directions. -/
  let f : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  -- Compare the two given topologies using exactly the same base and original fiber components.
  let e : Iso (Restrict (E ×ᵇ F) A) ((Restrict E A) ×ᵇ (Restrict F A)) :=
    { linearEquiv := fun x ↦ LinearEquiv.refl ℂ (E x × F x)
      continuous_total := by
        apply continuous_induced_rng.mpr
        change Continuous (fun z : TotalSpace Unit (Restrict (E ×ᵇ F) A) ↦
          ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit (Restrict E A)),
            (⟨z.proj, z.snd.2⟩ : TotalSpace Unit (Restrict F A))))
        apply Continuous.prodMk
        · rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
          exact (Pullback.continuous_proj Unit (E ×ᵇ F) f).prodMk
            (continuous_sum_fst.comp (Pullback.continuous_lift Unit (E ×ᵇ F) f))
        · rw [(inducing_pullbackTotalSpaceEmbedding Unit F f).continuous_iff]
          exact (Pullback.continuous_proj Unit (E ×ᵇ F) f).prodMk
            (continuous_sum_snd.comp (Pullback.continuous_lift Unit (E ×ᵇ F) f))
      continuous_symm := by
        change Continuous (fun z : TotalSpace Unit ((Restrict E A) ×ᵇ (Restrict F A)) ↦
          (⟨z.proj, z.snd⟩ : TotalSpace Unit (Restrict (E ×ᵇ F) A)))
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (E ×ᵇ F) f).continuous_iff]
        apply ((Pullback.continuous_proj Unit E f).comp continuous_sum_fst).prodMk
        apply continuous_induced_rng.mpr
        exact ((Pullback.continuous_lift Unit E f).comp continuous_sum_fst).prodMk
          ((Pullback.continuous_lift Unit F f).comp continuous_sum_snd) }
  exact ⟨e, fun _ _ ↦ rfl⟩

/-- Canonical restriction/direct-sum comparison. -/
def restrictSumIso (A : Set X) :
    Iso (Restrict (E ×ᵇ F) A) ((Restrict E A) ×ᵇ (Restrict F A)) :=
  (exists_restrict_sum_iso (E := E) (F := F) A).choose

/-- The sum comparison is the identity on fiber pairs. -/
theorem restrictSumIso_apply (A : Set X) (x : A) (v : E x × F x) :
    (restrictSumIso (E := E) (F := F) A).linearEquiv x v = v := by
  /- Apply the formula in the existence theorem. This fixes the coordinate action
  of the comparison independently of any local trivialization or rank. -/
  exact (exists_restrict_sum_iso (E := E) (F := F) A).choose_spec x v

attribute [local instance] sectionModule

/-- Restrict a continuous section by evaluating it on the subspace. -/
def restrictSection [IsFiniteRank E] (A : Set X) (s : continuousSections E) :
    continuousSections (Restrict E A) :=
  pullbackSection ⟨Subtype.val, continuous_subtype_val⟩ s

/-- Restriction of sections changes scalar functions by restriction. -/
theorem restrictSection_smul [IsFiniteRank E] (A : Set X)
    (c : C(X, ℂ)) (s : continuousSections E) :
    restrictSection A (c • s) =
      c.comp ⟨(Subtype.val : A → X), continuous_subtype_val⟩ • restrictSection A s := by
  /- Apply the semilinear pullback formula to the subtype inclusion. The scalar
  coefficient at a subspace point is precisely its original value at that point. -/
  exact pullbackSection_smul (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) c s

end AtiyahSinger.ComplexBundle
