/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleRestriction
public import AtiyahSinger.Topology.BundleTensor

/-!
# Restriction of the original tensor bundle

Public module ID: M1598.

The restriction of the tensor bundle and the tensor product of the restricted
bundles have the same algebraic fibers. Their total topologies arise by two
different constructions: native pullback of the original tensor topology, and
the original finite-sum tensor topology of the two native restrictions.
Local finite linear charts show that the identity on fibers is continuous in
both directions. The comparison below uses that actual identity equivalence.

The subset need be neither open nor closed, and local ranks may vary. No general
commutation theorem for base change and final topologies is assumed.
Source: Hatcher, Vector Bundles and K-Theory, pp.13--15, gives the tensor-chart
topology. The explicit comparison for the project's finite-sum presentation and
native restriction topology is the standard restriction compatibility supplement.
The continuity proof uses the finite-sum generators and the inverse-map
theorem for the original locally finite-rank bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

attribute [local instance] tensorTopology

/-- The identity tensor vectors are continuous between the two original restricted topologies. -/
theorem continuous_restrict_tensor [IsFiniteRank E] [IsFiniteRank F] (A : Set X) :
    Continuous (fun z : TotalSpace Unit (Restrict (fun x ↦ E x ⊗[ℂ] F x) A) ↦
      (⟨z.proj, z.snd⟩ : TotalSpace Unit
        (fun x : A ↦ (Restrict E A) x ⊗[ℂ] (Restrict F A) x))) ∧
    Continuous (fun z : TotalSpace Unit
        (fun x : A ↦ (Restrict E A) x ⊗[ℂ] (Restrict F A) x) ↦
      (⟨z.proj, z.snd⟩ : TotalSpace Unit (Restrict (fun x ↦ E x ⊗[ℂ] F x) A))) := by
  /- Stage 1: the identity from the tensor of restrictions to the restriction
  of the tensor is continuous on each finite-sum generator. Lift the factors
  to the original total spaces, preserving the common subspace base coordinate.
  Stage 2: both original topologies have finite linear local charts. The existing
  inverse-map theorem therefore gives continuity of the inverse of this same
  fiberwise identity. This uses local finite rank, not a general commutation
  of pullback and final topology. No condition on the subset A is required. -/
  let : IsFiniteRank (fun x ↦ E x ⊗[ℂ] F x) := isFiniteRank_tensor
  let : IsFiniteRank (Restrict E A) := isFiniteRank_restrict A
  let : IsFiniteRank (Restrict F A) := isFiniteRank_restrict A
  let : IsFiniteRank (fun x : A ↦ (Restrict E A) x ⊗[ℂ] (Restrict F A) x) :=
    isFiniteRank_tensor
  let : IsFiniteRank (Restrict (fun x ↦ E x ⊗[ℂ] F x) A) := isFiniteRank_restrict A
  -- Test the actual tensor final topology on each of its finite-sum generators.
  have hforward : Continuous (fun z : TotalSpace Unit
      (fun x : A ↦ (Restrict E A) x ⊗[ℂ] (Restrict F A) x) ↦
      (⟨z.proj, z.snd⟩ : TotalSpace Unit (Restrict (fun x ↦ E x ⊗[ℂ] F x) A))) := by
    apply continuous_iSup_dom.mpr
    intro m
    apply continuous_coinduced_dom.mpr
    let D := TotalSpace Unit
      (fun x : A ↦ (Fin m → Restrict E A x) × (Fin m → Restrict F A x))
    let D' := TotalSpace Unit (fun x : X ↦ (Fin m → E x) × (Fin m → F x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit (Restrict E A))),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit (Restrict F A))))) inferInstance
    let : TopologicalSpace D' := TopologicalSpace.induced
      (fun z : D' ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit E)),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit F)))) inferInstance
    have hd : Continuous (fun z : D ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit (Restrict E A))),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit (Restrict F A))))) :=
      continuous_induced_dom
    let liftTuple (z : D) : D' := ⟨z.proj.val, z.snd⟩
    have hlift : Continuous liftTuple := by
      apply continuous_induced_rng.mpr
      exact (continuous_subtype_val.comp hd.fst).prodMk
        ((continuous_pi fun i ↦ (Pullback.continuous_lift Unit E Subtype.val).comp
          ((continuous_apply i).comp hd.snd.fst)).prodMk
        (continuous_pi fun i ↦ (Pullback.continuous_lift Unit F Subtype.val).comp
          ((continuous_apply i).comp hd.snd.snd)))
    have hsum : Continuous (fun z : D' ↦
        (⟨z.proj, ∑ i : Fin m, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
          TotalSpace Unit (fun x ↦ E x ⊗[ℂ] F x))) :=
      continuous_iSup_rng (i := m) continuous_coinduced_rng
    rw [(inducing_pullbackTotalSpaceEmbedding Unit
      (fun x ↦ E x ⊗[ℂ] F x) (Subtype.val : A → X)).continuous_iff]
    exact hd.fst.prodMk (hsum.comp hlift)
  -- Finite local rank supplies inverse continuity for this exact identity map.
  let f : Hom (fun x : A ↦ (Restrict E A) x ⊗[ℂ] (Restrict F A) x)
      (Restrict (fun x ↦ E x ⊗[ℂ] F x) A) :=
    { linearMap := fun x ↦ LinearMap.id, continuous_total := hforward }
  let e := f.toIso (fun _ ↦ Function.bijective_id)
  have hback : Continuous (fun z : TotalSpace Unit (Restrict (fun x ↦ E x ⊗[ℂ] F x) A) ↦
      (⟨z.proj, z.snd⟩ : TotalSpace Unit
        (fun x : A ↦ (Restrict E A) x ⊗[ℂ] (Restrict F A) x))) := by
    refine e.continuous_symm.congr ?_
    intro z
    congr 1
    exact (e.linearEquiv z.proj).apply_symm_apply z.snd
  exact ⟨hback, hforward⟩

/-- The canonical restriction/tensor comparison is the actual identity on each tensor fiber. -/
def restrictTensorIso [IsFiniteRank E] [IsFiniteRank F] (A : Set X) :
    Iso (Restrict (fun x ↦ E x ⊗[ℂ] F x) A)
      (fun x : A ↦ (Restrict E A) x ⊗[ℂ] (Restrict F A) x) where
  linearEquiv x := LinearEquiv.refl ℂ (E x ⊗[ℂ] F x)
  continuous_total := (continuous_restrict_tensor (E := E) (F := F) A).1
  continuous_symm := (continuous_restrict_tensor (E := E) (F := F) A).2

end AtiyahSinger.ComplexBundle
