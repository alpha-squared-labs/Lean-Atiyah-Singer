/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeTriple

/-!
# Bundled finite-rank complex vector bundles

Public module ID: M1847.

This packages only the existing locally finite-rank bundle data.
Fibers are in Type 0 so triples range over a single universe. Any finite-rank
family in a larger universe has an isomorphic small model; that resizing is a
separate theorem, not a global bound on the ranks. Sources: SG I.9 and KA I.1–2.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]


/-- A continuous complex vector bundle with locally finite, possibly varying, rank. -/
structure FiniteBundle (X : Type*) [TopologicalSpace X] where
  /-- The fibers, in one fixed universe for forming the collection of triples. -/
  Fiber : X → Type
  /-- Addition on each original fiber. -/
  [addCommGroup : ∀ x, AddCommGroup (Fiber x)]
  /-- Complex scalar multiplication on each original fiber. -/
  [module : ∀ x, Module ℂ (Fiber x)]
  /-- The original topology on the total space. -/
  [totalTopology : TopologicalSpace (TotalSpace Unit Fiber)]
  /-- Local finite linear triviality, with no globally fixed rank. -/
  [isFiniteRank : IsFiniteRank Fiber]

attribute [instance] FiniteBundle.addCommGroup FiniteBundle.module
  FiniteBundle.totalTopology FiniteBundle.isFiniteRank

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial
  isFiniteRank_pullback

/-- Package an existing small family without altering any of its structures. -/
@[reducible]
def FiniteBundle.ofFamily (E : X → Type) [∀ x, AddCommGroup (E x)]
    [∀ x, Module ℂ (E x)] [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E] :
    FiniteBundle X where
  Fiber := E

/-- The finite trivial bundle with its actual product topology. -/
@[reducible]
def FiniteBundle.trivial (X : Type*) [TopologicalSpace X] (n : ℕ) : FiniteBundle X where
  Fiber := Bundle.Trivial X (Fin n → ℂ)

/-- Direct sum uses the product fibers and the existing induced topology. -/
@[reducible]
def FiniteBundle.sum (E F : FiniteBundle X) : FiniteBundle X where
  Fiber := E.Fiber ×ᵇ F.Fiber

/-- Pullback uses the existing mathlib pullback topology. -/
@[reducible]
def FiniteBundle.pullback (E : FiniteBundle Y) (f : C(X, Y)) : FiniteBundle X where
  Fiber := (f : X → Y) *ᵖ E.Fiber

/-- Restriction is pullback along the subtype inclusion. -/
@[reducible]
def FiniteBundle.restrict (E : FiniteBundle X) (A : Set X) : FiniteBundle A :=
  E.pullback ⟨Subtype.val, continuous_subtype_val⟩

/-- Finite-rank bundle families in any universe admit small isomorphic models. -/
theorem exists_small_bundle (E : X → Type*) [∀ x, AddCommGroup (E x)]
    [∀ x, Module ℂ (E x)] [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E] :
    ∃ F : FiniteBundle X, Nonempty (Iso E F.Fiber) := by
  /- Each fiber is finite dimensional. Choose a finite basis at each point and
  use its coordinate space Fin(rank(x)) → ℂ as a small fiber. Transport the
  original total-space topology along the resulting fiberwise bijection and
  transport local linear charts. The ranks may vary and need not be bounded;
  no continuous choice of basis or trivialization is being asserted. -/
  classical
  -- Choose a finite coordinate chart separately at each point; no continuous choice is needed.
  choose r t ht hlinear using IsFiniteRank.exists_linear_trivialization (E := E)
  let F : X → Type := fun x ↦ Fin (r x) → ℂ
  let e (x : X) : E x ≃ₗ[ℂ] F x :=
    { toFun := fun v ↦ (t x ⟨x, v⟩).2
      invFun := fun v ↦ cast (congrArg E ((t x).proj_symm_apply' (ht x)))
        ((t x).toOpenPartialHomeomorph.symm (x, v)).snd
      left_inv := by
        intro v
        rw [cast_eq_iff_heq]
        exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd)
          ((t x).symm_apply_mk_proj (x := ⟨x, v⟩) ((t x).mem_source.mpr (ht x)))
      right_inv := by
        intro v
        have hp := TotalSpace.mk_cast (F := Unit) (E := E)
          ((t x).proj_symm_apply' (x := v) (ht x))
          ((t x).toOpenPartialHomeomorph.symm (x, v)).snd
        exact (congrArg (fun z : TotalSpace Unit E ↦ (t x z).2) hp).trans
          (congrArg Prod.snd ((t x).apply_symm_apply' (ht x)))
      map_add' := (hlinear x x (ht x)).map_add
      map_smul' := (hlinear x x (ht x)).map_smul }
  -- Transport the original total topology through this explicit fiberwise equivalence.
  let totalEquiv : TotalSpace Unit E ≃ TotalSpace Unit F :=
    { toFun := fun z ↦ ⟨z.proj, e z.proj z.snd⟩
      invFun := fun z ↦ ⟨z.proj, (e z.proj).symm z.snd⟩
      left_inv := fun z ↦ congrArg (TotalSpace.mk z.proj) ((e z.proj).symm_apply_apply z.snd)
      right_inv := fun z ↦ congrArg (TotalSpace.mk z.proj) ((e z.proj).apply_symm_apply z.snd) }
  let : TopologicalSpace (TotalSpace Unit F) :=
    TopologicalSpace.induced totalEquiv.symm inferInstance
  let i : Iso E F :=
    { linearEquiv := e
      continuous_total := by
        apply continuous_induced_rng.mpr
        change Continuous (fun z ↦ totalEquiv.symm (totalEquiv z))
        apply continuous_id.congr
        intro z
        exact (totalEquiv.symm_apply_apply z).symm
      continuous_symm := continuous_induced_dom }
  -- The actual bundle isomorphism transports local linear charts to the small family.
  let : IsFiniteRank F := i.isFiniteRank
  exact ⟨FiniteBundle.ofFamily F, ⟨i⟩⟩

/-- Choose a small model only from the isomorphic-model theorem. -/
def smallBundle (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E] : FiniteBundle X :=
  (exists_small_bundle E).choose

/-- The actual isomorphism to the chosen small model. -/
def smallBundleIso (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E] : Iso E (smallBundle E).Fiber :=
  (exists_small_bundle E).choose_spec.some

/-- Bundled direct sum is commutative up to actual bundle isomorphism. -/
theorem FiniteBundle.nonempty_sum_comm_iso (E F : FiniteBundle X) :
    Nonempty (Iso (E.sum F).Fiber (F.sum E).Fiber) := by
  /- Swap the two fiber components using the existing direct-sum isomorphism.
  The two induced total-space topologies record the same original components. -/
  exact ⟨sumCommIso⟩

/-- Associating three direct sums preserves their three actual coordinates. -/
theorem FiniteBundle.exists_sum_assoc_iso (E F G : FiniteBundle X) :
    ∃ e : Iso ((E.sum F).sum G).Fiber (E.sum (F.sum G)).Fiber,
      ∀ x v, e.linearEquiv x v = (v.1.1, v.1.2, v.2) := by
  /- Use the linear associator ((u,v),w) ↦ (u,(v,w)). Each total topology
  is induced by the same three original total spaces and the common base point.
  The coordinate maps in both directions are therefore continuous. -/
  -- Reassociate the original three fiber vectors, retaining their common base point.
  let e : Iso ((E.sum F).sum G).Fiber (E.sum (F.sum G)).Fiber :=
    { linearEquiv x := LinearEquiv.prodAssoc ℂ (E.Fiber x) (F.Fiber x) (G.Fiber x)
      continuous_total := by
        apply continuous_induced_rng.mpr
        have hEF := continuous_sum_fst (E := (E.sum F).Fiber) (F := G.Fiber)
        have hE := (continuous_sum_fst (E := E.Fiber) (F := F.Fiber)).comp hEF
        have hF := (continuous_sum_snd (E := E.Fiber) (F := F.Fiber)).comp hEF
        have hG := continuous_sum_snd (E := (E.sum F).Fiber) (F := G.Fiber)
        exact hE.prodMk (continuous_induced_rng.mpr (hF.prodMk hG))
      continuous_symm := by
        apply continuous_induced_rng.mpr
        have hFG := continuous_sum_snd (E := E.Fiber) (F := (F.sum G).Fiber)
        have hE := continuous_sum_fst (E := E.Fiber) (F := (F.sum G).Fiber)
        have hF := (continuous_sum_fst (E := F.Fiber) (F := G.Fiber)).comp hFG
        have hG := (continuous_sum_snd (E := F.Fiber) (F := G.Fiber)).comp hFG
        exact (continuous_induced_rng.mpr (hE.prodMk hF)).prodMk hG }
  exact ⟨e, fun _ _ ↦ rfl⟩

/-- The direct-sum associator specified by its coordinate formula. -/
def FiniteBundle.sumAssocIso (E F G : FiniteBundle X) :
    Iso ((E.sum F).sum G).Fiber (E.sum (F.sum G)).Fiber :=
  (E.exists_sum_assoc_iso F G).choose

/-- The associator keeps all three vectors. -/
theorem FiniteBundle.sumAssocIso_apply (E F G : FiniteBundle X) (x : X)
    (v : ((E.sum F).sum G).Fiber x) :
    (E.sumAssocIso F G).linearEquiv x v = (v.1.1, v.1.2, v.2) := by
  /- Use the coordinate identity from the existence theorem selecting the
  associator. The choice cannot introduce any unrelated automorphism on a fiber. -/
  exact (E.exists_sum_assoc_iso F G).choose_spec x v

/-- Adding the zero-rank trivial bundle has the vector projection as an isomorphism. -/
theorem FiniteBundle.exists_sum_zero_iso (E : FiniteBundle X) :
    ∃ e : Iso (E.sum (FiniteBundle.trivial X 0)).Fiber E.Fiber,
      ∀ x v, e.linearEquiv x v = v.1 := by
  /- The second fiber is the zero-dimensional coordinate space and has a unique
  vector. Projection and insertion of that zero vector are inverse linear maps;
  local finite rank ensures the zero section and original projections are continuous. -/
  -- Projection forgets the unique zero-dimensional vector; insertion restores it.
  let e : Iso (E.sum (FiniteBundle.trivial X 0)).Fiber E.Fiber :=
    { linearEquiv x :=
        { toFun := Prod.fst
          invFun := fun v ↦ (v, 0)
          left_inv := fun v ↦ Prod.ext rfl (Subsingleton.elim _ _)
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      continuous_total := continuous_sum_fst
      continuous_symm := continuous_sum_inl }
  exact ⟨e, fun _ _ ↦ rfl⟩

/-- The right unit comparison for direct sum. -/
def FiniteBundle.sumZeroIso (E : FiniteBundle X) :
    Iso (E.sum (FiniteBundle.trivial X 0)).Fiber E.Fiber :=
  E.exists_sum_zero_iso.choose

/-- The class of a bundled vector bundle in the existing absolute K group. -/
def FiniteBundle.kZeroClass [CompactSpace X] [T2Space X] (E : FiniteBundle X) :
    ComplexKZero X :=
  ComplexBundle.kZeroClass E.Fiber

/-- The class of a direct sum is the sum of the classes. -/
theorem FiniteBundle.kZeroClass_sum [CompactSpace X] [T2Space X] (E F : FiniteBundle X) :
    (E.sum F).kZeroClass = E.kZeroClass + F.kZeroClass := by
  /- Apply the established geometric bundle direct-sum formula to the underlying
  families. Bundling has not changed the fibers, induced topology or K-class construction. -/
  exact ComplexBundle.kZeroClass_sum

/-- Bundle classes are natural under the specified pullback. -/
theorem FiniteBundle.kZeroClass_pullback [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (E : FiniteBundle Y) (f : C(X, Y)) :
    (E.pullback f).kZeroClass = complexKZeroPullback f E.kZeroClass := by
  /- The bundled pullback is precisely the existing geometric pullback family.
  Apply its K-class naturality statement; no additional presentation is chosen here. -/
  exact ComplexBundle.kZeroClass_pullback f

end AtiyahSinger.ComplexBundle
