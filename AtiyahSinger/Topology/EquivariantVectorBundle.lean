/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleSum
public import Mathlib.Topology.Algebra.MulAction

/-!
# Continuous equivariant structures on the original complex bundle

Public module ID: M1820.

A G action on a vector bundle covers the specified action on its base and is
complex-linear on each moving fiber. The identity and composition equations are
written in the original total space to make the base transports explicit without
choosing fiber identifications. Joint continuity refers to that same topology.

The total-space action is native `MulAction` data assembled from these equations.
Equivariant bundle maps retain the original continuous bundle maps, and direct
sum retains the original product fibers and induced total topology.

Sources: ASI §2, printed p.494 / PDF p.12, for the continuous equivariant bundle
definition; SG III.9, pp.211--214, for smooth equivariant bundles and operators.
The standard continuous version is used here before smooth geometric realization.
Local finite rank is supplied by the original bundle whenever needed downstream;
the action and its linearity do not require a global rank or a compact group/base.
The moving-fiber bijections and the direct-sum action are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable (G : Type*) [Group G] [TopologicalSpace G]
  {X : Type*} [TopologicalSpace X] [MulAction G X]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- A jointly continuous complex-linear G action covering the specified action on the base. -/
structure EquivariantStructure [IsTopologicalGroup G] [ContinuousSMul G X] where
  /-- The actual linear map from the fiber at x to the fiber at g*x. -/
  linearMap : ∀ (g : G) (x : X), E x →ₗ[ℂ] E (g • x)
  /-- Identity acts as identity on the original total space, including its base coordinate. -/
  one_map : ∀ (x : X) (v : E x),
    (⟨(1 : G) • x, linearMap 1 x v⟩ : TotalSpace Unit E) = ⟨x, v⟩
  /-- Composition uses the moved intermediate base point and the original total space. -/
  mul_map : ∀ (g h : G) (x : X) (v : E x),
    (⟨(g * h) • x, linearMap (g * h) x v⟩ : TotalSpace Unit E) =
      ⟨g • (h • x), linearMap g (h • x) (linearMap h x v)⟩
  /-- Continuity jointly in the group element and vector in the existing total topology. -/
  continuous_action : Continuous (fun p : G × TotalSpace Unit E ↦
    (⟨p.1 • p.2.proj, linearMap p.1 p.2.proj p.2.snd⟩ : TotalSpace Unit E))

variable {G E} [IsTopologicalGroup G] [ContinuousSMul G X]

/-- The same fiber formulas, packaged as a native action on the original total space. -/
@[reducible]
def EquivariantStructure.toMulAction (σ : EquivariantStructure G E) :
    MulAction G (TotalSpace Unit E) where
  smul g z := ⟨g • z.proj, σ.linearMap g z.proj z.snd⟩
  one_smul z := σ.one_map z.proj z.snd
  mul_smul g h z := σ.mul_map g h z.proj z.snd

/-- Every group element gives a linear bijection between the two original moving fibers. -/
theorem EquivariantStructure.linearMap_bijective (σ : EquivariantStructure G E)
    (g : G) (x : X) : Function.Bijective (σ.linearMap g x) := by
  /- Stage 1: the native total-space action has inverse action by g inverse.
  On the fiber over g*x its inverse lands over g inverse*(g*x)=x. Transport
  only along this actual base equality to obtain the inverse fiber function.
  Stage 2: the two action laws give both inverse identities in TotalSpace.
  Equality of total vectors with the same base identifies the fiber vectors.
  Thus the specified linear map is bijective, without a chosen frame, a
  finite-dimensional argument or an invariant inner product. -/
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  constructor
  · -- Cancellation in the total-space group action detects equality in the same fiber.
    intro u v huv
    have htotal : g • (⟨x, u⟩ : TotalSpace Unit E) = g • ⟨x, v⟩ :=
      congrArg (fun w : E (g • x) ↦ (⟨g • x, w⟩ : TotalSpace Unit E)) huv
    exact TotalSpace.mk_injective x ((MulAction.injective g) htotal)
  · -- A total-space preimage necessarily lies over x, by cancellation on the base.
    intro v
    obtain ⟨⟨y, u⟩, hu⟩ := (MulAction.surjective g) (⟨g • x, v⟩ : TotalSpace Unit E)
    have hbase : y = x :=
      (MulAction.injective g) (congrArg (fun z : TotalSpace Unit E ↦ z.proj) hu)
    subst y
    exact ⟨u, TotalSpace.mk_injective (g • x) hu⟩

variable {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- An original continuous bundle map intertwines the two specified moving-fiber actions. -/
def Hom.IsEquivariant (f : Hom E F)
    (σ : EquivariantStructure G E) (τ : EquivariantStructure G F) : Prop :=
  ∀ (g : G) (x : X) (v : E x),
    f.linearMap (g • x) (σ.linearMap g x v) = τ.linearMap g x (f.linearMap x v)

/-- Equivariance of a bundle isomorphism means equivariance of its actual forward bundle map. -/
def Iso.IsEquivariant (e : Iso E F)
    (σ : EquivariantStructure G E) (τ : EquivariantStructure G F) : Prop :=
  e.toHom.IsEquivariant σ τ

attribute [local instance] sumTopology

/-- The componentwise sum action satisfies the action laws and is jointly continuous. -/
theorem EquivariantStructure.sum_properties
    (σ : EquivariantStructure G E) (τ : EquivariantStructure G F) :
    (∀ (x : X) (v : E x × F x),
      (⟨(1 : G) • x, (σ.linearMap 1 x v.1, τ.linearMap 1 x v.2)⟩ :
        TotalSpace Unit (E ×ᵇ F)) = ⟨x, v⟩) ∧
    (∀ (g h : G) (x : X) (v : E x × F x),
      (⟨(g * h) • x, (σ.linearMap (g * h) x v.1, τ.linearMap (g * h) x v.2)⟩ :
        TotalSpace Unit (E ×ᵇ F)) =
      ⟨g • (h • x), (σ.linearMap g (h • x) (σ.linearMap h x v.1),
        τ.linearMap g (h • x) (τ.linearMap h x v.2))⟩) ∧
    Continuous (fun p : G × TotalSpace Unit (E ×ᵇ F) ↦
      (⟨p.1 • p.2.proj, (σ.linearMap p.1 p.2.proj p.2.snd.1,
        τ.linearMap p.1 p.2.proj p.2.snd.2)⟩ : TotalSpace Unit (E ×ᵇ F))) := by
  /- Stage 1: project a direct-sum total vector to the two original totals.
  Each component satisfies the supplied identity and composition equations,
  with exactly the same base action. The two equalities therefore combine
  into the displayed total-space equations without choosing transports.
  Stage 2: the two projections from the original sum total space are continuous.
  Compose them with the two jointly continuous actions. The sum topology is
  induced by this pair of maps, so continuity of those components is exactly
  continuity of the displayed action. This one construction certificate also
  applies to the same-base double bundle used by continuous Hermitian metrics. -/
  -- Equal component totals determine the same sum total, including its base transport.
  have hpair {x y : X} {u : E x} {v : F x} {w : E y} {z : F y}
      (hE : (⟨x, u⟩ : TotalSpace Unit E) = ⟨y, w⟩)
      (hF : (⟨x, v⟩ : TotalSpace Unit F) = ⟨y, z⟩) :
      (⟨x, (u, v)⟩ : TotalSpace Unit (E ×ᵇ F)) = ⟨y, (w, z)⟩ := by
    have hxy := congrArg (fun t : TotalSpace Unit E ↦ t.proj) hE
    dsimp only at hxy
    subst y
    have hu := TotalSpace.mk_injective x hE
    have hv := TotalSpace.mk_injective x hF
    cases hu
    cases hv
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro x v
    exact hpair (σ.one_map x v.1) (τ.one_map x v.2)
  · intro g h x v
    exact hpair (σ.mul_map g h x v.1) (τ.mul_map g h x v.2)
  · -- The existing induced topology tests the action on each original summand.
    apply continuous_induced_rng.mpr
    exact (σ.continuous_action.comp
      (continuous_fst.prodMk (continuous_sum_fst.comp continuous_snd))).prodMk
      (τ.continuous_action.comp
        (continuous_fst.prodMk (continuous_sum_snd.comp continuous_snd)))

/-- The direct-sum action on the original product fibers and induced sum topology. -/
def EquivariantStructure.sum (σ : EquivariantStructure G E)
    (τ : EquivariantStructure G F) : EquivariantStructure G (E ×ᵇ F) where
  linearMap g x := (σ.linearMap g x).prodMap (τ.linearMap g x)
  one_map := (σ.sum_properties τ).1
  mul_map := (σ.sum_properties τ).2.1
  continuous_action := (σ.sum_properties τ).2.2

end AtiyahSinger.ComplexBundle
