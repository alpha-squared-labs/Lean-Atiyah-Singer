/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleRestriction
public import AtiyahSinger.Topology.EquivariantBundlePullback
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Invariant rank strata of the original continuous complex bundle

Public module ID: M1802.

The rank of a locally finite-rank bundle is locally constant. Its rank strata
are the actual open subspaces of the original base, with their inherited
topology. The original equivariant action preserves every stratum because its
moving-fiber linear maps are bijections. The native `MulAction` structure below
restricts the same action to exactly that subtype, not to a replacement space.
Equivariant restriction uses the existing original-bundle pullback.

Sources: Karoubi I.2.9, printed p.7, defines the locally constant rank function;
II.1.26 and II.1.28--1.29, printed pp.56--57, describe finite open decompositions
and the finitely many rank values on a compact base. Clopen fibers and finite
range on compact spaces are reused from mathlib's `IsLocallyConstant` API.
Rank invariance is the direct linear-algebra consequence of the equivariant
bundle definition, not a separately numbered theorem in those passages.
The proofs retain the original fibers and the explicit subtype action adapters.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace

variable {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- The actual fiber dimension of a locally finite-rank bundle is locally constant. -/
theorem isLocallyConstant_finrank [IsFiniteRank E] :
    IsLocallyConstant (fun x : X ↦ Module.finrank ℂ (E x)) := by
  /- Stage 1: at x choose the original linear trivialization with model C^r.
  Its base set is an open neighborhood of x. At each y in that same set,
  the fiber coordinate map is linear and bijective, with inverse supplied
  by the existing trivialization. Thus E_y is linearly equivalent to C^r.
  Stage 2: invariance of finrank under these linear equivalences identifies
  every fiber rank on this neighborhood with r, including the rank at x.
  Apply IsLocallyConstant.iff_exists_open. No fixed global rank, separation,
  compactness, connectedness or chosen fiber norm is used. -/
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨r, e, hx, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := E) x
  -- Every fiber in this single chart has the same finite coordinate space.
  have hr (y : X) (hy : y ∈ e.baseSet) : Module.finrank ℂ (E y) = r := by
    let l : E y ≃ₗ[ℂ] (Fin r → ℂ) :=
      { toFun := fun v ↦ (e ⟨y, v⟩).2
        invFun := fun v ↦ cast (congrArg E (e.proj_symm_apply' hy))
          (e.toOpenPartialHomeomorph.symm (y, v)).snd
        left_inv := by
          intro v
          rw [cast_eq_iff_heq]
          exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd)
            (e.symm_apply_mk_proj (x := ⟨y, v⟩) (e.mem_source.mpr hy))
        right_inv := by
          intro v
          have hp := TotalSpace.mk_cast (F := Unit) (E := E)
            (e.proj_symm_apply' (x := v) hy) (e.toOpenPartialHomeomorph.symm (y, v)).snd
          exact (congrArg (fun z : TotalSpace Unit E ↦ (e z).2) hp).trans
            (congrArg Prod.snd (e.apply_symm_apply' hy))
        map_add' := (hlinear y hy).map_add
        map_smul' := (hlinear y hy).map_smul }
    simpa using l.finrank_eq
  exact ⟨e.baseSet, e.open_baseSet, hx, fun y hy ↦ (hr y hy).trans (hr x hx).symm⟩

/-- The actual open subspace on which the original bundle has rank r. -/
def rankStratum [IsFiniteRank E] (r : ℕ) : Opens X :=
  ⟨{x : X | Module.finrank ℂ (E x) = r},
    (isLocallyConstant_finrank E).isOpen_fiber r⟩

variable {E}
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G X] [ContinuousSMul G X]

/-- The original moving-fiber action preserves the actual algebraic fiber dimension. -/
theorem EquivariantStructure.finrank_smul (σ : EquivariantStructure G E)
    (g : G) (x : X) :
    Module.finrank ℂ (E (g • x)) = Module.finrank ℂ (E x) := by
  /- Stage 1: use linearMap_bijective for the specified map sigma.linearMap g x.
  Package this same map as a linear equivalence with LinearEquiv.ofBijective.
  Stage 2: apply invariance of finrank and reverse its equality. This argument
  does not need a finite-rank bundle or any compactness or smoothness. In
  particular, it applies even when G permutes connected components of X. -/
  -- The equivalence uses the given action map, not a separately chosen identification.
  let e := LinearEquiv.ofBijective (σ.linearMap g x) (σ.linearMap_bijective g x)
  exact e.finrank_eq.symm

/-- The native action on the actual rank stratum, using the original base action. -/
@[reducible]
def EquivariantStructure.rankStratumMulAction [IsFiniteRank E]
    (σ : EquivariantStructure G E) (r : ℕ) : MulAction G (rankStratum E r) where
  smul g x := ⟨g • x.val, (σ.finrank_smul g x.val).trans x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

/-- Joint continuity inherited through the original rank-stratum inclusion. -/
instance EquivariantStructure.continuousSMul_rankStratum [IsFiniteRank E]
    (σ : EquivariantStructure G E) (r : ℕ) :
    letI := σ.rankStratumMulAction r
    ContinuousSMul G (rankStratum E r) := by
  let _ := σ.rankStratumMulAction r
  -- The subtype inclusion sends the restricted action to the same ambient action.
  exact Topology.IsInducing.subtypeVal.continuousSMul
    (f := id) continuous_id (fun {g x} ↦ rfl)

end AtiyahSinger.ComplexBundle
