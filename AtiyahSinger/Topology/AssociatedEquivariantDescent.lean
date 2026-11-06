/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedEquivariantBundle
public import AtiyahSinger.Topology.BundleIso

/-!
# Covariant coordinates on an associated equivariant bundle

Public module ID: M1532.

An orbit-invariant continuous total-coordinate map, linear and bijective in
each representative fiber, identifies the actual descended equivariant bundle
with the specified bundle on the original associated base. This is the standard
associated descent argument from HU IV.5, applied without choosing a continuous
principal section. It is used to identify the original exterior Bott boundary
with the exterior Thom boundary in orthogonal frame coordinates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  isFiniteRank_associatedEquivariant

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Orbit-invariant continuous fiber coordinates identify the actual descended bundle. -/
theorem exists_associatedEquivariant_iso_of_covariant_equiv
    (hP : IsPrincipalBundle G projection) (σ : EquivariantStructure G E)
    (F : AssociatedBundle G P Y → Type*) [∀ z, AddCommGroup (F z)] [∀ z, Module ℂ (F z)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (L : ∀ (p : P) (y : Y), E y ≃ₗ[ℂ] F (associatedBundleMk G P Y p y))
    (hc : Continuous (fun z : P × TotalSpace Unit E ↦
      (⟨associatedBundleMk G P Y z.1 z.2.proj, L z.1 z.2.proj z.2.snd⟩ :
        TotalSpace Unit F)))
    (hcov : letI := σ.toMulAction
      ∀ (p : P) (g : G) (w : TotalSpace Unit E),
        (⟨associatedBundleMk G P Y (MulOpposite.op g • p) (g⁻¹ • w.proj),
          L (MulOpposite.op g • p) (g⁻¹ • w.proj) (σ.linearMap g⁻¹ w.proj w.snd)⟩ :
            TotalSpace Unit F) =
          ⟨associatedBundleMk G P Y p w.proj, L p w.proj w.snd⟩) :
    ∃ a : Iso (AssociatedEquivariantFiber hP σ) F,
      ∀ (p : P) (y : Y) (v : E y),
        a.linearEquiv (associatedBundleMk G P Y p y)
            (associatedEquivariantFiberMk hP σ p y rfl v) = L p y v := by
  let := σ.toMulAction
  let f : P × TotalSpace Unit E → TotalSpace Unit F := fun z ↦
    ⟨associatedBundleMk G P Y z.1 z.2.proj, L z.1 z.2.proj z.2.snd⟩
  -- Descend the complete map through the original orbit quotient.
  let Q : AssociatedBundle G P (TotalSpace Unit E) → TotalSpace Unit F :=
    Quotient.lift f (by
      intro x y hxy
      obtain ⟨g, rfl⟩ := hxy
      exact (hcov x.1 g x.2).symm)
  have hQ : Continuous Q := continuous_quot_lift _ hc
  have hbase (z : AssociatedBundle G P (TotalSpace Unit E)) :
      (Q z).proj = associatedEquivariantProjection σ z := by
    induction z using Quotient.inductionOn with
    | h w => rfl
  let a (z : AssociatedBundle G P Y) (v : AssociatedEquivariantFiber hP σ z) : F z :=
    cast (congrArg F ((hbase v.val).trans v.property)) (Q v.val).snd
  have hformula (p : P) (y : Y) (v : E y) :
      a (associatedBundleMk G P Y p y)
        (associatedEquivariantFiberMk hP σ p y rfl v) = L p y v := by
    dsimp only [a]
    rfl
  have hlinear (z : AssociatedBundle G P Y) : IsLinearMap ℂ (a z) := by
    obtain ⟨p, y, rfl⟩ : ∃ (p : P) (y : Y), associatedBundleMk G P Y p y = z :=
      ⟨(Quotient.out z).1, (Quotient.out z).2, Quotient.out_eq z⟩
    have hm := associatedEquivariantFiberMk_isLinear hP σ p y rfl
    have hs := (associatedEquivariantFiberMk_bijective hP σ p y rfl).surjective
    constructor
    · intro u v
      obtain ⟨u, rfl⟩ := hs u
      obtain ⟨v, rfl⟩ := hs v
      rw [← hm.map_add, hformula, hformula, hformula, map_add]
    · intro c v
      obtain ⟨v, rfl⟩ := hs v
      rw [← hm.map_smul, hformula, hformula, map_smul]
  have hbij (z : AssociatedBundle G P Y) : Function.Bijective (a z) := by
    obtain ⟨p, y, rfl⟩ : ∃ (p : P) (y : Y), associatedBundleMk G P Y p y = z :=
      ⟨(Quotient.out z).1, (Quotient.out z).2, Quotient.out_eq z⟩
    have h := associatedEquivariantFiberMk_bijective hP σ p y rfl
    have heq : a (associatedBundleMk G P Y p y) ∘
        associatedEquivariantFiberMk hP σ p y rfl = L p y := funext (hformula p y)
    apply (Function.Bijective.of_comp_iff (a (associatedBundleMk G P Y p y)) h).mp
    rw [heq]
    exact (L p y).bijective
  -- The source total homeomorphism retains its original quotient topology.
  let A : Hom (AssociatedEquivariantFiber hP σ) F :=
    { linearMap := fun z ↦ IsLinearMap.mk' (a z) (hlinear z)
      continuous_total := by
        have hh := hQ.comp (associatedEquivariantTotalHomeomorph hP σ).continuous
        apply hh.congr
        intro w
        change Q w.snd.val = ⟨w.proj, a w.proj w.snd⟩
        exact (TotalSpace.mk_cast (F := Unit) (E := F)
          ((hbase w.snd.val).trans w.snd.property) (Q w.snd.val).snd).symm }
  exact ⟨A.toIso hbij, hformula⟩

end AtiyahSinger
