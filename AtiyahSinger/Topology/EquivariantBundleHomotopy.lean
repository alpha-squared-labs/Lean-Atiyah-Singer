/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleHomotopyType
public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Topology.EquivariantCylinder
public import AtiyahSinger.Topology.EquivariantPullbackTransport

/-!
# Equivariant homotopy invariance of actual bundle pullbacks

Public module ID: M1766.

An actual equivariant homotopy induces an equivariant isomorphism between
the two endpoint pullbacks of the original locally finite-rank bundle.
The source is paracompact Hausdorff and may be noncompact. The acting group
is compact Hausdorff; its action fixes the interval coordinate. No smooth
structure, global rank bound or properness of the homotopy is required.

Karoubi I.9.31(f,g), printed p.50, states the compact-group equivariant
cylinder result with compact base. The paracompact extension uses the
numerable assembly of Hatcher, Vector Bundles and K-Theory, Theorem 1.6
and Proposition 1.7, pp.20--21, together with near-identity equivariant
transport. The combined noncompact equivariant generality is an explicit
project supplement. Neither ordinary
forgetting nor averaging an arbitrary isomorphism supplies this result.

The theorem is a prerequisite for reducing bundles on a vector-bundle
total space to pullbacks from the zero section. Such a contraction need
not be proper and is not being used as a compact-support K pullback.
The proof uses identity-normalized Haar transport and positive invariant
local time steps, followed by the original vector-preserving endpoint comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [TopologicalSpace X] [hXT : T2Space X] [hXP : ParacompactSpace X]
  [MulAction G X] [ContinuousSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]

include hGC hGT hXT hXP hE

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Endpoint comparisons keep the native definitionally identical pullback fibers visible.
/-- Equivariantly homotopic maps induce equivariantly isomorphic original pullback bundles. -/
theorem EquivariantStructure.exists_pullback_iso_of_homotopy
    (ρ : EquivariantStructure G E) (f₀ f₁ : C(X, Y))
    (hf₀ : ∀ (g : G) (x : X), f₀ (g • x) = g • f₀ x)
    (hf₁ : ∀ (g : G) (x : X), f₁ (g • x) = g • f₁ x)
    (H : ContinuousMap.Homotopy f₀ f₁)
    (hH : ∀ (t : unitInterval) (g : G) (x : X), H (t, g • x) = g • H (t, x)) :
    ∃ e : Iso ((f₀ : X → Y) *ᵖ E) ((f₁ : X → Y) *ᵖ E),
      e.IsEquivariant (ρ.pullback f₀ hf₀) (ρ.pullback f₁ hf₁) := by
  classical
  -- The original homotopy pulls the given action to a cylinder whose time
  -- coordinate is fixed by the group. This is a bundle pullback, with no properness requirement.
  let : MulAction G (X × unitInterval) := {
    smul g z := (g • z.1, z.2)
    one_smul z := Prod.ext (one_smul G z.1) rfl
    mul_smul g h z := Prod.ext (mul_smul g h z.1) rfl }
  let : ContinuousSMul G (X × unitInterval) :=
    ⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)⟩
  let c : C(X × unitInterval, Y) :=
    ⟨fun z ↦ H (z.2, z.1), H.continuous.comp continuous_swap⟩
  have hc (g : G) (z : X × unitInterval) : c (g • z) = g • c z := hH z.2 g z.1
  let p₀ : C(X, X × unitInterval) :=
    ⟨fun x ↦ (x, 0), continuous_id.prodMk continuous_const⟩
  let p₁ : C(X, X × unitInterval) :=
    ⟨fun x ↦ (x, 1), continuous_id.prodMk continuous_const⟩
  have hp₀ (g : G) (x : X) : p₀ (g • x) = g • p₀ x := rfl
  have hp₁ (g : G) (x : X) : p₁ (g • x) = g • p₁ x := rfl
  let := isFiniteRank_pullback (E := E) c
  obtain ⟨i, hi⟩ := (ρ.pullback c hc).exists_equivariant_endpoint_iso
    (E := (c : X × unitInterval → Y) *ᵖ E) (fun _ _ _ ↦ rfl)
  have h₀ : c.comp p₀ = f₀ := by
    apply ContinuousMap.ext
    intro x
    exact H.apply_zero x
  have h₁ : c.comp p₁ = f₁ := by
    apply ContinuousMap.ext
    intro x
    exact H.apply_one x
  -- The comparison isomorphisms preserve actual vectors and intertwine the
  -- iterated pulled actions. Endpoint equalities change only their base labels.
  let e₀ := pullbackCompIso (E := E) c p₀
  let e₁ := pullbackCompIso (E := E) c p₁
  have he₀inv (x : X) (v : E (c (p₀ x))) : (e₀.linearEquiv x).symm v = v := by
    apply (e₀.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (pullbackCompIso_apply c p₀ x v).symm
  have hact₀ (g : G) (x : X) (v : E (c (p₀ x))) :
      ((ρ.pullback c hc).pullback p₀ hp₀).linearMap g x v =
        (ρ.pullback (c.comp p₀) (fun g x ↦ (congrArg c (hp₀ g x)).trans
          (hc g (p₀ x)))).linearMap g x v := by
    have ht := ρ.pullbackCompIso_isEquivariant c hc p₀ hp₀ g x v
    dsimp only [Iso.IsEquivariant, Hom.IsEquivariant, Iso.toHom] at ht
    simpa only [e₀, LinearEquiv.coe_coe, pullbackCompIso_apply] using ht
  have hact₁ (g : G) (x : X) (v : E (c (p₁ x))) :
      ((ρ.pullback c hc).pullback p₁ hp₁).linearMap g x v =
        (ρ.pullback (c.comp p₁) (fun g x ↦ (congrArg c (hp₁ g x)).trans
          (hc g (p₁ x)))).linearMap g x v := by
    have ht := ρ.pullbackCompIso_isEquivariant c hc p₁ hp₁ g x v
    dsimp only [Iso.IsEquivariant, Hom.IsEquivariant, Iso.toHom] at ht
    simpa only [e₁, LinearEquiv.coe_coe, pullbackCompIso_apply] using ht
  revert hf₀ hf₁
  rw [← h₀, ← h₁]
  intro hf₀ hf₁
  refine ⟨e₀.symm.trans (i.trans e₁), ?_⟩
  intro g x v
  change e₁.linearEquiv (g • x) (i.linearEquiv (g • x)
      ((e₀.linearEquiv (g • x)).symm _)) =
    (ρ.pullback (c.comp p₁) _).linearMap g x
      (e₁.linearEquiv x (i.linearEquiv x ((e₀.linearEquiv x).symm v)))
  simp only [e₁, pullbackCompIso_apply, he₀inv]
  rw [← hact₀]
  exact (hi g x v).trans (hact₁ g x (i.linearEquiv x v))

end AtiyahSinger.ComplexBundle
