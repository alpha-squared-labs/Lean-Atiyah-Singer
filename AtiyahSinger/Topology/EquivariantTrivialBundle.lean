/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteContinuousRepresentation
public import AtiyahSinger.Topology.BundleTrivial
public import AtiyahSinger.Topology.EquivariantVectorBundle

/-!
# Product equivariant bundles from actual finite representations

Public module ID: M1819.

The product bundle X times V carries the diagonal action (x,v) -> (g*x,rho(g)v).
Both the original base action and the specified jointly continuous finite
representation are retained. The underlying bundle is trivial, but its fiber
action need not be trivial. Its topology is the previously defined product
topology on `TotalSpace Unit`, not a topology selected from existence.

Source: ASI §2, p.494, the equivariant-bundle definition; the diagonal product
construction is its standard elementary example. SG III.9, pp.211--212, supplies
the finite complex representation convention.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

attribute [local instance] trivialTopology

/-- The diagonal action of the original base action and a specified finite representation. -/
def EquivariantStructure.ofFiniteRepresentation (ρ : FiniteContinuousRepresentation G) :
    EquivariantStructure G (Bundle.Trivial X (Fin ρ.dimension → ℂ)) where
  linearMap g _ := (ρ.representation g).toLinearMap
  one_map x v := by
    apply TotalSpace.ext
    · exact one_smul G x
    · apply heq_of_eq
      change ρ.representation 1 v = v
      simp
  mul_map g h x v := by
    apply TotalSpace.ext
    · exact mul_smul g h x
    · apply heq_of_eq
      change ρ.representation (g * h) v = ρ.representation g (ρ.representation h v)
      rw [map_mul]
      rfl
  continuous_action := by
    -- The existing topology is induced by the actual base and vector coordinates.
    have hc : Continuous (fun z : TotalSpace Unit
        (Bundle.Trivial X (Fin ρ.dimension → ℂ)) ↦ (z.proj, z.snd)) :=
      continuous_induced_dom
    -- The two components use the supplied base action and joint representation continuity.
    exact continuous_induced_rng.mpr
      ((continuous_fst.smul (hc.fst.comp continuous_snd)).prodMk
        (ρ.continuous_action.comp (continuous_fst.prodMk (hc.snd.comp continuous_snd))))

end AtiyahSinger.ComplexBundle
