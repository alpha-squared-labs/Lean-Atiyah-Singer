/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ContinuousHermitianMetric
public import AtiyahSinger.Topology.ExteriorBundleSum
public import AtiyahSinger.Topology.SphereHodgeSymbolComparison

/-!
# The exterior Hodge phase on the original parity bundle

Public module ID: M1843.

Scalar multiplication by i induces a continuous map in the original exterior
bundle topology. Its original parity restrictions are bijective, hence define
one continuous bundle automorphism. The supplied Hermitian core is used only to
state the pointwise identification with the existing phase equivalence.

Source: SG II.5, the exterior degree phase, and the original exterior bundle functor.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] exteriorTopology exteriorParityTopology isFiniteRank_exterior
  isFiniteRank_exteriorParity

variable {X : Type*} [TopologicalSpace X]
  (E : X → Type) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E) (i : ZMod 2)

set_option backward.isDefEq.respectTransparency false in
/-- The pointwise exterior phase is a continuous automorphism of the original parity bundle. -/
def exteriorHodgePhaseBundleIso :
    Iso (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i)
      (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i) := by
  let phase (x : X) :=
    letI : FiniteDimensional ℂ (E x) := finite_fiber (E := E) x
    let core := h.toCore x
    letI : NormedAddCommGroup (E x) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (E x) := InnerProductSpace.ofCore core.toCore
    exteriorHodgePhaseEquiv (E x) i
  -- Scalar multiplication is continuous on the supplied finite-rank total topology.
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let : IsFiniteRank ((p : TotalSpace Unit E → X) *ᵖ E) := isFiniteRank_pullback p
  have hv : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z, z.snd⟩ : TotalSpace Unit ((p : TotalSpace Unit E → X) *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    exact continuous_id.prodMk continuous_id
  have hscale : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, Complex.I • z.snd⟩ : TotalSpace Unit E)) :=
    (Pullback.continuous_lift Unit E p).comp
      (continuous_smul_section _ (ContinuousMap.const _ Complex.I) _ hv)
  let f : Hom E E :=
    { linearMap x := Complex.I • (LinearMap.id : E x →ₗ[ℂ] E x)
      continuous_total := hscale }
  -- Restrict the same continuous exterior map through the induced parity topology.
  let F : Hom (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i)
      (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i) :=
    { linearMap x := (phase x).toLinearMap
      continuous_total := by
        apply continuous_induced_rng.mpr
        have hi : Continuous (fun z : TotalSpace Unit
            (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i) ↦
              (⟨z.proj, z.snd.val⟩ : TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) :=
          continuous_induced_dom
        exact f.exterior.continuous_total.comp hi }
  exact F.toIso (fun x ↦ (phase x).bijective)

/-- The continuous phase has exactly the original exterior scalar-map formula. -/
theorem exteriorHodgePhaseBundleIso_apply (x : X)
    (a : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i) :
    ((exteriorHodgePhaseBundleIso E h i).linearEquiv x a : ExteriorAlgebra ℂ (E x)) =
      ExteriorAlgebra.map (Complex.I • (LinearMap.id : E x →ₗ[ℂ] E x)) a.val := rfl

/-- The continuous phase agrees with the original phase for the supplied Hermitian core. -/
theorem exteriorHodgePhaseBundleIso_eq (x : X) :
    letI : FiniteDimensional ℂ (E x) := finite_fiber (E := E) x
    let core := h.toCore x
    letI : NormedAddCommGroup (E x) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (E x) := InnerProductSpace.ofCore core.toCore
    (exteriorHodgePhaseBundleIso E h i).linearEquiv x = exteriorHodgePhaseEquiv (E x) i := by
  ext a
  rfl

end AtiyahSinger
