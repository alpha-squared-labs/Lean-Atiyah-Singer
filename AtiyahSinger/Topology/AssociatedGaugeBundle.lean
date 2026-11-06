/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedEquivariantDescent
public import AtiyahSinger.Topology.AssociatedGaugeProduct

/-!
# Equivariant bundle descent in a principal gauge

Public module ID: M1534.

The actual gauge identifies each associated fiber with the original fiber at
the gauge-transformed point. The action on vectors, rather than a comparison
of their dimensions, supplies the continuous bundle isomorphism. It is used
for the support boundary and representation coefficient in the discrete-base
branch of the associated sphere index formula.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  isFiniteRank_associatedEquivariant isFiniteRank_pullback

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

/-- The original fiber coordinate after the supplied right-equivariant principal gauge. -/
def associatedGaugeProjection (θ : C(P, G))
    (hθ : ∀ (p : P) (g : G), θ (MulOpposite.op g • p) = θ p * g) :
    C(AssociatedBundle G P Y, Y) where
  toFun := Quotient.lift (fun z : P × Y ↦ θ z.1 • z.2) (by
    rintro x y ⟨g, rfl⟩
    simp only [hθ, mul_smul, smul_inv_smul])
  continuous_toFun := continuous_quot_lift _
    ((θ.continuous.comp continuous_fst).smul continuous_snd)

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A principal gauge transports the actual descended bundle by its original vector action. -/
theorem exists_associatedEquivariant_iso_gauge
    (hP : IsPrincipalBundle G projection) (θ : C(P, G))
    (hθ : ∀ (p : P) (g : G), θ (MulOpposite.op g • p) = θ p * g)
    (E : Y → Type*) [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (σ : EquivariantStructure G E) :
    ∃ a : Iso (AssociatedEquivariantFiber hP σ)
        ((associatedGaugeProjection (Y := Y) θ hθ : AssociatedBundle G P Y → Y) *ᵖ E),
      ∀ (p : P) (y : Y) (v : E y),
        a.linearEquiv (associatedBundleMk G P Y p y)
          (associatedEquivariantFiberMk hP σ p y rfl v) = σ.linearMap (θ p) y v := by
  let q := associatedGaugeProjection (Y := Y) θ hθ
  let Z := AssociatedBundle G P Y
  let L (p : P) (y : Y) : E y ≃ₗ[ℂ] ((q : Z → Y) *ᵖ E)
      (associatedBundleMk G P Y p y) :=
    LinearEquiv.ofBijective (σ.linearMap (θ p) y) (σ.linearMap_bijective (θ p) y)
  -- Continuity uses the original total-space action, jointly with the same principal gauge.
  have hc : Continuous (fun z : P × TotalSpace Unit E ↦
      (⟨associatedBundleMk G P Y z.1 z.2.proj, L z.1 z.2.proj z.2.snd⟩ :
        TotalSpace Unit ((q : Z → Y) *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E q).continuous_iff]
    exact (continuous_quot_mk.comp
      (continuous_fst.prodMk (continuous_proj.comp continuous_snd))).prodMk
      (σ.continuous_action.comp ((θ.continuous.comp continuous_fst).prodMk continuous_snd))
  -- The opposite principal action cancels the inverse action on the original vector.
  have hcov : letI := σ.toMulAction
      ∀ (p : P) (g : G) (w : TotalSpace Unit E),
        (⟨associatedBundleMk G P Y (MulOpposite.op g • p) (g⁻¹ • w.proj),
          L (MulOpposite.op g • p) (g⁻¹ • w.proj) (σ.linearMap g⁻¹ w.proj w.snd)⟩ :
            TotalSpace Unit ((q : Z → Y) *ᵖ E)) =
          ⟨associatedBundleMk G P Y p w.proj, L p w.proj w.snd⟩ := by
    let := σ.toMulAction
    intro p g w
    have hbase : associatedBundleMk G P Y (MulOpposite.op g • p) (g⁻¹ • w.proj) =
        associatedBundleMk G P Y p w.proj := by
      symm
      exact Quotient.sound ⟨g, rfl⟩
    have hvec : θ (MulOpposite.op g • p) • (g⁻¹ • w) = θ p • w := by
      rw [hθ, mul_smul, smul_inv_smul]
    apply TotalSpace.ext hbase
    exact (TotalSpace.ext_iff.mp hvec).2
  obtain ⟨a, ha⟩ := exists_associatedEquivariant_iso_of_covariant_equiv hP σ _ L hc hcov
  exact ⟨a, ha⟩

end AtiyahSinger
