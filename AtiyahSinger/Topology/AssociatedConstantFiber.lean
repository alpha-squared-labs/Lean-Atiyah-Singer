/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedEquivariantDescent
public import AtiyahSinger.Topology.AssociatedVectorCoordinates
public import AtiyahSinger.Topology.BundlePullback
public import AtiyahSinger.Topology.EquivariantTrivialBundle

/-!
# Constant equivariant fibers and the original associated coefficient bundle

Public module ID: M1530.

Descent of the diagonal product bundle is the pullback of the original
associated representation bundle along the actual quotient projection.
The isomorphism retains every principal representative: [p,(y,v)] maps to
([p,y],[p,v]). This is the coefficient comparison used in vertical kernel
evaluation for operators on the sphere bundle.

Source: the associated coefficient construction in SG III.13.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] trivialTopology isFiniteRank_trivial
  associatedEquivariantFiberAddCommGroup associatedEquivariantFiberModule
  associatedEquivariantTotalTopology associatedVectorFiberAddCommGroup
  associatedVectorFiberModule associatedVectorTotalTopology isFiniteRank_pullback

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
/-- Diagonal constant-fiber descent is the pullback of the same associated representation. -/
theorem exists_associatedConstantFiber_iso (hP : IsPrincipalBundle G projection)
    (ρ : FiniteContinuousRepresentation G) :
    let σ := EquivariantStructure.ofFiniteRepresentation (X := Y) ρ
    let q := associatedBundleProjection (F := Y) hP
    ∃ e : Iso (AssociatedEquivariantFiber hP σ)
        ((q : AssociatedBundle G P Y → B) *ᵖ (AssociatedVectorFiber hP ρ.representation)),
      ∀ (p : P) (y : Y) (v : Fin ρ.dimension → ℂ),
        e.linearEquiv (associatedBundleMk G P Y p y)
            (associatedEquivariantFiberMk hP σ p y rfl v) =
          associatedVectorFiberMk hP ρ.representation p rfl v := by
  let σ := EquivariantStructure.ofFiniteRepresentation (X := Y) ρ
  let q := associatedBundleProjection (F := Y) hP
  let V := AssociatedVectorFiber hP ρ.representation
  let Z := AssociatedBundle G P Y
  let W := (q : Z → B) *ᵖ V
  let : IsFiniteRank V := isFiniteRank_associatedVector hP ρ.representation ρ.continuous_action
  let L (p : P) (_y : Y) : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ]
      W (associatedBundleMk G P Y p _y) :=
    associatedVectorFiberMkLinearEquiv hP ρ.representation p rfl
  let : MulAction G (Fin ρ.dimension → ℂ) := associatedRepresentationAction ρ.representation
  -- The original quotient maps are jointly continuous in the same p, y and v.
  have hc : Continuous (fun z : P × TotalSpace Unit (Trivial Y (Fin ρ.dimension → ℂ)) ↦
      (⟨associatedBundleMk G P Y z.1 z.2.proj, L z.1 z.2.proj z.2.snd⟩ :
        TotalSpace Unit W)) := by
    have hcoord : Continuous (fun z : TotalSpace Unit (Trivial Y (Fin ρ.dimension → ℂ)) ↦
        (z.proj, z.snd)) := continuous_induced_dom
    have hbase : Continuous (fun z : P × TotalSpace Unit (Trivial Y (Fin ρ.dimension → ℂ)) ↦
        associatedBundleMk G P Y z.1 z.2.proj) :=
      continuous_quot_mk.comp (continuous_fst.prodMk (hcoord.fst.comp continuous_snd))
    have hvec : Continuous (fun z : P × TotalSpace Unit (Trivial Y (Fin ρ.dimension → ℂ)) ↦
        associatedBundleMk G P (Fin ρ.dimension → ℂ) z.1 z.2.snd) :=
      continuous_quot_mk.comp (continuous_fst.prodMk (hcoord.snd.comp continuous_snd))
    rw [(inducing_pullbackTotalSpaceEmbedding Unit V q).continuous_iff]
    exact hbase.prodMk ((associatedVectorTotalHomeomorph hP ρ.representation).symm.continuous.comp
      hvec)
  have hinj : Function.Injective (fun w : TotalSpace Unit W ↦ (w.proj, w.snd.val)) := by
    rintro ⟨z, u, hu⟩ ⟨z', v, hv⟩ he
    have hz : z = z' := congrArg Prod.fst he
    subst z'
    have huv : u = v := congrArg Prod.snd he
    subst v
    rfl
  -- One group element changes both quotient coordinates and cancels in both factors.
  have hcov : letI := σ.toMulAction
      ∀ (p : P) (g : G) (w : TotalSpace Unit (Trivial Y (Fin ρ.dimension → ℂ))),
        (⟨associatedBundleMk G P Y (MulOpposite.op g • p) (g⁻¹ • w.proj),
          L (MulOpposite.op g • p) (g⁻¹ • w.proj) (σ.linearMap g⁻¹ w.proj w.snd)⟩ :
            TotalSpace Unit W) =
          ⟨associatedBundleMk G P Y p w.proj, L p w.proj w.snd⟩ := by
    intro p g w
    apply hinj
    apply Prod.ext
    · change associatedBundleMk G P Y (MulOpposite.op g • p) (g⁻¹ • w.proj) = _
      rw [associatedBundleMk_smul, smul_inv_smul]
    · change associatedBundleMk G P (Fin ρ.dimension → ℂ) (MulOpposite.op g • p)
        (g⁻¹ • w.snd) = associatedBundleMk G P (Fin ρ.dimension → ℂ) p w.snd
      rw [associatedBundleMk_smul, smul_inv_smul]
  exact exists_associatedEquivariant_iso_of_covariant_equiv hP σ W L hc hcov

end AtiyahSinger
