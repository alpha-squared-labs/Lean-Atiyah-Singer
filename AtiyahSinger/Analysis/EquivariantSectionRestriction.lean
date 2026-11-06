/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSectionPullback
public import AtiyahSinger.Topology.EquivariantRestriction

/-!
# Smooth restriction of the original bundle and section actions

Public module ID: M0568.

Precomposition by a specified smooth continuous group homomorphism retains
the original bundle and its jointly smooth action. Its geometric section
action is the original action evaluated at the image group element, including
the inverse-base transports. These are the same actions used by group
restriction of the finite smooth kernel and quotient-cokernel representations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

variable {VG HG VH HH : Type*}
  [NormedAddCommGroup VG] [NormedSpace ℝ VG] [TopologicalSpace HG]
  [NormedAddCommGroup VH] [NormedSpace ℝ VH] [TopologicalSpace HH]
  (IG : ModelWithCorners ℝ VG HG) (IH : ModelWithCorners ℝ VH HH)
  {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace HH H]
  {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (φ : H →ₜ* G) (hφ : ContMDiff IH IG ∞ φ)

include hσ

/-- The original moving-fiber action remains jointly smooth under smooth group restriction. -/
theorem EquivariantStructure.restrict_isSmooth :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
    letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul IH 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
    (σ.restrict φ).IsSmooth (n := n) (r := r) IH := by
  let : MulAction H M := MulAction.compHom M φ.toMonoidHom
  let : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul IH 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
    MulAction.contMDiffSMul_compHom hφ
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  intro e f he hf j
  let := he
  let := hf
  -- The same frame coefficients are precomposed by φ times the identity on the base.
  exact (hσ e f j).comp
    ((hφ.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffOn (fun _ hp ↦ hp)

variable [IsManifold IG ∞ G] [IsManifold IH ∞ H]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

/-- Restriction evaluates the same original smooth section action at the image group element. -/
theorem EquivariantStructure.smoothSectionRepresentation_restrict :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
    letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul IH 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
    ∀ (h : H) (s : smoothSections (n := n) (r := r) E),
      (σ.restrict φ).smoothSectionRepresentation IH (σ.restrict_isSmooth IG IH hσ φ hφ) h s =
        σ.smoothSectionRepresentation IG hσ (φ h) s := by
  let : MulAction H M := MulAction.compHom M φ.toMonoidHom
  let : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul IH 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
    MulAction.contMDiffSMul_compHom hφ
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  intro h s
  apply Subtype.ext
  funext x
  apply TotalSpace.mk_injective x (F := Unit)
  -- Compare the original total vectors before eliminating the inverse-base transports.
  change (⟨x, (σ.restrict φ).sectionLinearMap h s.val x⟩ : TotalSpace Unit E) =
    ⟨x, σ.sectionLinearMap (φ h) s.val x⟩
  rw [EquivariantStructure.sectionLinearMap_totalSpace,
    EquivariantStructure.sectionLinearMap_totalSpace]
  change (⟨φ h • (φ h⁻¹ • x), σ.linearMap (φ h) (φ h⁻¹ • x) (s.val (φ h⁻¹ • x))⟩ :
      TotalSpace Unit E) =
    ⟨φ h • ((φ h)⁻¹ • x), σ.linearMap (φ h) ((φ h)⁻¹ • x) (s.val ((φ h)⁻¹ • x))⟩
  rw [map_inv]

end AtiyahSinger.ComplexBundle
