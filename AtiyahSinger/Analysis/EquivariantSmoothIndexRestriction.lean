/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationRestriction
public import AtiyahSinger.Analysis.EquivariantSectionRestriction
public import AtiyahSinger.Analysis.SmoothEquivariantIndex
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Group restriction of the actual smooth equivariant index

Public module ID: M0577.

Restriction preserves the specified section map and its actual kernel and
quotient cokernel. Restrict the same finite continuous coordinates and use
the geometric section-action identity to compute the full virtual class.
Neither compactness of the groups nor a choice of invariant measure is needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

variable {VG HG VH HH : Type*}
  [NormedAddCommGroup VG] [NormedSpace ℝ VG] [TopologicalSpace HG]
  [NormedAddCommGroup VH] [NormedSpace ℝ VH] [TopologicalSpace HH]
  (IG : ModelWithCorners ℝ VG HG) (IH : ModelWithCorners ℝ VH HH)
  {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace HH H]
  [LieGroup IG ∞ G] [LieGroup IH ∞ H]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    EquivariantStructure G E.Fiber)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure G F.Fiber)
  (hσE : σE.IsSmooth (n := n) (r := E.rank) IG)
  (hσF : σF.IsSmooth (n := n) (r := F.rank) IG)
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ] {l : ℝ}
  (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
    E.Fiber F.Fiber μ l)
  (hPg : P.IsEquivariant IG σE σF hσE hσF)
  (φ : H →ₜ* G) (hφ : ContMDiff IH IG ∞ φ)

include hPg

/-- The identical smooth section map is equivariant for the restricted geometric actions. -/
theorem PseudodifferentialOperator.isEquivariant_restrict :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
    letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul IH 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
    P.IsEquivariant IH (σE.restrict φ) (σF.restrict φ)
      (σE.restrict_isSmooth IG IH hσE φ hφ) (σF.restrict_isSmooth IG IH hσF φ hφ) := by
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let : MulAction H M := MulAction.compHom M φ.toMonoidHom
  let : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul IH 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
    MulAction.contMDiffSMul_compHom hφ
  intro h
  apply LinearMap.ext
  intro u
  change P.toLinearMap ((σE.restrict φ).smoothSectionRepresentation IH
      (σE.restrict_isSmooth IG IH hσE φ hφ) h u) =
    (σF.restrict φ).smoothSectionRepresentation IH
      (σF.restrict_isSmooth IG IH hσF φ hφ) h (P.toLinearMap u)
  rw [σE.smoothSectionRepresentation_restrict IG IH hσE φ hφ,
    σF.smoothSectionRepresentation_restrict IG IH hσF φ hφ]
  exact LinearMap.congr_fun (hPg (φ h)) u

/-- Restricting the original smooth kernel and quotient representations restricts their index. -/
theorem PseudodifferentialOperator.smoothEquivariantAnalyticIndex_restrict (hP : P.IsElliptic) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
    letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul IH 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
    representationRestriction φ (P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hP) =
      P.smoothEquivariantAnalyticIndex IH (σE.restrict φ) (σF.restrict φ)
        (σE.restrict_isSmooth IG IH hσE φ hφ) (σF.restrict_isSmooth IG IH hσF φ hφ)
        (P.isEquivariant_restrict IG IH E F σE σF hσE hσF hPg φ hφ) hP := by
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let : MulAction H M := MulAction.compHom M φ.toMonoidHom
  let : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul IH 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
    MulAction.contMDiffSMul_compHom hφ
  obtain ⟨ρ, τ, e, f, he, hf⟩ :=
    P.exists_smoothKernelCokernelRepresentations IG σE σF hσE hσF hPg hP
  -- Restrict the same finite coordinates; neither defect carrier nor section map changes.
  have heH (h : H) (v : Fin ρ.dimension → ℂ) :
      (e ((ρ.restrict φ).representation h v)).val =
        (σE.restrict φ).smoothSectionRepresentation IH
          (σE.restrict_isSmooth IG IH hσE φ hφ) h (e v).val := by
    rw [σE.smoothSectionRepresentation_restrict IG IH hσE φ hφ]
    exact he (φ h) v
  have hfH (h : H) (v : smoothSections (n := n) (r := F.rank) F.Fiber) :
      f ((τ.restrict φ).representation h (f.symm (P.toLinearMap.range.mkQ v))) =
        P.toLinearMap.range.mkQ ((σF.restrict φ).smoothSectionRepresentation IH
          (σF.restrict_isSmooth IG IH hσF φ hφ) h v) := by
    rw [σF.smoothSectionRepresentation_restrict IG IH hσF φ hφ]
    exact hf (φ h) v
  rw [P.smoothEquivariantAnalyticIndex_eq IG σE σF hσE hσF hPg hP ρ τ e f he hf,
    map_sub, representationRestriction_finiteClass, representationRestriction_finiteClass]
  exact (P.smoothEquivariantAnalyticIndex_eq IH (σE.restrict φ) (σF.restrict φ)
    (σE.restrict_isSmooth IG IH hσE φ hφ) (σF.restrict_isSmooth IG IH hσF φ hφ)
    (P.isEquivariant_restrict IG IH E F σE σF hσE hσF hPg φ hφ) hP
    (ρ.restrict φ) (τ.restrict φ) e f heH hfH).symm

end AtiyahSinger
