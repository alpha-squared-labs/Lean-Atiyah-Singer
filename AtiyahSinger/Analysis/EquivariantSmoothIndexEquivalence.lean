/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothEquivariantIndex
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Full smooth-index invariance under an actual section equivalence

Public module ID: M0573.

An equivariant commuting square of the specified smooth section maps identifies
their actual kernels and algebraic quotient cokernels. Transporting the same
finite continuous coordinates through these equivalences preserves the full
virtual representation. No invariant density, Hilbert norm or dimension-map
argument is needed. This is the coordinate comparison used in clopen assembly.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G]
  {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [CompactSpace N] [T2Space N] [SecondCountableTopology N]
  [MeasurableSpace N] [BorelSpace N]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (A B : SmoothFiniteComplexBundle (n := m) N)
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    EquivariantStructure G E.Fiber)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure G F.Fiber)
  (τA : letI := modelTopology (EuclideanSpace ℂ (Fin A.rank)) A.Fiber
    EquivariantStructure G A.Fiber)
  (τB : letI := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
    EquivariantStructure G B.Fiber)
  (hσE : σE.IsSmooth (n := n) (r := E.rank) IG)
  (hσF : σF.IsSmooth (n := n) (r := F.rank) IG)
  (hτA : τA.IsSmooth (n := m) (r := A.rank) IG)
  (hτB : τB.IsSmooth (n := m) (r := B.rank) IG)

/-- A specified equivariant section-operator square preserves the full smooth index. -/
theorem PseudodifferentialOperator.smoothEquivariantAnalyticIndex_eq_of_sectionEquiv
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := m) ν] {l l' : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ l)
    (Q : PseudodifferentialOperator (n := m) (r := A.rank) (q := B.rank)
      A.Fiber B.Fiber ν l')
    (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic)
    (hQg : Q.IsEquivariant IG τA τB hτA hτB) (hQ : Q.IsElliptic)
    (e : smoothSections (n := n) (r := E.rank) E.Fiber ≃ₗ[ℂ]
      smoothSections (n := m) (r := A.rank) A.Fiber)
    (f : smoothSections (n := n) (r := F.rank) F.Fiber ≃ₗ[ℂ]
      smoothSections (n := m) (r := B.rank) B.Fiber)
    (he : ∀ g u, e (σE.smoothSectionRepresentation IG hσE g u) =
      τA.smoothSectionRepresentation IG hτA g (e u))
    (hf : ∀ g v, f (σF.smoothSectionRepresentation IG hσF g v) =
      τB.smoothSectionRepresentation IG hτB g (f v))
    (hinter : ∀ u, Q.toLinearMap (e u) = f (P.toLinearMap u)) :
    P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hP =
      Q.smoothEquivariantAnalyticIndex IG τA τB hτA hτB hQg hQ := by
  -- Restrict the given source equivalence to the actual kernels.
  let K : P.toLinearMap.ker ≃ₗ[ℂ] Q.toLinearMap.ker := {
    toFun u := ⟨e u.val, by rw [LinearMap.mem_ker, hinter, u.property, map_zero]⟩
    invFun u := ⟨e.symm u.val, by
      apply f.injective
      rw [map_zero, ← hinter, e.apply_symm_apply]
      exact u.property⟩
    left_inv u := Subtype.ext (e.symm_apply_apply u.val)
    right_inv u := Subtype.ext (e.apply_symm_apply u.val)
    map_add' u v := Subtype.ext (e.map_add u.val v.val)
    map_smul' c u := Subtype.ext (e.map_smul c u.val) }
  have hrange : P.toLinearMap.range.map f.toLinearMap = Q.toLinearMap.range := by
    ext v
    constructor
    · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨e u, hinter u⟩
    · rintro ⟨u, rfl⟩
      exact ⟨P.toLinearMap (e.symm u), ⟨e.symm u, rfl⟩,
        (hinter (e.symm u)).symm.trans (congrArg Q.toLinearMap (e.apply_symm_apply u))⟩
  -- The target equivalence descends to the genuine quotient by the original range.
  let C := Submodule.Quotient.equiv P.toLinearMap.range Q.toLinearMap.range f hrange
  have hC (v : smoothSections (n := n) (r := F.rank) F.Fiber) :
      C (P.toLinearMap.range.mkQ v) = Q.toLinearMap.range.mkQ (f v) := rfl
  obtain ⟨ρ, τ, a, b, ha, hb⟩ :=
    P.exists_smoothKernelCokernelRepresentations IG σE σF hσE hσF hPg hP
  have hkernel (g : G) (v : Fin ρ.dimension → ℂ) :
      ((a.trans K) (ρ.representation g v)).val =
        τA.smoothSectionRepresentation IG hτA g ((a.trans K) v).val := by
    change e (a (ρ.representation g v)).val =
      τA.smoothSectionRepresentation IG hτA g (e (a v).val)
    rw [ha, he]
  have hcoker (g : G) (v : smoothSections (n := m) (r := B.rank) B.Fiber) :
      (b.trans C) (τ.representation g ((b.trans C).symm (Q.toLinearMap.range.mkQ v))) =
        Q.toLinearMap.range.mkQ (τB.smoothSectionRepresentation IG hτB g v) := by
    have hpre : C (P.toLinearMap.range.mkQ (f.symm v)) = Q.toLinearMap.range.mkQ v := by
      rw [hC, f.apply_symm_apply]
    change C (b (τ.representation g (b.symm (C.symm (Q.toLinearMap.range.mkQ v))))) = _
    rw [← hpre, C.symm_apply_apply, hb, hC, hf, f.apply_symm_apply]
  -- Both indices now use precisely the same finite continuous representations.
  rw [P.smoothEquivariantAnalyticIndex_eq IG σE σF hσE hσF hPg hP ρ τ a b ha hb]
  exact (Q.smoothEquivariantAnalyticIndex_eq IG τA τB hτA hτB hQg hQ
    ρ τ (a.trans K) (b.trans C) hkernel hcoker).symm

end AtiyahSinger
