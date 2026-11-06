/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedEquivariantDescent
public import AtiyahSinger.Topology.EquivariantBottRepresentation
public import AtiyahSinger.Topology.ExteriorFamilyContinuity
public import AtiyahSinger.Topology.OrthogonalFrameComplexification

/-!
# Exterior descent in the original orthogonal frames

Public module ID: M1978.

The original real orthogonal frame extends to a complex linear isometry for
the canonical Hermitian form on the actual tensor complexification. Its
exterior maps identify the original descended Bott parity bundles with the
pullback of the original exterior parity bundles of the complexification.
Every representative formula uses that same complex frame.

The proof uses the existing continuous exterior-family construction and the
actual associated quotient descent. This is the standard frame description
of associated exterior powers (HU IV.5; SG Appendix C), including rank zero.
It is used for the normal exterior Thom comparison. The control and boundary
comparison of compact-support classes is a separate subsequent step.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct Matrix.Norms.Elementwise

variable {n r : ℕ} {B : Type*} [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V
    𝓘(ℝ, EuclideanSpace ℝ (Fin n))]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin r)) V]

local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "W" => EuclideanSpace ℂ (Fin r)
local notation "GO" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))


attribute [local instance] orthogonalFrameTopology associatedVectorFiberAddCommGroup
  associatedVectorFiberModule associatedVectorTotalTopology exteriorAlgebraNormedAddCommGroup
  exteriorAlgebraNormedSpace exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity
  associatedEquivariantFiberAddCommGroup associatedEquivariantFiberModule
  associatedEquivariantTotalTopology isFiniteRank_associatedEquivariant isFiniteRank_pullback

include n r V in
set_option maxSynthPendingDepth 40 in
set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Keep the original scalar-extension fibers and both descended parity topologies together.
/-- Orthogonal frame coordinates descend on the original exterior parity bundles. -/
theorem exists_orthogonalFrame_exterior_descent :
    letI := continuousSMul_orthogonalFrame r V I
    let hP := (smoothOrthogonalFrameAtlas r V I).toIsPrincipalBundle
    let C := fun b : B ↦ ℂ ⊗[ℝ] V b
    letI := complexificationTopology R V
    let Z := AssociatedBundle GO P W
    let base : C(Z, B) := associatedBundleProjection hP
    let Parity (i : ZMod 2) : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i
    letI (i : ZMod 2) := modelTopology (Parity i) (Trivial W (Parity i))
    letI (i : ZMod 2) := isFiniteRank_model (Parity i) (Trivial W (Parity i))
    let σ (i : ZMod 2) := exteriorParityEquivariantStructure (G := GO) (V := W) i
    ∃ L : ∀ p : P, W ≃ₗ[ℂ] C p.1,
      (∀ (p : P) (z : W), complexificationReIm (V p.1) (L p z) =
        (p.2 (WithLp.toLp 2 (fun j ↦ (z j).re)),
          p.2 (WithLp.toLp 2 (fun j ↦ (z j).im)))) ∧
      (∀ (p : P) (z w : W),
        (complexificationHermitianCore (V p.1)).inner (L p z) (L p w) = inner ℂ z w) ∧
      ∀ i : ZMod 2,
        ∃ u : Iso (AssociatedEquivariantFiber hP (σ i))
            ((base : Z → B) *ᵖ (fun b ↦
              CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (C b)) i)),
          ∀ (p : P) (z : W) (w : Parity i),
            (u.linearEquiv (associatedBundleMk GO P W p z)
              (associatedEquivariantFiberMk hP (σ i) p z rfl w)).val =
                ExteriorAlgebra.map (L p).toLinearMap w.val := by
  classical
  let := continuousSMul_orthogonalFrame r V I
  let hP := (smoothOrthogonalFrameAtlas r V I).toIsPrincipalBundle
  let ρ := orthogonalComplexificationFiniteRepresentation r
  let := complexificationTopology R V
  let := ComplexBundle.isFiniteRank_complexification R V
  let C := fun b : B ↦ ℂ ⊗[ℝ] V b
  let : MulAction GO (Fin r → ℂ) := associatedRepresentationAction ρ.representation
  let : ContinuousSMul GO (Fin r → ℂ) := ⟨ρ.continuous_action⟩
  let q := EuclideanSpace.equiv (Fin r) ℂ
  obtain ⟨a, ha⟩ := exists_orthogonalFrame_complexification_iso (n := n) (r := r) V
  let L (p : P) : W ≃ₗ[ℂ] C p.1 := q.toLinearEquiv.trans
    ((associatedVectorFiberMkLinearEquiv hP ρ.representation p rfl).trans (a.linearEquiv p.1))
  have hL (p : P) (z : W) : complexificationReIm (V p.1) (L p z) =
      (p.2 (WithLp.toLp 2 (fun i ↦ (z i).re)),
        p.2 (WithLp.toLp 2 (fun i ↦ (z i).im))) := ha p (q z)
  have hLc : Continuous (fun z : P × W ↦ (⟨z.1.1, L z.1 z.2⟩ : TotalSpace Unit C)) := by
    have hc : Continuous (fun z : P × W ↦
        associatedBundleMk GO P (Fin r → ℂ) z.1 (q z.2)) :=
      continuous_quot_mk.comp (continuous_fst.prodMk (q.continuous.comp continuous_snd))
    exact a.continuous_total.comp
      ((associatedVectorTotalHomeomorph hP ρ.representation).symm.continuous.comp hc)
  have hcov (p : P) (g : GO) (z : W) :
      L (MulOpposite.op g • p) z = L p (g • z : W) := by
    apply (complexificationReIm (V p.1)).injective
    have hleft := hL (MulOpposite.op g • p) z
    have hright := hL p (g • z)
    refine Eq.trans hleft (Eq.trans ?_ hright.symm)
    apply Prod.ext
    · apply congrArg p.2
      ext i
      change ∑ j, (g.val i j) * (z j).re =
        (∑ j, (g.val i j : ℂ) * z j).re
      simp
    · apply congrArg p.2
      ext i
      change ∑ j, (g.val i j) * (z j).im =
        (∑ j, (g.val i j : ℂ) * z j).im
      simp
  have hmetric (p : P) (z w : W) :
      (complexificationHermitianCore (V p.1)).inner (L p z) (L p w) = inner ℂ z w := by
    change ((inner ℝ (complexificationReIm (V p.1) (L p z)).1
          (complexificationReIm (V p.1) (L p w)).1 +
        inner ℝ (complexificationReIm (V p.1) (L p z)).2
          (complexificationReIm (V p.1) (L p w)).2 : ℝ) : ℂ) +
      ((inner ℝ (complexificationReIm (V p.1) (L p z)).1
          (complexificationReIm (V p.1) (L p w)).2 -
        inner ℝ (complexificationReIm (V p.1) (L p z)).2
          (complexificationReIm (V p.1) (L p w)).1 : ℝ) : ℂ) * Complex.I = _
    rw [hL, hL]
    simp only [p.2.inner_map_map, PiLp.inner_apply, RCLike.inner_apply']
    change (((∑ i, (z i).re * (w i).re) + ∑ i, (z i).im * (w i).im : ℝ) : ℂ) +
      (((∑ i, (z i).re * (w i).im) - ∑ i, (z i).im * (w i).re : ℝ) : ℂ) * Complex.I =
        ∑ i, star (z i) * w i
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Complex.ofReal_sum,
      Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Complex.ext <;> simp [sub_eq_add_neg]
  let Z := AssociatedBundle GO P W
  let pr : C(P, B) := ⟨orthogonalFrameProjection r V, hP.projection_properties.1⟩
  let base : C(Z, B) := associatedBundleProjection hP
  let Parity (i : ZMod 2) : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i
  let H (i : ZMod 2) : B → Type _ :=
    fun b : B ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (C b)) i
  let F (i : ZMod 2) := (base : Z → B) *ᵖ (H i)
  let (i : ZMod 2) : TopologicalSpace (TotalSpace Unit (Trivial W (Parity i))) :=
    modelTopology (Parity i) (Trivial W (Parity i))
  let (i : ZMod 2) : IsFiniteRank (Trivial W (Parity i)) :=
    isFiniteRank_model (Parity i) (Trivial W (Parity i))
  let σ (i : ZMod 2) := exteriorParityEquivariantStructure (G := GO) (V := W) i
  have hd (i : ZMod 2) :
      letI := modelTopology (Parity i) (Trivial P (Parity i))
      ∃ d : Iso (Trivial P (Parity i)) ((pr : P → B) *ᵖ (H i)),
        ∀ (p : P) (w : Parity i),
          (d.linearEquiv p w).val = ExteriorAlgebra.map (L p).toLinearMap w.val :=
    exists_exteriorParity_family_iso pr (fun p ↦ (L p).toLinearMap)
      (fun p ↦ (L p).bijective) hLc i
  have hdesc (i : ZMod 2) :
      ∃ u : Iso (AssociatedEquivariantFiber hP (σ i)) (F i),
        ∀ (p : P) (z : W) (w : Parity i),
          (u.linearEquiv (associatedBundleMk GO P W p z)
            (associatedEquivariantFiberMk hP (σ i) p z rfl w)).val =
              ExteriorAlgebra.map (L p).toLinearMap w.val := by
    let := modelTopology (Parity i) (Trivial P (Parity i))
    obtain ⟨d, hd⟩ := hd i
    let J (p : P) (_z : W) : Parity i ≃ₗ[ℂ] F i (associatedBundleMk GO P W p _z) :=
      d.linearEquiv p
    have hc : Continuous (fun z : P × TotalSpace Unit (Trivial W (Parity i)) ↦
        (⟨associatedBundleMk GO P W z.1 z.2.proj, J z.1 z.2.proj z.2.snd⟩ :
          TotalSpace Unit (F i))) := by
      let eW := (unitTotalHomeomorph (Parity i) (Trivial W (Parity i))).trans
        (Trivial.homeomorphProd W (Parity i))
      let eP := (unitTotalHomeomorph (Parity i) (Trivial P (Parity i))).trans
        (Trivial.homeomorphProd P (Parity i))
      have hb : Continuous (fun z : P × TotalSpace Unit (Trivial W (Parity i)) ↦
          associatedBundleMk GO P W z.1 z.2.proj) :=
        continuous_quot_mk.comp (continuous_fst.prodMk (eW.continuous.fst.comp continuous_snd))
      have hv := eP.symm.continuous.comp
        (continuous_fst.prodMk (eW.continuous.snd.comp continuous_snd))
      apply (inducing_pullbackTotalSpaceEmbedding Unit (H i) base).continuous_iff.mpr
      exact hb.prodMk ((Pullback.continuous_lift Unit (H i) pr).comp
        (d.continuous_total.comp hv))
    have hJcov : letI := (σ i).toMulAction
        ∀ (p : P) (g : GO) (w : TotalSpace Unit (Trivial W (Parity i))),
          (⟨associatedBundleMk GO P W (MulOpposite.op g • p) (g⁻¹ • w.proj),
            J (MulOpposite.op g • p) (g⁻¹ • w.proj) ((σ i).linearMap g⁻¹ w.proj w.snd)⟩ :
              TotalSpace Unit (F i)) =
            ⟨associatedBundleMk GO P W p w.proj, J p w.proj w.snd⟩ := by
      intro p g w
      apply TotalSpace.ext
      · exact (associatedBundleMk_smul p g (g⁻¹ • w.proj)).trans
          (congrArg (associatedBundleMk GO P W p) (smul_inv_smul g w.proj))
      · apply heq_of_eq
        apply Subtype.ext
        change (d.linearEquiv (MulOpposite.op g • p)
          (exteriorParityAction g⁻¹ i w.snd)).val = (d.linearEquiv p w.snd).val
        rw [hd, hd]
        have heq : (ExteriorAlgebra.map (L (MulOpposite.op g • p)).toLinearMap).comp
            (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ W g⁻¹)) =
              ExteriorAlgebra.map (L p).toLinearMap := by
          apply ExteriorAlgebra.hom_ext
          ext v
          change ExteriorAlgebra.map (L (MulOpposite.op g • p)).toLinearMap
            (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ W g⁻¹)
              (ExteriorAlgebra.ι ℂ v)) =
            ExteriorAlgebra.map (L p).toLinearMap (ExteriorAlgebra.ι ℂ v)
          rw [ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι,
            ExteriorAlgebra.map_apply_ι]
          exact congrArg (ExteriorAlgebra.ι ℂ)
            ((hcov p g (g⁻¹ • v)).trans (congrArg (L p) (smul_inv_smul g v)))
        exact AlgHom.congr_fun heq w.snd.val
    obtain ⟨u, hu⟩ := exists_associatedEquivariant_iso_of_covariant_equiv hP (σ i) (F i)
      J hc hJcov
    refine ⟨u, ?_⟩
    intro p z w
    rw [hu]
    exact hd p w
  exact ⟨L, hL, hmetric, hdesc⟩

end AtiyahSinger
