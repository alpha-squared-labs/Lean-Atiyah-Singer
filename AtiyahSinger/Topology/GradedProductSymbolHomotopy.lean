/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.GradedProductCutoff
public import AtiyahSinger.Topology.ModelBundleTopology
public import AtiyahSinger.Topology.SupportTripleExternalProduct
public import AtiyahSinger.Topology.SupportTripleTransport
public import AtiyahSinger.Topology.TrivialSupportProduct

/-!
# The actual graded cutoff homotopy and its compact-support class

Public module ID: M1873.

continuous finite-dimensional symbols on two compact parameter spaces
are invertible beyond a common frequency radius. Their actual graded matrix built from the
symbols and their adjoints and the SG cutoff matrix are connected by the specified affine weights.
The compact control is the product of the two closed frequency balls over the
compact bases. Outside it the larger frequency is beyond the common radius;
its weight stays one for the whole homotopy when `0 < epsilon <= 1`.

The four vector spaces may have different dimensions. The same adjoints and
ordered tensor factors occur in every boundary map. These are the local bundle
models for the symbol part of SG III.13.5, pp.249--250. The compact parameter
spaces are closed coordinate windows, not an assertion that a spatially compact
local symbol is globally elliptic on the entire Euclidean base. The preceding
local Sobolev norm estimate retains its own compact spatial cutoff hypotheses.

The comparison with the original compact-support external product uses its
actual reciprocal-cutoff model, with enlarged controls and a positive homotopy
from adjoints to inverses. This avoids imposing scalar-square identities on
general elliptic symbols. No index theorem or target K-class equality is an
input. Global nontrivial-bundle assembly and analytic domain comparison require
separate arguments for their respective objects. The geometric supported homotopy is proved
below, including its final compact-support product-class comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct unitInterval

/-- The matrix family of an actual map between the prescribed trivial bundles. -/
private def matrixOfTrivialHom {Z A B : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B] :
    letI := modelTopology A (Trivial Z A)
    letI := modelTopology B (Trivial Z B)
    Hom (Trivial Z A) (Trivial Z B) → C(Z, A →L[ℂ] B) := by
  let := modelTopology A (Trivial Z A)
  let := modelTopology B (Trivial Z B)
  intro f
  refine ⟨fun z ↦ (f.linearMap z).toContinuousLinearMap, ?_⟩
  apply continuous_clm_apply.mpr
  intro v
  let ea := (unitTotalHomeomorph A (Trivial Z A)).trans (Trivial.homeomorphProd Z A)
  let eb := (unitTotalHomeomorph B (Trivial Z B)).trans (Trivial.homeomorphProd Z B)
  exact eb.continuous.snd.comp (f.continuous_total.comp
    (ea.symm.continuous.comp (continuous_id.prodMk continuous_const)))

/-- Four continuous finite matrix families give the original continuous reciprocal tensor block. -/
private theorem continuous_reciprocalTensorSymbol
    {Z E₀ E₁ F₀ F₁ : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [FiniteDimensional ℂ F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [FiniteDimensional ℂ F₁]
    (d : C(Z, E₀ →L[ℂ] E₁)) (d' : C(Z, E₁ →L[ℂ] E₀))
    (e : C(Z, F₀ →L[ℂ] F₁)) (e' : C(Z, F₁ →L[ℂ] F₀)) :
    Continuous (fun z ↦ (reciprocalTensorSymbol (d z).toLinearMap (d' z).toLinearMap
      (e z).toLinearMap (e' z).toLinearMap).toContinuousLinearMap) := by
  -- Tensor operations are linear on the finite-dimensional operator spaces.
  let D₀ : (E₀ →L[ℂ] E₁) →ₗ[ℂ] ((E₀ ⊗[ℂ] F₀) →L[ℂ] (E₁ ⊗[ℂ] F₀)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((LinearMap.rTensorHom F₀).comp (ContinuousLinearMap.coeLM ℂ))
  let D₁ : (E₁ →L[ℂ] E₀) →ₗ[ℂ] ((E₁ ⊗[ℂ] F₁) →L[ℂ] (E₀ ⊗[ℂ] F₁)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((LinearMap.rTensorHom F₁).comp (ContinuousLinearMap.coeLM ℂ))
  let E₀' : (F₀ →L[ℂ] F₁) →ₗ[ℂ] ((E₀ ⊗[ℂ] F₀) →L[ℂ] (E₀ ⊗[ℂ] F₁)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((LinearMap.lTensorHom E₀).comp (ContinuousLinearMap.coeLM ℂ))
  let E₁' : (F₁ →L[ℂ] F₀) →ₗ[ℂ] ((E₁ ⊗[ℂ] F₁) →L[ℂ] (E₁ ⊗[ℂ] F₀)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((LinearMap.lTensorHom E₁).comp (ContinuousLinearMap.coeLM ℂ))
  apply continuous_clm_apply.mpr
  intro w
  have hfirst := ((D₀.continuous_of_finiteDimensional.comp d.continuous).clm_apply
    (continuous_const (y := w.1))).sub
      ((E₁'.continuous_of_finiteDimensional.comp e'.continuous).clm_apply
        (continuous_const (y := w.2)))
  have hsecond := ((E₀'.continuous_of_finiteDimensional.comp e.continuous).clm_apply
    (continuous_const (y := w.1))).add
      ((D₁.continuous_of_finiteDimensional.comp d'.continuous).clm_apply
        (continuous_const (y := w.2)))
  exact hfirst.prodMk hsecond

/-- The two weighted adjoint pairs form a continuous family in the finite matrix topology. -/
private theorem continuous_weightedGradedTensorSymbol
    {Z E₀ E₁ F₀ F₁ : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [FiniteDimensional ℂ F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [FiniteDimensional ℂ F₁]
    (d : C(Z, E₀ →L[ℂ] E₁)) (e : C(Z, F₀ →L[ℂ] F₁)) (α β : C(Z, ℝ)) :
    Continuous (fun z ↦ (weightedGradedTensorSymbol (d z).toLinearMap
      (e z).toLinearMap (α z) (β z)).toContinuousLinearMap) := by
  have := FiniteDimensional.complete ℂ E₀
  have := FiniteDimensional.complete ℂ E₁
  have := FiniteDimensional.complete ℂ F₀
  have := FiniteDimensional.complete ℂ F₁
  exact continuous_reciprocalTensorSymbol
    ⟨fun z ↦ (α z : ℂ) • d z, (Complex.continuous_ofReal.comp α.continuous).smul d.continuous⟩
    ⟨fun z ↦ (α z : ℂ) • ContinuousLinearMap.adjoint (d z),
      (Complex.continuous_ofReal.comp α.continuous).smul
        (ContinuousLinearMap.adjoint.continuous.comp d.continuous)⟩
    ⟨fun z ↦ (β z : ℂ) • e z, (Complex.continuous_ofReal.comp β.continuous).smul e.continuous⟩
    ⟨fun z ↦ (β z : ℂ) • ContinuousLinearMap.adjoint (e z),
      (Complex.continuous_ofReal.comp β.continuous).smul
        (ContinuousLinearMap.adjoint.continuous.comp e.continuous)⟩

/-- Interpolating the two reverse blocks is continuous in the original finite matrix space. -/
private theorem continuous_reciprocalTensorSymbol_adjoint_homotopy
    {Z E₀ E₁ F₀ F₁ : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [FiniteDimensional ℂ F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [FiniteDimensional ℂ F₁]
    (d : C(Z, E₀ →L[ℂ] E₁)) (di : C(Z, E₁ →L[ℂ] E₀))
    (e : C(Z, F₀ →L[ℂ] F₁)) (ei : C(Z, F₁ →L[ℂ] F₀)) (t : C(Z, ℝ)) :
    Continuous (fun z ↦ (reciprocalTensorSymbol (d z).toLinearMap
      (((1 - t z : ℝ) : ℂ) • (d z).toLinearMap.adjoint + (t z : ℂ) • (di z).toLinearMap)
      (e z).toLinearMap
      (((1 - t z : ℝ) : ℂ) • (e z).toLinearMap.adjoint +
        (t z : ℂ) • (ei z).toLinearMap)).toContinuousLinearMap) := by
  have := FiniteDimensional.complete ℂ E₀
  have := FiniteDimensional.complete ℂ E₁
  have := FiniteDimensional.complete ℂ F₀
  have := FiniteDimensional.complete ℂ F₁
  have ht := Complex.continuous_ofReal.comp t.continuous
  simpa only [ContinuousMap.coe_mk, Complex.ofReal_sub, Complex.ofReal_one,
    ContinuousLinearMap.adjoint_toLinearMap, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul] using continuous_reciprocalTensorSymbol d
    ⟨fun z ↦ (1 - (t z : ℂ)) • ContinuousLinearMap.adjoint (d z) + (t z : ℂ) • di z,
      ((continuous_const.sub ht).smul
        (ContinuousLinearMap.adjoint.continuous.comp d.continuous)).add (ht.smul di.continuous)⟩
    e ⟨fun z ↦ (1 - (t z : ℂ)) • ContinuousLinearMap.adjoint (e z) + (t z : ℂ) • ei z,
      ((continuous_const.sub ht).smul
        (ContinuousLinearMap.adjoint.continuous.comp e.continuous)).add (ht.smul ei.continuous)⟩

end AtiyahSinger


namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct unitInterval

set_option maxSynthPendingDepth 30

variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
  {E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [FiniteDimensional ℂ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [FiniteDimensional ℂ F₁]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "W" => EuclideanSpace ℝ (Fin m)
local notation "Base" => (X × V) × (Y × W)
local notation "Even" => (E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)
local notation "Odd" => (E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁)

section Factor

variable (a : C(X × (EuclideanSpace ℝ (Fin n)), E₀ →L[ℂ] E₁)) (R : ℝ)
  (ha : ∀ (x : X) (ξ : (EuclideanSpace ℝ (Fin n))), R < ‖ξ‖ → Function.Bijective (a (x, ξ)))

local notation "K" => Set.prod (Set.univ : Set X) (Metric.closedBall (0 : V) R)

set_option linter.unusedSectionVars false in
/-- An eventual symbol isomorphism has continuous original and inverse boundary actions. -/
theorem euclideanSymbol_boundary_continuity :
    letI := modelTopology E₀ (Bundle.Trivial (X × V) E₀)
    letI := modelTopology E₁ (Bundle.Trivial (X × V) E₁)
    Continuous (fun z : TotalSpace Unit (Restrict (Bundle.Trivial (X × V) E₀) Kᶜ) ↦
      (⟨z.proj, a z.proj.val z.snd⟩ :
        TotalSpace Unit (Restrict (Bundle.Trivial (X × V) E₁) Kᶜ))) ∧
    Continuous (fun z : TotalSpace Unit (Restrict (Bundle.Trivial (X × V) E₁) Kᶜ) ↦
      (⟨z.proj, (LinearEquiv.ofBijective (a z.proj.val).toLinearMap
        (ha z.proj.val.1 z.proj.val.2 (by
          apply lt_of_not_ge
          intro h
          exact z.proj.property ⟨Set.mem_univ _, by
            simpa only [Metric.mem_closedBall, dist_zero_right] using h⟩))).symm z.snd⟩ :
        TotalSpace Unit (Restrict (Bundle.Trivial (X × V) E₀) Kᶜ))) := by
  /- The original continuous operator family gives the forward action in
  the product topology. On the stated exterior, ha makes this very map
  bijective. In finite coordinates matrix inversion is continuous on the
  open invertible locus, giving the inverse action. Retyping the phantom
  model and restricting the base preserve every point and vector. Empty
  bases or an empty frequency exterior do not require equal fiber ranks. -/
  let := modelTopology E₀ (Bundle.Trivial (X × V) E₀)
  let := modelTopology E₁ (Bundle.Trivial (X × V) E₁)
  let := isFiniteRank_model E₀ (Bundle.Trivial (X × V) E₀)
  let := isFiniteRank_model E₁ (Bundle.Trivial (X × V) E₁)
  let := isFiniteRank_restrict (E := Bundle.Trivial (X × V) E₀) Kᶜ
  let := isFiniteRank_restrict (E := Bundle.Trivial (X × V) E₁) Kᶜ
  -- Identify each original trivial total space with its base times its fiber.
  let e₀ := (unitTotalHomeomorph E₀ (Bundle.Trivial (X × V) E₀)).trans
    (Bundle.Trivial.homeomorphProd (X × V) E₀)
  let e₁ := (unitTotalHomeomorph E₁ (Bundle.Trivial (X × V) E₁)).trans
    (Bundle.Trivial.homeomorphProd (X × V) E₁)
  let f : Hom (Bundle.Trivial (X × V) E₀) (Bundle.Trivial (X × V) E₁) :=
    { linearMap := fun x ↦ (a x).toLinearMap
      continuous_total := e₁.symm.continuous.comp
        ((e₀.continuous.fst).prodMk
          ((a.continuous.comp e₀.continuous.fst).clm_apply e₀.continuous.snd)) }
  -- Restrict this very map, and invert it using finite-rank bundle inversion.
  let g := f.restrict Kᶜ
  have hg (x : (Kᶜ : Set (X × V))) : Function.Bijective (g.linearMap x) := by
    apply ha x.val.1 x.val.2
    apply lt_of_not_ge
    intro h
    exact x.property ⟨Set.mem_univ _, by
      simpa only [Metric.mem_closedBall, dist_zero_right] using h⟩
  exact ⟨g.continuous_total, g.continuous_inverse hg⟩

/-- The actual eventual symbol, on its original trivial bundles and closed-ball control. -/
def euclideanSymbolTriple :
    letI := modelTopology E₀ (Bundle.Trivial (X × V) E₀)
    letI := modelTopology E₁ (Bundle.Trivial (X × V) E₁)
    CompactSupportTriple (Bundle.Trivial (X × V) E₀) (Bundle.Trivial (X × V) E₁) :=
  letI := modelTopology E₀ (Bundle.Trivial (X × V) E₀)
  letI := modelTopology E₁ (Bundle.Trivial (X × V) E₁)
  { control := K
    isCompact_control := isCompact_univ.prod (isCompact_closedBall (0 : V) R)
    boundary :=
      { linearEquiv := fun z ↦ LinearEquiv.ofBijective (a z.val).toLinearMap
          (ha z.val.1 z.val.2 (by
            apply lt_of_not_ge
            intro h
            exact z.property ⟨Set.mem_univ _, by
              simpa only [Metric.mem_closedBall, dist_zero_right] using h⟩))
        continuous_total := (euclideanSymbol_boundary_continuity a R ha).1
        continuous_symm := (euclideanSymbol_boundary_continuity a R ha).2 } }

end Factor

variable (a : C(X × EuclideanSpace ℝ (Fin n), E₀ →L[ℂ] E₁))
  (b : C(Y × EuclideanSpace ℝ (Fin m), F₀ →L[ℂ] F₁))

/-- The genuine uncut-to-cut graded matrix on the original four tensor factors. -/
def gradedProductCutoffSymbol (ε : ℝ) (t : unitInterval) (z : Base) : Even →ₗ[ℂ] Odd :=
  weightedGradedTensorSymbol (a z.1).toLinearMap (b z.2).toLinearMap
    (productCutoffHomotopyWeight ε t ‖z.1.2‖ ‖z.2.2‖)
    (productCutoffHomotopyWeight ε t ‖z.2.2‖ ‖z.1.2‖)

variable (R : ℝ) (hR : 0 ≤ R)
  (ha : ∀ (x : X) (ξ : (EuclideanSpace ℝ (Fin n))), R < ‖ξ‖ → Function.Bijective (a (x, ξ)))
  (hb : ∀ (y : Y) (η : (EuclideanSpace ℝ (Fin m))), R < ‖η‖ → Function.Bijective (b (y, η)))
  (ε : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1)

local notation "K" =>
  Set.prod (Set.prod (Set.univ : Set X) (Metric.closedBall (0 : V) R))
    (Set.prod (Set.univ : Set Y) (Metric.closedBall (0 : W) R))

include hR ha hb hε hε₁ in
set_option linter.unusedSectionVars false in
/-- One fixed compact exterior supports invertibility at every time of this exact homotopy. -/
theorem gradedProductCutoffSymbol_bijective (t : unitInterval) (z : (Kᶜ : Set Base)) :
    Function.Bijective (gradedProductCutoffSymbol a b ε t z.val) := by
  /- Stage 1: being outside the product control means at least one frequency
  exceeds R. The larger frequency therefore exceeds the same R, even when
  the two factors originally had different ellipticity thresholds and R
  was chosen as their maximum. Its corresponding original symbol is bijective.
  Stage 2: for 0<epsilon<=1, productCutoffHomotopyWeight_properties says
  that the weight of this larger frequency is exactly one for every t.
  Apply weightedGradedTensorSymbol_bijective to that factor. Its proof uses
  both positive adjoint squares, so no common-rank or scalar-square premise
  is needed for the other factor. This one control works for the whole I. -/
  -- Outside the fixed product control, the larger frequency exceeds the common radius.
  have hlarge : R < ‖z.val.1.2‖ ∨ R < ‖z.val.2.2‖ := by
    by_contra! h
    exact z.property ⟨⟨Set.mem_univ _, by
      simpa only [Metric.mem_closedBall, dist_zero_right] using h.1⟩,
      ⟨Set.mem_univ _, by
        simpa only [Metric.mem_closedBall, dist_zero_right] using h.2⟩⟩
  apply weightedGradedTensorSymbol_bijective
  -- Its exact affine weight remains one throughout the interval.
  by_cases h : ‖z.val.2.2‖ ≤ ‖z.val.1.2‖
  · left
    refine ⟨?_, ha _ _ (hlarge.elim id (fun hb ↦ hb.trans_le h))⟩
    rw [(productCutoffHomotopyWeight_properties ε hε hε₁).2.2.1 t _ _
      (norm_nonneg _) (norm_nonneg _) h]
    exact one_ne_zero
  · right
    have h' : ‖z.val.1.2‖ ≤ ‖z.val.2.2‖ := (lt_of_not_ge h).le
    refine ⟨?_, hb _ _ (hlarge.elim (fun ha ↦ ha.trans_le h') id)⟩
    rw [(productCutoffHomotopyWeight_properties ε hε hε₁).2.2.1 t _ _
      (norm_nonneg _) (norm_nonneg _) h']
    exact one_ne_zero

/-- The original graded boundary and its actual inverse vary continuously on the full cylinder. -/
theorem gradedProductCutoffSymbol_boundary_continuity :
    letI := modelTopology Even (Bundle.Trivial Base Even)
    letI := modelTopology Odd (Bundle.Trivial Base Odd)
    Continuous (fun z : unitInterval × TotalSpace Unit (Restrict (Bundle.Trivial Base Even) Kᶜ) ↦
      (⟨z.2.proj, gradedProductCutoffSymbol a b ε z.1 z.2.proj.val z.2.snd⟩ :
        TotalSpace Unit (Restrict (Bundle.Trivial Base Odd) Kᶜ))) ∧
    Continuous (fun z : unitInterval × TotalSpace Unit (Restrict (Bundle.Trivial Base Odd) Kᶜ) ↦
      (⟨z.2.proj, (LinearEquiv.ofBijective
        (gradedProductCutoffSymbol a b ε z.1 z.2.proj.val)
        (gradedProductCutoffSymbol_bijective a b R hR ha hb ε hε hε₁ z.1 z.2.proj)).symm
          z.2.snd⟩ : TotalSpace Unit (Restrict (Bundle.Trivial Base Even) Kᶜ))) := by
  /- Stage 1: the original operator families, their finite-dimensional
  Hermitian adjoints, tensor operations and real scalar weights are continuous.
  The joint weight certificate includes the axis extension of the actual SG
  formula. Thus the displayed matrix acts continuously in (t,z,vector).
  Stage 2: the preceding theorem gives invertibility on this same full
  cylinder. In local finite coordinates inversion on the general linear
  group is continuous. Its inverse is the inverse of the specified matrix,
  rather than a separate chosen symbol. Product/trivial bundle topologies
  and restriction preserve these exact maps. No compactness of the cylinder's
  frequency exterior, or uniform bound on the inverse there, is assumed. -/
  let := modelTopology Even (Bundle.Trivial Base Even)
  let := modelTopology Odd (Bundle.Trivial Base Odd)
  have := FiniteDimensional.complete ℂ E₀
  have := FiniteDimensional.complete ℂ E₁
  have := FiniteDimensional.complete ℂ F₀
  have := FiniteDimensional.complete ℂ F₁
  -- Tensoring is a linear operation on the finite-dimensional operator spaces.
  let d₀ : (E₀ →L[ℂ] E₁) →ₗ[ℂ] ((E₀ ⊗[ℂ] F₀) →L[ℂ] (E₁ ⊗[ℂ] F₀)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((LinearMap.rTensorHom F₀).comp (ContinuousLinearMap.coeLM ℂ))
  let d₁ : (E₁ →L[ℂ] E₀) →ₗ[ℂ] ((E₁ ⊗[ℂ] F₁) →L[ℂ] (E₀ ⊗[ℂ] F₁)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((LinearMap.rTensorHom F₁).comp (ContinuousLinearMap.coeLM ℂ))
  let e₀ : (F₀ →L[ℂ] F₁) →ₗ[ℂ] ((E₀ ⊗[ℂ] F₀) →L[ℂ] (E₀ ⊗[ℂ] F₁)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((LinearMap.lTensorHom E₀).comp (ContinuousLinearMap.coeLM ℂ))
  let e₁ : (F₁ →L[ℂ] F₀) →ₗ[ℂ] ((E₁ ⊗[ℂ] F₁) →L[ℂ] (E₁ ⊗[ℂ] F₀)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((LinearMap.lTensorHom E₁).comp (ContinuousLinearMap.coeLM ℂ))
  have hd₀ : Continuous (fun p : unitInterval × Base ↦ d₀ (a p.2.1)) :=
    d₀.continuous_of_finiteDimensional.comp (a.continuous.comp continuous_snd.fst)
  have hd₁ : Continuous (fun p : unitInterval × Base ↦
      d₁ (ContinuousLinearMap.adjoint (a p.2.1))) :=
    d₁.continuous_of_finiteDimensional.comp
      (ContinuousLinearMap.adjoint.continuous.comp (a.continuous.comp continuous_snd.fst))
  have he₀ : Continuous (fun p : unitInterval × Base ↦ e₀ (b p.2.2)) :=
    e₀.continuous_of_finiteDimensional.comp (b.continuous.comp continuous_snd.snd)
  have he₁ : Continuous (fun p : unitInterval × Base ↦
      e₁ (ContinuousLinearMap.adjoint (b p.2.2))) :=
    e₁.continuous_of_finiteDimensional.comp
      (ContinuousLinearMap.adjoint.continuous.comp (b.continuous.comp continuous_snd.snd))
  -- The original affine weights include the axis extension of the cutoff formula.
  have hα : Continuous (fun p : unitInterval × Base ↦
      (productCutoffHomotopyWeight ε p.1 ‖p.2.1.2‖ ‖p.2.2.2‖ : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((productCutoffHomotopyWeight_properties ε hε hε₁).2.2.2.comp
        (continuous_fst.prodMk (continuous_snd.fst.snd.norm.prodMk
          continuous_snd.snd.snd.norm)))
  have hβ : Continuous (fun p : unitInterval × Base ↦
      (productCutoffHomotopyWeight ε p.1 ‖p.2.2.2‖ ‖p.2.1.2‖ : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((productCutoffHomotopyWeight_properties ε hε hε₁).2.2.2.comp
        (continuous_fst.prodMk (continuous_snd.snd.snd.norm.prodMk
          continuous_snd.fst.snd.norm)))
  have haction : Continuous (fun p : (unitInterval × Base) × Even ↦
      gradedProductCutoffSymbol a b ε p.1.1 p.1.2 p.2) := by
    have hfirst := ((hα.comp continuous_fst).smul
      ((hd₀.comp continuous_fst).clm_apply continuous_snd.fst)).sub
        ((hβ.comp continuous_fst).smul
          ((he₁.comp continuous_fst).clm_apply continuous_snd.snd))
    have hsecond := ((hβ.comp continuous_fst).smul
      ((he₀.comp continuous_fst).clm_apply continuous_snd.fst)).add
        ((hα.comp continuous_fst).smul
          ((hd₁.comp continuous_fst).clm_apply continuous_snd.snd))
    convert hfirst.prodMk hsecond using 1
    funext p
    simp only [gradedProductCutoffSymbol, weightedGradedTensorSymbol, reciprocalTensorSymbol,
      TensorProduct.map_smul_left, TensorProduct.map_smul_right]
    simp [d₀, d₁, e₀, e₁, ContinuousLinearMap.adjoint_toLinearMap,
      LinearMap.rTensor_def, LinearMap.lTensor_def, sub_eq_add_neg]
    constructor <;> rfl
  -- The restriction homeomorphisms preserve both the original point and vector.
  let q₀ : TotalSpace Unit (Bundle.Trivial Base Even) ≃ₜ Base × Even :=
    { toFun := fun z ↦ (z.proj, z.snd)
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by
        have hd := (FiberBundle.Prod.isInducing_diag (E₀ ⊗[ℂ] F₀)
          (Bundle.Trivial Base (E₀ ⊗[ℂ] F₀)) (E₁ ⊗[ℂ] F₁)
          (Bundle.Trivial Base (E₁ ⊗[ℂ] F₁))).continuous.comp
            (continuous_unitTotalEquiv Even (Bundle.Trivial Base Even))
        have h₀ := (Bundle.Trivial.homeomorphProd Base (E₀ ⊗[ℂ] F₀)).continuous.comp hd.fst
        have h₁ := (Bundle.Trivial.homeomorphProd Base (E₁ ⊗[ℂ] F₁)).continuous.comp hd.snd
        exact h₀.fst.prodMk (h₀.snd.prodMk h₁.snd)
      continuous_invFun := by
        apply (continuous_modelTotal_iff Even (Bundle.Trivial Base Even) _).mpr
        apply (FiberBundle.Prod.isInducing_diag (E₀ ⊗[ℂ] F₀)
          (Bundle.Trivial Base (E₀ ⊗[ℂ] F₀)) (E₁ ⊗[ℂ] F₁)
          (Bundle.Trivial Base (E₁ ⊗[ℂ] F₁))).continuous_iff.mpr
        exact ((Bundle.Trivial.homeomorphProd Base (E₀ ⊗[ℂ] F₀)).symm.continuous.comp
          (continuous_fst.prodMk continuous_snd.fst)).prodMk
            ((Bundle.Trivial.homeomorphProd Base (E₁ ⊗[ℂ] F₁)).symm.continuous.comp
              (continuous_fst.prodMk continuous_snd.snd)) }
  let q₁ : TotalSpace Unit (Bundle.Trivial Base Odd) ≃ₜ Base × Odd :=
    { toFun := fun z ↦ (z.proj, z.snd)
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by
        have hd := (FiberBundle.Prod.isInducing_diag (E₁ ⊗[ℂ] F₀)
          (Bundle.Trivial Base (E₁ ⊗[ℂ] F₀)) (E₀ ⊗[ℂ] F₁)
          (Bundle.Trivial Base (E₀ ⊗[ℂ] F₁))).continuous.comp
            (continuous_unitTotalEquiv Odd (Bundle.Trivial Base Odd))
        have h₀ := (Bundle.Trivial.homeomorphProd Base (E₁ ⊗[ℂ] F₀)).continuous.comp hd.fst
        have h₁ := (Bundle.Trivial.homeomorphProd Base (E₀ ⊗[ℂ] F₁)).continuous.comp hd.snd
        exact h₀.fst.prodMk (h₀.snd.prodMk h₁.snd)
      continuous_invFun := by
        apply (continuous_modelTotal_iff Odd (Bundle.Trivial Base Odd) _).mpr
        apply (FiberBundle.Prod.isInducing_diag (E₁ ⊗[ℂ] F₀)
          (Bundle.Trivial Base (E₁ ⊗[ℂ] F₀)) (E₀ ⊗[ℂ] F₁)
          (Bundle.Trivial Base (E₀ ⊗[ℂ] F₁))).continuous_iff.mpr
        exact ((Bundle.Trivial.homeomorphProd Base (E₁ ⊗[ℂ] F₀)).symm.continuous.comp
          (continuous_fst.prodMk continuous_snd.fst)).prodMk
            ((Bundle.Trivial.homeomorphProd Base (E₀ ⊗[ℂ] F₁)).symm.continuous.comp
              (continuous_fst.prodMk continuous_snd.snd)) }
  let r₀ : TotalSpace Unit (Restrict (Bundle.Trivial Base Even) Kᶜ) ≃ₜ
      (Kᶜ : Set Base) × Even :=
    { toFun := fun z ↦ (z.proj, z.snd)
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun :=
        (Pullback.continuous_proj Unit (Bundle.Trivial Base Even) Subtype.val).prodMk
          ((q₀.continuous.comp
            (Pullback.continuous_lift Unit (Bundle.Trivial Base Even) Subtype.val)).snd)
      continuous_invFun := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit
          (Bundle.Trivial Base Even) (Subtype.val : (Kᶜ : Set Base) → Base)).continuous_iff]
        exact continuous_fst.prodMk (q₀.symm.continuous.comp
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) }
  let r₁ : TotalSpace Unit (Restrict (Bundle.Trivial Base Odd) Kᶜ) ≃ₜ
      (Kᶜ : Set Base) × Odd :=
    { toFun := fun z ↦ (z.proj, z.snd)
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun :=
        (Pullback.continuous_proj Unit (Bundle.Trivial Base Odd) Subtype.val).prodMk
          ((q₁.continuous.comp
            (Pullback.continuous_lift Unit (Bundle.Trivial Base Odd) Subtype.val)).snd)
      continuous_invFun := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit
          (Bundle.Trivial Base Odd) (Subtype.val : (Kᶜ : Set Base) → Base)).continuous_iff]
        exact continuous_fst.prodMk (q₁.symm.continuous.comp
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) }
  have hforward : Continuous
      (fun z : unitInterval × TotalSpace Unit (Restrict (Bundle.Trivial Base Even) Kᶜ) ↦
        (⟨z.2.proj, gradedProductCutoffSymbol a b ε z.1 z.2.proj.val z.2.snd⟩ :
          TotalSpace Unit (Restrict (Bundle.Trivial Base Odd) Kᶜ))) :=
    r₁.symm.continuous.comp (((r₀.continuous.comp continuous_snd).fst).prodMk
      (haction.comp ((continuous_fst.prodMk
        (continuous_subtype_val.comp (r₀.continuous.comp continuous_snd).fst)).prodMk
          (r₀.continuous.comp continuous_snd).snd)))
  -- Invert exactly the same matrix over the full cylinder, using local finite-rank inversion.
  let B := unitInterval × (Kᶜ : Set Base)
  let := modelTopology Even (Bundle.Trivial B Even)
  let := modelTopology Odd (Bundle.Trivial B Odd)
  let := isFiniteRank_model Even (Bundle.Trivial B Even)
  let := isFiniteRank_model Odd (Bundle.Trivial B Odd)
  let t₀ : TotalSpace Unit (Bundle.Trivial B Even) ≃ₜ B × Even :=
    { toFun := fun z ↦ (z.proj, z.snd)
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by
        have hd := (FiberBundle.Prod.isInducing_diag (E₀ ⊗[ℂ] F₀)
          (Bundle.Trivial B (E₀ ⊗[ℂ] F₀)) (E₁ ⊗[ℂ] F₁)
          (Bundle.Trivial B (E₁ ⊗[ℂ] F₁))).continuous.comp
            (continuous_unitTotalEquiv Even (Bundle.Trivial B Even))
        have h₀ := (Bundle.Trivial.homeomorphProd B (E₀ ⊗[ℂ] F₀)).continuous.comp hd.fst
        have h₁ := (Bundle.Trivial.homeomorphProd B (E₁ ⊗[ℂ] F₁)).continuous.comp hd.snd
        exact h₀.fst.prodMk (h₀.snd.prodMk h₁.snd)
      continuous_invFun := by
        apply (continuous_modelTotal_iff Even (Bundle.Trivial B Even) _).mpr
        apply (FiberBundle.Prod.isInducing_diag (E₀ ⊗[ℂ] F₀)
          (Bundle.Trivial B (E₀ ⊗[ℂ] F₀)) (E₁ ⊗[ℂ] F₁)
          (Bundle.Trivial B (E₁ ⊗[ℂ] F₁))).continuous_iff.mpr
        exact ((Bundle.Trivial.homeomorphProd B (E₀ ⊗[ℂ] F₀)).symm.continuous.comp
          (continuous_fst.prodMk continuous_snd.fst)).prodMk
            ((Bundle.Trivial.homeomorphProd B (E₁ ⊗[ℂ] F₁)).symm.continuous.comp
              (continuous_fst.prodMk continuous_snd.snd)) }
  let t₁ : TotalSpace Unit (Bundle.Trivial B Odd) ≃ₜ B × Odd :=
    { toFun := fun z ↦ (z.proj, z.snd)
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by
        have hd := (FiberBundle.Prod.isInducing_diag (E₁ ⊗[ℂ] F₀)
          (Bundle.Trivial B (E₁ ⊗[ℂ] F₀)) (E₀ ⊗[ℂ] F₁)
          (Bundle.Trivial B (E₀ ⊗[ℂ] F₁))).continuous.comp
            (continuous_unitTotalEquiv Odd (Bundle.Trivial B Odd))
        have h₀ := (Bundle.Trivial.homeomorphProd B (E₁ ⊗[ℂ] F₀)).continuous.comp hd.fst
        have h₁ := (Bundle.Trivial.homeomorphProd B (E₀ ⊗[ℂ] F₁)).continuous.comp hd.snd
        exact h₀.fst.prodMk (h₀.snd.prodMk h₁.snd)
      continuous_invFun := by
        apply (continuous_modelTotal_iff Odd (Bundle.Trivial B Odd) _).mpr
        apply (FiberBundle.Prod.isInducing_diag (E₁ ⊗[ℂ] F₀)
          (Bundle.Trivial B (E₁ ⊗[ℂ] F₀)) (E₀ ⊗[ℂ] F₁)
          (Bundle.Trivial B (E₀ ⊗[ℂ] F₁))).continuous_iff.mpr
        exact ((Bundle.Trivial.homeomorphProd B (E₁ ⊗[ℂ] F₀)).symm.continuous.comp
          (continuous_fst.prodMk continuous_snd.fst)).prodMk
            ((Bundle.Trivial.homeomorphProd B (E₀ ⊗[ℂ] F₁)).symm.continuous.comp
              (continuous_fst.prodMk continuous_snd.snd)) }
  let f : Hom (Bundle.Trivial B Even) (Bundle.Trivial B Odd) :=
    { linearMap := fun p ↦ gradedProductCutoffSymbol a b ε p.1 p.2.val
      continuous_total := t₁.symm.continuous.comp (t₀.continuous.fst.prodMk
        (haction.comp ((t₀.continuous.fst.fst.prodMk
          (continuous_subtype_val.comp t₀.continuous.fst.snd)).prodMk t₀.continuous.snd))) }
  have hf (p : B) : Function.Bijective (f.linearMap p) :=
    gradedProductCutoffSymbol_bijective a b R hR ha hb ε hε hε₁ p.1 p.2
  have hinverse : Continuous (fun p : B × Odd ↦
      (LinearEquiv.ofBijective (f.linearMap p.1) (hf p.1)).symm p.2) :=
    (t₀.continuous.comp ((f.continuous_inverse hf).comp t₁.symm.continuous)).snd
  refine ⟨hforward, ?_⟩
  exact r₀.symm.continuous.comp (((r₁.continuous.comp continuous_snd).fst).prodMk
    (hinverse.comp ((continuous_fst.prodMk
      (r₁.continuous.comp continuous_snd).fst).prodMk
        (r₁.continuous.comp continuous_snd).snd)))

/-- The actual graded symbol triple at time t, with one compact control for every time. -/
def gradedProductCutoffTriple (t : unitInterval) :
    letI := modelTopology Even (Bundle.Trivial Base Even)
    letI := modelTopology Odd (Bundle.Trivial Base Odd)
    CompactSupportTriple (Bundle.Trivial Base Even) (Bundle.Trivial Base Odd) :=
  letI := modelTopology Even (Bundle.Trivial Base Even)
  letI := modelTopology Odd (Bundle.Trivial Base Odd)
  { control := K
    isCompact_control :=
      (isCompact_univ.prod (isCompact_closedBall (0 : V) R)).prod
        (isCompact_univ.prod (isCompact_closedBall (0 : W) R))
    boundary :=
      { linearEquiv := fun z ↦ LinearEquiv.ofBijective (gradedProductCutoffSymbol a b ε t z.val)
          (gradedProductCutoffSymbol_bijective a b R hR ha hb ε hε hε₁ t z)
        continuous_total :=
          (gradedProductCutoffSymbol_boundary_continuity a b R hR ha hb ε hε hε₁).1.comp
            (continuous_const.prodMk continuous_id)
        continuous_symm :=
          (gradedProductCutoffSymbol_boundary_continuity a b R hR ha hb ε hε hε₁).2.comp
            (continuous_const.prodMk continuous_id) } }

/-- The specified affine family is a homotopy of the original uncut and cutoff triples. -/
theorem gradedProductCutoffTriple_homotopic :
    letI := modelTopology Even (Bundle.Trivial Base Even)
    letI := modelTopology Odd (Bundle.Trivial Base Odd)
    (gradedProductCutoffTriple a b R hR ha hb ε hε hε₁ 0).Homotopic
      (gradedProductCutoffTriple a b R hR ha hb ε hε hε₁ 1) := by
  /- Use exactly K, not time-dependent compact controls. The full-cylinder
  continuity theorem and the specified fiber equivalences define the required
  IsoHomotopy. At t=0 both weights are one, giving the original SG matrix;
  at t=1 the weights are the two original productFrequencyCutoff values.
  The endpoint maps are the boundary maps of the displayed triples themselves.
  This proves supported homotopy, not just agreement on fixed compact sets. -/
  -- Assemble a continuous family on one control into a supported homotopy.
  -- Prove the cylinder conversion with abstract fibers to keep their original topologies fixed.
  have assemble {Z : Type _} [TopologicalSpace Z]
      (E F : Z → Type _) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
      (L : Set Z) (hL : IsCompact L)
      (e : unitInterval → Iso (Restrict E Lᶜ) (Restrict F Lᶜ))
      (he : Continuous (fun z : unitInterval × TotalSpace Unit (Restrict E Lᶜ) ↦
        (⟨z.2.proj, (e z.1).linearEquiv z.2.proj z.2.snd⟩ :
          TotalSpace Unit (Restrict F Lᶜ))))
      (hei : Continuous (fun z : unitInterval × TotalSpace Unit (Restrict F Lᶜ) ↦
        (⟨z.2.proj, ((e z.1).linearEquiv z.2.proj).symm z.2.snd⟩ :
          TotalSpace Unit (Restrict E Lᶜ)))) :
      (⟨L, hL, e 0⟩ : CompactSupportTriple E F).Homotopic ⟨L, hL, e 1⟩ := by
    let p : unitInterval × (Lᶜ : Set Z) → (Lᶜ : Set Z) := Prod.snd
    have hE : Continuous (fun z : TotalSpace Unit (p *ᵖ (Restrict E Lᶜ)) ↦
        (z.proj.1, (⟨z.proj.2, z.snd⟩ : TotalSpace Unit (Restrict E Lᶜ)))) :=
      (Pullback.continuous_proj Unit (Restrict E Lᶜ) p).fst.prodMk
        (Pullback.continuous_lift Unit (Restrict E Lᶜ) p)
    have hF : Continuous (fun z : TotalSpace Unit (p *ᵖ (Restrict F Lᶜ)) ↦
        (z.proj.1, (⟨z.proj.2, z.snd⟩ : TotalSpace Unit (Restrict F Lᶜ)))) :=
      (Pullback.continuous_proj Unit (Restrict F Lᶜ) p).fst.prodMk
        (Pullback.continuous_lift Unit (Restrict F Lᶜ) p)
    let q : Iso (p *ᵖ (Restrict E Lᶜ)) (p *ᵖ (Restrict F Lᶜ)) :=
      { linearEquiv := fun z ↦ (e z.1).linearEquiv z.2
        continuous_total := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (Restrict F Lᶜ) p).continuous_iff]
          exact (Pullback.continuous_proj Unit (Restrict E Lᶜ) p).prodMk (he.comp hE)
        continuous_symm := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (Restrict E Lᶜ) p).continuous_iff]
          exact (Pullback.continuous_proj Unit (Restrict F Lᶜ) p).prodMk (hei.comp hF) }
    refine ⟨L, hL, Set.Subset.refl _, Set.Subset.refl _,
      ⟨{ iso := q, map_zero := ?_, map_one := ?_ }⟩⟩
    · intro z v
      exact (CompactSupportTriple.enlarge_apply
        (⟨L, hL, e 0⟩ : CompactSupportTriple E F) L hL (Set.Subset.refl _) z v).symm
    · intro z v
      exact (CompactSupportTriple.enlarge_apply
        (⟨L, hL, e 1⟩ : CompactSupportTriple E F) L hL (Set.Subset.refl _) z v).symm
  let := modelTopology Even (Bundle.Trivial Base Even)
  let := modelTopology Odd (Bundle.Trivial Base Odd)
  -- Instantiate with the original matrix family and its single compact product control.
  have hc := gradedProductCutoffSymbol_boundary_continuity a b R hR ha hb ε hε hε₁
  exact assemble (Bundle.Trivial Base Even) (Bundle.Trivial Base Odd) K
    ((isCompact_univ.prod (isCompact_closedBall (0 : V) R)).prod
      (isCompact_univ.prod (isCompact_closedBall (0 : W) R)))
    (fun t ↦ (gradedProductCutoffTriple a b R hR ha hb ε hε hε₁ t).boundary) hc.1 hc.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1800000 in
-- Retain both tensor models and dependent compact-support transports in the two homotopies.
/-- Every time slice has the original compact-support product class of its two factor symbols. -/
theorem gradedProductCutoffTriple_compactSupportClass (t : unitInterval) :
    letI := modelTopology E₀ (Bundle.Trivial (X × V) E₀)
    letI := modelTopology E₁ (Bundle.Trivial (X × V) E₁)
    letI := modelTopology F₀ (Bundle.Trivial (Y × W) F₀)
    letI := modelTopology F₁ (Bundle.Trivial (Y × W) F₁)
    letI := isFiniteRank_model E₀ (Bundle.Trivial (X × V) E₀)
    letI := isFiniteRank_model E₁ (Bundle.Trivial (X × V) E₁)
    letI := isFiniteRank_model F₀ (Bundle.Trivial (Y × W) F₀)
    letI := isFiniteRank_model F₁ (Bundle.Trivial (Y × W) F₁)
    letI := modelTopology Even (Bundle.Trivial Base Even)
    letI := modelTopology Odd (Bundle.Trivial Base Odd)
    letI := isFiniteRank_model Even (Bundle.Trivial Base Even)
    letI := isFiniteRank_model Odd (Bundle.Trivial Base Odd)
    (gradedProductCutoffTriple a b R hR ha hb ε hε hε₁ t).compactSupportClass =
      compactSupportKZeroExternalProduct (euclideanSymbolTriple a R ha).compactSupportClass
        (euclideanSymbolTriple b R hb).compactSupportClass := by
  /- Enlarge the two original controls once and choose their independent scalar
  cutoffs. First mix the given time-t SG weights with these cutoffs. Before the
  last time, the larger-frequency factor keeps positive weight; at the endpoint,
  at least one cutoff is one outside the enlarged product control. Then interpolate
  only the reverse blocks from adjoints to reciprocal maps. Their reverse composite
  is a sum of nonnegative adjoint squares and a positive scalar off that same control.
  The endpoint is compared with the original supported external product through
  its specified small-bundle maps and actual tensor/sum topologies. -/
  classical
  let := modelTopology E₀ (Trivial (X × V) E₀)
  let := modelTopology E₁ (Trivial (X × V) E₁)
  let := modelTopology F₀ (Trivial (Y × W) F₀)
  let := modelTopology F₁ (Trivial (Y × W) F₁)
  let := isFiniteRank_model E₀ (Trivial (X × V) E₀)
  let := isFiniteRank_model E₁ (Trivial (X × V) E₁)
  let := isFiniteRank_model F₀ (Trivial (Y × W) F₀)
  let := isFiniteRank_model F₁ (Trivial (Y × W) F₁)
  let := modelTopology Even (Trivial Base Even)
  let := modelTopology Odd (Trivial Base Odd)
  let := isFiniteRank_model Even (Trivial Base Even)
  let := isFiniteRank_model Odd (Trivial Base Odd)
  have := FiniteDimensional.complete ℂ E₀
  have := FiniteDimensional.complete ℂ E₁
  have := FiniteDimensional.complete ℂ F₀
  have := FiniteDimensional.complete ℂ F₁
  let A := euclideanSymbolTriple a R ha
  let B := euclideanSymbolTriple b R hb
  -- Choose one enlarged product control for both changes of the original symbol.
  obtain ⟨U, hU, hAU, L, hL, hUL, ρ, hρzero, hρone⟩ :=
    exists_time_cutoff A.control A.isCompact_control
  obtain ⟨V', hV', hBV, M, hM, hVM, τ, hτzero, hτone⟩ :=
    exists_time_cutoff B.control B.isCompact_control
  have hAL : A.control ⊆ L := hAU.trans hUL
  have hBM : B.control ⊆ M := hBV.trans hVM
  let K' := L ×ˢ M
  have hK' : IsCompact K' := hL.prod hM
  have hKK' : K ⊆ K' := Set.prod_mono hAL hBM
  obtain ⟨Q, hQcontrol, hQmap, hQclass⟩ := exists_trivial_supportedExternalProduct
    A B ρ U hU hAU hρzero L hL hρone τ V' hV' hBV hτzero M hM hτone
  -- Express the actual zero-extended cutoff maps as continuous finite matrices.
  let d := matrixOfTrivialHom (A.cutoffHom ρ U hU hAU hρzero)
  let di := matrixOfTrivialHom (A.inverse.cutoffHom ρ U hU hAU hρzero)
  let e := matrixOfTrivialHom (B.cutoffHom τ V' hV' hBV hτzero)
  let ei := matrixOfTrivialHom (B.inverse.cutoffHom τ V' hV' hBV hτzero)
  have hd (x : X × V) : (d x).toLinearMap = ((ρ x : ℝ) : ℂ) • (a x).toLinearMap := by
    change A.cutoffLinearMap ρ x = _
    by_cases hx : x ∈ A.control
    · have hzero := hρzero x (hAU hx)
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_left hx, hzero,
        Set.Icc.coe_zero, Complex.ofReal_zero, zero_smul]
    · dsimp only [CompactSupportTriple.cutoffLinearMap]
      rw [dite_eq_right hx]
      rfl
  have he (y : Y × W) : (e y).toLinearMap = ((τ y : ℝ) : ℂ) • (b y).toLinearMap := by
    change B.cutoffLinearMap τ y = _
    by_cases hy : y ∈ B.control
    · have hzero := hτzero y (hBV hy)
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_left hy, hzero,
        Set.Icc.coe_zero, Complex.ofReal_zero, zero_smul]
    · dsimp only [CompactSupportTriple.cutoffLinearMap]
      rw [dite_eq_right hy]
      rfl
  have haL (x : X × V) (hx : x ∉ L) : Function.Bijective (a x) := by
    apply ha x.1 x.2
    apply lt_of_not_ge
    intro h
    apply hx
    apply hAL
    exact ⟨Set.mem_univ _, by simpa only [Metric.mem_closedBall, dist_zero_right] using h⟩
  have hbM (y : Y × W) (hy : y ∉ M) : Function.Bijective (b y) := by
    apply hb y.1 y.2
    apply lt_of_not_ge
    intro h
    apply hy
    apply hBM
    exact ⟨Set.mem_univ _, by simpa only [Metric.mem_closedBall, dist_zero_right] using h⟩
  let α (s : I) (z : Base) : ℝ :=
    (1 - (s : ℝ)) * productCutoffHomotopyWeight ε t ‖z.1.2‖ ‖z.2.2‖ +
      (s : ℝ) * (ρ z.1 : ℝ)
  let β (s : I) (z : Base) : ℝ :=
    (1 - (s : ℝ)) * productCutoffHomotopyWeight ε t ‖z.2.2‖ ‖z.1.2‖ +
      (s : ℝ) * (τ z.2 : ℝ)
  have hα : Continuous (fun p : I × Base ↦ α p.1 p.2) := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((productCutoffHomotopyWeight_properties ε hε hε₁).2.2.2.comp
        (continuous_const.prodMk (continuous_snd.fst.snd.norm.prodMk
          continuous_snd.snd.snd.norm)))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp (ρ.continuous.comp continuous_snd.fst)))
  have hβ : Continuous (fun p : I × Base ↦ β p.1 p.2) := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((productCutoffHomotopyWeight_properties ε hε hε₁).2.2.2.comp
        (continuous_const.prodMk (continuous_snd.snd.snd.norm.prodMk
          continuous_snd.fst.snd.norm)))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp (τ.continuous.comp continuous_snd.snd)))
  let Φ : C(I × Base, Even →L[ℂ] Odd) :=
    ⟨fun p ↦ (weightedGradedTensorSymbol (a p.2.1).toLinearMap (b p.2.2).toLinearMap
      (α p.1 p.2) (β p.1 p.2)).toContinuousLinearMap, by
      exact continuous_weightedGradedTensorSymbol (Z := I × Base)
        (E₀ := E₀) (E₁ := E₁) (F₀ := F₀) (F₁ := F₁)
        ⟨fun p ↦ a p.2.1, a.continuous.comp continuous_snd.fst⟩
        ⟨fun p ↦ b p.2.2, b.continuous.comp continuous_snd.snd⟩
        ⟨fun p ↦ α p.1 p.2, hα⟩ ⟨fun p ↦ β p.1 p.2, hβ⟩⟩
  have hΦ (s : I) (z : (K'ᶜ : Set Base)) : Function.Bijective (Φ (s, z.val)) := by
    apply weightedGradedTensorSymbol_bijective (a z.val.1).toLinearMap
      (b z.val.2).toLinearMap (α s z.val) (β s z.val)
    by_cases hs : (s : ℝ) = 1
    · rcases not_and_or.mp z.property with hx | hy
      · left
        refine ⟨?_, haL z.val.1 hx⟩
        simp only [α, hs, hρone _ hx, Set.Icc.coe_one, sub_self, zero_mul, one_mul,
          zero_add, ne_eq, one_ne_zero, not_false_eq_true]
      · right
        refine ⟨?_, hbM z.val.2 hy⟩
        simp only [β, hs, hτone _ hy, Set.Icc.coe_one, sub_self, zero_mul, one_mul,
          zero_add, ne_eq, one_ne_zero, not_false_eq_true]
    · have hspos : 0 < 1 - (s : ℝ) := sub_pos.mpr (lt_of_le_of_ne s.property.2 hs)
      have hlarge : R < ‖z.val.1.2‖ ∨ R < ‖z.val.2.2‖ := by
        by_contra! h
        exact z.property (hKK' ⟨⟨Set.mem_univ _, by
          simpa only [Metric.mem_closedBall, dist_zero_right] using h.1⟩,
          ⟨Set.mem_univ _, by
            simpa only [Metric.mem_closedBall, dist_zero_right] using h.2⟩⟩)
      by_cases h : ‖z.val.2.2‖ ≤ ‖z.val.1.2‖
      · left
        refine ⟨?_, ha _ _ (hlarge.elim id (fun h' ↦ h'.trans_le h))⟩
        apply ne_of_gt
        dsimp only [α]
        rw [(productCutoffHomotopyWeight_properties ε hε hε₁).2.2.1 t _ _
          (norm_nonneg _) (norm_nonneg _) h, mul_one]
        exact add_pos_of_pos_of_nonneg hspos (mul_nonneg s.property.1 (ρ z.val.1).property.1)
      · right
        have h' := le_of_not_ge h
        refine ⟨?_, hb _ _ (hlarge.elim (fun h'' ↦ h''.trans_le h') id)⟩
        apply ne_of_gt
        dsimp only [β]
        rw [(productCutoffHomotopyWeight_properties ε hε hε₁).2.2.1 t _ _
          (norm_nonneg _) (norm_nonneg _) h', mul_one]
        exact add_pos_of_pos_of_nonneg hspos (mul_nonneg s.property.1 (τ z.val.2).property.1)
  -- Deform the reverses to the original inverses; the real diagonal stays strictly positive.
  let Ψ : C(I × Base, Even →L[ℂ] Odd) :=
    ⟨fun p ↦ (reciprocalTensorSymbol (d p.2.1).toLinearMap
      (((1 - (p.1 : ℝ) : ℝ) : ℂ) • (d p.2.1).toLinearMap.adjoint +
        ((p.1 : ℝ) : ℂ) • (di p.2.1).toLinearMap) (e p.2.2).toLinearMap
      (((1 - (p.1 : ℝ) : ℝ) : ℂ) • (e p.2.2).toLinearMap.adjoint +
        ((p.1 : ℝ) : ℂ) • (ei p.2.2).toLinearMap)).toContinuousLinearMap, by
      exact continuous_reciprocalTensorSymbol_adjoint_homotopy (Z := I × Base)
        (E₀ := E₀) (E₁ := E₁) (F₀ := F₀) (F₁ := F₁)
        ⟨fun p ↦ d p.2.1, d.continuous.comp continuous_snd.fst⟩
        ⟨fun p ↦ di p.2.1, di.continuous.comp continuous_snd.fst⟩
        ⟨fun p ↦ e p.2.2, e.continuous.comp continuous_snd.snd⟩
        ⟨fun p ↦ ei p.2.2, ei.continuous.comp continuous_snd.snd⟩
        ⟨fun p ↦ (p.1 : ℝ), continuous_subtype_val.comp continuous_fst⟩⟩
  have hΨ (s : I) (z : (K'ᶜ : Set Base)) : Function.Bijective (Ψ (s, z.val)) := by
    have h₁ := A.cutoffHom_inverse_comp ρ U hU hAU hρzero z.val.1
    have h₂ := B.cutoffHom_inverse_comp τ V' hV' hBV hτzero z.val.2
    have hr : 0 < (ρ z.val.1 : ℝ) ^ 2 + (τ z.val.2 : ℝ) ^ 2 := by
      rcases not_and_or.mp z.property with hx | hy
      · rw [hρone _ hx]
        norm_num only [Set.Icc.coe_one, one_pow]
        positivity
      · rw [hτone _ hy]
        norm_num only [Set.Icc.coe_one, one_pow]
        positivity
    apply reciprocalTensorSymbol_adjoint_homotopy_bijective _ _ _ _
      ((ρ z.val.1 : ℝ) ^ 2) ((τ z.val.2 : ℝ) ^ 2) hr
    · change ((A.inverse.cutoffHom ρ U hU hAU hρzero).linearMap z.val.1).comp
        ((A.cutoffHom ρ U hU hAU hρzero).linearMap z.val.1) = _
      simpa only [Complex.ofReal_pow] using h₁.1
    · change ((A.cutoffHom ρ U hU hAU hρzero).linearMap z.val.1).comp
        ((A.inverse.cutoffHom ρ U hU hAU hρzero).linearMap z.val.1) = _
      simpa only [Complex.ofReal_pow] using h₁.2
    · change ((B.inverse.cutoffHom τ V' hV' hBV hτzero).linearMap z.val.2).comp
        ((B.cutoffHom τ V' hV' hBV hτzero).linearMap z.val.2) = _
      simpa only [Complex.ofReal_pow] using h₂.1
    · change ((B.cutoffHom τ V' hV' hBV hτzero).linearMap z.val.2).comp
        ((B.inverse.cutoffHom τ V' hV' hBV hτzero).linearMap z.val.2) = _
      simpa only [Complex.ofReal_pow] using h₂.2
    · rcases not_and_or.mp z.property with hx | hy
      · left
        change Function.Bijective (d z.val.1).toLinearMap
        rw [hd, hρone _ hx]
        simpa using haL z.val.1 hx
      · right
        change Function.Bijective (e z.val.2).toLinearMap
        rw [he, hτone _ hy]
        simpa using hbM z.val.2 hy
  -- The original product models are retained by their explicit point-vector coordinates.
  let q₀ : TotalSpace Unit (Bundle.Trivial Base Even) ≃ₜ Base × Even :=
    { toFun := fun z ↦ (z.proj, z.snd)
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by
        have hd := (FiberBundle.Prod.isInducing_diag (E₀ ⊗[ℂ] F₀)
          (Bundle.Trivial Base (E₀ ⊗[ℂ] F₀)) (E₁ ⊗[ℂ] F₁)
          (Bundle.Trivial Base (E₁ ⊗[ℂ] F₁))).continuous.comp
            (continuous_unitTotalEquiv Even (Bundle.Trivial Base Even))
        have h₀ := (Bundle.Trivial.homeomorphProd Base (E₀ ⊗[ℂ] F₀)).continuous.comp hd.fst
        have h₁ := (Bundle.Trivial.homeomorphProd Base (E₁ ⊗[ℂ] F₁)).continuous.comp hd.snd
        exact h₀.fst.prodMk (h₀.snd.prodMk h₁.snd)
      continuous_invFun := by
        apply (continuous_modelTotal_iff Even (Bundle.Trivial Base Even) _).mpr
        apply (FiberBundle.Prod.isInducing_diag (E₀ ⊗[ℂ] F₀)
          (Bundle.Trivial Base (E₀ ⊗[ℂ] F₀)) (E₁ ⊗[ℂ] F₁)
          (Bundle.Trivial Base (E₁ ⊗[ℂ] F₁))).continuous_iff.mpr
        exact ((Bundle.Trivial.homeomorphProd Base (E₀ ⊗[ℂ] F₀)).symm.continuous.comp
          (continuous_fst.prodMk continuous_snd.fst)).prodMk
            ((Bundle.Trivial.homeomorphProd Base (E₁ ⊗[ℂ] F₁)).symm.continuous.comp
              (continuous_fst.prodMk continuous_snd.snd)) }
  let q₁ : TotalSpace Unit (Bundle.Trivial Base Odd) ≃ₜ Base × Odd :=
    { toFun := fun z ↦ (z.proj, z.snd)
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by
        have hd := (FiberBundle.Prod.isInducing_diag (E₁ ⊗[ℂ] F₀)
          (Bundle.Trivial Base (E₁ ⊗[ℂ] F₀)) (E₀ ⊗[ℂ] F₁)
          (Bundle.Trivial Base (E₀ ⊗[ℂ] F₁))).continuous.comp
            (continuous_unitTotalEquiv Odd (Bundle.Trivial Base Odd))
        have h₀ := (Bundle.Trivial.homeomorphProd Base (E₁ ⊗[ℂ] F₀)).continuous.comp hd.fst
        have h₁ := (Bundle.Trivial.homeomorphProd Base (E₀ ⊗[ℂ] F₁)).continuous.comp hd.snd
        exact h₀.fst.prodMk (h₀.snd.prodMk h₁.snd)
      continuous_invFun := by
        apply (continuous_modelTotal_iff Odd (Bundle.Trivial Base Odd) _).mpr
        apply (FiberBundle.Prod.isInducing_diag (E₁ ⊗[ℂ] F₀)
          (Bundle.Trivial Base (E₁ ⊗[ℂ] F₀)) (E₀ ⊗[ℂ] F₁)
          (Bundle.Trivial Base (E₀ ⊗[ℂ] F₁))).continuous_iff.mpr
        exact ((Bundle.Trivial.homeomorphProd Base (E₁ ⊗[ℂ] F₀)).symm.continuous.comp
          (continuous_fst.prodMk continuous_snd.fst)).prodMk
            ((Bundle.Trivial.homeomorphProd Base (E₀ ⊗[ℂ] F₁)).symm.continuous.comp
              (continuous_fst.prodMk continuous_snd.snd)) }
  let fmid : Hom (Trivial Base Even) (Trivial Base Odd) :=
    { linearMap z := (Φ (1, z)).toLinearMap
      continuous_total := q₁.symm.continuous.comp (q₀.continuous.fst.prodMk
        ((Φ.continuous.comp (continuous_const.prodMk q₀.continuous.fst)).clm_apply
          q₀.continuous.snd)) }
  let := isFiniteRank_restrict (E := Trivial Base Even) K'ᶜ
  let := isFiniteRank_restrict (E := Trivial Base Odd) K'ᶜ
  let mid : CompactSupportTriple (Trivial Base Even) (Trivial Base Odd) :=
    { control := K'
      isCompact_control := hK'
      boundary := (fmid.restrict K'ᶜ).toIso (fun z ↦ hΦ 1 z) }
  have hfirst : (gradedProductCutoffTriple a b R hR ha hb ε hε hε₁ t).compactSupportClass =
      mid.compactSupportClass := by
    apply matrixFamily_compactSupportClass_eq q₀.continuous.snd q₁.symm.continuous
      K' hK' Φ hΦ _ mid hKK' (Set.Subset.refl _)
    · intro z v
      rw [(gradedProductCutoffTriple a b R hR ha hb ε hε hε₁ t).enlarge_apply]
      simp only [Φ, ContinuousMap.coe_mk, α, β, Set.Icc.coe_zero, sub_zero, one_mul,
        zero_mul, add_zero]
      rfl
    · intro z v
      rw [mid.enlarge_apply]
      rfl
  have hsecond : mid.compactSupportClass = Q.compactSupportClass := by
    apply matrixFamily_compactSupportClass_eq q₀.continuous.snd q₁.symm.continuous
      K' hK' Ψ hΨ mid Q (Set.Subset.refl _) (by rw [hQcontrol])
    · intro z v
      rw [mid.enlarge_apply]
      change reciprocalTensorSymbol (d z.val.1).toLinearMap
        (((1 - (0 : I) : ℝ) : ℂ) • (d z.val.1).toLinearMap.adjoint +
          (((0 : I) : ℝ) : ℂ) • (di z.val.1).toLinearMap) (e z.val.2).toLinearMap
        (((1 - (0 : I) : ℝ) : ℂ) • (e z.val.2).toLinearMap.adjoint +
          (((0 : I) : ℝ) : ℂ) • (ei z.val.2).toLinearMap) v =
        weightedGradedTensorSymbol (a z.val.1).toLinearMap (b z.val.2).toLinearMap
          (α 1 z.val) (β 1 z.val) v
      have hρstar : star ((ρ z.val.1 : ℝ) : ℂ) = ((ρ z.val.1 : ℝ) : ℂ) :=
        Complex.conj_ofReal _
      have hτstar : star ((τ z.val.2 : ℝ) : ℂ) = ((τ z.val.2 : ℝ) : ℂ) :=
        Complex.conj_ofReal _
      simp only [Set.Icc.coe_zero, Complex.ofReal_zero, sub_zero, Complex.ofReal_one,
        one_smul, zero_smul, add_zero, hd, he, map_smulₛₗ,
        starRingEnd_apply, hρstar, hτstar, α, β, Set.Icc.coe_one, sub_self,
        zero_mul, zero_add, one_mul, weightedGradedTensorSymbol]
    · intro z v
      rw [Q.enlarge_apply]
      rw [hQmap]
      simp only [Ψ, ContinuousMap.coe_mk, Set.Icc.coe_one, sub_self, Complex.ofReal_zero,
        Complex.ofReal_one, zero_smul, one_smul, zero_add]
      rfl
  exact hfirst.trans (hsecond.trans hQclass)

end AtiyahSinger
