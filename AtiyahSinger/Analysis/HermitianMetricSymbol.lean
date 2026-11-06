/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalEllipticSymbol
public import AtiyahSinger.Analysis.GlobalSymbolAdjoint
public import AtiyahSinger.Geometry.HermitianMetricAdjoint

/-!
# Symbols adjointed with explicit Hermitian metrics

Public module ID: M0729.

D02/D05/A02: fiber adjunction descends to the actual principal quotient.
The covector and real order stay fixed; changing metrics conjugates the fiber map.
Sources: SG III.3.11 and III.5 pp.194–195. These explicit-data comparisons are
project deductions. They require neither a density nor a compact base.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

namespace SmoothHermitianMetric

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

/-- Adjoint the actual fiber map at the same covector. -/
def symbolAdjoint (p : GlobalSymbolFunction (n := n) E F) :
    GlobalSymbolFunction (n := n) F E :=
  fun x ξ ↦ h.adjoint k x (p x ξ)

/-- The symbol adjunction identity retains the original covector. -/
theorem pairing_symbolAdjoint (p : GlobalSymbolFunction (n := n) E F)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
    (u : E x) (v : F x) :
    h.pairing x u (h.symbolAdjoint k p x ξ v) = k.pairing x (p x ξ u) v := by
  /- Apply the fiber adjunction identity to p x ξ. This uses the same real
  covector on both sides, including ξ=0, without a transpose frequency reflection. -/
  exact h.pairing_adjoint k x (p x ξ) u v

/-- The symbol operation is additive. -/
theorem symbolAdjoint_add (p p' : GlobalSymbolFunction (n := n) E F) :
    h.symbolAdjoint k (p + p') = h.symbolAdjoint k p + h.symbolAdjoint k p'  := by
  /- At each x and ξ apply additivity of the explicit fiber adjoint.
  Function extensionality assembles these equalities of continuous fiber maps. -/
  funext x ξ
  exact h.adjoint_add k x (p x ξ) (p' x ξ)

/-- Complex scalar multiplication is conjugated. -/
theorem symbolAdjoint_smul (c : ℂ) (p : GlobalSymbolFunction (n := n) E F) :
    h.symbolAdjoint k (c • p) = conj c • h.symbolAdjoint k p := by
  /- Evaluate at each fiber and use adjoint_smul. Conjugation is essential
  here; positive real homogeneity is a separate consequence of this identity. -/
  funext x ξ
  exact h.adjoint_smul k x c (p x ξ)

/-- Double symbol adjunction is exact before passing to the quotient. -/
theorem symbolAdjoint_adjoint (p : GlobalSymbolFunction (n := n) E F) :
    k.symbolAdjoint h (h.symbolAdjoint k p) = p := by
  /- Use double fiber adjunction pointwise. Equality of functions includes
  the zero section, so this identity has no lower-order or smoothing remainder. -/
  funext x ξ
  exact h.adjoint_adjoint k x (p x ξ)

/-- The change of both metrics has the exact weighted fiber formula. -/
theorem symbolAdjoint_change (h' : SmoothHermitianMetric (n := n) (r := r) E)
    (k' : SmoothHermitianMetric (n := n) (r := q) F)
    (p : GlobalSymbolFunction (n := n) E F) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
    h'.symbolAdjoint k' p x ξ = (h'.change h x).toContinuousLinearMap.comp
      ((h.symbolAdjoint k p x ξ).comp (k.change k' x).toContinuousLinearMap) := by
  /- Apply the fiber metric-change formula to p x ξ. Keep the input
  inverse Gram change on the left and the output change on the right; they
  generally do not commute, and the principal symbol need not stay equal. -/
  exact h.adjoint_change k h' k' x (p x ξ)

/-- Positive-real homogeneity keeps its degree under adjunction. -/
theorem isHomogeneous_symbolAdjoint {m : ℝ} {p : GlobalSymbolFunction (n := n) E F}
    (hp : IsHomogeneousGlobalSymbol E F m p) :
    IsHomogeneousGlobalSymbol F E m (h.symbolAdjoint k p) := by
  /- Adjoint the homogeneity equation at ξ≠0 and t>0. The factor t^m
  is real, so conjugation fixes it; the degree is m and does not change sign. -/
  intro x ξ hξ t ht
  change h.adjoint k x (p x (t • ξ)) = ((t ^ m : ℝ) : ℂ) • h.adjoint k x (p x ξ)
  rw [hp x ξ hξ t ht, h.adjoint_smul]
  simp

/-- Off-zero invertibility is equivalent in the two directions. -/
theorem isEllipticGlobalSymbol_symbolAdjoint_iff (p : GlobalSymbolFunction (n := n) E F) :
    IsEllipticGlobalSymbol F E (h.symbolAdjoint k p) ↔ IsEllipticGlobalSymbol E F p := by
  /- Apply bijective_adjoint_iff separately at every nonzero covector.
  The finite-rank hypothesis supplies continuity of inverse fiber maps; no
  condition at zero and no prior equality of the two ranks is imposed. -/
  constructor
  · intro hp x ξ hξ
    exact (h.bijective_adjoint_iff k x (p x ξ)).mp (hp x ξ hξ)
  · intro hp x ξ hξ
    exact (h.bijective_adjoint_iff k x (p x ξ)).mpr (hp x ξ hξ)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM

open scoped Matrix.Norms.Elementwise in
/-- Smooth explicit Gram matrices preserve every real symbol order. -/
theorem isGlobalSymbol_symbolAdjoint {m : ℝ} {p : GlobalSymbolFunction (n := n) E F}
    (hp : IsGlobalSymbol (n := n) (r := r) (q := q) E F m p) :
    IsGlobalSymbol (n := n) (r := q) (q := r) F E m (h.symbolAdjoint k p) := by
  /- In common frames the matrix is G_E⁻¹ p* G_F. Smooth invertible Gram
  matrices and all their derivatives are bounded on compact coordinate sets.
  They do not depend on frequency. Leibniz estimates preserve precisely order m. -/
  classical
  let P := EuclideanSpace ℝ (Fin n)
  intro c hc f e hf he
  let U := symbolChartDomain E F c e f
  have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
  have hswap : symbolChartDomain F E c f e = U := by
    ext z
    simp only [symbolChartDomain, U, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hswap]
  -- Each supplied metric gives a smooth invertible Gram operator in its original frame.
  let toOpE : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
  let matrixOpE : Matrix (Fin r) (Fin r) ℂ →L[ℝ]
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    LinearMap.toContinuousLinearMap (toOpE.restrictScalars ℝ)
  let GE (x : M) := matrixOpE (h.gramMatrix e x)
  have gramSmoothE : ContMDiffOn 𝓘(ℝ, P)
      𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
      GE e.baseSet := by
    apply matrixOpE.contDiff.contMDiff.comp_contMDiffOn
    apply contMDiffOn_pi_space.mpr
    intro i
    apply contMDiffOn_pi_space.mpr
    intro j
    exact h.contMDiffOn_gram e i j
  have gramInvertibleE (x : M) (hx : x ∈ e.baseSet) : (GE x).IsInvertible := by
    have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr
      (h.isUnit_det_gramMatrix e x hx)
    let L := (LinearEquiv.ofBijective (h.gramMatrix e x).mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
        Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
    let Q := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
    refine ⟨Q.trans (L.trans Q.symm), ?_⟩
    ext v i
    rfl
  have gramPairingE (x : M) (hx : x ∈ e.baseSet)
      (u v : EuclideanSpace ℂ (Fin r)) :
      inner ℂ u (GE x v) = h.pairing x (e.symmL ℂ x u) (e.symmL ℂ x v) := by
    rw [h.pairing_eq_gramMatrix e x hx]
    have hcoord (w : EuclideanSpace ℂ (Fin r)) :
        (e ⟨x, e.symmL ℂ x w⟩).2 = w := by
      rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
      exact e.continuousLinearMapAt_symmL hx w
    rw [hcoord, hcoord]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i, (∑ j, h.gramMatrix e x i j * v j) * star (u i)) = _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [starRingEnd_apply]
    ring
  have hGE : ContDiffOn ℝ ∞ (fun z ↦ GE (c.symm z)) U := by
    intro z hz
    have hbase := contMDiffAt_symm_of_mem_maximalAtlas
      (I := 𝓘(ℝ, P)) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1.1
    have hg := gramSmoothE.contMDiffAt (e.open_baseSet.mem_nhds hz.1.2)
    exact (contMDiffAt_iff_contDiffAt.mp (hg.comp z hbase)).contDiffWithinAt
  let toOpF : Matrix (Fin q) (Fin q) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
  let matrixOpF : Matrix (Fin q) (Fin q) ℂ →L[ℝ]
      (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
    LinearMap.toContinuousLinearMap (toOpF.restrictScalars ℝ)
  let GF (x : M) := matrixOpF (k.gramMatrix f x)
  have gramSmoothF : ContMDiffOn 𝓘(ℝ, P)
      𝓘(ℝ, EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
      GF f.baseSet := by
    apply matrixOpF.contDiff.contMDiff.comp_contMDiffOn
    apply contMDiffOn_pi_space.mpr
    intro i
    apply contMDiffOn_pi_space.mpr
    intro j
    exact k.contMDiffOn_gram f i j
  have gramInvertibleF (x : M) (hx : x ∈ f.baseSet) : (GF x).IsInvertible := by
    have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr
      (k.isUnit_det_gramMatrix f x hx)
    let L := (LinearEquiv.ofBijective (k.gramMatrix f x).mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
        Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
    let Q := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q ↦ ℂ)
    refine ⟨Q.trans (L.trans Q.symm), ?_⟩
    ext v i
    rfl
  have gramPairingF (x : M) (hx : x ∈ f.baseSet)
      (u v : EuclideanSpace ℂ (Fin q)) :
      inner ℂ u (GF x v) = k.pairing x (f.symmL ℂ x u) (f.symmL ℂ x v) := by
    rw [k.pairing_eq_gramMatrix f x hx]
    have hcoord (w : EuclideanSpace ℂ (Fin q)) :
        (f ⟨x, f.symmL ℂ x w⟩).2 = w := by
      rw [← f.continuousLinearMapAt_apply_of_mem ℂ hx]
      exact f.continuousLinearMapAt_symmL hx w
    rw [hcoord, hcoord]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i, (∑ j, k.gramMatrix f x i j * v j) * star (u i)) = _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [starRingEnd_apply]
    ring
  have hGF : ContDiffOn ℝ ∞ (fun z ↦ GF (c.symm z)) U := by
    intro z hz
    have hbase := contMDiffAt_symm_of_mem_maximalAtlas
      (I := 𝓘(ℝ, P)) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1.1
    have hg := gramSmoothF.contMDiffAt (f.open_baseSet.mem_nhds hz.2)
    exact (contMDiffAt_iff_contDiffAt.mp (hg.comp z hbase)).contDiffWithinAt
  have hGEinv : ContDiffOn ℝ ∞ (fun z ↦ (GE (c.symm z)).inverse) U := by
    intro z hz
    have hi := (gramInvertibleE (c.symm z) hz.1.2).contDiffAt_map_inverse (n := ∞)
    exact (hi.restrict_scalars ℝ).comp_contDiffWithinAt z (hGE z hz)
  -- Pairing with all source vectors fixes the two-sided Gram order at the same covector.
  have hformula (z η : P) (hz : z ∈ U) :
      globalSymbolInChart F E (h.symbolAdjoint k p) c f e z η =
        (GE (c.symm z)).inverse.comp
          ((globalSymbolInChart E F p c e f z η).adjoint.comp (GF (c.symm z))) := by
    let x := c.symm z
    let T := p x (covectorFromChart c x η)
    let A := globalSymbolInChart E F p c e f z η
    let B := globalSymbolInChart F E (h.symbolAdjoint k p) c f e z η
    apply ContinuousLinearMap.ext
    intro v
    have hw : GE x (B v) = A.adjoint (GF x v) := by
      apply ext_inner_left ℂ
      intro u
      rw [gramPairingE x hz.1.2, ContinuousLinearMap.adjoint_inner_right,
        gramPairingF x hz.2]
      change h.pairing x (e.symmL ℂ x u)
          (e.symmL ℂ x (e.continuousLinearMapAt ℂ x
            (h.adjoint k x T (f.symmL ℂ x v)))) =
        k.pairing x (f.symmL ℂ x
          (f.continuousLinearMapAt ℂ x (T (e.symmL ℂ x u)))) (f.symmL ℂ x v)
      rw [e.symmL_continuousLinearMapAt hz.1.2, h.pairing_adjoint,
        f.symmL_continuousLinearMapAt hz.2]
    exact ((gramInvertibleE x hz.1.2).inverse_apply_self (B v)).symm.trans
      (congrArg (GE x).inverse hw)
  -- A smooth coefficient independent of frequency is an order-zero symbol.
  have coefficientSymbol {s t : ℕ} (U : Set P) (hU : IsOpen U)
      (A : P → EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t))
      (hA : ContDiffOn ℝ ∞ A U) : IsSymbol U 0 (fun x _ ↦ A x) := by
    refine ⟨hA.comp contDiffOn_fst (fun _ hx ↦ hx.1), ?_⟩
    intro K hK hcompact i j
    cases j with
    | zero =>
      have hcont : ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ i A x‖) K := by
        intro x hx
        exact ((hA.contDiffAt (hU.mem_nhds (hK hx))).continuousAt_iteratedFDeriv
          (by simp)).norm.continuousWithinAt
      obtain ⟨C, hC⟩ := (hcompact.image_of_continuousOn hcont).bddAbove
      refine ⟨max C 0, le_max_right _ _, ?_⟩
      intro x hx ξ
      have heq : (fun y ↦ iteratedFDeriv ℝ 0 (fun _ : P ↦ A y) ξ) =
          (continuousMultilinearCurryFin0 ℝ P
            (EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t))).symm ∘ A := rfl
      change ‖iteratedFDeriv ℝ i
        (fun y ↦ iteratedFDeriv ℝ 0 (fun _ : P ↦ A y) ξ) x‖ ≤ _
      rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
      simp only [Nat.cast_zero, sub_zero, Real.rpow_zero, mul_one]
      exact (hC ⟨x, hx, rfl⟩).trans (le_max_left C 0)
    | succ j =>
      refine ⟨0, le_rfl, ?_⟩
      intro x hx ξ
      have hz : (fun y : P ↦ iteratedFDeriv ℝ (j + 1) (fun _ : P ↦ A y) ξ) = 0 := by
        funext y
        exact congrFun (iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j) (A y)) ξ
      change ‖iteratedFDeriv ℝ i
        (fun y ↦ iteratedFDeriv ℝ (j + 1) (fun _ : P ↦ A y) ξ) x‖ ≤ _
      rw [hz, iteratedFDeriv_zero]
      simp
  -- The complex adjoint is a real-linear isometry, also on every derivative target.
  have adjointSymbol {s t : ℕ} (U : Set P) (m : ℝ)
      (a : SymbolFunction n s t) (ha : IsSymbol U m a) :
      IsSymbol U m (fun x ξ ↦ (a x ξ).adjoint) := by
    let V := EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t)
    let W := EuclideanSpace ℂ (Fin t) →L[ℂ] EuclideanSpace ℂ (Fin s)
    let J : V ≃ₗᵢ[ℝ] W := {
      toEquiv := (ContinuousLinearMap.adjoint : V ≃ₗᵢ⋆[ℂ] W).toEquiv
      map_add' := map_add ContinuousLinearMap.adjoint
      map_smul' := by
        intro t A
        change (t • A).adjoint = t • A.adjoint
        rw [← Complex.coe_smul t A, map_smulₛₗ]
        simp
      norm_map' := ContinuousLinearMap.adjoint.norm_map }
    refine ⟨J.contDiff.comp_contDiffOn ha.1, ?_⟩
    intro K hK hcompact i j
    obtain ⟨C, hC, hbound⟩ := ha.2 K hK hcompact i j
    refine ⟨C, hC, ?_⟩
    intro x hx ξ
    let Jj : (P [×j]→L[ℝ] V) ≃ₗᵢ[ℝ] (P [×j]→L[ℝ] W) := {
      toLinearEquiv := (J.toContinuousLinearEquiv.continuousMultilinearMapCongrRight
        (fun _ : Fin j ↦ P)).toLinearEquiv
      norm_map' := fun f ↦ J.toLinearIsometry.norm_compContinuousMultilinearMap f }
    have heq : (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ (a y η).adjoint) ξ) =
        Jj ∘ (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) := by
      funext y
      exact J.toContinuousLinearEquiv.iteratedFDeriv_comp_left
    change ‖iteratedFDeriv ℝ i
      (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ (a y η).adjoint) ξ) x‖ ≤ _
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hbound x hx ξ
  -- Composition adds orders: the two Gram weights contribute exactly zero.
  have hweighted := (coefficientSymbol U hU _ hGEinv).symbolComp hU
    ((adjointSymbol U m _ (hp c hc e f)).symbolComp hU
      (coefficientSymbol U hU _ hGF))
  simp only [zero_add, add_zero] at hweighted
  have heq (z : P) (hz : z ∈ U) (η : P) :
      globalSymbolInChart F E (h.symbolAdjoint k p) c f e z η =
        symbolComp (fun z _ ↦ (GE (c.symm z)).inverse)
          (symbolComp (fun z η ↦ (globalSymbolInChart E F p c e f z η).adjoint)
            (fun z _ ↦ GF (c.symm z))) z η :=
    hformula z η hz
  refine ⟨hweighted.1.congr (fun z hz ↦ heq z.1 hz.1 z.2), ?_⟩
  intro K hK hcompact i j
  obtain ⟨C, hC, hbound⟩ := hweighted.2 K hK hcompact i j
  refine ⟨C, hC, ?_⟩
  intro z hz η
  -- Equality throughout the open overlap identifies the full, totalized mixed derivatives.
  have hnear : (fun y ↦ iteratedFDeriv ℝ j
      (globalSymbolInChart F E (h.symbolAdjoint k p) c f e y) η) =ᶠ[nhds z]
      (fun y ↦ iteratedFDeriv ℝ j
        (symbolComp (fun y _ ↦ (GE (c.symm y)).inverse)
          (symbolComp (fun y ξ ↦ (globalSymbolInChart E F p c e f y ξ).adjoint)
            (fun y _ ↦ GF (c.symm y))) y) η) := by
    filter_upwards [hU.mem_nhds (hK hz)] with y hy
    rw [show globalSymbolInChart F E (h.symbolAdjoint k p) c f e y =
      _ from funext (heq y hy)]
  change ‖iteratedFDeriv ℝ i _ z‖ ≤ _
  rw [(hnear.iteratedFDeriv ℝ i).eq_of_nhds]
  exact hbound z hz η

open scoped Matrix.Norms.Elementwise in
/-- Adjunction also preserves smoothness off the zero section. -/
theorem isSmoothOffZero_symbolAdjoint {p : GlobalSymbolFunction (n := n) E F}
    (hp : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F p) :
    IsSmoothOffZeroGlobalSymbol (n := n) (r := q) (q := r) F E (h.symbolAdjoint k p) := by
  /- On each off-zero coordinate domain use the weighted conjugate
  transpose formula. Matrix inversion and conjugation are real-smooth on
  the invertible locus, giving the required local smoothness predicate. -/
  classical
  let P := EuclideanSpace ℝ (Fin n)
  intro c hc f e hf he
  let U := symbolChartDomain E F c e f
  have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
  have hswap : symbolChartDomain F E c f e = U := by
    ext z
    simp only [symbolChartDomain, U, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hswap]
  -- Each supplied metric gives a smooth invertible Gram operator in its original frame.
  let toOpE : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
  let matrixOpE : Matrix (Fin r) (Fin r) ℂ →L[ℝ]
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    LinearMap.toContinuousLinearMap (toOpE.restrictScalars ℝ)
  let GE (x : M) := matrixOpE (h.gramMatrix e x)
  have gramSmoothE : ContMDiffOn 𝓘(ℝ, P)
      𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
      GE e.baseSet := by
    apply matrixOpE.contDiff.contMDiff.comp_contMDiffOn
    apply contMDiffOn_pi_space.mpr
    intro i
    apply contMDiffOn_pi_space.mpr
    intro j
    exact h.contMDiffOn_gram e i j
  have gramInvertibleE (x : M) (hx : x ∈ e.baseSet) : (GE x).IsInvertible := by
    have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr
      (h.isUnit_det_gramMatrix e x hx)
    let L := (LinearEquiv.ofBijective (h.gramMatrix e x).mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
        Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
    let Q := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
    refine ⟨Q.trans (L.trans Q.symm), ?_⟩
    ext v i
    rfl
  have gramPairingE (x : M) (hx : x ∈ e.baseSet)
      (u v : EuclideanSpace ℂ (Fin r)) :
      inner ℂ u (GE x v) = h.pairing x (e.symmL ℂ x u) (e.symmL ℂ x v) := by
    rw [h.pairing_eq_gramMatrix e x hx]
    have hcoord (w : EuclideanSpace ℂ (Fin r)) :
        (e ⟨x, e.symmL ℂ x w⟩).2 = w := by
      rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
      exact e.continuousLinearMapAt_symmL hx w
    rw [hcoord, hcoord]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i, (∑ j, h.gramMatrix e x i j * v j) * star (u i)) = _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [starRingEnd_apply]
    ring
  have hGE : ContDiffOn ℝ ∞ (fun z ↦ GE (c.symm z)) U := by
    intro z hz
    have hbase := contMDiffAt_symm_of_mem_maximalAtlas
      (I := 𝓘(ℝ, P)) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1.1
    have hg := gramSmoothE.contMDiffAt (e.open_baseSet.mem_nhds hz.1.2)
    exact (contMDiffAt_iff_contDiffAt.mp (hg.comp z hbase)).contDiffWithinAt
  let toOpF : Matrix (Fin q) (Fin q) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
  let matrixOpF : Matrix (Fin q) (Fin q) ℂ →L[ℝ]
      (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
    LinearMap.toContinuousLinearMap (toOpF.restrictScalars ℝ)
  let GF (x : M) := matrixOpF (k.gramMatrix f x)
  have gramSmoothF : ContMDiffOn 𝓘(ℝ, P)
      𝓘(ℝ, EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
      GF f.baseSet := by
    apply matrixOpF.contDiff.contMDiff.comp_contMDiffOn
    apply contMDiffOn_pi_space.mpr
    intro i
    apply contMDiffOn_pi_space.mpr
    intro j
    exact k.contMDiffOn_gram f i j
  have gramInvertibleF (x : M) (hx : x ∈ f.baseSet) : (GF x).IsInvertible := by
    have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr
      (k.isUnit_det_gramMatrix f x hx)
    let L := (LinearEquiv.ofBijective (k.gramMatrix f x).mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
        Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
    let Q := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q ↦ ℂ)
    refine ⟨Q.trans (L.trans Q.symm), ?_⟩
    ext v i
    rfl
  have gramPairingF (x : M) (hx : x ∈ f.baseSet)
      (u v : EuclideanSpace ℂ (Fin q)) :
      inner ℂ u (GF x v) = k.pairing x (f.symmL ℂ x u) (f.symmL ℂ x v) := by
    rw [k.pairing_eq_gramMatrix f x hx]
    have hcoord (w : EuclideanSpace ℂ (Fin q)) :
        (f ⟨x, f.symmL ℂ x w⟩).2 = w := by
      rw [← f.continuousLinearMapAt_apply_of_mem ℂ hx]
      exact f.continuousLinearMapAt_symmL hx w
    rw [hcoord, hcoord]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i, (∑ j, k.gramMatrix f x i j * v j) * star (u i)) = _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [starRingEnd_apply]
    ring
  have hGF : ContDiffOn ℝ ∞ (fun z ↦ GF (c.symm z)) U := by
    intro z hz
    have hbase := contMDiffAt_symm_of_mem_maximalAtlas
      (I := 𝓘(ℝ, P)) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1.1
    have hg := gramSmoothF.contMDiffAt (f.open_baseSet.mem_nhds hz.2)
    exact (contMDiffAt_iff_contDiffAt.mp (hg.comp z hbase)).contDiffWithinAt
  have hGEinv : ContDiffOn ℝ ∞ (fun z ↦ (GE (c.symm z)).inverse) U := by
    intro z hz
    have hi := (gramInvertibleE (c.symm z) hz.1.2).contDiffAt_map_inverse (n := ∞)
    exact (hi.restrict_scalars ℝ).comp_contDiffWithinAt z (hGE z hz)
  -- Pairing with all source vectors fixes the two-sided Gram order at the same covector.
  have hformula (z η : P) (hz : z ∈ U) :
      globalSymbolInChart F E (h.symbolAdjoint k p) c f e z η =
        (GE (c.symm z)).inverse.comp
          ((globalSymbolInChart E F p c e f z η).adjoint.comp (GF (c.symm z))) := by
    let x := c.symm z
    let T := p x (covectorFromChart c x η)
    let A := globalSymbolInChart E F p c e f z η
    let B := globalSymbolInChart F E (h.symbolAdjoint k p) c f e z η
    apply ContinuousLinearMap.ext
    intro v
    have hw : GE x (B v) = A.adjoint (GF x v) := by
      apply ext_inner_left ℂ
      intro u
      rw [gramPairingE x hz.1.2, ContinuousLinearMap.adjoint_inner_right,
        gramPairingF x hz.2]
      change h.pairing x (e.symmL ℂ x u)
          (e.symmL ℂ x (e.continuousLinearMapAt ℂ x
            (h.adjoint k x T (f.symmL ℂ x v)))) =
        k.pairing x (f.symmL ℂ x
          (f.continuousLinearMapAt ℂ x (T (e.symmL ℂ x u)))) (f.symmL ℂ x v)
      rw [e.symmL_continuousLinearMapAt hz.1.2, h.pairing_adjoint,
        f.symmL_continuousLinearMapAt hz.2]
    exact ((gramInvertibleE x hz.1.2).inverse_apply_self (B v)).symm.trans
      (congrArg (GE x).inverse hw)
  -- On the punctured chart domain, all three factors are jointly real-smooth.
  let J : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ≃ₗᵢ[ℝ]
      (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)) := {
    toEquiv := ContinuousLinearMap.adjoint.toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by
      intro t A
      change (t • A).adjoint = t • A.adjoint
      rw [← Complex.coe_smul t A, map_smulₛₗ]
      simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  have hleft : ContDiffOn ℝ ∞ (fun z : P × P ↦ (GE (c.symm z.1)).inverse)
      (U ×ˢ {ξ | ξ ≠ 0}) := hGEinv.comp contDiffOn_fst (fun _ hz ↦ hz.1)
  have hright : ContDiffOn ℝ ∞ (fun z : P × P ↦ GF (c.symm z.1))
      (U ×ˢ {ξ | ξ ≠ 0}) := hGF.comp contDiffOn_fst (fun _ hz ↦ hz.1)
  have hmiddle := J.contDiff.comp_contDiffOn (hp c hc e f)
  have hcompRight : ContDiff ℝ ∞
      (fun A : (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)) ×
        (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ↦ A.1.comp A.2) :=
    (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
  have hcompLeft : ContDiff ℝ ∞
      (fun A : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ×
        (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)) ↦ A.1.comp A.2) :=
    (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
  have hweighted := hcompLeft.comp_contDiffOn
    (hleft.prodMk (hcompRight.comp_contDiffOn (hmiddle.prodMk hright)))
  apply hweighted.congr
  intro z hz
  exact hformula z.1 z.2 hz.1

/-- The adjoint representative, with its separately stated order certificate. -/
def symbolSpaceAdjoint {m : ℝ}
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalSymbolSpace (n := n) (r := q) (q := r) F E m :=
  ⟨h.symbolAdjoint k p.val, h.isGlobalSymbol_symbolAdjoint k p.property⟩

/-- Lower-order differences stay lower-order under the explicit metric adjoint. -/
theorem principalSymbolClass_adjoint_congr {m : ℝ}
    (p p' : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : globalPrincipalSymbolClass E F m p = globalPrincipalSymbolClass E F m p') :
    globalPrincipalSymbolClass F E m (h.symbolSpaceAdjoint k p) =
      globalPrincipalSymbolClass F E m (h.symbolSpaceAdjoint k p') := by
  /- The source quotient equality says p-p' has order m-1. Apply order
  preservation at that order and additivity of adjunction. The target quotient
  criterion then identifies the two adjoint representatives. -/
  apply (globalPrincipalSymbolClass_eq_iff F E m _ _).mpr
  have hd := h.isGlobalSymbol_symbolAdjoint k
    ((globalPrincipalSymbolClass_eq_iff E F m p p').mp hp)
  have heq : h.symbolAdjoint k (p.val - p'.val) =
      (h.symbolSpaceAdjoint k p).val - (h.symbolSpaceAdjoint k p').val := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ p'.val, h.symbolAdjoint_add,
      h.symbolAdjoint_smul]
    simp only [map_neg, map_one, neg_one_smul, sub_eq_add_neg, symbolSpaceAdjoint]
  exact heq ▸ hd

/-- Explicit-metric adjunction on the actual principal-symbol quotient. -/
def principalSymbolAdjoint {m : ℝ} :
    GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m →
      GlobalPrincipalSymbolSpace (n := n) (r := q) (q := r) F E m :=
  Quotient.lift
    (fun p ↦ globalPrincipalSymbolClass F E m (h.symbolSpaceAdjoint k p))
    (fun p p' hp ↦ h.principalSymbolClass_adjoint_congr k p p' (Quotient.sound hp))

/-- Compute the quotient operation on any supplied representative. -/
theorem principalSymbolAdjoint_class {m : ℝ}
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    h.principalSymbolAdjoint k (globalPrincipalSymbolClass E F m p) =
      globalPrincipalSymbolClass F E m (h.symbolSpaceAdjoint k p) := by
  /- Evaluate the quotient lift on this representative. The congruence
  theorem ensures independence of all other choices without selecting a
  homogeneous principal function or a preferred full symbol. -/
  rfl

/-- The principal-class adjoint sends zero to zero. -/
theorem principalSymbolAdjoint_zero (m : ℝ) :
    h.principalSymbolAdjoint k
      (0 : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) = 0 := by
  /- Use the zero symbol as representative. Its adjoint is zero in every
  fiber, and the target linear quotient map sends that representative to zero. -/
  rw [← (globalPrincipalSymbolClass E F m).map_zero, h.principalSymbolAdjoint_class]
  have hz : h.symbolSpaceAdjoint k (0 : globalSymbolSpace E F m) = 0 := by
    apply Subtype.ext
    funext x ξ
    exact h.adjoint_zero k x
  rw [hz, map_zero]

/-- The principal-class adjoint is additive. -/
theorem principalSymbolAdjoint_add {m : ℝ}
    (p p' : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    h.principalSymbolAdjoint k (p + p') =
      h.principalSymbolAdjoint k p + h.principalSymbolAdjoint k p'  := by
  /- Lift both arguments to representatives. Fiber additivity and linearity
  of the class projections prove the formula; quotient surjectivity removes
  the choices and yields the equality for the actual principal classes. -/
  obtain ⟨p, rfl⟩ := globalPrincipalSymbolClass_surjective E F m p
  obtain ⟨p', rfl⟩ := globalPrincipalSymbolClass_surjective E F m p'
  rw [← map_add, h.principalSymbolAdjoint_class,
    h.principalSymbolAdjoint_class, h.principalSymbolAdjoint_class, ← map_add]
  apply congrArg (globalPrincipalSymbolClass F E m)
  apply Subtype.ext
  exact h.symbolAdjoint_add k p.val p'.val

/-- The principal-class adjoint conjugates scalars. -/
theorem principalSymbolAdjoint_smul {m : ℝ} (c : ℂ)
    (p : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    h.principalSymbolAdjoint k (c • p) = conj c • h.principalSymbolAdjoint k p := by
  /- Choose a representative of p and apply the conjugate-scalar formula
  before the quotient projection. Linearity of the projections leaves precisely
  conj c multiplying the target class. -/
  obtain ⟨p, rfl⟩ := globalPrincipalSymbolClass_surjective E F m p
  rw [← map_smul, h.principalSymbolAdjoint_class, h.principalSymbolAdjoint_class,
    ← map_smul]
  apply congrArg (globalPrincipalSymbolClass F E m)
  apply Subtype.ext
  exact h.symbolAdjoint_smul k c p.val

/-- The principal-class adjoint is involutive with metrics exchanged. -/
theorem principalSymbolAdjoint_adjoint {m : ℝ}
    (p : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    k.principalSymbolAdjoint h (h.principalSymbolAdjoint k p) = p := by
  /- Apply the representative formula twice and then exact double symbol
  adjunction. Projecting the recovered representative gives the original class. -/
  obtain ⟨p, rfl⟩ := globalPrincipalSymbolClass_surjective E F m p
  rw [h.principalSymbolAdjoint_class, k.principalSymbolAdjoint_class]
  apply congrArg (globalPrincipalSymbolClass E F m)
  apply Subtype.ext
  exact h.symbolAdjoint_adjoint k p.val

end SmoothHermitianMetric

end AtiyahSinger
