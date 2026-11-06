/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSpinSectionCoordinates
public import AtiyahSinger.Geometry.AtlasFrameTransition
public import AtiyahSinger.Geometry.HalfSpinConnectionGauge
public import AtiyahSinger.Geometry.LocalFrameConnection
public import AtiyahSinger.Geometry.SpinLeviCivitaCoefficients
public import AtiyahSinger.Geometry.SpinorConnectionFormula

/-!
# Clifford compatibility of the prescribed induced half-spin connections

Public module ID: M1281.

For the prescribed positive even-dimensional spin tangent bundle, the Clifford
commutator of the one-quarter bivector supplies the connection part of the
Leibniz identity. All differential comparisons use the
same lifted principal frame, original parity fibers, and actual Levi-Civita
coefficients. The connection existence theorem is not an input.

Source: Spin Geometry II.4, Proposition 4.11.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

attribute [local instance] exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original half-spin bivector has the Clifford commutator of its skew vector matrix. -/
theorem halfSpinBivector_clifford (m : ℕ) (i : ZMod 2)
    (coeff : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) (hcoeff : ∀ a b, coeff a b = -coeff b a)
    (v : EuclideanSpace ℝ (Fin (2 * m)))
    (s : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :
    let b := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
    let a := ∑ j : Fin (2 * m), ∑ k : Fin (2 * m),
      (coeff j k * inner ℝ (b j) v) • b k
    halfSpinBivector m (i + 1) coeff
        (cliffordSymbolParity (realSpinorCoordinateIsometry m v) i s) =
      cliffordSymbolParity (realSpinorCoordinateIsometry m a) i s +
        cliffordSymbolParity (realSpinorCoordinateIsometry m v) i
          (halfSpinBivector m i coeff s) := by
  classical
  dsimp only
  let V := EuclideanSpace ℝ (Fin (2 * m))
  let Q := euclideanSpinQuadraticForm (2 * m)
  let C := Module.End ℂ (ComplexSpinor m)
  let b := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
  let L := (realSpinorRepresentation m).comp (euclideanSpinCliffordEvenEquiv m).toAlgHom
  let c : V →ₗ[ℝ] C := L.toLinearMap.comp (CliffordAlgebra.ι Q)
  let q : C := (1 / 4 : ℝ) • ∑ j : Fin (2 * m), ∑ k : Fin (2 * m),
    coeff j k • (c (b j) * c (b k))
  let a := ∑ j : Fin (2 * m), ∑ k : Fin (2 * m),
    (coeff j k * inner ℝ (b j) v) • b k
  have hc (w : V) : c w = cliffordSymbol (realSpinorCoordinateIsometry m w) := by
    change realSpinorRepresentation m
      (euclideanSpinCliffordEvenEquiv m (CliffordAlgebra.ι Q w)) = _
    rw [show euclideanSpinCliffordEvenEquiv m (CliffordAlgebra.ι Q w) =
      CliffordAlgebra.ι (realSpinorQuadraticForm m) (realSpinorCoordinateIsometry m w) from
        CliffordAlgebra.map_apply_ι _ w, realSpinorRepresentation_ι]
  have hq (j : ZMod 2)
      (t : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) j) :
      q t.val = (halfSpinBivector m j coeff t).val := by
    rw [halfSpinBivector_apply]
    simp only [q, C, b, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply, hc]
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, Complex.coe_smul]
    simp only [Complex.coe_smul]
  -- The negative quadratic form fixes both signs in the triple Clifford commutator.
  have hpolar (u w : V) : QuadraticMap.polar Q u w = -2 * inner ℝ u w := by
    change QuadraticMap.polar (-⇑(LinearMap.BilinMap.toQuadraticMap (innerₗ V))) u w = _
    rw [QuadraticMap.polar_neg, LinearMap.BilinMap.polar_toQuadraticMap]
    change -(inner ℝ u w + inner ℝ w u) = _
    rw [real_inner_comm w u]
    ring
  have hpair (u w : V) : c u * c w + c w * c u = (-2 * inner ℝ u w) • (1 : C) := by
    have hraw : CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q w +
        CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q u =
          algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q u w) := by
      rw [CliffordAlgebra.ι_mul_ι_add_swap]
    rw [hpolar, Algebra.algebraMap_eq_smul_one] at hraw
    have h := congrArg L hraw
    simpa only [c, C, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      map_add, map_mul, map_smul, map_one] using h
  have htriple (j k : Fin (2 * m)) :
      (c (b j) * c (b k)) * c v - c v * (c (b j) * c (b k)) =
        (2 * inner ℝ (b j) v) • c (b k) - (2 * inner ℝ (b k) v) • c (b j) := by
    calc
      _ = c (b j) * (c (b k) * c v + c v * c (b k)) -
          (c (b j) * c v + c v * c (b j)) * c (b k) := by noncomm_ring
      _ = _ := by
        rw [hpair, hpair, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
        module
  let z : C := ∑ j : Fin (2 * m), ∑ k : Fin (2 * m),
    (coeff j k * inner ℝ (b j) v) • c (b k)
  have hleft : (∑ j : Fin (2 * m), ∑ k : Fin (2 * m),
      coeff j k • ((2 * inner ℝ (b j) v) • c (b k))) = (2 : ℝ) • z := by
    simp only [z, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    module
  have hright : (∑ j : Fin (2 * m), ∑ k : Fin (2 * m),
      coeff j k • ((2 * inner ℝ (b k) v) • c (b j))) = -(2 : ℝ) • z := by
    rw [Finset.sum_comm]
    simp only [z, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hcoeff k j]
    module
  have hcomm : q * c v - c v * q = c a := by
    let D : C →ₗ[ℝ] C := (LinearMap.mul ℝ C).flip (c v) - LinearMap.mul ℝ C (c v)
    have hD (j k : Fin (2 * m)) : D (c (b j) * c (b k)) =
        (2 * inner ℝ (b j) v) • c (b k) - (2 * inner ℝ (b k) v) • c (b j) := htriple j k
    change D q = c a
    simp only [q, map_smul, map_sum, hD, smul_sub, Finset.sum_sub_distrib]
    rw [hleft, hright]
    have hz : z = c a := by simp only [z, a, map_sum, map_smul]
    rw [← hz]
    module
  -- Apply the endomorphism identity and retain the original opposite-parity certificate.
  have h := congrArg (fun T : C ↦ T s.val) hcomm
  change q (c v s.val) - c v (q s.val) = c a s.val at h
  rw [hc, hc] at h
  have hqv := hq (i + 1) (cliffordSymbolParity (realSpinorCoordinateIsometry m v) i s)
  have hqs := hq i s
  apply Subtype.ext
  change (halfSpinBivector m (i + 1) coeff
      (cliffordSymbolParity (realSpinorCoordinateIsometry m v) i s)).val =
    cliffordSymbol (realSpinorCoordinateIsometry m a) s.val +
      cliffordSymbol (realSpinorCoordinateIsometry m v) (halfSpinBivector m i coeff s).val
  rw [← hqv, ← hqs]
  exact sub_eq_iff_eq_add.mp h

-- The fixed bilinear model is used both for section smoothness and for the product rule.
private def spinCliffordModel (m : ℕ) (i : ZMod 2) :
    EuclideanSpace ℝ (Fin (2 * m)) →L[ℝ]
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i →L[ℂ]
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) (i + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦
        (cliffordSymbolParity (realSpinorCoordinateIsometry m v) i).toContinuousLinearMap
      map_add' := by
        intro v w
        apply ContinuousLinearMap.ext
        intro u
        apply Subtype.ext
        change cliffordSymbol (realSpinorCoordinateIsometry m (v + w)) u.val =
          cliffordSymbol (realSpinorCoordinateIsometry m v) u.val +
            cliffordSymbol (realSpinorCoordinateIsometry m w) u.val
        simp only [map_add, cliffordSymbol, exteriorMultiplication, contraction,
          LinearMap.add_apply, LinearMap.sub_apply]
        abel
      map_smul' := by
        intro t v
        apply ContinuousLinearMap.ext
        intro u
        apply Subtype.ext
        change cliffordSymbol (realSpinorCoordinateIsometry m (t • v)) u.val =
          t • cliffordSymbol (realSpinorCoordinateIsometry m v) u.val
        rw [map_smul]
        have hscalar : t • realSpinorCoordinateIsometry m v =
            (t : ℂ) • realSpinorCoordinateIsometry m v := by simp
        rw [hscalar]
        simp only [cliffordSymbol, exteriorMultiplication, contraction, map_smul,
          map_smulₛₗ, Complex.conj_ofReal, LinearMap.smul_apply, LinearMap.sub_apply]
        simp only [Complex.coe_smul]
        exact (smul_sub t _ _).symm }

section Derivative

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

private theorem spinMvfderiv_linear (L : E →L[ℝ] F)
    (f : M → E) (x : M) (hf : MDifferentiableAt I 𝓘(ℝ, E) f x)
    (X : TangentSpace I x) :
    mvfderiv I (fun y ↦ L (f y)) x X = L (mvfderiv I f x X) := by
  have h := mvfderiv_comp_apply («I» := 𝓘(ℝ, E)) (I' := I) x
    L.mdifferentiableAt hf X
  rw [mvfderiv_eq_fderiv, L.fderiv] at h
  exact h


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The native manifold derivative obeys the product rule for a fixed real bilinear map. -/
theorem mvfderiv_bilinear (L : E →L[ℝ] F →L[ℝ] G)
    (f : M → E) (g : M → F) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, E) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ, F) g x) (X : TangentSpace I x) :
    mvfderiv I (fun y ↦ L (f y) (g y)) x X =
      L (f x) (mvfderiv I g x X) + L (mvfderiv I f x X) (g x) := by
  have h := mvfderiv_comp_apply («I» := 𝓘(ℝ, E × F)) (I' := I) x
    ((L.isBoundedBilinearMap.differentiableAt (f x, g x)).mdifferentiableAt)
    (hf.prodMk_space hg) X
  rw [mvfderiv_eq_fderiv, L.isBoundedBilinearMap.fderiv] at h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    IsBoundedBilinearMap.deriv_apply] at h
  change mvfderiv I (fun y ↦ L (f y) (g y)) x X =
    L (f x) (mvfderiv I (fun y ↦ (f y, g y)) x X).2 +
      L (mvfderiv I (fun y ↦ (f y, g y)) x X).1 (g x) at h
  have hfst := spinMvfderiv_linear (ContinuousLinearMap.fst ℝ E F)
    (fun y ↦ (f y, g y)) x (hf.prodMk_space hg) X
  have hsnd := spinMvfderiv_linear (ContinuousLinearMap.snd ℝ E F)
    (fun y ↦ (f y, g y)) x (hf.prodMk_space hg) X
  change mvfderiv I f x X = (mvfderiv I (fun y ↦ (f y, g y)) x X).1 at hfst
  change mvfderiv I g x X = (mvfderiv I (fun y ↦ (f y, g y)) x X).2 at hsnd
  rw [← hfst, ← hsnd] at h
  exact h



private theorem spinCoordinates_equation_iff {m : ℕ} (i : ZMod 2)
    (c : ComplexSpinor m ≃ₗ[ℂ] (Finset (Fin m) → ℂ))
    (q : M → CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i)
    (x : M) (hq : MDifferentiableAt I
      𝓘(ℝ, CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) q x)
    (X : TangentSpace I x)
    (s b : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :
    (c s.val = mvfderiv I (fun y ↦ c (q y).val) x X + c b.val) ↔
      s = mvfderiv I q x X + b := by
  let Jc := c.toContinuousLinearMap.comp
    (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i).subtypeL
  let J := Jc.restrictScalars ℝ
  have hJ : Function.Injective J := by
    intro a b h
    exact Subtype.ext (c.injective h)
  have hd := spinMvfderiv_linear J q x hq X
  change (J s = mvfderiv I (fun y ↦ J (q y)) x X + J b) ↔ _
  rw [hd, ← map_add]
  exact hJ.eq_iff

end Derivative

section AssociatedSmooth

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

variable {n m : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : ContRepresentation ℂ (spinGroup (realSpinorQuadraticForm m)) W)
  (A : SmoothSpinPrincipalAtlas m 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) projection)
  (H : SmoothComplexBundleAtlas (n := n) (AssociatedVectorFiber hP ρ))

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem spinIsSmoothSection_of_coordinates
    (hH : A.IsAssociatedVectorAtlas hP ρ H)
    (σ : ∀ x : M, AssociatedVectorFiber hP ρ x)
    (hσ : ∀ b : M, ContMDiffOn I 𝓘(ℝ, W) ∞
      (associatedSpinSectionCoordinates hP ρ A b σ) (A.trivialization b).baseSet) :
    H.IsSmoothSection σ := by
  classical
  let F (j : H.Index) := EuclideanSpace ℂ (Fin (H.rank j))
  let ec (j : H.Index) := EuclideanSpace.equiv (Fin (H.rank j)) ℂ
  -- Actual atlas transitions transport smooth model coordinates to every target chart.
  have hT (j k : H.Index) :
      ContMDiffOn I 𝓘(ℝ, F j →L[ℂ] F k) ∞ (H.coordChangeL j k)
        ((H.chart j).baseSet ∩ (H.chart k).baseSet) := by
    apply contMDiffOn_finsetSum
    intro a _
    have hc := ((ec k).symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
      |>.comp_contMDiffOn (H.contMDiffOn_coordChange j k a)
    let L := (ContinuousLinearMap.smulRightL ℂ (F j) (F k)
      ((ContinuousLinearMap.proj a).comp (ec j).toContinuousLinearMap)).restrictScalars ℝ
    exact L.contMDiff.comp_contMDiffOn hc
  -- A principal chart through the point supplies a covering associated frame.
  intro j x hx
  let b := x
  have hb : x ∈ (A.trivialization b).baseSet := A.mem_baseSet x
  obtain ⟨k, c, hbase, hchart⟩ :=
    hH b
  let q := associatedSpinSectionCoordinates hP ρ A b σ
  have hcoord (y : M) (hy : y ∈ (A.trivialization b).baseSet) :
      (H.chart k ⟨y, σ y⟩).2 = c (q y) := by
    let E := associatedVectorFiberMkLinearEquiv hP ρ
      ((A.trivialization b).toPartialEquiv.symm (y, 1))
      ((A.trivialization b).proj_symm_apply' hy)
    have h := hchart ((A.trivialization b).toPartialEquiv.symm (y, 1)) y
      ((A.trivialization b).proj_symm_apply' hy) hy (E.symm (σ y))
    change (H.chart k ⟨y, E (E.symm (σ y))⟩).2 = _ at h
    rw [E.apply_symm_apply] at h
    have hunit : (A.trivialization b)
        ((A.trivialization b).toPartialEquiv.symm (y, 1)) = (y, 1) :=
      (A.trivialization b).apply_symm_apply' hy
    rw [hunit] at h
    simp only [map_one, one_apply_eq_self] at h
    simp only [q, associatedSpinSectionCoordinates, dite_eq_left hy]
    exact h
  have hqs := (hσ b).contMDiffAt ((A.trivialization b).open_baseSet.mem_nhds hb)
  have hcs := (c.toContinuousLinearMap.restrictScalars ℝ).contMDiff.contMDiffAt.comp x hqs
  have hinput := ((ec k).symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
    |>.contMDiffAt.comp x hcs
  have htrans := (hT k j).contMDiffAt
    (((H.chart k).open_baseSet.inter (H.chart j).open_baseSet).mem_nhds
      ⟨hbase.symm ▸ hb, hx⟩)
  have hprod := ((ContinuousLinearMap.restrictScalarsL ℂ (F k) (F j) ℝ ℝ).contMDiff
    |>.contMDiffAt.comp x htrans).clm_apply hinput
  have hout := ((ec j).toContinuousLinearMap.restrictScalars ℝ).contMDiff
    |>.contMDiffAt.comp x hprod
  apply ContMDiffAt.contMDiffWithinAt
  apply hout.congr_of_eventuallyEq
  filter_upwards [(A.trivialization b).open_baseSet.mem_nhds hb,
    (H.chart j).open_baseSet.mem_nhds hx] with y hy hyj
  change (H.chart j ⟨y, σ y⟩).2 = ec j (H.coordChangeL k j y ((ec k).symm (c (q y))))
  rw [← hcoord y hy]
  have h := H.coordChangeL_apply k j y ⟨hbase.symm ▸ hy, hyj⟩ (σ y)
  simpa only [ec, ContinuousLinearEquiv.apply_symm_apply] using congrArg (ec j) h

end AssociatedSmooth

section LiftedCoordinates

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology associatedVectorFiberAddCommGroup
  associatedVectorFiberModule associatedVectorTotalTopology

set_option maxSynthPendingDepth 50

variable {m : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [RiemannianBundle
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) : M → Type _)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m)))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) : M → Type _)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞
    (EuclideanSpace ℝ (Fin (2 * m)))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) : M → Type _)]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
  {hm : 0 < m} {o : ∀ x : M,
    Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) x) (Fin (2 * m))}

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))
local notation "TM" => TangentSpace I (M := M)
local notation "V" => EuclideanSpace ℝ (Fin (2 * m))

private def spinTangentCoordinates (S : TopologicalSpinStructure m (TM) o hm hP)
    (b : M) (Y : ∀ y : M, TM y) (x : M) : V :=
  (EuclideanSpace.equiv (Fin (2 * m)) ℝ).symm
    (fun a ↦ inner ℝ (S.liftedFrameField (n := 2 * m) b a x) (Y x))

private theorem spinTangentCoordinates_smooth
    (S : TopologicalSpinStructure m (TM) o hm hP) (b : M)
    (Y : ∀ y : M, TM y)
    (hY : ContMDiff I (I).tangent ∞ (fun y ↦ (⟨y, Y y⟩ : TangentBundle I M))) :
    ContMDiffOn I 𝓘(ℝ, V) ∞ (spinTangentCoordinates S b Y)
      ((S.smoothPrincipalAtlas I).trivialization b).baseSet := by
  apply (EuclideanSpace.equiv (Fin (2 * m)) ℝ).symm.toContinuousLinearMap.contMDiff
    |>.comp_contMDiffOn
  apply contMDiffOn_pi_space.mpr
  intro a
  exact ((S.isLocalFrameOn_liftedFrameField (n := 2 * m) b).contMDiffOn a).inner_bundle
    hY.contMDiffOn

private theorem spinTangentCoordinates_eq
    (S : TopologicalSpinStructure m (TM) o hm hP) (b x : M)
    (hx : x ∈ ((S.smoothPrincipalAtlas I).trivialization b).baseSet)
    (Y : ∀ y : M, TM y) :
    spinTangentCoordinates S b Y x =
      (S.frame (((S.smoothPrincipalAtlas I).trivialization b).toPartialEquiv.symm (x, 1))
        x (((S.smoothPrincipalAtlas I).trivialization b).proj_symm_apply' hx)).symm (Y x) := by
  let t := (S.smoothPrincipalAtlas I).trivialization b
  let f := S.frame (t.toPartialEquiv.symm (x, 1)) x (t.proj_symm_apply' hx)
  let B := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
  apply (EuclideanSpace.equiv (Fin (2 * m)) ℝ).injective
  funext a
  change inner ℝ (S.liftedFrameField (n := 2 * m) b a x) (Y x) = (f.symm (Y x)) a
  have hfield : S.liftedFrameField (n := 2 * m) b a x = f (B a) := by
    simp only [TopologicalSpinStructure.liftedFrameField, dite_eq_left hx]
    rfl
  rw [hfield]
  calc
    inner ℝ (f (B a)) (Y x) = inner ℝ (f (B a)) (f (f.symm (Y x))) := by
      rw [f.apply_symm_apply]
    _ = inner ℝ (B a) (f.symm (Y x)) := f.inner_map_map _ _
    _ = _ := EuclideanSpace.basisFun_inner (Fin (2 * m)) ℝ (f.symm (Y x)) a

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem spinTangentCoordinates_leviCivita
    (S : TopologicalSpinStructure m (TM) o hm hP) (b x : M)
    (hx : x ∈ ((S.smoothPrincipalAtlas I).trivialization b).baseSet)
    (Y : ∀ y : M, TM y)
    (hY : ContMDiff I (I).tangent ∞ (fun y ↦ (⟨y, Y y⟩ : TangentBundle I M)))
    (X : TM x) :
    (S.frame (((S.smoothPrincipalAtlas I).trivialization b).toPartialEquiv.symm (x, 1))
        x (((S.smoothPrincipalAtlas I).trivialization b).proj_symm_apply' hx)).symm
      (CovariantDerivative.leviCivitaConnection I M Y x X) =
      mvfderiv I (spinTangentCoordinates S b Y) x X +
        ∑ a : Fin (2 * m), ∑ k : Fin (2 * m),
          (S.liftedLeviCivitaCoefficients b x X a k *
            inner ℝ (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a)
              (spinTangentCoordinates S b Y x)) •
            EuclideanSpace.basisFun (Fin (2 * m)) ℝ k := by
  classical
  let t := (S.smoothPrincipalAtlas I).trivialization b
  let s := S.liftedFrameField (n := 2 * m) b
  let hs := S.isLocalFrameOn_liftedFrameField (n := 2 * m) b
  let w := spinTangentCoordinates S b Y
  have hw : ContMDiffAt I 𝓘(ℝ, V) ∞ w x :=
    (spinTangentCoordinates_smooth S b Y hY).contMDiffAt (t.open_baseSet.mem_nhds hx)
  have hcoord (a : Fin (2 * m)) : (fun y ↦ hs.coeff a y (Y y)) =ᶠ[nhds x]
      (fun y ↦ w y a) := by
    filter_upwards [t.open_baseSet.mem_nhds hx] with y hy
    exact S.liftedFrameField_coeff b y hy a (Y y)
  have hc (a : Fin (2 * m)) : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y ↦ hs.coeff a y (Y y)) x :=
    ((EuclideanSpace.proj a : V →L[ℝ] ℝ).contMDiff.contMDiffAt.comp x hw).mdifferentiableAt
      (by simp) |>.congr_of_eventuallyEq (hcoord a)
  have hd (a : Fin (2 * m)) :
      mvfderiv I (fun y ↦ hs.coeff a y (Y y)) x X =
        (mvfderiv I w x X) a := by
    unfold mvfderiv
    rw [(hcoord a).mfderiv_eq]
    exact spinMvfderiv_linear (EuclideanSpace.proj a) w x
      (hw.mdifferentiableAt (by simp)) X
  -- Differentiate the genuine local frame expansion of the specified tangent field.
  have h := tangentCovariantDerivative_eq_sum_localFrame
    (CovariantDerivative.leviCivitaConnection I M) s t.baseSet t.open_baseSet hs Y x hx
    (hY x |>.mdifferentiableAt (by simp)) hc X
  apply (EuclideanSpace.equiv (Fin (2 * m)) ℝ).injective
  funext k
  have hread := congrArg (hs.coeff k x) h
  rw [map_sum] at hread
  simp only [map_add, map_smul, smul_eq_mul, Finset.sum_add_distrib, hd] at hread
  have hb (a : Fin (2 * m)) : hs.coeff k x (s a x) = if a = k then 1 else 0 := by
    rw [hs.coeff_apply_of_mem hx (s a) k]
    have hvec : s a x = hs.toBasisAt hx a := (hs.toBasisAt_coe hx a).symm
    rw [hvec, (hs.toBasisAt hx).repr_self]
    simp [Finsupp.single_apply, eq_comm]
  simp only [hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at hread
  have hcoeff (a : Fin (2 * m)) :
      hs.coeff k x (CovariantDerivative.leviCivitaConnection I M (s a) x X) =
        S.liftedLeviCivitaCoefficients b x X a k := by
    rw [S.liftedFrameField_coeff b x hx]
    exact real_inner_comm _ _
  rw [S.liftedFrameField_coeff b x hx] at hread
  simp only [hcoeff, (hcoord _).eq_of_nhds] at hread
  let f := S.frame (t.toPartialEquiv.symm (x, 1)) x (t.proj_symm_apply' hx)
  have hfield : s k x = f (EuclideanSpace.basisFun (Fin (2 * m)) ℝ k) := by
    simp only [s, TopologicalSpinStructure.liftedFrameField, dite_eq_left hx]
    rfl
  change (f.symm (CovariantDerivative.leviCivitaConnection I M Y x X)) k = _
  rw [← EuclideanSpace.basisFun_inner (Fin (2 * m)) ℝ _ k,
    ← f.inner_map_map, f.apply_symm_apply, ← hfield, hread]
  change (∑ a : Fin (2 * m), w x a * S.liftedLeviCivitaCoefficients b x X a k) +
      (mvfderiv I w x X) k =
    (mvfderiv I w x X) k +
      (EuclideanSpace.proj k : V →L[ℝ] ℝ)
        (∑ a : Fin (2 * m), ∑ j : Fin (2 * m),
        (S.liftedLeviCivitaCoefficients b x X a j *
          inner ℝ (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a) (w x)) •
            EuclideanSpace.basisFun (Fin (2 * m)) ℝ j)
  have hval (j : Fin (2 * m)) :
      (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j) k = if j = k then 1 else 0 := by
    simp [EuclideanSpace.basisFun_apply, eq_comm]
  simp only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_inner]
  change _ = _ + ∑ a : Fin (2 * m), ∑ j : Fin (2 * m),
    (S.liftedLeviCivitaCoefficients b x X a j * w x a) *
      (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j) k
  simp only [hval, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _


private theorem spinClifford_coordinates
    (S : TopologicalSpinStructure m (TM) o hm hP) (b x : M)
    (hx : x ∈ ((S.smoothPrincipalAtlas I).trivialization b).baseSet)
    (i : ZMod 2) (Y : TM x) (s : HalfSpinorBundle m hP i x) :
    let t := (S.smoothPrincipalAtlas I).trivialization b
    let p := t.toPartialEquiv.symm (x, 1)
    let hp : projection p = x := t.proj_symm_apply' hx
    (associatedVectorFiberMkLinearEquiv hP
      (complexSpinParityContRepresentation m (i + 1)) p hp).symm
        (S.cliffordParity x Y i s) =
      spinCliffordModel m i ((S.frame p x hp).symm Y)
        ((associatedVectorFiberMkLinearEquiv hP
          (complexSpinParityContRepresentation m i) p hp).symm s) := by
  let t := (S.smoothPrincipalAtlas I).trivialization b
  let p := t.toPartialEquiv.symm (x, 1)
  let hp : projection p = x := t.proj_symm_apply' hx
  let E (j : ZMod 2) :=
    associatedVectorFiberMkLinearEquiv hP (complexSpinParityContRepresentation m j) p hp
  have h := S.cliffordParity_apply_mk p x hp Y i ((E i).symm s)
  change S.cliffordParity x Y i (E i ((E i).symm s)) =
    E (i + 1) (spinCliffordModel m i ((S.frame p x hp).symm Y) ((E i).symm s)) at h
  rw [(E i).apply_symm_apply] at h
  change (E (i + 1)).symm (S.cliffordParity x Y i s) = _
  rw [h, (E (i + 1)).symm_apply_apply]


private theorem spinCliffordSection_coordinates
    (S : TopologicalSpinStructure m (TM) o hm hP) (i : ZMod 2) (b x : M)
    (hx : x ∈ ((S.smoothPrincipalAtlas I).trivialization b).baseSet)
    (Y : ∀ y : M, TM y) (σ : ∀ y : M, HalfSpinorBundle m hP i y) :
    associatedSpinSectionCoordinates hP (complexSpinParityContRepresentation m (i + 1))
      (S.smoothPrincipalAtlas I) b (fun y ↦ S.cliffordParity y (Y y) i (σ y)) x =
    spinCliffordModel m i (spinTangentCoordinates S b Y x)
      (associatedSpinSectionCoordinates hP (complexSpinParityContRepresentation m i)
        (S.smoothPrincipalAtlas I) b σ x) := by
  simp only [associatedSpinSectionCoordinates, dite_eq_left hx]
  have h := spinClifford_coordinates S b x hx i (Y x) (σ x)
  refine h.trans ?_
  exact congrArg (fun z : V ↦ spinCliffordModel m i z
    ((associatedVectorFiberMkLinearEquiv hP (complexSpinParityContRepresentation m i)
      (((S.smoothPrincipalAtlas I).trivialization b).toPartialEquiv.symm (x, 1))
      (((S.smoothPrincipalAtlas I).trivialization b).proj_symm_apply' hx)).symm (σ x)))
    (spinTangentCoordinates_eq S b x hx Y).symm

private theorem spinCliffordSection_isSmooth
    (S : TopologicalSpinStructure m (TM) o hm hP) (i : ZMod 2)
    (Y : ∀ y : M, TM y)
    (hY : ContMDiff I (I).tangent ∞ (fun y ↦ (⟨y, Y y⟩ : TangentBundle I M)))
    (u : (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I) i).smoothSections) :
    (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I) (i + 1)).IsSmoothSection
      (fun y ↦ S.cliffordParity y (Y y) i (u.val y)) := by
  let A := S.smoothPrincipalAtlas I
  let H := halfSpinorBundleSmoothAtlas m hP A
  let W (j : ZMod 2) : Type _ :=
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) j
  let L : V →L[ℝ] W i →L[ℝ] W (i + 1) :=
    (ContinuousLinearMap.restrictScalarsL ℂ (W i) (W (i + 1)) ℝ ℝ).comp
      (spinCliffordModel m i)
  apply spinIsSmoothSection_of_coordinates hP
    (complexSpinParityContRepresentation m (i + 1)) A (H (i + 1))
    ((spinorBundleSmoothAtlases_compatibility m hP A).2.1 (i + 1))
  intro b
  have hq := contMDiffOn_associatedSpinSectionCoordinates hP
    (complexSpinParityContRepresentation m i) A (H i)
    ((spinorBundleSmoothAtlases_compatibility m hP A).2.1 i) b u
  have hw := spinTangentCoordinates_smooth S b Y hY
  have hprod := (L.contMDiff.comp_contMDiffOn hw).clm_apply hq
  exact hprod.congr (fun y hy ↦ spinCliffordSection_coordinates S i b y hy Y u.val)

end LiftedCoordinates



section InducedFormula

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology associatedVectorFiberAddCommGroup
  associatedVectorFiberModule associatedVectorTotalTopology

set_option maxSynthPendingDepth 50

variable {m : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
  {hm : 0 < m} {o : ∀ x : M,
    Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) x) (Fin (2 * m))}

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))
local notation "TM" => (TangentSpace I : M → Type _)
local notation "V" => EuclideanSpace ℝ (Fin (2 * m))

namespace TopologicalSpinStructure

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original full-exterior formula is derivative-plus-bivector in parity coordinates. -/
theorem isInducedHalfSpinorConnection_iff_coordinates
    (g : SmoothTangentMetric (n := 2 * m) (M := M)) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle V TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ V TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    ∀ (S : TopologicalSpinStructure m TM o hm hP) (i : ZMod 2)
      (cov : AtlasComplexConnection
        (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I) i)),
      S.IsInducedHalfSpinorConnection g i cov ↔
      ∀ (b x : M) (hx : x ∈ ((S.smoothPrincipalAtlas I).trivialization b).baseSet)
        (u : (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I) i).smoothSections)
        (X : TangentSpace I x),
        let A := S.smoothPrincipalAtlas I
        let q := associatedSpinSectionCoordinates hP (complexSpinParityContRepresentation m i)
          A b u.val
        (associatedVectorFiberMkLinearEquiv hP (complexSpinParityContRepresentation m i)
          ((A.trivialization b).toPartialEquiv.symm (x, 1))
          ((A.trivialization b).proj_symm_apply' hx)).symm
            (cov.covariantDerivative u x X) =
          mvfderiv I q x X + halfSpinBivector m i (S.liftedLeviCivitaCoefficients b x X) (q x) := by
  classical
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle V TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ V TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S i cov
  apply forall_congr'
  intro b
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  apply forall_congr'
  intro u
  apply forall_congr'
  intro X
  let A := S.smoothPrincipalAtlas I
  let H := halfSpinorBundleSmoothAtlas m hP A i
  let W : Type _ := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i
  let c := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra.equivFun
  let q := associatedSpinSectionCoordinates hP (complexSpinParityContRepresentation m i)
    A b u.val
  have hq : MDifferentiableAt I 𝓘(ℝ, W) q x :=
    ((contMDiffOn_associatedSpinSectionCoordinates hP
      (complexSpinParityContRepresentation m i) A H
      ((spinorBundleSmoothAtlases_compatibility m hP A).2.1 i) b u).contMDiffAt
      ((A.trivialization b).open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  let coordinates : M → (Finset (Fin m) → ℂ) := fun y ↦
    if hy : y ∈ (A.trivialization b).baseSet then
      c (((associatedVectorFiberMkLinearEquiv hP (complexSpinParityContRepresentation m i)
        ((A.trivialization b).toPartialEquiv.symm (y, 1))
        ((A.trivialization b).proj_symm_apply' hy)).symm (u.val y)).val) else 0
  -- The fixed exterior-coordinate map factors through the original parity coordinates.
  have hcoordinates : coordinates = fun y ↦ c (q y).val := by
    funext y
    by_cases hy : y ∈ (A.trivialization b).baseSet
    · simp only [coordinates, q, associatedSpinSectionCoordinates, dite_eq_left hy]
    · simp only [coordinates, q, associatedSpinSectionCoordinates, dite_eq_right hy,
        Submodule.coe_zero, map_zero]
  let value := (associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m i)
    ((A.trivialization b).toPartialEquiv.symm (x, 1))
    ((A.trivialization b).proj_symm_apply' hx)).symm (cov.covariantDerivative u x X)
  let act (z : ComplexSpinor m) : Finset (Fin m) → ℂ :=
    c ((1 / 4 : ℂ) • ∑ a : Fin (2 * m), ∑ k : Fin (2 * m),
      (g.inner x (CovariantDerivative.leviCivitaConnection I M
        (S.liftedFrameField (n := 2 * m) b a) x X)
        (S.liftedFrameField (n := 2 * m) b k x) : ℂ) •
          cliffordSymbol
            (realSpinorCoordinateIsometry m (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a))
            (cliffordSymbol
              (realSpinorCoordinateIsometry m (EuclideanSpace.basisFun (Fin (2 * m)) ℝ k)) z))
  change (c value.val = mvfderiv I coordinates x X + act (c.symm (coordinates x))) ↔
    value = mvfderiv I q x X +
      halfSpinBivector m i (S.liftedLeviCivitaCoefficients b x X) (q x)
  rw [hcoordinates, c.symm_apply_apply]
  have hact : act (q x).val =
      c (halfSpinBivector m i (S.liftedLeviCivitaCoefficients b x X) (q x)).val := by
    rw [halfSpinBivector_apply]
    rfl
  rw [hact]
  exact spinCoordinates_equation_iff i c q x hq X _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 1000000 in
-- Both parity connections use the same lifted frame and tangent metric in the Leibniz identity.
/-- Any two connections with the original induced formulas satisfy Clifford Leibniz. -/
theorem inducedHalfSpinorConnections_clifford
    (g : SmoothTangentMetric (n := 2 * m) (M := M)) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle V TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ V TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    ∀ (S : TopologicalSpinStructure m TM o hm hP) (i : ZMod 2)
      (cov₀ : AtlasComplexConnection
        (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I) i))
      (cov₁ : AtlasComplexConnection
        (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I) (i + 1))),
      S.IsInducedHalfSpinorConnection g i cov₀ →
      S.IsInducedHalfSpinorConnection g (i + 1) cov₁ →
      ∀ (Y : ∀ y : M, TangentSpace I y)
        (_hY : ContMDiff I (I).tangent ∞ (fun y ↦ (⟨y, Y y⟩ : TangentBundle I M)))
        (u : (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I) i).smoothSections),
        ∃ v : (halfSpinorBundleSmoothAtlas m hP
          (S.smoothPrincipalAtlas I) (i + 1)).smoothSections,
          (∀ x : M, v.val x = S.cliffordParity x (Y x) i (u.val x)) ∧
            ∀ (x : M) (X : TangentSpace I x),
              cov₁.covariantDerivative v x X =
                S.cliffordParity x (CovariantDerivative.leviCivitaConnection I M Y x X)
                  i (u.val x) +
                S.cliffordParity x (Y x) i (cov₀.covariantDerivative u x X) := by
  classical
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle V TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ V TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S i cov₀ cov₁ hc₀ hc₁ Y hY u
  let A := S.smoothPrincipalAtlas I
  let H := halfSpinorBundleSmoothAtlas m hP A
  let W (j : ZMod 2) : Type _ :=
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) j
  let q (j : ZMod 2) (σ : ∀ x : M, HalfSpinorBundle m hP j x) (b : M) : M → W j :=
    associatedSpinSectionCoordinates hP (complexSpinParityContRepresentation m j) A b σ
  let w (b : M) := spinTangentCoordinates S b Y
  let L : V →L[ℝ] W i →L[ℝ] W (i + 1) :=
    (ContinuousLinearMap.restrictScalarsL ℂ (W i) (W (i + 1)) ℝ ℝ).comp
      (spinCliffordModel m i)
  let σ (x : M) : HalfSpinorBundle m hP (i + 1) x :=
    S.cliffordParity x (Y x) i (u.val x)
  -- On each original unit-section chart the quotient action is the same bilinear model.
  have haction (b x : M) (hx : x ∈ (A.trivialization b).baseSet) :
      q (i + 1) σ b x = L (w b x) (q i u.val b x) := by
    exact spinCliffordSection_coordinates S i b x hx Y u.val
  have hqu (b : M) : ContMDiffOn I 𝓘(ℝ, W i) ∞ (q i u.val b)
      (A.trivialization b).baseSet :=
    contMDiffOn_associatedSpinSectionCoordinates hP
      (complexSpinParityContRepresentation m i) A (H i)
      ((spinorBundleSmoothAtlases_compatibility m hP A).2.1 i) b u
  have hσ : (H (i + 1)).IsSmoothSection σ := spinCliffordSection_isSmooth S i Y hY u
  let v : (H (i + 1)).smoothSections := ⟨σ, hσ⟩
  refine ⟨v, fun _ ↦ rfl, ?_⟩
  intro x X
  let b := x
  have hx : x ∈ (A.trivialization b).baseSet := A.mem_baseSet x
  let t := A.trivialization b
  let p := t.toPartialEquiv.symm (x, 1)
  let hp : projection p = x := t.proj_symm_apply' hx
  let E (j : ZMod 2) := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m j) p hp
  have hvalue (j : ZMod 2) (τ : ∀ y : M, HalfSpinorBundle m hP j y) :
      q j τ b x = (E j).symm (τ x) := by
    simp only [q, associatedSpinSectionCoordinates, dite_eq_left hx]
    rfl
  have hwu := (spinTangentCoordinates_smooth S b Y hY).contMDiffAt
    (t.open_baseSet.mem_nhds hx)
  have hqu' := (hqu b).contMDiffAt (t.open_baseSet.mem_nhds hx)
  -- Differentiate only a germ on the valid principal chart; no global extension is used.
  have hnear : q (i + 1) v.val b =ᶠ[nhds x]
      (fun y ↦ L (w b y) (q i u.val b y)) := by
    filter_upwards [t.open_baseSet.mem_nhds hx] with y hy
    exact haction b y hy
  have hd : mvfderiv I (q (i + 1) v.val b) x X =
      L (w b x) (mvfderiv I (q i u.val b) x X) +
        L (mvfderiv I (w b) x X) (q i u.val b x) := by
    have h := mvfderiv_bilinear L (w b) (q i u.val b) x
      (hwu.mdifferentiableAt (by simp)) (hqu'.mdifferentiableAt (by simp)) X
    have hcongr {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
        (f₁ f₂ : M → F) (heq : f₁ =ᶠ[nhds x] f₂) :
        mvfderiv I f₁ x X = mvfderiv I f₂ x X := by
      unfold mvfderiv
      rw [heq.mfderiv_eq, heq.eq_of_nhds]
      rfl
    exact (hcongr _ _ hnear).trans h
  have hc₀' := (S.isInducedHalfSpinorConnection_iff_coordinates g i cov₀).mp hc₀ b x hx u X
  have hc₁' :=
    (S.isInducedHalfSpinorConnection_iff_coordinates g (i + 1) cov₁).mp hc₁ b x hx v X
  -- The native tangent connection is expressed in precisely the same lifted frame.
  have hLC := spinTangentCoordinates_leviCivita S b x hx Y hY X
  let coeff := S.liftedLeviCivitaCoefficients b x X
  let a := ∑ j : Fin (2 * m), ∑ k : Fin (2 * m),
    (coeff j k * inner ℝ (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j) (w b x)) •
      EuclideanSpace.basisFun (Fin (2 * m)) ℝ k
  have hskew : ∀ j k, coeff j k = -coeff k j :=
    S.liftedLeviCivitaCoefficients_skew b x hx X
  have hcomm := halfSpinBivector_clifford m i coeff hskew (w b x) (q i u.val b x)
  change halfSpinBivector m (i + 1) coeff (L (w b x) (q i u.val b x)) =
    L a (q i u.val b x) + L (w b x) (halfSpinBivector m i coeff (q i u.val b x)) at hcomm
  have hLC' : (S.frame p x hp).symm
      (CovariantDerivative.leviCivitaConnection I M Y x X) =
        mvfderiv I (w b) x X + a := hLC
  have hY' : (S.frame p x hp).symm (Y x) = w b x :=
    (spinTangentCoordinates_eq S b x hx Y).symm
  have hs' : (E i).symm (u.val x) = q i u.val b x := (hvalue i u.val).symm
  have hcov₀ : (E i).symm (cov₀.covariantDerivative u x X) =
      mvfderiv I (q i u.val b) x X + halfSpinBivector m i coeff (q i u.val b x) := hc₀'
  have hcov₁ : (E (i + 1)).symm (cov₁.covariantDerivative v x X) =
      mvfderiv I (q (i + 1) v.val b) x X +
        halfSpinBivector m (i + 1) coeff (q (i + 1) v.val b x) := hc₁'
  have hleft : (E (i + 1)).symm
      (S.cliffordParity x (CovariantDerivative.leviCivitaConnection I M Y x X) i (u.val x)) =
        L (mvfderiv I (w b) x X + a) (q i u.val b x) := by
    calc
      _ = L ((S.frame p x hp).symm
          (CovariantDerivative.leviCivitaConnection I M Y x X)) ((E i).symm (u.val x)) :=
        spinClifford_coordinates S b x hx i _ _
      _ = _ := congrArg₂ (fun z : V ↦ fun s : W i ↦ L z s) hLC' hs'
  have hright : (E (i + 1)).symm
      (S.cliffordParity x (Y x) i (cov₀.covariantDerivative u x X)) =
        L (w b x) (mvfderiv I (q i u.val b) x X +
          halfSpinBivector m i coeff (q i u.val b x)) := by
    calc
      _ = L ((S.frame p x hp).symm (Y x))
          ((E i).symm (cov₀.covariantDerivative u x X)) :=
        spinClifford_coordinates S b x hx i _ _
      _ = _ := congrArg₂ (fun z : V ↦ fun s : W i ↦ L z s) hY' hcov₀
  have hmodel : mvfderiv I (q (i + 1) v.val b) x X +
      halfSpinBivector m (i + 1) coeff (q (i + 1) v.val b x) =
    L (mvfderiv I (w b) x X + a) (q i u.val b x) +
      L (w b x) (mvfderiv I (q i u.val b) x X +
        halfSpinBivector m i coeff (q i u.val b x)) := by
    have hsum₁ : L (mvfderiv I (w b) x X + a) (q i u.val b x) =
        L (mvfderiv I (w b) x X) (q i u.val b x) + L a (q i u.val b x) :=
      congrArg (fun T : W i →L[ℝ] W (i + 1) ↦ T (q i u.val b x))
        (L.map_add (mvfderiv I (w b) x X) a)
    have hsum₂ := (L (w b x)).map_add (mvfderiv I (q i u.val b) x X)
      (halfSpinBivector m i coeff (q i u.val b x))
    calc
      _ = (L (w b x) (mvfderiv I (q i u.val b) x X) +
          L (mvfderiv I (w b) x X) (q i u.val b x)) +
          halfSpinBivector m (i + 1) coeff (L (w b x) (q i u.val b x)) :=
        congrArg₂ (· + ·) hd
          (congrArg (halfSpinBivector m (i + 1) coeff) (haction b x hx))
      _ = (L (w b x) (mvfderiv I (q i u.val b) x X) +
          L (mvfderiv I (w b) x X) (q i u.val b x)) +
          (L a (q i u.val b x) +
            L (w b x) (halfSpinBivector m i coeff (q i u.val b x))) :=
        congrArg (fun z : W (i + 1) ↦
          (L (w b x) (mvfderiv I (q i u.val b) x X) +
            L (mvfderiv I (w b) x X) (q i u.val b x)) + z) hcomm
      _ = (L (mvfderiv I (w b) x X) (q i u.val b x) + L a (q i u.val b x)) +
          (L (w b x) (mvfderiv I (q i u.val b) x X) +
            L (w b x) (halfSpinBivector m i coeff (q i u.val b x))) := by abel
      _ = _ := congrArg₂ (· + ·) hsum₁.symm hsum₂.symm
  -- Injectivity of the fixed representative equivalence descends the local equality.
  apply (E (i + 1)).symm.injective
  calc
    (E (i + 1)).symm (cov₁.covariantDerivative v x X) =
        mvfderiv I (q (i + 1) v.val b) x X +
          halfSpinBivector m (i + 1) coeff (q (i + 1) v.val b x) := hcov₁
    _ = L (mvfderiv I (w b) x X + a) (q i u.val b x) +
        L (w b x) (mvfderiv I (q i u.val b) x X +
          halfSpinBivector m i coeff (q i u.val b x)) := hmodel
    _ = (E (i + 1)).symm
          (S.cliffordParity x (CovariantDerivative.leviCivitaConnection I M Y x X) i (u.val x)) +
        (E (i + 1)).symm
          (S.cliffordParity x (Y x) i (cov₀.covariantDerivative u x X)) :=
      congrArg₂ (· + ·) hleft.symm hright.symm
    _ = _ := ((E (i + 1)).symm.map_add _ _).symm

end TopologicalSpinStructure

end InducedFormula

end AtiyahSinger
