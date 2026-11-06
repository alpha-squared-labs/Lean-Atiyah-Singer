/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ZeroOrderBundleMap
public import AtiyahSinger.Geometry.CliffordDirac
public import AtiyahSinger.Geometry.SmoothBundleMaps

/-!
# Chiral components of the actual Clifford connection operator

Public module ID: M1119.

S02: a smooth decomposition of the original full module into two given
smooth bundles supplies its actual inclusions and projections. Compressing
the same Clifford connection operator by these maps constructs both chiral
operators. Their symbols are +i times the corresponding blocks of the same
Clifford action, with the project's D_j = -i partial_j convention.

If Clifford multiplication is odd and the same connection preserves this
grading, the full operator has exactly the displayed off-diagonal action.
Oddness alone suffices for ellipticity of the compressed components; no
parallel-grading condition is hidden in that weaker symbol statement.

Sources: Spin Geometry II.6, pp.135--136, for a parallel decomposition,
odd Clifford multiplication and the two chiral Dirac components. The
arbitrary smooth complex connection construction is the same supplement
as in CliffordDirac. No mutual formal-adjoint assertion is made without
the additional metric and connection compatibility of SG Definition 5.2.
Associated spinor decompositions, canonical spin connections, twisting and
the symbol K class belong to their respective constructions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r p q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E Epos Eneg : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (Epos x)] [∀ x, NormedSpace ℂ (Epos x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin p)) Epos)]
  [FiberBundle (EuclideanSpace ℂ (Fin p)) Epos]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin p)) Epos]
  [∀ x, NormedAddCommGroup (Eneg x)] [∀ x, NormedSpace ℂ (Eneg x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) Eneg)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) Eneg]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) Eneg]

/-- A smooth direct-sum decomposition, with its four maps determined by one fiber equivalence. -/
structure SmoothChiralDecomposition where
  /-- The specified decomposition of each original full fiber into its two original summands. -/
  equiv : ∀ x : M, E x ≃ₗ[ℂ] Epos x × Eneg x
  /-- The positive inclusion supplied by this same equivalence is smooth. -/
  smooth_inclusionPlus : IsSmoothBundleMap (n := n) (r := p) (q := r)
    (fun x ↦ (equiv x).symm.toLinearMap.comp (LinearMap.inl ℂ (Epos x) (Eneg x)))
  /-- The negative inclusion supplied by this same equivalence is smooth. -/
  smooth_inclusionMinus : IsSmoothBundleMap (n := n) (r := q) (q := r)
    (fun x ↦ (equiv x).symm.toLinearMap.comp (LinearMap.inr ℂ (Epos x) (Eneg x)))
  /-- The positive projection supplied by this same equivalence is smooth. -/
  smooth_projectionPlus : IsSmoothBundleMap (n := n) (r := r) (q := p)
    (fun x ↦ (LinearMap.fst ℂ (Epos x) (Eneg x)).comp (equiv x).toLinearMap)
  /-- The negative projection supplied by this same equivalence is smooth. -/
  smooth_projectionMinus : IsSmoothBundleMap (n := n) (r := r) (q := q)
    (fun x ↦ (LinearMap.snd ℂ (Epos x) (Eneg x)).comp (equiv x).toLinearMap)

namespace SmoothChiralDecomposition

variable (d : SmoothChiralDecomposition (n := n) (r := r) (p := p) (q := q)
  (E := E) (Epos := Epos) (Eneg := Eneg))

/-- The actual grading involution is +1 on the positive summand and -1 on the negative one. -/
def grading (x : M) : Module.End ℂ (E x) :=
  (d.equiv x).symm.toLinearMap.comp
    (((LinearMap.id : Module.End ℂ (Epos x)).prodMap
      (-LinearMap.id : Module.End ℂ (Eneg x))).comp (d.equiv x).toLinearMap)

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- The positive inclusion on original smooth sections, using the specified fiber equivalence. -/
def inclusionPlus : smoothSections (n := n) (r := p) Epos →ₗ[ℂ]
    smoothSections (n := n) (r := r) E :=
  smoothSectionMap
    (fun x ↦ (d.equiv x).symm.toLinearMap.comp (LinearMap.inl ℂ (Epos x) (Eneg x)))
    d.smooth_inclusionPlus

/-- The negative inclusion on original smooth sections, using the same fiber equivalence. -/
def inclusionMinus : smoothSections (n := n) (r := q) Eneg →ₗ[ℂ]
    smoothSections (n := n) (r := r) E :=
  smoothSectionMap
    (fun x ↦ (d.equiv x).symm.toLinearMap.comp (LinearMap.inr ℂ (Epos x) (Eneg x)))
    d.smooth_inclusionMinus

/-- The positive projection of the original smooth section, with no new section carrier. -/
def projectionPlus : smoothSections (n := n) (r := r) E →ₗ[ℂ]
    smoothSections (n := n) (r := p) Epos :=
  smoothSectionMap
    (fun x ↦ (LinearMap.fst ℂ (Epos x) (Eneg x)).comp (d.equiv x).toLinearMap)
    d.smooth_projectionPlus

/-- The negative projection of the original smooth section, with no new section carrier. -/
def projectionMinus : smoothSections (n := n) (r := r) E →ₗ[ℂ]
    smoothSections (n := n) (r := q) Eneg :=
  smoothSectionMap
    (fun x ↦ (LinearMap.snd ℂ (Epos x) (Eneg x)).comp (d.equiv x).toLinearMap)
    d.smooth_projectionMinus

variable {g : SmoothCotangentMetric (n := n) (M := M)}
  (C : SmoothCliffordModule (n := n) (r := r) E g)

/-- The positive-to-negative block of the same original Clifford multiplication. -/
def cliffordPlus (x : M) (ξ : CotangentFiber (n := n) x) : Epos x →ₗ[ℂ] Eneg x :=
  ((LinearMap.snd ℂ (Epos x) (Eneg x)).comp (d.equiv x).toLinearMap).comp
    ((C.clifford x ξ).comp
      ((d.equiv x).symm.toLinearMap.comp (LinearMap.inl ℂ (Epos x) (Eneg x))))

/-- The negative-to-positive block, with the same original Clifford action and decomposition. -/
def cliffordMinus (x : M) (ξ : CotangentFiber (n := n) x) : Eneg x →ₗ[ℂ] Epos x :=
  ((LinearMap.fst ℂ (Epos x) (Eneg x)).comp (d.equiv x).toLinearMap).comp
    ((C.clifford x ξ).comp
      ((d.equiv x).symm.toLinearMap.comp (LinearMap.inr ℂ (Epos x) (Eneg x))))

variable [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := p) Epos]
  [IsSmoothComplexBundle (n := n) (r := q) Eneg]
  (cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℂ (Fin r)) E)
  (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
  (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E cov)


set_option linter.unusedSectionVars false in
/-- Both actual compressed section maps have order at most one. -/
theorem isDifferentialOperator_chiral :
    IsDifferentialOperator (n := n) (r := p) (q := q) Epos Eneg 1
      (d.projectionMinus.comp
        ((C.diracOperator cov hcov hcomplex).toLinearMap.comp d.inclusionPlus)) ∧
    IsDifferentialOperator (n := n) (r := q) (q := p) Eneg Epos 1
      (d.projectionPlus.comp
        ((C.diracOperator cov hcov hcomplex).toLinearMap.comp d.inclusionMinus)) := by
  /- Stage 1: in the original three smooth bundle frames, the four
  maps of d have smooth matrix coefficients by their specified fields.
  The full operator is the actual first-order Clifford contraction of
  cov. Compose each of its local expressions with the indicated input
  inclusion and output projection, preserving their order.
  Stage 2: the product rule differentiates the input inclusion matrix
  only in the zeroth-order terms. The remaining derivative falls on
  the original input section and has order one. Thus these exact two
  section maps, not independently chosen operators, have smooth local
  expressions of order at most one. No grading compatibility is needed
  for this compression argument, and neither summand rank is identified
  with the other before the separate ellipticity conclusion. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let D := C.diracOperator cov hcov hcomplex
    let H := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r)
    let emptyIndex : Fin 0 → Fin n := Fin.elim0
    have hempty : (default : Fin 0 → Fin n) = emptyIndex := Subsingleton.elim _ _
    -- A first-order expression has one value coefficient and one coefficient per direction.
    have hfirst {a b : ℕ} {Ω : Set H}
        (Q : CoordinateDifferentialOperator n a b 1 Ω)
        (v : H → EuclideanSpace ℂ (Fin a)) (z : H) :
        Q.apply v z = Q.coefficient 0 emptyIndex z (v z) +
          ∑ j : Fin n, Q.coefficient 1 (fun _ ↦ j) z
            (-Complex.I • fderiv ℝ v z (EuclideanSpace.single j 1)) := by
      let reindex : (Fin 1 → Fin n) ≃ Fin n := {
        toFun α := α 0
        invFun j := fun _ ↦ j
        left_inv α := by
          funext t
          exact congrArg α (Subsingleton.elim (0 : Fin 1) t)
        right_inv _ := rfl }
      have hα (α : Fin 1 → Fin n) : (fun _ ↦ α 0) = α := by
        funext t
        exact congrArg α (Subsingleton.elim (0 : Fin 1) t)
      unfold CoordinateDifferentialOperator.apply
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, one_smul,
        iteratedFDeriv_zero_apply, pow_one, Fintype.sum_unique, hempty]
      apply congrArg (Q.coefficient 0 emptyIndex z (v z) + ·)
      simp only [iteratedFDeriv_one_apply]
      calc
        _ = ∑ α : Fin 1 → Fin n, Q.coefficient 1 (fun _ ↦ α 0) z
            (-Complex.I • fderiv ℝ v z (EuclideanSpace.single (α 0) 1)) := by
          apply Finset.sum_congr rfl
          intro α _
          exact congrArg
            (fun t : Fin 1 → Fin n ↦ Q.coefficient 1 t z
              (-Complex.I • fderiv ℝ v z (EuclideanSpace.single (α 0) 1))) (hα α).symm
        _ = _ := reindex.sum_comp (fun j ↦ Q.coefficient 1 (fun _ ↦ j) z
          (-Complex.I • fderiv ℝ v z (EuclideanSpace.single j 1)))
    have hzero {a b : ℕ} {Ω : Set H}
        (Q : CoordinateDifferentialOperator n a b 0 Ω)
        (v : H → EuclideanSpace ℂ (Fin a)) (z : H) :
        Q.apply v z = Q.coefficient 0 emptyIndex z (v z) := by
      simp [CoordinateDifferentialOperator.apply, hempty]
    -- This local coordinate calculation serves both original chiral compressions.
    have hcoordinate {a b : ℕ} (Ω : Set H) (hΩ : IsOpen Ω)
        (Q : CoordinateDifferentialOperator n r r 1 Ω)
        (a₀ : H → EuclideanSpace ℂ (Fin a) →L[ℂ] V)
        (b₀ : H → V →L[ℂ] EuclideanSpace ℂ (Fin b))
        (ha₀ : ContDiffOn ℝ ∞ a₀ Ω) (hb₀ : ContDiffOn ℝ ∞ b₀ Ω) :
        ∃ R : CoordinateDifferentialOperator n a b 1 Ω,
          ∀ (u : H → EuclideanSpace ℂ (Fin a)) (v : H → V) (z : H), z ∈ Ω →
            DifferentiableAt ℝ u z → (v =ᶠ[nhds z] (fun w ↦ a₀ w (u w))) →
              b₀ z (Q.apply v z) = R.apply u z := by
      let Va := EuclideanSpace ℂ (Fin a)
      let Vb := EuclideanSpace ℂ (Fin b)
      let d₀ : H → V →L[ℂ] V := Q.coefficient 0 emptyIndex
      let d₁ (j : Fin n) : H → V →L[ℂ] V := Q.coefficient 1 (fun _ ↦ j)
      have hd₀ : ContDiffOn ℝ ∞ d₀ Ω := Q.smooth_coefficient 0 emptyIndex
      have hd₁ (j : Fin n) : ContDiffOn ℝ ∞ (d₁ j) Ω :=
        Q.smooth_coefficient 1 (fun _ ↦ j)
      let da (j : Fin n) (z : H) : Va →L[ℂ] V :=
        fderiv ℝ a₀ z (EuclideanSpace.single j 1)
      have hda (j : Fin n) : ContDiffOn ℝ ∞ (da j) Ω :=
        (ha₀.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
      let compose₁ := (ContinuousLinearMap.compL ℂ Va V V).bilinearRestrictScalars ℝ
      let compose₂ := (ContinuousLinearMap.compL ℂ Va V Vb).bilinearRestrictScalars ℝ
      let r₁ (j : Fin n) (z : H) : Va →L[ℂ] Vb :=
        (b₀ z).comp ((d₁ j z).comp (a₀ z))
      let r₀ (z : H) : Va →L[ℂ] Vb :=
        (b₀ z).comp ((d₀ z).comp (a₀ z)) +
          ∑ j : Fin n, (b₀ z).comp ((d₁ j z).comp (-Complex.I • da j z))
      have hr₁ (j : Fin n) : ContDiffOn ℝ ∞ (r₁ j) Ω :=
        (compose₂.contDiff.comp_contDiffOn hb₀).clm_apply
          ((compose₁.contDiff.comp_contDiffOn (hd₁ j)).clm_apply ha₀)
      have hr₀ : ContDiffOn ℝ ∞ r₀ Ω := by
        apply ContDiffOn.add
        · exact (compose₂.contDiff.comp_contDiffOn hb₀).clm_apply
            ((compose₁.contDiff.comp_contDiffOn hd₀).clm_apply ha₀)
        · apply ContDiffOn.sum
          intro j _
          exact (compose₂.contDiff.comp_contDiffOn hb₀).clm_apply
            ((compose₁.contDiff.comp_contDiffOn (hd₁ j)).clm_apply
              ((hda j).const_smul (-Complex.I)))
      let R : CoordinateDifferentialOperator n a b 1 Ω := {
        coefficient := Fin.cases (fun _ ↦ r₀)
          (fun k α ↦ r₁ (α ⟨0, Nat.zero_lt_succ k.val⟩))
        smooth_coefficient := by
          intro k
          refine Fin.cases (fun _ ↦ hr₀) (fun k α ↦ ?_) k
          exact hr₁ (α ⟨0, Nat.zero_lt_succ k.val⟩) }
      refine ⟨R, ?_⟩
      intro u v z hz hu hnear
      have ha₀z : DifferentiableAt ℝ a₀ z :=
        (ha₀.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp)
      let eval := (ContinuousLinearMap.apply (E' := Va) ℂ V).flip.bilinearRestrictScalars ℝ
      -- Differentiating the input inclusion adds a value term and leaves order one.
      have hderiv (j : Fin n) : fderiv ℝ v z (EuclideanSpace.single j 1) =
          a₀ z (fderiv ℝ u z (EuclideanSpace.single j 1)) + da j z (u z) := by
        rw [hnear.fderiv_eq]
        exact congrArg (fun L : H →L[ℝ] V ↦ L (EuclideanSpace.single j 1))
          (eval.fderiv_of_bilinear ha₀z hu)
      have hv : v z = a₀ z (u z) := hnear.eq_of_nhds
      rw [hfirst Q v z, hfirst R u z, hv]
      change b₀ z (d₀ z (a₀ z (u z)) +
          ∑ j : Fin n, d₁ j z (-Complex.I • fderiv ℝ v z (EuclideanSpace.single j 1))) =
        r₀ z (u z) +
          ∑ j : Fin n, r₁ j z (-Complex.I • fderiv ℝ u z (EuclideanSpace.single j 1))
      have hr₀_apply : r₀ z (u z) = b₀ z (d₀ z (a₀ z (u z))) +
          ∑ j : Fin n, b₀ z (d₁ j z (-Complex.I • da j z (u z))) := by
        simp only [r₀, add_apply, sum_apply]
        rfl
      rw [hr₀_apply]
      change b₀ z (d₀ z (a₀ z (u z)) +
          ∑ j : Fin n, d₁ j z (-Complex.I • fderiv ℝ v z (EuclideanSpace.single j 1))) =
        b₀ z (d₀ z (a₀ z (u z))) +
          (∑ j : Fin n, b₀ z (d₁ j z (-Complex.I • da j z (u z)))) +
          ∑ j : Fin n, b₀ z (d₁ j z
            (a₀ z (-Complex.I • fderiv ℝ u z (EuclideanSpace.single j 1))))
      simp only [hderiv, smul_add, map_add, map_sum, map_smul, Finset.sum_add_distrib]
      abel
    constructor
    · intro c hc e he f hf x hx
      let A := d.inclusionPlus
      let B := d.projectionMinus
      let t := trivializationAt V E x
      have htx : x ∈ t.baseSet := mem_baseSet_trivializationAt V E x
      -- The same full-bundle frame mediates all three original expressions.
      obtain ⟨UA, hUA, hxA, QA, hQA⟩ :=
        isDifferentialOperator_smoothSectionMap _ d.smooth_inclusionPlus
          c hc e t x ⟨⟨hx.1.1, hx.1.2⟩, htx⟩
      obtain ⟨UD, hUD, hxD, QD, hQD⟩ :=
        D.isDifferentialOperator c hc t t x ⟨⟨hx.1.1, htx⟩, htx⟩
      obtain ⟨UB, hUB, hxB, QB, hQB⟩ :=
        isDifferentialOperator_smoothSectionMap _ d.smooth_projectionMinus
          c hc t f x ⟨⟨hx.1.1, htx⟩, hx.2⟩
      let U := UA ∩ UD ∩ UB
      have hU : IsOpen U := (hUA.inter hUD).inter hUB
      have hUs : U ⊆ c.source := fun _ hy ↦ (hQA.1 hy.1.1).1.1
      let Ω := c '' U
      have hΩ : IsOpen Ω := c.isOpen_image_of_subset_source hU hUs
      have hΩA : Ω ⊆ c '' UA := Set.image_mono (fun _ hy ↦ hy.1.1)
      have hΩD : Ω ⊆ c '' UD := Set.image_mono (fun _ hy ↦ hy.1.2)
      have hΩB : Ω ⊆ c '' UB := Set.image_mono (fun _ hy ↦ hy.2)
      let a₀ := QA.coefficient 0 emptyIndex
      let b₀ := QB.coefficient 0 emptyIndex
      let Q : CoordinateDifferentialOperator n r r 1 Ω := {
        coefficient := QD.coefficient
        smooth_coefficient := fun k α ↦ (QD.smooth_coefficient k α).mono hΩD }
      obtain ⟨R, hR⟩ := hcoordinate Ω hΩ Q a₀ b₀
        ((QA.smooth_coefficient 0 emptyIndex).mono hΩA)
        ((QB.smooth_coefficient 0 emptyIndex).mono hΩB)
      refine ⟨U, hU, ⟨⟨hxA, hxD⟩, hxB⟩, R, ?_, ?_⟩
      · intro y hy
        exact ⟨⟨(hQA.1 hy.1.1).1.1, (hQA.1 hy.1.1).1.2⟩, (hQB.1 hy.2).2⟩
      intro u y hy
      let z := c y
      let u₀ := sectionInChart Epos c e u.val
      let v₀ := sectionInChart E c t (A u).val
      have hz : z ∈ Ω := ⟨y, hy, rfl⟩
      have hAz (w : M) (hw : w ∈ UA) :
          (t ⟨w, (A u).val w⟩).2 = a₀ (c w) (u₀ (c w)) := by
        have h := hQA.2 u w hw
        change (t ⟨w, (A u).val w⟩).2 = QA.apply u₀ (c w) at h
        exact h.trans (hzero QA u₀ (c w))
      have hnear : v₀ =ᶠ[nhds z] (fun w ↦ a₀ w (u₀ w)) := by
        have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
          (I := 𝓘(ℝ, H)) (n := ∞) (IsManifold.subset_maximalAtlas hc)
          (c.map_source (hUs hy))
        have hpre : c.symm ⁻¹' UA ∈ nhds z :=
          hsymm.continuousAt.preimage_mem_nhds (by
            simpa only [z, c.left_inv (hUs hy)] using hUA.mem_nhds hy.1.1)
        filter_upwards [hpre, c.open_target.mem_nhds (c.map_source (hUs hy))] with w hw hwt
        dsimp only [v₀, sectionInChart]
        have heq := hAz (c.symm w) hw
        rw [c.right_inv hwt] at heq
        exact heq
      have hu₀ : DifferentiableAt ℝ u₀ z := by
        have hs := u.property e he
        have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
          (I := 𝓘(ℝ, H)) (n := ∞) (IsManifold.subset_maximalAtlas hc)
          (c.map_source (hUs hy))
        have hvalue : c.symm z ∈ e.baseSet := by
          simpa only [z, c.left_inv (hUs hy)] using (hQA.1 hy.1.1).1.2
        have hlocal := (hs.contMDiffAt (e.open_baseSet.mem_nhds hvalue)).comp z hsymm
        exact (contMDiffAt_iff_contDiffAt.mp hlocal).differentiableAt (by simp)
      have hBy := hQB.2 (D.toLinearMap (A u)) y hy.2
      have hDy := hQD.2 (A u) y hy.1.2
      have hcy : c.symm (c y) = y := c.left_inv (hUs hy)
      have houtput :
          (f ⟨y, ((B.comp (D.toLinearMap.comp A)) u).val y⟩).2 = b₀ z (Q.apply v₀ z) := by
        change (f ⟨y, (B (D.toLinearMap (A u))).val y⟩).2 =
          QB.apply (sectionInChart E c t (D.toLinearMap (A u)).val) z at hBy
        rw [hzero] at hBy
        have hsection : sectionInChart E c t (D.toLinearMap (A u)).val z =
            (t ⟨y, (D.toLinearMap (A u)).val y⟩).2 := by
          dsimp only [sectionInChart, z]
          rw [hcy]
        rw [hsection, hDy] at hBy
        exact hBy
      exact houtput.trans (hR u₀ v₀ z hz hu₀ hnear)
    · intro c hc e he f hf x hx
      let A := d.inclusionMinus
      let B := d.projectionPlus
      let t := trivializationAt V E x
      have htx : x ∈ t.baseSet := mem_baseSet_trivializationAt V E x
      -- The same full-bundle frame mediates all three original expressions.
      obtain ⟨UA, hUA, hxA, QA, hQA⟩ :=
        isDifferentialOperator_smoothSectionMap _ d.smooth_inclusionMinus
          c hc e t x ⟨⟨hx.1.1, hx.1.2⟩, htx⟩
      obtain ⟨UD, hUD, hxD, QD, hQD⟩ :=
        D.isDifferentialOperator c hc t t x ⟨⟨hx.1.1, htx⟩, htx⟩
      obtain ⟨UB, hUB, hxB, QB, hQB⟩ :=
        isDifferentialOperator_smoothSectionMap _ d.smooth_projectionPlus
          c hc t f x ⟨⟨hx.1.1, htx⟩, hx.2⟩
      let U := UA ∩ UD ∩ UB
      have hU : IsOpen U := (hUA.inter hUD).inter hUB
      have hUs : U ⊆ c.source := fun _ hy ↦ (hQA.1 hy.1.1).1.1
      let Ω := c '' U
      have hΩ : IsOpen Ω := c.isOpen_image_of_subset_source hU hUs
      have hΩA : Ω ⊆ c '' UA := Set.image_mono (fun _ hy ↦ hy.1.1)
      have hΩD : Ω ⊆ c '' UD := Set.image_mono (fun _ hy ↦ hy.1.2)
      have hΩB : Ω ⊆ c '' UB := Set.image_mono (fun _ hy ↦ hy.2)
      let a₀ := QA.coefficient 0 emptyIndex
      let b₀ := QB.coefficient 0 emptyIndex
      let Q : CoordinateDifferentialOperator n r r 1 Ω := {
        coefficient := QD.coefficient
        smooth_coefficient := fun k α ↦ (QD.smooth_coefficient k α).mono hΩD }
      obtain ⟨R, hR⟩ := hcoordinate Ω hΩ Q a₀ b₀
        ((QA.smooth_coefficient 0 emptyIndex).mono hΩA)
        ((QB.smooth_coefficient 0 emptyIndex).mono hΩB)
      refine ⟨U, hU, ⟨⟨hxA, hxD⟩, hxB⟩, R, ?_, ?_⟩
      · intro y hy
        exact ⟨⟨(hQA.1 hy.1.1).1.1, (hQA.1 hy.1.1).1.2⟩, (hQB.1 hy.2).2⟩
      intro u y hy
      let z := c y
      let u₀ := sectionInChart Eneg c e u.val
      let v₀ := sectionInChart E c t (A u).val
      have hz : z ∈ Ω := ⟨y, hy, rfl⟩
      have hAz (w : M) (hw : w ∈ UA) :
          (t ⟨w, (A u).val w⟩).2 = a₀ (c w) (u₀ (c w)) := by
        have h := hQA.2 u w hw
        change (t ⟨w, (A u).val w⟩).2 = QA.apply u₀ (c w) at h
        exact h.trans (hzero QA u₀ (c w))
      have hnear : v₀ =ᶠ[nhds z] (fun w ↦ a₀ w (u₀ w)) := by
        have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
          (I := 𝓘(ℝ, H)) (n := ∞) (IsManifold.subset_maximalAtlas hc)
          (c.map_source (hUs hy))
        have hpre : c.symm ⁻¹' UA ∈ nhds z :=
          hsymm.continuousAt.preimage_mem_nhds (by
            simpa only [z, c.left_inv (hUs hy)] using hUA.mem_nhds hy.1.1)
        filter_upwards [hpre, c.open_target.mem_nhds (c.map_source (hUs hy))] with w hw hwt
        dsimp only [v₀, sectionInChart]
        have heq := hAz (c.symm w) hw
        rw [c.right_inv hwt] at heq
        exact heq
      have hu₀ : DifferentiableAt ℝ u₀ z := by
        have hs := u.property e he
        have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
          (I := 𝓘(ℝ, H)) (n := ∞) (IsManifold.subset_maximalAtlas hc)
          (c.map_source (hUs hy))
        have hvalue : c.symm z ∈ e.baseSet := by
          simpa only [z, c.left_inv (hUs hy)] using (hQA.1 hy.1.1).1.2
        have hlocal := (hs.contMDiffAt (e.open_baseSet.mem_nhds hvalue)).comp z hsymm
        exact (contMDiffAt_iff_contDiffAt.mp hlocal).differentiableAt (by simp)
      have hBy := hQB.2 (D.toLinearMap (A u)) y hy.2
      have hDy := hQD.2 (A u) y hy.1.2
      have hcy : c.symm (c y) = y := c.left_inv (hUs hy)
      have houtput :
          (f ⟨y, ((B.comp (D.toLinearMap.comp A)) u).val y⟩).2 = b₀ z (Q.apply v₀ z) := by
        change (f ⟨y, (B (D.toLinearMap (A u))).val y⟩).2 =
          QB.apply (sectionInChart E c t (D.toLinearMap (A u)).val) z at hBy
        rw [hzero] at hBy
        have hsection : sectionInChart E c t (D.toLinearMap (A u)).val z =
            (t ⟨y, (D.toLinearMap (A u)).val y⟩).2 := by
          dsimp only [sectionInChart, z]
          rw [hcy]
        rw [hsection, hDy] at hBy
        exact hBy
      exact houtput.trans (hR u₀ v₀ z hz hu₀ hnear)

/-- The positive chiral operator is the actual negative projection of D on positive inputs. -/
def diracPlus : DifferentialOperator (n := n) (r := p) (q := q) Epos Eneg 1 where
  toLinearMap := d.projectionMinus.comp
    ((C.diracOperator cov hcov hcomplex).toLinearMap.comp d.inclusionPlus)
  isDifferentialOperator := (d.isDifferentialOperator_chiral C cov hcov hcomplex).1

/-- The negative chiral operator is the actual positive projection of D on negative inputs. -/
def diracMinus : DifferentialOperator (n := n) (r := q) (q := p) Eneg Epos 1 where
  toLinearMap := d.projectionPlus.comp
    ((C.diracOperator cov hcov hcomplex).toLinearMap.comp d.inclusionMinus)
  isDifferentialOperator := (d.isDifferentialOperator_chiral C cov hcov hcomplex).2

/-- The positive chiral principal symbol retains +i and the actual positive Clifford block. -/
theorem diracPlus_principalSymbol (x : M) (ξ : CotangentFiber (n := n) x) :
    (d.diracPlus C cov hcov hcomplex).principalSymbol x ξ =
      Complex.I • d.cliffordPlus C x ξ := by
  /- Stage 1: the positive inclusion commutes with real scalar multiplication.
  Apply the same full Dirac Leibniz identity to this included section, then
  take its negative projection. The derivative-of-scalar term is precisely
  cliffordPlus acting on df and the original positive input.
  Stage 2: the principal-symbol characterization by this Leibniz identity
  gives +i cliffordPlus in the fixed D_j = -i partial_j convention.
  All inclusion and projection maps are those of the supplied decomposition. -/
  -- Compress the same full Dirac Leibniz identity through the specified bundle maps.
  refine (d.diracPlus C cov hcov hcomplex).principalSymbol_eq_smul_of_leibniz
    (fun y η ↦ d.cliffordPlus C y η) ?_ x ξ
  intro φ hφ u v hv y
  have hmul : d.inclusionPlus v = smoothSectionMul E (fun z ↦ (φ z : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hφ) (d.inclusionPlus u) := by
    apply Subtype.ext
    funext z
    change (d.equiv z).symm (v.val z, 0) =
      (φ z : ℂ) • (d.equiv z).symm (u.val z, 0)
    rw [hv z, ← map_smul]
    congr 1
    simp only [Prod.smul_mk, smul_zero]
  have hfull := C.diracOperator_smoothSectionMul cov hcov hcomplex
    φ hφ (d.inclusionPlus u) y
  change (d.equiv y (((C.diracOperator cov hcov hcomplex).toLinearMap
      (d.inclusionPlus v)).val y)).2 = _
  rw [hmul, hfull, map_add, map_smul]
  rfl

/-- The negative chiral symbol uses the opposite block of the same full Clifford action. -/
theorem diracMinus_principalSymbol (x : M) (ξ : CotangentFiber (n := n) x) :
    (d.diracMinus C cov hcov hcomplex).principalSymbol x ξ =
      Complex.I • d.cliffordMinus C x ξ := by
  /- The negative inclusion commutes with real scalar multiplication. Apply
  the same full Dirac Leibniz identity and take the positive projection.
  Its scalar-derivative term is cliffordMinus on the same original fibers.
  The Leibniz characterization of the principal symbol gives +i cliffordMinus,
  preserving both the Fourier convention and the chirality labels. -/
  -- Compress the same full Dirac Leibniz identity through the specified bundle maps.
  refine (d.diracMinus C cov hcov hcomplex).principalSymbol_eq_smul_of_leibniz
    (fun y η ↦ d.cliffordMinus C y η) ?_ x ξ
  intro φ hφ u v hv y
  have hmul : d.inclusionMinus v = smoothSectionMul E (fun z ↦ (φ z : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hφ) (d.inclusionMinus u) := by
    apply Subtype.ext
    funext z
    change (d.equiv z).symm (0, v.val z) =
      (φ z : ℂ) • (d.equiv z).symm (0, u.val z)
    rw [hv z, ← map_smul]
    congr 1
    simp only [Prod.smul_mk, smul_zero]
  have hfull := C.diracOperator_smoothSectionMul cov hcov hcomplex
    φ hφ (d.inclusionMinus u) y
  change (d.equiv y (((C.diracOperator cov hcov hcomplex).toLinearMap
      (d.inclusionMinus v)).val y)).1 = _
  rw [hmul, hfull, map_add, map_smul]
  rfl

variable (hodd : ∀ (x : M) (ξ : CotangentFiber (n := n) x) (v : E x),
  d.grading x (C.clifford x ξ v) = -C.clifford x ξ (d.grading x v))

include hodd in
/-- Odd Clifford multiplication makes the actual positive chiral component elliptic. -/
theorem diracPlus_isElliptic : (d.diracPlus C cov hcov hcomplex).IsElliptic := by
  /- Stage 1: the original decomposition makes grading +1 and -1
  on its two summands. Anticommutation therefore makes Clifford
  multiplication exchange these summands exactly. Its square identity
  gives cMinus(ξ)cPlus(ξ)=-a Id and cPlus(ξ)cMinus(ξ)=-a Id,
  where a=g.inner x ξ ξ is positive for a nonzero covector.
  Stage 2: the positive principal symbol is i cPlus(ξ). The map
  (i/a)cMinus(ξ) is its two-sided inverse, by those same two square
  identities. This proves bijectivity without a prior rank equality.
  Connection preservation of grading is unnecessary for this symbol
  argument. For n=0 there are no nonzero covectors; zero fibers and
  empty bases are allowed. -/
  intro x ξ hξ
  rw [d.diracPlus_principalSymbol C cov hcov hcomplex]
  let a : ℂ := g.inner x ξ ξ
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (g.pos x ξ hξ))
  have hgrade (w : E x) : d.grading x w =
      (d.equiv x).symm ((d.equiv x w).1, -(d.equiv x w).2) := rfl
  -- Oddness removes the same-summand component in the original decomposition.
  have hplus (v : Epos x) :
      C.clifford x ξ ((d.equiv x).symm (v, 0)) =
        (d.equiv x).symm (0, d.cliffordPlus C x ξ v) := by
    let w := C.clifford x ξ ((d.equiv x).symm (v, 0))
    have h := hodd x ξ ((d.equiv x).symm (v, 0))
    simp only [hgrade, (d.equiv x).apply_symm_apply, neg_zero] at h
    have hcoord := congrArg (fun z : E x ↦ (d.equiv x z).1) h
    have hanti : (d.equiv x w).1 = -(d.equiv x w).1 := by
      simpa only [(d.equiv x).apply_symm_apply, map_neg, Prod.fst_neg] using hcoord
    have hzero : (d.equiv x w).1 = 0 := by
      have htwo : (2 : ℂ) • (d.equiv x w).1 = 0 := by
        calc
          _ = (d.equiv x w).1 + (d.equiv x w).1 := two_smul ℂ _
          _ = -(d.equiv x w).1 + (d.equiv x w).1 :=
            congrArg (· + (d.equiv x w).1) hanti
          _ = 0 := neg_add_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    apply (d.equiv x).injective
    rw [(d.equiv x).apply_symm_apply]
    exact Prod.ext hzero rfl
  have hminus (v : Eneg x) :
      C.clifford x ξ ((d.equiv x).symm (0, v)) =
        (d.equiv x).symm (d.cliffordMinus C x ξ v, 0) := by
    let w := C.clifford x ξ ((d.equiv x).symm (0, v))
    have h := hodd x ξ ((d.equiv x).symm (0, v))
    simp only [hgrade, (d.equiv x).apply_symm_apply] at h
    have hin : (d.equiv x).symm (0, -v) = -(d.equiv x).symm (0, v) := by
      rw [← map_neg]
      simp only [Prod.neg_mk, neg_zero]
    rw [hin, map_neg, neg_neg] at h
    have hcoord := congrArg (fun z : E x ↦ (d.equiv x z).2) h
    have hanti : (d.equiv x w).2 = -(d.equiv x w).2 := by
      simpa only [(d.equiv x).apply_symm_apply] using hcoord.symm
    have hzero : (d.equiv x w).2 = 0 := by
      have htwo : (2 : ℂ) • (d.equiv x w).2 = 0 := by
        calc
          _ = (d.equiv x w).2 + (d.equiv x w).2 := two_smul ℂ _
          _ = -(d.equiv x w).2 + (d.equiv x w).2 :=
            congrArg (· + (d.equiv x w).2) hanti
          _ = 0 := neg_add_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    apply (d.equiv x).injective
    rw [(d.equiv x).apply_symm_apply]
    exact Prod.ext rfl hzero
  -- The full Clifford square now gives both ordered block compositions.
  have hsquarePlus (v : Epos x) :
      d.cliffordMinus C x ξ (d.cliffordPlus C x ξ v) = -a • v := by
    have h := congrArg (fun w : E x ↦ (d.equiv x w).1)
      (C.clifford_sq x ξ ((d.equiv x).symm (v, 0)))
    rw [hplus, map_smul, (d.equiv x).apply_symm_apply] at h
    exact h
  have hsquareMinus (v : Eneg x) :
      d.cliffordPlus C x ξ (d.cliffordMinus C x ξ v) = -a • v := by
    have h := congrArg (fun w : E x ↦ (d.equiv x w).2)
      (C.clifford_sq x ξ ((d.equiv x).symm (0, v)))
    rw [hminus, map_smul, (d.equiv x).apply_symm_apply] at h
    exact h
  let A : Epos x →ₗ[ℂ] Eneg x := Complex.I • d.cliffordPlus C x ξ
  let R : Eneg x →ₗ[ℂ] Epos x := Complex.I • d.cliffordMinus C x ξ
  have hRA (v : Epos x) : R (A v) = a • v := by
    dsimp only [A, R]
    simp only [LinearMap.smul_apply, map_smul, hsquarePlus, smul_smul,
      ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, neg_neg]
  have hAR (v : Eneg x) : A (R v) = a • v := by
    dsimp only [A, R]
    simp only [LinearMap.smul_apply, map_smul, hsquareMinus, smul_smul,
      ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, neg_neg]
  -- Reciprocal metric scaling of the opposite +i block is an actual two-sided inverse.
  let B : Eneg x → Epos x := fun v ↦ a⁻¹ • R v
  have hleft : Function.LeftInverse B A := by
    intro v
    change a⁻¹ • R (A v) = v
    rw [hRA, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hright : Function.RightInverse B A := by
    intro v
    change A (a⁻¹ • R v) = v
    rw [map_smul, hAR, smul_smul, inv_mul_cancel₀ ha, one_smul]
  exact ⟨hleft.injective, hright.surjective⟩

include hodd in
/-- The same odd Clifford relation also makes the actual negative chiral component elliptic. -/
theorem diracMinus_isElliptic : (d.diracMinus C cov hcov hcomplex).IsElliptic := by
  /- Interchange the two original summands in the preceding Clifford
  square argument. The exact inverse of i cMinus(ξ) is (i/a)cPlus(ξ),
  with the same positive a from the original metric. The two ordered
  compositions give identity on their respective original fibers.
  This uses only hodd and the same full Clifford square identity,
  not a formal-adjoint assertion or a parallel-grading assumption. -/
  intro x ξ hξ
  rw [d.diracMinus_principalSymbol C cov hcov hcomplex]
  let a : ℂ := g.inner x ξ ξ
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (g.pos x ξ hξ))
  have hgrade (w : E x) : d.grading x w =
      (d.equiv x).symm ((d.equiv x w).1, -(d.equiv x w).2) := rfl
  -- Oddness removes the same-summand component in the original decomposition.
  have hplus (v : Epos x) :
      C.clifford x ξ ((d.equiv x).symm (v, 0)) =
        (d.equiv x).symm (0, d.cliffordPlus C x ξ v) := by
    let w := C.clifford x ξ ((d.equiv x).symm (v, 0))
    have h := hodd x ξ ((d.equiv x).symm (v, 0))
    simp only [hgrade, (d.equiv x).apply_symm_apply, neg_zero] at h
    have hcoord := congrArg (fun z : E x ↦ (d.equiv x z).1) h
    have hanti : (d.equiv x w).1 = -(d.equiv x w).1 := by
      simpa only [(d.equiv x).apply_symm_apply, map_neg, Prod.fst_neg] using hcoord
    have hzero : (d.equiv x w).1 = 0 := by
      have htwo : (2 : ℂ) • (d.equiv x w).1 = 0 := by
        calc
          _ = (d.equiv x w).1 + (d.equiv x w).1 := two_smul ℂ _
          _ = -(d.equiv x w).1 + (d.equiv x w).1 :=
            congrArg (· + (d.equiv x w).1) hanti
          _ = 0 := neg_add_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    apply (d.equiv x).injective
    rw [(d.equiv x).apply_symm_apply]
    exact Prod.ext hzero rfl
  have hminus (v : Eneg x) :
      C.clifford x ξ ((d.equiv x).symm (0, v)) =
        (d.equiv x).symm (d.cliffordMinus C x ξ v, 0) := by
    let w := C.clifford x ξ ((d.equiv x).symm (0, v))
    have h := hodd x ξ ((d.equiv x).symm (0, v))
    simp only [hgrade, (d.equiv x).apply_symm_apply] at h
    have hin : (d.equiv x).symm (0, -v) = -(d.equiv x).symm (0, v) := by
      rw [← map_neg]
      simp only [Prod.neg_mk, neg_zero]
    rw [hin, map_neg, neg_neg] at h
    have hcoord := congrArg (fun z : E x ↦ (d.equiv x z).2) h
    have hanti : (d.equiv x w).2 = -(d.equiv x w).2 := by
      simpa only [(d.equiv x).apply_symm_apply] using hcoord.symm
    have hzero : (d.equiv x w).2 = 0 := by
      have htwo : (2 : ℂ) • (d.equiv x w).2 = 0 := by
        calc
          _ = (d.equiv x w).2 + (d.equiv x w).2 := two_smul ℂ _
          _ = -(d.equiv x w).2 + (d.equiv x w).2 :=
            congrArg (· + (d.equiv x w).2) hanti
          _ = 0 := neg_add_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    apply (d.equiv x).injective
    rw [(d.equiv x).apply_symm_apply]
    exact Prod.ext rfl hzero
  -- The full Clifford square now gives both ordered block compositions.
  have hsquarePlus (v : Epos x) :
      d.cliffordMinus C x ξ (d.cliffordPlus C x ξ v) = -a • v := by
    have h := congrArg (fun w : E x ↦ (d.equiv x w).1)
      (C.clifford_sq x ξ ((d.equiv x).symm (v, 0)))
    rw [hplus, map_smul, (d.equiv x).apply_symm_apply] at h
    exact h
  have hsquareMinus (v : Eneg x) :
      d.cliffordPlus C x ξ (d.cliffordMinus C x ξ v) = -a • v := by
    have h := congrArg (fun w : E x ↦ (d.equiv x w).2)
      (C.clifford_sq x ξ ((d.equiv x).symm (0, v)))
    rw [hminus, map_smul, (d.equiv x).apply_symm_apply] at h
    exact h
  let A : Epos x →ₗ[ℂ] Eneg x := Complex.I • d.cliffordPlus C x ξ
  let R : Eneg x →ₗ[ℂ] Epos x := Complex.I • d.cliffordMinus C x ξ
  have hRA (v : Epos x) : R (A v) = a • v := by
    dsimp only [A, R]
    simp only [LinearMap.smul_apply, map_smul, hsquarePlus, smul_smul,
      ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, neg_neg]
  have hAR (v : Eneg x) : A (R v) = a • v := by
    dsimp only [A, R]
    simp only [LinearMap.smul_apply, map_smul, hsquareMinus, smul_smul,
      ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, neg_neg]
  -- Reciprocal metric scaling of the opposite +i block is an actual two-sided inverse.
  let B : Epos x → Eneg x := fun v ↦ a⁻¹ • A v
  have hleft : Function.LeftInverse B R := by
    intro v
    change a⁻¹ • A (R v) = v
    rw [hAR, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hright : Function.RightInverse B R := by
    intro v
    change R (a⁻¹ • A v) = v
    rw [map_smul, hRA, smul_smul, inv_mul_cancel₀ ha, one_smul]
  exact ⟨hleft.injective, hright.surjective⟩

include hodd in
/-- A parallel grading makes the full operator exactly off-diagonal with these two components. -/
theorem diracOperator_block
    (hparallel : ∀ (u : smoothSections (n := n) (r := r) E) (x : M)
      (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
      cov (fun y ↦ d.grading y (u.val y)) x v = d.grading x (cov u.val x v))
    (u : smoothSections (n := n) (r := r) E) (x : M) :
    ((C.diracOperator cov hcov hcomplex).toLinearMap u).val x =
      (d.equiv x).symm
        (((d.diracMinus C cov hcov hcomplex).toLinearMap (d.projectionMinus u)).val x,
          ((d.diracPlus C cov hcov hcomplex).toLinearMap (d.projectionPlus u)).val x) := by
  /- Stage 1: the four smooth maps of d make its grading preserve
  original smooth sections. Apply hparallel to the actual covariant
  derivative and hodd to every term of its same Clifford contraction.
  This gives D(grading u)=-grading(Du) exactly, including the connection
  terms. A principal-symbol relation alone would not give this equality.
  Stage 2: each input equals the sum of its two actual inclusions of
  its projections. On a positive input the displayed anticommutation
  forces D's positive projection to vanish; on a negative input its
  negative projection vanishes. The scalar 2 is invertible over ℂ.
  Stage 3: use the linearity of the same full D and the definitions of
  diracPlus and diracMinus. Reassemble the surviving components by the
  same inverse equivalence d.equiv. No independent half connection,
  altered zeroth-order term or silently exchanged labels occur. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let D := C.diracOperator cov hcov hcomplex
    let Γ : smoothSections (n := n) (r := r) E →ₗ[ℂ]
        smoothSections (n := n) (r := r) E :=
      d.inclusionPlus.comp d.projectionPlus - d.inclusionMinus.comp d.projectionMinus
    -- The original four smooth maps realize the actual grading on smooth sections.
    have hΓ (v : smoothSections (n := n) (r := r) E) (y : M) :
        (Γ v).val y = d.grading y (v.val y) := by
      change (d.equiv y).symm ((d.equiv y (v.val y)).1, 0) -
          (d.equiv y).symm (0, (d.equiv y (v.val y)).2) =
        (d.equiv y).symm ((d.equiv y (v.val y)).1, -(d.equiv y (v.val y)).2)
      rw [← map_sub]
      congr 1
      ext <;> simp
    have hΓfun (v : smoothSections (n := n) (r := r) E) :
        (Γ v).val = fun y ↦ d.grading y (v.val y) := funext (hΓ v)
    have hplus (v : smoothSections (n := n) (r := p) Epos) :
        Γ (d.inclusionPlus v) = d.inclusionPlus v := by
      apply Subtype.ext
      funext y
      rw [hΓ]
      change (d.equiv y).symm
          ((d.equiv y ((d.equiv y).symm (v.val y, 0))).1,
            -(d.equiv y ((d.equiv y).symm (v.val y, 0))).2) =
        (d.equiv y).symm (v.val y, 0)
      rw [(d.equiv y).apply_symm_apply]
      simp only [neg_zero]
    have hminus (v : smoothSections (n := n) (r := q) Eneg) :
        Γ (d.inclusionMinus v) = -d.inclusionMinus v := by
      apply Subtype.ext
      funext y
      rw [hΓ]
      change (d.equiv y).symm
          ((d.equiv y ((d.equiv y).symm (0, v.val y))).1,
            -(d.equiv y ((d.equiv y).symm (0, v.val y))).2) =
        -(d.equiv y).symm (0, v.val y)
      rw [(d.equiv y).apply_symm_apply, ← map_neg]
      congr 1
      ext <;> simp
    -- Parallelism and odd Clifford multiplication concern this exact connection contraction.
    have hanti (v : smoothSections (n := n) (r := r) E) (y : M) :
        (D.toLinearMap (Γ v)).val y = -d.grading y ((D.toLinearMap v).val y) := by
      change ((C.diracOperator cov hcov hcomplex).toLinearMap (Γ v)).val y =
        -d.grading y (((C.diracOperator cov hcov hcomplex).toLinearMap v).val y)
      rw [C.diracOperator_apply cov hcov hcomplex, C.diracOperator_apply cov hcov hcomplex]
      change (∑ j : Fin n, C.clifford y (EuclideanSpace.proj j)
          (cov (Γ v).val y (EuclideanSpace.single j 1))) =
        -d.grading y (∑ j : Fin n, C.clifford y (EuclideanSpace.proj j)
          (cov v.val y (EuclideanSpace.single j 1)))
      rw [map_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hΓfun, hparallel v y (EuclideanSpace.single j 1)]
      have hh := congrArg Neg.neg
        (hodd y (EuclideanSpace.proj j) (cov v.val y (EuclideanSpace.single j 1)))
      simpa only [neg_neg] using hh.symm
    -- On each summand anticommutation kills the same-summand component over ℂ.
    have hdiagPlus (v : smoothSections (n := n) (r := p) Epos) (y : M) :
        (d.equiv y ((D.toLinearMap (d.inclusionPlus v)).val y)).1 = 0 := by
      let w := (D.toLinearMap (d.inclusionPlus v)).val y
      have hh := hanti (d.inclusionPlus v) y
      rw [hplus v] at hh
      have h := congrArg (fun z : E y ↦ (d.equiv y z).1) hh
      have hcoord : (d.equiv y w).1 = -(d.equiv y w).1 := by
        change (d.equiv y w).1 =
          (d.equiv y (-(d.equiv y).symm ((d.equiv y w).1, -(d.equiv y w).2))).1 at h
        simpa only [map_neg, (d.equiv y).apply_symm_apply, Prod.fst_neg] using h
      have hzero : (2 : ℂ) • (d.equiv y w).1 = 0 := by
        calc
          _ = (d.equiv y w).1 + (d.equiv y w).1 := two_smul ℂ _
          _ = -(d.equiv y w).1 + (d.equiv y w).1 := congrArg (· + (d.equiv y w).1) hcoord
          _ = 0 := neg_add_cancel _
      exact (smul_eq_zero.mp hzero).resolve_left (by norm_num)
    have hdiagMinus (v : smoothSections (n := n) (r := q) Eneg) (y : M) :
        (d.equiv y ((D.toLinearMap (d.inclusionMinus v)).val y)).2 = 0 := by
      let w := (D.toLinearMap (d.inclusionMinus v)).val y
      have hh := hanti (d.inclusionMinus v) y
      rw [hminus v, map_neg] at hh
      have hsame : w = d.grading y w := neg_injective hh
      have h := congrArg (fun z : E y ↦ (d.equiv y z).2) hsame
      have hcoord : (d.equiv y w).2 = -(d.equiv y w).2 := by
        change (d.equiv y w).2 =
          (d.equiv y ((d.equiv y).symm ((d.equiv y w).1, -(d.equiv y w).2))).2 at h
        simpa only [(d.equiv y).apply_symm_apply] using h
      have hzero : (2 : ℂ) • (d.equiv y w).2 = 0 := by
        calc
          _ = (d.equiv y w).2 + (d.equiv y w).2 := two_smul ℂ _
          _ = -(d.equiv y w).2 + (d.equiv y w).2 := congrArg (· + (d.equiv y w).2) hcoord
          _ = 0 := neg_add_cancel _
      exact (smul_eq_zero.mp hzero).resolve_left (by norm_num)
    -- Split the original input, apply the same D, and reassemble through the same equivalence.
    have hsplit : d.inclusionPlus (d.projectionPlus u) +
        d.inclusionMinus (d.projectionMinus u) = u := by
      apply Subtype.ext
      funext y
      change (d.equiv y).symm ((d.equiv y (u.val y)).1, 0) +
          (d.equiv y).symm (0, (d.equiv y (u.val y)).2) = u.val y
      rw [← map_add]
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using
        (d.equiv y).symm_apply_apply (u.val y)
    have hDsplit := congrArg
      (fun v : smoothSections (n := n) (r := r) E ↦ (D.toLinearMap v).val x) hsplit
    rw [map_add] at hDsplit
    change (D.toLinearMap (d.inclusionPlus (d.projectionPlus u))).val x +
      (D.toLinearMap (d.inclusionMinus (d.projectionMinus u))).val x =
        (D.toLinearMap u).val x at hDsplit
    apply (d.equiv x).injective
    rw [(d.equiv x).apply_symm_apply]
    change d.equiv x ((D.toLinearMap u).val x) =
      ((d.equiv x ((D.toLinearMap (d.inclusionMinus (d.projectionMinus u))).val x)).1,
        (d.equiv x ((D.toLinearMap (d.inclusionPlus (d.projectionPlus u))).val x)).2)
    rw [← hDsplit, map_add]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, hdiagPlus, hdiagMinus, zero_add, add_zero]

end SmoothChiralDecomposition

end AtiyahSinger
