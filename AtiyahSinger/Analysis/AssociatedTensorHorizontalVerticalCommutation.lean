/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorBaseExtensionValue
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalLift
public import AtiyahSinger.Analysis.AssociatedTensorLocalizedFiber
public import AtiyahSinger.Analysis.AssociatedTensorLocalHorizontalProperties
public import AtiyahSinger.Analysis.AssociatedTensorVerticalOperator
public import AtiyahSinger.Analysis.AtlasPseudodifferentialPairing

/-!
# Commutation of the horizontal and vertical section maps

Public module ID: M0175.

The principal-localized horizontal section map commutes with the specified
whole equivariant sphere PDO. Distributional Fubini applies to the compact
base localization of the full sphere family. Both compositions use the same
principal atlas, tensor fibers, base plateau, and complete operators.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap Topology

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology tensorTopology continuousSMul_orthogonalSphere
  lieGroup_orthogonalGroup

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  {F' : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F' y)]
  [∀ y, Module ℂ (F' y)] [TopologicalSpace (TotalSpace Unit F')] [IsFiniteRank F']
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')
  (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z


local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z

variable {a' : ℕ} [T2Space B]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "U" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z
local notation "U'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 3200000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A fixed original local horizontal piece commutes with the whole vertical sphere PDO. -/
theorem associatedSphereTensorLocalHorizontalLift_vertical_commute {m d : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (Q : AtlasPseudodifferentialOperator A A' d)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (b : B) (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, χ x = 1)
    (hinput : L.chart.symm '' tsupport L.input.cutoff ⊆ (S.trivialization b).baseSet)
    (houtput : L.chart.symm '' tsupport L.output.cutoff ⊆ (S.trivialization b).baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    letI : TopologicalSpace (TotalSpace Unit U) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI : TopologicalSpace (TotalSpace Unit U') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (associatedSphereTensorVerticalOperator (a := a') S E' A σ hσ A' σ' hσ' Q hQ).comp
      (associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ b χ
        hχ hχsupport houtput) =
    (associatedSphereTensorLocalHorizontalLift (a := a) S E A' σ' E' L hσ' b χ
      hχ hχsupport houtput).comp
        (associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ) := by
  classical
  let := L.output.frame_mem_atlas
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let : TopologicalSpace (TotalSpace Unit U) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let : TopologicalSpace (TotalSpace Unit U') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  let (x : B) : FiniteDimensional ℂ (E' x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a')) E' x
  let (y : OrthogonalSphere r) : FiniteDimensional ℂ (F y) :=
    .of_injective (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).toLinearMap
      (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).injective
  let (y : OrthogonalSphere r) : FiniteDimensional ℂ (F' y) :=
    .of_injective (A'.frameLinearEquiv (A'.covers y).choose y (A'.covers y).choose_spec).toLinearMap
      (A'.frameLinearEquiv (A'.covers y).choose y (A'.covers y).choose_spec).injective
  let H := associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ b χ
    hχ hχsupport houtput
  let H' := associatedSphereTensorLocalHorizontalLift (a := a) S E A' σ' E' L hσ' b χ
    hχ hχsupport houtput
  let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
  let V' := associatedSphereTensorVerticalOperator (a := a') S E' A σ hσ A' σ' hσ' Q hQ
  let R := associatedSphereTensorFiberRestriction (a := a) S E A σ hσ
  let R' := associatedSphereTensorFiberRestriction (a := a) S E A' σ' hσ'
  let K := associatedSphereTensorFiberRestriction (a := a') S E' A σ hσ
  let K' := associatedSphereTensorFiberRestriction (a := a') S E' A' σ' hσ'
  apply LinearMap.ext
  intro w
  change V' (H w) = H' (V w)
  -- The full vertical action restricts to the same tensorized sphere operator.
  have hR (p : P) : R' p (V w) =
      tensorSectionOperator (E (projection p)) A.smoothSections A'.smoothSections
        Q.toLinearMap (R p w) := by
    apply Subtype.ext
    funext y
    apply (associatedSphereTensorFiberEquiv S E σ' p y).injective
    rw [associatedSphereTensorFiberRestriction_apply, associatedSphereTensorVerticalOperator_apply]
    rfl
  obtain ⟨u, huvalue, husmooth, husupport, hulocal⟩ :=
    exists_associatedSphereTensorLocalizedFiberFamily (a := a)
      S E A σ hσ b L.input L.chart_mem_atlas hinput χ hχ hχsupport hχone w
  obtain ⟨u', huvalue', _, _, hulocal'⟩ :=
    exists_associatedSphereTensorLocalizedFiberFamily (a := a)
      S E A' σ' hσ' b L.input L.chart_mem_atlas hinput χ hχ hχsupport hχone (V w)
  -- Localizing only the base commutes with the original vertical PDO, coordinate by coordinate.
  have huQ (z : Xp) (i : Fin a) : u' z i = Q.toLinearMap (u z i) := by
    rw [huvalue, huvalue', map_smul]
    congr 1
    let x := L.chart.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z)
    change associatedSphereTensorLocalFiberCoordinates S E A' b L.input.frame
      L.input.frame_mem_atlas i (fun p ↦ R' p (V w)) x =
        Q.toLinearMap (associatedSphereTensorLocalFiberCoordinates S E A b L.input.frame
          L.input.frame_mem_atlas i (fun p ↦ R p w) x)
    by_cases hx : x ∈ (S.trivialization b).baseSet ∩ L.input.frame.baseSet
    · let := L.input.frame_mem_atlas
      let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
      let φ : E (projection p) →ₗ[ℂ] ℂ := (LinearMap.proj i).comp
        ((EuclideanSpace.equiv (Fin a) ℂ).toLinearMap.comp
          ((L.input.frame.linearEquivAt ℂ x hx.2).toLinearMap.comp
            (LinearEquiv.cast (R := ℂ) (M := E)
              ((S.trivialization b).proj_symm_apply' hx.1)).toLinearMap))
      apply Subtype.ext
      have hc := tensorSectionOperator_contract (E (projection p)) A.smoothSections
        A'.smoothSections Q.toLinearMap (R p w) φ
      simp only [associatedSphereTensorLocalFiberCoordinates, dite_eq_left hx]
      change (fun y ↦ TensorProduct.lid ℂ (F' y)
        (TensorProduct.map φ LinearMap.id ((R' p (V w)).val y))) = _
      rw [hR]
      exact hc
    · simp only [associatedSphereTensorLocalFiberCoordinates, dite_eq_right hx, map_zero]
  have hnormalized (p : P) (hp : projection p ∈ (S.trivialization b).baseSet)
      (hg : (S.trivialization b p).2 = 1) :
      K' p (V' (H w)) = K' p (H' (V w)) := by
    let x := projection p
    -- A dual of the output coefficient turns the horizontal PDO into one Schwartz functional.
    have hdual (φ : E' x →ₗ[ℂ] ℂ) :
        (fun y ↦ TensorProduct.lid ℂ (F' y)
          (TensorProduct.map φ LinearMap.id ((K' p (V' (H w))).val y))) =
        fun y ↦ TensorProduct.lid ℂ (F' y)
          (TensorProduct.map φ LinearMap.id ((K' p (H' (V w))).val y)) := by
      let ex := EuclideanSpace.equiv (Fin n) ℝ
      let φc : E' x →L[ℂ] ℂ := { φ with cont := φ.continuous_of_finiteDimensional }
      let ev : 𝓢(X, EuclideanSpace ℂ (Fin a')) →L[ℂ] EuclideanSpace ℂ (Fin a') :=
        (BoundedContinuousFunction.evalCLM ℂ (L.chart x)).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ X (EuclideanSpace ℂ (Fin a')))
      let T₀ : 𝓢(X, EuclideanSpace ℂ (Fin a)) →L[ℂ] ℂ :=
        if x ∈ L.chart.source then
          (L.output.cutoff (L.chart x) : ℂ) •
            (φc.comp ((L.output.frame.symmL ℂ x).comp (ev.comp L.operator)))
        else 0
      let T₁ : 𝓢(Xp, EuclideanSpace ℂ (Fin a)) →L[ℂ] ℂ :=
        T₀.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ex)
      have hT (s : smoothSections (n := n) (r := a) E) :
          φ ((L.toLinearMap s).val x) = T₁
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ex.symm
              (L.input.localize L.chart_mem_atlas s)) := by
        have heq : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ex
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ex.symm
              (L.input.localize L.chart_mem_atlas s)) =
                L.input.localize L.chart_mem_atlas s := by
          apply SchwartzMap.ext
          intro z
          change L.input.localize L.chart_mem_atlas s (ex.symm (ex z)) = _
          rw [ex.symm_apply_apply]
        change φ (L.output.extendedFunction (L.operator
          (L.input.localize L.chart_mem_atlas s)) x) = _
        simp only [T₁, ContinuousLinearMap.comp_apply, heq]
        by_cases hx : x ∈ L.chart.source
        · simp only [BundleChartCutoff.extendedFunction, ite_eq_left hx, T₀,
            smul_apply, map_smul]
          rfl
        · simp only [BundleChartCutoff.extendedFunction, ite_eq_right hx, T₀,
            zero_apply, map_zero]
      let s : A.smoothSections :=
        ⟨fun y ↦ TensorProduct.lid ℂ (F y)
          (TensorProduct.map φ LinearMap.id ((K p (H w)).val y)), (K p (H w)).property φ⟩
      let t : A'.smoothSections :=
        ⟨fun y ↦ TensorProduct.lid ℂ (F' y)
          (TensorProduct.map φ LinearMap.id ((K' p (H' (V w))).val y)),
            (K' p (H' (V w))).property φ⟩
      have hs : ∀ (y : OrthogonalSphere r) (l : F y →ₗ[ℂ] ℂ),
          ∃ f : 𝓢(Xp, EuclideanSpace ℂ (Fin a)),
            (∀ z i, f z i = l ((u z i).val y)) ∧ l (s.val y) = T₁ f := by
        intro y l
        let RB := associatedSphereTensorCutoffBaseRestriction (a := a)
          S E A σ hσ b χ hχ hχsupport y w
        let sb : smoothSections (n := n) (r := a) E :=
          ⟨fun x ↦ TensorProduct.lid ℂ (E x)
            (TensorProduct.map l LinearMap.id (RB.val x)), RB.property l⟩
        let f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ex.symm
          (L.input.localize L.chart_mem_atlas sb)
        refine ⟨f, ?_, ?_⟩
        · intro z i
          have hv := hulocal y l z i
          exact hv
        · have hK (y : OrthogonalSphere r) : (K p (H w)).val y =
              TensorProduct.comm ℂ (F y) (E' x)
                ((associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ
                  b χ hχ hχsupport y w).val x) := by
            apply (associatedSphereTensorFiberEquiv S E' σ p y).injective
            rw [associatedSphereTensorFiberRestriction_apply,
              associatedSphereTensorLocalHorizontalLift_apply,
              associatedSphereTensorBaseExtension_apply_mk S E' σ b p y hp hg]
          change l (TensorProduct.lid ℂ (F y)
            (TensorProduct.map φ LinearMap.id ((K p (H w)).val y))) = _
          have hcross (v : F y ⊗[ℂ] E' x) :
              l (TensorProduct.lid ℂ (F y) (TensorProduct.map φ LinearMap.id
                (TensorProduct.comm ℂ (F y) (E' x) v))) =
              φ (TensorProduct.lid ℂ (E' x) (TensorProduct.map l LinearMap.id v)) := by
            induction v using TensorProduct.inductionOn with
            | tmul v e =>
              simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
                TensorProduct.lid_tmul, map_smul]
              exact mul_comm _ _
            | add v e hv he => simpa only [map_add] using congrArg₂ (· + ·) hv he
          rw [hK, hcross]
          have hc := congrFun (tensorSectionOperator_contract (F y)
            (smoothSections E) (smoothSections E') L.toLinearMap RB l) x
          change φ (TensorProduct.lid ℂ (E' x)
            (TensorProduct.map l LinearMap.id
              ((tensorSectionOperator (F y) (smoothSections E) (smoothSections E')
                L.toLinearMap RB).val x))) = _
          rw [hc]
          exact hT sb
      have ht : ∀ (y : OrthogonalSphere r) (l : F' y →ₗ[ℂ] ℂ),
          ∃ f : 𝓢(Xp, EuclideanSpace ℂ (Fin a)),
            (∀ z i, f z i = l ((Q.toLinearMap (u z i)).val y)) ∧ l (t.val y) = T₁ f := by
        intro y l
        let RB := associatedSphereTensorCutoffBaseRestriction (a := a)
          S E A' σ' hσ' b χ hχ hχsupport y (V w)
        let sb : smoothSections (n := n) (r := a) E :=
          ⟨fun x ↦ TensorProduct.lid ℂ (E x)
            (TensorProduct.map l LinearMap.id (RB.val x)), RB.property l⟩
        let f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ex.symm
          (L.input.localize L.chart_mem_atlas sb)
        refine ⟨f, ?_, ?_⟩
        · intro z i
          have hv := hulocal' y l z i
          rw [huQ] at hv
          exact hv
        · have hK (y : OrthogonalSphere r) : (K' p (H' (V w))).val y =
              TensorProduct.comm ℂ (F' y) (E' x)
                ((associatedSphereTensorHorizontalFamily (a := a) S E A' σ' E' L hσ'
                  b χ hχ hχsupport y (V w)).val x) := by
            apply (associatedSphereTensorFiberEquiv S E' σ' p y).injective
            rw [associatedSphereTensorFiberRestriction_apply,
              associatedSphereTensorLocalHorizontalLift_apply,
              associatedSphereTensorBaseExtension_apply_mk S E' σ' b p y hp hg]
          change l (TensorProduct.lid ℂ (F' y)
            (TensorProduct.map φ LinearMap.id ((K' p (H' (V w))).val y))) = _
          have hcross (v : F' y ⊗[ℂ] E' x) :
              l (TensorProduct.lid ℂ (F' y) (TensorProduct.map φ LinearMap.id
                (TensorProduct.comm ℂ (F' y) (E' x) v))) =
              φ (TensorProduct.lid ℂ (E' x) (TensorProduct.map l LinearMap.id v)) := by
            induction v using TensorProduct.inductionOn with
            | tmul v e =>
              simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
                TensorProduct.lid_tmul, map_smul]
              exact mul_comm _ _
            | add v e hv he => simpa only [map_add] using congrArg₂ (· + ·) hv he
          rw [hK, hcross]
          have hc := congrFun (tensorSectionOperator_contract (F' y)
            (smoothSections E) (smoothSections E') L.toLinearMap RB l) x
          change φ (TensorProduct.lid ℂ (E' x)
            (TensorProduct.map l LinearMap.id
              ((tensorSectionOperator (F' y) (smoothSections E) (smoothSections E')
                L.toLinearMap RB).val x))) = _
          rw [hc]
          exact hT sb
      -- Distributional Fubini retains the whole sphere operator and its full remainder.
      have hQt := Q.apply_schwartz_parameter_pairing A A' T₁ u husmooth
        ((EuclideanSpace.equiv (Fin n) ℝ) '' tsupport L.input.cutoff)
        (L.input.compact_support.image (EuclideanSpace.equiv (Fin n) ℝ).continuous)
        husupport s t hs ht
      have hKV : K' p (V' (H w)) =
          tensorSectionOperator (E' x) A.smoothSections A'.smoothSections
            Q.toLinearMap (K p (H w)) := by
        apply Subtype.ext
        funext y
        apply (associatedSphereTensorFiberEquiv S E' σ' p y).injective
        rw [associatedSphereTensorFiberRestriction_apply,
          associatedSphereTensorVerticalOperator_apply]
        rfl
      rw [hKV]
      exact (tensorSectionOperator_contract (E' x) A.smoothSections A'.smoothSections
        Q.toLinearMap (K p (H w)) φ).trans (congrArg Subtype.val hQt)
    -- The original finite base frame separates the two actual tensor-valued sections.
    let e := (trivializationAt (EuclideanSpace ℂ (Fin a')) E' x).linearEquivAt ℂ x
      (mem_baseSet_trivializationAt (EuclideanSpace ℂ (Fin a')) E' x)
    let ec : E' x ≃ₗ[ℂ] (Fin a' → ℂ) :=
      e.trans (EuclideanSpace.equiv (Fin a') ℂ).toLinearEquiv
    apply Subtype.ext
    funext y
    let et := (TensorProduct.congr ec (LinearEquiv.refl ℂ (F' y))).trans
      ((TensorProduct.comm ℂ (Fin a' → ℂ) (F' y)).trans
        (TensorProduct.piScalarRight ℂ ℂ (F' y) (Fin a')))
    have hcoord (v : E' x ⊗[ℂ] F' y) (i : Fin a') : et v i =
        TensorProduct.lid ℂ (F' y)
          (TensorProduct.map ((LinearMap.proj i).comp ec.toLinearMap) LinearMap.id v) := by
      induction v using TensorProduct.inductionOn with
      | tmul u v => simp [et]
      | add u v hu hv => simp only [map_add, Pi.add_apply, hu, hv]
    apply et.injective
    funext i
    rw [hcoord, hcoord]
    exact congrFun (hdual ((LinearMap.proj i).comp ec.toLinearMap)) y
  -- Every point over the principal chart has a normalized representative in that same chart.
  apply Subtype.ext
  funext z
  by_cases hx : πS z ∈ (S.trivialization b).baseSet
  · let t := associatedSphereTrivialization S b
    have hbase : t.baseSet = (S.trivialization b).baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization b) (S.equivariant b)).choose_spec.1
    have hz : z ∈ t.source := t.mem_source.mpr (hbase.symm ▸ hx)
    have hfst : (t z).1 = πS z := t.proj_toFun z hz
    let p := (S.trivialization b).toOpenPartialHomeomorph.symm (πS z, 1)
    have hp : projection p = πS z := (S.trivialization b).proj_symm_apply' hx
    have hg : (S.trivialization b p).2 = 1 :=
      congrArg Prod.snd ((S.trivialization b).apply_symm_apply' hx)
    have hrep : associatedBundleMk G P (OrthogonalSphere r) p (t z).2 = z := by
      have h := (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization b) (S.equivariant b)).choose_spec.2.2 (πS z) (t z).2 hx
      have hpair : (πS z, (t z).2) = t z := Prod.ext hfst.symm rfl
      rw [hpair] at h
      exact h.symm.trans (t.left_inv hz)
    have heq := congrArg (fun R ↦ R.val (t z).2)
      (hnormalized p (hp.symm ▸ hx) hg)
    have hval := congrArg (associatedSphereTensorFiberEquiv S E' σ' p (t z).2) heq
    rw [associatedSphereTensorFiberRestriction_apply,
      associatedSphereTensorFiberRestriction_apply] at hval
    exact hrep ▸ hval
  · -- Outside the base output support the entire restricted family vanishes before Q acts.
    have hout : πS z ∉ L.chart.symm '' tsupport L.output.cutoff :=
      fun h ↦ hx (houtput h)
    have hright : (H' (V w)).val z = 0 :=
      associatedSphereTensorLocalHorizontalLift_apply_eq_zero (a := a)
        S E A' σ' E' L hσ' b χ hχ hχsupport houtput z hout (V w)
    rw [hright]
    obtain ⟨⟨p, y⟩, rfl⟩ := Quotient.exists_rep z
    have hzero : K p (H w) = 0 := by
      apply Subtype.ext
      funext y'
      apply (associatedSphereTensorFiberEquiv S E' σ p y').injective
      rw [associatedSphereTensorFiberRestriction_apply]
      change (H w).val (associatedBundleMk G P (OrthogonalSphere r) p y') =
        associatedSphereTensorFiberEquiv S E' σ p y' 0
      rw [map_zero]
      exact associatedSphereTensorLocalHorizontalLift_apply_eq_zero (a := a)
        S E A σ E' L hσ b χ hχ hχsupport houtput
          (associatedBundleMk G P (OrthogonalSphere r) p y') hout w
    change (V' (H w)).val (associatedBundleMk G P (OrthogonalSphere r) p y) = 0
    rw [associatedSphereTensorVerticalOperator_apply]
    change associatedSphereTensorFiberEquiv S E' σ' p y
      ((tensorSectionOperator (E' (projection p)) A.smoothSections A'.smoothSections
        Q.toLinearMap (K p (H w))).val y) = 0
    rw [hzero, map_zero]
    exact map_zero _

variable [SecondCountableTopology B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The global horizontal map from one fixed principal localization commutes with the same Q. -/
theorem PrincipalPseudodifferentialLocalization.horizontalLift_vertical_commute {m d : ℝ}
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m)
    (Q : AtlasPseudodifferentialOperator A A' d)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ') :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    letI : TopologicalSpace (TotalSpace Unit U) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI : TopologicalSpace (TotalSpace Unit U') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (associatedSphereTensorVerticalOperator (a := a') S E' A σ hσ A' σ' hσ' Q hQ).comp
      (C.horizontalLift S E A σ E' hσ) =
    (C.horizontalLift S E A' σ' E' hσ').comp
      (associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let : TopologicalSpace (TotalSpace Unit U) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let : TopologicalSpace (TotalSpace Unit U') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  -- The same finite family and the same base-only plateaus occur in both compositions.
  apply LinearMap.ext
  intro w
  simp only [LinearMap.comp_apply, PrincipalPseudodifferentialLocalization.horizontalLift,
    LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hinput : (C.piece j).chart.symm '' tsupport (C.piece j).input.cutoff ⊆
      (S.trivialization (C.center j)).baseSet := by
    rintro x ⟨y, hy, rfl⟩
    exact C.piece_support j ⟨y, Or.inr hy, rfl⟩
  have houtput : (C.piece j).chart.symm '' tsupport (C.piece j).output.cutoff ⊆
      (S.trivialization (C.center j)).baseSet := by
    rintro x ⟨y, hy, rfl⟩
    exact C.piece_support j ⟨y, Or.inl hy, rfl⟩
  exact DFunLike.congr_fun
    (associatedSphereTensorLocalHorizontalLift_vertical_commute (a := a)
      S E A σ hσ A' σ' hσ' E' (C.piece j) Q hQ (C.center j)
      (C.inputCutoff j) (C.smooth_inputCutoff j) (C.inputCutoff_support j)
      (C.inputCutoff_eq_one j) hinput houtput) w

end AtiyahSinger
