/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedFiberRestriction
public import AtiyahSinger.Geometry.AssociatedSphereTensorBundle
public import AtiyahSinger.Geometry.TensorSectionOperator

/-!
# Full fiber restriction of associated tensor sections

Public module ID: M0142.

The base-first tensor atlas restricts to tensor-valued sections on every
entire sphere fiber. Every dual contraction in the fixed base fiber is smooth
in the sphere atlas, so the restriction belongs to the finite tensor section
space.

The proof uses tensor-chart coordinates at a fixed principal point, contracts
the finite base coordinates, and removes the principal group coordinate by
its inverse smooth action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

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

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in
-- Tensor-chart contractions and the inverse action require a larger elaboration budget.

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction preserves the full sphere and every original smooth dual contraction. -/
theorem exists_associatedSphereTensorFiberRestriction (p : P) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∃ R : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections →ₗ[ℂ]
        dualTensorSections (E (projection p)) A.smoothSections,
      ∀ (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections)
        (y : OrthogonalSphere r),
        associatedSphereTensorFiberEquiv S E σ p y ((R w).val y) =
          w.val (associatedBundleMk G P (OrthogonalSphere r) p y) := by
  classical
  let := lieGroup_orthogonalGroup r
  -- Recover smoothness by the inverse of the same smooth group action.
  have hsmooth_of_action (g : G) (s : ∀ y : OrthogonalSphere r, F y)
      (hsg : A.IsSmoothSection (σ.dependentSectionLinearMap g s)) :
      A.IsSmoothSection s := by
    as_aux_lemma =>
      let sg := σ.dependentSectionLinearMap g s
      let props := σ.atlasSmoothSectionAction_properties 𝓘(ℝ, OrthogonalGroupModel r) A hσ
      -- Apply the inverse action to the already smooth transformed section.
      have hback := props.1 g⁻¹ ⟨sg, hsg⟩
      -- Cancel inverse-after-forward action by the original representation laws.
      have heq : σ.dependentSectionLinearMap g⁻¹ sg = s := by
        -- Expose the original forward section before forming the local algebraic proof.
        change σ.dependentSectionLinearMap g⁻¹ (σ.dependentSectionLinearMap g s) = s
        as_aux_lemma =>
          let ρ : Representation ℂ G (∀ y : OrthogonalSphere r, F y) :=
            { toFun := σ.dependentSectionLinearMap
              map_one' := props.2.1
              map_mul' := props.2.2 }
          exact ρ.inv_self_apply g s
      -- Use the section identity to recover smoothness of the original section.
      change A.IsSmoothSection (σ.dependentSectionLinearMap g⁻¹ sg) at hback
      rw [heq] at hback
      exact hback
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let l := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let d := linearModelDiffeomorph l Z
  let := linearModelChartedSpace l Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  let AE := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
  have hq : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ q :=
    (smoothAssociatedSphereProjection S).contMDiff.comp d.symm.contMDiff
  let AC := AE.pullback q hq
  let t := associatedSphereTrivialization S
  let e (y : OrthogonalSphere r) := associatedSphereTensorFiberEquiv S E σ p y
  let R₀ : AT.smoothSections →ₗ[ℂ]
      (∀ y : OrthogonalSphere r, E (projection p) ⊗[ℂ] F y) :=
    LinearMap.pi fun y ↦ (e y).symm.toLinearMap.comp
      ((LinearMap.proj (associatedBundleMk G P (OrthogonalSphere r) p y)).comp
        AT.smoothSections.subtype)
  have hR (w : AT.smoothSections) (y : OrthogonalSphere r) :
      e y (R₀ w y) = w.val (associatedBundleMk G P (OrthogonalSphere r) p y) :=
    (e y).apply_symm_apply _
  -- Smoothness depends only on the fiber evaluation identity of the restriction map.
  have hsmooth
      (R₀ : AT.smoothSections →ₗ[ℂ]
        (∀ y : OrthogonalSphere r, E (projection p) ⊗[ℂ] F y))
      (hR : ∀ (w : AT.smoothSections) (y : OrthogonalSphere r),
        e y (R₀ w y) = w.val (associatedBundleMk G P (OrthogonalSphere r) p y))
      (w : AT.smoothSections) (φ : E (projection p) →ₗ[ℂ] ℂ) :
      A.IsSmoothSection (fun y ↦ TensorProduct.lid ℂ (F y)
        (TensorProduct.map φ LinearMap.id (R₀ w y))) := by
    as_aux_lemma =>
      let b := projection p
      let g : G := (S.trivialization b p).2
      let s (y : OrthogonalSphere r) : F y := TensorProduct.lid ℂ (F y)
        (TensorProduct.map φ LinearMap.id (R₀ w y))
      let sg := σ.dependentSectionLinearMap g s
      let c := trivializationAt (EuclideanSpace ℂ (Fin a)) E b
      have hc : MemTrivializationAtlas c := inferInstance
      have hcb : b ∈ c.baseSet := mem_baseSet_trivializationAt _ _ b
      let ec := AE.frameLinearEquiv ⟨c, hc⟩ b hcb
      let v (i : Fin a) : E b := ec.symm (Pi.single i 1)
      have hφ (u : E b) : φ u = ∑ i, (c ⟨b, u⟩).2 i * φ (v i) := by
        have hu : (∑ i, ec u i • v i) = u := by
          apply ec.injective
          simp only [map_sum, map_smul, v, LinearEquiv.apply_symm_apply]
          funext k
          simp [Pi.single_apply]
        have h := congrArg φ hu
        change φ u = ∑ i, ec u i * φ (v i)
        simpa only [map_sum, map_smul, smul_eq_mul] using h.symm
      have htotal (y : OrthogonalSphere r) :
          (⟨y, sg y⟩ : TotalSpace Unit F) =
            ⟨g • (g⁻¹ • y), σ.linearMap g (g⁻¹ • y) (s (g⁻¹ • y))⟩ := by
        let transport : ∀ {x z : OrthogonalSphere r}, x = z → F x →ₗ[ℂ] F z :=
          fun {x z} h ↦ by
            subst z
            exact LinearMap.id
        have htransport {x z : OrthogonalSphere r} (h : x = z) (u : F x) :
            (⟨z, transport h u⟩ : TotalSpace Unit F) = ⟨x, u⟩ := by
          subst z
          rfl
        exact htransport (smul_inv_smul g y) _
      have hsg : A.IsSmoothSection sg := by
        as_aux_lemma =>
          intro j
          let f (y : OrthogonalSphere r) : Z :=
            associatedBundleMk G P (OrthogonalSphere r) p (g⁻¹ • y)
          have hf : ContMDiff (𝓡 r) (𝓡 (n + r)) ∞ f :=
            d.contMDiff.comp ((smoothAssociatedSphereFiberInclusion S p).contMDiff.comp
              (orthogonalSphereDiffeomorph r g⁻¹).contMDiff)
          have htb : (t b).baseSet = (S.trivialization b).baseSet :=
            (exists_associatedBundleTrivialization S.toIsPrincipalBundle
              (S.trivialization b) (S.equivariant b)).choose_spec.1
          have ht (y : OrthogonalSphere r) : t b (f y) = (b, y) := by
            have h := (exists_associatedBundleTrivialization S.toIsPrincipalBundle
              (S.trivialization b) (S.equivariant b)).choose_spec.2.1
              p (g⁻¹ • y) (S.mem_baseSet b)
            have h' : t b (f y) = (b, g • (g⁻¹ • y)) := h
            simpa only [smul_inv_smul] using h'
          have hbase (y : OrthogonalSphere r) (hy : y ∈ (A.chart j).baseSet) :
              f y ∈ (AD.chart (b, j)).baseSet := by
            have hADbase : (AD.chart (b, j)).baseSet =
                (t b).source ∩ (t b) ⁻¹' (Set.univ ×ˢ (A.chart j).baseSet) :=
              (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
                (S.trivialization b) (S.equivariant b) (A.chart j) (A.linear j)).choose_spec.1
            rw [hADbase]
            refine ⟨(t b).mem_source.mpr (htb.symm ▸ S.mem_baseSet b), ?_⟩
            rw [Set.mem_preimage, ht]
            exact ⟨Set.mem_univ b, hy⟩
          have hTbase (y : OrthogonalSphere r) (hy : y ∈ (A.chart j).baseSet) :
              f y ∈ (AT.chart (⟨c, hc⟩, (b, j))).baseSet := by
            have hEbase : f y ∈ (AC.chart ⟨c, hc⟩).baseSet := by
              have h := (AE.exists_pullbackChart q ⟨c, hc⟩).choose_spec.1
              exact h.symm ▸ hcb
            exact (exists_tensor_trivialization (AC.chart ⟨c, hc⟩) (AD.chart (b, j))
              (AC.linear ⟨c, hc⟩) (AD.linear (b, j))).choose_spec.1.symm ▸
                ⟨hEbase, hbase y hy⟩
          -- Finite base-coordinate contraction commutes with the actual tensor chart.
          have hformula (y : OrthogonalSphere r) (hy : y ∈ (A.chart j).baseSet)
              (z : E b ⊗[ℂ] F (g⁻¹ • y)) (k : Fin (A.rank j)) :
              (A.chart j ⟨g • (g⁻¹ • y), σ.linearMap g (g⁻¹ • y)
                (TensorProduct.lid ℂ (F (g⁻¹ • y))
                  (TensorProduct.map φ LinearMap.id z))⟩).2 k =
                ∑ i, φ (v i) * (AT.chart (⟨c, hc⟩, (b, j))
                  ⟨f y, e (g⁻¹ • y) z⟩).2 (finProdFinEquiv (i, k)) := by
            as_aux_lemma =>
              have hg : g • (g⁻¹ • y) ∈ (A.chart j).baseSet := by
                simpa only [smul_inv_smul] using hy
              induction z using TensorProduct.inductionOn with
              | tmul u z =>
                simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul,
                  map_smul]
                have hlin := congrFun ((A.linear j _ hg).map_smul (φ u)
                  (σ.linearMap g (g⁻¹ • y) z)) k
                change (A.chart j ⟨_, φ u • σ.linearMap g (g⁻¹ • y) z⟩).2 k = _ at hlin
                rw [hlin, hφ]
                change (∑ i, (c ⟨b, u⟩).2 i * φ (v i)) *
                  (A.chart j ⟨_, σ.linearMap g (g⁻¹ • y) z⟩).2 k = _
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i _
                have h := associatedSphereTensorBundleAtlas_chart_tmul (a := a) S E A σ hσ c hc
                  b j p (g⁻¹ • y) (S.mem_baseSet b) hcb (hbase y hy) u z i k
                change (AT.chart (⟨c, hc⟩, (b, j))
                  ⟨f y, e (g⁻¹ • y) (u ⊗ₜ[ℂ] z)⟩).2 _ = _ at h
                rw [h]
                ring
              | add z z' hz hz' =>
                have hA := congrFun ((A.linear j _ hg).map_add
                  (σ.linearMap g (g⁻¹ • y) (TensorProduct.lid ℂ (F (g⁻¹ • y))
                    (TensorProduct.map φ LinearMap.id z)))
                  (σ.linearMap g (g⁻¹ • y) (TensorProduct.lid ℂ (F (g⁻¹ • y))
                    (TensorProduct.map φ LinearMap.id z')))) k
                have hT := (AT.linear (⟨c, hc⟩, (b, j)) (f y) (hTbase y hy)).map_add
                  (e (g⁻¹ • y) z) (e (g⁻¹ • y) z')
                simp only [map_add] at hA ⊢
                rw [hA, hT]
                change _ + _ = ∑ i, φ (v i) * (_ + _)
                rw [hz, hz']
                simp only [mul_add, Finset.sum_add_distrib]
          apply contMDiffOn_pi_space.mpr
          intro k
          have hs : ContMDiffOn (𝓡 r) 𝓘(ℝ, ℂ) ∞
              (fun y ↦ ∑ i, φ (v i) * (AT.chart (⟨c, hc⟩, (b, j))
                ⟨f y, w.val (f y)⟩).2 (finProdFinEquiv (i, k))) (A.chart j).baseSet := by
            apply contMDiffOn_finsetSum
            intro i _
            have h := contMDiffOn_pi_space.mp
              ((w.property (⟨c, hc⟩, (b, j))).comp hf.contMDiffOn hTbase)
              (finProdFinEquiv (i, k))
            exact (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
              (contMDiffOn_const.prodMk_space h)
          apply hs.congr
          intro y hy
          have h := hformula y hy (R₀ w (g⁻¹ • y)) k
          rw [hR] at h
          exact (congrArg (fun z : TotalSpace Unit F ↦ (A.chart j z).2 k)
            (htotal y)).trans h
      -- The actual inverse smooth action cancels the fixed principal coordinate.
      exact hsmooth_of_action g s hsg
  let R : AT.smoothSections →ₗ[ℂ] dualTensorSections (E (projection p)) A.smoothSections :=
    { toFun w := ⟨R₀ w, hsmooth R₀ hR w⟩
      map_add' u v := Subtype.ext (R₀.map_add u v)
      map_smul' c u := Subtype.ext (R₀.map_smul c u) }
  exact ⟨R, hR⟩

set_option maxSynthPendingDepth 30 in
/-- The full sphere restriction in the original tensor and quotient-fiber coordinates. -/
def associatedSphereTensorFiberRestriction (p : P) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections →ₗ[ℂ]
      dualTensorSections (E (projection p)) A.smoothSections :=
  (exists_associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p).choose

set_option maxSynthPendingDepth 30 in
/-- The restriction evaluates through the specified fiber equivalence at every sphere point. -/
theorem associatedSphereTensorFiberRestriction_apply (p : P) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections)
      (y : OrthogonalSphere r),
      associatedSphereTensorFiberEquiv S E σ p y
          ((associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w).val y) =
        w.val (associatedBundleMk G P (OrthogonalSphere r) p y) :=
  (exists_associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p).choose_spec

end AtiyahSinger
