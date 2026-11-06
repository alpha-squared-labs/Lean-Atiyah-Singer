/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalKernelRealization
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalVerticalCommutation
public import AtiyahSinger.Analysis.AssociatedTensorVerticalGreenIdentity
public import AtiyahSinger.Analysis.ClosedJointKernelReduction
public import AtiyahSinger.Analysis.ClosedMetricL2KernelCokernel

/-!
# Regularity of associated joint zero modes (M2319)

The sphere Green relation and kernel projection are lifted to the associated
bundles. Horizontal commutation puts each projected smooth pair in the graph
of the coefficient PDO. Bounded lift realizations and the supplied coefficient
isometries extend this fact to the joint graph closure. Native elliptic
regularity then yields an explicit equivalence from the smooth coefficient
kernel to the joint kernel, through the prescribed evaluation map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u v w w' u' v'

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology tensorTopology continuousSMul_orthogonalSphere
  lieGroup_orthogonalGroup

variable {n r a a' : ℕ} {P : Type u} {B : Type v}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type w) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type w') [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  {F : OrthogonalSphere r → Type u'} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  {F' : OrthogonalSphere r → Type v'} [∀ y, AddCommGroup (F' y)]
  [∀ y, Module ℂ (F' y)] [TopologicalSpace (TotalSpace Unit F')] [IsFiniteRank F']
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')
  (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))
  {μ : MeasureTheory.Measure B} [IsSmoothPositiveMeasure (n := n) μ]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "K" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "U" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z
local notation "U'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 9000000 in
-- The extended limit accommodates the bounded Green lifts and coefficient-kernel regularity.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Bounded Green lifts identify the joint graph kernel with the smooth coefficient kernel
by an explicit linear equivalence. -/
theorem PrincipalPseudodifferentialLocalization.exists_associated_closedJointKernelEquiv
    {d t : ℝ} (C₀ : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (Q : AtlasPseudodifferentialOperator A A' d)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (J : AtlasPseudodifferentialOperator A A 0)
    (hJ : J.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ hσ hσ)
    (Green : AtlasPseudodifferentialOperator A' A t)
    (hGreen : Green.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ' σ hσ' hσ)
    (hQJ : Q.toLinearMap.comp J.toLinearMap = 0)
    (hGQ : Green.toLinearMap.comp Q.toLinearMap = LinearMap.id - J.toLinearMap)
    (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] Q.toLinearMap.ker)
    (he : ∀ (g : G) (y : OrthogonalSphere r) (v : Fin ρ.dimension → ℂ),
      (e (ρ.representation g v)).val.val (g • y) =
        σ.linearMap g y ((e v).val.val y)) :
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
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
    let AU := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
    let AC := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
      (associatedOrthogonalRepresentationAtlas S ρ)
    let AC' := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
      (associatedOrthogonalRepresentationAtlas S ρ)
    let H := C₀.horizontalLift S E A σ E' hσ
    let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
    let V' := associatedSphereTensorVerticalOperator (a := a') S E' A σ hσ A' σ' hσ' Q hQ
    let J₀ := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A σ hσ J hJ
    let J₁ := associatedSphereTensorVerticalOperator (a := a') S E' A σ hσ A σ hσ J hJ
    let G₀ := associatedSphereTensorVerticalOperator (a := a) S E A' σ' hσ' A σ hσ
      Green hGreen
    let Pc := C₀.coefficientOperator S E E' ρ
    ∃ ev : Hom ((πS : Z → B) *ᵖ K) D,
      (∀ (p : P) (y : OrthogonalSphere r) (v : Fin ρ.dimension → ℂ),
        ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
            (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((e v).val.val y)) ∧
      ∃ (Φ : AC.smoothSections ≃ₗ[ℂ] V.ker) (Ψ : AC'.smoothSections ≃ₗ[ℂ] V'.ker),
        (∀ u z, (Φ u).val.val z =
          TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
        (∀ u z, (Ψ u).val.val z =
          TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
        ∀ (N₀ N₁ : SmoothFiniteComplexBundle (n := n) B)
          (k₀ : SmoothHermitianMetric (n := n) (r := N₀.rank) N₀.Fiber)
          (k₁ : SmoothHermitianMetric (n := n) (r := N₁.rank) N₁.Fiber)
          (S₀ : AC.smoothSections ≃ₗ[ℂ] smoothSections (n := n) (r := N₀.rank) N₀.Fiber)
          (S₁ : AC'.smoothSections ≃ₗ[ℂ] smoothSections (n := n) (r := N₁.rank) N₁.Fiber)
          (Pn : PseudodifferentialOperator (n := n) (r := N₀.rank) (q := N₁.rank)
            N₀.Fiber N₁.Fiber μ 1),
          Pn.toLinearMap = S₁.toLinearMap.comp (Pc.toLinearMap.comp S₀.symm.toLinearMap) →
          Pn.IsElliptic →
          ∀ (X₀ X₁ X₂ : Type*) [NormedAddCommGroup X₀] [NormedSpace ℂ X₀]
            [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
            [NormedAddCommGroup X₂] [NormedSpace ℂ X₂]
            (i₀ : AT.smoothSections →ₗ[ℂ] X₀) (i₁ : AU.smoothSections →ₗ[ℂ] X₁)
            (i₂ : AT'.smoothSections →ₗ[ℂ] X₂),
            Function.Injective i₀ →
            ∀ (e₀ : k₀.L2SectionSpace μ →ₗᵢ[ℂ] X₀)
              (e₁ : k₁.L2SectionSpace μ →ₗᵢ[ℂ] X₁),
              (∀ u, e₀ (k₀.smoothToL2 μ (S₀ u)) = i₀ (Φ u).val) →
              (∀ u, e₁ (k₁.smoothToL2 μ (S₁ u)) = i₁ (Ψ u).val) →
              ∀ (P₀ : X₀ →L[ℂ] X₀) (P₁ : X₁ →L[ℂ] X₁) (G₁ : X₂ →L[ℂ] X₀),
                (∀ u, P₀ (i₀ u) = i₀ (J₀ u)) →
                (∀ u, P₁ (i₁ u) = i₁ (J₁ u)) →
                (∀ u, G₁ (i₂ u) = i₀ (G₀ u)) →
                ∀ R : X₀ →ₗ.[ℂ] (X₁ × X₂),
                  R.graph = (i₀.prod ((i₁.comp H).prod (i₂.comp V))).range.topologicalClosure →
                  ∃ κ : Pn.toLinearMap.ker ≃ₗ[ℂ] R.ker,
                    ∀ u, (κ u).val = i₀ (Φ (S₀.symm u.val)).val := by
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
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  intro AT AT' AU AC AC' H V V' J₀ J₁ G₀ Pc
  obtain ⟨ev, hev, Φ, Ψ, hΦ, hΨ, hH⟩ :=
    C₀.exists_horizontalLift_coefficientKernelRealization S E E' A σ hσ A' σ' hσ'
      ρ Q hQ e he
  refine ⟨ev, hev, Φ, Ψ, hΦ, hΨ, ?_⟩
  intro N₀ N₁ k₀ k₁ S₀ S₁ Pn hPn hEll X₀ X₁ X₂
    _ _ _ _ _ _ i₀ i₁ i₂ hi₀ e₀ e₁ he₀ he₁ P₀ P₁ G₁ hP₀ hP₁ hG₁ R hR
  -- The actual lifted kernel projection takes values in the full vertical kernel.
  have hJker (s : AT.smoothSections) : J₀ s ∈ V.ker := by
    let restr := associatedSphereTensorFiberRestriction (a := a) S E A σ hσ
    have hrestrict (p : P) : restr p (J₀ s) =
        tensorSectionOperator (E (projection p)) A.smoothSections A.smoothSections
          J.toLinearMap (restr p s) := by
      apply Subtype.ext
      funext y
      apply (associatedSphereTensorFiberEquiv S E σ p y).injective
      rw [associatedSphereTensorFiberRestriction_apply,
        associatedSphereTensorVerticalOperator_apply]
      rfl
    have htensor (p : P) : tensorSectionOperator (E (projection p))
        A.smoothSections A'.smoothSections Q.toLinearMap (restr p (J₀ s)) = 0 := by
      rw [hrestrict]
      obtain ⟨z, hz⟩ := (tensorSectionEquiv (E (projection p)) A.smoothSections).surjective
        (restr p s)
      rw [← hz]
      simp only [tensorSectionOperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      rw [← LinearMap.lTensor_comp_apply, hQJ, LinearMap.lTensor_zero]
      simp only [LinearMap.zero_apply, map_zero]
    change V (J₀ s) = 0
    apply Subtype.ext
    funext z
    induction z using Quotient.inductionOn with
    | h z =>
      change (V (J₀ s)).val (associatedBundleMk G P (OrthogonalSphere r) z.1 z.2) = 0
      calc
        _ = associatedSphereTensorFiberEquiv S E σ' z.1 z.2
            ((tensorSectionOperator (E (projection z.1)) A.smoothSections A'.smoothSections
              Q.toLinearMap (restr z.1 (J₀ s))).val z.2) :=
          associatedSphereTensorVerticalOperator_apply (a := a)
            S E A σ hσ A' σ' hσ' Q hQ (J₀ s) z.1 z.2
        _ = associatedSphereTensorFiberEquiv S E σ' z.1 z.2 0 :=
          congrArg (fun w ↦ associatedSphereTensorFiberEquiv S E σ' z.1 z.2 (w.val z.2))
            (htensor z.1)
        _ = 0 := map_zero _
  have hcommute (s : AT.smoothSections) : J₁ (H s) = H (J₀ s) :=
    LinearMap.congr_fun (C₀.horizontalLift_vertical_commute S E A σ hσ A σ hσ E' J hJ) s
  have hgreen (s : AT.smoothSections) : G₀ (V s) = s - J₀ s :=
    LinearMap.congr_fun
      (associatedSphereTensorVerticalOperator_comp_eq_id_sub
        S E A σ hσ A' σ' hσ' Q Green J hQ hGreen hJ hGQ) s
  let L := Pn.metricL2ClosedRealization k₀ k₁
  have hL := Pn.metricL2ClosedRealization_realization k₀ k₁
  have hcoefficient (u : AC.smoothSections) : Pn.toLinearMap (S₀ u) =
      S₁ (Pc.toLinearMap u) := by
    rw [hPn]
    change S₁ (Pc.toLinearMap (S₀.symm (S₀ u))) = _
    rw [S₀.symm_apply_apply]
  have hsmoothGraph (u : smoothSections (n := n) (r := N₀.rank) N₀.Fiber) :
      (k₀.smoothToL2 μ u, k₁.smoothToL2 μ (Pn.toLinearMap u)) ∈ L.graph := by
    rw [hL.1]
    apply (Pn.metricL2SmoothCore k₀ k₁).graph.le_topologicalClosure
    let f := LinearEquiv.ofInjective (k₀.smoothToL2 μ) (k₀.smoothToL2_injective μ)
    exact (Pn.metricL2SmoothCore k₀ k₁).mem_graph_iff.mpr
      ⟨f u, rfl, congrArg (fun w ↦ k₁.smoothToL2 μ (Pn.toLinearMap w))
        (f.symm_apply_apply u)⟩
  -- Projection and horizontal commutation give the graph of this same coefficient operator.
  have hproject (s : AT.smoothSections) : (P₀ (i₀ s), P₁ (i₁ (H s))) ∈
      L.graph.map (e₀.toLinearMap.prodMap e₁.toLinearMap) := by
    let c := Φ.symm ⟨J₀ s, hJker s⟩
    have hvalue : (Φ c).val = J₀ s := congrArg Subtype.val (Φ.apply_symm_apply _)
    refine ⟨(k₀.smoothToL2 μ (S₀ c), k₁.smoothToL2 μ (Pn.toLinearMap (S₀ c))),
      hsmoothGraph (S₀ c), ?_⟩
    apply Prod.ext
    · change e₀ (k₀.smoothToL2 μ (S₀ c)) = P₀ (i₀ s)
      rw [he₀, hvalue, hP₀]
    · change e₁ (k₁.smoothToL2 μ (Pn.toLinearMap (S₀ c))) = P₁ (i₁ (H s))
      rw [hcoefficient, he₁, ← hH, hvalue, hP₁, hcommute]
  have hsplit (s : AT.smoothSections) : P₀ (i₀ s) = i₀ s - G₁ (i₂ (V s)) := by
    rw [hP₀, hG₁, hgreen, map_sub]
    abel
  have hreduce : R.ker ≤ L.ker.map e₀.toLinearMap :=
    ker_le_map_of_closedJointGreenSplitting i₀ (i₁.comp H) (i₂.comp V) R hR L hL.2.1
      e₀ e₁ P₀ P₁ G₁ hsplit hproject
  -- Native elliptic regularity identifies the original closed coefficient zeros with smooth zeros.
  obtain ⟨ec, _, hec, _⟩ := Pn.exists_metricL2ClosedRealization_kernel_cokernel_equiv k₀ k₁ hEll
  let f₀ : Pn.toLinearMap.ker →ₗ[ℂ] X₀ :=
    i₀.comp (V.ker.subtype.comp (Φ.toLinearMap.comp
      (S₀.symm.toLinearMap.comp Pn.toLinearMap.ker.subtype)))
  have hf₀ (u : Pn.toLinearMap.ker) : f₀ u ∈ R.ker := by
    have hz : Pc.toLinearMap (S₀.symm u.val) = 0 := by
      apply S₁.injective
      rw [S₁.map_zero]
      have hvalue := congrArg (fun f ↦ f u.val) hPn
      exact hvalue.symm.trans u.property
    have hHz : H (Φ (S₀.symm u.val)).val = 0 :=
      (hH (S₀.symm u.val)).trans
        ((congrArg (fun w ↦ (Ψ w).val) hz).trans (congrArg Subtype.val Ψ.map_zero))
    have hVz : V (Φ (S₀.symm u.val)).val = 0 := (Φ (S₀.symm u.val)).property
    have hgraph : (f₀ u, (0, 0)) ∈ R.graph := by
      rw [hR]
      apply Submodule.le_topologicalClosure
      refine ⟨(Φ (S₀.symm u.val)).val, ?_⟩
      exact Prod.ext rfl (Prod.ext ((congrArg i₁ hHz).trans i₁.map_zero)
        ((congrArg i₂ hVz).trans i₂.map_zero))
    obtain ⟨v, hv, hzero⟩ := R.mem_graph_iff.mp hgraph
    exact R.mem_ker_iff.mpr ⟨v, hv.symm, hzero⟩
  let f := f₀.codRestrict R.ker hf₀
  have hbij : Function.Bijective f := by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply S₀.symm.injective
      apply Φ.injective
      apply Subtype.ext
      exact hi₀ (congrArg Subtype.val huv)
    · intro x
      obtain ⟨c, hc, hcx⟩ := hreduce x.property
      obtain ⟨u, hu⟩ := ec.surjective ⟨c, hc⟩
      have huc : k₀.smoothToL2 μ u.val = c :=
        (hec u).symm.trans (congrArg Subtype.val hu)
      have hsame : e₀ (k₀.smoothToL2 μ u.val) = i₀ (Φ (S₀.symm u.val)).val :=
        (congrArg (fun w ↦ e₀ (k₀.smoothToL2 μ w))
          (S₀.apply_symm_apply u.val).symm).trans (he₀ (S₀.symm u.val))
      refine ⟨u, Subtype.ext ?_⟩
      exact hsame.symm.trans ((congrArg e₀ huc).trans hcx)
  exact ⟨LinearEquiv.ofBijective f hbij, fun _ ↦ rfl⟩

end AtiyahSinger
