/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantPseudodifferentialOperator
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential
public import AtiyahSinger.Geometry.EquivariantAtlasSmoothing

/-!
# The original equivariant action on variable-rank atlas operators

Public module ID: M0466.

The section action is the actual formula (g.s)(x) = g.s(g inverse.x), with
only the equality transport between those two names for the same base point.
The given jointly smooth moving-frame action preserves the original atlas
smooth sections and gives their usual complex representation. Equivariance
of an atlas PDO means intertwining these exact two representations.

The generic dependent-section map is the same formula as the earlier native
fixed-rank section action, extended to the original Unit-model bundle family.
It is an implementation adapter, not a second notion of section action.
The native comparison retains the same PDO, actual fiber values, density,
bundle actions and identity transport of smooth sections.

Source: Lawson--Michelsohn, Spin Geometry, III.9 Definition 9.1, printed p.211,
for the section action and operator equivariance. Applying that condition to
PDOs and allowing locally varying ranks uses the same standard definition.
No group compactness, invariant density, fiber metric, principal-symbol
equivariance, or new representation is assumed in defining equivariance.
The compactness of the base belongs to the existing global atlas PDO type.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

section OriginalAtlas

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type*} [TopologicalSpace M] [MulAction G M] [ContinuousSMul G M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- The actual moving-fiber action on dependent sections, without a global rank choice. -/
def ComplexBundle.EquivariantStructure.dependentSectionLinearMap
    (σ : EquivariantStructure G E) (g : G) : (∀ x, E x) →ₗ[ℂ] (∀ x, E x) := by
  -- Transport changes only the fiber index along the original action identity.
  let transport : ∀ {x y : M}, x = y → E x →ₗ[ℂ] E y := fun {x y} h ↦ by
    subst y
    exact LinearMap.id
  exact LinearMap.pi fun x ↦
    (transport (smul_inv_smul g x)).comp
      ((σ.linearMap g (g⁻¹ • x)).comp (LinearMap.proj (g⁻¹ • x)))

variable {VG HG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG) [ChartedSpace HG G]
  {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hG : IsManifold IG ∞ G]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

include hG hM hAction in
set_option linter.unusedSectionVars false in
/-- Joint smoothness preserves the original atlas section space and its actual action laws. -/
theorem ComplexBundle.EquivariantStructure.atlasSmoothSectionAction_properties
    (σ : EquivariantStructure G E) (A : SmoothComplexBundleAtlas (n := n) E)
    (hσ : σ.IsSmoothAtlas IG A) :
    (∀ (g : G) (s : A.smoothSections),
      A.IsSmoothSection (σ.dependentSectionLinearMap g s.val)) ∧
      σ.dependentSectionLinearMap 1 = LinearMap.id ∧
      ∀ g h : G, σ.dependentSectionLinearMap (g * h) =
        (σ.dependentSectionLinearMap g).comp (σ.dependentSectionLinearMap h) := by
  /- Stage 1: near x, choose an original source frame near g inverse.x
  and an original target frame near x. Expand the input section in the
  source frame. The moving-overlap columns in hσ and the smooth inverse
  base action make every output coordinate a finite sum of smooth terms.
  This proves smoothness in the given target atlas; no common fiber rank
  or artificial identification between disjoint fiber spaces is used.
  Stage 2: the identity and multiplication equations of σ hold in its
  original total space. Evaluate them on the section at the required
  inverse-moved point. Equality induction removes precisely the dependent
  index transports, and pointwise extensionality gives the displayed laws.
  This is the same geometric formula as the existing fixed-rank action;
  no section-space topology, average or operator property is required. -/
  classical
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  let transport : ∀ {x y : M}, x = y → E x →ₗ[ℂ] E y := fun {x y} h ↦ by
    subst y
    exact LinearMap.id
  have htransport {x y : M} (hxy : x = y) (v : E x) :
      (⟨y, transport hxy v⟩ : TotalSpace Unit E) = ⟨x, v⟩ := by
    subst y
    rfl
  -- Record the original action formula as an equality of total vectors.
  have htotal (g : G) (s : ∀ x, E x) (x : M) :
      (⟨x, σ.dependentSectionLinearMap g s x⟩ : TotalSpace Unit E) =
        g • (⟨g⁻¹ • x, s (g⁻¹ • x)⟩ : TotalSpace Unit E) := by
    change (⟨x, transport (smul_inv_smul g x)
      (σ.linearMap g (g⁻¹ • x) (s (g⁻¹ • x)))⟩ : TotalSpace Unit E) = _
    exact htransport (smul_inv_smul g x) _
  refine ⟨?_, ?_, ?_⟩
  · intro g s j x hx
    obtain ⟨i, hix⟩ := A.covers (g⁻¹ • x)
    let U : Set M := {y | g⁻¹ • y ∈ (A.chart i).baseSet ∧ y ∈ (A.chart j).baseSet}
    have hk : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun y : M ↦ g⁻¹ • y) :=
      ContMDiffSMul.contMDiff_const_smul (I := IG) g⁻¹
    have hopen : IsOpen U :=
      ((A.chart i).open_baseSet.preimage hk.continuous).inter (A.chart j).open_baseSet
    have hsource := (s.property i).comp hk.contMDiffOn
      (show Set.MapsTo (fun y : M ↦ g⁻¹ • y) U (A.chart i).baseSet from fun _ hy ↦ hy.1)
    -- Restrict each given smooth moving-frame column to the original inverse base action.
    let column (k : Fin (A.rank i)) (y : M) : Fin (A.rank j) → ℂ :=
      if hy : g⁻¹ • y ∈ (A.chart i).baseSet then
        (A.chart j ⟨g • (g⁻¹ • y),
          σ.linearMap g (g⁻¹ • y)
            ((A.frameLinearEquiv i (g⁻¹ • y) hy).symm (Pi.single k 1))⟩).2
      else 0
    have hcolumns (k : Fin (A.rank i)) :
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, Fin (A.rank j) → ℂ) ∞ (column k) U := by
      apply (hσ i j k).comp (contMDiff_const.prodMk hk).contMDiffOn
      intro y hy
      exact ⟨hy.1, by simpa only [smul_inv_smul] using hy.2⟩
    have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
        (fun y ↦ ∑ k : Fin (A.rank i),
          (A.chart i ⟨g⁻¹ • y, s.val (g⁻¹ • y)⟩).2 k • column k y) U := by
      apply contMDiffOn_finsetSum
      intro k _
      have hcoeff := (contMDiffOn_pi_space.mp hsource) k
      have hmul : ContDiff ℝ ∞
          (fun p : ℂ × (Fin (A.rank j) → ℂ) ↦ p.1 • p.2) := contDiff_smul
      exact hmul.contMDiff.comp_contMDiffOn (hcoeff.prodMk_space (hcolumns k))
    -- Reconstruct the input in its own frame; no equality of chart ranks is used.
    have hlocal := hsum.congr
      (f₁ := fun y ↦ (A.chart j ⟨y, σ.dependentSectionLinearMap g s.val y⟩).2) ?_
    · exact (hlocal.contMDiffAt (hopen.mem_nhds ⟨hix, hx⟩)).contMDiffWithinAt
    · intro y hy
      have hmoved : g • (g⁻¹ • y) ∈ (A.chart j).baseSet := by
        simpa only [smul_inv_smul] using hy.2
      let L := (A.frameLinearEquiv j (g • (g⁻¹ • y)) hmoved).toLinearMap.comp
        ((σ.linearMap g (g⁻¹ • y)).comp
          (A.frameLinearEquiv i (g⁻¹ • y) hy.1).symm.toLinearMap)
      have hexpand := congrArg L ((Pi.basisFun ℂ (Fin (A.rank i))).sum_repr
        ((A.frameLinearEquiv i (g⁻¹ • y) hy.1) (s.val (g⁻¹ • y))))
      simp [L, map_sum, map_smul] at hexpand
      have hcoordinates := congrArg (fun z : TotalSpace Unit E ↦ (A.chart j z).2)
        (htotal g s.val y)
      exact hcoordinates.trans (by
        change (A.chart j ⟨g • (g⁻¹ • y),
          σ.linearMap g (g⁻¹ • y) (s.val (g⁻¹ • y))⟩).2 = _
        simpa [column, hy.1, SmoothComplexBundleAtlas.frameLinearEquiv] using hexpand.symm)
  · -- The identity law holds before restricting to the smooth subspace.
    apply LinearMap.ext
    intro s
    funext x
    apply TotalSpace.mk_injective (F := Unit) x
    have hbase : (1 : G)⁻¹ • x = x := by rw [inv_one, one_smul]
    exact (htotal 1 s x).trans ((one_smul G _).trans
      (congrArg (fun y : M ↦ (⟨y, s y⟩ : TotalSpace Unit E)) hbase))
  · -- Composition uses the same source point h⁻¹*(g⁻¹*x) on both sides.
    intro g h
    apply LinearMap.ext
    intro s
    funext x
    apply TotalSpace.mk_injective (F := Unit) x
    change (⟨x, σ.dependentSectionLinearMap (g * h) s x⟩ : TotalSpace Unit E) =
      ⟨x, σ.dependentSectionLinearMap g (σ.dependentSectionLinearMap h s) x⟩
    rw [htotal, htotal, htotal, mul_smul]
    apply congrArg (fun z : TotalSpace Unit E ↦ g • h • z)
    apply congrArg (fun y : M ↦ (⟨y, s y⟩ : TotalSpace Unit E))
    rw [mul_inv_rev, mul_smul]


/-- The original geometric representation on the same variable-rank atlas smooth sections. -/
def ComplexBundle.EquivariantStructure.atlasSmoothSectionRepresentation
    (σ : EquivariantStructure G E) (A : SmoothComplexBundleAtlas (n := n) E)
    (hσ : σ.IsSmoothAtlas IG A) : Representation ℂ G A.smoothSections := by
  let h := σ.atlasSmoothSectionAction_properties IG A hσ
  exact
    { toFun := fun g ↦
        { toFun := fun s ↦ ⟨σ.dependentSectionLinearMap g s.val, h.1 g s⟩
          map_add' := fun s t ↦
            Subtype.ext ((σ.dependentSectionLinearMap g).map_add s.val t.val)
          map_smul' := fun c s ↦
            Subtype.ext ((σ.dependentSectionLinearMap g).map_smul c s.val) }
      map_one' := by
        apply LinearMap.ext
        intro s
        apply Subtype.ext
        exact congrArg (fun T : (∀ x, E x) →ₗ[ℂ] (∀ x, E x) ↦ T s.val) h.2.1
      map_mul' := by
        intro g k
        apply LinearMap.ext
        intro s
        apply Subtype.ext
        exact congrArg (fun T : (∀ x, E x) →ₗ[ℂ] (∀ x, E x) ↦ T s.val) (h.2.2 g k) }

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

/-- SG's intertwining condition on the two original variable-rank smooth-section actions. -/
def AtlasPseudodifferentialOperator.IsEquivariant
    (σE : EquivariantStructure G E) (σF : EquivariantStructure G F)
    (hσE : σE.IsSmoothAtlas IG A) (hσF : σF.IsSmoothAtlas IG B)
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m) : Prop :=
  ∀ g : G, P.toLinearMap.comp (σE.atlasSmoothSectionRepresentation IG A hσE g) =
    (σF.atlasSmoothSectionRepresentation IG B hσF g).comp P.toLinearMap

end OriginalAtlas

section NativeComparison

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  {F : M → Type*} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

/-- Identity transport of the same native PDO preserves and reflects its original equivariance. -/
theorem PseudodifferentialOperator.isEquivariant_toAtlas_iff
    (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      EquivariantStructure G F)
    (hσE : σE.IsSmooth (n := n) (r := r) IG)
    (hσF : σF.IsSmooth (n := n) (r := q) IG)
    {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    P.toAtlasPseudodifferentialOperator.IsEquivariant IG σE σF
        (σE.isSmoothAtlas_native IG hσE) (σF.isSmoothAtlas_native IG hσF) ↔
      P.IsEquivariant IG σE σF hσE hσF := by
  /- Stage 1: the nativeSmoothSectionLinearEquiv used by the PDO adapter
  retains each dependent section value. The native and generic action
  formulas therefore agree after that very identity transport, including
  the original equality casts at g inverse.x and g.(g inverse.x).
  Stage 2: expand the actual toAtlasPseudodifferentialOperator section map.
  Conjugate its intertwining equality by the source and target identity
  section equivalences. The preceding action comparison gives exactly the
  old native equivariance equality, and the inverse equivalences give the
  converse. This retains the original P, σE, σF and μ; no replacement PDO,
  principal-symbol premise, averaging or invariant-density assumption is added. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let e := nativeSmoothSectionLinearEquiv (n := n) (r := r) E
  let f := nativeSmoothSectionLinearEquiv (n := n) (r := q) F
  -- Both section-action formulas are the same dependent function and the same index transport.
  have hE (g : G) (u : (nativeSmoothComplexBundleAtlas (n := n) (r := r) E).smoothSections) :
      e (σE.atlasSmoothSectionRepresentation IG _ (σE.isSmoothAtlas_native IG hσE) g u) =
        σE.smoothSectionRepresentation IG hσE g (e u) := rfl
  have hF (g : G) (u : (nativeSmoothComplexBundleAtlas (n := n) (r := q) F).smoothSections) :
      f (σF.atlasSmoothSectionRepresentation IG _ (σF.isSmoothAtlas_native IG hσF) g u) =
        σF.smoothSectionRepresentation IG hσF g (f u) := rfl
  constructor
  · intro hP g
    apply LinearMap.ext
    intro u
    have heq := congrArg (fun T ↦ f (T (e.symm u))) (hP g)
    change P.toLinearMap
        (e (σE.atlasSmoothSectionRepresentation IG _ (σE.isSmoothAtlas_native IG hσE)
          g (e.symm u))) =
      f (σF.atlasSmoothSectionRepresentation IG _ (σF.isSmoothAtlas_native IG hσF)
        g (f.symm (P.toLinearMap u))) at heq
    simpa only [hE, hF, LinearEquiv.apply_symm_apply, LinearMap.comp_apply] using heq
  · intro hP g
    apply LinearMap.ext
    intro u
    apply f.injective
    change P.toLinearMap
        (e (σE.atlasSmoothSectionRepresentation IG _ (σE.isSmoothAtlas_native IG hσE) g u)) =
      f (σF.atlasSmoothSectionRepresentation IG _ (σF.isSmoothAtlas_native IG hσF)
        g (f.symm (P.toLinearMap (e u))))
    rw [hE, hF, LinearEquiv.apply_symm_apply]
    exact congrArg (fun T ↦ T (e u)) (hP g)

end NativeComparison

end AtiyahSinger
