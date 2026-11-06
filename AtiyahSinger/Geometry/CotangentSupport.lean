/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CosphereBundle
public import AtiyahSinger.Topology.CompactSupportKZero

/-!
# The zero section as compact symbol control

Public module ID: M1156.

SG III.1 (1.6) and III.13 (13.1) place the symbol over the cotangent bundle.
Its zero section is compact when the base is compact, including dimension zero.
The tangent/cotangent metric identification in the book is not implicit here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- The actual cotangent projection as a continuous map. -/
@[reducible]
def cotangentProjection : C(CotangentTotalSpace (n := n) (M := M), M) :=
  ⟨Bundle.TotalSpace.proj, FiberBundle.continuous_proj (CotangentModel n) _⟩

/-- The cotangent projection keeps the base point. -/
theorem cotangentProjection_apply (z : CotangentTotalSpace (n := n) (M := M)) :
    cotangentProjection z = z.proj := by
  /- The continuous map was defined using the actual total-space projection. Evaluating it
  returns the original base point, independently of the covector. -/
  rfl

/-- The zero section as an actual map into the cotangent total space. -/
def cotangentZeroSection : M → CotangentTotalSpace (n := n) (M := M) :=
  fun x ↦ ⟨x, 0⟩

/-- The zero section is continuous for the original bundle topology. -/
theorem continuous_cotangentZeroSection :
    Continuous (cotangentZeroSection (n := n) (M := M)) := by
  /- In every cotangent trivialization the zero section is x ↦ (x,0). Local linear frames
  preserve zero, hence these continuous local formulas agree globally. -/
  exact Trivialization.continuous_zeroSection ℝ (F := CotangentModel n)

/-- Zero covectors form the control set for an elliptic symbol. -/
@[reducible]
def cotangentZeroSet : Set (CotangentTotalSpace (n := n) (M := M)) :=
  {z | z.snd = 0}

set_option linter.unusedSectionVars false in
/-- The control set is exactly the image of the zero section. -/
theorem range_cotangentZeroSection :
    Set.range (cotangentZeroSection (n := n) (M := M)) = cotangentZeroSet := by
  /- Every value of the zero section has zero covector. Conversely a point with zero covector
  is the zero-section value of its own base point, by dependent-pair extensionality. -/
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hz
    refine ⟨z.proj, ?_⟩
    cases z with
    | mk x ξ =>
      change ξ = 0 at hz
      simp only [cotangentZeroSection, hz]

/-- Projection after the zero section is identity. -/
theorem cotangentProjection_zeroSection (x : M) :
    cotangentProjection (cotangentZeroSection (n := n) x) = x := by
  /- Evaluate the two displayed maps on the original base point. The zero covector affects only
  the second component, leaving the base point unchanged. -/
  rfl

set_option linter.unusedSectionVars false in
/-- The zero section is injective. -/
theorem cotangentZeroSection_injective :
    Function.Injective (cotangentZeroSection (n := n) (M := M)) := by
  /- Apply the actual cotangent projection to an equality of zero-section values. Its left-
  inverse identity recovers the two original base points. -/
  intro x y hxy
  exact congrArg (fun z : CotangentTotalSpace (n := n) (M := M) ↦ z.proj) hxy

/-- Over a compact base the zero section gives one compact control set. -/
theorem isCompact_cotangentZeroSet [CompactSpace M] :
    IsCompact (cotangentZeroSet (n := n) (M := M)) := by
  /- Use continuity of the zero section and compactness of the entire base. Its compact image
  is exactly the displayed zero set; no positive dimension or cotangent metric is needed. -/
  rw [← range_cotangentZeroSection]
  exact isCompact_range continuous_cotangentZeroSection

/-- The cotangent total space is Hausdorff over a Hausdorff base. -/
theorem t2Space_cotangent [T2Space M] :
    T2Space (CotangentTotalSpace (n := n) (M := M)) := by
  /- Different base points are separated through the continuous projection. Points over one
  base point are separated inside a local trivialization, whose fiber is finite-dimensional
  Hausdorff. -/
  -- First separate distinct base points through the actual projection.
  refine t2_iff_nhds.mpr ?_
  intro x y hxy
  let := hxy
  have hp : x.proj = y.proj := tendsto_nhds_unique
    (cotangentProjection.continuous.continuousAt.mono_left inf_le_left)
    (cotangentProjection.continuous.continuousAt.mono_left inf_le_right)
  -- Points over the same base lie in one injective Hausdorff bundle chart.
  let e := trivializationAt (CotangentModel n) (CotangentFiber (n := n) (M := M)) x.proj
  have hx : x ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
  have hy : y ∈ e.source := by
    apply e.mem_source.mpr
    rw [← hp]
    exact mem_baseSet_trivializationAt (CotangentModel n) _ x.proj
  have he : e x = e y := tendsto_nhds_unique
    ((e.toOpenPartialHomeomorph.continuousAt hx).mono_left inf_le_left)
    ((e.toOpenPartialHomeomorph.continuousAt hy).mono_left inf_le_right)
  exact e.toOpenPartialHomeomorph.injOn hx hy he

/-- The zero section is closed. -/
theorem isClosed_cotangentZeroSet [T2Space M] :
    IsClosed (cotangentZeroSet (n := n) (M := M)) := by
  /- The actual total space is Hausdorff by local bundle charts. The zero covectors are
  exactly the fixed points of the continuous map which projects to the base and then
  takes the zero section, hence form a closed equalizer. -/
  -- The zero section is the fixed-point locus of the continuous fiberwise retraction.
  let := t2Space_cotangent (n := n) (M := M)
  have hclosed := isClosed_eq
    ((continuous_cotangentZeroSection (n := n) (M := M)).comp
      (cotangentProjection (n := n) (M := M)).continuous)
    continuous_id
  convert hclosed using 1
  ext z
  constructor
  · intro hz
    cases z with
    | mk x ξ =>
      change ξ = 0 at hz
      change (⟨x, 0⟩ : CotangentTotalSpace (n := n) (M := M)) = ⟨x, ξ⟩
      rw [hz]
  · intro hz
    have hzero : cotangentZeroSection z.proj = z := hz
    rw [← hzero]
    rfl

/-- The finite-dimensional cotangent total space of a Hausdorff base is locally compact. -/
theorem locallyCompactSpace_cotangent [T2Space M] :
    LocallyCompactSpace (CotangentTotalSpace (n := n) (M := M)) := by
  /- A finite-dimensional real manifold is locally compact. Cotangent trivializations identify
  open neighborhoods with products of an open base neighborhood and a finite-dimensional
  real vector space, so local compactness transfers. -/
  -- The native cotangent atlas has a finite-dimensional locally compact model.
  let : LocallyCompactSpace (ModelProd (EuclideanSpace ℝ (Fin n)) (CotangentModel n)) :=
    inferInstanceAs (LocallyCompactSpace
      (EuclideanSpace ℝ (Fin n) × CotangentModel n))
  exact ChartedSpace.locallyCompactSpace
    (ModelProd (EuclideanSpace ℝ (Fin n)) (CotangentModel n))
    (CotangentTotalSpace (n := n) (M := M))

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- Projection from nonzero covectors to the original base. -/
def puncturedCotangentProjection : C(PuncturedCotangentBundle (n := n) (M := M), M) :=
  cotangentProjection.comp ⟨Subtype.val, continuous_subtype_val⟩

/-- Every cotangent vector is zero in dimension zero. -/
theorem cotangentFiber_eq_zero_of_dim_zero (hn : n = 0) (x : M)
    (ξ : CotangentFiber (n := n) x) : ξ = 0 := by
  /- The tangent model has dimension zero, so each tangent fiber and its real dual are zero-
  dimensional. Any continuous linear functional on the zero space is zero. -/
  subst n
  -- This foundational use of the tangent-space model only establishes zero dimension.
  let : Subsingleton (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) x) := by
    unfold TangentSpace
    infer_instance
  exact Subsingleton.elim ξ 0

/-- In dimension zero the zero set is the entire cotangent total space. -/
theorem cotangentZeroSet_eq_univ_of_dim_zero (hn : n = 0) :
    cotangentZeroSet (n := n) (M := M) = Set.univ := by
  /- Every covector is zero by zero-dimensionality of its tangent fiber. Thus every total-space
  point lies in the zero set, independently of the base cardinality. -/
  apply Set.eq_univ_of_forall
  intro z
  exact cotangentFiber_eq_zero_of_dim_zero hn z.proj z.snd

/-- The cotangent projection is a homeomorphism in dimension zero. -/
theorem exists_cotangentProjection_homeomorph_of_dim_zero (hn : n = 0) :
    ∃ e : CotangentTotalSpace (n := n) (M := M) ≃ₜ M,
      (∀ z, e z = z.proj) ∧ ∀ x, e.symm x = cotangentZeroSection x := by
  /- Use projection and the continuous zero section as inverse functions. Their first composite
  is identity by the base formula; their second is identity because every covector is zero.
  The characterization fixes both actual maps. -/
  -- Construct the inverse on the actual total space, using the zero fiber at every point.
  let e : CotangentTotalSpace (n := n) (M := M) ≃ₜ M :=
    { toFun := cotangentProjection
      invFun := cotangentZeroSection
      left_inv := by
        intro z
        cases z with
        | mk x ξ =>
          have hξ := cotangentFiber_eq_zero_of_dim_zero hn x ξ
          change (⟨x, 0⟩ : CotangentTotalSpace (n := n) (M := M)) = ⟨x, ξ⟩
          rw [hξ]
      right_inv := cotangentProjection_zeroSection
      continuous_toFun := cotangentProjection.continuous
      continuous_invFun := continuous_cotangentZeroSection }
  -- Both characterizations refer to this same homeomorphism and its chosen inverse.
  exact ⟨e, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The dimension-zero comparison uses the actual projection and zero section. -/
def cotangentProjectionHomeomorphOfDimZero (hn : n = 0) :
    CotangentTotalSpace (n := n) (M := M) ≃ₜ M :=
  (exists_cotangentProjection_homeomorph_of_dim_zero hn).choose

/-- The dimension-zero homeomorphism keeps the base point. -/
theorem cotangentProjectionHomeomorphOfDimZero_apply (hn : n = 0)
    (z : CotangentTotalSpace (n := n) (M := M)) :
    cotangentProjectionHomeomorphOfDimZero hn z = z.proj := by
  /- Extract the forward-map characterization from the existence theorem used in this precise
  choice. The chosen homeomorphism cannot permute base points. -/
  exact (exists_cotangentProjection_homeomorph_of_dim_zero hn).choose_spec.1 z

/-- The dimension-zero inverse is the original zero section. -/
theorem cotangentProjectionHomeomorphOfDimZero_symm_apply (hn : n = 0) (x : M) :
    (cotangentProjectionHomeomorphOfDimZero hn).symm x = cotangentZeroSection x := by
  /- Extract the inverse-map characterization from the same existence witness. It is the
  displayed zero section, not an arbitrary inverse chosen independently. -/
  exact (exists_cotangentProjection_homeomorph_of_dim_zero hn).choose_spec.2 x

end AtiyahSinger
