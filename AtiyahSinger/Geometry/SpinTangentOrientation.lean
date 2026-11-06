/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentCohomologyOrientation
public import AtiyahSinger.Topology.ChartHomologicalOrientation
public import AtiyahSinger.Topology.SpinCohomologyOrientation
public import AtiyahSinger.Topology.ZeroRankEuler

/-!
# The original manifold orientation determined by its spin frames

Public module ID: M1460.

The geometric tangent orientation determines integral local generators by
the original signed affine simplex and the original tangent-to-local-homology
comparison. Continuous positive local frames make these generators locally
compatible. The resulting manifold orientation is therefore specified by
the original tangent orientation, rather than supplied independently.

Its tangent Thom orientation equals the original geometrically normalized
fiber orientation. Specializing to the original spin frame lift identifies
it with the same integral orientation used by the spin Thom character.
In rank zero the canonical empty basis gives the positive point orientation;
no negative empty basis or positive-rank spin covering is asserted.

Sources: Hatcher, Algebraic Topology, section 3.3, and Milnor--Stasheff,
Characteristic Classes, section 9. The explicit comparison of the project's
two normalized singular models is a project supplement. The proofs below
retain the local normalization, continuous positive frames and original
coordinate maps in constructing and comparing these integral orientations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

section Geometric

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  (g : SmoothTangentMetric (n := n) (M := M))

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "TM" => (TangentSpace 𝓘(ℝ, V) : M → Type)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same positive local tangent frames specify unique integral local manifold generators. -/
theorem existsUnique_geometricTangentHomologicalOrientation :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    ∀ (o : ∀ x : M, Orientation ℝ (TM x) (Fin n))
      (_ho : IsLocallyCompatibleBundleOrientation n TM o),
      ∃! O : HomologicalOrientation n M, ∀ x : M,
        let b : Module.Basis (Fin n) ℝ (TM x) :=
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
            (VectorBundle.continuousLinearEquivAt ℝ V TM x).symm.toLinearEquiv
        O.localGenerator x (1 : ℤ) = tangentLocalHomologyEquiv (n := n) (M := M) x
          (realOrientationCycle (r := n) («V» := TM x) b (o x)) := by
  /- Stage 1: the signed simplex in the original preferred linear tangent
  chart represents the generator prescribed by o x. The same translated
  tangent chart and original excision equivalence transport it to the local
  integral homology of M at x. Its integer multiples define an equivalence
  from Z; no rational-unit rescaling or independent generator is chosen.
  Stage 2: near a fixed point, use the actual positive continuous local
  frames supplied by ho. Relative to one smooth coordinate chart their
  determinant has a constant positive orientation sign after shrinking.
  The local homology map of a smooth transition has the sign of its
  derivative determinant. The native tangent transition is that derivative,
  so the signed simplex generators and local chart generators agree.
  A sufficiently small chart ball consequently supplies the one relative
  class whose restrictions are all the prescribed local generators.
  Stage 3: these maps and local classes define HomologicalOrientation.
  Two such orientations agree at 1 in each integral rank-one local group,
  hence agree as linear equivalences and as structures. For n=0 the local
  frames are empty and have canonical positive orientation, giving the
  positive signed point; no nonexistent negative empty basis is used. -/
  classical
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  intro o ho
  let b (x : M) : Module.Basis (Fin n) ℝ (TM x) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
      (VectorBundle.continuousLinearEquivAt ℝ V TM x).symm.toLinearEquiv
  let z (x : M) := tangentLocalHomologyEquiv (n := n) (M := M) x
    (realOrientationCycle (b x) (o x))
  have hgen (x : M) : Function.Bijective (LinearMap.toSpanSingleton ℤ _ (z x)) := by
    have h := (tangentLocalHomologyEquiv (n := n) (M := M) x).bijective.comp
      (realOrientationCycle_is_generator (b x) (o x))
    convert h using 1
    funext a
    change _ = tangentLocalHomologyEquiv x (a • realOrientationCycle (b x) (o x))
    rw [map_zsmul]
    exact int_smul_eq_zsmul (relativeSingularHomology ℤ ({x}ᶜ : Set M) n).isModule a (z x)
  apply existsUnique_homologicalOrientation_of_chart_transport z hgen
  intro x
  obtain ⟨U, hU, hx, c, hc, hcont⟩ := ho x
  let t := trivializationAt V TM x
  let W := U ∩ t.baseSet
  have hW : IsOpen W := hU.inter t.open_baseSet
  have hxW : x ∈ W := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let j : W → U := fun y ↦ ⟨y.val, y.property.1⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let e (y : W) : TM y.val ≃L[ℝ] V :=
    t.continuousLinearEquivAt ℝ y.val y.property.2
  let d (y : W) : Module.Basis (Fin n) ℝ V := (c (j y)).map (e y).toLinearEquiv
  -- One fixed tangent trivialization makes the given positive frame columns continuous.
  have hd (i : Fin n) : Continuous (fun y : W ↦ d y i) := by
    exact (t.continuousOn.comp_continuous ((hcont i).comp hj)
      (fun y ↦ t.mem_source.mpr y.property.2)).snd
  let d₀ := d ⟨x, hxW⟩
  let D (y : W) : ℝ := d₀.det (d y)
  have hmat : Continuous (fun y : W ↦ d₀.toMatrix (d y)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro k
    exact ((continuous_apply i).comp (continuous_equivFun_basis d₀)).comp (hd k)
  have hD : Continuous D := hmat.matrix_det
  let W' : Set M := Subtype.val '' {y : W | 0 < D y}
  have hW' : IsOpen W' := hW.isOpenMap_subtype_val _ (isOpen_lt continuous_const hD)
  have hxW' : x ∈ W' := by
    refine ⟨⟨x, hxW⟩, ?_, rfl⟩
    change 0 < d₀.det d₀
    rw [Module.Basis.det_self]
    norm_num
  have hW'W : W' ⊆ W := by rintro y ⟨v, _, rfl⟩; exact v.property
  have hW'e : W' ⊆ (chartAt V x).source := fun y hy ↦ (hW'W hy).2
  refine ⟨W', hW', hxW', hW'e, realOrientationCycle d₀ d₀.orientation, ?_⟩
  intro y hy
  let yW : W := ⟨y, hW'W hy⟩
  have hpos : 0 < D yW := by
    obtain ⟨v, hv, heq⟩ := hy
    have heq' : v = yW := Subtype.ext heq
    exact heq' ▸ hv
  have hor : Orientation.map (Fin n) (e yW).toLinearEquiv (o y) = d₀.orientation := by
    have h := ((d₀.orientation_eq_iff_det_pos (d yW)).mpr hpos).symm
    simpa only [d, Module.Basis.orientation_map, hc] using h
  let f : C(TM y, V) := ⟨e yW, (e yW).continuous⟩
  have hf : Set.MapsTo f {v : TM y | v ≠ 0} {v : V | v ≠ 0} :=
    fun _ hv h ↦ hv ((e yW).injective (h.trans (e yW).map_zero.symm))
  have hcycle : relativeSingularHomologyMap ℤ f hf n (realOrientationCycle (b y) (o y)) =
      realOrientationCycle d₀ d₀.orientation := by
    have h := realOrientationCycle_map (b y) (o y) (e yW)
    rw [hor] at h
    exact h.trans (realOrientationCycle_basis_independent _ d₀ d₀.orientation)
  -- The fixed-chart tangent comparison retains the actual base chart and its derivative.
  let ta : C(V, V) := ⟨fun v ↦ chartAt V x y + v, continuous_const.add continuous_id⟩
  have hta : Set.MapsTo ta {v : V | v ≠ 0} ({chartAt V x y}ᶜ : Set V) :=
    fun _ hv h ↦ hv (add_left_cancel (h.trans (add_zero _).symm))
  have hnative := tangentLocalHomologyEquiv_chartAt x y (hW'e hy)
    (realOrientationCycle (b y) (o y))
  have hcomp := congrArg (fun F ↦ HomologicalComplex.homologyMap F n)
    (relativeSingularChainsMap_comp ℤ f ta hf hta)
  rw [HomologicalComplex.homologyMap_comp] at hcomp
  have hvalue := congrArg (fun F ↦ F (realOrientationCycle (b y) (o y))) hcomp
  change relativeSingularHomologyMap ℤ (ta.comp f) (hta.comp hf) n
    (realOrientationCycle (b y) (o y)) = relativeSingularHomologyMap ℤ ta hta n
      (relativeSingularHomologyMap ℤ f hf n (realOrientationCycle (b y) (o y))) at hvalue
  rw [hcycle] at hvalue
  exact hvalue.symm.trans hnative.symm

/-- The homological orientation obtained from the original locally positive tangent frames. -/
def geometricTangentHomologicalOrientation :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    (o : ∀ x : M, Orientation ℝ (TM x) (Fin n)) →
      IsLocallyCompatibleBundleOrientation n TM o → HomologicalOrientation n M := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  intro o ho
  exact (existsUnique_geometricTangentHomologicalOrientation g o ho).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The selected local generators and the induced tangent Thom orientation have the same sign. -/
theorem geometricTangentHomologicalOrientation_properties :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    ∀ (o : ∀ x : M, Orientation ℝ (TM x) (Fin n))
      (ho : IsLocallyCompatibleBundleOrientation n TM o),
      (∀ x : M,
        let b : Module.Basis (Fin n) ℝ (TM x) :=
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
            (VectorBundle.continuousLinearEquivAt ℝ V TM x).symm.toLinearEquiv
        (geometricTangentHomologicalOrientation g o ho).localGenerator x (1 : ℤ) =
          tangentLocalHomologyEquiv (n := n) (M := M) x
            (realOrientationCycle (r := n) («V» := TM x) b (o x))) ∧
      tangentCohomologyOrientation g (geometricTangentHomologicalOrientation g o ho) =
        geometricCohomologyOrientation n TM o ho := by
  /- Stage 1: take the defining generator formula from precisely the unique
  existence witness selected by geometricTangentHomologicalOrientation.
  Stage 2: tangentCohomologyFiberEvaluation now evaluates on the original
  signed realOrientationCycle, since tangentLocalHomologyEquiv cancels
  with its inverse. realOrientationClass_evaluation gives exactly one on
  that cycle. Uniqueness of the tangent fiber class identifies it with the
  same geometricCohomologyFiberClass at every point.
  Stage 3: equality of fiber classes identifies the two orientations;
  their generation and local-compatibility fields are propositions.
  This compares normalized integral classes before rationalization and
  includes the canonical positive degree-zero generator. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  intro o ho
  let O := geometricTangentHomologicalOrientation g o ho
  have hz (x : M) :
      O.localGenerator x 1 = tangentLocalHomologyEquiv (n := n) (M := M) x
        (realOrientationCycle (r := n) («V» := TM x)
          ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
            (VectorBundle.continuousLinearEquivAt ℝ V TM x).symm.toLinearEquiv) (o x)) := by
    dsimp only [O, geometricTangentHomologicalOrientation]
    exact (existsUnique_geometricTangentHomologicalOrientation g o ho).exists.choose_spec x
  refine ⟨hz, ?_⟩
  have hf (x : M) : tangentCohomologyFiberClass O x =
      geometricCohomologyFiberClass n TM o x := by
    apply (existsUnique_tangentCohomologyFiberClass O x).unique
    · exact (existsUnique_tangentCohomologyFiberClass O x).exists.choose_spec
    · -- Both evaluations use the same signed tangent simplex after cancelling the chart inverse.
      unfold tangentCohomologyFiberEvaluation
      rw [hz, LinearEquiv.symm_apply_apply]
      exact realOrientationClass_evaluation _ _
  have hext (a b : CohomologyOrientation ℤ n TM)
      (h : a.fiberClass = b.fiberClass) : a = b := by
    cases a with
    | mk a ha hla =>
      cases b with
      | mk b hb hlb =>
        change a = b at h
        subst b
        rfl
  exact hext _ _ (funext hf)

end Geometric

section Spin

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology

variable {m : ℕ} {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M] [T2Space M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
  {hm : 0 < m}
  {o : ∀ x : M,
    Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) x) (Fin (2 * m))}
  (g : SmoothTangentMetric (n := 2 * m) (M := M))

local notation "V" => EuclideanSpace ℝ (Fin (2 * m))
local notation "TM" => (TangentSpace 𝓘(ℝ, V) : M → Type)

/-- The original spin frame lift induces the integral orientation of the same base manifold. -/
def TopologicalSpinStructure.homologicalOrientation :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle V TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    TopologicalSpinStructure m TM o hm hP → HomologicalOrientation (2 * m) M := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle V TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  intro S
  exact geometricTangentHomologicalOrientation g o S.isLocallyCompatibleBundleOrientation

/-- The induced base orientation gives exactly the same integral spin Thom orientation. -/
theorem TopologicalSpinStructure.tangentCohomologyOrientation_eq :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle V TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    ∀ S : TopologicalSpinStructure m TM o hm hP,
      tangentCohomologyOrientation g (S.homologicalOrientation g) =
        S.integralCohomologyOrientation := by
  /- Apply geometricTangentHomologicalOrientation_properties to the original
  o and the local positive frames derived from precisely S. Its right-hand
  geometric orientation is definitionally S.integralCohomologyOrientation.
  In particular neither orientation is independently supplied or reversed. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle V TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  intro S
  exact (geometricTangentHomologicalOrientation_properties g o
    S.isLocallyCompatibleBundleOrientation).2

end Spin

section Zero

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) ∞ M] [T2Space M]
  (g : SmoothTangentMetric (n := 0) (M := M))

local notation "TM" => (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) : M → Type)

/-- The canonical empty tangent bases give the positive homological orientation in rank zero. -/
def zeroTangentHomologicalOrientation : HomologicalOrientation 0 M := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  exact geometricTangentHomologicalOrientation g (zeroRankBundleOrientation TM)
    (isLocallyCompatibleBundleOrientation_zeroRank TM)

/-- The same positive point orientation induces the native empty-basis Thom orientation. -/
theorem tangentCohomologyOrientation_zero :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    tangentCohomologyOrientation g (zeroTangentHomologicalOrientation g) =
      zeroRankIntegralCohomologyOrientation TM := by
  /- Specialize the geometric comparison to the same canonical empty
  bases and their existing local-frame certificate. Both fiber classes
  evaluate to one on the actual positive point cycle. This is the native
  zero endpoint, not a claim concerning a negative point orientation. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  exact (geometricTangentHomologicalOrientation_properties g (zeroRankBundleOrientation TM)
    (isLocallyCompatibleBundleOrientation_zeroRank TM)).2

end Zero

end AtiyahSinger
