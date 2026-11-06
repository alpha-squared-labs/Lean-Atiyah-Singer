/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMaps
public import AtiyahSinger.Geometry.SmoothSpinPrincipalAtlas
public import AtiyahSinger.Topology.SpinorBundleZero

/-!
# Smooth full and half-spin bundles on the original associated fibers

Public module ID: M1415.

S01. One specified smooth principal spin atlas gives compatible smooth atlases
on the original full-spin quotient, both original parity quotients, and their
original same-base sum. Every principal chart occurs in the associated atlas
with its exact representative formula [p,v] -> c(rho(gamma(p))v), where c is a
fixed complex-linear model coordinate. Thus these are the associated smooth
structures for the specified principal atlas, rather than arbitrary smoothings
of the underlying topological bundles.

The same selected atlas triple makes the original parity splitting and its
inverse smooth. The sum projections and inclusions are smooth in those very
half-spin atlases, so the sum structure cannot be chosen independently. All
fibers, their operations, and their Unit total-space topologies are unchanged.
The original chirality labels are retained, including the even line and zero
odd fiber at m=0. No connection, Clifford contraction, or Dirac operator is
part of this smooth associated-bundle construction.

Sources: Lawson--Michelsohn, Spin Geometry II.3, pp.93--99; I.5 for the exterior
model and parity convention. Smoothness follows because the original full
Clifford representation is real-linear, and its parity restrictions use the
same invariant subspaces. The associated atlas construction and all six
structural maps are proved below. The atlas selections and compatibility record
use one and the same witness.
-/

@[expose] public noncomputable section

universe u v w

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology ComplexBundle.sumTopology

variable (m : ℕ) {n : ℕ} {P : Type v} {B : Type u}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection)
  (S : SmoothSpinPrincipalAtlas m 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) projection)

namespace SmoothSpinPrincipalAtlas

variable {m hP S}

/-- Associated smooth charts retain the actual quotient formula in each specified spin chart. -/
def IsAssociatedVectorAtlas
    (S : SmoothSpinPrincipalAtlas m 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) projection)
    (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection)
    {V : Type w} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ρ : ContRepresentation ℂ (spinGroup (realSpinorQuadraticForm m)) V)
    (A : SmoothComplexBundleAtlas (n := n) (AssociatedVectorFiber hP ρ)) : Prop :=
  ∀ b₀ : B, ∃ (i : A.Index) (c : V ≃ₗ[ℂ] (Fin (A.rank i) → ℂ)),
    (A.chart i).baseSet = (S.trivialization b₀).baseSet ∧
      ∀ (p : P) (b : B) (hp : projection p = b),
        b ∈ (S.trivialization b₀).baseSet → ∀ v : V,
          (A.chart i ⟨b, associatedVectorFiberMk hP ρ p hp v⟩).2 =
            c (ρ ((S.trivialization b₀) p).2 v)

end SmoothSpinPrincipalAtlas

/-- The same spin charts give the original smooth associated bundles and parity splitting. -/
theorem exists_spinorBundle_smoothAtlases :
    letI : ∀ b, Module ℂ (HalfSpinorBundle m hP 0 b × HalfSpinorBundle m hP 1 b) :=
      fun _b ↦ inferInstance
    ∃ A : SmoothComplexBundleAtlas.{u} (n := n) (SpinorBundle m hP),
      ∃ H : ∀ i : ZMod 2, SmoothComplexBundleAtlas.{u} (n := n) (HalfSpinorBundle m hP i),
        ∃ C : SmoothComplexBundleAtlas.{u} (n := n)
            (HalfSpinorBundle m hP 0 ×ᵇ HalfSpinorBundle m hP 1),
          S.IsAssociatedVectorAtlas hP (complexSpinContRepresentation m) A ∧
            (∀ i : ZMod 2,
              S.IsAssociatedVectorAtlas hP (complexSpinParityContRepresentation m i) (H i)) ∧
            IsSmoothAtlasBundleMap C (H 0) (fun b ↦
              LinearMap.fst ℂ (HalfSpinorBundle m hP 0 b) (HalfSpinorBundle m hP 1 b)) ∧
            IsSmoothAtlasBundleMap C (H 1) (fun b ↦
              LinearMap.snd ℂ (HalfSpinorBundle m hP 0 b) (HalfSpinorBundle m hP 1 b)) ∧
            IsSmoothAtlasBundleMap (H 0) C (fun b ↦
              LinearMap.inl ℂ (HalfSpinorBundle m hP 0 b) (HalfSpinorBundle m hP 1 b)) ∧
            IsSmoothAtlasBundleMap (H 1) C (fun b ↦
              LinearMap.inr ℂ (HalfSpinorBundle m hP 0 b) (HalfSpinorBundle m hP 1 b)) ∧
            IsSmoothAtlasBundleMap A C
              (fun b ↦ ((spinorBundleParityIso m hP).linearEquiv b).toLinearMap) ∧
            IsSmoothAtlasBundleMap C A
              (fun b ↦ ((spinorBundleParityIso m hP).linearEquiv b).symm.toLinearMap) := by
  classical
  let : ∀ b, Module ℂ (HalfSpinorBundle m hP 0 b × HalfSpinorBundle m hP 1 b) :=
    fun _b ↦ inferInstance
  let G : Type := spinGroup (realSpinorQuadraticForm m)
  let V := ComplexSpinor m
  let W (i : ZMod 2) := CliffordAlgebra.evenOdd
    (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i
  let ρ := complexSpinContRepresentation m
  let σ (i : ZMod 2) := complexSpinParityContRepresentation m i
  let d := exteriorParityEquiv (EuclideanSpace ℂ (Fin m))
  let τ (i j b : B) : G :=
    ((S.trivialization j) ((S.trivialization i).toPartialEquiv.symm (b, 1))).2
  -- Finite coordinates use the original complex representation spaces, including rank zero.
  let c {T : Type} [NormedAddCommGroup T] [NormedSpace ℂ T]
      [FiniteDimensional ℂ T] : T ≃L[ℂ] (Fin (Module.finrank ℂ T) → ℂ) :=
    (Module.finBasis ℂ T).equivFun.toContinuousLinearEquiv
  -- Use each supplied principal chart, rather than an independently selected principal atlas.
  let quotientChart {T : Type} [NormedAddCommGroup T] [NormedSpace ℂ T]
      (r : ContRepresentation ℂ G T)
      (hr : Continuous (fun z : G × T ↦ r z.1 z.2)) (i : B) :
      letI := associatedRepresentationAction r
      Trivialization T (associatedBundleProjection (F := T) hP) := by
    let : MulAction G T := associatedRepresentationAction r
    let : ContinuousSMul G T := ⟨hr⟩
    exact (exists_associatedBundleTrivialization (F := T) hP
      (S.trivialization i) (S.equivariant i)).choose
  have quotientChart_properties {T : Type} [NormedAddCommGroup T] [NormedSpace ℂ T]
      (r : ContRepresentation ℂ G T)
      (hr : Continuous (fun z : G × T ↦ r z.1 z.2)) (i : B) :
      letI := associatedRepresentationAction r
      (quotientChart r hr i).baseSet = (S.trivialization i).baseSet ∧
        ∀ (p : P) (v : T), projection p ∈ (S.trivialization i).baseSet →
          quotientChart r hr i (associatedBundleMk G P T p v) =
            (projection p, r ((S.trivialization i) p).2 v) := by
    let : MulAction G T := associatedRepresentationAction r
    let : ContinuousSMul G T := ⟨hr⟩
    have h := (exists_associatedBundleTrivialization (F := T) hP
      (S.trivialization i) (S.equivariant i)).choose_spec
    exact ⟨h.1, h.2.1⟩
  -- Transport only by genuine original total-space homeomorphisms and complex coordinates.
  let bundleChart {T : Type} [NormedAddCommGroup T] [NormedSpace ℂ T]
      [FiniteDimensional ℂ T] (r : ContRepresentation ℂ G T)
      (hr : Continuous (fun z : G × T ↦ r z.1 z.2))
      {E : B → Type v} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
      [TopologicalSpace (TotalSpace Unit E)]
      (e : ComplexBundle.Iso (AssociatedVectorFiber hP r) E) (i : B) :
      Trivialization (Fin (Module.finrank ℂ T) → ℂ) (π Unit E) := by
    let : MulAction G T := associatedRepresentationAction r
    let H := associatedVectorTotalHomeomorph hP r
    let t₀ := ((quotientChart r hr i).transFiberHomeomorph c.toHomeomorph).compHomeomorph H
    let t : Trivialization (Fin (Module.finrank ℂ T) → ℂ)
        (π Unit (AssociatedVectorFiber hP r)) :=
      { toOpenPartialHomeomorph := t₀.toOpenPartialHomeomorph
        baseSet := t₀.baseSet
        open_baseSet := t₀.open_baseSet
        source_eq := by
          rw [t₀.source_eq]
          ext z
          change associatedBundleProjection (F := T) hP (H z) ∈ t₀.baseSet ↔
            z.proj ∈ t₀.baseSet
          rw [show associatedBundleProjection (F := T) hP (H z) = z.proj from z.snd.property]
        target_eq := t₀.target_eq
        proj_toFun := fun z hz ↦ (t₀.proj_toFun z hz).trans z.snd.property }
    exact t.compHomeomorph e.totalHomeomorph.symm
  have chart_base {T : Type} [NormedAddCommGroup T] [NormedSpace ℂ T]
      [FiniteDimensional ℂ T] (r : ContRepresentation ℂ G T)
      (hr : Continuous (fun z : G × T ↦ r z.1 z.2))
      {E : B → Type v} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
      [TopologicalSpace (TotalSpace Unit E)]
      (e : ComplexBundle.Iso (AssociatedVectorFiber hP r) E) (i : B) :
      (bundleChart r hr e i).baseSet = (S.trivialization i).baseSet :=
    (quotientChart_properties r hr i).1
  have chart_rep {T : Type} [NormedAddCommGroup T] [NormedSpace ℂ T]
      [FiniteDimensional ℂ T] (r : ContRepresentation ℂ G T)
      (hr : Continuous (fun z : G × T ↦ r z.1 z.2))
      {E : B → Type v} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
      [TopologicalSpace (TotalSpace Unit E)]
      (e : ComplexBundle.Iso (AssociatedVectorFiber hP r) E)
      (i : B) (p : P) (b : B) (hp : projection p = b)
      (hb : b ∈ (S.trivialization i).baseSet) (v : T) :
      (bundleChart r hr e i
        ⟨b, e.linearEquiv b (associatedVectorFiberMk hP r p hp v)⟩).2 =
          c (r ((S.trivialization i) p).2 v) := by
    let : MulAction G T := associatedRepresentationAction r
    change c (quotientChart r hr i
      ((associatedVectorTotalHomeomorph hP r)
        ⟨b, (e.linearEquiv b).symm
          (e.linearEquiv b (associatedVectorFiberMk hP r p hp v))⟩)).2 = _
    rw [LinearEquiv.symm_apply_apply]
    change c (quotientChart r hr i (associatedBundleMk G P T p v)).2 = _
    rw [(quotientChart_properties r hr i).2 p v (hp ▸ hb)]
  have chart_local {T : Type} [NormedAddCommGroup T] [NormedSpace ℂ T]
      [FiniteDimensional ℂ T] (r : ContRepresentation ℂ G T)
      (hr : Continuous (fun z : G × T ↦ r z.1 z.2))
      {E : B → Type v} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
      [TopologicalSpace (TotalSpace Unit E)]
      (e : ComplexBundle.Iso (AssociatedVectorFiber hP r) E)
      (i b : B) (hb : b ∈ (S.trivialization i).baseSet) (v : T) :
      (bundleChart r hr e i ⟨b, e.linearEquiv b
        (associatedVectorFiberMk hP r
          ((S.trivialization i).toPartialEquiv.symm (b, 1))
          ((S.trivialization i).proj_symm_apply' hb) v)⟩).2 = c v := by
    erw [chart_rep r hr e i _ b _ hb v]
    erw [(S.trivialization i).apply_symm_apply' (x := (1 : G)) hb]
    simp
  have chart_linear {T : Type} [NormedAddCommGroup T] [NormedSpace ℂ T]
      [FiniteDimensional ℂ T] (r : ContRepresentation ℂ G T)
      (hr : Continuous (fun z : G × T ↦ r z.1 z.2))
      {E : B → Type v} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
      [TopologicalSpace (TotalSpace Unit E)]
      (e : ComplexBundle.Iso (AssociatedVectorFiber hP r) E) (i b : B)
      (hb : b ∈ (bundleChart r hr e i).baseSet) :
      IsLinearMap ℂ (fun z : E b ↦ (bundleChart r hr e i ⟨b, z⟩).2) := by
    have hbS : b ∈ (S.trivialization i).baseSet := chart_base r hr e i ▸ hb
    let p := (S.trivialization i).toPartialEquiv.symm (b, 1)
    have hp : projection p = b := (S.trivialization i).proj_symm_apply' hbS
    let k := (associatedVectorFiberMkLinearEquiv hP r p hp).trans (e.linearEquiv b)
    have hformula (v : T) : (bundleChart r hr e i ⟨b, k v⟩).2 = c v :=
      chart_local r hr e i b hbS v
    constructor
    · intro z w
      obtain ⟨v, rfl⟩ := k.surjective z
      obtain ⟨u, rfl⟩ := k.surjective w
      rw [← map_add k, hformula, hformula, hformula]
      exact c.map_add v u
    · intro a z
      obtain ⟨v, rfl⟩ := k.surjective z
      rw [← map_smul k, hformula, hformula]
      exact c.map_smul a v
  have chart_inverse {T : Type} [NormedAddCommGroup T] [NormedSpace ℂ T]
      [FiniteDimensional ℂ T] (r : ContRepresentation ℂ G T)
      (hr : Continuous (fun z : G × T ↦ r z.1 z.2))
      {E : B → Type v} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
      [TopologicalSpace (TotalSpace Unit E)]
      (e : ComplexBundle.Iso (AssociatedVectorFiber hP r) E)
      (i b : B) (hb : b ∈ (S.trivialization i).baseSet)
      (z : Fin (Module.finrank ℂ T) → ℂ) :
      (bundleChart r hr e i).toPartialEquiv.symm (b, z) =
        ⟨b, e.linearEquiv b (associatedVectorFiberMk hP r
          ((S.trivialization i).toPartialEquiv.symm (b, 1))
          ((S.trivialization i).proj_symm_apply' hb) (c.symm z))⟩ := by
    let w : TotalSpace Unit E :=
      ⟨b, e.linearEquiv b (associatedVectorFiberMk hP r
        ((S.trivialization i).toPartialEquiv.symm (b, 1))
        ((S.trivialization i).proj_symm_apply' hb) (c.symm z))⟩
    have hw : (bundleChart r hr e i w).2 = z := by
      change (bundleChart r hr e i
        ⟨b, e.linearEquiv b (associatedVectorFiberMk hP r _ _ (c.symm z))⟩).2 = z
      rw [chart_local r hr e i b hb, c.apply_symm_apply]
    calc
      (bundleChart r hr e i).toPartialEquiv.symm (b, z) =
          (bundleChart r hr e i).toPartialEquiv.symm (w.proj,
            (bundleChart r hr e i w).2) := by rw [hw]
      _ = w := (bundleChart r hr e i).symm_apply_mk_proj
        ((bundleChart r hr e i).mem_source.mpr (chart_base r hr e i ▸ hb))
  -- Smoothness of the Spin action is linear smoothness in the supplied Clifford coordinates.
  have full_smooth (i j : B) (v : V) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞
        (fun b : B ↦ ρ (τ i j b) v)
        ((S.trivialization i).baseSet ∩ (S.trivialization j).baseSet) := by
    let L : (Finset (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin m)))) → ℝ) →ₗ[ℝ] V :=
      ((LinearMap.applyₗ' (R := ℂ) ℝ v).comp
        (realSpinorRepresentation m).toLinearMap).comp
          (realSpinorCliffordCoordinates m).symm.toLinearMap
    have h := L.toContinuousLinearMap.contMDiff.comp_contMDiffOn
      (S.contMDiffOn_transition i j)
    apply h.congr
    intro b hb
    change complexSpinRepresentation m (τ i j b) v =
      realSpinorRepresentation m
        ((realSpinorCliffordCoordinates m).symm
          (realSpinorCliffordCoordinates m (τ i j b).val)) v
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have half_smooth (a : ZMod 2) (i j : B) (v : W a) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, W a) ∞
        (fun b : B ↦ σ a (τ i j b) v)
        ((S.trivialization i).baseSet ∩ (S.trivialization j).baseSet) := by
    let inc : W a →ₗ[ℂ] V :=
      (CliffordAlgebra.evenOdd
        (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) a).subtype
    have hinc : LinearMap.ker inc = ⊥ := LinearMap.ker_eq_bot.mpr Subtype.val_injective
    let q : V →ₗ[ℂ] W a := inc.leftInverse
    -- A linear retraction agrees with the subtype inverse on every actual invariant value.
    have h := (q.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
      (full_smooth i j v.val)
    apply h.congr
    intro b hb
    exact (LinearMap.leftInverse_apply_of_inj hinc (σ a (τ i j b) v)).symm
  -- One local construction handles the original associated fibers and transport to the sum.
  let atlas {T : Type} [NormedAddCommGroup T] [NormedSpace ℂ T]
      [FiniteDimensional ℂ T] (r : ContRepresentation ℂ G T)
      (hr : Continuous (fun z : G × T ↦ r z.1 z.2))
      (hs : ∀ (i j : B) (v : T),
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, T) ∞
          (fun b : B ↦ r (τ i j b) v)
          ((S.trivialization i).baseSet ∩ (S.trivialization j).baseSet))
      {E : B → Type v} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
      [TopologicalSpace (TotalSpace Unit E)]
      (e : ComplexBundle.Iso (AssociatedVectorFiber hP r) E) :
      SmoothComplexBundleAtlas.{u} (n := n) E :=
    { Index := B
      rank := fun _ ↦ Module.finrank ℂ T
      chart := bundleChart r hr e
      covers := fun b ↦ ⟨b, (chart_base r hr e b).symm ▸ S.mem_baseSet b⟩
      linear := chart_linear r hr e
      contMDiffOn_coordChange := by
        intro i j a
        have h := (c.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
          (hs i j (c.symm (Pi.single a 1)))
        refine (h.mono (fun b hb ↦
          ⟨chart_base r hr e i ▸ hb.1, chart_base r hr e j ▸ hb.2⟩)).congr ?_
        intro b hb
        have hi : b ∈ (S.trivialization i).baseSet := chart_base r hr e i ▸ hb.1
        have hj : b ∈ (S.trivialization j).baseSet := chart_base r hr e j ▸ hb.2
        rw [chart_inverse r hr e i b hi]
        exact chart_rep r hr e j _ b _ hj _ }
  have frame_inverse {T : Type} [NormedAddCommGroup T] [NormedSpace ℂ T]
      [FiniteDimensional ℂ T] (r : ContRepresentation ℂ G T)
      (hr : Continuous (fun z : G × T ↦ r z.1 z.2))
      (hs : ∀ (i j : B) (v : T),
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, T) ∞
          (fun b : B ↦ r (τ i j b) v)
          ((S.trivialization i).baseSet ∩ (S.trivialization j).baseSet))
      {E : B → Type v} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
      [TopologicalSpace (TotalSpace Unit E)]
      (e : ComplexBundle.Iso (AssociatedVectorFiber hP r) E)
      (i b : B) (hb : b ∈ ((atlas r hr hs e).chart i).baseSet)
      (z : Fin (Module.finrank ℂ T) → ℂ) :
      ((atlas r hr hs e).frameLinearEquiv i b hb).symm z =
        e.linearEquiv b (associatedVectorFiberMk hP r
          ((S.trivialization i).toPartialEquiv.symm (b, 1))
          ((S.trivialization i).proj_symm_apply' (chart_base r hr e i ▸ hb))
          (c.symm z)) := by
    apply ((atlas r hr hs e).frameLinearEquiv i b hb).injective
    rw [LinearEquiv.apply_symm_apply]
    change z = (bundleChart r hr e i
      ⟨b, e.linearEquiv b (associatedVectorFiberMk hP r _ _ (c.symm z))⟩).2
    rw [chart_local r hr e i b (chart_base r hr e i ▸ hb), c.apply_symm_apply]
  -- A map with one fixed linear representative formula is smooth in these same charts.
  have smooth_map {T U : Type} [NormedAddCommGroup T] [NormedSpace ℂ T]
      [FiniteDimensional ℂ T] [NormedAddCommGroup U] [NormedSpace ℂ U]
      [FiniteDimensional ℂ U]
      (r : ContRepresentation ℂ G T)
      (hr : Continuous (fun z : G × T ↦ r z.1 z.2))
      (hs : ∀ (i j : B) (v : T),
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, T) ∞
          (fun b : B ↦ r (τ i j b) v)
          ((S.trivialization i).baseSet ∩ (S.trivialization j).baseSet))
      {E : B → Type v} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
      [TopologicalSpace (TotalSpace Unit E)]
      (e : ComplexBundle.Iso (AssociatedVectorFiber hP r) E)
      (s : ContRepresentation ℂ G U)
      (ht : Continuous (fun z : G × U ↦ s z.1 z.2))
      (hu : ∀ (i j : B) (v : U),
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, U) ∞
          (fun b : B ↦ s (τ i j b) v)
          ((S.trivialization i).baseSet ∩ (S.trivialization j).baseSet))
      {F : B → Type v} [∀ b, AddCommGroup (F b)] [∀ b, Module ℂ (F b)]
      [TopologicalSpace (TotalSpace Unit F)]
      (f : ComplexBundle.Iso (AssociatedVectorFiber hP s) F)
      (L : T →ₗ[ℂ] U) (a : ∀ b : B, E b →ₗ[ℂ] F b)
      (hmap : ∀ (p : P) (b : B) (hp : projection p = b) (v : T),
        a b (e.linearEquiv b (associatedVectorFiberMk hP r p hp v)) =
          f.linearEquiv b (associatedVectorFiberMk hP s p hp (L v))) :
      IsSmoothAtlasBundleMap (atlas r hr hs e) (atlas s ht hu f) a := by
    refine ⟨contMDiff_id, ?_⟩
    intro i j k
    have h := ((c (T := U)).toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
      (hu i j (L (c.symm (Pi.single k 1))))
    refine (h.mono (fun b hb ↦
      ⟨chart_base r hr e i ▸ hb.1, chart_base s ht f j ▸ hb.2⟩)).congr ?_
    intro b hb
    rcases hb with ⟨hb₀, hb₁⟩
    rw [dite_eq_left hb₀, frame_inverse r hr hs e i b hb₀]
    dsimp only [id_eq]
    erw [hmap]
    exact chart_rep s ht f j _ b _ (chart_base s ht f j ▸ hb₁) _
  let e := spinorBundleParityIso m hP
  let eV := ComplexBundle.Iso.refl (SpinorBundle m hP)
  let eW (a : ZMod 2) := ComplexBundle.Iso.refl (HalfSpinorBundle m hP a)
  let A := atlas ρ (continuous_complexSpinRepresentation m) full_smooth eV
  let H (a : ZMod 2) := atlas (σ a) (continuous_complexSpinParityRepresentation m a)
    (half_smooth a) (eW a)
  let C := atlas ρ (continuous_complexSpinRepresentation m) full_smooth e
  refine ⟨A, H, C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Every original full-spin representative uses exactly its specified principal chart.
    intro i
    refine ⟨i, c.toLinearEquiv,
      chart_base ρ (continuous_complexSpinRepresentation m) eV i, ?_⟩
    intro p b hp hb v
    exact chart_rep ρ (continuous_complexSpinRepresentation m) eV i p b hp hb v
  · intro a i
    refine ⟨i, c.toLinearEquiv,
      chart_base (σ a) (continuous_complexSpinParityRepresentation m a) (eW a) i, ?_⟩
    intro p b hp hb v
    exact chart_rep (σ a) (continuous_complexSpinParityRepresentation m a) (eW a)
      i p b hp hb v
  · -- The sum projections are the fixed exterior-parity projections on representatives.
    apply smooth_map ρ (continuous_complexSpinRepresentation m) full_smooth e
      (σ 0) (continuous_complexSpinParityRepresentation m 0) (half_smooth 0) (eW 0)
      ((LinearMap.fst ℂ (W 0) (W 1)).comp d.toLinearMap)
    intro p b hp v
    change ((spinorBundleParityIso m hP).linearEquiv b
      (associatedVectorFiberMk hP ρ p hp v)).1 = _
    rw [spinorBundleParityIso_apply]
    rfl
  · apply smooth_map ρ (continuous_complexSpinRepresentation m) full_smooth e
      (σ 1) (continuous_complexSpinParityRepresentation m 1) (half_smooth 1) (eW 1)
      ((LinearMap.snd ℂ (W 0) (W 1)).comp d.toLinearMap)
    intro p b hp v
    change ((spinorBundleParityIso m hP).linearEquiv b
      (associatedVectorFiberMk hP ρ p hp v)).2 = _
    rw [spinorBundleParityIso_apply]
    rfl
  · -- Inclusion uses the original zero vector in the other associated parity fiber.
    apply smooth_map (σ 0) (continuous_complexSpinParityRepresentation m 0)
      (half_smooth 0) (eW 0) ρ (continuous_complexSpinRepresentation m) full_smooth e
      (d.symm.toLinearMap.comp (LinearMap.inl ℂ (W 0) (W 1)))
    intro p b hp v
    change (associatedVectorFiberMk hP (σ 0) p hp v, 0) =
      (spinorBundleParityIso m hP).linearEquiv b
        (associatedVectorFiberMk hP ρ p hp (d.symm (v, 0)))
    rw [spinorBundleParityIso_apply, d.apply_symm_apply]
    exact Prod.ext rfl
      ((associatedVectorFiberMk_isLinear hP (σ 1) p hp).map_zero).symm
  · apply smooth_map (σ 1) (continuous_complexSpinParityRepresentation m 1)
      (half_smooth 1) (eW 1) ρ (continuous_complexSpinRepresentation m) full_smooth e
      (d.symm.toLinearMap.comp (LinearMap.inr ℂ (W 0) (W 1)))
    intro p b hp v
    change (0, associatedVectorFiberMk hP (σ 1) p hp v) =
      (spinorBundleParityIso m hP).linearEquiv b
        (associatedVectorFiberMk hP ρ p hp (d.symm (0, v)))
    rw [spinorBundleParityIso_apply, d.apply_symm_apply]
    exact Prod.ext
      ((associatedVectorFiberMk_isLinear hP (σ 0) p hp).map_zero).symm rfl
  · -- The original splitting is the identity on its original full-spin representative model.
    apply smooth_map ρ (continuous_complexSpinRepresentation m) full_smooth eV
      ρ (continuous_complexSpinRepresentation m) full_smooth e (LinearMap.id)
    intro p b hp v
    rfl
  · apply smooth_map ρ (continuous_complexSpinRepresentation m) full_smooth e
      ρ (continuous_complexSpinRepresentation m) full_smooth eV (LinearMap.id)
    intro p b hp v
    exact (e.linearEquiv b).symm_apply_apply _

/-- The full-spin smooth atlas selected on the original quotient and topology. -/
@[reducible]
def spinorBundleSmoothAtlas :
    SmoothComplexBundleAtlas.{u} (n := n) (SpinorBundle m hP) :=
  (exists_spinorBundle_smoothAtlases m hP S).choose

/-- The selected half-spin atlas, with the original fixed parity label. -/
@[reducible]
def halfSpinorBundleSmoothAtlas (i : ZMod 2) :
    SmoothComplexBundleAtlas.{u} (n := n) (HalfSpinorBundle m hP i) :=
  (exists_spinorBundle_smoothAtlases m hP S).choose_spec.choose i

/-- The selected direct-sum smooth atlas on the original pair of half-spin fibers. -/
@[reducible]
def spinorBundleParitySmoothAtlas :
    letI : ∀ b, Module ℂ (HalfSpinorBundle m hP 0 b × HalfSpinorBundle m hP 1 b) :=
      fun _b ↦ inferInstance
    SmoothComplexBundleAtlas.{u} (n := n)
      (HalfSpinorBundle m hP 0 ×ᵇ HalfSpinorBundle m hP 1) :=
  (exists_spinorBundle_smoothAtlases m hP S).choose_spec.choose_spec.choose

set_option linter.defProp false in
/-- Original representative charts, sum maps and parity maps for the same selected atlas triple. -/
def spinorBundleSmoothAtlases_compatibility :
    letI : ∀ b, Module ℂ (HalfSpinorBundle m hP 0 b × HalfSpinorBundle m hP 1 b) :=
      fun _b ↦ inferInstance
    S.IsAssociatedVectorAtlas hP (complexSpinContRepresentation m)
        (spinorBundleSmoothAtlas m hP S) ∧
      (∀ i : ZMod 2, S.IsAssociatedVectorAtlas hP (complexSpinParityContRepresentation m i)
        (halfSpinorBundleSmoothAtlas m hP S i)) ∧
      IsSmoothAtlasBundleMap (spinorBundleParitySmoothAtlas m hP S)
        (halfSpinorBundleSmoothAtlas m hP S 0) (fun b ↦
          LinearMap.fst ℂ (HalfSpinorBundle m hP 0 b) (HalfSpinorBundle m hP 1 b)) ∧
      IsSmoothAtlasBundleMap (spinorBundleParitySmoothAtlas m hP S)
        (halfSpinorBundleSmoothAtlas m hP S 1) (fun b ↦
          LinearMap.snd ℂ (HalfSpinorBundle m hP 0 b) (HalfSpinorBundle m hP 1 b)) ∧
      IsSmoothAtlasBundleMap (halfSpinorBundleSmoothAtlas m hP S 0)
        (spinorBundleParitySmoothAtlas m hP S) (fun b ↦
          LinearMap.inl ℂ (HalfSpinorBundle m hP 0 b) (HalfSpinorBundle m hP 1 b)) ∧
      IsSmoothAtlasBundleMap (halfSpinorBundleSmoothAtlas m hP S 1)
        (spinorBundleParitySmoothAtlas m hP S) (fun b ↦
          LinearMap.inr ℂ (HalfSpinorBundle m hP 0 b) (HalfSpinorBundle m hP 1 b)) ∧
      IsSmoothAtlasBundleMap (spinorBundleSmoothAtlas m hP S)
        (spinorBundleParitySmoothAtlas m hP S)
        (fun b ↦ ((spinorBundleParityIso m hP).linearEquiv b).toLinearMap) ∧
      IsSmoothAtlasBundleMap (spinorBundleParitySmoothAtlas m hP S)
        (spinorBundleSmoothAtlas m hP S)
        (fun b ↦ ((spinorBundleParityIso m hP).linearEquiv b).symm.toLinearMap) := by
  -- All structural maps and representative formulas come from one joint existence witness.
  exact (exists_spinorBundle_smoothAtlases m hP S).choose_spec.choose_spec.choose_spec

end AtiyahSinger
