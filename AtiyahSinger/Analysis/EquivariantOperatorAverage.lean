/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantConjugation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

import AtiyahSinger.Analysis.EquivariantAveragingAssembly
import AtiyahSinger.Analysis.EquivariantAveragingPrincipalSymbolAssembly
import AtiyahSinger.Analysis.EquivariantLocalAverage
import AtiyahSinger.Analysis.EquivariantSectionTopologyWeak
import AtiyahSinger.Analysis.EquivariantWeightedSymbolIntegral
import AtiyahSinger.Analysis.PseudodifferentialDistributions
import AtiyahSinger.Analysis.SmoothSectionIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Haar averaging of actual pseudodifferential operators

Public module ID: M0548.

The average is specified on every original smooth section and at every base
point by the normalized left Haar integral of `ρF(g) P ρE(g⁻¹)`. This integral
has values in the one finite-dimensional original fiber `F x`. We do not put
a fictitious norm on the smooth section space or take a Bochner integral there.
The existence theorem proves that these values define an original PDO of the
same real order, rather than assuming regularity of an averaged operator.

Sources: SG III.3.17--3.19 and the averaging argument for III.9.7, pp.214--215.
The full PDO quotient formulation and the precise parameter estimates below
are project supplements to that route. The same positive smooth base density
is retained; its invariance is unnecessary because transformed smooth kernels
keep the appropriate density ratio and absolute inverse Jacobian.

The given joint smooth actions and continuous group inversion give continuous
group parameters for every base derivative. Smoothness of group inversion is
not required: only base derivatives enter the averaging argument. In particular
the statements impose no `LieGroup` assumption. Compactness supplies uniform
estimates only after their joint parameter dependence has been established.

A fixed principal quotient class gives an order-lowering difference for each
group element, but that fact alone does not give uniform lower-order bounds.
The same-class theorem retains a supplementary saturated-seminorm, Baire and
cocycle argument to obtain those bounds. A separate authoritative reference
for this direct argument is not supplied here. No closedness of the lower-order
symbol subspace is assumed. PDO realization and fixed-class preservation are
proved in separate statements; evaluation, equivariance and support use the
same constructed average.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

include hM hT2 hSC hC hBorel hE hF hμ hG hAction

omit [T2Space G] in
/-- The original Haar formula defines a unique linear operator on actual smooth sections.
Its additional PDO order and principal-symbol properties are separate assertions below. -/
theorem existsUnique_smoothSectionAverage :
    ∃! Q : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F,
      ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
        (Q u).val x =
          ∫ g : G, ((σF.smoothSectionRepresentation IG hσF g)
            (P.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x
            ∂(Measure.haarMeasure (⊤ : PositiveCompacts G)) := by
  classical
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  let ρE := σE.smoothSectionRepresentation IG hσE
  let ρF := σF.smoothSectionRepresentation IG hσF
  let ν := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let C (g : G) : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F :=
    (ρF g).comp (P.toLinearMap.comp (ρE g⁻¹))
  have hfamily (u : smoothSections (n := n) (r := r) E) :
      Continuous (fun g : G ↦ B.smoothSectionEquiv.symm (C g u)) := by
    -- Inversion is used only as a continuous parameter map in the original smooth topology.
    have hinput : Continuous (fun g : G ↦ A.smoothSectionEquiv.symm (ρE g⁻¹ u)) :=
      (A.continuous_smoothSectionAction_of_isManifold IG σE hσE).comp
        (continuous_inv.prodMk (continuous_const (y := A.smoothSectionEquiv.symm u)))
    have hoperator := (P.continuous_smoothSectionMap A B).comp hinput
    exact (B.continuous_smoothSectionAction_of_isManifold IG σF hσF).comp
      (continuous_id.prodMk hoperator)
  have hint (u : smoothSections (n := n) (r := r) E) (x : M) :
      Integrable (fun g : G ↦ (C g u).val x) ν :=
    ((B.continuous_section_evaluation x).comp (hfamily u)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let Q : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F :=
    { toFun := fun u ↦ ⟨fun x ↦ ∫ g, (C g u).val x ∂ν,
        B.isSmoothSection_integral ν
          (fun g ↦ B.smoothSectionEquiv.symm (C g u)) (hfamily u)⟩
      map_add' := by
        intro u v
        apply Subtype.ext
        funext x
        change (∫ g, (C g (u + v)).val x ∂ν) =
          (∫ g, (C g u).val x ∂ν) + ∫ g, (C g v).val x ∂ν
        simp only [map_add, Submodule.coe_add, Pi.add_apply]
        exact integral_add (hint u x) (hint v x)
      map_smul' := by
        intro a u
        apply Subtype.ext
        funext x
        change (∫ g, (C g (a • u)).val x ∂ν) = a • ∫ g, (C g u).val x ∂ν
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply]
        exact integral_smul a _ }
  -- Equality is on the original fibers for every original input; extensionality gives uniqueness.
  refine ⟨Q, fun _ _ ↦ rfl, ?_⟩
  intro R hR
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  exact hR u x

/-- The pointwise Haar integral is realized by a unique original PDO of the same real order. -/
theorem existsUnique_average :
    ∃! Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m,
      ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
        (Q.toLinearMap u).val x =
          ∫ g : G, ((σF.smoothSectionRepresentation IG hσF g)
            (P.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x
            ∂(Measure.haarMeasure (⊤ : PositiveCompacts G)) := by
  classical
  -- In one fixed group neighborhood, the original amplitude family and its fixed native
  -- smooth remainder integrate to the same-order PDO with the prescribed fiber values.
  have hlocal := fun (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
      (g₀ : G) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f] ↦
        L.exists_local_weighted_average (μ := μ) IG σE σF hσE hσF g₀ c hc e f
  -- Two finite original chart refinements and a continuous group partition assemble those
  -- exact local amplitude integrals. The outer Fourier exchange uses uniform decay bounds.
  obtain ⟨Q, hQ⟩ := exists_pseudodifferential_average_of_local IG σE σF hσE hσF hlocal P
  refine ⟨Q, hQ, ?_⟩
  intro R hR
  -- Equality is in every original fiber for every original input; PDO membership is a proof.
  have hlinear : R.toLinearMap = Q.toLinearMap := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    exact (hR u x).trans (hQ u x).symm
  cases R
  cases Q
  cases hlinear
  rfl

/-- The actual normalized Haar average on the original smooth sections. -/
def average : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m :=
  Classical.choose (P.existsUnique_average IG σE σF hσE hσF).exists

/-- Evaluation of the average is the finite-dimensional Haar integral in the original fiber. -/
theorem average_apply (u : smoothSections (n := n) (r := r) E) (x : M) :
    ((P.average IG σE σF hσE hσF).toLinearMap u).val x =
      ∫ g : G, ((σF.smoothSectionRepresentation IG hσF g)
        (P.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x
        ∂(Measure.haarMeasure (⊤ : PositiveCompacts G)) := by
  -- The chosen PDO retains its defining identity in each original output fiber.
  exact (Classical.choose_spec (P.existsUnique_average IG σE σF hσE hσF).exists) u x

/-- Averaging by normalized left Haar measure makes the same original PDO equivariant. -/
theorem isEquivariant_average :
    (P.average IG σE σF hσE hσF).IsEquivariant IG σE σF hσE hσF := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let ρE := σE.smoothSectionRepresentation IG hσE
  let ρF := σF.smoothSectionRepresentation IG hσF
  let ν := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let L (g : G) (u : smoothSections (n := n) (r := r) E)
      (x : M) : F x := (ρF g (P.toLinearMap (ρE g⁻¹ u))).val x
  intro h
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  obtain ⟨y, rfl⟩ := MulAction.surjective h x
  -- The representation laws identify the same conjugated section before evaluation.
  have hconj (g : G) : L (h * g) (ρE h u) (h • y) =
      σF.linearMap h y (L g u y) := by
    have hin : ρE (h * g)⁻¹ (ρE h u) = ρE g⁻¹ u := by
      change (ρE (h * g)⁻¹ * ρE h) u = _
      rw [← map_mul]
      simp only [mul_inv_rev, inv_mul_cancel_right]
    have hout : ρF (h * g) (P.toLinearMap (ρE g⁻¹ u)) =
        ρF h (ρF g (P.toLinearMap (ρE g⁻¹ u))) := by
      rw [map_mul]
      rfl
    dsimp only [L]
    rw [hin, hout]
    exact σF.sectionLinearMap_smul h _ y
  -- Left translation in Haar measure moves the group action to the fixed fiber map.
  change ((P.average IG σE σF hσE hσF).toLinearMap (ρE h u)).val (h • y) =
    σF.sectionLinearMap h ((P.average IG σE σF hσE hσF).toLinearMap u).val (h • y)
  rw [σF.sectionLinearMap_smul, average_apply, average_apply]
  change (∫ g, L g (ρE h u) (h • y) ∂ν) =
    σF.linearMap h y (∫ g, L g u y ∂ν)
  rw [← integral_mul_left_eq_self (μ := ν) (fun g ↦ L g (ρE h u) (h • y)) h]
  simp_rw [hconj]
  -- A finite-dimensional fiber equivalence commutes with the Bochner integral.
  let C : F y ≃L[ℂ] F (h • y) :=
    (LinearEquiv.ofBijective (σF.linearMap h y)
      (σF.linearMap_bijective h y)).toContinuousLinearEquiv
  exact C.integral_comp_comm (fun g ↦ L g u y)

/-- A fixed original principal quotient class is unchanged by the actual Haar average. -/
theorem principalSymbol_average_of_fixed
    (hFixed : ∀ g : G,
      equivariantPrincipalSymbolRepresentation IG σE σF hσE hσF m g
        P.principalSymbol = P.principalSymbol) :
    (P.average IG σE σF hσE hσF).principalSymbol = P.principalSymbol := by
  classical
  let ν := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let J (w : G → ℂ) (hw : Continuous w) :=
    equivariantWeightedPrincipalSymbolIntegral IG σE σF hσE hσF ν w hw m
  -- Genuine weighted symbol integrals pass through finite group partitions before quotienting.
  have hJsum (N : ℕ) (w : Fin N → G → ℂ) (hw : ∀ j, Continuous (w j))
      (hone : ∀ g, ∑ j, w j g = 1) (pclass : GlobalPrincipalSymbolSpace E F m) :
      (∑ j, J (w j) (hw j) pclass) = J (fun _ ↦ 1) continuous_const pclass := by
    exact equivariantWeightedPrincipalSymbolIntegral_sum IG σE σF hσE hσF ν m
      w hw hone pclass
  -- Each local certificate retains one operator and one source symbol before choosing the weight.
  obtain ⟨Q, hQ, hQclass⟩ := exists_pseudodifferential_average_with_principalSymbol_of_local
    IG σE σF hσE hσF J hJsum
    (fun L g₀ c hc e f _ _ hbase ↦ by
      obtain ⟨U, hU, hg₀U, p, hp, hlocal⟩ :=
        L.exists_local_weighted_average_with_principalSymbol
          (μ := μ) IG σE σF hσE hσF g₀ c hc e f hbase
      refine ⟨U, hU, hg₀U, ?_⟩
      intro w hw hwsupp
      obtain ⟨R, hR, pbar, hpbar, hlower⟩ := hlocal w hw hwsupp
      refine ⟨R, hR, ?_⟩
      rw [hpbar, ← hp]
      change globalPrincipalSymbolClass E F m pbar =
        equivariantWeightedPrincipalSymbolIntegral IG σE σF hσE hσF ν w hw m
          (globalPrincipalSymbolClass E F m p)
      rw [equivariantWeightedPrincipalSymbolIntegral_class]
      apply (globalPrincipalSymbolClass_eq_iff E F m _ _).mpr
      exact hlower) P
  -- Extensional equality identifies this certified PDO with the original chosen average.
  have hsame : (P.average IG σE σF hσE hσF).toLinearMap = Q.toLinearMap := by
    ext u x
    exact (P.average_apply IG σE σF hσE hσF u x).trans (hQ u x).symm
  rw [(P.average IG σE σF hσE hσF).principalSymbol_eq_of_toLinearMap_eq μ Q hsame,
    hQclass]
  -- The Baire-cocycle lower-order estimates justify integration of the fixed-class defect.
  change equivariantWeightedPrincipalSymbolIntegral IG σE σF hσE hσF ν
    (fun _ ↦ 1) continuous_const m P.principalSymbol = _
  rw [equivariantWeightedPrincipalSymbolIntegral_one_of_fixed IG σE σF hσE hσF ν m
    P.principalSymbol hFixed]
  have hmass : ν.real Set.univ = 1 := by
    change (Measure.haarMeasure (⊤ : PositiveCompacts G) Set.univ).toReal = 1
    rw [show Measure.haarMeasure (⊤ : PositiveCompacts G) Set.univ = 1 from
      Measure.haarMeasure_self, ENNReal.toReal_one]
  rw [hmass, Complex.ofReal_one, one_smul]

/-- Averaging preserves both sides of operator support in a compact invariant subset. -/
theorem hasSectionOperatorSupport_average (K : Set M) (hK : IsCompact K)
    (hKInvariant : ∀ g : G, (fun x : M ↦ g • x) '' K ⊆ K)
    (hP : HasSectionOperatorSupport K P.toLinearMap) :
    HasSectionOperatorSupport K (P.average IG σE σF hσE hσF).toLinearMap := by
  constructor
  · intro u
    -- Every conjugate has output support in g*K, which lies in the same closed K.
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    have hzero (g : G) :
        ((σF.smoothSectionRepresentation IG hσF g)
          (P.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x = 0 := by
      by_contra hne
      have hmem := (P.hasSectionOperatorSupport_conjugate IG σE σF hσE hσF g K hP).1
        u (subset_closure hne)
      exact hxK (hKInvariant g hmem)
    apply hx
    rw [average_apply]
    simp only [hzero, integral_zero]
  · intro u hu
    -- The input condition uses disjoint closed support, retained for every g*K.
    have hzero (g : G) :
        (P.conjugate IG σE σF hσE hσF g).toLinearMap u = 0 :=
      (P.hasSectionOperatorSupport_conjugate IG σE σF hσE hσF g K hP).2 u
        (hu.mono_right (hKInvariant g))
    apply Subtype.ext
    funext x
    change ((P.average IG σE σF hσE hσF).toLinearMap u).val x = 0
    rw [average_apply]
    have hvalues (g : G) :
        ((σF.smoothSectionRepresentation IG hσF g)
          (P.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x = 0 :=
      congrArg (fun v : smoothSections (n := n) (r := q) F ↦ v.val x) (hzero g)
    simp only [hvalues, integral_zero]

end AtiyahSinger.PseudodifferentialOperator
