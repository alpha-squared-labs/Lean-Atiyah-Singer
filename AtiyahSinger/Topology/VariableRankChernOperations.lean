/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTensor
public import AtiyahSinger.Topology.ChernCharacterOperations
public import AtiyahSinger.Topology.GlobalChernLocalComparison
public import AtiyahSinger.Topology.HermitianMetricSum
public import AtiyahSinger.Topology.VariableRankChern

/-!
# Operations on the original locally varying-rank characteristic classes

Public module ID: M2268.

C02. These are identities for the actual integral Chern classes and rational
character components on the original Unit-topology bundle. Metrics on distinct
bundles are independently supplied and isomorphisms need not be unitary.
All fiber universes are independent. Pullback bases use the same universe,
as required by the existing singular-cohomology pullback functor.

Sources: SG III.11, the splitting principle and normalized line calculations,
Proposition 11.16 and Corollary 11.17; MS Section 14; Hatcher VBKT Theorem 3.2,
Proposition 3.3 and pp.109--110. The arbitrary-base singular-cohomology scope
uses the projective Leray--Hirsch construction of ChernClass. Locally
varying ranks are handled on the actual clopen rank strata and their common
refinements. No connectedness, compactness or uniform rank bound is imposed.
The tensor formula is degreewise and finite; no infinite direct-sum class is
asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory
open scoped TensorProduct

universe u v w z

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (hE : ContinuousHermitianMetric E)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The original integral Chern classes are independent of the auxiliary Hermitian metric. -/
theorem globalChernClass_metric_independent (hE' : ContinuousHermitianMetric E) (k : ℕ) :
    globalChernClass E hE k = globalChernClass E hE' k := by
  /- Restrict to each actual clopen rank stratum. Both prescribed components
  are the metric-independent fixed-rank Chern class of the same original
  bundle, transported only through the specified resizing isomorphisms.
  Metric-independent normalized line classes identify the two finite-rank
  constructions. The cohomology product over these actual clopen pieces
  detects equality of the two classes on the original base. -/
  -- Compare independent native norm presentations through their original Unit-topology iso.
  have hcompare {Y : Type u} [TopologicalSpace Y]
      (A B : Y → Type u) [∀ y, AddCommGroup (A y)] [∀ y, Module ℂ (A y)]
      [∀ y, AddCommGroup (B y)] [∀ y, Module ℂ (B y)]
      [TopologicalSpace (TotalSpace Unit A)] [TopologicalSpace (TotalSpace Unit B)]
      [IsFiniteRank A] [IsFiniteRank B]
      (hA : ContinuousHermitianMetric A) (hB : ContinuousHermitianMetric B)
      (n : ℕ) (hArank : ∀ y, Module.finrank ℂ (A y) = n)
      (hBrank : ∀ y, Module.finrank ℂ (B y) = n) (e : Iso A B) :
      (letI : ∀ y, NormedAddCommGroup (A y) := hA.fiberNormedAddCommGroup
       letI : ∀ y, InnerProductSpace ℂ (A y) := hA.fiberInnerProductSpace
       letI := nativeModelTopology A (EuclideanSpace ℂ (Fin n))
       letI := hA.nativeFiberBundle n hArank
       letI := hA.nativeVectorBundle n hArank
       chernClass n A (hA.nativeModelMetric n) k) =
      (letI : ∀ y, NormedAddCommGroup (B y) := hB.fiberNormedAddCommGroup
       letI : ∀ y, InnerProductSpace ℂ (B y) := hB.fiberInnerProductSpace
       letI := nativeModelTopology B (EuclideanSpace ℂ (Fin n))
       letI := hB.nativeFiberBundle n hBrank
       letI := hB.nativeVectorBundle n hBrank
       chernClass n B (hB.nativeModelMetric n) k) := by
    let : ∀ y, NormedAddCommGroup (A y) := hA.fiberNormedAddCommGroup
    let : ∀ y, InnerProductSpace ℂ (A y) := hA.fiberInnerProductSpace
    let : ∀ y, NormedAddCommGroup (B y) := hB.fiberNormedAddCommGroup
    let : ∀ y, InnerProductSpace ℂ (B y) := hB.fiberInnerProductSpace
    let := nativeModelTopology A (EuclideanSpace ℂ (Fin n))
    let := nativeModelTopology B (EuclideanSpace ℂ (Fin n))
    let := hA.nativeFiberBundle n hArank
    let := hA.nativeVectorBundle n hArank
    let := hB.nativeFiberBundle n hBrank
    let := hB.nativeVectorBundle n hBrank
    have e' : letI := modelTopology (EuclideanSpace ℂ (Fin n)) A
        letI := modelTopology (EuclideanSpace ℂ (Fin n)) B
        Iso A B := by
      rw [ContinuousHermitianMetric.modelTopology_nativeModelTopology,
        ContinuousHermitianMetric.modelTopology_nativeModelTopology]
      exact e
    exact chernClass_eq_of_iso n A (hA.nativeModelMetric n)
      B (hB.nativeModelMetric n) e' k
  let := cohomologyModelTopology E
  let := isFiniteRank_cohomologyModel E
  -- The actual clopen rank pieces detect equality of the two globally assembled classes.
  apply (singularCohomologyPullback_rankStrata_bijective ℤ (CohomologyModel E) (2 * k)).injective
  funext n
  have hleft := (existsUnique_globalChernClass E hE k).exists.choose_spec n
  have hright := (existsUnique_globalChernClass E hE' k).exists.choose_spec n
  change singularCohomologyPullback ℤ
    (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) n, X))
    (2 * k) (globalChernClass E hE k) = _ at hleft
  change singularCohomologyPullback ℤ
    (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) n, X))
    (2 * k) (globalChernClass E hE' k) = _ at hright
  change singularCohomologyPullback ℤ
    (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) n, X))
    (2 * k) (globalChernClass E hE k) =
    singularCohomologyPullback ℤ
      (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) n, X))
      (2 * k) (globalChernClass E hE' k)
  rw [hleft, hright]
  let F := Restrict (CohomologyModel E) (rankStratum (CohomologyModel E) n)
  let := isFiniteRank_restrict (E := CohomologyModel E)
    (rankStratum (CohomologyModel E) n : Set X)
  exact hcompare F F
    (rankHermitianMetric (CohomologyModel E) (cohomologyModelMetric E hE) n)
    (rankHermitianMetric (CohomologyModel E) (cohomologyModelMetric E hE') n)
    n (fun x ↦ x.property) (fun x ↦ x.property) (Iso.refl F)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The original rational character components are independent of the auxiliary metric. -/
theorem globalChernCharacterComponent_metric_independent
    (hE' : ContinuousHermitianMetric E) (k : ℕ) :
    globalChernCharacterComponent E hE k = globalChernCharacterComponent E hE' k := by
  /- On each original rank piece, both values are the same rational Newton
  polynomial in the metric-independent integral Chern classes. Degree zero
  is the actual rank on that piece. The clopen cohomology product detects
  equality, with no finite bound on the number of occupied rank pieces. -/
  -- Compare independent native norm presentations through their original Unit-topology iso.
  have hcompare {Y : Type u} [TopologicalSpace Y]
      (A B : Y → Type u) [∀ y, AddCommGroup (A y)] [∀ y, Module ℂ (A y)]
      [∀ y, AddCommGroup (B y)] [∀ y, Module ℂ (B y)]
      [TopologicalSpace (TotalSpace Unit A)] [TopologicalSpace (TotalSpace Unit B)]
      [IsFiniteRank A] [IsFiniteRank B]
      (hA : ContinuousHermitianMetric A) (hB : ContinuousHermitianMetric B)
      (n : ℕ) (hArank : ∀ y, Module.finrank ℂ (A y) = n)
      (hBrank : ∀ y, Module.finrank ℂ (B y) = n) (e : Iso A B) :
      (letI : ∀ y, NormedAddCommGroup (A y) := hA.fiberNormedAddCommGroup
       letI : ∀ y, InnerProductSpace ℂ (A y) := hA.fiberInnerProductSpace
       letI := nativeModelTopology A (EuclideanSpace ℂ (Fin n))
       letI := hA.nativeFiberBundle n hArank
       letI := hA.nativeVectorBundle n hArank
       chernCharacterComponent n A (hA.nativeModelMetric n) k) =
      (letI : ∀ y, NormedAddCommGroup (B y) := hB.fiberNormedAddCommGroup
       letI : ∀ y, InnerProductSpace ℂ (B y) := hB.fiberInnerProductSpace
       letI := nativeModelTopology B (EuclideanSpace ℂ (Fin n))
       letI := hB.nativeFiberBundle n hBrank
       letI := hB.nativeVectorBundle n hBrank
       chernCharacterComponent n B (hB.nativeModelMetric n) k) := by
    let : ∀ y, NormedAddCommGroup (A y) := hA.fiberNormedAddCommGroup
    let : ∀ y, InnerProductSpace ℂ (A y) := hA.fiberInnerProductSpace
    let : ∀ y, NormedAddCommGroup (B y) := hB.fiberNormedAddCommGroup
    let : ∀ y, InnerProductSpace ℂ (B y) := hB.fiberInnerProductSpace
    let := nativeModelTopology A (EuclideanSpace ℂ (Fin n))
    let := nativeModelTopology B (EuclideanSpace ℂ (Fin n))
    let := hA.nativeFiberBundle n hArank
    let := hA.nativeVectorBundle n hArank
    let := hB.nativeFiberBundle n hBrank
    let := hB.nativeVectorBundle n hBrank
    have e' : letI := modelTopology (EuclideanSpace ℂ (Fin n)) A
        letI := modelTopology (EuclideanSpace ℂ (Fin n)) B
        Iso A B := by
      rw [ContinuousHermitianMetric.modelTopology_nativeModelTopology,
        ContinuousHermitianMetric.modelTopology_nativeModelTopology]
      exact e
    exact chernCharacterComponent_eq_of_iso n n A (hA.nativeModelMetric n)
      B (hB.nativeModelMetric n) e' k
  let := cohomologyModelTopology E
  let := isFiniteRank_cohomologyModel E
  -- The actual clopen rank pieces detect equality of the two globally assembled classes.
  apply (singularCohomologyPullback_rankStrata_bijective ℚ (CohomologyModel E) (2 * k)).injective
  funext n
  have hleft := (existsUnique_globalChernCharacterComponent E hE k).exists.choose_spec n
  have hright := (existsUnique_globalChernCharacterComponent E hE' k).exists.choose_spec n
  change singularCohomologyPullback ℚ
    (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) n, X))
    (2 * k) (globalChernCharacterComponent E hE k) = _ at hleft
  change singularCohomologyPullback ℚ
    (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) n, X))
    (2 * k) (globalChernCharacterComponent E hE' k) = _ at hright
  change singularCohomologyPullback ℚ
    (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) n, X))
    (2 * k) (globalChernCharacterComponent E hE k) =
    singularCohomologyPullback ℚ
      (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) n, X))
      (2 * k) (globalChernCharacterComponent E hE' k)
  rw [hleft, hright]
  let F := Restrict (CohomologyModel E) (rankStratum (CohomologyModel E) n)
  let := isFiniteRank_restrict (E := CohomologyModel E)
    (rankStratum (CohomologyModel E) n : Set X)
  exact hcompare F F
    (rankHermitianMetric (CohomologyModel E) (cohomologyModelMetric E hE) n)
    (rankHermitianMetric (CohomologyModel E) (cohomologyModelMetric E hE') n)
    n (fun x ↦ x.property) (fun x ↦ x.property) (Iso.refl F)

/-- The degree-zero integral Chern class is the original cohomological unit. -/
theorem globalChernClass_zero :
    globalChernClass E hE 0 = singularCohomologyOne ℤ X := by
  /- Restrict both sides to every original rank stratum. The defining class
  there is the zeroth elementary symmetric polynomial, namely one, and
  singular pullback preserves the same unit. Equality on the clopen pieces
  gives equality on X. Zero-rank fibers and an empty base are included. -/
  let := cohomologyModelTopology E
  let := isFiniteRank_cohomologyModel E
  apply (singularCohomologyPullback_rankStrata_bijective ℤ (CohomologyModel E) 0).injective
  funext r
  have hspec := (existsUnique_globalChernClass E hE 0).exists.choose_spec r
  change singularCohomologyPullback ℤ
    (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) r, X)) 0
      (globalChernClass E hE 0) = _ at hspec
  change singularCohomologyPullback ℤ
    (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) r, X)) 0
      (globalChernClass E hE 0) = _
  rw [hspec]
  change rankStratumChernClass (CohomologyModel E) (cohomologyModelMetric E hE) r 0 =
    singularCohomologyPullback ℤ
      (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) r, X)) 0
      (singularCohomologyOne ℤ X)
  rw [singularCohomologyPullback_one]
  let F := Restrict (CohomologyModel E) (rankStratum (CohomologyModel E) r)
  let := isFiniteRank_restrict (E := CohomologyModel E)
    (rankStratum (CohomologyModel E) r : Set X)
  let hF := rankHermitianMetric (CohomologyModel E) (cohomologyModelMetric E hE) r
  let : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  let := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
  let := hF.nativeFiberBundle r (fun x ↦ x.property)
  let := hF.nativeVectorBundle r (fun x ↦ x.property)
  exact chernClass_zero r F (hF.nativeModelMetric r)

variable (F : X → Type w) [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (hF : ContinuousHermitianMetric F)

/-- An actual continuous complex bundle isomorphism preserves the original integral classes. -/
theorem globalChernClass_eq_of_iso (e : Iso E F) (k : ℕ) :
    globalChernClass E hE k = globalChernClass F hF k := by
  /- Stage 1: the original fiberwise linear equivalences identify the rank
  strata, including the original restricted topologies. After passing to
  that same piece, compare the actual normalized complex line classes on
  its flag splitting. Complex-linear maps preserve their positive real
  orientations. Elementary symmetric classes therefore agree after the
  same injective flag pullback, and hence on the original piece.
  Stage 2: metric independence removes any need for e to be unitary.
  The clopen cohomology product detects equality on X. The resizing models
  are related by their specified actual total-space isomorphisms, so no
  equality of independently chosen bases or topologies is an assumption. -/
  -- Use one original model and one rank inclusion for both characteristic classes.
  let M := CohomologyModel E
  let := cohomologyModelTopology E
  let := isFiniteRank_cohomologyModel E
  apply (singularCohomologyPullback_rankStrata_bijective ℤ M (2 * k)).injective
  funext r
  let S := rankStratum M r
  let i : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let V := Restrict M S
  let := isFiniteRank_restrict (E := M) (S : Set X)
  let hV := rankHermitianMetric M (cohomologyModelMetric E hE) r
  have ei : Iso V ((i : S → X) *ᵖ E) := (cohomologyModelIso E).restrict (S : Set X)
  change singularCohomologyPullback ℤ i (2 * k) (globalChernClass E hE k) =
    singularCohomologyPullback ℤ i (2 * k) (globalChernClass F hF k)
  -- The given e compares these same fibers, with their independent original metrics.
  exact (globalChernClass_pullback_eq_chernClass E hE i V hV r (fun x ↦ x.property) ei k).trans
    (globalChernClass_pullback_eq_chernClass F hF i V hV r (fun x ↦ x.property)
      (ei.trans (e.restrict (S : Set X))) k).symm

/-- An actual continuous complex bundle isomorphism preserves the original character. -/
theorem globalChernCharacterComponent_eq_of_iso (e : Iso E F) (k : ℕ) :
    globalChernCharacterComponent E hE k = globalChernCharacterComponent F hF k := by
  /- Restrict both character components to each rank piece of one cohomology
  model. The model isomorphism and its composite with e compare both
  restrictions with the same fixed-rank character component. Bijective
  rank-piece restriction then detects their equality on X. The metrics
  and fiber universes remain independent. -/
  -- Use one original model and one rank inclusion for both characteristic classes.
  let M := CohomologyModel E
  let := cohomologyModelTopology E
  let := isFiniteRank_cohomologyModel E
  apply (singularCohomologyPullback_rankStrata_bijective ℚ M (2 * k)).injective
  funext r
  let S := rankStratum M r
  let i : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let V := Restrict M S
  let := isFiniteRank_restrict (E := M) (S : Set X)
  let hV := rankHermitianMetric M (cohomologyModelMetric E hE) r
  have ei : Iso V ((i : S → X) *ᵖ E) := (cohomologyModelIso E).restrict (S : Set X)
  change singularCohomologyPullback ℚ i (2 * k) (globalChernCharacterComponent E hE k) =
    singularCohomologyPullback ℚ i (2 * k) (globalChernCharacterComponent F hF k)
  -- The given e compares these same fibers, with their independent original metrics.
  exact (globalChernCharacterComponent_pullback_eq_chernCharacterComponent E hE i V hV r
    (fun x ↦ x.property) ei k).trans
    (globalChernCharacterComponent_pullback_eq_chernCharacterComponent F hF i V hV r
      (fun x ↦ x.property)
      (ei.trans (e.restrict (S : Set X))) k).symm

variable (G : X → Type z) [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]
  (hG : ContinuousHermitianMetric G)

/-- The Whitney sum formula on the original possibly varying-rank complex bundles. -/
theorem globalChernClass_sum
    (e : letI := sumTopology (E := E) (F := F)
      Iso G (E ×ᵇ F)) (k : ℕ) :
    globalChernClass G hG k =
      ∑ i : Fin (k + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
            singularCohomology ℤ X (2 * (i.val + (k - i.val))) ≅
              singularCohomology ℤ X (2 * k)).hom
          (singularCohomologyEvenCup ℤ X i.val (k - i.val)
            (globalChernClass E hE i.val) (globalChernClass F hF (k - i.val))) := by
  /- Stage 1: use the common clopen refinement of the actual ranks of E
  and F. The given original isomorphism makes G have the sum rank on each
  such piece; that equality is not an extra global constant-rank premise.
  Stage 2: successively pull back to the actual flags of E and F. Their
  integral pullbacks are injective. The original sum is the concatenation
  of the two actual line families, so its elementary symmetric polynomial
  is the displayed finite convolution. Pullback preserves the original cup.
  Stage 3: descend through those injective pullbacks and then detect the
  equality on the clopen refinement. Independent metrics do not change
  the classes. Empty pieces, zero ranks and arbitrary fiber universes are
  retained, with no choice of a substitute direct-sum topology. -/
  -- First fix the original rank of E, then the rank of F over that same piece.
  let M := CohomologyModel E
  let N := CohomologyModel F
  let := cohomologyModelTopology E
  let := cohomologyModelTopology F
  let := isFiniteRank_cohomologyModel E
  let := isFiniteRank_cohomologyModel F
  apply (singularCohomologyPullback_rankStrata_bijective ℤ M (2 * k)).injective
  funext r
  let S := rankStratum M r
  let i : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let MS := Restrict M S
  let NS := Restrict N S
  let := isFiniteRank_restrict (E := M) (S : Set X)
  let := isFiniteRank_restrict (E := N) (S : Set X)
  apply (singularCohomologyPullback_rankStrata_bijective ℤ NS (2 * k)).injective
  funext s
  let T := rankStratum NS s
  let j : C(T, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let f := i.comp j
  let A := Restrict MS T
  let B := Restrict NS T
  let := isFiniteRank_restrict (E := MS) (T : Set S)
  let := isFiniteRank_restrict (E := NS) (T : Set S)
  let hA := ((cohomologyModelMetric E hE).pullback i).pullback j
  let hB := ((cohomologyModelMetric F hF).pullback i).pullback j
  have hrA (x : T) : Module.finrank ℂ (A x) = r := x.val.property
  have hrB (x : T) : Module.finrank ℂ (B x) = s := x.property
  -- Restrict the actual sum and its given isomorphism, retaining each original vector.
  let := sumTopology (E := E) (F := F)
  let := sumTopology (E := M) (F := N)
  let := sumTopology (E := MS) (F := NS)
  let := sumTopology (E := A) (F := B)
  let := isFiniteRank_sum (E := M) (F := N)
  let HS := Restrict (M ×ᵇ N) S
  let := isFiniteRank_restrict (E := M ×ᵇ N) (S : Set X)
  let H := Restrict HS T
  let := isFiniteRank_restrict (E := HS) (T : Set S)
  let hMN := (cohomologyModelMetric E hE).sum (cohomologyModelMetric F hF)
  let hH := (hMN.pullback i).pullback j
  have e₀ : Iso (M ×ᵇ N) G :=
    ((cohomologyModelIso E).sum (cohomologyModelIso F)).trans e.symm
  have eH : Iso H (A ×ᵇ B) :=
    ((restrictSumIso (E := M) (F := N) (S : Set X)).restrict (T : Set S)).trans
      (restrictSumIso (E := MS) (F := NS) (T : Set S))
  have eA : Iso A ((f : T → X) *ᵖ E) :=
    (pullbackCompIso (E := M) i j).trans ((cohomologyModelIso E).pullback f)
  have eB : Iso B ((f : T → X) *ᵖ F) :=
    (pullbackCompIso (E := N) i j).trans ((cohomologyModelIso F).pullback f)
  have eG : Iso H ((f : T → X) *ᵖ G) :=
    ((e₀.restrict (S : Set X)).restrict (T : Set S)).trans
      (pullbackCompIso (E := G) i j)
  have hrH (x : T) : Module.finrank ℂ (H x) = r + s := by
    let : FiniteDimensional ℂ (A x) := finite_fiber (E := A) x
    let : FiniteDimensional ℂ (B x) := finite_fiber (E := B) x
    change Module.finrank ℂ (A x × B x) = r + s
    rw [Module.finrank_prod, hrA x, hrB x]
  have hEA (n : ℕ) := globalChernClass_pullback_eq_chernClass
    E hE f A hA r hrA eA n
  have hFB (n : ℕ) := globalChernClass_pullback_eq_chernClass
    F hF f B hB s hrB eB n
  have hGH := globalChernClass_pullback_eq_chernClass
    G hG f H hH (r + s) hrH eG k
  -- Composition and linearity reduce the global comparison to this one fixed-rank sum.
  have hcomp (c : singularCohomology ℤ X (2 * k)) :
      singularCohomologyPullback ℤ j (2 * k)
          (singularCohomologyPullback ℤ i (2 * k) c) =
        singularCohomologyPullback ℤ f (2 * k) c := by
    symm
    change (singularCohomologyFunctor ℤ (2 * k)).map
      ((TopCat.ofHom i).op ≫ (TopCat.ofHom j).op) c = _
    rw [Functor.map_comp]
    rfl
  change singularCohomologyPullback ℤ j (2 * k)
      (singularCohomologyPullback ℤ i (2 * k) (globalChernClass G hG k)) =
    singularCohomologyPullback ℤ j (2 * k)
      (singularCohomologyPullback ℤ i (2 * k) _)
  rw [hcomp, hcomp, map_sum, hGH]
  let : ∀ x, NormedAddCommGroup (A x) := hA.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (A x) := hA.fiberInnerProductSpace
  let : ∀ x, NormedAddCommGroup (B x) := hB.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (B x) := hB.fiberInnerProductSpace
  let : ∀ x, NormedAddCommGroup (H x) := hH.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (H x) := hH.fiberInnerProductSpace
  let := nativeModelTopology A (EuclideanSpace ℂ (Fin r))
  let := nativeModelTopology B (EuclideanSpace ℂ (Fin s))
  let := nativeModelTopology H (EuclideanSpace ℂ (Fin (r + s)))
  let := hA.nativeFiberBundle r hrA
  let := hA.nativeVectorBundle r hrA
  let := hB.nativeFiberBundle s hrB
  let := hB.nativeVectorBundle s hrB
  let := hH.nativeFiberBundle (r + s) hrH
  let := hH.nativeVectorBundle (r + s) hrH
  have eH' : letI := modelTopology (EuclideanSpace ℂ (Fin r)) A
      letI := modelTopology (EuclideanSpace ℂ (Fin s)) B
      letI := modelTopology (EuclideanSpace ℂ (Fin (r + s))) H
      letI := sumTopology (E := A) (F := B)
      Iso H (A ×ᵇ B) := by
    rw [ContinuousHermitianMetric.modelTopology_nativeModelTopology,
      ContinuousHermitianMetric.modelTopology_nativeModelTopology,
      ContinuousHermitianMetric.modelTopology_nativeModelTopology]
    exact eH
  apply (chernClass_sum r A (hA.nativeModelMetric r) s
    B (hB.nativeModelMetric s) (r + s) H (hH.nativeModelMetric (r + s)) eH' k).trans
  -- The original degree transports commute with pullback, as do the actual cup products.
  have htransport {m n : ℕ} (h : m = n) (c : singularCohomology ℤ X m) :
      singularCohomologyPullback ℤ f n
          ((eqToIso (congrArg (singularCohomology ℤ X) h)).hom c) =
        (eqToIso (congrArg (singularCohomology ℤ T) h)).hom
          (singularCohomologyPullback ℤ f m c) := by
    subst n
    rfl
  apply Finset.sum_congr rfl
  intro l hl
  symm
  rw [htransport (congrArg (2 * ·) (Nat.add_sub_of_le (Nat.le_of_lt_succ l.isLt))),
    singularCohomologyPullback_evenCup, hEA, hFB]
  rfl

/-- The actual character takes the original direct-sum bundle to addition in every degree. -/
theorem globalChernCharacterComponent_sum
    (e : letI := sumTopology (E := E) (F := F)
      Iso G (E ×ᵇ F)) (k : ℕ) :
    globalChernCharacterComponent G hG k =
      globalChernCharacterComponent E hE k + globalChernCharacterComponent F hF k := by
  /- Restrict to the common original clopen rank pieces. Use successive
  flags of E and F, where e identifies G with their concatenated actual
  line factors. The normalized power sum therefore splits into the two
  original power sums, also in degree zero. Injectivity descends the fixed
  piece identity, and clopen detection returns it to X. No metric on G is
  required to equal a chosen sum metric, and no occupied piece is assumed. -/
  -- First fix the original rank of E, then the rank of F over that same piece.
  let M := CohomologyModel E
  let N := CohomologyModel F
  let := cohomologyModelTopology E
  let := cohomologyModelTopology F
  let := isFiniteRank_cohomologyModel E
  let := isFiniteRank_cohomologyModel F
  apply (singularCohomologyPullback_rankStrata_bijective ℚ M (2 * k)).injective
  funext r
  let S := rankStratum M r
  let i : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let MS := Restrict M S
  let NS := Restrict N S
  let := isFiniteRank_restrict (E := M) (S : Set X)
  let := isFiniteRank_restrict (E := N) (S : Set X)
  apply (singularCohomologyPullback_rankStrata_bijective ℚ NS (2 * k)).injective
  funext s
  let T := rankStratum NS s
  let j : C(T, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let f := i.comp j
  let A := Restrict MS T
  let B := Restrict NS T
  let := isFiniteRank_restrict (E := MS) (T : Set S)
  let := isFiniteRank_restrict (E := NS) (T : Set S)
  let hA := ((cohomologyModelMetric E hE).pullback i).pullback j
  let hB := ((cohomologyModelMetric F hF).pullback i).pullback j
  have hrA (x : T) : Module.finrank ℂ (A x) = r := x.val.property
  have hrB (x : T) : Module.finrank ℂ (B x) = s := x.property
  -- Restrict the actual sum and its given isomorphism, retaining each original vector.
  let := sumTopology (E := E) (F := F)
  let := sumTopology (E := M) (F := N)
  let := sumTopology (E := MS) (F := NS)
  let := sumTopology (E := A) (F := B)
  let := isFiniteRank_sum (E := M) (F := N)
  let HS := Restrict (M ×ᵇ N) S
  let := isFiniteRank_restrict (E := M ×ᵇ N) (S : Set X)
  let H := Restrict HS T
  let := isFiniteRank_restrict (E := HS) (T : Set S)
  let hMN := (cohomologyModelMetric E hE).sum (cohomologyModelMetric F hF)
  let hH := (hMN.pullback i).pullback j
  have e₀ : Iso (M ×ᵇ N) G :=
    ((cohomologyModelIso E).sum (cohomologyModelIso F)).trans e.symm
  have eH : Iso H (A ×ᵇ B) :=
    ((restrictSumIso (E := M) (F := N) (S : Set X)).restrict (T : Set S)).trans
      (restrictSumIso (E := MS) (F := NS) (T : Set S))
  have eA : Iso A ((f : T → X) *ᵖ E) :=
    (pullbackCompIso (E := M) i j).trans ((cohomologyModelIso E).pullback f)
  have eB : Iso B ((f : T → X) *ᵖ F) :=
    (pullbackCompIso (E := N) i j).trans ((cohomologyModelIso F).pullback f)
  have eG : Iso H ((f : T → X) *ᵖ G) :=
    ((e₀.restrict (S : Set X)).restrict (T : Set S)).trans
      (pullbackCompIso (E := G) i j)
  have hrH (x : T) : Module.finrank ℂ (H x) = r + s := by
    let : FiniteDimensional ℂ (A x) := finite_fiber (E := A) x
    let : FiniteDimensional ℂ (B x) := finite_fiber (E := B) x
    change Module.finrank ℂ (A x × B x) = r + s
    rw [Module.finrank_prod, hrA x, hrB x]
  have hEA := globalChernCharacterComponent_pullback_eq_chernCharacterComponent
    E hE f A hA r hrA eA k
  have hFB := globalChernCharacterComponent_pullback_eq_chernCharacterComponent
    F hF f B hB s hrB eB k
  have hGH := globalChernCharacterComponent_pullback_eq_chernCharacterComponent
    G hG f H hH (r + s) hrH eG k
  -- Composition and linearity reduce the global comparison to this one fixed-rank sum.
  have hcomp (c : singularCohomology ℚ X (2 * k)) :
      singularCohomologyPullback ℚ j (2 * k)
          (singularCohomologyPullback ℚ i (2 * k) c) =
        singularCohomologyPullback ℚ f (2 * k) c := by
    symm
    change (singularCohomologyFunctor ℚ (2 * k)).map
      ((TopCat.ofHom i).op ≫ (TopCat.ofHom j).op) c = _
    rw [Functor.map_comp]
    rfl
  change singularCohomologyPullback ℚ j (2 * k)
      (singularCohomologyPullback ℚ i (2 * k) (globalChernCharacterComponent G hG k)) =
    singularCohomologyPullback ℚ j (2 * k)
      (singularCohomologyPullback ℚ i (2 * k)
        (globalChernCharacterComponent E hE k + globalChernCharacterComponent F hF k))
  rw [hcomp, hcomp, map_add, hEA, hFB, hGH]
  let : ∀ x, NormedAddCommGroup (A x) := hA.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (A x) := hA.fiberInnerProductSpace
  let : ∀ x, NormedAddCommGroup (B x) := hB.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (B x) := hB.fiberInnerProductSpace
  let : ∀ x, NormedAddCommGroup (H x) := hH.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (H x) := hH.fiberInnerProductSpace
  let := nativeModelTopology A (EuclideanSpace ℂ (Fin r))
  let := nativeModelTopology B (EuclideanSpace ℂ (Fin s))
  let := nativeModelTopology H (EuclideanSpace ℂ (Fin (r + s)))
  let := hA.nativeFiberBundle r hrA
  let := hA.nativeVectorBundle r hrA
  let := hB.nativeFiberBundle s hrB
  let := hB.nativeVectorBundle s hrB
  let := hH.nativeFiberBundle (r + s) hrH
  let := hH.nativeVectorBundle (r + s) hrH
  have eH' : letI := modelTopology (EuclideanSpace ℂ (Fin r)) A
      letI := modelTopology (EuclideanSpace ℂ (Fin s)) B
      letI := modelTopology (EuclideanSpace ℂ (Fin (r + s))) H
      letI := sumTopology (E := A) (F := B)
      Iso H (A ×ᵇ B) := by
    rw [ContinuousHermitianMetric.modelTopology_nativeModelTopology,
      ContinuousHermitianMetric.modelTopology_nativeModelTopology,
      ContinuousHermitianMetric.modelTopology_nativeModelTopology]
    exact eH
  exact chernCharacterComponent_sum r s A (hA.nativeModelMetric r)
    B (hB.nativeModelMetric s) (r + s) H (hH.nativeModelMetric (r + s)) eH' k

set_option maxHeartbeats 1000000 in
-- Descend the finite tensor cup convolution through the same two original rank decompositions.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual tensor product gives the finite cup convolution of the original character. -/
theorem globalChernCharacterComponent_tensor
    (e : letI := tensorTopology (E := E) (F := F)
      Iso G (fun x ↦ E x ⊗[ℂ] F x)) (k : ℕ) :
    globalChernCharacterComponent G hG k =
      ∑ i : Fin (k + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
            singularCohomology ℚ X (2 * (i.val + (k - i.val))) ≅
              singularCohomology ℚ X (2 * k)).hom
          (singularCohomologyEvenCup ℚ X i.val (k - i.val)
            (globalChernCharacterComponent E hE i.val)
            (globalChernCharacterComponent F hF (k - i.val))) := by
  -- First fix the original rank of E, then the rank of F over that same piece.
  let M := CohomologyModel E
  let N := CohomologyModel F
  let K := CohomologyModel G
  let := cohomologyModelTopology E
  let := cohomologyModelTopology F
  let := cohomologyModelTopology G
  let := isFiniteRank_cohomologyModel E
  let := isFiniteRank_cohomologyModel F
  let := isFiniteRank_cohomologyModel G
  apply (singularCohomologyPullback_rankStrata_bijective ℚ M (2 * k)).injective
  funext r
  let S := rankStratum M r
  let i : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let MS := Restrict M S
  let NS := Restrict N S
  let := isFiniteRank_restrict (E := M) (S : Set X)
  let := isFiniteRank_restrict (E := N) (S : Set X)
  apply (singularCohomologyPullback_rankStrata_bijective ℚ NS (2 * k)).injective
  funext s
  let T := rankStratum NS s
  let j : C(T, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let f := i.comp j
  let A := Restrict MS T
  let B := Restrict NS T
  let := isFiniteRank_restrict (E := MS) (T : Set S)
  let := isFiniteRank_restrict (E := NS) (T : Set S)
  let hA := ((cohomologyModelMetric E hE).pullback i).pullback j
  let hB := ((cohomologyModelMetric F hF).pullback i).pullback j
  have hrA (x : T) : Module.finrank ℂ (A x) = r := x.val.property
  have hrB (x : T) : Module.finrank ℂ (B x) = s := x.property
  -- Use the original third bundle model, so its supplied metric stays independent of the tensor.
  let KS := Restrict K S
  let := isFiniteRank_restrict (E := K) (S : Set X)
  let H := Restrict KS T
  let := isFiniteRank_restrict (E := KS) (T : Set S)
  let hH := ((cohomologyModelMetric G hG).pullback i).pullback j
  let := tensorTopology (E := E) (F := F)
  let := tensorTopology (E := A) (F := B)
  have eA : Iso A ((f : T → X) *ᵖ E) :=
    (pullbackCompIso (E := M) i j).trans ((cohomologyModelIso E).pullback f)
  have eB : Iso B ((f : T → X) *ᵖ F) :=
    (pullbackCompIso (E := N) i j).trans ((cohomologyModelIso F).pullback f)
  have eG : Iso H ((f : T → X) *ᵖ G) :=
    (pullbackCompIso (E := K) i j).trans ((cohomologyModelIso G).pullback f)
  let := tensorTopology (E := (f : T → X) *ᵖ E) (F := (f : T → X) *ᵖ F)
  have eH : Iso H (fun x ↦ A x ⊗[ℂ] B x) :=
    (eG.trans (e.pullback f)).trans
      ((pullbackTensorIso (E := E) (F := F) f).trans (eA.symm.tensor eB.symm))
  have hrH (x : T) : Module.finrank ℂ (H x) = r * s := by
    let : FiniteDimensional ℂ (A x) := finite_fiber (E := A) x
    let : FiniteDimensional ℂ (B x) := finite_fiber (E := B) x
    exact (eH.linearEquiv x).finrank_eq.trans (by
      rw [Module.finrank_tensorProduct, hrA x, hrB x])
  have hEA (n : ℕ) := globalChernCharacterComponent_pullback_eq_chernCharacterComponent
    E hE f A hA r hrA eA n
  have hFB (n : ℕ) := globalChernCharacterComponent_pullback_eq_chernCharacterComponent
    F hF f B hB s hrB eB n
  have hGH := globalChernCharacterComponent_pullback_eq_chernCharacterComponent
    G hG f H hH (r * s) hrH eG k
  have hcomp (c : singularCohomology ℚ X (2 * k)) :
      singularCohomologyPullback ℚ j (2 * k)
          (singularCohomologyPullback ℚ i (2 * k) c) =
        singularCohomologyPullback ℚ f (2 * k) c := by
    symm
    change (singularCohomologyFunctor ℚ (2 * k)).map
      ((TopCat.ofHom i).op ≫ (TopCat.ofHom j).op) c = _
    rw [Functor.map_comp]
    rfl
  change singularCohomologyPullback ℚ j (2 * k)
      (singularCohomologyPullback ℚ i (2 * k) (globalChernCharacterComponent G hG k)) =
    singularCohomologyPullback ℚ j (2 * k)
      (singularCohomologyPullback ℚ i (2 * k) _)
  rw [hcomp, hcomp, hGH, map_sum]
  let : ∀ x, NormedAddCommGroup (A x) := hA.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (A x) := hA.fiberInnerProductSpace
  let : ∀ x, NormedAddCommGroup (B x) := hB.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (B x) := hB.fiberInnerProductSpace
  let : ∀ x, NormedAddCommGroup (H x) := hH.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (H x) := hH.fiberInnerProductSpace
  let := nativeModelTopology A (EuclideanSpace ℂ (Fin r))
  let := nativeModelTopology B (EuclideanSpace ℂ (Fin s))
  let := nativeModelTopology H (EuclideanSpace ℂ (Fin (r * s)))
  let := hA.nativeFiberBundle r hrA
  let := hA.nativeVectorBundle r hrA
  let := hB.nativeFiberBundle s hrB
  let := hB.nativeVectorBundle s hrB
  let := hH.nativeFiberBundle (r * s) hrH
  let := hH.nativeVectorBundle (r * s) hrH
  have eH' : letI := modelTopology (EuclideanSpace ℂ (Fin r)) A
      letI := modelTopology (EuclideanSpace ℂ (Fin s)) B
      letI := modelTopology (EuclideanSpace ℂ (Fin (r * s))) H
      letI := tensorTopology (E := A) (F := B)
      Iso H (fun x ↦ A x ⊗[ℂ] B x) := by
    rw [ContinuousHermitianMetric.modelTopology_nativeModelTopology,
      ContinuousHermitianMetric.modelTopology_nativeModelTopology,
      ContinuousHermitianMetric.modelTopology_nativeModelTopology]
    exact eH
  -- The fixed-rank tensor law applies to these same three restricted original models.
  apply (chernCharacterComponent_tensor r s A (hA.nativeModelMetric r)
    B (hB.nativeModelMetric s) (r * s) H (hH.nativeModelMetric (r * s)) eH' k).trans
  have htransport {m n : ℕ} (h : m = n) (c : singularCohomology ℚ X m) :
      singularCohomologyPullback ℚ f n
          ((eqToIso (congrArg (singularCohomology ℚ X) h)).hom c) =
        (eqToIso (congrArg (singularCohomology ℚ T) h)).hom
          (singularCohomologyPullback ℚ f m c) := by
    subst n
    rfl
  apply Finset.sum_congr rfl
  intro l hl
  symm
  rw [htransport (congrArg (2 * ·) (Nat.add_sub_of_le (Nat.le_of_lt_succ l.isLt))),
    singularCohomologyPullback_evenCup, hEA, hFB]
  rfl

/-- The original integral classes commute with the specified actual bundle pullback. -/
theorem globalChernClass_pullback
    {Y : Type u} [TopologicalSpace Y] (f : C(Y, X))
    (V : Y → Type w) [∀ y, AddCommGroup (V y)] [∀ y, Module ℂ (V y)]
    [TopologicalSpace (TotalSpace Unit V)] [IsFiniteRank V]
    (hV : ContinuousHermitianMetric V) (e : Iso V ((f : Y → X) *ᵖ E)) (k : ℕ) :
    globalChernClass V hV k =
      singularCohomologyPullback ℤ f (2 * k) (globalChernClass E hE k) := by
  /- The isomorphism e identifies the rank pieces of V with the inverse
  images of the original rank pieces of E. On each piece, normalized
  complex-line Thom classes and their zero-section Euler restrictions are
  natural under that same actual map. The elementary symmetric flag formula
  and the original injective flag pullback therefore give integral Chern
  naturality. Detect equality on the clopen decomposition of Y. The supplied
  metric on V may differ from the pullback metric; metric independence
  identifies the two values. Neither properness nor smoothness is required. -/
  -- Detect equality on the actual rank strata of the specified model of V.
  let M := CohomologyModel V
  let := cohomologyModelTopology V
  let := isFiniteRank_cohomologyModel V
  apply (singularCohomologyPullback_rankStrata_bijective ℤ M (2 * k)).injective
  funext r
  let S := rankStratum M r
  let i : C(S, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let A := Restrict M S
  let := isFiniteRank_restrict (E := M) (S : Set Y)
  let hA := rankHermitianMetric M (cohomologyModelMetric V hV) r
  have ei : Iso A ((i : S → Y) *ᵖ V) := (cohomologyModelIso V).restrict (S : Set Y)
  have ef : Iso A (((f.comp i : C(S, X)) : S → X) *ᵖ E) :=
    (ei.trans (e.pullback i)).trans (pullbackCompIso (E := E) f i)
  have hi := globalChernClass_pullback_eq_chernClass V hV i A hA r
    (fun x ↦ x.property) ei k
  have hf := globalChernClass_pullback_eq_chernClass E hE (f.comp i) A hA r
    (fun x ↦ x.property) ef k
  change singularCohomologyPullback ℤ i (2 * k) (globalChernClass V hV k) =
    singularCohomologyPullback ℤ i (2 * k)
      (singularCohomologyPullback ℤ f (2 * k) (globalChernClass E hE k))
  -- Both pullbacks equal the same fixed-rank class on A; compose the original maps.
  apply hi.trans
  apply hf.symm.trans
  change (singularCohomologyFunctor ℤ (2 * k)).map
    ((TopCat.ofHom f).op ≫ (TopCat.ofHom i).op) _ = _
  rw [Functor.map_comp]
  rfl

/-- The original rational character commutes with the specified actual bundle pullback. -/
theorem globalChernCharacterComponent_pullback
    {Y : Type u} [TopologicalSpace Y] (f : C(Y, X))
    (V : Y → Type w) [∀ y, AddCommGroup (V y)] [∀ y, Module ℂ (V y)]
    [TopologicalSpace (TotalSpace Unit V)] [IsFiniteRank V]
    (hV : ContinuousHermitianMetric V) (e : Iso V ((f : Y → X) *ᵖ E)) (k : ℕ) :
    globalChernCharacterComponent V hV k =
      singularCohomologyPullback ℚ f (2 * k) (globalChernCharacterComponent E hE k) := by
  /- Restrict to the inverse images of the original rank strata. Integral
  Chern naturality and compatibility of coefficient change and cup products
  with the same singular pullback identify every Newton-polynomial component.
  Degree zero is the pulled-back original rank function. Clopen detection
  then identifies the classes on Y. The actual isomorphism e uses the
  inherited pullback topology and does not supply any characteristic-class
  equality. Independent metrics and fiber universes are allowed. -/
  -- Detect equality on the actual rank strata of the specified model of V.
  let M := CohomologyModel V
  let := cohomologyModelTopology V
  let := isFiniteRank_cohomologyModel V
  apply (singularCohomologyPullback_rankStrata_bijective ℚ M (2 * k)).injective
  funext r
  let S := rankStratum M r
  let i : C(S, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let A := Restrict M S
  let := isFiniteRank_restrict (E := M) (S : Set Y)
  let hA := rankHermitianMetric M (cohomologyModelMetric V hV) r
  have ei : Iso A ((i : S → Y) *ᵖ V) := (cohomologyModelIso V).restrict (S : Set Y)
  have ef : Iso A (((f.comp i : C(S, X)) : S → X) *ᵖ E) :=
    (ei.trans (e.pullback i)).trans (pullbackCompIso (E := E) f i)
  have hi := globalChernCharacterComponent_pullback_eq_chernCharacterComponent V hV i A hA r
    (fun x ↦ x.property) ei k
  have hf := globalChernCharacterComponent_pullback_eq_chernCharacterComponent
    E hE (f.comp i) A hA r
    (fun x ↦ x.property) ef k
  change singularCohomologyPullback ℚ i (2 * k) (globalChernCharacterComponent V hV k) =
    singularCohomologyPullback ℚ i (2 * k)
      (singularCohomologyPullback ℚ f (2 * k) (globalChernCharacterComponent E hE k))
  -- Both pullbacks equal the same fixed-rank class on A; compose the original maps.
  apply hi.trans
  apply hf.symm.trans
  change (singularCohomologyFunctor ℚ (2 * k)).map
    ((TopCat.ofHom f).op ≫ (TopCat.ofHom i).op) _ = _
  rw [Functor.map_comp]
  rfl

end AtiyahSinger.ComplexBundle
