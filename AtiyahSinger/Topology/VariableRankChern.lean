/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleCohomologyModel
public import AtiyahSinger.Topology.ChernCharacterOperations
public import AtiyahSinger.Topology.RankStratumCohomology
public import AtiyahSinger.Topology.VariableRankSplittingPrinciple

/-!
# Characteristic classes on the original locally varying-rank base

Public module ID: M2267.

C02. The actual clopen rank decomposition assembles the existing normalized
classes into original-base cohomology. Singular cochains on a topological sum
form a product, not a direct sum. Consequently ranks may be unbounded and no
compactness, connectedness or positive rank is needed.

The universe-compatible fiber model is explicitly isomorphic to the original
bundle with its transported original metric. It leaves the base and its
cohomology unchanged. The original-rank comparison below recovers precisely
the normalized rank-piece root construction, rather than new characteristic data.

Sources: SG III.11 (11.22)--(11.23); Hatcher VBKT p.71 and pp.109--110.
The cochain-product assembly and universe transport are project supplements.
All components remain degreewise; no unsupported infinite direct sum occurs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u v

attribute [local instance] cohomologyModelTopology isFiniteRank_cohomologyModel

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E)

/-- The normalized integral classes assemble uniquely across the actual clopen rank pieces. -/
theorem existsUnique_globalChernClass (k : ℕ) :
    ∃! c : singularCohomology ℤ X (2 * k), ∀ r : ℕ,
      singularCohomologyPullback ℤ
          (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) r, X))
          (2 * k) c =
        rankStratumChernClass (CohomologyModel E) (cohomologyModelMetric E h) r k := by
  /- Stage 1: every singular simplex lies in one rank stratum: its connected
  domain maps through the locally constant original rank function. Thus the
  original singular chain complex decomposes as the direct sum of its rank
  pieces, and its dual cochain complex is their product.
  Stage 2: products of modules preserve kernels and surjections, so degreewise
  cohomology is the product of the actual rank-piece cohomologies. Assemble
  the already constructed normalized integral Chern classes through this
  canonical comparison. Bijectivity of restriction gives existence.
  Stage 3: restriction detects equality and proves uniqueness. The model's
  specified fiber isomorphism and transported metric keep each rank and
  normalized class tied to the original bundle, including empty pieces. -/
  obtain ⟨c, hc, huniq⟩ :=
    (singularCohomologyPullback_rankStrata_bijective ℤ (CohomologyModel E) (2 * k)).existsUnique
      (fun r ↦ rankStratumChernClass (CohomologyModel E) (cohomologyModelMetric E h) r k)
  refine ⟨c, fun r ↦ congrFun hc r, ?_⟩
  intro y hy
  exact huniq y (funext hy)

/-- The integral Chern class of the original locally finite-rank complex bundle. -/
def globalChernClass (k : ℕ) : singularCohomology ℤ X (2 * k) :=
  (existsUnique_globalChernClass E h k).exists.choose

/-- The existing normalized Chern-character components assemble on the same original base. -/
theorem existsUnique_globalChernCharacterComponent (k : ℕ) :
    ∃! c : singularCohomology ℚ X (2 * k), ∀ r : ℕ,
      singularCohomologyPullback ℚ
          (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum (CohomologyModel E) r, X))
          (2 * k) c =
        rankStratumChernCharacterComponent (CohomologyModel E)
          (cohomologyModelMetric E h) r k := by
  /- Use the same cochain-product comparison as for integral Chern classes.
  Each prescribed component is the Newton power sum in the normalized
  integral roots, rationalized and divided by k!. Bijective restriction
  assembles this family uniquely. The zeroth component is the locally
  constant rank class. No uniform rank bound or finite base dimension is
  required, since the construction is in one cohomological degree. -/
  obtain ⟨c, hc, huniq⟩ :=
    (singularCohomologyPullback_rankStrata_bijective ℚ (CohomologyModel E) (2 * k)).existsUnique
      (fun r ↦ rankStratumChernCharacterComponent (CohomologyModel E)
        (cohomologyModelMetric E h) r k)
  refine ⟨c, fun r ↦ congrFun hc r, ?_⟩
  intro y hy
  exact huniq y (funext hy)

/-- The degree-2k rational Chern character of the original locally finite-rank bundle. -/
def globalChernCharacterComponent (k : ℕ) : singularCohomology ℚ X (2 * k) :=
  (existsUnique_globalChernCharacterComponent E h k).exists.choose

section OriginalRankComparison

variable (F : X → Type u) [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (hF : ContinuousHermitianMetric F)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The global classes restrict to the normalized integral and rational rank-piece classes.
Both comparisons use the same original bundle and metric. -/
theorem globalChern_rank_restriction (r k : ℕ) :
    singularCohomologyPullback ℤ
        (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum F r, X)) (2 * k)
        (globalChernClass F hF k) = rankStratumChernClass F hF r k ∧
      singularCohomologyPullback ℚ
        (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum F r, X)) (2 * k)
        (globalChernCharacterComponent F hF k) =
          rankStratumChernCharacterComponent F hF r k := by
  /- Restrict cohomologyModelIso to the corresponding original rank locus.
  Its fiber isomorphism preserves the complex orientation and normalized
  line classes; the model metric is exactly the transported original form.
  Therefore the rank-stratum Chern and character constructions agree on
  these same rank pieces. Apply the assembly specifications and their
  natural restriction comparison. Neither a different root normalization
  nor a replacement topology on the original flag lines is introduced. -/
  constructor
  · -- The integral class uses the same original normalized Chern construction.
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
    let := cohomologyModelTopology F
    let := isFiniteRank_cohomologyModel F
    have hstr : rankStratum (CohomologyModel F) r = rankStratum F r := by
      ext x
      change Module.finrank ℂ (CohomologyModel F x) = r ↔ Module.finrank ℂ (F x) = r
      rw [(cohomologyModelLinearEquiv F x).finrank_eq]
    have hretarget (s : TopologicalSpace.Opens X)
        (hs : s = rankStratum (CohomologyModel F) r)
        (hr : ∀ x : s, Module.finrank ℂ (CohomologyModel F x.val) = r) :
        let G := Restrict (CohomologyModel F) s
        letI := isFiniteRank_restrict (E := CohomologyModel F) (s : Set X)
        let hG := (cohomologyModelMetric F hF).pullback
          (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))
        letI : ∀ x, NormedAddCommGroup (G x) := hG.fiberNormedAddCommGroup
        letI : ∀ x, InnerProductSpace ℂ (G x) := hG.fiberInnerProductSpace
        letI := nativeModelTopology G (EuclideanSpace ℂ (Fin r))
        letI := hG.nativeFiberBundle r hr
        letI := hG.nativeVectorBundle r hr
        singularCohomologyPullback ℤ
          (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)) (2 * k)
          (globalChernClass F hF k) =
            chernClass r G (hG.nativeModelMetric r) k := by
      subst s
      exact (existsUnique_globalChernClass F hF k).exists.choose_spec r
    have hrestriction := hretarget (rankStratum F r) hstr.symm
      (fun x ↦ (cohomologyModelLinearEquiv F x.val).finrank_eq.trans x.property)
    apply hrestriction.trans
    let G := Restrict (CohomologyModel F) (rankStratum F r)
    let H := Restrict F (rankStratum F r)
    let := isFiniteRank_restrict (E := CohomologyModel F) (rankStratum F r : Set X)
    let := isFiniteRank_restrict (E := F) (rankStratum F r : Set X)
    exact hcompare G H
      ((cohomologyModelMetric F hF).pullback
        (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum F r, X)))
      (rankHermitianMetric F hF r) r
      (fun x ↦ (cohomologyModelLinearEquiv F x.val).finrank_eq.trans x.property)
      (fun x ↦ x.property) ((cohomologyModelIso F).restrict (rankStratum F r))
  · -- The rational component uses the same original normalized character construction.
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
    let := cohomologyModelTopology F
    let := isFiniteRank_cohomologyModel F
    have hstr : rankStratum (CohomologyModel F) r = rankStratum F r := by
      ext x
      change Module.finrank ℂ (CohomologyModel F x) = r ↔ Module.finrank ℂ (F x) = r
      rw [(cohomologyModelLinearEquiv F x).finrank_eq]
    have hretarget (s : TopologicalSpace.Opens X)
        (hs : s = rankStratum (CohomologyModel F) r)
        (hr : ∀ x : s, Module.finrank ℂ (CohomologyModel F x.val) = r) :
        let G := Restrict (CohomologyModel F) s
        letI := isFiniteRank_restrict (E := CohomologyModel F) (s : Set X)
        let hG := (cohomologyModelMetric F hF).pullback
          (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))
        letI : ∀ x, NormedAddCommGroup (G x) := hG.fiberNormedAddCommGroup
        letI : ∀ x, InnerProductSpace ℂ (G x) := hG.fiberInnerProductSpace
        letI := nativeModelTopology G (EuclideanSpace ℂ (Fin r))
        letI := hG.nativeFiberBundle r hr
        letI := hG.nativeVectorBundle r hr
        singularCohomologyPullback ℚ
          (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)) (2 * k)
          (globalChernCharacterComponent F hF k) =
            chernCharacterComponent r G (hG.nativeModelMetric r) k := by
      subst s
      exact (existsUnique_globalChernCharacterComponent F hF k).exists.choose_spec r
    have hrestriction := hretarget (rankStratum F r) hstr.symm
      (fun x ↦ (cohomologyModelLinearEquiv F x.val).finrank_eq.trans x.property)
    apply hrestriction.trans
    let G := Restrict (CohomologyModel F) (rankStratum F r)
    let H := Restrict F (rankStratum F r)
    let := isFiniteRank_restrict (E := CohomologyModel F) (rankStratum F r : Set X)
    let := isFiniteRank_restrict (E := F) (rankStratum F r : Set X)
    exact hcompare G H
      ((cohomologyModelMetric F hF).pullback
        (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum F r, X)))
      (rankHermitianMetric F hF r) r
      (fun x ↦ (cohomologyModelLinearEquiv F x.val).finrank_eq.trans x.property)
      (fun x ↦ x.property) ((cohomologyModelIso F).restrict (rankStratum F r))

end OriginalRankComparison

end AtiyahSinger.ComplexBundle
