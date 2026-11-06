/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CommonFlagChern
public import AtiyahSinger.Topology.EvenCohomologyWhitney

/-!
# Isomorphisms, pullbacks and direct sums of original Chern classes

Public module ID: M1610.

The projective coefficient formula compares isomorphic original bundles on
one fixed flag. Their norms, native total topologies and supplied Hermitian
metrics remain separate. The actual projective pullback square gives naturality.
Its isomorphism comparison uses equality of the two original pullback topologies.

Whitney's formula uses the supplied direct-sum isomorphism and one common flag.
The same two root lists concatenate there; the finite symmetric-class formula
and the original degree transports give the asserted cup convolution.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianProjectiveTopology hermitianFlagTopology

section Iso

variable (F : X → Type u) [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) F]
  (hF : letI := modelTopology (EuclideanSpace ℂ (Fin r)) F
    ContinuousHermitianMetric F)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Isomorphic original bundles have the same Chern classes with their independent metrics. -/
theorem chernClass_eq_of_iso
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      let := modelTopology (EuclideanSpace ℂ (Fin r)) F
      Iso E F) (k : ℕ) :
    chernClass r E h k = chernClass r F hF k := by
  let Q := HermitianFlagBundle r F hF
  let f := hermitianFlagProjection r F hF
  let G := (f : Q → X) *ᵖ E
  let hnorm : ∀ x, NormedAddCommGroup (E x) := inferInstance
  let hspace : ∀ x, NormedSpace ℂ (E x) := inferInstance
  let : ∀ p, NormedAddCommGroup (G p) := fun p ↦ hnorm (f p)
  let : ∀ p, NormedSpace ℂ (G p) := fun p ↦ hspace (f p)
  let : FiberBundle (EuclideanSpace ℂ (Fin r)) G :=
    FiberBundle.pullback (F := EuclideanSpace ℂ (Fin r)) (E := E) f
  let : VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) G :=
    VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin r)) (E := E) f
  have hb := hermitianProjectivePowerCombination_int_bijective r E h r
    (fun i ↦ Nat.le_of_lt i.isLt)
  have hb' := hermitianProjectivePowerCombination_int_bijective r G
    (hermitianProjectivePullbackMetric r E h f) r (fun i ↦ Nat.le_of_lt i.isLt)
  -- The same F-flag coordinates, composed with e, determine the E-projective coefficients.
  rw [chernClass_eq_projectiveChernCoefficient r E h hb]
  apply hermitianFlagProjection_cohomology_injective ℤ r F hF (2 * k)
  rw [chernClass_flag_pullback]
  exact hermitianProjectiveChernCoefficient_flag_pullback_of_iso r E h F hF e hb hb' k

end Iso

section Pullback

variable {Y : Type u} [TopologicalSpace Y] (f : C(Y, X))

local instance : ∀ y, NormedAddCommGroup (((f : Y → X) *ᵖ E) y) :=
  fun y ↦ inferInstanceAs (NormedAddCommGroup (E (f y)))

local instance : ∀ y, NormedSpace ℂ (((f : Y → X) *ᵖ E) y) :=
  fun y ↦ inferInstanceAs (NormedSpace ℂ (E (f y)))

local instance : FiberBundle (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E) :=
  FiberBundle.pullback (F := EuclideanSpace ℂ (Fin r)) (E := E) f

local instance : VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E) :=
  VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin r)) (E := E) f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original Chern classes are natural for the native pullback bundle and metric. -/
theorem chernClass_pullback (k : ℕ) :
    singularCohomologyPullback ℤ f (2 * k) (chernClass r E h k) =
      chernClass r ((f : Y → X) *ᵖ E) (hermitianProjectivePullbackMetric r E h f) k := by
  let F := (f : Y → X) *ᵖ E
  let hF := hermitianProjectivePullbackMetric r E h f
  let p := hermitianProjectiveProjection r E h
  let q := hermitianProjectiveProjection r F hF
  let g := hermitianProjectivePullback r E h f
  let t := hermitianProjectiveChernRoot r E h
  let t' := hermitianProjectiveChernRoot r F hF
  have hb := hermitianProjectivePowerCombination_int_bijective r E h r
    (fun i ↦ Nat.le_of_lt i.isLt)
  have hb' := hermitianProjectivePowerCombination_int_bijective r F hF r
    (fun i ↦ Nat.le_of_lt i.isLt)
  have ht : singularCohomologyPullback ℤ g 2 t = t' :=
    hermitianProjectiveChernRoot_pullback r E h f
  have hb'' : Function.Bijective (singularCohomologyPowerCombination ℤ q
      (singularCohomologyPullback ℤ g 2 t) r r (fun i ↦ Nat.le_of_lt i.isLt)) := by
    rw [ht]
    exact hb'
  -- Pull back the same leading-power expansion around the actual projective square.
  rw [chernClass_eq_projectiveChernCoefficient r E h hb,
    chernClass_eq_projectiveChernCoefficient r F hF hb']
  have hn := projectiveChernCoefficient_pullback p q f g
    (hermitianProjectiveProjection_comp_pullback r E h f) r t hb hb'' k
  -- Equality of actual root classes also identifies the dependent bijectivity certificates.
  have hcoeff (s₁ s₂ : singularCohomology ℤ (HermitianProjectiveBundle r F hF) 2)
      (hb₁ : Function.Bijective
        (singularCohomologyPowerCombination ℤ q s₁ r r (fun i ↦ Nat.le_of_lt i.isLt)))
      (hb₂ : Function.Bijective
        (singularCohomologyPowerCombination ℤ q s₂ r r (fun i ↦ Nat.le_of_lt i.isLt)))
      (hs : s₁ = s₂) :
      projectiveChernCoefficient q r s₁ hb₁ k = projectiveChernCoefficient q r s₂ hb₂ k := by
    subst s₂
    rfl
  exact hn.trans (hcoeff _ _ hb'' hb' ht)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An isomorphism from the actual native pullback identifies the original Chern classes. -/
theorem chernClass_pullback_eq_of_iso
    (F : Y → Type u) [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) F)]
    [FiberBundle (EuclideanSpace ℂ (Fin r)) F]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) F]
    (hF : letI := modelTopology (EuclideanSpace ℂ (Fin r)) F
      ContinuousHermitianMetric F)
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      let := modelTopology (EuclideanSpace ℂ (Fin r)) F
      Iso ((f : Y → X) *ᵖ E) F) (k : ℕ) :
    singularCohomologyPullback ℤ f (2 * k) (chernClass r E h k) = chernClass r F hF k := by
  rw [chernClass_pullback]
  apply chernClass_eq_of_iso
  -- Unit retyping before or after native pullback gives the identical total topology.
  dsimp only
  rw [modelTopology_pullback]
  exact e

end Pullback

variable (s : ℕ)
  (F : X → Type u) [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  (hF : letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
    ContinuousHermitianMetric F)
  (t : ℕ)
  (G : X → Type u) [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin t)) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin t)) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin t)) G]
  (hG : letI := modelTopology (EuclideanSpace ℂ (Fin t)) G
    ContinuousHermitianMetric G)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Whitney's formula for a genuine original direct sum and independent Hermitian metrics. -/
theorem chernClass_sum
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin t)) G
      letI := sumTopology (E := E) (F := F)
      Iso G (E ×ᵇ F)) (k : ℕ) :
    chernClass t G hG k =
      ∑ i : Fin (k + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
          singularCohomology ℤ X (2 * (i.val + (k - i.val))) ≅
            singularCohomology ℤ X (2 * k)).hom
          (singularCohomologyEvenCup ℤ X i.val (k - i.val)
            (chernClass r E h i.val) (chernClass s F hF (k - i.val))) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin s)) F
  let := modelTopology (EuclideanSpace ℂ (Fin t)) G
  let := sumTopology (E := E) (F := F)
  by_cases hX : Nonempty X
  · obtain ⟨z⟩ := hX
    -- The specified fiber isomorphism supplies rank addition when the base is nonempty.
    let vE := EuclideanSpace ℂ (Fin r)
    let vF := EuclideanSpace ℂ (Fin s)
    let vG := EuclideanSpace ℂ (Fin t)
    let lE := (trivializationAt vE E z).linearEquivAt ℂ z
      (mem_baseSet_trivializationAt vE E z)
    let lF := (trivializationAt vF F z).linearEquivAt ℂ z
      (mem_baseSet_trivializationAt vF F z)
    let lG := (trivializationAt vG G z).linearEquivAt ℂ z
      (mem_baseSet_trivializationAt vG G z)
    have hGrank : Module.finrank ℂ (G z) = t := by simpa [vG] using lG.finrank_eq
    have hsumrank : Module.finrank ℂ (E z × F z) = r + s := by
      simpa [vE, vF] using (lE.prodCongr lF).finrank_eq
    have htr : t = r + s := hGrank.symm.trans ((e.linearEquiv z).finrank_eq.trans hsumrank)
    cases htr
    obtain ⟨Y, f, x, y, hinj, _, hE', hF', hG'⟩ :=
      exists_commonFlag_chernClass_sum r E h s F hF G hG e
    apply hinj (2 * k)
    -- Both summands and their direct sum use the very same actual roots on the common flag.
    rw [hG', singularCohomologyElementarySymmetric_append, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have htransport (a b : ℕ) (hab : a = b) (c : singularCohomology ℤ X (2 * a)) :
        singularCohomologyPullback ℤ f (2 * b)
            ((eqToIso (congrArg (fun j ↦ singularCohomology ℤ X (2 * j)) hab)).hom c) =
          (eqToIso (congrArg (fun j ↦ singularCohomology ℤ Y (2 * j)) hab)).hom
            (singularCohomologyPullback ℤ f (2 * a) c) := by
      subst b
      rfl
    rw [htransport _ _ (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)),
      singularCohomologyPullback_evenCup, hE', hF']
  · -- Empty bases need no relation between their vacuous rank parameters.
    let : IsEmpty X := not_nonempty_iff.mp hX
    exact (subsingleton_singularCohomology_of_isEmpty ℤ X (2 * k)).elim _ _

end AtiyahSinger.ComplexBundle
