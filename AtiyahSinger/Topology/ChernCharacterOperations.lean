/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExponentialPowerSum
public import AtiyahSinger.Topology.BundleTensor
public import AtiyahSinger.Topology.ChernCharacter
public import AtiyahSinger.Topology.ChernClassOperations
public import AtiyahSinger.Topology.CommonFlagTensorChern
public import AtiyahSinger.Topology.EvenCohomologyWeightedEvaluation
public import AtiyahSinger.Topology.FiniteCupVanishing

/-!
# Naturality, direct sums and tensor products of the actual Chern character

Public module ID: M1608.

C02: SG III.11, (11.22)--(11.23) and Proposition 11.16. Note 11.5
and the proof of Proposition 11.16 supply the line-tensor first-Chern formula.
The book's manifold formulation extends degreewise to arbitrary bases via
the actual double-projective line comparison and common flag spaces. These are
identities for the actual rational classes constructed from normalized
integral Chern roots. The comparison data are genuine original bundle
isomorphisms, with continuity on total spaces, rather than an equality of
assigned characteristic classes. Each metric is auxiliary and independent.

The source, target and product bundles keep their original Euclidean models.
Only the phantom total-space model is retyped to Unit to express the same
continuous bundle isomorphisms. Direct sums use the existing sumTopology;
tensor products use the existing tensorTopology on the actual algebraic
complex tensor fibers. The target rank need not be stipulated as a formula:
the supplied fiberwise isomorphism forces the appropriate rank at each point.

The tensor identity is the finite convolution in degree 2*k. It does not
form an infinite sum in direct-sum cohomology, require a finite-dimensional
base, or assert descent to K-theory. Isomorphism invariance follows from the
normalized Newton construction. Original Chern-class naturality proves pullbacks;
the same common flag spaces prove direct sums.
The tensor identity follows from the normalized line formula and finite exponential convolution.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory
open scoped TensorProduct

universe u

variable (r s : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (hE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)
  (F : X → Type u) [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  (hF : letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
    ContinuousHermitianMetric F)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An actual original complex bundle isomorphism preserves every Chern-character component. -/
theorem chernCharacterComponent_eq_of_iso
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
      Iso E F) (k : ℕ) :
    chernCharacterComponent r E hE k = chernCharacterComponent s F hF k := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin s)) F
  by_cases hX : Nonempty X
  · obtain ⟨x⟩ := hX
    -- One fiber identifies the two constant ranks; the original norms need not agree.
    let vE := EuclideanSpace ℂ (Fin r)
    let vF := EuclideanSpace ℂ (Fin s)
    let lE := (trivializationAt vE E x).linearEquivAt ℂ x
      (mem_baseSet_trivializationAt vE E x)
    let lF := (trivializationAt vF F x).linearEquivAt ℂ x
      (mem_baseSet_trivializationAt vF F x)
    have hErank : Module.finrank ℂ (E x) = r := by simpa [vE] using lE.finrank_eq
    have hFrank : Module.finrank ℂ (F x) = s := by simpa [vF] using lF.finrank_eq
    have hrs : r = s := hErank.symm.trans ((e.linearEquiv x).finrank_eq.trans hFrank)
    cases hrs
    -- The same normalized Newton polynomial uses the isomorphic bundles' same Chern classes.
    rw [chernCharacterComponent_eq_newton, chernCharacterComponent_eq_newton]
    simp_rw [chernClass_eq_of_iso r E hE F hF e]
  · -- The empty base has zero cohomology even if its two vacuous rank parameters differ.
    let : IsEmpty X := not_nonempty_iff.mp hX
    exact (subsingleton_singularCohomology_of_isEmpty ℚ X (2 * k)).elim _ _

variable (t : ℕ)
  (G : X → Type u) [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin t)) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin t)) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin t)) G]
  (hG : letI := modelTopology (EuclideanSpace ℂ (Fin t)) G
    ContinuousHermitianMetric G)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- SG Proposition 11.16: genuine direct-sum identification gives degreewise additivity. -/
theorem chernCharacterComponent_sum
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin t)) G
      letI := sumTopology (E := E) (F := F)
      Iso G (E ×ᵇ F)) (k : ℕ) :
    chernCharacterComponent t G hG k =
      chernCharacterComponent r E hE k + chernCharacterComponent s F hF k := by
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
    obtain ⟨Y, f, x, y, _, hinj, hE', hF', hG'⟩ :=
      exists_commonFlag_chernClass_sum r E hE s F hF G hG e
    apply hinj (2 * k)
    -- Naturality of Newton evaluation turns the same integral roots into rational power sums.
    have hcE : singularCohomologyPullback ℚ f (2 * k) (chernCharacterComponent r E hE k) =
        (Nat.factorial k : ℚ)⁻¹ • ∑ i : Fin r,
          singularCohomologyDegreeTwoPow ℚ Y (singularCohomologyRationalization Y 2 (x i)) k := by
      rw [chernCharacterComponent_eq_newton, map_smul,
        singularCohomologyNewtonPowerSum_pullback]
      simp_rw [← singularCohomologyRationalization_naturality, hE',
        singularCohomologyRationalization_elementarySymmetric, List.map_ofFn]
      rw [singularCohomologyNewtonPowerSum_elementarySymmetric]
      rfl
    have hcF : singularCohomologyPullback ℚ f (2 * k) (chernCharacterComponent s F hF k) =
        (Nat.factorial k : ℚ)⁻¹ • ∑ i : Fin s,
          singularCohomologyDegreeTwoPow ℚ Y (singularCohomologyRationalization Y 2 (y i)) k := by
      rw [chernCharacterComponent_eq_newton, map_smul,
        singularCohomologyNewtonPowerSum_pullback]
      simp_rw [← singularCohomologyRationalization_naturality, hF',
        singularCohomologyRationalization_elementarySymmetric, List.map_ofFn]
      rw [singularCohomologyNewtonPowerSum_elementarySymmetric]
      rfl
    have hcG : singularCohomologyPullback ℚ f (2 * k)
        (chernCharacterComponent (r + s) G hG k) =
        (Nat.factorial k : ℚ)⁻¹ • ∑ i : Fin (r + s),
          singularCohomologyDegreeTwoPow ℚ Y
            (singularCohomologyRationalization Y 2 (Fin.append x y i)) k := by
      rw [chernCharacterComponent_eq_newton, map_smul,
        singularCohomologyNewtonPowerSum_pullback]
      simp_rw [← singularCohomologyRationalization_naturality, hG',
        ← List.ofFn_fin_append, singularCohomologyRationalization_elementarySymmetric,
        List.map_ofFn]
      rw [singularCohomologyNewtonPowerSum_elementarySymmetric]
      rfl
    rw [map_add, hcE, hcF, hcG]
    -- Splitting a finite power sum needs no positivity assumption on k, so rank is included.
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, smul_add]
  · let : IsEmpty X := not_nonempty_iff.mp hX
    exact (subsingleton_singularCohomology_of_isEmpty ℚ X (2 * k)).elim _ _

set_option maxHeartbeats 1000000 in
-- Descend the finite cup convolution through the actual tensor bundle identification.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- SG Proposition 11.16: genuine tensor identification gives the finite cup convolution. -/
theorem chernCharacterComponent_tensor
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin t)) G
      letI := tensorTopology (E := E) (F := F)
      Iso G (fun x ↦ E x ⊗[ℂ] F x)) (k : ℕ) :
    chernCharacterComponent t G hG k =
      ∑ i : Fin (k + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
            singularCohomology ℚ X (2 * (i.val + (k - i.val))) ≅
              singularCohomology ℚ X (2 * k)).hom
          (singularCohomologyEvenCup ℚ X i.val (k - i.val)
            (chernCharacterComponent r E hE i.val)
            (chernCharacterComponent s F hF (k - i.val))) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin s)) F
  let := modelTopology (EuclideanSpace ℂ (Fin t)) G
  let := tensorTopology (E := E) (F := F)
  by_cases hX : Nonempty X
  · obtain ⟨z⟩ := hX
    -- The original specified fiber Iso forces the tensor rank on a nonempty base.
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
    have htensorRank : Module.finrank ℂ (E z ⊗[ℂ] F z) = r * s := by
      simpa [vE, vF, Module.finrank_tensorProduct] using
        (TensorProduct.congr lE lF).finrank_eq
    have htr : t = r * s :=
      hGrank.symm.trans ((e.linearEquiv z).finrank_eq.trans htensorRank)
    cases htr
    obtain ⟨Y, f, x, y, _, hinj, hE', hF', hG'⟩ :=
      exists_commonFlag_chernClass_tensor r E hE s F hF G hG e
    -- The same two line families give all rational Newton power sums on this one flag space.
    let xr (i : Fin r) : singularCohomology ℚ Y 2 := singularCohomologyRationalization Y 2 (x i)
    let yr (i : Fin s) : singularCohomology ℚ Y 2 := singularCohomologyRationalization Y 2 (y i)
    have hcE (n : ℕ) : singularCohomologyPullback ℚ f (2 * n)
        (chernCharacterComponent r E hE n) =
        (Nat.factorial n : ℚ)⁻¹ • ∑ i : Fin r,
          singularCohomologyDegreeTwoPow ℚ Y (xr i) n := by
      rw [chernCharacterComponent_eq_newton, map_smul,
        singularCohomologyNewtonPowerSum_pullback]
      simp_rw [← singularCohomologyRationalization_naturality, hE',
        singularCohomologyRationalization_elementarySymmetric, List.map_ofFn]
      rw [singularCohomologyNewtonPowerSum_elementarySymmetric]
      rfl
    have hcF (n : ℕ) : singularCohomologyPullback ℚ f (2 * n)
        (chernCharacterComponent s F hF n) =
        (Nat.factorial n : ℚ)⁻¹ • ∑ i : Fin s,
          singularCohomologyDegreeTwoPow ℚ Y (yr i) n := by
      rw [chernCharacterComponent_eq_newton, map_smul,
        singularCohomologyNewtonPowerSum_pullback]
      simp_rw [← singularCohomologyRationalization_naturality, hF',
        singularCohomologyRationalization_elementarySymmetric, List.map_ofFn]
      rw [singularCohomologyNewtonPowerSum_elementarySymmetric]
      rfl
    have hcG : singularCohomologyPullback ℚ f (2 * k)
        (chernCharacterComponent (r * s) G hG k) =
        (Nat.factorial k : ℚ)⁻¹ • ∑ i : Fin (r * s),
          singularCohomologyDegreeTwoPow ℚ Y
            (xr (finProdFinEquiv.symm i).1 + yr (finProdFinEquiv.symm i).2) k := by
      rw [chernCharacterComponent_eq_newton, map_smul,
        singularCohomologyNewtonPowerSum_pullback]
      simp_rw [← singularCohomologyRationalization_naturality, hG',
        singularCohomologyRationalization_elementarySymmetric, List.map_ofFn]
      rw [singularCohomologyNewtonPowerSum_elementarySymmetric]
      apply congrArg ((Nat.factorial k : ℚ)⁻¹ • ·)
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg (fun a : singularCohomology ℚ Y 2 ↦
        singularCohomologyDegreeTwoPow ℚ Y a k)
      exact map_add (singularCohomologyRationalization Y 2).hom
        (x (finProdFinEquiv.symm i).1) (y (finProdFinEquiv.symm i).2)
    have htransport (a b : ℕ) (hab : a = b) (c : singularCohomology ℚ X (2 * a)) :
        singularCohomologyPullback ℚ f (2 * b)
            ((eqToIso (congrArg (fun j ↦ singularCohomology ℚ X (2 * j)) hab)).hom c) =
          (eqToIso (congrArg (fun j ↦ singularCohomology ℚ Y (2 * j)) hab)).hom
            (singularCohomologyPullback ℚ f (2 * a) c) := by
      subst b
      rfl
    apply hinj (2 * k)
    rw [hcG, map_sum]
    conv_rhs =>
      arg 2
      ext i
      rw [htransport _ _ (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)),
        singularCohomologyPullback_evenCup, hcE, hcF]
    -- Include homogeneous classes in the even cup algebra, preserving every degree transport.
    apply singularEvenCohomologyOf_injective ℚ Y k
    rw [map_smul, map_sum, map_sum]
    conv_rhs =>
      arg 2
      ext i
      rw [singularEvenCohomologyOf_eqToIso ℚ Y
        (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)), singularEvenCohomologyOf_cup]
    simp only [map_smul, map_sum, singularEvenCohomologyOf_degreeTwoPow, map_add]
    let x' (i : Fin r) :=
      singularEvenCohomologyOf ℚ Y 1 (xr i)
    let y' (i : Fin s) :=
      singularEvenCohomologyOf ℚ Y 1 (yr i)
    have hsum : (∑ i : Fin (r * s),
        (x' (finProdFinEquiv.symm i).1 + y' (finProdFinEquiv.symm i).2) ^ k) =
        ∑ a : Fin r, ∑ b : Fin s, (x' a + y' b) ^ k := by
      calc
        _ = ∑ ij : Fin r × Fin s, (x' ij.1 + y' ij.2) ^ k :=
          Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ ↦ rfl)
        _ = _ := Fintype.sum_prod_type _
    rw [hsum]
    exact sum_add_pow_inv_factorial x' y' k
  · -- Empty bases impose no equality between their vacuous model ranks.
    let : IsEmpty X := not_nonempty_iff.mp hX
    exact (subsingleton_singularCohomology_of_isEmpty ℚ X (2 * k)).elim _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A specified original model of a pullback has the pullback Chern-character component. -/
theorem chernCharacterComponent_pullback
    {Y : Type u} [TopologicalSpace Y] (f : C(Y, X)) (q : ℕ)
    (V : Y → Type u) [∀ y, NormedAddCommGroup (V y)] [∀ y, NormedSpace ℂ (V y)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) V)]
    [FiberBundle (EuclideanSpace ℂ (Fin q)) V]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) V]
    (hV : letI := modelTopology (EuclideanSpace ℂ (Fin q)) V
      ContinuousHermitianMetric V)
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) V
      Iso V ((f : Y → X) *ᵖ E)) (k : ℕ) :
    chernCharacterComponent q V hV k =
      singularCohomologyPullback ℚ f (2 * k) (chernCharacterComponent r E hE k) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) V
  by_cases hY : Nonempty Y
  · obtain ⟨y⟩ := hY
    -- A fiber of the actual pullback identifies the original constant rank parameters.
    let vE := EuclideanSpace ℂ (Fin r)
    let vV := EuclideanSpace ℂ (Fin q)
    let lE := (trivializationAt vE E (f y)).linearEquivAt ℂ (f y)
      (mem_baseSet_trivializationAt vE E (f y))
    let lV := (trivializationAt vV V y).linearEquivAt ℂ y
      (mem_baseSet_trivializationAt vV V y)
    have hErank : Module.finrank ℂ (E (f y)) = r := by simpa [vE] using lE.finrank_eq
    have hVrank : Module.finrank ℂ (V y) = q := by simpa [vV] using lV.finrank_eq
    have hqr : q = r := hVrank.symm.trans ((e.linearEquiv y).finrank_eq.trans hErank)
    cases hqr
    -- Integral naturality uses the same supplied isomorphism and independent metrics.
    have hc (j : ℕ) := chernClass_pullback_eq_of_iso r E hE f V hV e.symm j
    rw [chernCharacterComponent_eq_newton, chernCharacterComponent_eq_newton,
      map_smul, singularCohomologyNewtonPowerSum_pullback]
    simp_rw [← singularCohomologyRationalization_naturality, hc]
  · -- No rank equality is needed on an empty base: all its cohomology groups vanish.
    let : IsEmpty Y := not_nonempty_iff.mp hY
    exact (subsingleton_singularCohomology_of_isEmpty ℚ Y (2 * k)).elim _ _

end AtiyahSinger.ComplexBundle
