/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTrivial
public import AtiyahSinger.Topology.ChernCharacterNormalization
public import AtiyahSinger.Topology.HalfSpinorCharacter
public import AtiyahSinger.Topology.SpinorBundleZero

/-!
# The character of the original half-spin bundles in rank zero

Public module ID: M2273.

SR05. The positive half-spin bundle of the original native Spin(0) principal
bundle is globally trivialized by the actual exterior vacuum. The negative
half-spin bundle is the zero bundle. Their degreewise character difference
is therefore the canonical unit family: one in degree zero and zero above it.
All associated fibers, representations and quotient topologies are unchanged.

Sources: Lawson--Michelsohn, Spin Geometry, I.5, the exterior spinor model and
its parity decomposition; II.3, the associated spinor bundle construction;
III.11, Construction 11.23 and Proposition 11.24. This is the empty-product
endpoint of these constructions, rather than a new numbered source theorem.
The native group convention is the original unit-generated subgroup: SpinZero
establishes its triviality in dimension zero. A stable two-sheeted convention
would require a separate comparison and is not substituted here.

Fiber rank one does not establish triviality of a line bundle. The specified
vacuum and the identity action of this native Spin(0) fix the positive global
isomorphism; its formula is required at every original principal representative.
The negative bundle comparison follows from its actual empty parity basis.
No positive-rank TopologicalSpinStructure, global section of the principal
bundle, nonempty base, separation axiom or compactness assumption is supplied.
The metrics in the character formula are arbitrary supplied metrics on the
same original half-spin bundles. The two actual quotient-bundle trivializations are
proved below and determine the cohomological character in every degree.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  ComplexBundle.trivialTopology

universe u v

variable {B : Type u} {P : Type v} [TopologicalSpace B] [TopologicalSpace P]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → B}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)

/-- The original positive rank-zero half-spin bundle has its unique vacuum trivialization. -/
theorem existsUnique_halfSpinorBundle_zero_positive_trivial_iso :
    ∃! e : ComplexBundle.Iso (HalfSpinorBundle 0 hP 0)
        (Bundle.Trivial B (Fin 1 → ℂ)),
      ∀ (p : P) (b : B) (hp : projection p = b) (z : ℂ),
        e.linearEquiv b
            (associatedVectorFiberMk hP (complexSpinParityContRepresentation 0 0) p hp
              (z • complexSpinorParityBasis 0 0 ⟨∅, by simp⟩)) =
          fun _ : Fin 1 ↦ z := by
  /- Stage 1: the original exterior parity basis at m=0 has exactly the
  empty subset in positive parity. Thus every vector has a unique scalar
  coefficient against the displayed vacuum, and this coefficient map is
  a complex-linear equivalence to the specified one-coordinate space.
  Stage 2: spinGroup_zero_subsingleton makes every original group element
  equal to one. Its given parity representation therefore acts identically.
  The associated relation [p*g,v]=[p,rho(g)v] preserves the vacuum coordinate.
  Consequently the coefficient map descends from the original quotient and
  is independent of the original principal point used to represent a fiber.
  Stage 3: descend the continuous coefficient map through the original
  total-space quotient to the specified trivialTopology. Finite local rank
  supplies inverse continuity for the resulting fiberwise equivalence.
  No continuity of an arbitrary chosen principal representative is needed.
  Stage 4: each principal fiber is nonempty by hP over each supplied b.
  Every associated vector is represented by a scalar multiple of the vacuum
  at such a point, so the formula determines every fiber equivalence. Bundle
  extensionality gives uniqueness, also when B is empty. The actual trivial
  action is essential: the fiber dimension one alone proves none of this. -/
  classical
  let G := spinGroup (realSpinorQuadraticForm 0)
  let V := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin 0))) 0
  let ρ := complexSpinParityContRepresentation 0 0
  let I := {s : Finset (Fin 0) // (s.card : ZMod 2) = 0}
  let : Unique I :=
    { default := ⟨∅, by simp⟩
      uniq := fun s ↦ Subtype.ext (Subsingleton.elim _ _) }
  -- The sole original even basis vector fixes the scalar coordinate, including its normalization.
  let d : V ≃ₗ[ℂ] (Fin 1 → ℂ) := (complexSpinorParityBasis 0 0).equivFun.trans
    (LinearEquiv.piCongrLeft ℂ (fun _ : Fin 1 ↦ ℂ) (Equiv.ofUnique I (Fin 1)))
  have hvac (z : ℂ) : d (z • complexSpinorParityBasis 0 0 ⟨∅, by simp⟩) =
      (fun _ : Fin 1 ↦ z) := by
    have hdefault : (default : I) = ⟨∅, by simp⟩ := Subsingleton.elim _ _
    ext i
    simp [d, LinearEquiv.piCongrLeft, Equiv.ofUnique, hdefault]
  let := isFiniteRank_associatedVector hP ρ (continuous_complexSpinParityRepresentation 0 0)
  let := ComplexBundle.isFiniteRank_trivial (X := B) 1
  -- Principal transitivity and the native trivial group identify all representatives over b.
  let p (b : B) : P := (hP.projection_properties.2.2 b).choose
  have hp (b : B) : projection (p b) = b := (hP.projection_properties.2.2 b).choose_spec
  let a (b : B) := (associatedVectorFiberMkLinearEquiv hP ρ (p b) (hp b)).symm.trans d
  have hrep (b : B) (q : P) (hq : projection q = b) (v : V) :
      a b (associatedVectorFiberMk hP ρ q hq v) = d v := by
    obtain ⟨g, hg, _⟩ := hP.existsUnique_smul (p b) q ((hp b).trans hq.symm)
    have hg1 : g = 1 := Subsingleton.elim _ _
    have hq' : p b = q := by simpa only [hg1, MulOpposite.op_one, one_smul] using hg
    clear hg
    subst q
    exact congrArg d ((associatedVectorFiberMkLinearEquiv hP ρ (p b) (hp b)).symm_apply_apply v)
  -- Descend continuity through the original quotient to the specified trivial-bundle topology.
  let A : ComplexBundle.Hom (HalfSpinorBundle 0 hP 0) (Bundle.Trivial B (Fin 1 → ℂ)) :=
    { linearMap := fun b ↦ (a b).toLinearMap
      continuous_total := by
        let := associatedRepresentationAction ρ
        let H := associatedVectorTotalHomeomorph hP ρ
        have hquot : Continuous (fun z : AssociatedBundle G P V ↦
            (⟨(H.symm z).proj, a (H.symm z).proj (H.symm z).snd⟩ :
              TotalSpace Unit (Bundle.Trivial B (Fin 1 → ℂ)))) := by
          apply isQuotientMap_quotient_mk'.continuous_iff.mpr
          have hc : Continuous (fun z : P × V ↦
              (⟨projection z.1, d z.2⟩ : TotalSpace Unit (Bundle.Trivial B (Fin 1 → ℂ)))) := by
            apply continuous_induced_rng.mpr
            exact (hP.projection_properties.1.comp continuous_fst).prodMk
              (d.continuous_of_finiteDimensional.comp continuous_snd)
          apply hc.congr
          intro z
          change (⟨projection z.1, d z.2⟩ : TotalSpace Unit (Bundle.Trivial B (Fin 1 → ℂ))) =
            ⟨projection z.1, a (projection z.1) (associatedVectorFiberMk hP ρ z.1 rfl z.2)⟩
          rw [hrep]
        have hc := hquot.comp H.continuous
        have hfun : ((fun z ↦
            (⟨(H.symm z).proj, a (H.symm z).proj (H.symm z).snd⟩ :
              TotalSpace Unit (Bundle.Trivial B (Fin 1 → ℂ)))) ∘ H) =
            (fun z ↦ (⟨z.proj, a z.proj z.snd⟩ :
              TotalSpace Unit (Bundle.Trivial B (Fin 1 → ℂ)))) := by
          funext z
          exact congrArg (fun w : TotalSpace Unit (HalfSpinorBundle 0 hP 0) ↦
            (⟨w.proj, a w.proj w.snd⟩ : TotalSpace Unit (Bundle.Trivial B (Fin 1 → ℂ))))
            (H.symm_apply_apply z)
        rw [hfun] at hc
        exact hc }
  -- Local finite rank gives inverse continuity; the vacuum formula determines the isomorphism.
  let e := A.toIso (fun b ↦ (a b).bijective)
  have he (q : P) (b : B) (hq : projection q = b) (z : ℂ) :
      e.linearEquiv b (associatedVectorFiberMk hP ρ q hq
        (z • complexSpinorParityBasis 0 0 ⟨∅, by simp⟩)) = (fun _ : Fin 1 ↦ z) :=
    (hrep b q hq _).trans (hvac z)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply ComplexBundle.Iso.ext
  intro b
  apply LinearEquiv.ext
  intro v
  obtain ⟨s, rfl⟩ := (associatedVectorFiberMk_bijective hP ρ (p b) (hp b)).2 v
  have hs : s = (d s 0) • complexSpinorParityBasis 0 0 ⟨∅, by simp⟩ := by
    apply d.injective
    rw [hvac]
    ext i
    exact congrArg (d s) (Subsingleton.elim _ _)
  rw [hs, he', he]

/-- The original negative rank-zero half-spin bundle is isomorphic to the actual zero bundle. -/
theorem exists_halfSpinorBundle_zero_negative_trivial_iso :
    Nonempty (ComplexBundle.Iso (HalfSpinorBundle 0 hP 1)
      (Bundle.Trivial B (Fin 0 → ℂ))) := by
  /- Stage 1: the only finite subset of Fin 0 is empty, whose cardinality
  has parity zero. The original negative parity basis therefore has no
  vectors. Its space is zero, and associatedVectorFiberMkLinearEquiv
  transfers that assertion to every original negative quotient fiber.
  Stage 2: the unique linear equivalence with the empty-coordinate fiber
  defines the bundle map. Its total map is base projection paired with
  zero, so it is continuous in the trivial-bundle topology. Finite local
  rank then supplies inverse continuity. Principal fiber coordinates used
  to identify the dimensions are supplied by hP. -/
  classical
  let ρ := complexSpinParityContRepresentation 0 1
  let := isFiniteRank_associatedVector hP ρ (continuous_complexSpinParityRepresentation 0 1)
  let := ComplexBundle.isFiniteRank_trivial (X := B) 0
  -- Transfer the empty parity basis to the actual associated fibers.
  let : ∀ b, FiniteDimensional ℂ (HalfSpinorBundle 0 hP 1 b) := fun b ↦
    FiniteDimensional.of_injective (associatedVectorFiberLinearEquiv hP ρ b).toLinearMap
      (associatedVectorFiberLinearEquiv hP ρ b).injective
  let : ∀ b, Subsingleton (HalfSpinorBundle 0 hP 1 b) := fun b ↦
    Module.finrank_zero_iff.mp (by simpa using finrank_halfSpinorBundle_zero hP 1 b)
  let a (b : B) : HalfSpinorBundle 0 hP 1 b ≃ₗ[ℂ] (Fin 0 → ℂ) :=
    LinearEquiv.ofSubsingleton _ _
  -- The unique fiber map has continuous total map: base projection paired with zero.
  let A : ComplexBundle.Hom (HalfSpinorBundle 0 hP 1) (Bundle.Trivial B (Fin 0 → ℂ)) :=
    { linearMap := fun b ↦ (a b).toLinearMap
      continuous_total := by
        apply continuous_induced_rng.mpr
        have hc := (ComplexBundle.continuous_proj (E := HalfSpinorBundle 0 hP 1)).prodMk
          (continuous_const (y := (0 : Fin 0 → ℂ)))
        apply hc.congr
        intro z
        exact Prod.ext rfl (Subsingleton.elim _ _) }
  exact ⟨A.toIso (fun b ↦ (a b).bijective)⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In rank zero the original positive-minus-negative character is the degreewise unit. -/
theorem halfSpinorCharacterComponent_zero
    (hPlus : ComplexBundle.ContinuousHermitianMetric (HalfSpinorBundle 0 hP 0))
    (hMinus : ComplexBundle.ContinuousHermitianMetric (HalfSpinorBundle 0 hP 1))
    (k : ℕ) :
    halfSpinorCharacterComponent 0 hP hPlus hMinus k =
      singularCohomologyDegreeTwoPow ℚ B (0 : singularCohomology ℚ B 2) k := by
  classical
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 0)
    (continuous_complexSpinParityRepresentation 0 0)
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 1)
    (continuous_complexSpinParityRepresentation 0 1)
  let T := PUnit.{u + 1}
  let F (n : ℕ) := Bundle.Trivial T (Fin n → ℂ)
  let : ∀ n, ComplexBundle.IsFiniteRank (F n) :=
    fun n ↦ ComplexBundle.isFiniteRank_trivial n
  let hF (n : ℕ) := (ComplexBundle.nonempty_continuousHermitianMetric (F n)).some
  let f : C(B, T) := ContinuousMap.const _ PUnit.unit
  -- These are the actual vacuum and empty-parity identifications, not rank-only comparisons.
  obtain ⟨ePlus, _, _⟩ := existsUnique_halfSpinorBundle_zero_positive_trivial_iso hP
  obtain ⟨eMinus⟩ := exists_halfSpinorBundle_zero_negative_trivial_iso hP
  have hPlus' := ComplexBundle.globalChernCharacterComponent_pullback (F 1) (hF 1) f
    (HalfSpinorBundle 0 hP 0) hPlus
    (ePlus.trans (ComplexBundle.pullbackTrivialIso f 1).symm) k
  have hMinus' := ComplexBundle.globalChernCharacterComponent_pullback (F 0) (hF 0) f
    (HalfSpinorBundle 0 hP 1) hMinus
    (eMinus.trans (ComplexBundle.pullbackTrivialIso f 0).symm) k
  change ComplexBundle.globalChernCharacterComponent (HalfSpinorBundle 0 hP 0) hPlus k -
    ComplexBundle.globalChernCharacterComponent (HalfSpinorBundle 0 hP 1) hMinus k = _
  rw [hPlus', hMinus']
  cases k with
  | zero =>
    -- The two actual point fibers have dimensions one and zero, respectively.
    have h1 := ComplexBundle.globalChernCharacterComponent_zero_of_finrank
      (F 1) (hF 1) 1 (fun _ ↦ by simp [F, Bundle.Trivial])
    have h0 := ComplexBundle.globalChernCharacterComponent_zero_of_finrank
      (F 0) (hF 0) 0 (fun _ ↦ by simp [F, Bundle.Trivial])
    rw [h1, h0]
    simp only [Nat.cast_one, one_smul, Nat.cast_zero, zero_smul, map_zero, sub_zero,
      singularCohomologyDegreeTwoPow]
    exact singularCohomologyPullback_one ℚ f
  | succ k =>
    -- Positive cohomology of the point vanishes; naturality retains the original base and metrics.
    let := subsingleton_singularHomology_of_subsingleton ℚ T (2 * (k + 1)) (by omega)
    let : Subsingleton (singularCohomology ℚ T (2 * (k + 1))) :=
      subsingleton_singularCochainDualHomology_of_subsingleton ℚ
        (singularChains ℚ T) (2 * (k + 1))
    have h1 : ComplexBundle.globalChernCharacterComponent (F 1) (hF 1) (k + 1) = 0 :=
      Subsingleton.elim _ _
    have h0 : ComplexBundle.globalChernCharacterComponent (F 0) (hF 0) (k + 1) = 0 :=
      Subsingleton.elim _ _
    rw [h1, h0, map_zero, sub_self]
    simp only [singularCohomologyDegreeTwoPow, singularCohomologyEvenCup,
        map_zero, LinearMap.zero_apply]

end AtiyahSinger
