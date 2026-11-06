/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinTopology
public import AtiyahSinger.Algebra.SpinorChirality
public import AtiyahSinger.Topology.AssociatedVectorBundle
public import AtiyahSinger.Topology.AssociatedVectorCoordinates
public import AtiyahSinger.Topology.BundleSum

/-!
# The actual associated full and half-spin bundles

Public module ID: M2175.

S01. The fibers below are the original associated quotient fibers for the
specified principal native Spin bundle, with its original right action and
the original full or parity spin representation. Addition, scalar multiplication
and total topology are exactly those of AssociatedVectorFiber. No second
quotient, independent choice of representation or new bundle topology is used.

The standard exterior parity decomposition descends to a unique continuous
bundle isomorphism, specified on every representative using the same principal
point. The parity labels agree with the positive/negative normalized volume
eigenspaces in SpinorChirality and the fixed interleaved real orientation.
Finite local triviality follows from isFiniteRank_associatedVector and the
joint continuity certificates in SpinTopology; fiber dimensions are stated here.

Sources: Lawson--Michelsohn, Spin Geometry, II.3, pp.93--99, in particular the
associated spinor construction and the splitting on p.99. The construction
works on any specified principal Spin bundle; a TopologicalSpinStructure ties
that very bundle to the original oriented orthogonal frames. It does not supply
a smooth structure, connection, Clifford bundle action or Dirac operator.
The associated construction includes m=0, but no rank-zero spin structure is
asserted. The unique associated parity splitting and its fiber dimensions are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology ComplexBundle.sumTopology

variable (m : ℕ) {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection)

/-- The full complex spinor bundle on the original associated quotient fibers. -/
abbrev SpinorBundle (b : B) : Type _ :=
  AssociatedVectorFiber hP (complexSpinContRepresentation m) b

/-- Either half-spin bundle, with its original exterior parity representation and topology. -/
abbrev HalfSpinorBundle (i : ZMod 2) (b : B) : Type _ :=
  AssociatedVectorFiber hP (complexSpinParityContRepresentation m i) b

/-- The original full spinor bundle has the standard unique associated parity splitting. -/
theorem existsUnique_spinorBundleParityIso :
    letI : ∀ b, Module ℂ (HalfSpinorBundle m hP 0 b × HalfSpinorBundle m hP 1 b) :=
      fun _b ↦ inferInstance
    ∃! e : ComplexBundle.Iso (SpinorBundle m hP)
        (HalfSpinorBundle m hP 0 ×ᵇ HalfSpinorBundle m hP 1),
      ∀ (p : P) (b : B) (hp : projection p = b) (s : ComplexSpinor m),
        e.linearEquiv b (associatedVectorFiberMk hP (complexSpinContRepresentation m) p hp s) =
          (associatedVectorFiberMk hP (complexSpinParityContRepresentation m 0) p hp
            ((exteriorParityEquiv (EuclideanSpace ℂ (Fin m)) s).1),
           associatedVectorFiberMk hP (complexSpinParityContRepresentation m 1) p hp
            ((exteriorParityEquiv (EuclideanSpace ℂ (Fin m)) s).2)) := by
  /- Stage 1: the original Spin action preserves both exterior parity spaces.
  Therefore exteriorParityEquiv intertwines the full action with the product
  of the two original restricted actions. The formula on representatives
  respects [p*g,s]=[p,rho(g)s] and descends to the original quotient fibers.
  Stage 2: a common principal point identifies all three fibers with their
  original representation spaces. The descended map is linear and bijective;
  its inverse adds the two original parity vectors at that same point.
  Stage 3: descend the continuous representative map through the total
  quotient into the direct-sum topology. Finite local rank then gives
  continuity of the inverse of this same fiberwise equivalence.
  Every vector has a representative at a principal point over its base, so the
  displayed formula determines each fiber map and the whole isomorphism. -/
  classical
  let : ∀ b, Module ℂ (HalfSpinorBundle m hP 0 b × HalfSpinorBundle m hP 1 b) :=
    fun _b ↦ inferInstance
  let G := spinGroup (realSpinorQuadraticForm m)
  let V := ComplexSpinor m
  let W (i : ZMod 2) := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ
    (EuclideanSpace ℂ (Fin m))) i
  let ρ := complexSpinContRepresentation m
  let σ (i : ZMod 2) := complexSpinParityContRepresentation m i
  let d := exteriorParityEquiv (EuclideanSpace ℂ (Fin m))
  -- The original parity decomposition intertwines the full and both restricted actions.
  have hsplit (g : G) (s : V) : d (ρ g s) = (σ 0 g (d s).1, σ 1 g (d s).2) := by
    apply d.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change complexSpinRepresentation m g s =
      complexSpinRepresentation m g ((d s).1 : V) +
        complexSpinRepresentation m g ((d s).2 : V)
    rw [← map_add]
    exact congrArg (complexSpinRepresentation m g) (d.symm_apply_apply s).symm
  let := isFiniteRank_associatedVector hP ρ (continuous_complexSpinRepresentation m)
  let := isFiniteRank_associatedVector hP (σ 0) (continuous_complexSpinParityRepresentation m 0)
  let := isFiniteRank_associatedVector hP (σ 1) (continuous_complexSpinParityRepresentation m 1)
  let := ComplexBundle.isFiniteRank_sum (E := HalfSpinorBundle m hP 0)
    (F := HalfSpinorBundle m hP 1)
  let f (b : B) (p : P) (hp : projection p = b) :=
    d.trans ((associatedVectorFiberMkLinearEquiv hP (σ 0) p hp).prodCongr
      (associatedVectorFiberMkLinearEquiv hP (σ 1) p hp))
  have hcov (b : B) (p : P) (hp : projection p = b) (g : G) (v : V) :
      f b (MulOpposite.op g • p) ((hP.projection_smul g p).trans hp) v =
        f b p hp (ρ g v) := by
    change (associatedVectorFiberMk hP (σ 0) (MulOpposite.op g • p) _ (d v).1,
      associatedVectorFiberMk hP (σ 1) (MulOpposite.op g • p) _ (d v).2) =
        (associatedVectorFiberMk hP (σ 0) p hp (d (ρ g v)).1,
          associatedVectorFiberMk hP (σ 1) p hp (d (ρ g v)).2)
    rw [hsplit]
    apply Prod.ext
    · let := associatedRepresentationAction (σ 0)
      apply Subtype.ext
      exact associatedBundleMk_smul p g (d v).1
    · let := associatedRepresentationAction (σ 1)
      apply Subtype.ext
      exact associatedBundleMk_smul p g (d v).2
  -- Use one principal point in all three fibers, then verify every representative.
  let p (b : B) : P := (hP.projection_properties.2.2 b).choose
  have hp (b : B) : projection (p b) = b := (hP.projection_properties.2.2 b).choose_spec
  let a (b : B) := (associatedVectorFiberMkLinearEquiv hP ρ (p b) (hp b)).symm.trans
    (f b (p b) (hp b))
  have hrep (b : B) (q : P) (hq : projection q = b) (v : V) :
      a b (associatedVectorFiberMk hP ρ q hq v) = f b q hq v := by
    obtain ⟨g, hg, _⟩ := hP.existsUnique_smul (p b) q ((hp b).trans hq.symm)
    have hvec : associatedVectorFiberMk hP ρ q hq v =
        associatedVectorFiberMkLinearEquiv hP ρ (p b) (hp b) (ρ g v) := by
      let := associatedRepresentationAction ρ
      apply Subtype.ext
      change associatedBundleMk G P V q v = associatedBundleMk G P V (p b) (ρ g v)
      rw [← hg]
      exact associatedBundleMk_smul (p b) g v
    rw [hvec]
    change f b (p b) (hp b)
      ((associatedVectorFiberMkLinearEquiv hP ρ (p b) (hp b)).symm
        (associatedVectorFiberMkLinearEquiv hP ρ (p b) (hp b) (ρ g v))) = _
    rw [LinearEquiv.symm_apply_apply, ← hcov b (p b) (hp b) g v]
    subst q
    rfl
  -- Descend the continuous representative map into the original sum total topology.
  have hmk (i : ZMod 2) : Continuous (fun z : P × W i ↦
      (⟨projection z.1, associatedVectorFiberMk hP (σ i) z.1 rfl z.2⟩ :
        TotalSpace Unit (HalfSpinorBundle m hP i))) :=
    (associatedVectorTotalHomeomorph hP (σ i)).symm.continuous.comp continuous_quot_mk
  have hc : Continuous (fun z : P × V ↦
      (⟨projection z.1, f (projection z.1) z.1 rfl z.2⟩ :
        TotalSpace Unit (HalfSpinorBundle m hP 0 ×ᵇ HalfSpinorBundle m hP 1))) := by
    apply continuous_induced_rng.mpr
    have hd : Continuous (fun z : P × V ↦ d z.2) :=
      d.continuous_of_finiteDimensional.comp continuous_snd
    exact ((hmk 0).comp (continuous_fst.prodMk hd.fst)).prodMk
      ((hmk 1).comp (continuous_fst.prodMk hd.snd))
  let A : ComplexBundle.Hom (SpinorBundle m hP)
      (HalfSpinorBundle m hP 0 ×ᵇ HalfSpinorBundle m hP 1) :=
    { linearMap := fun b ↦ (a b).toLinearMap
      continuous_total := by
        let := associatedRepresentationAction ρ
        let H := associatedVectorTotalHomeomorph hP ρ
        have hquot : Continuous (fun z : AssociatedBundle G P V ↦
            (⟨(H.symm z).proj, a (H.symm z).proj (H.symm z).snd⟩ :
              TotalSpace Unit (HalfSpinorBundle m hP 0 ×ᵇ HalfSpinorBundle m hP 1))) := by
          apply isQuotientMap_quotient_mk'.continuous_iff.mpr
          apply hc.congr
          intro z
          change (⟨projection z.1, f (projection z.1) z.1 rfl z.2⟩ :
            TotalSpace Unit (HalfSpinorBundle m hP 0 ×ᵇ HalfSpinorBundle m hP 1)) =
            ⟨projection z.1, a (projection z.1) (associatedVectorFiberMk hP ρ z.1 rfl z.2)⟩
          rw [hrep]
        have hc' := hquot.comp H.continuous
        have hfun : ((fun z ↦
            (⟨(H.symm z).proj, a (H.symm z).proj (H.symm z).snd⟩ :
              TotalSpace Unit (HalfSpinorBundle m hP 0 ×ᵇ HalfSpinorBundle m hP 1))) ∘ H) =
            (fun z ↦ (⟨z.proj, a z.proj z.snd⟩ :
              TotalSpace Unit (HalfSpinorBundle m hP 0 ×ᵇ HalfSpinorBundle m hP 1))) := by
          funext z
          exact congrArg (fun w : TotalSpace Unit (SpinorBundle m hP) ↦
            (⟨w.proj, a w.proj w.snd⟩ :
              TotalSpace Unit (HalfSpinorBundle m hP 0 ×ᵇ HalfSpinorBundle m hP 1)))
            (H.symm_apply_apply z)
        rw [hfun] at hc'
        exact hc' }
  -- Finite local rank supplies continuity of this same inverse; representatives give uniqueness.
  let e := A.toIso (fun b ↦ (a b).bijective)
  have he (q : P) (b : B) (hq : projection q = b) (v : V) :
      e.linearEquiv b (associatedVectorFiberMk hP ρ q hq v) = f b q hq v := hrep b q hq v
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply ComplexBundle.Iso.ext
  intro b
  apply LinearEquiv.ext
  intro v
  obtain ⟨s, rfl⟩ := (associatedVectorFiberMk_bijective hP ρ (p b) (hp b)).2 v
  exact (he' (p b) b (hp b) s).trans (he (p b) b (hp b) s).symm

/-- The associated parity splitting selected with its specified representative formula. -/
def spinorBundleParityIso :
    letI : ∀ b, Module ℂ (HalfSpinorBundle m hP 0 b × HalfSpinorBundle m hP 1 b) :=
      fun _b ↦ inferInstance
    ComplexBundle.Iso (SpinorBundle m hP)
      (HalfSpinorBundle m hP 0 ×ᵇ HalfSpinorBundle m hP 1) :=
  (existsUnique_spinorBundleParityIso m hP).exists.choose

/-- The selected bundle splitting acts on the original quotient representative. -/
theorem spinorBundleParityIso_apply (p : P) (b : B) (hp : projection p = b)
    (s : ComplexSpinor m) :
    letI : ∀ b, Module ℂ (HalfSpinorBundle m hP 0 b × HalfSpinorBundle m hP 1 b) :=
      fun _b ↦ inferInstance
    (spinorBundleParityIso m hP).linearEquiv b
        (associatedVectorFiberMk hP (complexSpinContRepresentation m) p hp s) =
      (associatedVectorFiberMk hP (complexSpinParityContRepresentation m 0) p hp
        ((exteriorParityEquiv (EuclideanSpace ℂ (Fin m)) s).1),
       associatedVectorFiberMk hP (complexSpinParityContRepresentation m 1) p hp
        ((exteriorParityEquiv (EuclideanSpace ℂ (Fin m)) s).2)) := by
  /- Apply the representative specification of the very witness chosen by
  spinorBundleParityIso. The same p, hp and s occur in both quotient factors;
  no independent local section or fiber equivalence is substituted. -/
  exact (existsUnique_spinorBundleParityIso m hP).exists.choose_spec p b hp s

/-- Each original full-spin associated fiber has its standard complex dimension. -/
theorem finrank_spinorBundle (b : B) :
    Module.finrank ℂ (SpinorBundle m hP b) = 2 ^ m := by
  /- Stage 1: associatedVectorFiberLinearEquiv identifies this actual quotient
  fiber linearly with the original exterior spinor space, without changing
  its transported operations. Stage 2: the standard exterior basis is indexed
  by finite subsets of Fin m, whose cardinality is 2^m, including m=0. -/
  exact (associatedVectorFiberLinearEquiv hP (complexSpinContRepresentation m) b).finrank_eq.trans
    (finrank_complexSpinor m)

/-- In positive even vector rank, both original half-spin fibers have dimension 2^(m-1). -/
theorem finrank_halfSpinorBundle (hm : 0 < m) (i : ZMod 2) (b : B) :
    Module.finrank ℂ (HalfSpinorBundle m hP i b) = 2 ^ (m - 1) := by
  /- Stage 1: the original associated fiber equivalence preserves dimension
  and identifies the fiber with its actual exterior parity subspace.
  Stage 2: complexHalfSpinor_eq_evenOdd identifies that subspace with the
  normalized volume eigenspace of the same chirality convention. Apply
  finrank_complexHalfSpinor. The positive-rank assumption is essential:
  at m=0 the even space is a line and the odd space is zero. -/
  calc
    _ = Module.finrank ℂ
        (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :=
      (associatedVectorFiberLinearEquiv hP (complexSpinParityContRepresentation m i) b).finrank_eq
    _ = _ := by
      rw [← complexHalfSpinor_eq_evenOdd]
      exact finrank_complexHalfSpinor m hm i

end AtiyahSinger
