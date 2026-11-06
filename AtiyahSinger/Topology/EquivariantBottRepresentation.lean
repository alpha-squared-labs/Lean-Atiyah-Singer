/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.EquivariantExteriorSymbol
public import AtiyahSinger.Topology.EquivariantRepresentationAction
public import AtiyahSinger.Topology.ExteriorBott
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# The equivariant exterior Bott class of a complex representation

Public module ID: M1759.

A supplied unitary linear action acts by its actual exterior algebra maps on
the original even and odd bundles of `exteriorBottTriple`. Its compact control
is exactly the zero vector and its boundary is the specified wedge-minus-
contraction map. The class lies in the equivariant support-triple group with
its representation-ring action.

The implemented forward map is the R(G)-linear map r ↦ r times this particular
class. For a compact Lie group, its bijectivity is the content of the independent
equivariant complex Bott theorem. The full inverse and equivalence below remain
inactive source documentation, and their declarations are not Lean constants.
The class and forward map require neither group compactness nor Lie structure.
Forgetting the action recovers the original exterior-symbol class; this comparison
does not construct an equivariant inverse or prove its two inverse identities.

Sources: Atiyah--Singer I, section 2, equation (2.7), printed pp.494--496,
uses the independent equivariant Bott theorem; Spin Geometry, Appendix C,
fixes the exterior symbol. The unit-modulus phase comparison relates wedge-plus
and wedge-minus contraction on the same exterior carrier. It does not identify
V with a source's dual carrier or establish the representation-character and
complex-orientation normalizations required by such a carrier comparison.
These constructions do not use an index theorem or sphere-index normalization.

External-product, restriction and open-extension compatibility for this same class
are established under their stated hypotheses in EquivariantBottProduct,
EquivariantBottRestriction and EquivariantBottSuspension. Those diagrams are
separate from the nonequivariant forgetful formula below.
The representation lies in the universe of the bundled finite support model.
Dimension zero is included; its off-zero boundary has empty base.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

attribute [local instance] exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [DistribMulAction G V] [SMulCommClass G ℂ V] [ContinuousSMul G V]

local notation "Parity" i => CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i

/-- The actual induced exterior action on the original trivial parity bundle over V. -/
def exteriorParityEquivariantStructure (i : ZMod 2) :
    letI := modelTopology (Parity i) (Bundle.Trivial V (Parity i))
    EquivariantStructure G (Bundle.Trivial V (Parity i)) := by
  letI := modelTopology (Parity i) (Bundle.Trivial V (Parity i))
  refine
    { linearMap := fun g _ ↦ exteriorParityAction g i
      one_map := ?_
      mul_map := ?_
      continuous_action := ?_ }
  · intro x a
    apply TotalSpace.ext
    · exact one_smul G x
    · apply heq_of_eq
      exact LinearMap.congr_fun (exteriorParityAction_properties (G := G) (V := V) i).1 a
  · intro g h x a
    apply TotalSpace.ext
    · exact mul_smul g h x
    · apply heq_of_eq
      exact LinearMap.congr_fun
        ((exteriorParityAction_properties (G := G) (V := V) i).2.1 g h) a
  · -- Use the actual point-and-vector homeomorphism for the unchanged model topology.
    let e : TotalSpace Unit (Bundle.Trivial V (Parity i)) ≃ₜ V × Parity i :=
      (unitTotalHomeomorph (Parity i) (Bundle.Trivial V (Parity i))).trans
        (Bundle.Trivial.homeomorphProd V (Parity i))
    have he : Continuous (fun z : TotalSpace Unit (Bundle.Trivial V (Parity i)) ↦
        (z.proj, z.snd)) := e.continuous
    have hbase : Continuous (fun z : G × TotalSpace Unit (Bundle.Trivial V (Parity i)) ↦
        z.1 • z.2.proj) := continuous_fst.smul (he.fst.comp continuous_snd)
    have haction : Continuous (fun p : G × Parity i ↦
        exteriorParityAction p.1 i p.2) :=
      (exteriorParityAction_properties (G := G) (V := V) i).2.2
    have hinput : Continuous (fun z : G × TotalSpace Unit (Bundle.Trivial V (Parity i)) ↦
        (z.1, (z.2.snd : Parity i))) :=
      continuous_fst.prodMk (he.snd.comp continuous_snd)
    -- Infer these composites before comparing the dependent bundle output pointwise.
    have hfiber := haction.comp hinput
    have htotal := e.symm.continuous.comp (hbase.prodMk hfiber)
    exact htotal.congr (fun z ↦ by rfl)

variable (hunitary : ∀ (g : G) (u v : V), inner ℂ (g • u) (g • v) = inner ℂ u v)

include hunitary in

set_option linter.style.haveILetI false in
/-- The same zero-controlled exterior triple is equivariant for the actual induced actions. -/
theorem exteriorBottTriple_isEquivariant :
    letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
    letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
    (exteriorBottTriple V).IsEquivariant
      (exteriorParityEquivariantStructure (G := G) (V := V) 0)
      (exteriorParityEquivariantStructure (G := G) (V := V) 1) := by
  /- Stage 1: each original group action map is a linear bijection, so it
  preserves the singleton zero control and its complement. Stage 2: exterior
  multiplication is functorial for the same action map, while the supplied
  unitary identity makes contraction equivariant. The actual Clifford
  intertwining identity therefore commutes with the original even-to-odd
  off-zero boundary. No new symbol, control or representation is chosen. -/
  letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
  letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
  refine ⟨?_, ?_⟩
  · intro g x
    change g • x ∈ ({0} : Set V) ↔ x ∈ ({0} : Set V)
    simp only [Set.mem_singleton_iff]
    exact (DistribMulAction.toLinearEquiv ℂ V g).map_eq_zero_iff
  · intro g x a
    exact LinearMap.congr_fun (cliffordSymbolParity_equivariant hunitary g x.val 0) a

/-- The original exterior Bott triple, with its specified actual equivariant structures. -/
def equivariantExteriorBottTriple : EquivariantSupportBundleTriple G V :=
  letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
  letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
  letI := isFiniteRank_model (Parity 0) (Bundle.Trivial V (Parity 0))
  letI := isFiniteRank_model (Parity 1) (Bundle.Trivial V (Parity 1))
  EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily (Bundle.Trivial V (Parity 0)))
    (FiniteBundle.ofFamily (Bundle.Trivial V (Parity 1)))
    (exteriorBottTriple V)
    (exteriorParityEquivariantStructure (G := G) (V := V) 0)
    (exteriorParityEquivariantStructure (G := G) (V := V) 1)
    (exteriorBottTriple_isEquivariant hunitary)

/-- The actual equivariant exterior Bott class in the existing geometric support group. -/
def equivariantExteriorBottClass : EquivariantSupportTripleKZero G V :=
  (equivariantExteriorBottTriple hunitary).kZeroClass

/-- Forgetting the action recovers the specified original exterior-symbol K-class. -/
theorem equivariantExteriorBottClass_forget :
    letI := FiniteDimensional.proper ℂ V
    supportTripleKZeroToCompactSupport
        (equivariantSupportTripleKZeroForget (equivariantExteriorBottClass hunitary)) =
      exteriorBottClass V := by
  /- Stage 1: the existing equivariant forgetful homomorphism retains the
  underlying support triple. Its two bundles, their topologies, zero control
  and negative-square boundary are exactly those in exteriorBottTriple.
  Stage 2: the existing support-to-compactification comparison sends that
  same generator to its compact-support class, which is exteriorBottClass.
  This is a same-triple comparison, not an equivariant Bott argument. -/
  let := FiniteDimensional.proper ℂ V
  let := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
  let := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
  let := isFiniteRank_model (Parity 0) (Bundle.Trivial V (Parity 0))
  let := isFiniteRank_model (Parity 1) (Bundle.Trivial V (Parity 1))
  -- Both comparison maps evaluate on the same original exterior support generator.
  simp only [equivariantExteriorBottClass, equivariantSupportTripleKZeroForget_apply,
    supportTripleKZeroToCompactSupport_apply]
  exact (compactSupportTriple_compactSupportClass_ofBoundary
    (FiniteBundle.ofFamily (Bundle.Trivial V (Parity 0)))
    (FiniteBundle.ofFamily (Bundle.Trivial V (Parity 1))) (exteriorBottTriple V)).symm

/-- Multiplication by the actual exterior Bott class, using the existing R(G)-module action. -/
def equivariantBottLinearMap :
    RepresentationGrothendieckGroup G →ₗ[RepresentationGrothendieckGroup G]
      EquivariantSupportTripleKZero G V where
  toFun r := r • equivariantExteriorBottClass hunitary
  map_add' r s := add_smul r s (equivariantExteriorBottClass hunitary)
  map_smul' r s := mul_smul r s (equivariantExteriorBottClass hunitary)

/-
The full equivariant Bott inverse and equivalence below are retained as inactive
mathematical source documentation. The active declarations above construct the
exterior class and its forward map; the two declarations here are not Lean constants.

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [hFinite : FiniteDimensional ℝ EG] [TopologicalSpace HG]
  (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G]
  [hLie : LieGroup IG ∞ G] [hCompact : CompactSpace G] [hHausdorff : T2Space G]

include hFinite hLie hCompact hHausdorff

/-- Independent equivariant complex Bott periodicity for this actual exterior generator. -/
theorem equivariantBottLinearMap_bijective :
    Function.Bijective (equivariantBottLinearMap hunitary)
  /- Stage 1: use the independent equivariant complex Bott construction
  for the supplied finite-dimensional representation of the compact Lie
  group. Its forward map is tensoring representation classes with the
  equivariant exterior Koszul symbol, in the compact-support triple model.
  An independent equivariant inverse and both inverse identities remain
  unproved for this generator and support-triple model; the ordinary Bott
  theorem alone does not prove them equivariantly.
  Stage 2: first identify the independent construction's actual exterior
  carrier and complex orientation with this SG model. For a dual carrier,
  the required duality, representation-character comparison and orientation
  agreement remain unproved. A phase change does not establish these
  identifications. Once the carrier is fixed, the unit-modulus phase
  homotopy compares the plus and minus contraction conventions. Unitarity
  makes that homotopy equivariant with the same zero control, so the existing
  equivariant homotopy invariance identifies those same-carrier classes.
  Stage 3: the existing representation tensor action is exactly the forward
  map specified above. Transport the independent inverse identities through
  this same-model comparison. No final index theorem, sphere index or
  dimension-only comparison enters the argument. -/

/-- The independent Bott equivalence, whose forward map is multiplication by this same class. -/
def equivariantBottEquiv :
    RepresentationGrothendieckGroup G ≃ₗ[RepresentationGrothendieckGroup G]
      EquivariantSupportTripleKZero G V :=
  LinearEquiv.ofBijective (equivariantBottLinearMap hunitary)
    (equivariantBottLinearMap_bijective hunitary IG)
-/

end AtiyahSinger
