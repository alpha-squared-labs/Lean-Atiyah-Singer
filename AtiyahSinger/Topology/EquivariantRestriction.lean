/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantSupportTripleKZero
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Restricting the original equivariant support data along a group homomorphism

Public module ID: M1808.

Precomposition along a continuous homomorphism H -> G keeps the original base,
fibers, topologies, compact controls and boundary maps. The restricted base
action is mathlib's native `MulAction.compHom`, with its native joint continuity
certificate. Both instances are explicit in the result types; no alternative
action object or replacement equivariant bundle is selected.

Actual equivariant global squares and arbitrary equivariant identity stabilizers
restrict with the same maps and bundles. Consequently restriction descends to
the original support-group presentation and to the actual stable quotient.
The two descents commute with the existing stable-to-group comparison, and
forgetting the restricted action retains the same ordinary class.

Sources: SG III.9 and ASI I Section 2 give the equivariant bundle framework.
Restriction is the standard action-precomposition construction; the explicit
descent and compatibility statements are project supplements, not separately
numbered lemmas in these passages. No compactness of either group, local
compactness of the base, invariant metric or equivariant trivial complement
is used. The restriction laws and both quotient descents are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {G H X : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-- Precompose the original moving-fiber action with the specified continuous homomorphism. -/
def EquivariantStructure.restrict
    {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)]
    (σ : EquivariantStructure G E) (φ : H →ₜ* G) :
    letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
    letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
    EquivariantStructure H E := by
  letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
  letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
  exact
    { linearMap := fun h x ↦ σ.linearMap (φ h) x
      one_map := fun x v ↦ by
        change (⟨φ 1 • x, σ.linearMap (φ 1) x v⟩ : TotalSpace Unit E) = ⟨x, v⟩
        rw [map_one]
        exact σ.one_map x v
      mul_map := fun h k x v ↦ by
        change (⟨φ (h * k) • x, σ.linearMap (φ (h * k)) x v⟩ : TotalSpace Unit E) =
          ⟨φ h • (φ k • x), σ.linearMap (φ h) (φ k • x) (σ.linearMap (φ k) x v)⟩
        rw [map_mul]
        exact σ.mul_map (φ h) (φ k) x v
      continuous_action := σ.continuous_action.comp
        ((φ.continuous.comp continuous_fst).prodMk continuous_snd) }

/-- Restrict the two specified actions, retaining the exact original support triple. -/
def EquivariantSupportBundleTriple.restrict
    (a : EquivariantSupportBundleTriple G X) (φ : H →ₜ* G) :
    letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
    letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
    EquivariantSupportBundleTriple H X := by
  letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
  letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
  exact ⟨a.1,
    { sourceAction := a.2.sourceAction.restrict φ
      targetAction := a.2.targetAction.restrict φ
      isEquivariant :=
        { invariant_control := fun h x ↦ a.2.isEquivariant.invariant_control (φ h) x
          boundary_intertwines := fun h x v ↦
            a.2.isEquivariant.boundary_intertwines (φ h) x v } }⟩

/-- Restriction preserves the original isomorphism relations, sums and identity stabilizers. -/
theorem EquivariantSupportBundleTriple.restrict_properties (φ : H →ₜ* G) :
    letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
    letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
    (∀ a b : EquivariantSupportBundleTriple G X, a.IsIsomorphic b →
      (a.restrict φ).IsIsomorphic (b.restrict φ)) ∧
    (∀ a b : EquivariantSupportBundleTriple G X, a.IsStablyIsomorphic b →
      (a.restrict φ).IsStablyIsomorphic (b.restrict φ)) ∧
    (∀ a b : EquivariantSupportBundleTriple G X,
      (a.sum b).restrict φ = (a.restrict φ).sum (b.restrict φ)) ∧
    ∀ (E : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber),
      (identity E ρE).restrict φ = identity E (ρE.restrict φ) := by
  /- Stage 1: retain the original common compact control and both original
  global bundle isomorphisms. Substitute phi(h) into their G-equivariance
  equations and into invariance of the control. The same boundary square
  then witnesses an H-equivariant isomorphism for the native restricted action.
  Stage 2: direct sum evaluates both original action blocks at phi(h), and
  identity retains exactly the original identity boundary and the restricted
  action. Thus the displayed operations agree as actual Sigma triples; only
  their proof fields may differ, and those agree by proof irrelevance.
  Stage 3: restrict the two actual finite-rank stabilizing bundles and their
  actions, then apply Stage 1 to the same stabilized square. Stage 2 identifies
  its original sum and identity carriers with the displayed restricted ones.
  Arbitrary equivariant stabilizers remain admissible; no product-bundle
  replacement, compact-group averaging or finite trivial complement is used.
  This one certificate is the descent input for both quotients below. -/
  let : MulAction H X := MulAction.compHom X φ.toMonoidHom
  let : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
  have hiso (a b : EquivariantSupportBundleTriple G X) (h : a.IsIsomorphic b) :
      (a.restrict φ).IsIsomorphic (b.restrict φ) := by
    -- Keep the entire original square; only precompose its action equations.
    obtain ⟨K, hK, hInv, ha, hb, u, v, hu, hv, hsquare⟩ := h
    exact ⟨K, hK, (fun h x ↦ hInv (φ h) x), ha, hb, u, v,
      (fun h x w ↦ hu (φ h) x w), (fun h x w ↦ hv (φ h) x w), hsquare⟩
  have hsum (a b : EquivariantSupportBundleTriple G X) :
      (a.sum b).restrict φ = (a.restrict φ).sum (b.restrict φ) := by
    -- Both component actions are the original maps evaluated at φ(h).
    rfl
  have hid (E : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber) :
      (EquivariantSupportBundleTriple.identity E ρE).restrict φ =
        EquivariantSupportBundleTriple.identity E (ρE.restrict φ) := by
    rfl
  refine ⟨hiso, ?_, hsum, hid⟩
  intro a b h
  obtain ⟨E, F, ρE, ρF, h⟩ := h
  refine ⟨E, F, ρE.restrict φ, ρF.restrict φ, ?_⟩
  -- The original stabilizing bundles remain unchanged, with their restricted actions.
  have hrestricted := hiso _ _ h
  rw [hsum, hsum, hid, hid] at hrestricted
  exact hrestricted

/-- The actual additive restriction map on the original equivariant support-group presentation. -/
def equivariantSupportTripleKZeroRestrict (φ : H →ₜ* G) :
    letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
    letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
    EquivariantSupportTripleKZero G X →+ EquivariantSupportTripleKZero H X := by
  letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
  letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
  -- Use the original presentation's unique homomorphism with these actual generator values.
  apply Exists.choose
  apply equivariantSupportTripleKZero_universal_property
    (fun a : EquivariantSupportBundleTriple G X ↦ (a.restrict φ).kZeroClass)
  · intro a b h
    -- The same original global equivariant square restricts along phi.
    exact equivariantSupportTripleKZero_generator_relations.1 _ _
      ((EquivariantSupportBundleTriple.restrict_properties φ).1 a b h)
  · intro a b
    -- Restriction keeps the original direct-sum carrier and its two action blocks.
    rw [(EquivariantSupportBundleTriple.restrict_properties φ).2.2.1 a b]
    exact equivariantSupportTripleKZero_generator_relations.2.1 _ _
  · intro E ρE
    -- Every original equivariant identity stabilizer restricts on the same bundle.
    rw [(EquivariantSupportBundleTriple.restrict_properties φ).2.2.2 E ρE]
    exact equivariantSupportTripleKZero_generator_relations.2.2 _ _

/-- Restriction sends each original generator to the class of its actual restricted action. -/
theorem equivariantSupportTripleKZeroRestrict_apply (φ : H →ₜ* G)
    (a : EquivariantSupportBundleTriple G X) :
    letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
    letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
    equivariantSupportTripleKZeroRestrict φ a.kZeroClass = (a.restrict φ).kZeroClass := by
  /- The additive map is selected from the original universal property with
  generator value a mapped to the class of its actual restriction. Read the
  generator equation from that same unique witness. The underlying ordinary
  triple, compact control and boundary remain exactly a.1 throughout. -/
  let : MulAction H X := MulAction.compHom X φ.toMonoidHom
  let : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
  exact (equivariantSupportTripleKZero_universal_property
    (fun b : EquivariantSupportBundleTriple G X ↦ (b.restrict φ).kZeroClass)
    (fun b c h ↦ equivariantSupportTripleKZero_generator_relations.1 _ _
      ((EquivariantSupportBundleTriple.restrict_properties φ).1 b c h))
    (fun b c ↦ by
      rw [(EquivariantSupportBundleTriple.restrict_properties φ).2.2.1 b c]
      exact equivariantSupportTripleKZero_generator_relations.2.1 _ _)
    (fun E ρE ↦ by
      rw [(EquivariantSupportBundleTriple.restrict_properties φ).2.2.2 E ρE]
      exact equivariantSupportTripleKZero_generator_relations.2.2 _ _)).choose_spec.1 a

/-- Restrict actual stable classes using the same original representative and stabilizers. -/
def stableEquivariantSupportTripleClassRestrict (φ : H →ₜ* G) :
    letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
    letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
    StableEquivariantSupportTripleClass G X → StableEquivariantSupportTripleClass H X := by
  letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
  letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
  exact Quotient.map (fun a : EquivariantSupportBundleTriple G X ↦ a.restrict φ)
    (fun a b h ↦ (EquivariantSupportBundleTriple.restrict_properties φ).2.1 a b h)

/-- The two restriction descents commute with forgetting and with the original stable comparison. -/
theorem equivariantSupportRestriction_compatibility (φ : H →ₜ* G) :
    letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
    letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
    (equivariantSupportTripleKZeroForget (G := H) (X := X)).comp
        (equivariantSupportTripleKZeroRestrict φ) =
      equivariantSupportTripleKZeroForget (G := G) (X := X) ∧
    ∀ q : StableEquivariantSupportTripleClass G X,
      stableEquivariantSupportTripleClassToKZero
          (stableEquivariantSupportTripleClassRestrict φ q) =
        equivariantSupportTripleKZeroRestrict φ (stableEquivariantSupportTripleClassToKZero q) := by
  /- Stage 1: on each original group generator, restriction keeps exactly its
  ordinary support triple. Apply the restriction generator equation and both
  original forgetful generator equations. The two additive maps agree on all
  generators, hence on the specified free-group quotient.
  Stage 2: quotient induction represents q by one original equivariant triple.
  The stable restriction is the actual Quotient.map of that triple, while
  both stable-to-group maps are the original Quotient.lift of its generator.
  The same restriction generator equation therefore identifies the two routes.
  This naturality holds without assuming either stable-to-group map bijective,
  and so does not acquire the compact-group or LCH hypotheses of that theorem. -/
  let : MulAction H X := MulAction.compHom X φ.toMonoidHom
  let : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
  constructor
  · -- Forgetting after restriction is determined on the same free-group generators.
    apply AddMonoidHom.ext
    intro z
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective
      (equivariantSupportTripleKZeroRelations (G := G) (X := X)) z
    have heq : ((equivariantSupportTripleKZeroForget (G := H) (X := X)).comp
        (equivariantSupportTripleKZeroRestrict φ)).comp
          (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations (G := G) (X := X))) =
        (equivariantSupportTripleKZeroForget (G := G) (X := X)).comp
          (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations (G := G) (X := X))) := by
      apply FreeAbelianGroup.lift_ext
      intro a
      change equivariantSupportTripleKZeroForget
          (equivariantSupportTripleKZeroRestrict φ a.kZeroClass) =
        equivariantSupportTripleKZeroForget a.kZeroClass
      rw [equivariantSupportTripleKZeroRestrict_apply, equivariantSupportTripleKZeroForget_apply,
        equivariantSupportTripleKZeroForget_apply]
      rfl
    exact DFunLike.congr_fun heq w
  · -- Both stable maps evaluate at the very same restricted representative.
    intro q
    refine Quotient.inductionOn q ?_
    intro a
    change (a.restrict φ).kZeroClass = equivariantSupportTripleKZeroRestrict φ a.kZeroClass
    exact (equivariantSupportTripleKZeroRestrict_apply φ a).symm

/-- Restriction along the identity preserves the same group and its original generators. -/
theorem equivariantSupportTripleKZeroRestrict_id :
    equivariantSupportTripleKZeroRestrict (X := X) (ContinuousMonoidHom.id G) =
      AddMonoidHom.id (EquivariantSupportTripleKZero G X) := by
  /- The native action precomposed with identity is definitionally the original
  action. On every generator, the restricted triple has the same underlying
  data and the same linear maps; proof irrelevance identifies the certificates.
  Apply the generator formula, then uniqueness in the original presentation's
  universal property. No comparison with stable classes is needed. -/
  -- The presentation reduces equality to its original triple generators.
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective
    (equivariantSupportTripleKZeroRelations (G := G) (X := X)) z
  have heq : (equivariantSupportTripleKZeroRestrict (X := X)
      (ContinuousMonoidHom.id G)).comp
        (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations (G := G) (X := X))) =
      (AddMonoidHom.id (EquivariantSupportTripleKZero G X)).comp
        (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations (G := G) (X := X))) := by
    apply FreeAbelianGroup.lift_ext
    intro a
    change equivariantSupportTripleKZeroRestrict (ContinuousMonoidHom.id G) a.kZeroClass =
      a.kZeroClass
    rw [equivariantSupportTripleKZeroRestrict_apply]
    -- Precomposing by identity leaves the entire triple and its fiber action unchanged.
    rfl
  exact DFunLike.congr_fun heq w

/-- Successive restrictions are precomposition along the same composite group homomorphism. -/
theorem equivariantSupportTripleKZeroRestrict_comp
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (φ : H →ₜ* G) (ψ : K →ₜ* H) :
    letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
    letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
    letI : MulAction K X := MulAction.compHom X ψ.toMonoidHom
    letI : ContinuousSMul K X := MulAction.continuousSMul_compHom ψ.continuous
    equivariantSupportTripleKZeroRestrict (X := X) (φ.comp ψ) =
      (equivariantSupportTripleKZeroRestrict (X := X) ψ).comp
        (equivariantSupportTripleKZeroRestrict (X := X) φ) := by
  /- Stage 1: both native base actions evaluate a group element k as phi(psi(k))
  acting on the same x. The composed and successive compHom instances have
  definitionally equal action functions and proof-irrelevant group laws.
  On every original triple, both routes therefore retain identical fibers,
  topology, compact control and boundary, with linear action sigma(phi(psi(k))).
  Stage 2: apply the generator characterization to the direct restriction and
  to both successive restrictions. They agree on every original generator,
  so uniqueness in the presentation identifies the additive homomorphisms.
  No injectivity, surjectivity or properness of either homomorphism is needed. -/
  let : MulAction H X := MulAction.compHom X φ.toMonoidHom
  let : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
  let : MulAction K X := MulAction.compHom X ψ.toMonoidHom
  let : ContinuousSMul K X := MulAction.continuousSMul_compHom ψ.continuous
  -- Compare direct and successive restriction on the original free-group generators.
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective
    (equivariantSupportTripleKZeroRelations (G := G) (X := X)) z
  have heq : (equivariantSupportTripleKZeroRestrict (X := X) (φ.comp ψ)).comp
      (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations (G := G) (X := X))) =
      ((equivariantSupportTripleKZeroRestrict (X := X) ψ).comp
        (equivariantSupportTripleKZeroRestrict (X := X) φ)).comp
          (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations (G := G) (X := X))) := by
    apply FreeAbelianGroup.lift_ext
    intro a
    change equivariantSupportTripleKZeroRestrict (φ.comp ψ) a.kZeroClass =
      equivariantSupportTripleKZeroRestrict ψ (equivariantSupportTripleKZeroRestrict φ a.kZeroClass)
    rw [equivariantSupportTripleKZeroRestrict_apply, equivariantSupportTripleKZeroRestrict_apply,
      equivariantSupportTripleKZeroRestrict_apply]
    -- Both actions evaluate σ at φ(ψ(k)); all controls and boundary data coincide.
    rfl
  exact DFunLike.congr_fun heq w

end AtiyahSinger.ComplexBundle
