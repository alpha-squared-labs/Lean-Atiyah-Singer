/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteContinuousRepresentation
public import AtiyahSinger.Topology.AssociatedBundle
public import AtiyahSinger.Topology.SerreSwan
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Vector fibers on the original associated quotient

Public module ID: M1559.

D08. A specified complex representation supplies the actual action used in the
associated quotient. Each vector fiber is the subtype of that original quotient
over the specified base point. Its algebraic structure is transported from V by
the actual map v -> [p,v], where p is a chosen point of the original principal
fiber. This algebraic choice is not asserted to be a continuous section.

The representative map is linear for every principal point, which identifies the
transported operations with the usual associated vector-space operations. The
total topology is induced from the original quotient by forgetting only the
fiber-membership certificate. An explicit total homeomorphism retains that
topology and projection. The original associated local charts then establish
finite linear local triviality for a finite-dimensional model.

Sources: SG II.3, printed pp.93--94 / PDF pp.105--106, and HU IV.5--6.
The action convention is [p*g,v]=[p,rho(g)v]. No compactness or separation
assumption on the base or group is needed here. The construction retains the
original quotient fibers, operations, total topology and model norm.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Topology

variable {G P B V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The exact group action of the supplied continuous linear representation. -/
@[reducible]
def associatedRepresentationAction (ρ : ContRepresentation ℂ G V) : MulAction G V where
  smul g v := ρ g v
  one_smul v := by
    change (ρ 1) v = v
    simp
  mul_smul g h v := by
    change (ρ (g * h)) v = ρ g (ρ h v)
    rw [map_mul]
    rfl

/-- The actual fiber subtype of the original quotient with the specified representation action. -/
abbrev AssociatedVectorFiber (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V) (b : B) : Type _ :=
  letI := associatedRepresentationAction ρ
  {z : AssociatedBundle G P V // associatedBundleProjection hP z = b}

/-- The original quotient class, considered in its specified actual vector fiber. -/
def associatedVectorFiberMk (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V) (p : P) {b : B} (hp : projection p = b)
    (v : V) : AssociatedVectorFiber hP ρ b :=
  letI := associatedRepresentationAction ρ
  ⟨associatedBundleMk G P V p v, hp⟩

/-- A point of the original principal fiber gives bijective coordinates on its associated fiber. -/
theorem associatedVectorFiberMk_bijective (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V) (p : P) {b : B} (hp : projection p = b) :
    Function.Bijective (associatedVectorFiberMk hP ρ p hp) := by
  /- First prove injectivity: an orbit element relating [p,v] and [p,w]
  fixes p, so principal freeness makes it 1 and the vector coordinates agree.
  For surjectivity, a representative [q,v] over b has the same principal
  projection as p. The torsor theorem gives g with p*g=q, and the original
  quotient relation yields [q,v]=[p,ρ(g)v]. Thus the exact quotient-class
  map is bijective on the unchanged associated fiber. -/
  classical
  let : MulAction G V := associatedRepresentationAction ρ
  constructor
  · -- Principal freeness forces the orbit element relating two vectors over p to be one.
    intro u v huv
    obtain ⟨g, hg⟩ := Quotient.exact (congrArg Subtype.val huv)
    have hfix : MulOpposite.op g • p = p := (congrArg Prod.fst hg).symm
    obtain ⟨k, _, huniq⟩ := hP.existsUnique_smul p p rfl
    have hg1 : g = 1 := (huniq g hfix).trans (huniq 1 (one_smul Gᵐᵒᵖ p)).symm
    have hvu := congrArg (fun z : P × V ↦ z.2) hg
    rw [hg1] at hvu
    simpa only [inv_one, one_smul] using hvu.symm
  · -- Translate any original representative to the specified principal point p.
    intro w
    obtain ⟨⟨q, v⟩, hw⟩ := Quotient.exists_rep w.val
    have hq : projection q = b :=
      (congrArg (associatedBundleProjection (F := V) hP) hw).trans w.property
    obtain ⟨g, hg, _⟩ := hP.existsUnique_smul p q (hp.trans hq.symm)
    refine ⟨ρ g v, ?_⟩
    apply Subtype.ext
    calc
      associatedBundleMk G P V p (ρ g v) =
          associatedBundleMk G P V (MulOpposite.op g • p) v :=
        (associatedBundleMk_smul p g v).symm
      _ = associatedBundleMk G P V q v := congrArg (fun t : P ↦ associatedBundleMk G P V t v) hg
      _ = w.val := hw

/-- Algebraic fiber coordinates from a chosen point of the original principal fiber. -/
def associatedVectorFiberEquiv (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V) (b : B) : AssociatedVectorFiber hP ρ b ≃ V :=
  let p : {p : P // projection p = b} :=
    ⟨Classical.choose (hP.projection_properties.2.2 b),
      Classical.choose_spec (hP.projection_properties.2.2 b)⟩
  (Equiv.ofBijective (associatedVectorFiberMk hP ρ p.val p.property)
    (associatedVectorFiberMk_bijective hP ρ p.val p.property)).symm

/-- Addition on the actual quotient fiber, transported through its specified coordinates. -/
@[reducible]
def associatedVectorFiberAddCommGroup (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V) (b : B) : AddCommGroup (AssociatedVectorFiber hP ρ b) :=
  (associatedVectorFiberEquiv hP ρ b).addCommGroup

attribute [local instance] associatedVectorFiberAddCommGroup

/-- Complex scalar multiplication on the same fiber and transported additive group. -/
@[reducible]
def associatedVectorFiberModule (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V) (b : B) : Module ℂ (AssociatedVectorFiber hP ρ b) :=
  (associatedVectorFiberEquiv hP ρ b).addEquiv.module ℂ

attribute [local instance] associatedVectorFiberModule

/-- The chosen algebraic coordinates are a complex-linear equivalence on the original fiber. -/
def associatedVectorFiberLinearEquiv (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V) (b : B) : AssociatedVectorFiber hP ρ b ≃ₗ[ℂ] V :=
  (associatedVectorFiberEquiv hP ρ b).addEquiv.linearEquiv ℂ

/-- Every original principal point represents vectors linearly in these same fiber operations. -/
theorem associatedVectorFiberMk_isLinear (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V) (p : P) {b : B} (hp : projection p = b) :
    IsLinearMap ℂ (associatedVectorFiberMk hP ρ p hp) := by
  /- Stage 1: let p0 be the principal point used in the actual definition of
  the fiber coordinates. The torsor property gives a unique g with p0*g=p.
  For every v the quotient convention gives [p,v]=[p0,rho(g)v].
  Stage 2: in the chosen fiber coordinates this representative map is exactly
  the original complex-linear operator rho(g). Transported addition and
  scalar multiplication therefore make the original map v -> [p,v] linear.
  In particular, using any common p, [p,v]+[p,w]=[p,v+w]. No continuity of the
  chosen family p0(b) is claimed or used; no other fiber algebra is selected. -/
  classical
  let : MulAction G V := associatedRepresentationAction ρ
  let p₀ : P := (hP.projection_properties.2.2 b).choose
  have hp₀ : projection p₀ = b := (hP.projection_properties.2.2 b).choose_spec
  let e₀ := associatedVectorFiberLinearEquiv hP ρ b
  obtain ⟨g, hg, _⟩ := hP.existsUnique_smul p₀ p (hp₀.trans hp.symm)
  -- In the originally chosen coordinates, this representative map is exactly the operator ρ(g).
  have hcoord (v : V) : associatedVectorFiberMk hP ρ p hp v = e₀.symm (ρ g v) := by
    apply Subtype.ext
    change associatedBundleMk G P V p v = associatedBundleMk G P V p₀ (ρ g v)
    rw [← hg]
    exact associatedBundleMk_smul p₀ g v
  constructor
  · intro u v
    simp only [hcoord, map_add]
  · intro c v
    simp only [hcoord, map_smul]

/-- Forgetting only the fiber certificate identifies the total space with the actual quotient. -/
def associatedVectorTotalEquiv (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V) :
    letI := associatedRepresentationAction ρ
    TotalSpace Unit (AssociatedVectorFiber hP ρ) ≃ AssociatedBundle G P V :=
  letI := associatedRepresentationAction ρ
  { toFun := fun z ↦ z.snd.val
    invFun := fun z ↦ ⟨associatedBundleProjection hP z, ⟨z, rfl⟩⟩
    left_inv := by
      intro z
      rcases z with ⟨b, z, hz⟩
      cases hz
      rfl
    right_inv := fun _ ↦ rfl }

/-- The total topology is exactly the topology transported from the original associated quotient. -/
@[reducible]
def associatedVectorTotalTopology (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V) :
    TopologicalSpace (TotalSpace Unit (AssociatedVectorFiber hP ρ)) :=
  letI := associatedRepresentationAction ρ
  TopologicalSpace.induced (associatedVectorTotalEquiv hP ρ) inferInstance

attribute [local instance] associatedVectorTotalTopology

/-- The same total equivalence is a homeomorphism for the original quotient topology. -/
def associatedVectorTotalHomeomorph (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V) :
    letI := associatedRepresentationAction ρ
    TotalSpace Unit (AssociatedVectorFiber hP ρ) ≃ₜ AssociatedBundle G P V :=
  letI := associatedRepresentationAction ρ
  (associatedVectorTotalEquiv hP ρ).toHomeomorphOfIsInducing ⟨rfl⟩

/-- A jointly continuous finite-dimensional representation gives the actual finite-rank bundle. -/
theorem isFiniteRank_associatedVector (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V)
    (hρ : Continuous (fun z : G × V ↦ ρ z.1 z.2)) [FiniteDimensional ℂ V] :
    ComplexBundle.IsFiniteRank (AssociatedVectorFiber hP ρ) := by
  /- Install the specified action with joint continuity hρ. At each base
  point, use the original principal chart e and its associated quotient chart
  eA. Their representative coordinates use ρ((e p).2)v on the same open base.
  Choose continuous linear model coordinates
  c : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ).
  Compose eA.transFiberHomeomorph c.toHomeomorph with the original total
  homeomorphism H; its projection is still the native vector-bundle projection.
  To prove fiber linearity, take the local principal representative
  p₀=e.symm(b,1). Its representative map is linear and surjective, and the
  displayed chart sends its vector v to c v. This proves linearity of the
  chart on every original fiber and supplies the finite-rank trivialization.
  Empty bases and zero-dimensional models are included. No compactness,
  separation condition or continuous global choice of principal points is used. -/
  classical
  let : MulAction G V := associatedRepresentationAction ρ
  let : ContinuousSMul G V := ⟨hρ⟩
  let H := associatedVectorTotalHomeomorph hP ρ
  let c : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
    (Module.finBasis ℂ V).equivFun.toContinuousLinearEquiv
  constructor
  intro b₀
  obtain ⟨e, he₀, he⟩ := hP.exists_trivialization b₀
  obtain ⟨eA, hAb, _, hAi⟩ := exists_associatedBundleTrivialization (F := V) hP e he
  -- Compose actual quotient charts and model coordinates, retaining the original projection.
  let t₀ := (eA.transFiberHomeomorph c.toHomeomorph).compHomeomorph H
  let t : Trivialization (Fin (Module.finrank ℂ V) → ℂ) (π Unit (AssociatedVectorFiber hP ρ)) :=
    { toOpenPartialHomeomorph := t₀.toOpenPartialHomeomorph
      baseSet := t₀.baseSet
      open_baseSet := t₀.open_baseSet
      source_eq := by
        rw [t₀.source_eq]
        ext w
        change associatedBundleProjection (F := V) hP (H w) ∈ t₀.baseSet ↔
          w.proj ∈ t₀.baseSet
        have hw : associatedBundleProjection (F := V) hP (H w) = w.proj := w.snd.property
        rw [hw]
      target_eq := t₀.target_eq
      proj_toFun := fun w hw ↦ (t₀.proj_toFun w hw).trans w.snd.property }
  refine ⟨Module.finrank ℂ V, t, hAb.symm ▸ he₀, ?_⟩
  intro b hb
  have hbP : b ∈ e.baseSet := hAb ▸ hb
  let p₀ := e.toOpenPartialHomeomorph.symm (b, 1)
  have hp₀ : projection p₀ = b := e.proj_symm_apply' hbP
  let mk := associatedVectorFiberMk hP ρ p₀ hp₀
  have hlinear := associatedVectorFiberMk_isLinear hP ρ p₀ hp₀
  have hsurj := (associatedVectorFiberMk_bijective hP ρ p₀ hp₀).2
  -- This same local section is linear for the original transported fiber operations.
  have hformula (v : V) : (t ⟨b, mk v⟩).2 = c v := by
    change c (eA (associatedBundleMk G P V p₀ v)).2 = c v
    rw [← hAi b v hbP, eA.apply_symm_apply' hb]
  constructor
  · intro u v
    obtain ⟨u₀, rfl⟩ := hsurj u
    obtain ⟨v₀, rfl⟩ := hsurj v
    rw [← hlinear.map_add, hformula, hformula, hformula]
    exact c.map_add u₀ v₀
  · intro a v
    obtain ⟨v₀, rfl⟩ := hsurj v
    rw [← hlinear.map_smul, hformula, hformula]
    exact c.map_smul a v₀

end AtiyahSinger
