/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportModule
public import AtiyahSinger.Topology.ExteriorBottComparison
public import AtiyahSinger.Topology.ExteriorBundle
public import AtiyahSinger.Topology.ExteriorKoszulContinuity
public import AtiyahSinger.Topology.FiniteBundleTopology

/-!
# The actual exterior Thom class on a compact base

Public module ID: M1599.

D10/K04. The bundles on the total space are the pullbacks of the actual even and
odd exterior subbundles. Their off-zero boundary is the original Clifford symbol,
with SG's wedge-minus-Hermitian-contraction convention. The only possible failure
of invertibility lies on the zero section. A continuous Hermitian metric is
expressed by joint continuity of the given pairing on the same-base double bundle.

The boundary is defined without compactness. A compact Hausdorff base makes its
zero section compact and its total space LCH, giving the existing compact-support
triple class. The Thom homomorphism uses the previously defined graph action of
K(X), with that exact class as its second factor. Its bijectivity is the compact,
degree-zero part of SG Theorem C.8 and Karoubi IV.1.9.

The graded local-to-global proof is provided downstream in KOrientation, using
full Mayer--Vietoris compatibility required by SG C.7 / KA IV.1.3. Degree-zero local bijectivity
alone does not justify the local-to-global argument. General noncompact-base Thom
maps require fiberwise support; no global compact-support Thom class is asserted
there. Boundary continuity and the resulting class construction are proved here;
the compact Thom bijectivity theorem and equivalence live in KOrientation to keep
the symbol construction below its local-to-global proof dependencies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] sumTopology exteriorTopology exteriorParityTopology
  isFiniteRank_exteriorParity t2Space_totalSpace locallyCompactSpace_totalSpace

variable {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]
  (hinner : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦ inner ℂ z.snd.1 z.snd.2))

local notation "Even" => fun x : X ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0
local notation "Odd" => fun x : X ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1
local notation "PullEven" => (π Unit E) *ᵖ Even
local notation "PullOdd" => (π Unit E) *ᵖ Odd
local notation "ZeroSection" =>
  Set.ofPred (fun z : TotalSpace Unit E ↦ Bundle.TotalSpace.snd z = 0)

include hE hinner

/-- The tautological exterior symbol and its inverse are jointly continuous off the zero section. -/
theorem exteriorThom_boundary_continuity :
    Continuous (fun z : TotalSpace Unit (Restrict PullEven ZeroSectionᶜ) ↦
      (⟨z.proj, cliffordSymbolParityEquiv z.proj.val.snd z.proj.property 0 z.snd⟩ :
        TotalSpace Unit (Restrict PullOdd ZeroSectionᶜ))) ∧
    Continuous (fun z : TotalSpace Unit (Restrict PullOdd ZeroSectionᶜ) ↦
      (⟨z.proj, (cliffordSymbolParityEquiv z.proj.val.snd z.proj.property 0).symm z.snd⟩ :
        TotalSpace Unit (Restrict PullEven ZeroSectionᶜ))) := by
  /- Stage 1: the shared exterior-continuity theorem uses original finite linear
  charts and their exterior charts. The supplied jointly continuous pairing gives
  continuous Gram entries; the fixed complex phase recovers the original Clifford
  sign without changing a total-space topology or choosing orthonormal frames.
  Stage 2: restrict the same continuous symbol to the actual even and odd subbundles,
  then pull it to the punctured original total bundle with its native pullback topology.
  Stage 3: the already proved fiberwise Clifford inverse laws give bijectivity of
  precisely this bundle map. Finite-rank inverse continuity gives continuity of its
  specified inverse. Both maps preserve the original pullback fibers; rank-zero
  charts have empty punctured fibers. -/
  let A := fun x ↦ ExteriorAlgebra ℂ (E x)
  let D := TotalSpace Unit (E ×ᵇ A)
  have hsymbol := continuous_cliffordSymbol E hinner
  -- Restrict that same total map to the even part over the punctured original bundle.
  let U := (ZeroSectionᶜ : Set (TotalSpace Unit E))
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let q : C(U, TotalSpace Unit E) := ⟨Subtype.val, continuous_subtype_val⟩
  let := isFiniteRank_pullback (E := Even) p
  let := isFiniteRank_pullback (E := Odd) p
  let := isFiniteRank_pullback (E := PullEven) q
  let := isFiniteRank_pullback (E := PullOdd) q
  have hp : Continuous (fun z : TotalSpace Unit (Restrict PullEven ZeroSectionᶜ) ↦
      z.proj) := Pullback.continuous_proj Unit PullEven Subtype.val
  have hv : Continuous (fun z : TotalSpace Unit (Restrict PullEven ZeroSectionᶜ) ↦
      z.proj.val) := continuous_subtype_val.comp hp
  have ha : Continuous (fun z : TotalSpace Unit (Restrict PullEven ZeroSectionᶜ) ↦
      (⟨z.proj.val.proj, z.snd.val⟩ : TotalSpace Unit A)) := by
    have hi : Continuous (fun z : TotalSpace Unit Even ↦
        (⟨z.proj, z.snd.val⟩ : TotalSpace Unit A)) := continuous_induced_dom
    exact hi.comp ((Pullback.continuous_lift Unit Even (π Unit E)).comp
      (Pullback.continuous_lift Unit PullEven Subtype.val))
  have hpair : Continuous (fun z : TotalSpace Unit (Restrict PullEven ZeroSectionᶜ) ↦
      (⟨z.proj.val.proj, (z.proj.val.snd, z.snd.val)⟩ : D)) := by
    apply continuous_induced_rng.mpr
    exact hv.prodMk ha
  have hforward : Continuous (fun z : TotalSpace Unit (Restrict PullEven ZeroSectionᶜ) ↦
      (⟨z.proj, cliffordSymbolParityEquiv z.proj.val.snd z.proj.property 0 z.snd⟩ :
        TotalSpace Unit (Restrict PullOdd ZeroSectionᶜ))) := by
    apply (inducing_pullbackTotalSpaceEmbedding Unit PullOdd
      (q : U → TotalSpace Unit E)).continuous_iff.mpr
    apply hp.prodMk
    apply (inducing_pullbackTotalSpaceEmbedding Unit Odd
      (π Unit E)).continuous_iff.mpr
    apply hv.prodMk
    apply continuous_induced_rng.mpr
    dsimp only [Function.comp_def, q]
    change Continuous (fun z : TotalSpace Unit (Restrict PullEven ZeroSectionᶜ) ↦
      (⟨z.proj.val.proj, cliffordSymbol z.proj.val.snd z.snd.val⟩ : TotalSpace Unit A))
    exact hsymbol.comp hpair
  -- Fiberwise bijectivity of this exact symbol gives continuity of its exact inverse.
  let f : Hom (Restrict PullEven ZeroSectionᶜ) (Restrict PullOdd ZeroSectionᶜ) :=
    { linearMap := fun z ↦ (cliffordSymbolParityEquiv z.val.snd z.property 0).toLinearMap
      continuous_total := hforward }
  refine ⟨hforward, ?_⟩
  exact f.continuous_inverse
    (fun z ↦ (cliffordSymbolParityEquiv z.val.snd z.property 0).bijective)

/-- The actual relative exterior symbol on the complement of the zero section. -/
def exteriorThomBoundary : RelativeTriple PullEven PullOdd ZeroSectionᶜ where
  linearEquiv z := cliffordSymbolParityEquiv z.val.snd z.property 0
  continuous_total := (exteriorThom_boundary_continuity E hinner).1
  continuous_symm := (exteriorThom_boundary_continuity E hinner).2

variable [CompactSpace X] [T2Space X]

/-- The compact-base Thom triple has the actual zero section as its compact control. -/
def exteriorThomTriple : CompactSupportTriple PullEven PullOdd where
  control := ZeroSection
  isCompact_control := by
    -- The control is the image of the existing continuous zero section.
    convert isCompact_range (continuous_zero_section E) using 1
    ext z
    constructor
    · intro hz
      rcases z with ⟨x, v⟩
      change v = 0 at hz
      exact ⟨x, by cases hz; rfl⟩
    · rintro ⟨x, rfl⟩
      rfl
  boundary := exteriorThomBoundary E hinner

/-- The compact-support class of the actual even-to-odd exterior Thom triple. -/
def exteriorThomClass : CompactSupportKZero (TotalSpace Unit E) :=
  let proj : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj (E := E)⟩
  letI := isFiniteRank_pullback (E := Even) proj
  letI := isFiniteRank_pullback (E := Odd) proj
  (exteriorThomTriple E hinner).compactSupportClass

/-- The specified Thom map is the original K(X)-action on the actual exterior Thom class. -/
def exteriorThomHom : ComplexKZero X →+ CompactSupportKZero (TotalSpace Unit E) :=
  (complexKZeroCompactSupportAction
    (⟨π Unit E, continuous_proj (E := E)⟩ : C(TotalSpace Unit E, X))).flip
      (exteriorThomClass E hinner)

end AtiyahSinger.ComplexBundle
