/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorTopology
public import AtiyahSinger.Topology.ModelBundleTopology
public import AtiyahSinger.Topology.SupportTripleTransport
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# The compact-support class of the actual exterior symbol

Public module ID: M1837.

For a finite-dimensional Hermitian complex vector space, the fibers below
are literally the even and odd subspaces of its exterior algebra. The boundary map
is the previously specified wedge-minus-contraction symbol, and its compact control
is the singleton zero vector. Standard trivial bundles are retyped only through the
existing `ComplexBundle.modelTopology` adapter; no coordinate replacement of the
fibers or arbitrary K-group identification enters the construction.

This is Spin Geometry, Appendix C, Example C.3, for a bundle over a point. Karoubi,
K-Theory, IV.1.4--1.6 supplies the parallel exterior-algebra construction with the
wedge-plus-contraction convention. The present file retains SG's negative-square
convention throughout. Comparison with the iterated Bott generator is separate.

The zero-dimensional space is included: its even and odd fibers have unequal ranks,
and the required boundary isomorphism has empty base. No positive-dimensional or
equal-rank assumption is imposed. Unitary naturality uses the actual induced exterior
algebra map and retains the same off-zero symbol, not an abstract generator choice.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] exteriorAlgebra_finiteDimensional
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

local notation "EvenExterior" => CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 0
local notation "OddExterior" => CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 1

/-- The original off-zero Clifford equivalence is continuous in both total-space directions. -/
theorem exteriorBott_boundary_continuity :
    letI := modelTopology EvenExterior (Bundle.Trivial V EvenExterior)
    letI := modelTopology OddExterior (Bundle.Trivial V OddExterior)
    Continuous (fun z : TotalSpace Unit
      (Restrict (Bundle.Trivial V EvenExterior) ({0} : Set V)ᶜ) ↦
        (⟨z.proj, cliffordSymbolParityEquiv z.proj.val (by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.proj.property)
            0 z.snd⟩ : TotalSpace Unit
          (Restrict (Bundle.Trivial V OddExterior) ({0} : Set V)ᶜ))) ∧
    Continuous (fun z : TotalSpace Unit
      (Restrict (Bundle.Trivial V OddExterior) ({0} : Set V)ᶜ) ↦
        (⟨z.proj, (cliffordSymbolParityEquiv z.proj.val (by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.proj.property)
            0).symm z.snd⟩ : TotalSpace Unit
          (Restrict (Bundle.Trivial V EvenExterior) ({0} : Set V)ᶜ))) := by
  /- Stage 1: identify the standard trivial total spaces with the corresponding
  products, then restrict to the complement of zero. The existing phantom-model
  homeomorphisms and restriction topologies preserve each base point and vector.
  Stage 2: apply continuous_cliffordSymbolParity to the forward product map and
  continuous_cliffordSymbolParityEquiv_symm to the inverse product map. The latter
  uses the same symbol scaled by -‖v‖⁻²; the scalar is continuous exactly on this
  nonzero locus. Compose with the vector-preserving total-space comparisons.
  In dimension zero these continuity statements concern empty total spaces. -/
  letI := modelTopology EvenExterior (Bundle.Trivial V EvenExterior)
  letI := modelTopology OddExterior (Bundle.Trivial V OddExterior)
  let A : Set V := ({0} : Set V)ᶜ
  let e₀ : TotalSpace Unit (Bundle.Trivial V EvenExterior) ≃ₜ V × EvenExterior :=
    (unitTotalHomeomorph EvenExterior (Bundle.Trivial V EvenExterior)).trans
      (Bundle.Trivial.homeomorphProd V EvenExterior)
  let e₁ : TotalSpace Unit (Bundle.Trivial V OddExterior) ≃ₜ V × OddExterior :=
    (unitTotalHomeomorph OddExterior (Bundle.Trivial V OddExterior)).trans
      (Bundle.Trivial.homeomorphProd V OddExterior)
  have h₀ := e₀.continuous.comp
    (Pullback.continuous_lift Unit (Bundle.Trivial V EvenExterior) (Subtype.val : A → V))
  have h₁ := e₁.continuous.comp
    (Pullback.continuous_lift Unit (Bundle.Trivial V OddExterior) (Subtype.val : A → V))
  constructor
  · rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial V OddExterior)
      (Subtype.val : A → V)).continuous_iff]
    have hsym := (continuous_cliffordSymbolParity (V := V) 0).comp h₀
    have htotal := e₁.symm.continuous.comp (h₀.fst.prodMk hsym)
    exact (Pullback.continuous_proj Unit (Bundle.Trivial V EvenExterior)
      (Subtype.val : A → V)).prodMk htotal
  · rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial V EvenExterior)
      (Subtype.val : A → V)).continuous_iff]
    have hbase : Continuous (fun z : TotalSpace Unit
        (Restrict (Bundle.Trivial V OddExterior) A) ↦
          (⟨z.proj.val, by
            simpa only [A, Set.mem_compl_iff, Set.mem_singleton_iff]
              using z.proj.property⟩ : {v : V // v ≠ 0})) :=
      h₁.fst.subtype_mk _
    have hsym := (continuous_cliffordSymbolParityEquiv_symm (V := V) 0).comp
      (hbase.prodMk h₁.snd)
    have htotal := e₀.symm.continuous.comp (h₁.fst.prodMk hsym)
    exact (Pullback.continuous_proj Unit (Bundle.Trivial V OddExterior)
      (Subtype.val : A → V)).prodMk htotal

/-- The actual even-to-odd exterior symbol with precisely the compact control `{0}`. -/
def exteriorBottTriple :
    letI := modelTopology EvenExterior (Bundle.Trivial V EvenExterior)
    letI := modelTopology OddExterior (Bundle.Trivial V OddExterior)
    CompactSupportTriple (Bundle.Trivial V EvenExterior) (Bundle.Trivial V OddExterior) :=
  letI := modelTopology EvenExterior (Bundle.Trivial V EvenExterior)
  letI := modelTopology OddExterior (Bundle.Trivial V OddExterior)
  { control := {0}
    isCompact_control := isCompact_singleton
    boundary :=
      { linearEquiv := fun v ↦ cliffordSymbolParityEquiv v.val (by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using v.property) 0
        continuous_total := (exteriorBott_boundary_continuity V).1
        continuous_symm := (exteriorBott_boundary_continuity V).2 } }

/-- The support class of the specified exterior triple, using its actual boundary map. -/
def exteriorBottClass :
    letI := FiniteDimensional.proper ℂ V
    CompactSupportKZero V :=
  letI := FiniteDimensional.proper ℂ V
  letI := modelTopology EvenExterior (Bundle.Trivial V EvenExterior)
  letI := modelTopology OddExterior (Bundle.Trivial V OddExterior)
  letI := isFiniteRank_model EvenExterior (Bundle.Trivial V EvenExterior)
  letI := isFiniteRank_model OddExterior (Bundle.Trivial V OddExterior)
  (exteriorBottTriple V).compactSupportClass

variable {V} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

set_option backward.isDefEq.respectTransparency.types false in
/-- A unitary base change carries the specified exterior symbol class to the same construction. -/
theorem exteriorBottClass_natural (e : V ≃ₗᵢ[ℂ] W) :
    letI := FiniteDimensional.proper ℂ V
    letI := FiniteDimensional.proper ℂ W
    compactSupportKZeroHomeomorph e.toHomeomorph (exteriorBottClass V) =
      exteriorBottClass W := by
  /- Stage 1: the exterior algebra map induced by the unitary e is a complex
  algebra equivalence preserving parity. Its restrictions give global isomorphisms
  of the two trivial parity bundles; finite dimensionality gives their continuity.
  Stage 2: exterior multiplication intertwines with this algebra map by functoriality.
  Since e preserves the Hermitian inner product, contraction intertwines as well.
  Subtraction therefore yields a commuting square for the original Clifford symbols.
  Stage 3: homeomorphism transport is proper pullback along e.symm. Its compact
  control is still {0}; conjugate the pulled-back triple by the parity isomorphisms
  from Stage 1. The commuting square identifies its boundary with the W symbol.
  Apply the existing proper-pullback and conjugation invariance of support classes.
  This compares the chosen triples themselves and does not use Bott periodicity. -/
  classical
  let := FiniteDimensional.proper ℂ V
  let := FiniteDimensional.proper ℂ W
  let PV (i : ZMod 2) := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
  let PW (i : ZMod 2) := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i
  let F := ExteriorAlgebra.map e.toLinearMap
  let G := ExteriorAlgebra.map e.symm.toLinearMap
  -- The actual exterior maps preserve parity and are inverse on vector generators.
  have hparityF (i : ZMod 2) (a : ExteriorAlgebra ℂ V)
      (ha : a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i) :
      F a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i := by
    have hrange : (LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ V))).map
        F.toLinearMap ≤ LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ W)) := by
      rintro _ ⟨x, ⟨v, rfl⟩, rfl⟩
      exact ⟨e v, (ExteriorAlgebra.map_apply_ι e.toLinearMap v).symm⟩
    have hp : (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i).map
        F.toLinearMap ≤ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i := by
      simp only [CliffordAlgebra.evenOdd, Submodule.map_iSup, Submodule.map_pow]
      exact iSup_mono (fun n ↦ pow_le_pow_left' hrange n.val)
    exact (Submodule.map_le_iff_le_comap.mp hp) ha
  have hparityG (i : ZMod 2) (b : ExteriorAlgebra ℂ W)
      (hb : b ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i) :
      G b ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i := by
    have hrange : (LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ W))).map
        G.toLinearMap ≤ LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ V)) := by
      rintro _ ⟨x, ⟨w, rfl⟩, rfl⟩
      exact ⟨e.symm w, (ExteriorAlgebra.map_apply_ι e.symm.toLinearMap w).symm⟩
    have hp : (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i).map
        G.toLinearMap ≤ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i := by
      simp only [CliffordAlgebra.evenOdd, Submodule.map_iSup, Submodule.map_pow]
      exact iSup_mono (fun n ↦ pow_le_pow_left' hrange n.val)
    exact (Submodule.map_le_iff_le_comap.mp hp) hb
  have hGF : G.comp F = AlgHom.id ℂ (ExteriorAlgebra ℂ V) := by
    apply ExteriorAlgebra.hom_ext
    ext v
    simp [F, G]
  have hFG : F.comp G = AlgHom.id ℂ (ExteriorAlgebra ℂ W) := by
    apply ExteriorAlgebra.hom_ext
    ext w
    simp [F, G]
  let L (i : ZMod 2) : PV i ≃ₗ[ℂ] PW i :=
    { toFun := fun a ↦ ⟨F a.val, hparityF i a.val a.property⟩
      invFun := fun b ↦ ⟨G b.val, hparityG i b.val b.property⟩
      left_inv := fun a ↦ Subtype.ext (AlgHom.congr_fun hGF a.val)
      right_inv := fun b ↦ Subtype.ext (AlgHom.congr_fun hFG b.val)
      map_add' := fun a b ↦ Subtype.ext (map_add F a.val b.val)
      map_smul' := fun c a ↦ Subtype.ext (map_smul F c a.val) }
  -- Unitarity preserves every Hermitian coefficient in the contraction recursion.
  have hcontract (v : V) (a : ExteriorAlgebra ℂ V) :
      contraction (e v) (F a) = F (contraction v a) := by
    induction a using CliffordAlgebra.left_induction with
    | algebraMap r =>
      simp [contraction, CliffordAlgebra.contractLeft_algebraMap]
    | add a b ha hb =>
      simp only [map_add, ha, hb]
    | ι_mul a w ha =>
      have hw : F (CliffordAlgebra.ι (0 : QuadraticForm ℂ V) w) =
          CliffordAlgebra.ι (0 : QuadraticForm ℂ W) (e w) :=
        ExteriorAlgebra.map_apply_ι e.toLinearMap w
      change CliffordAlgebra.contractLeft (innerₛₗ ℂ (e v))
        (F (CliffordAlgebra.ι (0 : QuadraticForm ℂ V) w * a)) =
          F (CliffordAlgebra.contractLeft (innerₛₗ ℂ v)
            (CliffordAlgebra.ι (0 : QuadraticForm ℂ V) w * a))
      rw [map_mul, hw, CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul F, map_mul, hw]
      change inner ℂ (e v) (e w) • F a -
        CliffordAlgebra.ι (0 : QuadraticForm ℂ W) (e w) * contraction (e v) (F a) =
          inner ℂ v w • F a -
            CliffordAlgebra.ι (0 : QuadraticForm ℂ W) (e w) * F (contraction v a)
      rw [e.inner_map_map, ha]
  have hsymbol (v : V) (a : ExteriorAlgebra ℂ V) :
      cliffordSymbol (e v) (F a) = F (cliffordSymbol v a) := by
    change ExteriorAlgebra.ι ℂ (e v) * F a - contraction (e v) (F a) =
      F (ExteriorAlgebra.ι ℂ v * a - contraction v a)
    rw [map_sub, map_mul, hcontract]
    rw [show F (ExteriorAlgebra.ι ℂ v) = ExteriorAlgebra.ι ℂ (e v) from
      ExteriorAlgebra.map_apply_ι e.toLinearMap v]
  -- Retype only the phantom models; every fiber is still the original parity subspace.
  let f : C(W, V) := ⟨e.symm, e.symm.continuous⟩
  let hf : IsProperMap f := e.symm.toHomeomorph.isProperMap
  let j (i : ZMod 2) :
      letI := modelTopology (PV i) (Bundle.Trivial V (PV i))
      letI := modelTopology (PW i) (Bundle.Trivial W (PW i))
      Iso ((f : W → V) *ᵖ (Bundle.Trivial V (PV i))) (Bundle.Trivial W (PW i)) := by
    let := modelTopology (PV i) (Bundle.Trivial V (PV i))
    let := modelTopology (PW i) (Bundle.Trivial W (PW i))
    let hV : TotalSpace Unit (Bundle.Trivial V (PV i)) ≃ₜ V × PV i :=
      (unitTotalHomeomorph (PV i) (Bundle.Trivial V (PV i))).trans
        (Bundle.Trivial.homeomorphProd V (PV i))
    let hW : TotalSpace Unit (Bundle.Trivial W (PW i)) ≃ₜ W × PW i :=
      (unitTotalHomeomorph (PW i) (Bundle.Trivial W (PW i))).trans
        (Bundle.Trivial.homeomorphProd W (PW i))
    refine { linearEquiv := fun _ ↦ L i, continuous_total := ?_, continuous_symm := ?_ }
    · have hsource := hV.continuous.comp
        (Pullback.continuous_lift Unit (Bundle.Trivial V (PV i)) f)
      have hbase := Pullback.continuous_proj Unit (Bundle.Trivial V (PV i)) f
      exact hW.symm.continuous.comp
        (hbase.prodMk ((L i).toContinuousLinearEquiv.continuous.comp hsource.snd))
    · rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial V (PV i))
        f).continuous_iff]
      exact hW.continuous.fst.prodMk (hV.symm.continuous.comp
        ((f.continuous.comp hW.continuous.fst).prodMk
          ((L i).toContinuousLinearEquiv.symm.continuous.comp hW.continuous.snd)))
  let := modelTopology (PV 0) (Bundle.Trivial V (PV 0))
  let := modelTopology (PV 1) (Bundle.Trivial V (PV 1))
  let := modelTopology (PW 0) (Bundle.Trivial W (PW 0))
  let := modelTopology (PW 1) (Bundle.Trivial W (PW 1))
  let : IsFiniteRank (Bundle.Trivial V (PV 0)) := isFiniteRank_model _ _
  let : IsFiniteRank (Bundle.Trivial V (PV 1)) := isFiniteRank_model _ _
  let : IsFiniteRank (Bundle.Trivial W (PW 0)) := isFiniteRank_model _ _
  let : IsFiniteRank (Bundle.Trivial W (PW 1)) := isFiniteRank_model _ _
  let : IsFiniteRank ((f : W → V) *ᵖ (Bundle.Trivial V (PV 0))) := isFiniteRank_pullback f
  let : IsFiniteRank ((f : W → V) *ᵖ (Bundle.Trivial V (PV 1))) := isFiniteRank_pullback f
  let a := exteriorBottTriple V
  let b := exteriorBottTriple W
  let d := (a.pullback f hf).congr (j 0) (j 1)
  have hd : d.control ⊆ ({0} : Set W) := by
    intro w hw
    change e.symm w ∈ ({0} : Set V) at hw
    have hw' : e.symm w = 0 := hw
    simpa using congrArg e hw'
  have hb : b.control ⊆ ({0} : Set W) := Set.Subset.refl _
  have hboundary (z : (d.controlᶜ : Set W)) (v : PW 0) :
      d.boundary.linearEquiv z v = cliffordSymbolParity z.val 0 v := by
    rw [CompactSupportTriple.congr_apply]
    change (f ⁻¹' a.controlᶜ : Set W) at z
    change (j 1).linearEquiv z.val
      ((a.boundary.pullback f).linearEquiv z ((j 0).symm.linearEquiv z.val v)) = _
    rw [RelativeTriple.pullback_apply]
    apply Subtype.ext
    change F (cliffordSymbol (e.symm z.val) (G v.val)) = cliffordSymbol z.val v.val
    have h := hsymbol (e.symm z.val) (G v.val)
    rw [e.apply_symm_apply, show F (G v.val) = v.val from AlgHom.congr_fun hFG v.val] at h
    exact h.symm
  -- Compare the same boundary on the common zero-complement, including dimension zero.
  have hsame : (d.enlarge {0} isCompact_singleton hd).boundary =
      (b.enlarge {0} isCompact_singleton hb).boundary := by
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    rw [CompactSupportTriple.enlarge_apply, hboundary, CompactSupportTriple.enlarge_apply]
    rfl
  have hhom : d.Homotopic b := by
    refine ⟨{0}, isCompact_singleton, hd, hb, ?_⟩
    rw [hsame]
    exact IsoHomotopy.nonempty_refl _
  calc
    compactSupportKZeroHomeomorph e.toHomeomorph (exteriorBottClass V) =
        (a.pullback f hf).compactSupportClass := (a.compactSupportClass_pullback f hf).symm
    _ = d.compactSupportClass :=
      ((a.pullback f hf).compactSupportClass_congr (j 0) (j 1)).symm
    _ = exteriorBottClass W := d.compactSupportClass_eq_of_homotopic b hhom

end AtiyahSinger
