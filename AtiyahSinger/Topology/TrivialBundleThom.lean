/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleThom
public import AtiyahSinger.Topology.ExteriorBottComparison
public import AtiyahSinger.Topology.SuspendedKModule

/-!
# The exterior Thom class of a trivial Hermitian bundle

Public module ID: M2260.

The comparison preserves the actual even and odd exterior fibers and their
wedge-minus-contraction map. Native exterior total-space topologies are compared
with the fixed finite-dimensional model through the identity on vectors.
For a compact base, projection onto the model fiber is proper, and the original
Thom triple is exactly the pullback of the original exterior Bott triple.
This is the representative comparison in Spin Geometry, Appendix C.3 and C.8;
it does not assume the Thom isomorphism.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] exteriorAlgebra_finiteDimensional
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity
  isFiniteRank_pullback t2Space_totalSpace locallyCompactSpace_totalSpace sumTopology

variable {X : Type*} [TopologicalSpace X]
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

private theorem continuous_exterior_trivial :
    let := modelTopology V (Bundle.Trivial X V)
    Continuous (fun z : TotalSpace Unit
      (fun _ : X ↦ ExteriorAlgebra ℂ V) ↦ z.snd) := by
  let := modelTopology V (Bundle.Trivial X V)
  -- Expand a fixed alternating map in a finite basis to prove continuity of each monomial.
  have hmulti (k : ℕ) : Continuous (ExteriorAlgebra.ιMulti ℂ k :
      (Fin k → V) → ExteriorAlgebra ℂ V) := by
    let b := Module.finBasis ℂ V
    let T := (ExteriorAlgebra.ιMulti ℂ k (M := V)).toMultilinearMap
    have hexpand (a : Fin k → V) : T a =
        ∑ j : Fin k → Fin (Module.finrank ℂ V),
          (∏ i : Fin k, b.repr (a i) (j i)) • T (fun i ↦ b (j i)) := by
      have hb (i : Fin k) : a i =
          ∑ j : Fin (Module.finrank ℂ V), b.repr (a i) j • b j :=
        (b.sum_repr (a i)).symm
      conv_lhs => rw [show a = (fun i ↦
        ∑ j : Fin (Module.finrank ℂ V), b.repr (a i) j • b j) from funext hb]
      rw [T.map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact T.map_smul_univ _ _
    have hc : Continuous (fun a : Fin k → V ↦
        ∑ j : Fin k → Fin (Module.finrank ℂ V),
          (∏ i : Fin k, b.repr (a i) (j i)) • T (fun i ↦ b (j i))) := by
      apply continuous_finsetSum
      intro j _
      have hprod : Continuous (fun a : Fin k → V ↦
          ∏ i : Fin k, b.repr (a i) (j i)) := by
        apply continuous_finsetProd
        intro i _
        exact (continuous_apply (j i)).comp
          (b.equivFun.toContinuousLinearEquiv.continuous.comp (continuous_apply i))
      exact hprod.smul (continuous_const (y := T (fun i ↦ b (j i))))
    exact hc.congr (fun a ↦ (hexpand a).symm)
  -- Every native generator is a finite sum of these continuous wedge monomials.
  apply continuous_iSup_dom.mpr
  intro m
  apply continuous_iSup_dom.mpr
  intro k
  apply continuous_coinduced_dom.mpr
  let D := TotalSpace Unit
    (fun _ : X ↦ (Fin m → ℂ) × (∀ i : Fin m, Fin (k i) → V))
  let : TopologicalSpace D := TopologicalSpace.induced
    (fun z : D ↦ (z.proj, z.snd.1,
      (fun (i : Fin m) (j : Fin (k i)) ↦
        (⟨z.proj, z.snd.2 i j⟩ : TotalSpace Unit (Bundle.Trivial X V))))) inferInstance
  have hd : Continuous (fun z : D ↦ (z.proj, z.snd.1,
      (fun (i : Fin m) (j : Fin (k i)) ↦
        (⟨z.proj, z.snd.2 i j⟩ : TotalSpace Unit (Bundle.Trivial X V))))) :=
    continuous_induced_dom
  let e := (unitTotalHomeomorph V (Bundle.Trivial X V)).trans
    (Bundle.Trivial.homeomorphProd X V)
  change Continuous (fun z : D ↦
    ∑ i : Fin m, z.snd.1 i • ExteriorAlgebra.ιMulti ℂ (k i) (z.snd.2 i))
  apply continuous_finsetSum
  intro i _
  apply ((continuous_apply i).comp hd.snd.fst).smul
  apply (hmulti (k i)).comp
  apply continuous_pi
  intro j
  exact e.continuous.snd.comp
    ((continuous_apply j).comp ((continuous_apply i).comp hd.snd.snd))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Compare the original parity topologies and their exact pulled-back exterior triples.
/-- The actual trivial-bundle Thom class is the fiber projection's pullback of the Bott class. -/
theorem exteriorThomClass_trivial_pullback [CompactSpace X] [T2Space X] :
    letI := modelTopology V (Bundle.Trivial X V)
    letI := isFiniteRank_model V (Bundle.Trivial X V)
    letI := FiniteDimensional.proper ℂ V
    let e := (unitTotalHomeomorph V (Bundle.Trivial X V)).trans
      (Bundle.Trivial.homeomorphProd X V)
    ∀ hinner : Continuous (fun z : TotalSpace Unit
      ((Bundle.Trivial X V) ×ᵇ (Bundle.Trivial X V)) ↦ inner ℂ z.snd.1 z.snd.2),
      exteriorThomClass (Bundle.Trivial X V) hinner =
        compactSupportKZeroPullback ⟨fun z ↦ (e z).2, e.continuous.snd⟩
          (isProperMap_snd_of_compactSpace.comp e.isProperMap) (exteriorBottClass V) := by
  let := modelTopology V (Bundle.Trivial X V)
  let := isFiniteRank_model V (Bundle.Trivial X V)
  let e := (unitTotalHomeomorph V (Bundle.Trivial X V)).trans
    (Bundle.Trivial.homeomorphProd X V)
  let := FiniteDimensional.proper ℂ V
  dsimp only
  intro hinner
  let Z := TotalSpace Unit (Bundle.Trivial X V)
  let p : C(Z, V) := ⟨fun z ↦ (e z).2, e.continuous.snd⟩
  have hp : IsProperMap p := isProperMap_snd_of_compactSpace.comp e.isProperMap
  let q : C(Z, X) := ⟨π Unit (Bundle.Trivial X V), continuous_proj⟩
  let P (i : ZMod 2) : Type _ := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
  let N (i : ZMod 2) := fun _ : X ↦ P i
  let B (i : ZMod 2) := Bundle.Trivial V (P i)
  let (i : ZMod 2) : TopologicalSpace (TotalSpace Unit (B i)) :=
    modelTopology (P i) (B i)
  let (i : ZMod 2) : IsFiniteRank (B i) := isFiniteRank_model (P i) (B i)
  let (i : ZMod 2) : IsFiniteRank ((q : Z → X) *ᵖ (N i)) :=
    isFiniteRank_pullback (E := N i) q
  let (i : ZMod 2) : IsFiniteRank ((p : Z → V) *ᵖ (B i)) :=
    isFiniteRank_pullback (E := B i) p
  -- The native exterior topology gives continuity of the identity into the fixed model.
  have hvector (i : ZMod 2) : Continuous (fun z : TotalSpace Unit (N i) ↦ z.snd) := by
    have hi : Continuous (fun z : TotalSpace Unit (N i) ↦
        (⟨z.proj, z.snd.val⟩ : TotalSpace Unit (fun _ : X ↦ ExteriorAlgebra ℂ V))) :=
      continuous_induced_dom
    exact continuous_induced_rng.mpr ((continuous_exterior_trivial (X := X) V).comp hi)
  let f (i : ZMod 2) : Hom ((q : Z → X) *ᵖ (N i)) ((p : Z → V) *ᵖ (B i)) :=
    { linearMap := fun _ ↦ LinearMap.id
      continuous_total := by
        apply (inducing_pullbackTotalSpaceEmbedding Unit (B i) (p : Z → V)).continuous_iff.mpr
        have hz : Continuous (fun z : TotalSpace Unit ((q : Z → X) *ᵖ (N i)) ↦ z.proj) :=
          Pullback.continuous_proj Unit (N i) (q : Z → X)
        apply hz.prodMk
        apply (continuous_modelTotal_iff (P i) (B i) _).mpr
        let b := Bundle.Trivial.homeomorphProd V (P i)
        exact b.symm.continuous.comp ((p.continuous.comp hz).prodMk
          ((hvector i).comp (Pullback.continuous_lift Unit (N i) (q : Z → X)))) }
  let u (i : ZMod 2) := (f i).toIso (fun _ ↦ Function.bijective_id)
  have hu (i : ZMod 2) (z : Z) (w : P i) : (u i).linearEquiv z w = w := rfl
  have hus (i : ZMod 2) (z : Z) (w : P i) : (u i).symm.linearEquiv z w = w := by
    exact (hu i z (((u i).linearEquiv z).symm w)).symm.trans
      (((u i).linearEquiv z).apply_symm_apply w)
  let a := exteriorThomTriple (Bundle.Trivial X V) hinner
  let b := (exteriorBottTriple V).pullback p hp
  -- Both controls are the literal zero section; identity parity maps preserve the Clifford block.
  have htriple : a.congr (u 0) (u 1) = b := by
    change CompactSupportTriple.mk _ _ _ = CompactSupportTriple.mk _ _ _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro w
    have h₁ := a.congr_apply (u 0) (u 1) z w
    have h₂ := hu 1 z.val
      (a.boundary.linearEquiv z ((u 0).symm.linearEquiv z.val w))
    have h₃ := congrArg (a.boundary.linearEquiv z) (hus 0 z.val w)
    have h₄ : a.boundary.linearEquiv z w = b.boundary.linearEquiv z w := by
      exact ((exteriorBottTriple V).boundary.pullback_apply p z w).symm
    exact h₁.trans (h₂.trans (h₃.trans h₄))
  change a.compactSupportClass = compactSupportKZeroPullback p hp (exteriorBottClass V)
  rw [← a.compactSupportClass_congr (u 0) (u 1), htriple]
  exact (exteriorBottTriple V).compactSupportClass_pullback p hp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 500000 in
-- Normalize the original fiber projection and graph pullbacks through the external product.
/-- In the standard trivialization, the actual compact Thom operator is external Bott product. -/
theorem exteriorThomHom_trivial [CompactSpace X] [T2Space X] :
    letI := modelTopology V (Bundle.Trivial X V)
    letI := isFiniteRank_model V (Bundle.Trivial X V)
    letI := FiniteDimensional.proper ℂ V
    let e := (unitTotalHomeomorph V (Bundle.Trivial X V)).trans
      (Bundle.Trivial.homeomorphProd X V)
    ∀ (hinner : Continuous (fun z : TotalSpace Unit
      ((Bundle.Trivial X V) ×ᵇ (Bundle.Trivial X V)) ↦ inner ℂ z.snd.1 z.snd.2))
      (a : ComplexKZero X),
      compactSupportKZeroHomeomorph e (exteriorThomHom (Bundle.Trivial X V) hinner a) =
        compactSupportKZeroExternalProduct ((compactSupportKZeroCompactEquiv X).symm a)
          (exteriorBottClass V) := by
  let := modelTopology V (Bundle.Trivial X V)
  let := isFiniteRank_model V (Bundle.Trivial X V)
  let := FiniteDimensional.proper ℂ V
  dsimp only
  intro hinner a
  let Z := TotalSpace Unit (Bundle.Trivial X V)
  let e := (unitTotalHomeomorph V (Bundle.Trivial X V)).trans
    (Bundle.Trivial.homeomorphProd X V)
  let p : C(Z, V) := ⟨fun z ↦ (e z).2, e.continuous.snd⟩
  have hp : IsProperMap p := isProperMap_snd_of_compactSpace.comp e.isProperMap
  let q : C(Z, X) := ⟨π Unit (Bundle.Trivial X V), continuous_proj⟩
  let g : C(Z, X × Z) := q.prodMk (ContinuousMap.id Z)
  have hg : IsProperMap g :=
    isProperMap_of_comp_of_t2 g.continuous continuous_snd isProperMap_id
  let l : C(X × Z, X × V) := (ContinuousMap.id X).prodMap p
  have hl : IsProperMap l := isProperMap_id.prodMap hp
  let t : C(X × V, Z) := ⟨e.symm, e.symm.continuous⟩
  let ac := (compactSupportKZeroCompactEquiv X).symm a
  let b := exteriorBottClass V
  -- First replace the actual exterior Thom class by the same fiber Bott pullback.
  have hclass := exteriorThomClass_trivial_pullback (X := X) V hinner
  change compactSupportKZeroPullback t e.symm.isProperMap
    (compactSupportKZeroAction q ac (exteriorThomClass (Bundle.Trivial X V) hinner)) =
      compactSupportKZeroExternalProduct ac b
  rw [hclass]
  -- Naturality moves that pullback through the external product before the graph restriction.
  have hprod := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id X) isProperMap_id p hp ac b
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hprod
  change compactSupportKZeroPullback t e.symm.isProperMap
    (compactSupportKZeroPullback g hg
      (compactSupportKZeroExternalProduct ac (compactSupportKZeroPullback p hp b))) = _
  rw [← hprod, ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
  rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
  -- The composite sends (x,v) to (x,v), with neither a new generator nor a sign change.
  have hid : l.comp (g.comp t) = ContinuousMap.id (X × V) := by
    apply ContinuousMap.ext
    intro z
    rfl
  change compactSupportKZeroPullback (l.comp (g.comp t))
    (hl.comp (hg.comp e.symm.isProperMap)) (compactSupportKZeroExternalProduct ac b) = _
  simp only [hid, compactSupportKZeroPullback_id, AddMonoidHom.id_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 600000 in
-- Elaborate the suspended action with the same exterior Bott class in every degree.
/-- Exterior Thom action for a trivial Hermitian bundle is bijective in every degree. -/
theorem exteriorThomClass_trivial_action_bijective [CompactSpace X] [T2Space X] :
    letI := modelTopology V (Bundle.Trivial X V)
    letI := isFiniteRank_model V (Bundle.Trivial X V)
    ∀ (hinner : Continuous (fun z : TotalSpace Unit
      ((Bundle.Trivial X V) ×ᵇ (Bundle.Trivial X V)) ↦ inner ℂ z.snd.1 z.snd.2))
      (n : ℕ),
      Function.Bijective ((compactSupportKAction n
        (⟨π Unit (Bundle.Trivial X V), continuous_proj⟩ :
          C(TotalSpace Unit (Bundle.Trivial X V), X))).flip
        (exteriorThomClass (Bundle.Trivial X V) hinner)) := by
  let := modelTopology V (Bundle.Trivial X V)
  let := isFiniteRank_model V (Bundle.Trivial X V)
  let := FiniteDimensional.proper ℂ V
  intro hinner n
  let Z := TotalSpace Unit (Bundle.Trivial X V)
  let T := Fin n → ℝ
  let e := (unitTotalHomeomorph V (Bundle.Trivial X V)).trans
    (Bundle.Trivial.homeomorphProd X V)
  let h : Z × T ≃ₜ (X × T) × V :=
    ((e.prodCongr (Homeomorph.refl T)).trans (Homeomorph.prodAssoc X V T)).trans
      (((Homeomorph.refl X).prodCongr (Homeomorph.prodComm V T)).trans
        (Homeomorph.prodAssoc X T V).symm)
  let H := compactSupportKZeroHomeomorphEquiv h
  let p : C(Z, V) := ⟨fun z ↦ (e z).2, e.continuous.snd⟩
  have hp : IsProperMap p := isProperMap_snd_of_compactSpace.comp e.isProperMap
  let q : C(Z, X) := ⟨π Unit (Bundle.Trivial X V), continuous_proj⟩
  let u := exteriorThomClass (Bundle.Trivial X V) hinner
  let B : CompactSupportK n X →+ CompactSupportKZero ((X × T) × V) :=
    compactSupportKZeroExternalProduct.flip (exteriorBottClass V)
  have hB : Function.Bijective (B : CompactSupportK n X →+ _) :=
    exteriorBottExternalProduct_bijective (X × T) V
  -- The same suspended graph factors through the same fiber projection.
  have hsquare (a : CompactSupportK n X) : H (compactSupportKAction n q a u) = B a := by
    let g : C(Z × T, (X × T) × Z) :=
      (q.prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
    let r : C((X × T) × Z, Z × T) :=
      ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
    have hg : IsProperMap g :=
      isProperMap_of_comp_of_t2 g.continuous r.continuous isProperMap_id
    let l : C((X × T) × Z, (X × T) × V) := (ContinuousMap.id (X × T)).prodMap p
    have hl : IsProperMap l := isProperMap_id.prodMap hp
    let t : C((X × T) × V, Z × T) := ⟨h.symm, h.symm.continuous⟩
    have hclass := exteriorThomClass_trivial_pullback (X := X) V hinner
    change compactSupportKZeroPullback t h.symm.isProperMap
      (compactSupportKZeroPullback g hg (compactSupportKZeroExternalProduct a u)) = B a
    change u = compactSupportKZeroPullback p hp (exteriorBottClass V) at hclass
    rw [hclass]
    have hprod := compactSupportKZeroExternalProduct_properPullback
      (ContinuousMap.id (X × T)) isProperMap_id p hp a (exteriorBottClass V)
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hprod
    rw [← hprod, ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    have hid : l.comp (g.comp t) = ContinuousMap.id ((X × T) × V) := by
      apply ContinuousMap.ext
      intro z
      rfl
    change compactSupportKZeroPullback (l.comp (g.comp t))
      (hl.comp (hg.comp h.symm.isProperMap))
        (compactSupportKZeroExternalProduct a (exteriorBottClass V)) = B a
    simp only [hid, compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
    rfl
  -- Transport bijectivity of this exact exterior product, retaining every real coordinate.
  constructor
  · intro a b hab
    apply hB.injective
    exact (hsquare a).symm.trans ((congrArg H hab).trans (hsquare b))
  · intro b
    obtain ⟨a, ha⟩ := hB.surjective (H b)
    refine ⟨a, H.injective ?_⟩
    exact (hsquare a).trans ha

end AtiyahSinger.ComplexBundle
