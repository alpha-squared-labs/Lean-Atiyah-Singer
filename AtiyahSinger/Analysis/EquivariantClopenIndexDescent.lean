/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantClopenFamilyRefinement
public import AtiyahSinger.Analysis.EquivariantClopenFamilyReindex
public import AtiyahSinger.Analysis.EquivariantEllipticSymbolSum

/-!
# Descent of the full equivariant index through actual common refinements

Public module ID: M0481.

Both original families are placed on the same finite invariant clopen pieces.
The existing same-K-class theorem then gives independence, and the actual
bundle direct sum gives additivity. Only after these conclusions is the index
on the original equivariant cotangent K group selected. Empty pieces and
independent ranks are retained throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

variable [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Two original families admit representatives on one common partition, preserving both values. -/
theorem EquivariantClopenSymbolFamily.exists_common_refinement
    (a b : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G)) :
    ∃ P : EquivariantClopenPartition (G := G) (M := M),
      ∃ c d : P.Symbols (n := n) (VG := VG),
        (EquivariantClopenSymbolFamily.mk P c).kClass = a.kClass ∧
        (EquivariantClopenSymbolFamily.mk P c).index = a.index ∧
        (EquivariantClopenSymbolFamily.mk P d).kClass = b.kClass ∧
        (EquivariantClopenSymbolFamily.mk P d).index = b.index := by
  classical
  obtain ⟨c, hc, hic⟩ := a.exists_refinement b.partition
  obtain ⟨d, hd, hid⟩ := b.exists_refinement a.partition
  let P := a.partition.refinement b.partition
  let Q := b.partition.refinement a.partition
  let ep := (Fintype.equivFin (Fin a.partition.size × Fin b.partition.size)).symm
  let eq := (Fintype.equivFin (Fin b.partition.size × Fin a.partition.size)).symm
  let e : Fin P.size ≃ Fin Q.size :=
    ep.trans ((Equiv.prodComm _ _).trans eq.symm)
  have hpieces (t : Fin P.size) : P.piece t = Q.piece (e t) := by
    have h : eq (e t) = ((ep t).2, (ep t).1) := by exact eq.apply_symm_apply _
    change a.partition.piece (ep t).1 ⊓ b.partition.piece (ep t).2 =
      b.partition.piece (eq (e t)).1 ⊓ a.partition.piece (eq (e t)).2
    rw [h]
    exact inf_comm _ _
  -- Reverse the indexing of the second refinement while keeping the same actual open sets.
  obtain ⟨d', hd', hid'⟩ := (EquivariantClopenSymbolFamily.mk Q d).exists_reindex P e hpieces
  exact ⟨P, c, d', hc, hic, hd'.trans hd, hid'.trans hid⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equal original K classes give equal full indices for any two original clopen families. -/
theorem EquivariantClopenSymbolFamily.index_eq_of_kClass_eq [FiniteDimensional ℝ VG]
    (a b : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G))
    (h : a.kClass = b.kClass) : a.index = b.index := by
  obtain ⟨P, c, d, hc, hic, hd, hid⟩ := a.exists_common_refinement b
  let := P.mulAction
  let := P.continuousSMul
  let := P.contMDiffSMul (n := n) (VG := VG)
  let := P.compactSpace
  let Φ := equivariantCotangentClopenEquiv (n := n) 𝓘(ℝ, VG) P.piece P.isClosed
    P.equivariant P.disjoint P.cover
  have hclasses : (EquivariantClopenSymbolFamily.mk P c).kClass =
      (EquivariantClopenSymbolFamily.mk P d).kClass := hc.trans (h.trans hd.symm)
  have hcoords (i : Fin P.size) : (c i).kClass = (d i).kClass := by
    have hi := congrArg (fun z ↦ Φ z i) hclasses
    change Φ (Φ.symm (fun j ↦ (c j).kClass)) i =
      Φ (Φ.symm (fun j ↦ (d j).kClass)) i at hi
    simpa only [Φ.apply_symm_apply] using hi
  rw [← hic, ← hid]
  change (∑ i, (c i).index) = ∑ i, (d i).index
  apply Finset.sum_congr rfl
  intro i _
  -- The same-class theorem now compares symbols on the same actual base with the same action.
  exact equivariantHomogeneousAnalyticIndex_eq_of_equivariantSymbolKClass_eq
    (c i).sourceAction (c i).targetAction (d i).sourceAction (d i).targetAction
    (c i).source_smooth (c i).target_smooth (d i).source_smooth (d i).target_smooth
    (c i).symbol (d i).symbol (c i).elliptic (d i).elliptic
    (c i).equivariant (d i).equivariant (hcoords i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Genuine direct sums on a common partition realize addition of classes and full indices. -/
theorem EquivariantClopenSymbolFamily.exists_add
    (a b : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G)) :
    ∃ c : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G),
      c.kClass = a.kClass + b.kClass ∧ c.index = a.index + b.index := by
  classical
  obtain ⟨P, c, d, hc, hic, hd, hid⟩ := a.exists_common_refinement b
  let := P.mulAction
  let := P.continuousSMul
  let := P.contMDiffSMul (n := n) (VG := VG)
  let := P.compactSpace
  choose s hs his using fun i ↦ (c i).exists_add (d i)
  refine ⟨⟨P, s⟩, ?_, ?_⟩
  · let Φ := equivariantCotangentClopenEquiv (n := n) 𝓘(ℝ, VG) P.piece P.isClosed
      P.equivariant P.disjoint P.cover
    rw [← hc, ← hd]
    change Φ.symm (fun i ↦ (s i).kClass) =
      Φ.symm (fun i ↦ (c i).kClass) + Φ.symm (fun i ↦ (d i).kClass)
    rw [← map_add]
    congr 1
    funext i
    exact hs i
  · rw [← hic, ← hid]
    change (∑ i, (s i).index) = (∑ i, (c i).index) + ∑ i, (d i).index
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ ↦ his i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unique additive full index evaluates every original finite clopen symbol family. -/
theorem existsUnique_equivariantClopenIndex [FiniteDimensional ℝ VG] :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∃! I : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) →+
        RepresentationGrothendieckGroup G,
      ∀ a : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G),
        I a.kClass = a.index := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  -- Choose whole families once, then prove their value independent of every choice.
  choose a ha using exists_equivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G)
  let f (z : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M))) :
      RepresentationGrothendieckGroup G := (a z).index
  have heval (b : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G)) :
      f b.kClass = b.index := (a b.kClass).index_eq_of_kClass_eq b (ha b.kClass)
  have hadd (z w : EquivariantSupportTripleKZero G
      (CotangentTotalSpace (n := n) (M := M))) : f (z + w) = f z + f w := by
    obtain ⟨b, hb, hi⟩ := (a z).exists_add (a w)
    rw [ha, ha] at hb
    exact (congrArg f hb).symm.trans ((heval b).trans hi)
  let I : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) →+
      RepresentationGrothendieckGroup G := AddMonoidHom.mk' f hadd
  refine ⟨I, heval, ?_⟩
  -- Every original K class has a family, so evaluation also forces uniqueness.
  intro J hJ
  apply AddMonoidHom.ext
  intro z
  have h := hJ (a z)
  rw [ha] at h
  exact h

end AtiyahSinger
