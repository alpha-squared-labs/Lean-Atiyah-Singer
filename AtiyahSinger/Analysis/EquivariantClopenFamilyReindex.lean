/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantClopenSymbolFamily

/-!
# Reindexing a finite family of original equivariant symbols

Public module ID: M0479.

Equal open pieces carry the same specified subtype action because both agree
with the original ambient action. Transport these equal data and permute the
same finite family. Coordinate restriction identifies the reconstructed K
class, and reindexing the finite sum preserves the full index value.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Reindex the same original symbol family along equal actual pieces and their equal actions. -/
theorem EquivariantClopenSymbolFamily.exists_reindex
    (a : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G))
    (Q : EquivariantClopenPartition (G := G) (M := M))
    (e : Fin Q.size ≃ Fin a.partition.size)
    (hpieces : ∀ i, Q.piece i = a.partition.piece (e i)) :
    ∃ b : Q.Symbols (n := n) (VG := VG),
      (EquivariantClopenSymbolFamily.mk Q b).kClass = a.kClass ∧
      (EquivariantClopenSymbolFamily.mk Q b).index = a.index := by
  classical
  rcases a with ⟨P, symbols⟩
  rcases P with ⟨p, U, hclosed, hdisjoint, hcover, hinvariant, actions, heq⟩
  rcases Q with ⟨q, V, hclosed', hdisjoint', hcover', hinvariant', actions', heq'⟩
  have hsize : q = p := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst q
  change Fin p ≃ Fin p at e
  change ∀ i, V i = U (e i) at hpieces
  have hV : V = fun i ↦ U (e i) := funext hpieces
  subst V
  -- Equality of the underlying subtype actions follows from their common ambient action.
  have hactions : actions' = fun i ↦ actions (e i) := by
    funext i
    apply MulAction.ext
    funext g x
    exact Subtype.ext ((heq' i g x).trans (heq (e i) g x).symm)
  subst actions'
  let P : EquivariantClopenPartition (G := G) (M := M) :=
    ⟨p, U, hclosed, hdisjoint, hcover, hinvariant, actions, heq⟩
  let Q : EquivariantClopenPartition (G := G) (M := M) :=
    ⟨p, fun i ↦ U (e i), hclosed', hdisjoint', hcover', hinvariant',
      fun i ↦ actions (e i), heq'⟩
  let := P.mulAction
  let := P.continuousSMul
  let := P.contMDiffSMul (VG := VG) (n := n)
  let := P.compactSpace
  let b : Q.Symbols (n := n) (VG := VG) := fun i ↦ symbols (e i)
  refine ⟨b, ?_, ?_⟩
  · let := Q.mulAction
    let := Q.continuousSMul
    let := Q.contMDiffSMul (VG := VG) (n := n)
    let := Q.compactSpace
    let Φ := equivariantCotangentClopenEquiv (n := n) 𝓘(ℝ, VG) P.piece P.isClosed
      P.equivariant P.disjoint P.cover
    let Ψ := equivariantCotangentClopenEquiv (n := n) 𝓘(ℝ, VG) Q.piece Q.isClosed
      Q.equivariant Q.disjoint Q.cover
    apply Ψ.injective
    change Ψ (Ψ.symm (fun i ↦ (b i).kClass)) =
      Ψ (Φ.symm (fun i ↦ (symbols i).kClass))
    rw [Ψ.apply_symm_apply]
    funext i
    have h := congrFun (Φ.apply_symm_apply (fun j ↦ (symbols j).kClass)) (e i)
    exact h.symm
  · change (∑ i, (symbols (e i)).index) = ∑ i, (symbols i).index
    exact Equiv.sum_comp e (fun i ↦ (symbols i).index)

end AtiyahSinger
