/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolKClass

import AtiyahSinger.Topology.ModelBundleHom

/-!
# Equivariant symbol homotopies with fixed actions

Public module ID: M0590.

A jointly continuous elliptic family on the punctured cotangent bundle gives
an actual equivariant boundary homotopy with the compact zero section as one
control. The original equivariant support classes of its endpoints coincide.
Endpoint degrees may differ, and no assertion is made about values at zero.
This is the equivariant support-class version of SG III.13 (13.1), using the
original fixed-action homotopy theorem and its actual cylinder isomorphism.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [IsManifold IG ∞ G] [CompactSpace G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M] [T2Space M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E F : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (τ : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

set_option maxHeartbeats 1200000 in
-- The cylinder retains the actual original iterated pullback topologies.
/-- An equivariant continuous elliptic family preserves the original support K class. -/
theorem equivariantHomogeneousSymbolKClass_eq_of_family (m l : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F l)
    (hi : IsEllipticGlobalSymbol E F a.val) (hj : IsEllipticGlobalSymbol E F b.val)
    (heqa : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ = a.val x ξ)
    (heqb : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g b.val x ξ = b.val x ξ)
    (H : unitInterval → GlobalSymbolFunction (n := n) E F)
    (hH : IsContinuousOffZeroSymbolFamily (r := r) (q := q) H)
    (hI : ∀ t, IsEllipticGlobalSymbol E F (H t))
    (hEq : ∀ (t : unitInterval) (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g (H t) x ξ = H t x ξ)
    (h0 : ∀ x ξ, ξ ≠ 0 → H 0 x ξ = a.val x ξ)
    (h1 : ∀ x ξ, ξ ≠ 0 → H 1 x ξ = b.val x ξ) :
    equivariantHomogeneousSymbolKClass IG σ τ m a hi heqa =
      equivariantHomogeneousSymbolKClass IG σ τ l b hj heqb :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let ha := a.property.1.continuous
  let hb := b.property.1.continuous
  let p := cotangentProjection (n := n) (M := M)
  let ρE := σ.pullback p (fun _ _ ↦ rfl)
  let ρF := τ.pullback p (fun _ _ ↦ rfl)
  have haEq := ellipticSymbolTriple_isEquivariant IG σ τ a.val ha hi heqa
  have hbEq := ellipticSymbolTriple_isEquivariant IG σ τ b.val hb hj heqb
  let i : C(PuncturedCotangentBundle (n := n) (M := M),
      CotangentTotalSpace (n := n) (M := M)) := ⟨Subtype.val, continuous_subtype_val⟩
  let s : C(unitInterval × PuncturedCotangentBundle (n := n) (M := M),
      PuncturedCotangentBundle (n := n) (M := M)) := ⟨Prod.snd, continuous_snd⟩
  -- Build one invertible Hom section over the actual product of time and exterior.
  let e := modelPullbackIso (EuclideanSpace ℂ (Fin r)) (EuclideanSpace ℂ (Fin q))
    ((p.comp i).comp s) (fun z ↦ H z.1 z.2.val.proj z.2.val.snd) hH
    (fun z ↦ hI z.1 z.2.val.proj z.2.val.snd z.2.property)
  let cE := ((pullbackCompIso (E := E) p i).pullback s).trans
    (pullbackCompIso (E := E) (p.comp i) s)
  let cF := ((pullbackCompIso (E := F) p i).pullback s).trans
    (pullbackCompIso (E := F) (p.comp i) s)
  let J := cE.trans (e.trans cF.symm)
  -- The reassociations preserve vectors at every time, not merely at the endpoints.
  have hcE (t : unitInterval) (z : PuncturedCotangentBundle (n := n) (M := M))
      (v : E z.val.proj) : cE.linearEquiv (t, z) v = v := by
    change (pullbackCompIso (E := E) (p.comp i) s).linearEquiv (t, z)
      ((pullbackCompIso (E := E) p i).linearEquiv z v) = v
    exact (pullbackCompIso_apply (E := E) (p.comp i) s (t, z) _).trans
      (pullbackCompIso_apply (E := E) p i z v)
  have hcF (t : unitInterval) (z : PuncturedCotangentBundle (n := n) (M := M))
      (w : F z.val.proj) : cF.linearEquiv (t, z) w = w := by
    change (pullbackCompIso (E := F) (p.comp i) s).linearEquiv (t, z)
      ((pullbackCompIso (E := F) p i).linearEquiv z w) = w
    exact (pullbackCompIso_apply (E := F) (p.comp i) s (t, z) _).trans
      (pullbackCompIso_apply (E := F) p i z w)
  have hJ (t : unitInterval) (z : PuncturedCotangentBundle (n := n) (M := M))
      (v : E z.val.proj) : J.linearEquiv (t, z) v = H t z.val.proj z.val.snd v := by
    apply (cF.linearEquiv (t, z)).injective
    change cF.linearEquiv (t, z)
      ((cF.linearEquiv (t, z)).symm (e.linearEquiv (t, z)
        (cE.linearEquiv (t, z) v))) = _
    rw [LinearEquiv.apply_symm_apply]
    change H t z.val.proj z.val.snd (cE.linearEquiv (t, z) v) =
      cF.linearEquiv (t, z) (H t z.val.proj z.val.snd v)
    rw [hcE, hcF]
  -- One invariant zero section controls all times; equivariance uses the same family maps.
  let K := cotangentZeroSet (n := n) (M := M)
  let A := ellipticSymbolTriple a.val ha hi
  let B := ellipticSymbolTriple b.val hb hj
  have hpath : A.EquivariantlyHomotopic B ρE ρF := by
    refine ⟨{ control := K
              isCompact_control := isCompact_cotangentZeroSet
              invariant_control := haEq.invariant_control
              left_control := Set.Subset.refl _
              right_control := Set.Subset.refl _
              homotopy := { iso := J, map_zero := ?_, map_one := ?_ }
              intertwines := ?_ }⟩
    · intro z v
      refine (hJ 0 z v).trans ?_
      refine (congrArg (fun L : E z.val.proj →L[ℂ] F z.val.proj ↦ L v)
        (h0 z.val.proj z.val.snd z.property)).trans ?_
      exact ((A.enlarge_apply K isCompact_cotangentZeroSet (Set.Subset.refl _) z v).trans
        (ellipticSymbolTriple_boundary_apply a.val ha hi z v)).symm
    · intro z v
      refine (hJ 1 z v).trans ?_
      refine (congrArg (fun L : E z.val.proj →L[ℂ] F z.val.proj ↦ L v)
        (h1 z.val.proj z.val.snd z.property)).trans ?_
      exact ((B.enlarge_apply K isCompact_cotangentZeroSet (Set.Subset.refl _) z v).trans
        (ellipticSymbolTriple_boundary_apply b.val hb hj z v)).symm
    · intro t g z v
      have hslice : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) (H t) :=
        hH.slice t
      have he := ellipticSymbolTriple_isEquivariant IG σ τ (H t) hslice (hI t) (hEq t)
      let gz : PuncturedCotangentBundle (n := n) (M := M) :=
        ⟨g • z.val, fun hz ↦ z.property ((haEq.invariant_control g z.val).mp hz)⟩
      refine (hJ t gz (ρE.linearMap g z.val v)).trans ?_
      refine Eq.trans ?_ (congrArg (ρF.linearMap g z.val) (hJ t z v).symm)
      exact (ellipticSymbolTriple_boundary_apply (H t) hslice (hI t) gz _).symm.trans
        ((he.boundary_intertwines g z v).trans
          (congrArg (ρF.linearMap g z.val)
            (ellipticSymbolTriple_boundary_apply (H t) hslice (hI t) z v)))
  -- Apply the fixed-action homotopy relation before any forgetful map.
  exact equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ E))
    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ F)) ρE ρF A B haEq hbEq hpath

end AtiyahSinger
