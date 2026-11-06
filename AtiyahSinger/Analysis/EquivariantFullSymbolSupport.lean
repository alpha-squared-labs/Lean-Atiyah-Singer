/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantFullSymbolCovariance
public import AtiyahSinger.Analysis.EquivariantSymbolKClass
public import AtiyahSinger.Analysis.FullSymbolBundleHom
public import AtiyahSinger.Geometry.CotangentMetricCompact

/-!
# The original homogeneous class represented by an invariant full-symbol tail

Public module ID: M0514.

Enlarging the original zero-section control to the prescribed invariant metric
disk retains its original equivariant K class. On the new exterior the boundary
is exactly the supplied full symbol. The full symbol's fixedness also gives
an actual equivariant Hom on the original cotangent pullback bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [IsManifold IG ∞ G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M]
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

omit [CompactSpace M] in
/-- A globally fixed full symbol is a Hom for the original pulled bundle actions. -/
theorem fullSymbolBundleHom_isEquivariant {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : ∀ g : G, equivariantGlobalSymbolLinearMap IG σ τ g a.val = a.val) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    let p := cotangentProjection (n := n) (M := M)
    (fullSymbolBundleHom a).IsEquivariant
      (σ.pullback p (fun _ _ ↦ rfl)) (τ.pullback p (fun _ _ ↦ rfl)) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  have hcov := (equivariantGlobalSymbolLinearMap_eq_iff_forall IG σ τ a.val).mp
    (fun g x ξ ↦ congrArg (fun b : GlobalSymbolFunction (n := n) E F ↦ b x ξ) (ha g))
  dsimp only
  intro g z v
  exact hcov g z.proj z.snd v

variable [T2Space M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exact full-symbol tail represents the original homogeneous equivariant class. -/
theorem exists_equivariantFullSymbolSupport_of_tail (m : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hi : IsEllipticGlobalSymbol E F a.val)
    (heq : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ = a.val x ξ)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (gInv : ∀ (k : G) (x : M) (ξ : CotangentFiber (n := n) x),
      g.length (k • x) (cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ k)
          ⟨x, ξ⟩).snd = g.length x ξ)
    (R : ℝ) (hR : 0 ≤ R)
    (b : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hb : ∀ x ξ, R ≤ g.length x ξ → b.val x ξ = a.val x ξ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    let p := cotangentProjection (n := n) (M := M)
    ∃ d : CompactSupportTriple ((p : _ → M) *ᵖ E) ((p : _ → M) *ᵖ F),
      d.control = {z | g.length z.proj z.snd ≤ R} ∧
      ∃ hd : d.IsEquivariant (σ.pullback p (fun _ _ ↦ rfl))
          (τ.pullback p (fun _ _ ↦ rfl)),
        (∀ z : (d.controlᶜ : Set (CotangentTotalSpace (n := n) (M := M))),
          (d.boundary.linearEquiv z).toLinearMap = (fullSymbolBundleHom b).linearMap z.val) ∧
        (EquivariantSupportBundleTriple.ofBoundary
          (FiniteBundle.ofFamily ((p : _ → M) *ᵖ E))
          (FiniteBundle.ofFamily ((p : _ → M) *ᵖ F)) d
          (σ.pullback p (fun _ _ ↦ rfl)) (τ.pullback p (fun _ _ ↦ rfl)) hd).kZeroClass =
            equivariantHomogeneousSymbolKClass IG σ τ m a hi heq := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let p := cotangentProjection (n := n) (M := M)
  let d₀ := ellipticSymbolTriple a.val a.property.1.continuous hi
  have hd₀ := ellipticSymbolTriple_isEquivariant IG σ τ
    a.val a.property.1.continuous hi heq
  let K : Set (CotangentTotalSpace (n := n) (M := M)) :=
    {z | g.length z.proj z.snd ≤ R}
  have hK : IsCompact K := g.isCompact_sublevel R
  have hInv : ∀ (k : G) (z : CotangentTotalSpace (n := n) (M := M)),
      k • z ∈ K ↔ z ∈ K := by
    intro k z
    change g.length (k • z.proj) (k • z).snd ≤ R ↔ g.length z.proj z.snd ≤ R
    exact (congrArg (fun t : ℝ ↦ t ≤ R) (gInv k z.proj z.snd)).to_iff
  -- Only the compact control is enlarged; both original actions and bundles stay fixed.
  have hzero : d₀.control ⊆ K := by
    intro z hz
    change z.snd = 0 at hz
    change g.length z.proj z.snd ≤ R
    rw [hz]
    simpa only [SmoothCotangentMetric.length, map_zero, Real.sqrt_zero] using hR
  let d := d₀.enlarge K hK hzero
  have hd := hd₀.enlarge K hK hzero hInv
  refine ⟨d, rfl, hd, ?_, ?_⟩
  · intro z
    apply LinearMap.ext
    intro v
    have htail : b.val z.val.proj z.val.snd = a.val z.val.proj z.val.snd :=
      hb _ _ (le_of_lt (lt_of_not_ge z.property))
    exact (d₀.enlarge_apply K hK hzero z v).trans
      ((ellipticSymbolTriple_boundary_apply a.val a.property.1.continuous hi
        ⟨z.val, fun hz ↦ z.property (hzero hz)⟩ v).trans
          (congrArg (fun L : E z.val.proj →L[ℂ] F z.val.proj ↦ L v) htail.symm))
  · -- The enlargement is an original equivariant isomorphism relation, before taking classes.
    let A := EquivariantSupportBundleTriple.ofBoundary
      (FiniteBundle.ofFamily ((p : _ → M) *ᵖ E))
      (FiniteBundle.ofFamily ((p : _ → M) *ᵖ F)) d₀
      (σ.pullback p (fun _ _ ↦ rfl)) (τ.pullback p (fun _ _ ↦ rfl)) hd₀
    exact ((equivariantSupportTripleKZero_generator_relations).1 A
      (A.enlarge K hK hzero hInv)
      ((EquivariantSupportBundleTriple.isIsomorphic_sum_enlarge).2
        A K hK hzero hInv)).symm

end AtiyahSinger
