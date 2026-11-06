/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricSymbol
public import AtiyahSinger.Analysis.EquivariantPrincipalSymbol
public import AtiyahSinger.Geometry.EquivariantCotangentAction
public import AtiyahSinger.Geometry.EquivariantHermitianAdjoint
public import AtiyahSinger.Topology.EquivariantBundlePullback

/-!
# Full-symbol covariance and metric adjunction

Public module ID: M0512.

The conjugation fixed-point condition on every frequency is equivalent to
the actual moving-fiber square. Invariant Hermitian metrics preserve that
square under adjunction. These statements include the zero section and
therefore apply to the globally smooth full symbols used in product cutoffs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [IsManifold IG ∞ G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E F : M → Type*}
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

/-- The original conjugation fixed-point condition is the actual moving-fiber square. -/
theorem equivariantGlobalSymbolLinearMap_eq_iff_forall
    (a : GlobalSymbolFunction (n := n) E F) :
    (∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      equivariantGlobalSymbolLinearMap IG σ τ g a x ξ = a x ξ) ↔
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ∀ v : E x,
      a (g • x)
          (cotangentDiffeomorphMap
            (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
              ⟨x, ξ⟩).snd (σ.linearMap g x v) = τ.linearMap g x (a x ξ v) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let p := cotangentProjection (n := n) (M := M)
  let W := TotalSpace Unit ((p : _ → M) *ᵖ E)
  let : MulAction G W := (σ.pullback p (fun _ _ ↦ rfl)).toMulAction
  let : MulAction G (TotalSpace Unit F) := τ.toMulAction
  let T : W → TotalSpace Unit F :=
    fun w ↦ ⟨w.proj.proj, a w.proj.proj w.proj.snd w.snd⟩
  -- The conjugation formula is equality in the original target total space.
  let transport : ∀ {x y : M}, x = y → F x →L[ℂ] F y := fun {x y} h ↦ by
    subst y
    exact ContinuousLinearMap.id ℂ (F x)
  have htransport {x y : M} (h : x = y) (v : F x) :
      (⟨y, transport h v⟩ : TotalSpace Unit F) = ⟨x, v⟩ := by
    subst y
    rfl
  have hconj (g : G) (w : W) :
      (⟨w.proj.proj,
        equivariantGlobalSymbolLinearMap IG σ τ g a w.proj.proj w.proj.snd w.snd⟩ :
          TotalSpace Unit F) = g • T (g⁻¹ • w) := by
    change (⟨w.proj.proj,
      transport (smul_inv_smul g w.proj.proj)
      (τ.linearMap g (g⁻¹ • w.proj.proj)
        (a (g⁻¹ • w.proj.proj)
          ((cotangentDiffeomorphMap
            (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm)
              w.proj).snd (σ.linearMap g⁻¹ w.proj.proj w.snd)))⟩ :
        TotalSpace Unit F) = _
    rw [htransport]
    erw [Diffeomorph.smul_symm]
    rfl
  constructor
  · intro heq g x ξ v
    let w : W := ⟨⟨x, ξ⟩, v⟩
    have hfixed := congrArg (fun L : E x →L[ℂ] F x ↦
      (⟨x, L v⟩ : TotalSpace Unit F)) (heq g⁻¹ x ξ)
    have h := congrArg (fun z : TotalSpace Unit F ↦ g • z)
      ((hconj g⁻¹ w).symm.trans hfixed)
    have hintertwine : T (g • w) = g • T w := by
      simpa only [inv_inv, smul_inv_smul] using h
    exact TotalSpace.mk_injective (g • x) hintertwine
  · intro hcov g x ξ
    apply ContinuousLinearMap.ext
    intro v
    let w : W := ⟨⟨x, ξ⟩, v⟩
    have hforward : T (g⁻¹ • w) = g⁻¹ • T w := by
      change (⟨g⁻¹ • x, a (g⁻¹ • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g⁻¹)
            ⟨x, ξ⟩).snd (σ.linearMap g⁻¹ x v)⟩ : TotalSpace Unit F) =
          ⟨g⁻¹ • x, τ.linearMap g⁻¹ x (a x ξ v)⟩
      exact congrArg (TotalSpace.mk (g⁻¹ • x)) (hcov g⁻¹ x ξ v)
    apply TotalSpace.mk_injective x
    exact (hconj g w).trans (by rw [hforward, smul_inv_smul])

/-- Full-symbol fixedness is preserved by the same invariant Hermitian adjoint. -/
theorem SmoothHermitianMetric.symbolAdjoint_fixed
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (hInv : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ (g : G) (x : M) (u v : E x),
        h.pairing (g • x) (σ.linearMap g x u) (σ.linearMap g x v) = h.pairing x u v)
    (kInv : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ (g : G) (x : M) (u v : F x),
        k.pairing (g • x) (τ.linearMap g x u) (τ.linearMap g x v) = k.pairing x u v)
    (a : GlobalSymbolFunction (n := n) E F)
    (ha : ∀ g : G, equivariantGlobalSymbolLinearMap IG σ τ g a = a) :
    ∀ g : G, equivariantGlobalSymbolLinearMap IG τ σ g (h.symbolAdjoint k a) =
      h.symbolAdjoint k a := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  have hcov := (equivariantGlobalSymbolLinearMap_eq_iff_forall IG σ τ a).mp
    (fun g x ξ ↦ congrArg (fun b : GlobalSymbolFunction (n := n) E F ↦ b x ξ) (ha g))
  have hadj := (equivariantGlobalSymbolLinearMap_eq_iff_forall IG τ σ
    (h.symbolAdjoint k a)).mpr (fun g x ξ v ↦
      h.adjoint_intertwines k σ τ g x (hInv g x) (kInv g x) _ _ (hcov g x ξ) v)
  intro g
  funext x ξ
  exact hadj g x ξ

end AtiyahSinger
