/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereSymbol
public import AtiyahSinger.Analysis.EquivariantPrincipalSymbol
public import AtiyahSinger.Geometry.EquivariantCotangentAction
public import AtiyahSinger.Topology.EquivariantBundlePullback

/-!
# Conjugation and the actual equivariant cotangent fiber square

Public module ID: M0587.

The original inverse-cotangent conjugation fixes a symbol exactly when its
forward cotangent fiber maps intertwine the original bundle actions. The
comparison keeps every dependent base transport. No homogeneity, ellipticity,
compactness, or smoothness of the symbol is needed. This is the geometric
covariance used in SG III.9 and in equivariant radial reconstruction.
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
theorem equivariantGlobalSymbolLinearMap_eq_iff
    (a : GlobalSymbolFunction (n := n) E F) :
    (∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g a x ξ = a x ξ) ↔
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → ∀ v : E x,
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
  · intro heq g x ξ hξ v
    let w : W := ⟨⟨x, ξ⟩, v⟩
    have hfixed := congrArg (fun L : E x →L[ℂ] F x ↦
      (⟨x, L v⟩ : TotalSpace Unit F)) (heq g⁻¹ x ξ hξ)
    have h := congrArg (fun z : TotalSpace Unit F ↦ g • z)
      ((hconj g⁻¹ w).symm.trans hfixed)
    have hintertwine : T (g • w) = g • T w := by
      simpa only [inv_inv, smul_inv_smul] using h
    exact TotalSpace.mk_injective (g • x) hintertwine
  · intro hcov g x ξ hξ
    apply ContinuousLinearMap.ext
    intro v
    let w : W := ⟨⟨x, ξ⟩, v⟩
    have hforward : T (g⁻¹ • w) = g⁻¹ • T w := by
      change (⟨g⁻¹ • x, a (g⁻¹ • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g⁻¹)
            ⟨x, ξ⟩).snd (σ.linearMap g⁻¹ x v)⟩ : TotalSpace Unit F) =
          ⟨g⁻¹ • x, τ.linearMap g⁻¹ x (a x ξ v)⟩
      exact congrArg (TotalSpace.mk (g⁻¹ • x)) (hcov g⁻¹ x ξ hξ v)
    apply TotalSpace.mk_injective x
    exact (hconj g w).trans (by rw [hforward, smul_inv_smul])

/-- An invariant metric makes restriction followed by homogeneous radial extension equivariant. -/
theorem equivariant_cosphereExtension_restriction
    (h : SmoothCotangentMetric (n := n) (M := M))
    (hInv : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      h.length (g • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
            ⟨x, ξ⟩).snd = h.length x ξ)
    (m : ℝ) (a : GlobalSymbolFunction (n := n) E F)
    (ha : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g a x ξ = a x ξ) :
    ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g
        (cosphereExtension h m (cosphereRestriction h a)) x ξ =
          cosphereExtension h m (cosphereRestriction h a) x ξ := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  have hcov := (equivariantGlobalSymbolLinearMap_eq_iff IG σ τ a).mp ha
  apply (equivariantGlobalSymbolLinearMap_eq_iff IG σ τ _).mpr
  intro g x ξ hξ v
  let D := Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g
  have hgne : (cotangentDiffeomorphMap D ⟨x, ξ⟩).snd ≠ 0 := by
    intro hz
    exact (h.length_pos x ξ hξ).ne' ((hInv g x ξ).symm.trans
      ((h.length_eq_zero_iff _ _).mpr hz))
  have hnorm : h.normalize (g • x) (cotangentDiffeomorphMap D ⟨x, ξ⟩).snd =
      (cotangentDiffeomorphMap D ⟨x, h.normalize x ξ⟩).snd := by
    simp only [SmoothCotangentMetric.normalize]
    rw [show h.length (g • x) (cotangentDiffeomorphMap D ⟨x, ξ⟩).snd =
      h.length x ξ from hInv g x ξ]
    rfl
  -- The same positive radial factor and normalized covector are preserved by the action.
  rw [cosphereExtension_of_ne_zero h m _ (g • x) _ hgne,
    cosphereExtension_of_ne_zero h m _ x ξ hξ]
  change ((h.length (g • x) (cotangentDiffeomorphMap D ⟨x, ξ⟩).snd ^ m : ℝ) : ℂ) •
      a (g • x) (h.normalize (g • x) (cotangentDiffeomorphMap D ⟨x, ξ⟩).snd)
        (σ.linearMap g x v) =
    τ.linearMap g x (((h.length x ξ ^ m : ℝ) : ℂ) • a x (h.normalize x ξ) v)
  rw [hInv g x ξ, hnorm, map_smul]
  exact congrArg (fun w : F (g • x) ↦ ((h.length x ξ ^ m : ℝ) : ℂ) • w)
    (hcov g x (h.normalize x ξ) (h.normalize_ne_zero x ξ hξ) v)

end AtiyahSinger
