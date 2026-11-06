/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMapContinuity
public import AtiyahSinger.Geometry.SmoothBundleMapPullback
public import AtiyahSinger.Geometry.SmoothFiniteRepresentationBundle

/-!
# Exterior frames from the original finite-representation source

Public module ID: M1194.

The native trivial source has its identity frame. Composing the inverse of
the actual exterior multiplier with that frame gives the target frame.
Both smoothness and equivariance follow from those same specified maps;
the finite representation is retained, including its actual action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G M] [ContinuousSMul G M]

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A native representation source determines compatible smooth equivariant exterior frames. -/
theorem exists_equivariant_native_exterior_frames
    (ρ : FiniteContinuousRepresentation G)
    (hT : IsSmoothComplexBundle (n := n) (r := ρ.dimension)
      (Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))))
    (F : SmoothFiniteComplexBundle (n := n) M) :
    letI := hT
    let T := Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))
    letI := modelTopology (EuclideanSpace ℂ (Fin ρ.dimension)) T
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ (σT : EquivariantStructure G T) (σF : EquivariantStructure G F.Fiber)
      (_hσTvalue : ∀ (g : G) (x : M) (v : T x), σT.linearMap g x v =
        (EuclideanSpace.equiv (Fin ρ.dimension) ℂ).symm
          (ρ.representation g ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) v)))
      (K : Set M) (_hK : IsClosed K)
      (hKi : ∀ (g : G) (x : M), g • x ∈ K ↔ x ∈ K)
      (c : Hom T F.Fiber)
      (_hc : IsSmoothBundleMap (n := n) (r := ρ.dimension) (q := F.rank) c.linearMap)
      (_hcg : c.IsEquivariant σT σF)
      (_hcbij : ∀ x ∉ K, Function.Bijective (c.linearMap x)),
      let W : Opens M := ⟨Kᶜ, _hK.isOpen_compl⟩
      ∃ (τT : ∀ x : W, T x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin ρ.dimension))
        (τF : ∀ x : W, F.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin ρ.dimension)),
        IsSmoothBundleMap (n := n) (r := ρ.dimension) (q := ρ.dimension) (M := W)
          (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ T))
          (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin ρ.dimension)))
          (fun x ↦ (τT x).toLinearMap) ∧
        IsSmoothBundleMap (n := n) (r := F.rank) (q := ρ.dimension) (M := W)
          (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ F.Fiber))
          (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin ρ.dimension)))
          (fun x ↦ (τF x).toLinearMap) ∧
        (∀ (x : W) (v : T x.val), τF x (c.linearMap x.val v) = τT x v) ∧
        (∀ (g : G) (x : W) (v : T x.val),
          τT ⟨g • x.val, (hKi g x.val).not.mpr x.property⟩ (σT.linearMap g x.val v) =
            (EuclideanSpace.equiv (Fin ρ.dimension) ℂ).symm
              (ρ.representation g ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) (τT x v)))) ∧
        ∀ (g : G) (x : W) (v : F.Fiber x.val),
          τF ⟨g • x.val, (hKi g x.val).not.mpr x.property⟩ (σF.linearMap g x.val v) =
            (EuclideanSpace.equiv (Fin ρ.dimension) ℂ).symm
              (ρ.representation g ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) (τF x v))) := by
  classical
  dsimp only
  let := hT
  let T := Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))
  let := modelTopology (EuclideanSpace ℂ (Fin ρ.dimension)) T
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  intro σT σF hσTvalue K hK hKi c hc hcg hcbij
  let W : Opens M := ⟨Kᶜ, hK.isOpen_compl⟩
  let i : C(W, M) := ContinuousMap.subtypeVal (W : Set M)
  let : IsSmoothComplexBundle (n := n) (r := ρ.dimension) ((i : W → M) *ᵖ T) :=
    isSmoothComplexBundle_pullback T i contMDiff_subtype_val
  let : IsSmoothComplexBundle (n := n) (r := F.rank) ((i : W → M) *ᵖ F.Fiber) :=
    isSmoothComplexBundle_pullback F.Fiber i contMDiff_subtype_val
  let : IsSmoothComplexBundle (n := n) (r := ρ.dimension)
      (Bundle.Trivial W (EuclideanSpace ℂ (Fin ρ.dimension))) := by
    constructor
    intro a b ha hb
    obtain rfl := Bundle.Trivial.eq_trivialization W (EuclideanSpace ℂ (Fin ρ.dimension)) a
    obtain rfl := Bundle.Trivial.eq_trivialization W (EuclideanSpace ℂ (Fin ρ.dimension)) b
    simp only [Bundle.Trivial.trivialization.coordChangeL]
    exact contMDiffOn_const
  let τT (x : W) : T x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin ρ.dimension) :=
    LinearEquiv.refl ℂ _
  let e (x : W) : T x.val ≃ₗ[ℂ] F.Fiber x.val :=
    LinearEquiv.ofBijective (c.linearMap x.val) (hcbij x.val x.property)
  let τF (x : W) : F.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin ρ.dimension) :=
    (e x).symm.trans (τT x)
  -- The native identity frame remains smooth after restricting its original trivial atlas.
  have hτT : IsSmoothBundleMap (n := n) (r := ρ.dimension) (q := ρ.dimension)
      (E := (i : W → M) *ᵖ T)
      (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin ρ.dimension)))
      (fun x ↦ (τT x).toLinearMap) := by
    rintro _ ⟨a, ha, rfl⟩ b hb j
    obtain rfl := Bundle.Trivial.eq_trivialization M (EuclideanSpace ℂ (Fin ρ.dimension)) a
    obtain rfl := Bundle.Trivial.eq_trivialization W (EuclideanSpace ℂ (Fin ρ.dimension)) b
    apply (contMDiffOn_const (c := EuclideanSpace.single j (1 : ℂ))).congr
    intro x hx
    let t := Bundle.Trivial.trivialization M (EuclideanSpace ℂ (Fin ρ.dimension))
    change (t.pullback i).symmL ℂ x (EuclideanSpace.single j 1) =
      EuclideanSpace.single j 1
    rw [(t.pullback i).symmL_apply hx.1]
    change (t.pullback i).symm x (EuclideanSpace.single j 1) = EuclideanSpace.single j 1
    rw [(t.pullback i).symm_apply hx.1]
    simp [t, Trivialization.pullback, Bundle.Trivial.trivialization_symm_apply]
  have he : IsSmoothBundleMap (n := n) (r := ρ.dimension) (q := F.rank)
      (E := (i : W → M) *ᵖ T) (F := (i : W → M) *ᵖ F.Fiber)
      (fun x ↦ (e x).toLinearMap) := hc.pullback i contMDiff_subtype_val
  have hinv := IsSmoothBundleMap.symm (E := (i : W → M) *ᵖ T)
    (F := (i : W → M) *ᵖ F.Fiber) e he
  have hτF : IsSmoothBundleMap (n := n) (r := F.rank) (q := ρ.dimension)
      (E := (i : W → M) *ᵖ F.Fiber)
      (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin ρ.dimension)))
      (fun x ↦ (τF x).toLinearMap) :=
    IsSmoothBundleMap.comp (E := (i : W → M) *ᵖ F.Fiber)
      (F := (i : W → M) *ᵖ T)
      (H := Bundle.Trivial W (EuclideanSpace ℂ (Fin ρ.dimension))) hτT hinv
  refine ⟨τT, τF, hτT, hτF, ?_, ?_, ?_⟩
  · intro x v
    exact (e x).symm_apply_apply v
  · intro g x v
    exact hσTvalue g x.val v
  · -- Invert the same multiplier intertwining square, preserving the actual representation.
    intro g x v
    let gx : W := ⟨g • x.val, (hKi g x.val).not.mpr x.property⟩
    have hi : (e gx).symm (σF.linearMap g x.val v) =
        σT.linearMap g x.val ((e x).symm v) := by
      apply (e gx).injective
      rw [LinearEquiv.apply_symm_apply]
      change σF.linearMap g x.val v = c.linearMap (g • x.val)
        (σT.linearMap g x.val ((e x).symm v))
      rw [hcg]
      exact congrArg (σF.linearMap g x.val) ((e x).apply_symm_apply v).symm
    change (e gx).symm (σF.linearMap g x.val v) = _
    rw [hi]
    exact hσTvalue g x.val ((e x).symm v)

end AtiyahSinger
