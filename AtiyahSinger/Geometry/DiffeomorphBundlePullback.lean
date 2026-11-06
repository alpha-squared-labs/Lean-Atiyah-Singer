/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Geometry.SmoothSectionPullback
public import AtiyahSinger.Geometry.SmoothBundleMaps

/-!
# Native bundle pullback for a specified diffeomorphism

Public module ID: M1162.

Smooth pullback retains the original fibers, fiber norms and native pullback
atlas. Pulling back along the inverse of a diffeomorphism gives the canonical
fiber identification over its original point map. Its smoothness is checked
in these same native charts. These are the bundle comparisons used to transport
actual elliptic representatives, without choosing a substitute source atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]

/-- Smooth pullback in the small native bundle model, with every original fiber norm. -/
def SmoothFiniteComplexBundle.pullback (E : SmoothFiniteComplexBundle (n := n) M)
    (f : C(N, M))
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f) :
    SmoothFiniteComplexBundle (n := m) N where
  rank := E.rank
  Fiber := (f : N → M) *ᵖ E.Fiber
  isSmooth := isSmoothComplexBundle_pullback E.Fiber f hf

/-- The specified diffeomorphism on the full open subspaces keeps the original point maps. -/
def diffeomorphTop
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N) :
    (⊤ : Opens M) ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ (⊤ : Opens N) where
  toFun x := ⟨e x.val, Set.mem_univ _⟩
  invFun y := ⟨e.symm y.val, Set.mem_univ _⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    (e.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    (e.symm.contMDiff.comp contMDiff_subtype_val)

/-- The canonical inverse-pullback fiber comparison is smooth in the actual top-open atlases. -/
theorem isSmoothBundleMap_diffeomorphPullback_top
    (E : SmoothFiniteComplexBundle (n := n) M)
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N) :
    let G := E.pullback ⟨e.symm, e.symm.continuous⟩ e.symm.contMDiff
    IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank) (M := (⊤ : Opens M))
      (E := (ContinuousMap.subtypeVal ((⊤ : Opens M) : Set M) : (⊤ : Opens M) → M) *ᵖ E.Fiber)
      (F := ((⟨diffeomorphTop e, (diffeomorphTop e).continuous⟩ :
          C((⊤ : Opens M), (⊤ : Opens N))) : (⊤ : Opens M) → (⊤ : Opens N)) *ᵖ
        ((ContinuousMap.subtypeVal ((⊤ : Opens N) : Set N) : (⊤ : Opens N) → N) *ᵖ G.Fiber))
      (fun x ↦ (LinearEquiv.cast (R := ℂ) (M := E.Fiber)
        (e.symm_apply_apply x.val).symm).toLinearMap) := by
  dsimp only
  -- The three target pullback frames descend to one frame of the original E bundle.
  rintro _ ⟨a, ha, rfl⟩ _ ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩ j
  let := ha
  let := hb
  have hcolumn := ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin E.rank))
    (EuclideanSpace.single j (1 : ℂ))).restrictScalars ℝ).contMDiff.comp_contMDiffOn
      (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) (E := E.Fiber) a b)
  have hs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin E.rank)) ∞
      (fun x : (⊤ : Opens M) ↦ (a.coordChangeL ℂ b x.val) (EuclideanSpace.single j 1))
      {x | x.val ∈ a.baseSet ∧ e.symm (e x.val) ∈ b.baseSet} := by
    exact hcolumn.comp (contMDiff_subtype_val (U := (⊤ : Opens M))).contMDiffOn
      (fun x hx ↦ by
        change x.val ∈ a.baseSet ∧ e.symm (e x.val) ∈ b.baseSet at hx
        change x.val ∈ a.baseSet ∧ x.val ∈ b.baseSet
        simpa only [Diffeomorph.symm_apply_apply] using hx)
  apply hs.congr
  intro x hx
  have hframe : (a.pullback (ContinuousMap.subtypeVal ((⊤ : Opens M) : Set M))).symmL
      ℂ x (EuclideanSpace.single j 1) = a.symmL ℂ x.val (EuclideanSpace.single j 1) := by
    rw [(a.pullback (ContinuousMap.subtypeVal ((⊤ : Opens M) : Set M))).symmL_apply hx.1,
      a.symmL_apply hx.1,
      (a.pullback (ContinuousMap.subtypeVal ((⊤ : Opens M) : Set M))).symm_apply hx.1]
    rfl
  change (b ⟨e.symm (e x.val),
    (LinearEquiv.cast (R := ℂ) (M := E.Fiber) (e.symm_apply_apply x.val).symm)
      ((a.pullback (ContinuousMap.subtypeVal ((⊤ : Opens M) : Set M))).symmL
        ℂ x (EuclideanSpace.single j 1))⟩).2 = _
  rw [hframe]
  change (b ⟨e.symm (e x.val),
    cast (congrArg E.Fiber (e.symm_apply_apply x.val).symm)
      (a.symmL ℂ x.val (EuclideanSpace.single j 1))⟩).2 =
    (a.coordChangeL ℂ b x.val) (EuclideanSpace.single j 1)
  rw [show (⟨e.symm (e x.val),
      cast (congrArg E.Fiber (e.symm_apply_apply x.val).symm)
        (a.symmL ℂ x.val (EuclideanSpace.single j 1))⟩ :
        TotalSpace (EuclideanSpace ℂ (Fin E.rank)) E.Fiber) =
      ⟨x.val, a.symmL ℂ x.val (EuclideanSpace.single j 1)⟩ from
    TotalSpace.mk_cast (F := EuclideanSpace ℂ (Fin E.rank))
      (E := E.Fiber) (e.symm_apply_apply x.val).symm _]
  have hxb : x.val ∈ b.baseSet := by
    simpa only [Trivialization.pullback_baseSet, Set.mem_preimage,
      Diffeomorph.symm_apply_apply] using hx.2
  rw [a.symmL_apply hx.1]
  exact (a.coordChangeL_apply b ⟨hx.1, hxb⟩ _).symm

end AtiyahSinger
