/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ExternalTensorH1Density

/-!
# Separated coordinate functions are dense in the original first Sobolev graph

Public module ID: M0607.

Compactly supported scalar functions are reconstructed with a product of two
plateau cutoffs. Every modulation of that cutoff is separated in the original
product coordinates. Fourier reconstruction therefore places each compact test
in the closed H1 span of separated functions. Schwartz density and the finite
coordinate basis give the full vector-valued result.

The coordinate splitting is the same Euclidean concatenation used by the
geometric exterior bundle. No uniform-norm density is substituted for H1 density.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false

variable (n m r : ℕ)

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin m)
local notation "Z" => EuclideanSpace ℝ (Fin (n + m))
local notation "V" => EuclideanSpace ℂ (Fin r)

/-- Finite sums of separated scalar coordinate functions times vectors are dense in H1. -/
theorem dense_span_schwartz_products_h1Graph :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    Dense (Submodule.span ℂ ((schwartzToH1Graph (n + m) r) ''
      {u : 𝓢(Z, V) | ∃ a : 𝓢(X, ℂ), ∃ b : 𝓢(Y, ℂ), ∃ v : V,
        ∀ z : Z, u z = (a (e z).1 * b (e z).2) • v}) :
          Set (EuclideanH1Graph (n + m) r)) := by
  classical
  have hcast : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let S := Submodule.span ℂ ((schwartzToH1Graph (n + m) r) ''
    {u : 𝓢(Z, V) | ∃ a : 𝓢(X, ℂ), ∃ b : 𝓢(Y, ℂ), ∃ v : V,
      ∀ z : Z, u z = (a (e z).1 * b (e z).2) • v})
  let C := S.topologicalClosure
  have hgraph : Continuous (schwartzToH1Graph (n + m) r) := by
    have hcoord (a : Option (Fin (n + m))) :
        Continuous (fun u : 𝓢(Z, V) ↦ (schwartzH1Jet (n + m) r u).ofLp a) := by
      cases a with
      | none => exact (SchwartzMap.toLpCLM ℂ V 2 volume).continuous
      | some a =>
        exact (((SchwartzMap.toLpCLM ℂ V 2 volume).comp
          (LineDeriv.lineDerivOpCLM ℂ 𝓢(Z, V)
            (EuclideanSpace.single a (1 : ℝ)))).continuous).const_smul
              ((2 * Real.pi)⁻¹ : ℂ)
    exact ((PiLp.continuous_toLp 2 _).comp (continuous_pi hcoord)).subtype_mk _
  let lift (v : V) : 𝓢(Z, ℂ) →L[ℂ] 𝓢(Z, V) :=
    SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight v)
  have hlift (v : V) (f : 𝓢(Z, ℂ)) (z : Z) : lift v f z = f z • v := rfl
  have hproj (j : Fin r) (v : V) : (EuclideanSpace.proj (𝕜 := ℂ) j) v = v j := rfl
  -- Compact tests admit product plateau cutoffs, whose plane waves remain separated.
  have hcompact (f : 𝓢(Z, ℂ)) (hf : HasCompactSupport f) (v : V) :
      schwartzToH1Graph (n + m) r (lift v f) ∈ C := by
    obtain ⟨R, hR, hKR⟩ :=
      ((hf.image e.continuous).image continuous_fst).isBounded.subset_closedBall_lt 0 (0 : X)
    obtain ⟨T, hT, hKT⟩ :=
      ((hf.image e.continuous).image continuous_snd).isBounded.subset_closedBall_lt 0 (0 : Y)
    let a : ContDiffBump (0 : X) :=
      { rIn := R, rOut := R + 1, rIn_pos := hR, rIn_lt_rOut := by linarith }
    let b : ContDiffBump (0 : Y) :=
      { rIn := T, rOut := T + 1, rIn_pos := hT, rIn_lt_rOut := by linarith }
    have haSmooth : ContDiff ℝ ∞ a := a.contDiff
    have hbSmooth : ContDiff ℝ ∞ b := b.contDiff
    let c : Z → ℂ := fun z ↦ (a (e z).1 : ℂ) * (b (e z).2 : ℂ)
    have hc : ContDiff ℝ ∞ c := by dsimp [c]; fun_prop
    have hcK : HasCompactSupport c := by
      have hK := (a.hasCompactSupport.prod b.hasCompactSupport).image e.symm.continuous
      apply hK.of_isClosed_subset (isClosed_tsupport c)
      apply closure_minimal ?_ hK.isClosed
      intro z hz
      refine ⟨e z, ⟨?_, ?_⟩, e.symm_apply_apply z⟩
      · apply subset_tsupport
        intro ha
        exact hz (by simp [c, ha])
      · apply subset_tsupport
        intro hb
        exact hz (by simp [c, hb])
    let u : 𝓢(Z, V) := (hcK.smul_right (f' := fun _ ↦ v)).toSchwartzMap
      (hc.smul contDiff_const)
    have hu (z : Z) : u z = c z • v := rfl
    have hplateau (z : Z) (hz : z ∈ tsupport f) : c z = 1 := by
      have ha : a (e z).1 = 1 := a.one_of_mem_closedBall (hKR ⟨e z, ⟨z, hz, rfl⟩, rfl⟩)
      have hb : b (e z).2 = 1 := b.one_of_mem_closedBall (hKT ⟨e z, ⟨z, hz, rfl⟩, rfl⟩)
      simp [c, ha, hb]
    have hproduct : SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) f u = lift v f := by
      apply SchwartzMap.ext
      intro z
      change f z • (c z • v) = f z • v
      by_cases hz : f z = 0
      · simp [hz]
      · rw [hplateau z (subset_tsupport f hz), one_smul]
    have horbit (ξ : Z) : schwartzToH1Graph (n + m) r (schwartzModulation ξ u) ∈ S := by
      have hinner : ContDiff ℝ ∞ (fun z : Z ↦ inner ℝ ξ z) := (innerSL ℝ ξ).contDiff
      let ax : X → ℂ := fun x ↦
        (Real.fourierChar (inner ℝ ξ (e.symm (x, 0))) : ℂ) * (a x : ℂ)
      let byFun : Y → ℂ := fun y ↦
        (Real.fourierChar (inner ℝ ξ (e.symm (0, y))) : ℂ) * (b y : ℂ)
      have hax : ContDiff ℝ ∞ ax := by
        simp only [ax, Real.fourierChar_apply]
        fun_prop
      have hby : ContDiff ℝ ∞ byFun := by
        simp only [byFun, Real.fourierChar_apply]
        fun_prop
      have hcax : HasCompactSupport ax :=
        (a.hasCompactSupport.comp_left (g := Complex.ofReal) rfl).mul_left
      have hcby : HasCompactSupport byFun :=
        (b.hasCompactSupport.comp_left (g := Complex.ofReal) rfl).mul_left
      refine Submodule.subset_span ⟨schwartzModulation ξ u,
        ⟨hcax.toSchwartzMap hax, hcby.toSchwartzMap hby, v, ?_⟩, rfl⟩
      intro z
      have hsplit : inner ℝ ξ z = inner ℝ ξ (e.symm ((e z).1, 0)) +
          inner ℝ ξ (e.symm (0, (e z).2)) := by
        rw [← inner_add_right, ← map_add]
        simp
      rw [schwartzModulation_apply, hu, hsplit, AddChar.map_add_eq_mul]
      change ((Real.fourierChar (inner ℝ ξ (e.symm ((e z).1, 0))) : ℂ) *
        (Real.fourierChar (inner ℝ ξ (e.symm (0, (e z).2))) : ℂ)) • (c z • v) =
          (ax (e z).1 * byFun (e z).2) • v
      rw [smul_smul]
      congr 1
      dsimp [ax, byFun, c]
      ring
    have hle : (Submodule.span ℂ (Set.range fun ξ : Z ↦
        schwartzToH1Graph (n + m) r (schwartzModulation ξ u))).topologicalClosure ≤ C :=
      Submodule.topologicalClosure_mono (Submodule.span_le.mpr (by
        rintro _ ⟨ξ, rfl⟩
        exact horbit ξ))
    have hmem := hle (schwartzToH1Graph_pairing_mem_closure_span_modulation f u)
    rwa [hproduct] at hmem
  -- Compact scalar tests are dense in Schwartz topology, which maps continuously into H1.
  have hscalar (v : V) (f : 𝓢(Z, ℂ)) :
      schwartzToH1Graph (n + m) r (lift v f) ∈ C := by
    apply (dense_hasCompactSupport_schwartz (n + m)).induction
      (P := fun f : 𝓢(Z, ℂ) ↦ schwartzToH1Graph (n + m) r (lift v f) ∈ C)
      (fun f hf ↦ hcompact f hf v)
      (S.isClosed_topologicalClosure.preimage (hgraph.comp (lift v).continuous)) f
  -- The finite coordinate basis reduces every vector-valued Schwartz function to scalar tests.
  have hall (u : 𝓢(Z, V)) : schwartzToH1Graph (n + m) r u ∈ C := by
    let f (j : Fin r) : 𝓢(Z, ℂ) :=
      SchwartzMap.postcompCLM (EuclideanSpace.proj (𝕜 := ℂ) j) u
    have hsum : u = ∑ j : Fin r, lift (EuclideanSpace.single j 1) (f j) := by
      apply SchwartzMap.ext
      intro z
      simp only [sum_apply, hlift]
      symm
      simpa only [f, SchwartzMap.postcompCLM_apply, hproj,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.sum_repr (u z)
    rw [hsum, map_sum]
    exact Submodule.sum_mem C (fun j _ ↦ hscalar _ _)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro u _
  refine (denseRange_schwartzToH1Graph (n + m) r).induction ?_
    S.isClosed_topologicalClosure u
  rintro _ ⟨v, rfl⟩
  exact hall v

end AtiyahSinger
