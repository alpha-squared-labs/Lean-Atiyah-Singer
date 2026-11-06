/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleHomotopyType
public import AtiyahSinger.Topology.RelativeTriple

/-!
# Cylinder endpoint isomorphisms preserving a specified external trivialization

Public module ID: M2054.

A bundle on a paracompact Hausdorff cylinder has an endpoint isomorphism
that preserves a specified trivialization near a closed subset of the base.
The trivialization is supplied on the whole time cylinder over an open
neighborhood. Its two endpoints need not coincide in any preassigned frame.
The conclusion compares their actual coordinate maps, without assuming a
global endpoint isomorphism as input.

Hatcher, Vector Bundles and K-Theory, Theorem 1.6 and Proposition 1.7 provide
ordinary bundle homotopy invariance. The relative correction below is an
explicit project supplement supporting the preservation of exterior data in
SG III.13 Lemma 13.3, equation (13.6); that application does not state this
general relative theorem verbatim. The neighborhood buffer replaces any need
to assume that the closed subset is a cofibration. Ranks may vary away from
the specified trivialization, and the base need not be compact.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Topology unitInterval

variable {X : Type*} [TopologicalSpace X]
  [hT : T2Space X] [hP : ParacompactSpace X]

attribute [local instance] isFiniteRank_pullback trivialTopology

include hT hP

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A cylinder endpoint isomorphism can preserve the supplied exterior coordinate maps. -/
theorem exists_endpoint_pullback_iso_preserving_trivialization
    (P : FiniteBundle (X × unitInterval))
    (A U : Set X) (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) (r : ℕ)
    (triv : RelativeTriple P.Fiber (Bundle.Trivial (X × unitInterval) (Fin r → ℂ))
      (Prod.fst ⁻¹' U)) :
    ∃ e : Iso
        (((⟨fun x ↦ (x, (0 : unitInterval)), continuous_id.prodMk continuous_const⟩ :
          C(X, X × unitInterval)) : X → X × unitInterval) *ᵖ P.Fiber)
        (((⟨fun x ↦ (x, (1 : unitInterval)), continuous_id.prodMk continuous_const⟩ :
          C(X, X × unitInterval)) : X → X × unitInterval) *ᵖ P.Fiber),
      ∀ (x : X) (hx : x ∈ A) (v : P.Fiber (x, 0)),
        triv.linearEquiv ⟨(x, 1), hAU hx⟩ (e.linearEquiv x v) =
          triv.linearEquiv ⟨(x, 0), hAU hx⟩ v := by
  classical
  -- Ordinary homotopy invariance supplies a jointly continuous family on the whole cylinder.
  let B := X × unitInterval
  let c : C(B, B) := ⟨fun z ↦ (z.1, 0), continuous_fst.prodMk continuous_const⟩
  let H : ContinuousMap.Homotopy c (ContinuousMap.id B) :=
    { toFun z := (z.2.1, z.1 * z.2.2)
      continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
        (continuous_fst.mul (continuous_snd.comp continuous_snd))
      map_zero_left z := by simp [c]
      map_one_left z := by simp }
  obtain ⟨b'⟩ := nonempty_pullback_iso_of_homotopic P c (ContinuousMap.id B) ⟨H⟩
  let b : Iso ((c : B → B) *ᵖ P.Fiber) P.Fiber :=
    b'.trans (pullbackIdIso (E := P.Fiber))
  -- A closed/open buffer makes the correction identically constant outside a smaller open set.
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA hU hAU
  have hdisjoint : Disjoint Vᶜ A := Set.disjoint_left.mpr (fun _ hx ha ↦ hx (hAV ha))
  obtain ⟨w, hwzero, hwone, hwbounds⟩ :=
    exists_continuous_zero_one_of_isClosed hV.isClosed_compl hA hdisjoint
  let χ : C(X, unitInterval) := ⟨fun x ↦ ⟨w x, hwbounds x⟩, w.continuous.subtype_mk _⟩
  have hχzero (x : X) (hx : x ∉ V) : χ x = 0 := Subtype.ext (hwzero hx)
  have hχone (x : X) (hx : x ∈ A) : χ x = 1 := Subtype.ext (hwone hx)
  let p₀ : C(X, B) := ⟨fun x ↦ (x, 0), continuous_id.prodMk continuous_const⟩
  let p₁ : C(X, B) := ⟨fun x ↦ (x, 1), continuous_id.prodMk continuous_const⟩
  let L₀ (x : X) : P.Fiber (x, 0) ≃ₗ[ℂ] P.Fiber (x, 1) :=
    (b.linearEquiv (x, 0)).symm.trans (b.linearEquiv (x, 1))
  let L (x : X) : P.Fiber (x, 0) ≃ₗ[ℂ] P.Fiber (x, 1) :=
    if hx : x ∈ U then
      (triv.linearEquiv ⟨(x, 0), hx⟩).trans
        ((triv.linearEquiv ⟨(x, χ x), hx⟩).symm.trans
          ((b.linearEquiv (x, χ x)).symm.trans (b.linearEquiv (x, 1))))
    else L₀ x
  have hLzero (x : X) (hx : χ x = 0) : L x = L₀ x := by
    dsimp only [L]
    split_ifs with hU
    · rw [hx]
      apply LinearEquiv.ext
      intro v
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      rfl
    · rfl
  let D := TotalSpace Unit ((p₀ : X → B) *ᵖ P.Fiber)
  -- Both the baseline and final b_1 evaluation use the original induced pullback topologies.
  have hb₁ : Continuous (fun z : D ↦
      (⟨p₁ z.proj, b.linearEquiv (p₁ z.proj) z.snd⟩ : TotalSpace Unit P.Fiber)) := by
    have hin : Continuous (fun z : D ↦
        (⟨p₁ z.proj, z.snd⟩ : TotalSpace Unit ((c : B → B) *ᵖ P.Fiber))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit P.Fiber c).continuous_iff]
      exact (p₁.continuous.comp continuous_proj).prodMk
        (Pullback.continuous_lift Unit P.Fiber p₀)
    exact b.continuous_total.comp hin
  have hb₀inv : Continuous (fun z : D ↦
      (⟨z.proj, (b.linearEquiv (p₀ z.proj)).symm z.snd⟩ : D)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit P.Fiber p₀).continuous_iff]
    exact continuous_proj.prodMk ((Pullback.continuous_lift Unit P.Fiber c).comp
      (b.continuous_symm.comp (Pullback.continuous_lift Unit P.Fiber p₀)))
  have hbaseline : Continuous (fun z : D ↦
      (⟨p₁ z.proj, L₀ z.proj z.snd⟩ : TotalSpace Unit P.Fiber)) := hb₁.comp hb₀inv
  let W : Set D := {z | z.proj ∈ U}
  let base : C(W, X) := ⟨fun z ↦ z.val.proj, continuous_proj.comp continuous_subtype_val⟩
  let O : Set B := Prod.fst ⁻¹' U
  let inc : C(O, B) := ⟨Subtype.val, continuous_subtype_val⟩
  let g₀ : C(W, O) :=
    ⟨fun z ↦ ⟨(z.val.proj, 0), z.property⟩,
      (base.continuous.prodMk continuous_const).subtype_mk _⟩
  let gχ : C(W, O) :=
    ⟨fun z ↦ ⟨(z.val.proj, χ z.val.proj), z.property⟩,
      (base.continuous.prodMk (χ.continuous.comp base.continuous)).subtype_mk _⟩
  -- The prescribed coordinate maps give q_chi = sigma_chi^{-1} sigma_0 on U.
  have hstart : Continuous (fun z : W ↦
      (⟨g₀ z, z.val.snd⟩ : TotalSpace Unit (Restrict P.Fiber O))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit P.Fiber inc).continuous_iff]
    exact g₀.continuous.prodMk
      ((Pullback.continuous_lift Unit P.Fiber p₀).comp continuous_subtype_val)
  let coords (z : W) : Fin r → ℂ := triv.linearEquiv (g₀ z) z.val.snd
  have hcoords : Continuous coords := by
    have hscalar : Continuous (fun z : TotalSpace Unit (Bundle.Trivial B (Fin r → ℂ)) ↦
        z.snd) := by
      have hc : Continuous (fun z : TotalSpace Unit (Bundle.Trivial B (Fin r → ℂ)) ↦
          (z.proj, z.snd)) := continuous_induced_dom
      exact hc.snd
    exact hscalar.comp ((Pullback.continuous_lift Unit
      (Bundle.Trivial B (Fin r → ℂ)) inc).comp (triv.continuous_total.comp hstart))
  have htrivinput : Continuous (fun z : W ↦
      (⟨gχ z, coords z⟩ : TotalSpace Unit (Restrict (Bundle.Trivial B (Fin r → ℂ)) O))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial B (Fin r → ℂ))
      inc).continuous_iff]
    apply gχ.continuous.prodMk
    apply continuous_induced_rng.mpr
    exact (continuous_subtype_val.comp gχ.continuous).prodMk hcoords
  let q (z : W) : P.Fiber (z.val.proj, χ z.val.proj) :=
    (triv.linearEquiv (gχ z)).symm (coords z)
  have hq : Continuous (fun z : W ↦
      (⟨(z.val.proj, χ z.val.proj), q z⟩ : TotalSpace Unit P.Fiber)) :=
    (Pullback.continuous_lift Unit P.Fiber inc).comp
      (triv.continuous_symm.comp htrivinput)
  -- Send q_chi back by b_chi^{-1}, then forward by b_1, without changing any frame.
  have hcorrect : Continuous (fun z : W ↦
      (⟨z.val.proj, (b.linearEquiv (z.val.proj, χ z.val.proj)).symm (q z)⟩ : D)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit P.Fiber p₀).continuous_iff]
    exact base.continuous.prodMk ((Pullback.continuous_lift Unit P.Fiber c).comp
      (b.continuous_symm.comp hq))
  have hlocal : Continuous (fun z : W ↦
      (⟨p₁ z.val.proj, L z.val.proj z.val.snd⟩ : TotalSpace Unit P.Fiber)) := by
    apply (hb₁.comp hcorrect).congr
    intro z
    dsimp only [L]
    erw [dite_eq_left (show z.val.proj ∈ U from z.property)]
    rfl
  have hcontinuous : Continuous (fun z : D ↦
      (⟨p₁ z.proj, L z.proj z.snd⟩ : TotalSpace Unit P.Fiber)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z.proj ∈ U
    · have hW : IsOpen W := hU.preimage continuous_proj
      exact (continuousOn_iff_continuous_domRestrict.mpr hlocal).continuousAt (hW.mem_nhds hz)
    · have hzV : z.proj ∉ closure V := fun h ↦ hz (hVU h)
      apply hbaseline.continuousAt.congr_of_eventuallyEq
      have hproj : ContinuousAt (π Unit ((p₀ : X → B) *ᵖ P.Fiber)) z :=
        continuous_proj.continuousAt
      filter_upwards [hproj.preimage_mem_nhds
        (isClosed_closure.isOpen_compl.mem_nhds hzV)] with y hy
      rw [hLzero y.proj (hχzero y.proj (fun h ↦ hy (subset_closure h)))]
  let F : Hom ((p₀ : X → B) *ᵖ P.Fiber) ((p₁ : X → B) *ᵖ P.Fiber) :=
    { linearMap x := (L x).toLinearMap
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit P.Fiber p₁).continuous_iff]
        exact continuous_proj.prodMk hcontinuous }
  refine ⟨F.toIso (fun x ↦ (L x).bijective), ?_⟩
  intro x hx v
  change triv.linearEquiv ⟨(x, 1), hAU hx⟩ (L x v) = _
  dsimp only [L]
  rw [dite_eq_left (hAU hx), hχone x hx]
  simp only [LinearEquiv.trans_apply]
  erw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

end AtiyahSinger.ComplexBundle
