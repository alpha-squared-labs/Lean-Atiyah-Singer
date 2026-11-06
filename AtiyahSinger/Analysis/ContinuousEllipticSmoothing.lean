/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OperatorSymbolKClass
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Smooth homogeneous representatives of continuous cotangent triples

Public module ID: M0401.

On two specified native smooth bundles, a continuous degree-zero elliptic
boundary with zero-section control admits a smooth homogeneous representative
of any real degree and the identical compact-support K class. Its restriction
to a cosphere is smoothed through invertible maps, then extended radially.

This is the ordinary smoothing supplement to Spin Geometry III.13, Lemma 13.3.
Neither connectedness, positive dimension nor equal global model ranks is
required. The original boundary, its exact control and its K class are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hC : CompactSpace M] [hSC : SecondCountableTopology M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent isFiniteRank_pullback

include hM hT hC hSC in
/-- Smooth the specified homogeneous continuous triple without changing its cotangent K class. -/
theorem exists_smooth_homogeneousSymbol_of_continuousTriple
    (E F : SmoothFiniteComplexBundle (n := n) M) (m : ℝ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ a : CompactSupportTriple
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
      a.control = cotangentZeroSet →
      (∀ (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ), 0 < t →
        ∀ (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ)
          (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ),
          a.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
            a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩) →
      ∃ b : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber m,
        ∃ hi : IsEllipticGlobalSymbol E.Fiber F.Fiber b.val,
          homogeneousSymbolKClass m b hi = a.compactSupportClass := by
  classical
  let VE := EuclideanSpace ℂ (Fin E.rank)
  let VF := EuclideanSpace ℂ (Fin F.rank)
  let := modelTopology VE E.Fiber
  let := modelTopology VF F.Fiber
  let : IsFiniteRank E.Fiber := isFiniteRank_model VE E.Fiber
  let : IsFiniteRank F.Fiber := isFiniteRank_model VF F.Fiber
  let : ∀ x, FiniteDimensional ℂ (E.Fiber x) := fun x ↦
    VectorBundle.finiteDimensional ℂ VE E.Fiber x
  let : ∀ x, FiniteDimensional ℂ (F.Fiber x) := fun x ↦
    VectorBundle.finiteDimensional ℂ VF F.Fiber x
  intro a hzero hhom
  rcases a with ⟨K, hK, β⟩
  dsimp only at hzero hhom ⊢
  subst K
  let πM := cotangentProjection (n := n) (M := M)
  let U := PuncturedCotangentBundle (n := n) (M := M)
  let incl : C(U, CotangentTotalSpace (n := n) (M := M)) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let f : C(U, M) := πM.comp incl
  let eE := pullbackCompIso (E := E.Fiber) πM incl
  let eF := pullbackCompIso (E := F.Fiber) πM incl
  let β' : Iso ((f : U → M) *ᵖ E.Fiber) ((f : U → M) *ᵖ F.Fiber) :=
    eE.symm.trans (β.trans eF)
  have hβ (z : U) (v : E.Fiber (f z)) : β'.linearEquiv z v = β.linearEquiv z v := by
    change eF.linearEquiv z (β.linearEquiv z ((eE.linearEquiv z).symm v)) = _
    have hinv : (eE.linearEquiv z).symm v = v :=
      (congrArg (eE.linearEquiv z).symm
        (pullbackCompIso_apply (E := E.Fiber) πM incl z v)).symm.trans
          ((eE.linearEquiv z).symm_apply_apply v)
    exact (pullbackCompIso_apply (E := F.Fiber) πM incl z
      (β.linearEquiv z ((eE.linearEquiv z).symm v))).trans
        (congrArg (β.linearEquiv z) hinv)
  let s : GlobalSymbolFunction (n := n) E.Fiber F.Fiber := fun x ξ ↦
    if hξ : ξ ≠ 0 then
      LinearMap.toContinuousLinearMap
        (show E.Fiber x →ₗ[ℂ] F.Fiber x from (β.linearEquiv ⟨⟨x, ξ⟩, hξ⟩).toLinearMap)
    else 0
  have hsapply (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0)
      (v : E.Fiber x) : s x ξ v = β.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ v := by
    simp only [s, dite_eq_left hξ]
    rfl
  -- Joint continuity of the original bundle map gives continuity of its finite Hom coordinates.
  have hs : IsContinuousOffZeroGlobalSymbol (r := E.rank) (q := F.rank) s := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
    refine ⟨f.continuous.continuousAt, ?_⟩
    let e := trivializationAt VE E.Fiber (f z₀)
    let d := trivializationAt VF F.Fiber (f z₀)
    have he₀ : f z₀ ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    have hd₀ : f z₀ ∈ d.baseSet := mem_baseSet_trivializationAt _ _ _
    have hevent : ∀ᶠ z : U in 𝓝 z₀, f z ∈ e.baseSet :=
      f.continuous.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he₀)
    have hdevent : ∀ᶠ z : U in 𝓝 z₀, f z ∈ d.baseSet :=
      f.continuous.continuousAt.preimage_mem_nhds (d.open_baseSet.mem_nhds hd₀)
    apply continuousAt_clm_apply.mpr
    intro v
    have hsection : ContinuousAt (fun z : U ↦
        (⟨f z, e.symm (f z) v⟩ : TotalSpace VE E.Fiber)) z₀ := by
      have hlocal : ContinuousOn (fun z : U ↦
          (⟨f z, e.symm (f z) v⟩ : TotalSpace VE E.Fiber))
          (f ⁻¹' e.baseSet) :=
        e.continuousOn_symm.comp (f.continuous.prodMk continuous_const).continuousOn
          (fun z hz ↦ ⟨hz, Set.mem_univ v⟩)
      exact hlocal.continuousAt hevent
    have hpull : ContinuousAt (fun z : U ↦
        (⟨z, e.symm (f z) v⟩ : TotalSpace Unit ((f : U → M) *ᵖ E.Fiber))) z₀ := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber f).continuousAt_iff]
      exact continuousAt_id.prodMk
        ((continuous_unitTotalEquiv_symm VE E.Fiber).continuousAt.comp hsection)
    have hout := β'.continuous_total.continuousAt.comp hpull
    have hlift := (continuous_unitTotalEquiv VF F.Fiber).continuousAt.comp
      ((Pullback.continuous_lift Unit F.Fiber f).continuousAt.comp hout)
    have hcoord := (d.continuousAt (d.mem_source.mpr hd₀)).snd.comp hlift
    apply hcoord.congr_of_eventuallyEq
    filter_upwards [hevent, hdevent] with z hez hdz
    change (d.continuousLinearMapAt ℂ (f z))
      (s z.val.proj z.val.snd ((e.symmL ℂ (f z)) v)) =
        (d ⟨f z, β'.linearEquiv z (e.symm (f z) v)⟩).2
    rw [e.symmL_apply hez, hsapply _ _ z.property, ← hβ]
    exact d.continuousLinearMapAt_apply_of_mem ℂ hdz _
  have hi : IsEllipticGlobalSymbol E.Fiber F.Fiber s := by
    intro x ξ hξ
    constructor
    · intro v w hvw
      apply (β.linearEquiv ⟨⟨x, ξ⟩, hξ⟩).injective
      exact (hsapply x ξ hξ v).symm.trans (hvw.trans (hsapply x ξ hξ w))
    · intro w
      obtain ⟨v, hv⟩ := (β.linearEquiv ⟨⟨x, ξ⟩, hξ⟩).surjective w
      exact ⟨v, (hsapply x ξ hξ v).trans hv⟩
  have hh : IsHomogeneousGlobalSymbol E.Fiber F.Fiber 0 s := by
    intro x ξ hξ t ht
    have htξ : t • ξ ≠ 0 := smul_ne_zero (ne_of_gt ht) hξ
    apply ContinuousLinearMap.ext
    intro v
    simp only [Real.rpow_zero, Complex.ofReal_one, one_smul]
    rw [hsapply _ _ htξ, hsapply _ _ hξ, hhom x ξ t ht hξ htξ]
    rfl
  -- Smooth on one actual cosphere through invertible maps and then choose the requested degree.
  obtain ⟨g⟩ := SmoothCotangentMetric.nonempty (n := n) (M := M)
  let c : ContinuousCosphereSymbol (r := E.rank) (q := F.rank)
      (E := E.Fiber) (F := F.Fiber) g := ⟨cosphereRestriction g s, hs.cosphereRestriction g⟩
  have hc : IsEllipticCosphereSymbol g c.val :=
    (isEllipticCosphereSymbol_restriction_iff g 0 s hh).mpr hi
  obtain ⟨d, hcd⟩ := exists_smoothCosphere_homotopic g c hc
  let b := smoothCosphereExtension (r := E.rank) (q := F.rank) g m d
  have hb : IsEllipticGlobalSymbol E.Fiber F.Fiber b.val :=
    (isEllipticGlobalSymbol_cosphereExtension_iff g m d.val).mpr (hcd.elliptic_right g)
  refine ⟨b, hb, ?_⟩
  have htriple : ellipticSymbolTriple s hs hi =
      (⟨cotangentZeroSet, hK, β⟩ : CompactSupportTriple
        ((πM : _ → M) *ᵖ E.Fiber) ((πM : _ → M) *ᵖ F.Fiber)) := by
    change CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet
      (ellipticSymbolBoundary s hs hi) = CompactSupportTriple.mk cotangentZeroSet hK β
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    exact (ellipticSymbolBoundary_apply s hs hi z v).trans (hsapply _ _ z.property v)
  calc
    homogeneousSymbolKClass m b hb = cosphereKClass g d.val
        (IsSmoothCosphereSymbol.continuous g d.property) (hcd.elliptic_right g) :=
      symbolKClass_extension g d.val (IsSmoothCosphereSymbol.continuous g d.property)
        (hcd.elliptic_right g) m
    _ = cosphereKClass g c.val c.property hc :=
      (cosphereKClass_eq_of_homotopic g c.val c.property hc d.val
        (IsSmoothCosphereSymbol.continuous g d.property) (hcd.elliptic_right g) hcd).symm
    _ = symbolKClass s hs hi := (symbolKClass_eq_cosphere g 0 s hs hh hi).symm
    _ = _ := congrArg CompactSupportTriple.compactSupportClass htriple

end AtiyahSinger
