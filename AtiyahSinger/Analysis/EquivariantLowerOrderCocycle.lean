/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactGroupCocycle
public import AtiyahSinger.Analysis.GlobalSymbolFamilyBounds
public import AtiyahSinger.Analysis.EquivariantSymbolOrbitBounds

/-!
# Uniform bounds for the original lower-order symbol cocycle

Public module ID: M0538.

If a geometric orbit differs from one original order-m symbol by lower-order
symbols, the differences are uniformly bounded in every original lower-order
seminorm. Saturating that seminorm over compact geometric orbits produces a
finite invariant seminorm. Closed sublevels follow from the actual mixed jets,
and the existing compact-group Baire cocycle theorem supplies the uniform bound.
No continuity in the stronger lower-order symbol topology is assumed.
-/

@[expose] public noncomputable section
namespace AtiyahSinger
open Bundle Set
open scoped Manifold ContDiff
set_option maxSynthPendingDepth 20
variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    ComplexBundle.EquivariantStructure G E)
  (τ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
    ComplexBundle.EquivariantStructure G F)

variable [hG : IsManifold IG ∞ G]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (hτ : τ.IsSmooth (n := n) (r := q) IG)


variable [CompactSpace G] [T2Space G]
attribute [local instance] GlobalSymbolSeminormIndex.input_mem_atlas
  GlobalSymbolSeminormIndex.output_mem_atlas

set_option maxHeartbeats 1200000 in
-- The exact original geometric action is expanded only in the cocycle and jet identities.
include hG hM hE hF hσ hτ in
/-- Pointwise lower-order orbit differences have uniform original lower-order seminorm bounds. -/
theorem bddAbove_range_globalSymbolSeminorm_lowerOrder_cocycle (m : ℝ)
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hLower : ∀ g, IsGlobalSymbol E F (m - 1)
      (equivariantGlobalSymbolLinearMap IG σ τ g p.val - p.val))
    (J : GlobalSymbolSeminormIndex (n := n) (r := r) (q := q) E F) :
    BddAbove (range (fun g : G ↦ globalSymbolSeminorm E F (m - 1) J
      ⟨equivariantGlobalSymbolLinearMap IG σ τ g p.val - p.val, hLower g⟩)) := by
  -- The existing compact geometric orbit bound makes the saturated seminorm finite.
  have hbounded (v : globalSymbolSpace (n := n) (r := r) (q := q) E F (m - 1)) :
      BddAbove (range (fun g : G ↦ globalSymbolSeminorm E F (m - 1) J
        (equivariantGlobalSymbolRepresentation IG σ τ hσ hτ (m - 1) g v))) :=
    bddAbove_range_globalSymbolSeminorm_equivariant IG σ τ hσ hτ (m - 1) v J
  let W := globalSymbolSpace (n := n) (r := r) (q := q) E F (m - 1)
  let R := equivariantGlobalSymbolRepresentation IG σ τ hσ hτ
  let ρ : G →* AddMonoid.End W := {
    toFun g := (R (m - 1) g).toAddMonoidHom
    map_one' := by
      apply AddMonoidHom.ext
      intro v
      exact congrArg (fun T ↦ T v) (R (m - 1)).map_one
    map_mul' := by
      intro g h
      apply AddMonoidHom.ext
      intro v
      exact congrArg (fun T ↦ T v) ((R (m - 1)).map_mul g h) }
  let qNorm := (globalSymbolSeminorm E F (m - 1) J).toAddGroupSeminorm
  let d (g : G) : W := ⟨equivariantGlobalSymbolLinearMap IG σ τ g p.val - p.val, hLower g⟩
  -- Both sides are the same original geometric action, so the difference is a cocycle.
  have hcocycle (g h : G) : d (g * h) = ρ g (d h) + d g := by
    apply Subtype.ext
    change equivariantGlobalSymbolLinearMap IG σ τ (g * h) p.val - p.val =
      equivariantGlobalSymbolLinearMap IG σ τ g
        (equivariantGlobalSymbolLinearMap IG σ τ h p.val - p.val) +
        (equivariantGlobalSymbolLinearMap IG σ τ g p.val - p.val)
    rw [(equivariantGlobalSymbolAction_properties IG σ τ hσ hτ).2.2, LinearMap.comp_apply,
      map_sub]
    abel
  -- Each saturated sublevel is an intersection of closed actual mixed-jet tests.
  have hclosed (h : G) (N : ℕ) : IsClosed {g : G | qNorm (ρ h (d g)) ≤ (N : ℝ)} := by
    apply isClosed_le_globalSymbolSeminorm_of_continuous_jets E F (m - 1)
      (fun g ↦ ρ h (d g)) J
    intro x hx ξ
    have hdom := J.localIndex.subset_domain hx
    have hraw := continuousOn_symbolDerivative_equivariantGlobalSymbol IG σ τ hσ hτ
      p J.chart J.mem_atlas J.inputFrame J.outputFrame
      J.localIndex.spatialOrder J.localIndex.frequencyOrder
    have hmap : Continuous (fun g : G ↦ (h * g, (x, ξ))) :=
      (continuous_const.mul continuous_id).prodMk continuous_const
    have hfirst : Continuous (fun g : G ↦ symbolDerivative
        (globalSymbolInChart E F
          (equivariantGlobalSymbolLinearMap IG σ τ (h * g) p.val)
          J.chart J.inputFrame J.outputFrame)
        J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ) :=
      hraw.comp_continuous (f := fun g : G ↦ (h * g, (x, ξ))) hmap
        (fun _ ↦ hdom)
    have hdiff := hfirst.sub (continuous_const (y := symbolDerivative
      (globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ h p.val)
        J.chart J.inputFrame J.outputFrame)
      J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ))
    convert hdiff using 1
    funext g
    have heq : (ρ h (d g)).val =
        equivariantGlobalSymbolLinearMap IG σ τ (h * g) p.val -
          equivariantGlobalSymbolLinearMap IG σ τ h p.val := by
      change equivariantGlobalSymbolLinearMap IG σ τ h
          (equivariantGlobalSymbolLinearMap IG σ τ g p.val - p.val) = _
      rw [map_sub, (equivariantGlobalSymbolAction_properties IG σ τ hσ hτ).2.2,
        LinearMap.comp_apply]
    rw [heq]
    let U := symbolChartDomain E F J.chart J.inputFrame J.outputFrame
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    have hU : IsOpen U := isOpen_symbolChartDomain E F J.chart J.inputFrame J.outputFrame
    let a := globalSymbolInChart E F
      (equivariantGlobalSymbolLinearMap IG σ τ (h * g) p.val)
      J.chart J.inputFrame J.outputFrame
    let b := globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ h p.val)
      J.chart J.inputFrame J.outputFrame
    have ha : IsSymbol U m a :=
      (R m (h * g) p).property J.chart J.mem_atlas J.inputFrame J.outputFrame
    have hb : IsSymbol U m b :=
      (R m h p).property J.chart J.mem_atlas J.inputFrame J.outputFrame
    have hcoord : globalSymbolInChart E F
        (equivariantGlobalSymbolLinearMap IG σ τ (h * g) p.val -
          equivariantGlobalSymbolLinearMap IG σ τ h p.val)
        J.chart J.inputFrame J.outputFrame = a - b := by
      ext z η v
      simp [globalSymbolInChart, a, b]
    rw [hcoord]
    have hfreq (f : SymbolFunction n r q) (hf : IsSymbol U m f) :
        ContDiffAt ℝ ∞ (fun z ↦ iteratedFDeriv ℝ J.localIndex.frequencyOrder (f z) ξ) x := by
      have hpair : ContMDiffOn (I.prod I)
          𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
          (Function.uncurry f) (U ×ˢ univ) := by
        intro z hz
        exact ((hf.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz)).contMDiffAt.comp z
          (contMDiffAt_fst.prodMk_space contMDiffAt_snd)).contMDiffWithinAt
      have h := (contMDiffOn_iteratedFDeriv_parameter I (hU.prod isOpen_univ)
        hpair J.localIndex.frequencyOrder).contMDiffAt (x := (x, ξ))
          ((hU.prod isOpen_univ).mem_nhds ⟨hdom, mem_univ ξ⟩)
      exact (h.comp x (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt
    have hevent : (fun z ↦ iteratedFDeriv ℝ J.localIndex.frequencyOrder ((a - b) z) ξ)
        =ᶠ[nhds x] (fun z ↦ iteratedFDeriv ℝ J.localIndex.frequencyOrder (a z) ξ -
          iteratedFDeriv ℝ J.localIndex.frequencyOrder (b z) ξ) := by
      filter_upwards [hU.mem_nhds hdom] with z hz
      apply iteratedFDeriv_sub_apply
      · exact ((ha.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds
          ⟨hz, mem_univ ξ⟩)).comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
      · exact ((hb.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds
          ⟨hz, mem_univ ξ⟩)).comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
    exact ((hevent.iteratedFDeriv ℝ J.localIndex.spatialOrder).eq_of_nhds).trans
      (iteratedFDeriv_sub_apply ((hfreq a ha).of_le (by simp)) ((hfreq b hb).of_le (by simp)))
  have hbounded' (v : W) : BddAbove (range (fun g : G ↦ qNorm (ρ g v))) := hbounded v
  -- The supremum over the same group action is an invariant finite seminorm.
  let P : AddGroupSeminorm W := {
    toFun v := sSup (range (fun g : G ↦ qNorm (ρ g v)))
    map_zero' := by
      have hz (g : G) : qNorm (ρ g (0 : W)) = 0 :=
        (congrArg qNorm (map_zero (ρ g))).trans qNorm.map_zero'
      simp only [hz, range_const, csSup_singleton]
    add_le' := by
      intro v w
      apply csSup_le (range_nonempty _)
      rintro t ⟨g, rfl⟩
      change qNorm (ρ g (v + w)) ≤ _
      rw [map_add]
      exact (map_add_le_add qNorm _ _).trans
        (add_le_add (le_csSup (hbounded' v) (mem_range_self g))
          (le_csSup (hbounded' w) (mem_range_self g)))
    neg' := by
      intro v
      have hn (g : G) : qNorm (ρ g (-v)) = qNorm (ρ g v) :=
        (congrArg qNorm (map_neg (ρ g) v)).trans (qNorm.neg' (ρ g v))
      simp only [hn] }
  have hP (v : W) : qNorm v ≤ P v := by
    have h := le_csSup (hbounded' v) (mem_range_self (1 : G))
    change qNorm v ≤ sSup (range (fun g : G ↦ qNorm (ρ g v)))
    simpa using h
  have hinv (g : G) (v : W) : P (ρ g v) = P v := by
    change sSup _ = sSup _
    congr 1
    ext t
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h * g, by simp⟩
    · rintro ⟨h, rfl⟩
      refine ⟨h * g⁻¹, ?_⟩
      change qNorm ((ρ (h * g⁻¹) * ρ g) v) = qNorm (ρ h v)
      rw [← map_mul, inv_mul_cancel_right]
  have hPc (n : ℕ) : IsClosed {g : G | P (d g) ≤ (n : ℝ)} := by
    have heq : {g : G | P (d g) ≤ (n : ℝ)} =
        ⋂ h : G, {g : G | qNorm (ρ h (d g)) ≤ (n : ℝ)} := by
      ext g
      simp only [mem_ofPred_eq, mem_iInter]
      constructor
      · intro h h'
        exact (le_csSup (hbounded' (d g)) (mem_range_self h')).trans h
      · intro h
        exact csSup_le (range_nonempty _) (by rintro t ⟨h', rfl⟩; exact h h')
    rw [heq]
    exact isClosed_iInter (fun h ↦ hclosed h n)
  -- Baire category and compactness now apply to the original lower-order difference.
  let : SMul G W := ⟨fun g v ↦ ρ g v⟩
  obtain ⟨C, hC⟩ := AtiyahSinger.bddAbove_range_seminorm_cocycle P d hinv hcocycle hPc
  exact ⟨C, by rintro t ⟨g, rfl⟩; exact (hP (d g)).trans (hC (mem_range_self g))⟩

end AtiyahSinger
