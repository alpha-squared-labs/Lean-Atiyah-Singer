/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentModelChangeInverse
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Support triples in the specified native cotangent model

Public module ID: M1748.

A support triple on the original cotangent projection pullbacks transports to
the Euclidean model by the actual inverse cotangent homeomorphism. The source
and target fibers keep their original vectors. The exact exterior boundary,
compact control and constructed K class are retained together.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isFiniteRank_pullback

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
  (M : Type*) [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℝ, V) ∞ M] [T2Space M]
  (A B : M → Type*)
  [∀ x, AddCommGroup (A x)] [∀ x, Module ℂ (A x)]
  [TopologicalSpace (TotalSpace Unit A)] [IsFiniteRank A]
  [∀ x, AddCommGroup (B x)] [∀ x, Module ℂ (B x)]
  [TopologicalSpace (TotalSpace Unit B)] [IsFiniteRank B]

local notation "OrigCot" =>
  TotalSpace (V →L[ℝ] ℝ) (fun x : M ↦ TangentSpace 𝓘(ℝ, V) x →L[ℝ] ℝ)
local notation "Cot" => CotangentTotalSpace (n := n) (M := M)

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- The two cotangent topologies and their nested projection pullbacks are checked together.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same support datum in the actual Euclidean cotangent model retains its full boundary. -/
theorem exists_cotangentLinearModelSupportTriple :
    let proj : C(OrigCot, M) := ⟨TotalSpace.proj,
      FiberBundle.continuous_proj (V →L[ℝ] ℝ)
        (fun x : M ↦ TangentSpace 𝓘(ℝ, V) x →L[ℝ] ℝ)⟩
    ∀ d : CompactSupportTriple (proj *ᵖ A) (proj *ᵖ B),
      letI := linearModelChartedSpace e M
      letI := isManifold_linearModelChartedSpace e M
      let c := cotangentLinearModelHomeomorph e M
      letI := c.symm.t2Space
      letI := c.isOpenEmbedding.locallyCompactSpace
      let pr := cotangentProjection (n := n) (M := M)
      let back : Cot → OrigCot := fun z ↦ ⟨z.proj, z.snd.comp e.toContinuousLinearMap⟩
      ∃ d' : CompactSupportTriple (pr *ᵖ A) (pr *ᵖ B),
        d'.control = back ⁻¹' d.control ∧
        d'.compactSupportClass =
          compactSupportKZeroPullback ⟨c.symm, c.symm.continuous⟩ c.symm.isProperMap
            d.compactSupportClass ∧
        ∀ (z : Cot) (hz : back z ∉ d.control) (hz' : z ∉ d'.control) (u : A z.proj),
          d'.boundary.linearEquiv ⟨z, hz'⟩ u =
            d.boundary.linearEquiv ⟨back z, hz⟩ u := by
  intro proj d
  let := linearModelChartedSpace e M
  let := isManifold_linearModelChartedSpace e M
  intro c
  let := c.symm.t2Space
  let := c.isOpenEmbedding.locallyCompactSpace
  intro pr back
  -- Use the proved inverse formula to retain literal projection fibers and full covectors.
  have hback : back = c.symm := by
    funext z
    exact (cotangentLinearModelHomeomorph_symm_apply e M z).symm
  let inverse : C(Cot, OrigCot) := ⟨back, hback ▸ c.symm.continuous⟩
  have hinverse : inverse = ⟨c.symm, c.symm.continuous⟩ := by
    apply ContinuousMap.ext
    exact fun z ↦ congrFun hback z
  have hproper : IsProperMap inverse := by
    rw [hinverse]
    exact c.symm.isProperMap
  let s : Iso (inverse *ᵖ (proj *ᵖ A)) (pr *ᵖ A) := pullbackCompIso proj inverse
  let t : Iso (inverse *ᵖ (proj *ᵖ B)) (pr *ᵖ B) := pullbackCompIso proj inverse
  let d' := (d.pullback inverse hproper).congr s t
  refine ⟨d', rfl, ?_, ?_⟩
  · -- Proper pullback gives the original K map; projection reassociation changes no vector.
    calc
      d'.compactSupportClass = (d.pullback inverse hproper).compactSupportClass :=
        (d.pullback inverse hproper).compactSupportClass_congr s t
      _ = compactSupportKZeroPullback inverse hproper d.compactSupportClass :=
        d.compactSupportClass_pullback inverse hproper
      _ = _ := by
        have hpull (f g : C(Cot, OrigCot)) (hf : IsProperMap f) (hg : IsProperMap g)
            (hfg : f = g) :
            compactSupportKZeroPullback f hf d.compactSupportClass =
              compactSupportKZeroPullback g hg d.compactSupportClass := by
          subst g
          rfl
        exact hpull inverse ⟨c.symm, c.symm.continuous⟩ hproper c.symm.isProperMap hinverse
  · intro z hz hz' u
    have hs : s.symm.linearEquiv z u = u := by
      apply (s.linearEquiv z).injective
      exact ((s.linearEquiv z).apply_symm_apply u).trans
        (pullbackCompIso_apply proj inverse z u).symm
    -- The same exterior vector is evaluated by the original boundary at the full inverse image.
    have hcongr := (d.pullback inverse hproper).congr_apply s t ⟨z, hz'⟩ u
    have hpull := RelativeTriple.pullback_apply d.boundary inverse
      ⟨z, hz'⟩ (s.symm.linearEquiv z u)
    exact hcongr.trans ((congrArg (t.linearEquiv z)
      (hpull.trans (congrArg (d.boundary.linearEquiv ⟨back z, hz⟩) hs))).trans
        (pullbackCompIso_apply proj inverse z _))

end AtiyahSinger
