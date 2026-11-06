/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OpenManifoldDerivative
public import AtiyahSinger.Geometry.SphereCotangentPoleCoordinates
public import AtiyahSinger.Geometry.SphereProductPoleCoordinates

/-!
# Inverse-dual product pole coordinates

Public module ID: M1437.

The common Euclidean chart of the actual product of two spheres has the
same cotangent lift as the two factor charts, under the original finite
coordinate concatenation and canonical cotangent splitting. This is a
geometric equality before any analytic index or Bott evaluation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace Topology
open scoped Manifold ContDiff Topology Matrix.Norms.L2Operator

set_option maxSynthPendingDepth 30

/-- The product pole chart lifted by the inverse differential to the native cotangent bundle. -/
def orthogonalSphereProductCotangentChart (p q : ℕ) (atInfinity : Bool) :
    letI := euclideanProductChartedSpace (n := p) (m := q)
      (OrthogonalSphere p) (OrthogonalSphere q)
    letI := isManifold_euclideanProductChartedSpace (n := p) (m := q)
      (OrthogonalSphere p) (OrthogonalSphere q)
    C(EuclideanSpace ℂ (Fin (p + q)),
      CotangentTotalSpace (n := p + q) (M := OrthogonalSphere p × OrthogonalSphere q)) := by
  let := euclideanProductChartedSpace (n := p) (m := q)
    (OrthogonalSphere p) (OrthogonalSphere q)
  let := isManifold_euclideanProductChartedSpace (n := p) (m := q)
    (OrthogonalSphere p) (OrthogonalSphere q)
  let U := orthogonalSphereProductPoleOpen p q atInfinity
  let f := orthogonalSphereProductPoleDiffeomorph p q atInfinity
  let C := euclideanCotangentComplexHomeomorph (p + q)
  exact ⟨fun z ↦ cotangentOpenInclusion U (cotangentDiffeomorph f (C.symm z)),
    (isOpenEmbedding_cotangentOpenInclusion U).continuous.comp
      ((cotangentDiffeomorph f).continuous.comp C.symm.continuous)⟩

/-- The native product cotangent pole lift is an open embedding. -/
theorem orthogonalSphereProductCotangentChart_isOpenEmbedding (p q : ℕ) (atInfinity : Bool) :
    letI := euclideanProductChartedSpace (n := p) (m := q)
      (OrthogonalSphere p) (OrthogonalSphere q)
    letI := isManifold_euclideanProductChartedSpace (n := p) (m := q)
      (OrthogonalSphere p) (OrthogonalSphere q)
    IsOpenEmbedding (orthogonalSphereProductCotangentChart p q atInfinity) := by
  let := euclideanProductChartedSpace (n := p) (m := q)
    (OrthogonalSphere p) (OrthogonalSphere q)
  let := isManifold_euclideanProductChartedSpace (n := p) (m := q)
    (OrthogonalSphere p) (OrthogonalSphere q)
  exact (isOpenEmbedding_cotangentOpenInclusion _).comp
    ((cotangentDiffeomorph _).isOpenEmbedding.comp
      (euclideanCotangentComplexHomeomorph (p + q)).symm.isOpenEmbedding)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2400000 in
-- Differentiate in the original product model, then use the fixed linear recharting.
/-- The actual inverse-dual product chart splits into the two original cotangent pole charts. -/
theorem orthogonalSphereProductCotangentChart_split (p q : ℕ) (atInfinity : Bool)
    (z : EuclideanSpace ℂ (Fin (p + q))) :
    letI := euclideanProductChartedSpace (n := p) (m := q)
      (OrthogonalSphere p) (OrthogonalSphere q)
    letI := isManifold_euclideanProductChartedSpace (n := p) (m := q)
      (OrthogonalSphere p) (OrthogonalSphere q)
    let C := EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := p) (m := q)
    cotangentProductHomeomorph (OrthogonalSphere p) (OrthogonalSphere q)
        (orthogonalSphereProductCotangentChart p q atInfinity z) =
      (orthogonalSphereCotangentChart p atInfinity (C z).1,
        orthogonalSphereCotangentChart q atInfinity (C z).2) := by
  let E := EuclideanSpace ℝ (Fin p)
  let F := EuclideanSpace ℝ (Fin q)
  let R := EuclideanSpace ℝ (Fin (p + q))
  let X := OrthogonalSphere p × OrthogonalSphere q
  let P := 𝓘(ℝ, E × F)
  let K := 𝓡 (p + q)
  let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q)
  let C := EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := p) (m := q)
  let e := orthogonalSphereNormalizedChart p atInfinity
  let f := orthogonalSphereNormalizedChart q atInfinity
  let b (x : X) : R := c.symm (e x.1, f x.2)
  let U := orthogonalSphereProductPoleOpen p q atInfinity
  let : ChartedSpace (E × F) X := prodChartedSpace E (OrthogonalSphere p) F (OrthogonalSphere q)
  let : IsManifold P ∞ X := by
    dsimp only [P]
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (OrthogonalSphere p) (OrthogonalSphere q)
  have he (x : OrthogonalSphere p) (hx : x ∈ e.source) :
      MDifferentiableAt (𝓡 p) (𝓡 p) e x :=
    ((orthogonalSphereNormalizedChart_smooth p atInfinity).1.contMDiffAt
      (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hf (x : OrthogonalSphere q) (hx : x ∈ f.source) :
      MDifferentiableAt (𝓡 q) (𝓡 q) f x :=
    ((orthogonalSphereNormalizedChart_smooth q atInfinity).1.contMDiffAt
      (f.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hpair (x : X) (hx : x ∈ U) :
      MDifferentiableAt P 𝓘(ℝ, E × F) (Prod.map e f) x := by
    dsimp only [P, E, F, X]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (he x.1 hx.1).prodMap (hf x.2 hx.2)
  have hb (x : X) (hx : x ∈ U) : MDifferentiableAt P K b x :=
    (c.symm.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp) |>.comp x (hpair x hx)
  have hDb (x : X) (hx : x ∈ U) :
      mfderiv P K b x = c.symm.toContinuousLinearMap.comp
        ((mfderiv (𝓡 p) (𝓡 p) e x.1).prodMap (mfderiv (𝓡 q) (𝓡 q) f x.2)) := by
    have hh := mfderiv_comp x
      ((c.symm.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp)) (hpair x hx)
    change mfderiv P K b x = _ at hh
    have hlin : mfderiv 𝓘(ℝ, E × F) K c.symm (e x.1, f x.2) =
        c.symm.toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv]
      exact c.symm.toContinuousLinearMap.fderiv
    have hp : mfderiv P 𝓘(ℝ, E × F) (Prod.map e f) x =
        (mfderiv (𝓡 p) (𝓡 p) e x.1).prodMap (mfderiv (𝓡 q) (𝓡 q) f x.2) := by
      dsimp only [P, E, F, X]
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact mfderiv_prodMap (he x.1 hx.1) (hf x.2 hx.2)
    exact hh.trans (congrArg₂ (fun a d ↦ a.comp d) hlin hp)
  let := euclideanProductChartedSpace (n := p) (m := q)
    (OrthogonalSphere p) (OrthogonalSphere q)
  let := isManifold_euclideanProductChartedSpace (n := p) (m := q)
    (OrthogonalSphere p) (OrthogonalSphere q)
  let D := orthogonalSphereProductPoleDiffeomorph p q atInfinity
  have hchange := contMDiff_mfderiv_linearModelId c.symm X
  have hbK (x : X) (hx : x ∈ U) : MDifferentiableAt K K b x :=
    (hb x hx).comp (f := id) x (hchange.1.2.mdifferentiable (by simp) x)
  have hDbK (x : X) (hx : x ∈ U) :
      mfderiv K K b x = c.symm.toContinuousLinearMap.comp
        (((mfderiv (𝓡 p) (𝓡 p) e x.1).prodMap
          (mfderiv (𝓡 q) (𝓡 q) f x.2)).comp c.toContinuousLinearMap) := by
    have hh := mfderiv_comp (f := id) x (hb x hx)
      (hchange.1.2.mdifferentiable (by simp) x)
    change mfderiv K K b x = _ at hh
    have hcomp := congrArg₂ (fun a d ↦ a.comp d) (hDb x hx) (hchange.2.2 x)
    exact hh.trans hcomp
  have hD (x : U) : mfderiv K K D.symm x = mfderiv K K b x.val := by
    have hh := mfderiv_comp x (hbK x.val x.property)
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
    change mfderiv K K D.symm x = _ at hh
    rw [mfderiv_openSubtype_val] at hh
    change (mfderiv K K D.symm x : R →L[ℝ] R) =
      (mfderiv K K b x.val : R →L[ℝ] R).comp (ContinuousLinearMap.id ℝ R) at hh
    exact hh.trans (ContinuousLinearMap.comp_id _)
  let u : R := WithLp.toLp 2 (fun i ↦ (z i).re)
  let v : R := WithLp.toLp 2 (fun i ↦ (z i).im)
  have hx : (D u).val ∈ U := (D u).property
  have hξ : orthogonalSphereProductCotangentChart p q atInfinity z =
      (⟨(D u).val, (innerSL ℝ v).comp (mfderiv K K b (D u).val)⟩ :
        CotangentTotalSpace (n := p + q) (M := X)) := by
    change (⟨(D u).val, (innerSL ℝ v).comp (mfderiv K K D.symm (D u))⟩ :
      CotangentTotalSpace (n := p + q) (M := X)) = _
    rw [hD]
  have hinverse (w : CotangentTotalSpace (n := p + q) (M := X)) :
      (cotangentLinearModelHomeomorph c.symm X).symm w =
        ⟨w.proj, w.snd.comp c.symm.toContinuousLinearMap⟩ := by
    apply (cotangentLinearModelHomeomorph c.symm X).injective
    rw [Homeomorph.apply_symm_apply]
    change w = ⟨w.proj, (w.snd.comp c.symm.toContinuousLinearMap).comp
      c.toContinuousLinearMap⟩
    cases w with
    | mk x ξ =>
      apply congrArg (TotalSpace.mk x)
      apply ContinuousLinearMap.ext
      intro w
      exact (congrArg ξ (c.symm_apply_apply w)).symm
  have hsplit (w : CotangentTotalSpace (n := p + q) (M := X)) :
      cotangentProductHomeomorph (OrthogonalSphere p) (OrthogonalSphere q) w =
        (⟨w.proj.1, (w.snd.comp c.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ E F)⟩,
        ⟨w.proj.2, (w.snd.comp c.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ E F)⟩) := by
    change cotangentProductModelHomeomorph (OrthogonalSphere p) (OrthogonalSphere q)
      ((cotangentLinearModelHomeomorph c.symm X).symm w) = _
    rw [hinverse]
    rfl
  have hre : c u =
      (WithLp.toLp 2 (fun i ↦ ((C z).1 i).re), WithLp.toLp 2 (fun i ↦ ((C z).2 i).re)) := by
    apply Prod.ext <;> ext i <;> rfl
  have him : c v =
      (WithLp.toLp 2 (fun i ↦ ((C z).1 i).im), WithLp.toLp 2 (fun i ↦ ((C z).2 i).im)) := by
    apply Prod.ext <;> ext i <;> rfl
  have hinner (w : E × F) : inner ℝ v (c.symm w) =
      inner ℝ (c v).1 w.1 + inner ℝ (c v).2 w.2 := by
    simp only [R, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
    rw [Fin.sum_univ_add]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _
      have hi := congrArg (fun y : E × F ↦ y.1 i) (c.apply_symm_apply w)
      change (c.symm w) (Fin.castAdd q i) = w.1 i at hi
      change (c.symm w) (Fin.castAdd q i) * v (Fin.castAdd q i) =
        w.1 i * v (Fin.castAdd q i)
      rw [hi]
    · apply Finset.sum_congr rfl
      intro i _
      have hi := congrArg (fun y : E × F ↦ y.2 i) (c.apply_symm_apply w)
      change (c.symm w) (Fin.natAdd p i) = w.2 i at hi
      change (c.symm w) (Fin.natAdd p i) * v (Fin.natAdd p i) =
        w.2 i * v (Fin.natAdd p i)
      rw [hi]
  -- The fixed cotangent splitting cancels exactly the same real coordinate concatenation.
  dsimp only
  rw [hsplit, hξ, orthogonalSphereCotangentChart_apply, orthogonalSphereCotangentChart_apply]
  dsimp only
  apply Prod.ext
  · apply congrArg (TotalSpace.mk ((D u).val.1))
    apply ContinuousLinearMap.ext
    intro w
    change inner ℝ v (mfderiv K K b (D u).val (c.symm (w, 0))) =
      inner ℝ (c v).1 (mfderiv (𝓡 p) (𝓡 p) e (D u).val.1 w)
    rw [hDbK (D u).val hx]
    change inner ℝ v (c.symm
      (((mfderiv (𝓡 p) (𝓡 p) e (D u).val.1).prodMap
        (mfderiv (𝓡 q) (𝓡 q) f (D u).val.2)) (c (c.symm (w, 0))))) = _
    rw [c.apply_symm_apply, hinner]
    change inner ℝ (c v).1 ((mfderiv (𝓡 p) (𝓡 p) e (D u).val.1) w) +
      inner ℝ (c v).2 ((mfderiv (𝓡 q) (𝓡 q) f (D u).val.2) 0) = _
    rw [map_zero, inner_zero_right, add_zero]
  · apply congrArg (TotalSpace.mk ((D u).val.2))
    apply ContinuousLinearMap.ext
    intro w
    change inner ℝ v (mfderiv K K b (D u).val (c.symm (0, w))) =
      inner ℝ (c v).2 (mfderiv (𝓡 q) (𝓡 q) f (D u).val.2 w)
    rw [hDbK (D u).val hx]
    change inner ℝ v (c.symm
      (((mfderiv (𝓡 p) (𝓡 p) e (D u).val.1).prodMap
        (mfderiv (𝓡 q) (𝓡 q) f (D u).val.2)) (c (c.symm (0, w))))) = _
    rw [c.apply_symm_apply, hinner]
    change inner ℝ (c v).1 ((mfderiv (𝓡 p) (𝓡 p) e (D u).val.1) 0) +
      inner ℝ (c v).2 ((mfderiv (𝓡 q) (𝓡 q) f (D u).val.2) w) = _
    rw [map_zero, inner_zero_right, zero_add]

end AtiyahSinger
