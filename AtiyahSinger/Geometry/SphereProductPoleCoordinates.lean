/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.OrthogonalDirectSum
public import AtiyahSinger.Geometry.CotangentProduct
public import AtiyahSinger.Geometry.SphereCotangentCoordinates

/-!
# The actual common Euclidean open in a product of native spheres

Public module ID: M1438.

The ordered Euclidean coordinate splitting followed by the two specified
inverse pole charts parametrizes an actual open subset of the compact product.
The codomain keeps `euclideanProductChartedSpace`, the atlas used by the
analytic external product. Neither compact ambient manifold is replaced.

Source: ASI I Proposition (4.4), pp.504--505. The explicit atlas comparison
is the project supplement needed for the inverse-dual cotangent excision map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open TopologicalSpace
open scoped Manifold ContDiff

/-- The product of the two actual selected pole chart images. -/
def orthogonalSphereProductPoleOpen (p q : ℕ) (atInfinity : Bool) :
    Opens (OrthogonalSphere p × OrthogonalSphere q) :=
  ⟨(orthogonalSphereNormalizedChart p atInfinity).source ×ˢ
      (orthogonalSphereNormalizedChart q atInfinity).source,
    (orthogonalSphereNormalizedChart p atInfinity).open_source.prod
      (orthogonalSphereNormalizedChart q atInfinity).open_source⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified ordered common Euclidean source in the native compact-product atlas. -/
def orthogonalSphereProductPoleDiffeomorph (p q : ℕ) (atInfinity : Bool) :
    letI := euclideanProductChartedSpace (n := p) (m := q)
      (OrthogonalSphere p) (OrthogonalSphere q)
    EuclideanSpace ℝ (Fin (p + q)) ≃ₘ⟮𝓡 (p + q), 𝓡 (p + q)⟯
      orthogonalSphereProductPoleOpen p q atInfinity := by
  let E := EuclideanSpace ℝ (Fin p)
  let F := EuclideanSpace ℝ (Fin q)
  let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q)
  let e := orthogonalSphereNormalizedChart p atInfinity
  let f := orthogonalSphereNormalizedChart q atInfinity
  have he := orthogonalSphereNormalizedChart_smooth p atInfinity
  have hf := orthogonalSphereNormalizedChart_smooth q atInfinity
  have het : e.target = Set.univ :=
    (orthogonalSphereNormalizedChart_properties p atInfinity).2.1
  have hft : f.target = Set.univ :=
    (orthogonalSphereNormalizedChart_properties q atInfinity).2.1
  let U := orthogonalSphereProductPoleOpen p q atInfinity
  let a (u : EuclideanSpace ℝ (Fin (p + q))) : OrthogonalSphere p × OrthogonalSphere q :=
    (e.symm (c u).1, f.symm (c u).2)
  let b (x : OrthogonalSphere p × OrthogonalSphere q) : EuclideanSpace ℝ (Fin (p + q)) :=
    c.symm (e x.1, f x.2)
  letI : ChartedSpace (E × F) (OrthogonalSphere p × OrthogonalSphere q) :=
    prodChartedSpace E (OrthogonalSphere p) F (OrthogonalSphere q)
  -- First work in the ordinary product model, retaining the specified factor charts.
  have hc : ContMDiff (𝓡 (p + q)) ((𝓡 p).prod (𝓡 q)) ∞ c := by
    exact (contDiff_fst.comp c.contDiff).contMDiff.prodMk
      (contDiff_snd.comp c.contDiff).contMDiff
  have hci : ContMDiff ((𝓡 p).prod (𝓡 q)) (𝓡 (p + q)) ∞ c.symm := by
    exact c.symm.contDiff.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  have ha : ContMDiff (𝓡 (p + q)) ((𝓡 p).prod (𝓡 q)) ∞ a :=
    (he.2.comp (contMDiff_fst.comp hc)).prodMk (hf.2.comp (contMDiff_snd.comp hc))
  have hb : ContMDiffOn ((𝓡 p).prod (𝓡 q)) (𝓡 (p + q)) ∞ b U :=
    hci.comp_contMDiffOn
      ((he.1.comp contMDiffOn_fst (fun _ hx ↦ hx.1)).prodMk
        (hf.1.comp contMDiffOn_snd (fun _ hx ↦ hx.2)))
  let : IsManifold 𝓘(ℝ, E × F) ∞ (OrthogonalSphere p × OrthogonalSphere q) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 p) (I' := 𝓡 q) (OrthogonalSphere p) (OrthogonalSphere q)
  let d := linearModelDiffeomorph c.symm (OrthogonalSphere p × OrthogonalSphere q)
  -- Rechart precisely by the same finite-coordinate concatenation used by the product index.
  letI := euclideanProductChartedSpace (n := p) (m := q)
    (OrthogonalSphere p) (OrthogonalSphere q)
  have hd : ContMDiff ((𝓡 p).prod (𝓡 q)) (𝓡 (p + q)) ∞
      (id : OrthogonalSphere p × OrthogonalSphere q → _) := by
    rw [← modelWithCornersSelf_prod]
    exact d.contMDiff
  have hdi : ContMDiff (𝓡 (p + q)) ((𝓡 p).prod (𝓡 q)) ∞
      (id : OrthogonalSphere p × OrthogonalSphere q → _) := by
    rw [← modelWithCornersSelf_prod]
    exact d.symm.contMDiff
  have ha' : ContMDiff (𝓡 (p + q)) (𝓡 (p + q)) ∞ a := hd.comp ha
  have hb' : ContMDiffOn (𝓡 (p + q)) (𝓡 (p + q)) ∞ b U :=
    hb.comp hdi.contMDiffOn (fun _ hx ↦ hx)
  have ham (u : EuclideanSpace ℝ (Fin (p + q))) : a u ∈ U :=
    ⟨e.map_target (het.symm ▸ Set.mem_univ _),
      f.map_target (hft.symm ▸ Set.mem_univ _)⟩
  exact {
    toFun u := ⟨a u, ham u⟩
    invFun x := b x
    left_inv u := by
      change c.symm (e (e.symm (c u).1), f (f.symm (c u).2)) = u
      rw [e.right_inv (het.symm ▸ Set.mem_univ _),
        f.right_inv (hft.symm ▸ Set.mem_univ _), c.symm_apply_apply]
    right_inv x := by
      apply Subtype.ext
      change (e.symm (c (c.symm (e x.val.1, f x.val.2))).1,
        f.symm (c (c.symm (e x.val.1, f x.val.2))).2) = x.val
      rw [c.apply_symm_apply]
      exact Prod.ext (e.left_inv x.property.1) (f.left_inv x.property.2)
    contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff U _).mp ha'
    contMDiff_invFun := by
      intro x
      exact ((hb' x x.property).contMDiffAt (U.isOpen.mem_nhds x.property)).comp x
        (contMDiff_subtype_val (n := ∞) x) }

open scoped Matrix Matrix.Norms.L2Operator in
/-- The actual block subgroup intertwines the common-open chart with the separate sphere actions. -/
theorem orthogonalSphereProductPoleDiffeomorph_equivariant (p q : ℕ) (atInfinity : Bool)
    (g : Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
    (u : EuclideanSpace ℝ (Fin (p + q))) :
    letI := euclideanProductChartedSpace (n := p) (m := q)
      (OrthogonalSphere p) (OrthogonalSphere q)
    (orthogonalSphereProductPoleDiffeomorph p q atInfinity
      (orthogonalEuclideanIsometry (p + q) (orthogonalDirectSumInclusion p q g) u) :
        OrthogonalSphere p × OrthogonalSphere q) =
      (g.1 • (orthogonalSphereProductPoleDiffeomorph p q atInfinity u).val.1,
        g.2 • (orthogonalSphereProductPoleDiffeomorph p q atInfinity u).val.2) := by
  let := euclideanProductChartedSpace (n := p) (m := q)
    (OrthogonalSphere p) (OrthogonalSphere q)
  let C := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q)
  let e : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm
  -- The real block action uses exactly the same finite index ordering as the specified chart.
  have hcoords (w : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q))
      (i : Fin (p + q)) : C.symm w i = Sum.elim (fun j ↦ w.1 j) (fun j ↦ w.2 j) (e i) := by
    simp [C, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      LinearIsometryEquiv.piLpCongrLeft, PiLp.sumPiLpEquivProdLpPiLp,
      LinearIsometryEquiv.symm, LinearEquiv.piCongrLeft', Equiv.piCongrLeft',
      LinearEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, e]
    cases finSumFinEquiv.symm i <;> rfl
  have hblock (z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) :
      C.symm (orthogonalEuclideanIsometry p g.1 z.1, orthogonalEuclideanIsometry q g.2 z.2) =
        orthogonalEuclideanIsometry (p + q) (orthogonalDirectSumInclusion p q g) (C.symm z) := by
    have hvec : (fun j ↦ C.symm z (e.symm j)) =
        Sum.elim (fun j ↦ z.1 j) (fun j ↦ z.2 j) := by
      funext j
      rw [hcoords, e.apply_symm_apply]
    ext i
    change C.symm (orthogonalEuclideanIsometry p g.1 z.1,
        orthogonalEuclideanIsometry q g.2 z.2) i =
      ((Matrix.fromBlocks g.1.val 0 0 g.2.val).submatrix e e *ᵥ (fun j ↦ C.symm z j)) i
    rw [Matrix.submatrix_mulVec_equiv]
    change C.symm (orthogonalEuclideanIsometry p g.1 z.1,
        orthogonalEuclideanIsometry q g.2 z.2) i =
      (Matrix.fromBlocks g.1.val 0 0 g.2.val *ᵥ (fun j ↦ C.symm z (e.symm j))) (e i)
    rw [hvec, Matrix.fromBlocks_mulVec, hcoords]
    cases e i <;> simp [Function.comp_def] <;> rfl
  have hsplit : C (orthogonalEuclideanIsometry (p + q) (orthogonalDirectSumInclusion p q g) u) =
      (orthogonalEuclideanIsometry p g.1 (C u).1, orthogonalEuclideanIsometry q g.2 (C u).2) := by
    have h := congrArg C (hblock (C u))
    simpa only [C.apply_symm_apply, C.symm_apply_apply] using h.symm
  -- Apply the previously fixed equivariance of each original pole chart to these two coordinates.
  change ((orthogonalSphereNormalizedChart p atInfinity).symm
      (C (orthogonalEuclideanIsometry (p + q) (orthogonalDirectSumInclusion p q g) u)).1,
    (orthogonalSphereNormalizedChart q atInfinity).symm
      (C (orthogonalEuclideanIsometry (p + q) (orthogonalDirectSumInclusion p q g) u)).2) = _
  rw [hsplit]
  exact Prod.ext (orthogonalSpherePoleDiffeomorph_equivariant p atInfinity g.1 (C u).1)
    (orthogonalSpherePoleDiffeomorph_equivariant q atInfinity g.2 (C u).2)

end AtiyahSinger
