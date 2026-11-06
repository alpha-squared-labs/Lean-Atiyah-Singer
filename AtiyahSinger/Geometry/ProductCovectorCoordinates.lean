/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSymbol
public import AtiyahSinger.Geometry.CotangentProduct

/-!
# Covector coordinates in the fixed product atlas

Public module ID: M1348.

The native cotangent splitting and the concatenated product chart use the same
linear maps. In particular their frequency coordinates split into the two
original chart coordinates. This is the geometric comparison needed to identify
the global symbols of the actual product-frequency cutoff PDOs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]

/-- The native cotangent splitting restricts along the fixed two tangent inclusions. -/
theorem cotangentProductHomeomorph_apply :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    ∀ z : CotangentTotalSpace (n := n + m) (M := M × N),
      cotangentProductHomeomorph (n := n) (m := m) M N z =
        (⟨z.proj.1, (z.snd.comp EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin m)))⟩,
        ⟨z.proj.2, (z.snd.comp EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin m)))⟩) := by
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let : ChartedSpace (X × Y) (M × N) := prodChartedSpace X M Y N
  let : IsManifold 𝓘(ℝ, X × Y) ∞ (M × N) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod M N
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
  intro z
  -- Undo precisely the linear model change used in the original homeomorphism.
  have hinverse : (cotangentLinearModelHomeomorph e (M × N)).symm z =
      ⟨z.proj, z.snd.comp e.toContinuousLinearMap⟩ := by
    apply (cotangentLinearModelHomeomorph e (M × N)).injective
    rw [Homeomorph.apply_symm_apply]
    change z = ⟨z.proj, (z.snd.comp e.toContinuousLinearMap).comp
      e.symm.toContinuousLinearMap⟩
    cases z with
    | mk p ξ =>
      apply congrArg (TotalSpace.mk p)
      apply ContinuousLinearMap.ext
      intro v
      exact (congrArg ξ (e.apply_symm_apply v)).symm
  change cotangentProductModelHomeomorph (n := n) (m := m) M N
    ((cotangentLinearModelHomeomorph e (M × N)).symm z) = _
  rw [hinverse]
  rfl

/-- A covector in the concatenated product chart has the two original factor coordinates. -/
theorem covectorInChart_product
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (d : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)))
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin m)) N) (x : M) (y : N)
    (hx : x ∈ c.source) (hy : y ∈ d.source) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    ∀ ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) (x, y) →L[ℝ] ℝ,
      e (covectorInChart ((c.prod d).trans e.symm.toHomeomorph.toOpenPartialHomeomorph)
        (x, y) ξ) =
      (covectorInChart c x ((ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))),
      covectorInChart d y ((ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))))) := by
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let Z := EuclideanSpace ℝ (Fin (n + m))
  let I := 𝓘(ℝ, X)
  let J := 𝓘(ℝ, Y)
  let P := 𝓘(ℝ, X × Y)
  let K := 𝓘(ℝ, Z)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let : ChartedSpace (X × Y) (M × N) := prodChartedSpace X M Y N
  let : IsManifold P ∞ (M × N) := by
    simp only [P, modelWithCornersSelf_prod]
    exact IsManifold.prod M N
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  dsimp only
  intro ξ
  let q := (c.prod d).trans e.symm.toHomeomorph.toOpenPartialHomeomorph
  let a := mfderiv I I c.symm (c x)
  let b := mfderiv J J d.symm (d y)
  have hc' := mdifferentiableAt_atlas_symm (I := I) hc (c.map_source hx)
  have hd' := mdifferentiableAt_atlas_symm (I := J) hd (d.map_source hy)
  have hf : MDifferentiableAt P P (Prod.map c.symm d.symm) (c x, d y) := by
    dsimp only [P]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hc'.prodMap hd'
  have hchange := contMDiff_mfderiv_linearModelId e.symm (M × N)
  -- Differentiate the inverse product chart through the same two model changes.
  have hderiv : mfderiv K K q.symm (q (x, y)) =
      e.symm.toContinuousLinearMap.comp ((a.prodMap b).comp e.toContinuousLinearMap) := by
    have he : MDifferentiableAt K P e (e.symm (c x, d y)) :=
      e.toContinuousLinearMap.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
    have hf' : MDifferentiableAt P P (Prod.map c.symm d.symm)
        (e (e.symm (c x, d y))) := by
      simpa only [e.apply_symm_apply] using hf
    have hcomp := mfderiv_comp (e.symm (c x, d y)) hf' he
    have hcomp' := mfderiv_comp (e.symm (c x, d y))
      (hchange.1.1.mdifferentiable (by simp) _)
      (hf'.comp _ he)
    change mfderiv K K q.symm (q (x, y)) = _ at hcomp'
    rw [hcomp', hcomp, hchange.2.1]
    have hederiv : mfderiv K P e (e.symm (c x, d y)) = e.toContinuousLinearMap := by
      exact e.toContinuousLinearMap.hasFDerivAt.hasMFDerivAt.mfderiv
    rw [hederiv, e.apply_symm_apply]
    have hprod : mfderiv P P (Prod.map c.symm d.symm) (c x, d y) = a.prodMap b := by
      dsimp only [P]
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact mfderiv_prodMap hc' hd'
    rw [hprod]
  -- Coordinate concatenation sends the original basis vectors to the two summands.
  have hinl (i : Fin n) : e (EuclideanSpace.single (Fin.castAdd m i) 1) =
      (EuclideanSpace.single i 1, 0) := by
    apply Prod.ext
    · ext j
      change EuclideanSpace.single (Fin.castAdd m i) (1 : ℝ) (Fin.castAdd m j) = _
      simp
    · ext j
      change EuclideanSpace.single (Fin.castAdd m i) (1 : ℝ) (Fin.natAdd n j) = _
      simp only [PiLp.single_apply, PiLp.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      omega
  have hinr (j : Fin m) : e (EuclideanSpace.single (Fin.natAdd n j) 1) =
      (0, EuclideanSpace.single j 1) := by
    apply Prod.ext
    · ext i
      change EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ) (Fin.castAdd m i) = _
      simp only [PiLp.single_apply, PiLp.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      omega
    · ext i
      change EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ) (Fin.natAdd n i) = _
      simp
  apply Prod.ext
  · ext i
    change ξ ((mfderiv K K q.symm (q (x, y)))
      (EuclideanSpace.single (Fin.castAdd m i) 1)) =
        ξ (e.symm (a (EuclideanSpace.single i 1), 0))
    rw [hderiv]
    change ξ (e.symm ((a.prodMap b) (e (EuclideanSpace.single (Fin.castAdd m i) 1)))) = _
    rw [hinl]
    simp
  · ext j
    change ξ ((mfderiv K K q.symm (q (x, y)))
      (EuclideanSpace.single (Fin.natAdd n j) 1)) =
        ξ (e.symm (0, b (EuclideanSpace.single j 1)))
    rw [hderiv]
    change ξ (e.symm ((a.prodMap b) (e (EuclideanSpace.single (Fin.natAdd n j) 1)))) = _
    rw [hinr]
    simp

end AtiyahSinger
