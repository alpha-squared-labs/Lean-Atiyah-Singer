/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentModelChange
public import AtiyahSinger.Geometry.EquivariantCotangentAction
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Cotangent bundles of products with separate group actions

Public module ID: M1155.

The canonical splitting of the original product cotangent bundle restricts a
covector to the two tangent factors. Its inverse adds the two covectors. Both
total spaces keep their native dual tangent bundle topologies. The second
homeomorphism first undoes the fixed Euclidean coordinate change
`EuclideanSpace.finAddEquivProd.symm`; it therefore applies to the same
`n + m` dimensional manifold model required by the analytic index.

The separate actions of `G` and `H` are restricted along the two continuous
group projections before forming the diagonal product action. Equivariance
uses the actual inverse-differential cotangent lifts on all three manifolds.
No compactness, fixed bundle rank, metric, orientation, positive dimension,
or index product formula is assumed by these geometric constructions.

Sources: Atiyah--Singer, The index of elliptic operators I, section 4,
pp. 504--505, the different-group external product; SG III.1 and III.3 for
cotangent coordinate covariance. The explicit model and topology comparisons
are the differential-geometric bookkeeping required by that product.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n m : ℕ} (M N : Type*)
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]

/-- Product charts followed by the fixed concatenation of Euclidean coordinates. -/
@[instance_reducible]
def euclideanProductChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + m))) (M × N) := by
  letI : ChartedSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) (M × N) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin m)) N
  exact linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm (M × N)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]

set_option linter.defProp false in
/-- Reuse the product and linear-coordinate-change manifold certificates for this atlas. -/
@[instance_reducible]
def isManifold_euclideanProductChartedSpace :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ (M × N) := by
  let : ChartedSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) (M × N) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin m)) N
  let : IsManifold
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ∞ (M × N) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) M N
  exact isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm (M × N)

/-- Restrict a product tangent covector to the two factors; add them for the inverse. -/
def cotangentProductModelEquiv :
    letI : ChartedSpace
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) (M × N) :=
      prodChartedSpace (EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin m)) N
    TotalSpace ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ)
        (fun x : M × N ↦
          TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) x →L[ℝ] ℝ) ≃
      CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N) := by
  letI : ChartedSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) (M × N) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin m)) N
  exact
    { toFun := fun z ↦
        (⟨z.proj.1, z.snd.comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin m)))⟩,
        ⟨z.proj.2, z.snd.comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin m)))⟩)
      invFun := fun z ↦ ⟨(z.1.proj, z.2.proj), z.1.snd.coprod z.2.snd⟩
      left_inv := by
        rintro ⟨⟨x, y⟩, ξ⟩
        apply congrArg (TotalSpace.mk (x, y))
        exact ContinuousLinearMap.coprod_comp_inl_inr
          (R := ℝ) (M := EuclideanSpace ℝ (Fin n))
          (M₁ := EuclideanSpace ℝ (Fin m)) (M₂ := ℝ) ξ
      right_inv := by
        rintro ⟨⟨x, ξ⟩, ⟨y, η⟩⟩
        apply Prod.ext
        · apply congrArg (TotalSpace.mk x)
          apply ContinuousLinearMap.ext
          intro v
          change ξ v + η 0 = ξ v
          simp
        · apply congrArg (TotalSpace.mk y)
          apply ContinuousLinearMap.ext
          intro w
          change ξ 0 + η w = η w
          simp }

include hM hN in
/-- Restriction and addition of covectors are continuous in the original bundle topologies. -/
theorem continuous_cotangentProductModelEquiv :
    letI : ChartedSpace
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) (M × N) :=
      prodChartedSpace (EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin m)) N
    letI : IsManifold
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ∞ (M × N) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) M N
    Continuous (cotangentProductModelEquiv (n := n) (m := m) M N) ∧
      Continuous (cotangentProductModelEquiv (n := n) (m := m) M N).symm := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin m)
  let I := 𝓘(ℝ, E)
  let J := 𝓘(ℝ, F)
  let P := 𝓘(ℝ, E × F)
  let : ChartedSpace (E × F) (M × N) := prodChartedSpace E M F N
  let : IsManifold 𝓘(ℝ, E × F) ∞ (M × N) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod M N
  let source := TotalSpace ((E × F) →L[ℝ] ℝ)
    (fun p : M × N ↦ TangentSpace P p →L[ℝ] ℝ)
  constructor
  · apply Continuous.prodMk
    · apply continuous_iff_continuousAt.mpr
      intro z₀
      let a := trivializationAt (E × F) (TangentSpace P) z₀.proj
      let b := trivializationAt E (TangentSpace I) z₀.proj.1
      have hz := (continuousAt_hom_bundle (RingHom.id ℝ)
        (fun z : source ↦ z) (x₀ := z₀)).mp continuousAt_id
      have hξ : ContinuousAt (fun z : source ↦ z.snd.comp (a.symmL ℝ z.proj)) z₀ := by
        have h := hz.2
        change ContinuousAt (fun z : source ↦
          ((Bundle.Trivial.trivialization (M × N) ℝ).continuousLinearMapAt ℝ z.proj).comp
            (z.snd.comp (a.symmL ℝ z.proj))) z₀ at h
        simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
          ContinuousLinearMap.id_comp] using h
      -- Differentiate the first-factor insertion while retaining the other base point.
      have hf : ContMDiffAt (P.prod I) P ∞
          (fun q : (M × N) × M ↦ (q.2, q.1.2)) (z₀.proj, z₀.proj.1) :=
        by
          simp only [P, modelWithCornersSelf_prod]
          exact contMDiffAt_snd.prodMk contMDiffAt_fst.snd
      have hg : ContMDiffAt P I ∞ (Prod.fst : M × N → M) z₀.proj := by
        simp only [P, modelWithCornersSelf_prod]
        exact contMDiffAt_fst
      have hd := (ContMDiffAt.mfderiv
        (fun p : M × N ↦ fun x : M ↦ (x, p.2)) Prod.fst hf hg
        (by simp)).continuousAt.comp hz.1
      apply (continuousAt_hom_bundle (RingHom.id ℝ) _).mpr
      refine ⟨hz.1.fst, ?_⟩
      apply (hξ.clm_comp hd).congr_of_eventuallyEq
      filter_upwards [hz.1.preimage_mem_nhds
        (a.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ z₀.proj))] with z hz'
      apply ContinuousLinearMap.ext
      intro v
      have hscalar :
          (trivializationAt ℝ (fun _ : M ↦ ℝ) z₀.proj.1).continuousLinearMapAt ℝ
            z.proj.1 = ContinuousLinearMap.id ℝ ℝ := by
        change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ _ = _
        exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
      simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
        Function.comp_apply, ContinuousLinearMap.comp_apply, hscalar,
        ContinuousLinearMap.id_apply]
      change z.snd ((ContinuousLinearMap.inl ℝ E F) (b.symmL ℝ z.proj.1 v)) =
        z.snd (a.symmL ℝ z.proj (a.continuousLinearMapAt ℝ z.proj
          ((mfderiv I P (fun x : M ↦ (x, z.proj.2)) z.proj.1)
            (b.symmL ℝ z.proj.1 v))))
      erw [a.symmL_continuousLinearMapAt (R := ℝ) hz']
      have hi : mfderiv I P (fun x : M ↦ (x, z.proj.2)) z.proj.1 =
          ContinuousLinearMap.inl ℝ E F := by
        change mfderiv I 𝓘(ℝ, E × F) _ _ = _
        rw [modelWithCornersSelf_prod]
        exact mfderiv_prod_left
      rw [hi]
      rfl
    · apply continuous_iff_continuousAt.mpr
      intro z₀
      let a := trivializationAt (E × F) (TangentSpace P) z₀.proj
      let b := trivializationAt F (TangentSpace J) z₀.proj.2
      have hz := (continuousAt_hom_bundle (RingHom.id ℝ)
        (fun z : source ↦ z) (x₀ := z₀)).mp continuousAt_id
      have hξ : ContinuousAt (fun z : source ↦ z.snd.comp (a.symmL ℝ z.proj)) z₀ := by
        have h := hz.2
        change ContinuousAt (fun z : source ↦
          ((Bundle.Trivial.trivialization (M × N) ℝ).continuousLinearMapAt ℝ z.proj).comp
            (z.snd.comp (a.symmL ℝ z.proj))) z₀ at h
        simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
          ContinuousLinearMap.id_comp] using h
      -- Differentiate the second-factor insertion while retaining the other base point.
      have hf : ContMDiffAt (P.prod J) P ∞
          (fun q : (M × N) × N ↦ (q.1.1, q.2)) (z₀.proj, z₀.proj.2) :=
        by
          simp only [P, modelWithCornersSelf_prod]
          exact contMDiffAt_fst.fst.prodMk contMDiffAt_snd
      have hg : ContMDiffAt P J ∞ (Prod.snd : M × N → N) z₀.proj := by
        simp only [P, modelWithCornersSelf_prod]
        exact contMDiffAt_snd
      have hd := (ContMDiffAt.mfderiv
        (fun p : M × N ↦ fun y : N ↦ (p.1, y)) Prod.snd hf hg
        (by simp)).continuousAt.comp hz.1
      apply (continuousAt_hom_bundle (RingHom.id ℝ) _).mpr
      refine ⟨hz.1.snd, ?_⟩
      apply (hξ.clm_comp hd).congr_of_eventuallyEq
      filter_upwards [hz.1.preimage_mem_nhds
        (a.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ z₀.proj))] with z hz'
      apply ContinuousLinearMap.ext
      intro v
      have hscalar :
          (trivializationAt ℝ (fun _ : N ↦ ℝ) z₀.proj.2).continuousLinearMapAt ℝ
            z.proj.2 = ContinuousLinearMap.id ℝ ℝ := by
        change (Bundle.Trivial.trivialization N ℝ).continuousLinearMapAt ℝ _ = _
        exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
      simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
        Function.comp_apply, ContinuousLinearMap.comp_apply, hscalar,
        ContinuousLinearMap.id_apply]
      change z.snd ((ContinuousLinearMap.inr ℝ E F) (b.symmL ℝ z.proj.2 v)) =
        z.snd (a.symmL ℝ z.proj (a.continuousLinearMapAt ℝ z.proj
          ((mfderiv J P (fun y : N ↦ (z.proj.1, y)) z.proj.2)
            (b.symmL ℝ z.proj.2 v))))
      erw [a.symmL_continuousLinearMapAt (R := ℝ) hz']
      have hi : mfderiv J P (fun y : N ↦ (z.proj.1, y)) z.proj.2 =
          ContinuousLinearMap.inr ℝ E F := by
        change mfderiv J 𝓘(ℝ, E × F) _ _ = _
        rw [modelWithCornersSelf_prod]
        exact mfderiv_prod_right
      rw [hi]
      rfl
  · apply continuous_iff_continuousAt.mpr
    intro z₀
    let target := CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N)
    let a := trivializationAt E (TangentSpace I) z₀.1.proj
    let b := trivializationAt F (TangentSpace J) z₀.2.proj
    let c := trivializationAt (E × F) (TangentSpace P) (z₀.1.proj, z₀.2.proj)
    have hx := (continuousAt_hom_bundle (RingHom.id ℝ)
      (fun z : target ↦ z.1) (x₀ := z₀)).mp continuousAt_fst
    have hy := (continuousAt_hom_bundle (RingHom.id ℝ)
      (fun z : target ↦ z.2) (x₀ := z₀)).mp continuousAt_snd
    have hbase := hx.1.prodMk hy.1
    have hξ : ContinuousAt (fun z : target ↦ z.1.snd.comp (a.symmL ℝ z.1.proj)) z₀ := by
      have h := hx.2
      change ContinuousAt (fun z : target ↦
        ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ z.1.proj).comp
          (z.1.snd.comp (a.symmL ℝ z.1.proj))) z₀ at h
      simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
        ContinuousLinearMap.id_comp] using h
    have hη : ContinuousAt (fun z : target ↦ z.2.snd.comp (b.symmL ℝ z.2.proj)) z₀ := by
      have h := hy.2
      change ContinuousAt (fun z : target ↦
        ((Bundle.Trivial.trivialization N ℝ).continuousLinearMapAt ℝ z.2.proj).comp
          (z.2.snd.comp (b.symmL ℝ z.2.proj))) z₀ at h
      simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
        ContinuousLinearMap.id_comp] using h
    -- The inverse adds the pullbacks by the two actual product projections.
    have hf : ContMDiffAt P I ∞ (Prod.fst : M × N → M) (z₀.1.proj, z₀.2.proj) := by
      simp only [P, modelWithCornersSelf_prod]
      exact contMDiffAt_fst
    have hg : ContMDiffAt P J ∞ (Prod.snd : M × N → N) (z₀.1.proj, z₀.2.proj) := by
      simp only [P, modelWithCornersSelf_prod]
      exact contMDiffAt_snd
    have hd₁ := (hf.mfderiv_const (m := (∞ : WithTop ℕ∞)) (by simp)).continuousAt.comp
      (f := fun z : target ↦ (z.1.proj, z.2.proj)) hbase
    have hd₂ := (hg.mfderiv_const (m := (∞ : WithTop ℕ∞)) (by simp)).continuousAt.comp
      (f := fun z : target ↦ (z.1.proj, z.2.proj)) hbase
    apply (continuousAt_hom_bundle (RingHom.id ℝ) _).mpr
    refine ⟨hbase, ?_⟩
    apply ((hξ.clm_comp hd₁).add (hη.clm_comp hd₂)).congr_of_eventuallyEq
    filter_upwards [hx.1.preimage_mem_nhds
      (a.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ z₀.1.proj)),
      hy.1.preimage_mem_nhds
      (b.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ z₀.2.proj))] with z hx' hy'
    apply ContinuousLinearMap.ext
    intro v
    have hscalar :
        (trivializationAt ℝ (fun _ : M × N ↦ ℝ) (z₀.1.proj, z₀.2.proj)).continuousLinearMapAt
          ℝ (z.1.proj, z.2.proj) = ContinuousLinearMap.id ℝ ℝ := by
      change (Bundle.Trivial.trivialization (M × N) ℝ).continuousLinearMapAt ℝ _ = _
      exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
    change (trivializationAt ℝ (fun _ : M × N ↦ ℝ)
        (z₀.1.proj, z₀.2.proj)).continuousLinearMapAt ℝ (z.1.proj, z.2.proj)
      ((z.1.snd.coprod z.2.snd) (c.symmL ℝ (z.1.proj, z.2.proj) v)) = _
    rw [hscalar, ContinuousLinearMap.id_apply]
    simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      Function.comp_apply, ContinuousLinearMap.comp_apply, Pi.add_apply, add_apply]
    change (z.1.snd.coprod z.2.snd) (c.symmL ℝ (z.1.proj, z.2.proj) v) =
      z.1.snd (a.symmL ℝ z.1.proj (a.continuousLinearMapAt ℝ z.1.proj
        ((mfderiv P I (Prod.fst : M × N → M) (z.1.proj, z.2.proj))
          (c.symmL ℝ (z.1.proj, z.2.proj) v)))) +
      z.2.snd (b.symmL ℝ z.2.proj (b.continuousLinearMapAt ℝ z.2.proj
        ((mfderiv P J (Prod.snd : M × N → N) (z.1.proj, z.2.proj))
          (c.symmL ℝ (z.1.proj, z.2.proj) v))))
    erw [a.symmL_continuousLinearMapAt (R := ℝ) hx',
      b.symmL_continuousLinearMapAt (R := ℝ) hy']
    have hd₁' : mfderiv P I (Prod.fst : M × N → M) (z.1.proj, z.2.proj) =
        ContinuousLinearMap.fst ℝ E F := by
      change mfderiv 𝓘(ℝ, E × F) I _ _ = _
      rw [modelWithCornersSelf_prod]
      exact mfderiv_fst
    have hd₂' : mfderiv P J (Prod.snd : M × N → N) (z.1.proj, z.2.proj) =
        ContinuousLinearMap.snd ℝ E F := by
      change mfderiv 𝓘(ℝ, E × F) J _ _ = _
      rw [modelWithCornersSelf_prod]
      exact mfderiv_snd
    rw [hd₁', hd₂']
    rfl

/-- The canonical splitting with its exact restriction and coprod formulas. -/
def cotangentProductModelHomeomorph :
    letI : ChartedSpace
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) (M × N) :=
      prodChartedSpace (EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin m)) N
    letI : IsManifold
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ∞ (M × N) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) M N
    TotalSpace ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ)
        (fun x : M × N ↦
          TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) x →L[ℝ] ℝ) ≃ₜ
      CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N) := by
  letI : ChartedSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) (M × N) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin m)) N
  letI : IsManifold
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ∞ (M × N) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) M N
  exact
    { toEquiv := cotangentProductModelEquiv (n := n) (m := m) M N
      continuous_toFun := (continuous_cotangentProductModelEquiv (n := n) (m := m) M N).1
      continuous_invFun := (continuous_cotangentProductModelEquiv (n := n) (m := m) M N).2 }

/-- Split the actual cotangent of the concatenated Euclidean product atlas. -/
def cotangentProductHomeomorph :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    CotangentTotalSpace (n := n + m) (M := M × N) ≃ₜ
      CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N) := by
  letI : ChartedSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) (M × N) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin m)) N
  letI : IsManifold
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ∞ (M × N) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) M N
  letI := euclideanProductChartedSpace (n := n) (m := m) M N
  letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  exact (cotangentLinearModelHomeomorph
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm (M × N)).symm.trans
    (cotangentProductModelHomeomorph (n := n) (m := m) M N)

variable {VG VH G H : Type*}
  [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [NormedAddCommGroup VH] [NormedSpace ℝ VH]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace VH H]
  [MulAction G M] [ContinuousSMul G M] [MulAction H N] [ContinuousSMul H N]
  [hActionG : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [hActionH : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ H N]

include hM hN hActionG hActionH in
/-- The separate product action is smooth in the specified concatenated Euclidean atlas. -/
theorem contMDiffSMul_euclideanProduct :
    letI : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
    letI : MulAction (G × H) M :=
      MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) M :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) N :=
      MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) N :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    ContMDiffSMul 𝓘(ℝ, VG × VH)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ (G × H) (M × N) := by
  let : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
  let : MulAction (G × H) M :=
    MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) M :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) N :=
    MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) N :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let P := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)
  let : ChartedSpace P (M × N) := prodChartedSpace _ M _ N
  let : IsManifold 𝓘(ℝ, P) ∞ (M × N) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod M N
  -- Form the separate action in the original product atlas.
  have hact : ContMDiff (𝓘(ℝ, VG × VH).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun q : (G × H) × (M × N) ↦ (q.1.1 • q.2.1, q.1.2 • q.2.2)) := by
    simp only [P, modelWithCornersSelf_prod]
    exact (contMDiff_fst.fst.smul contMDiff_snd.fst).prodMk
      (contMDiff_fst.snd.smul contMDiff_snd.snd)
  -- Conjugate the source and target charts by the same fixed linear equivalence.
  let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  have hchange := contMDiff_mfderiv_linearModelId e (M × N)
  constructor
  exact hchange.1.1.comp (hact.comp
    (contMDiff_fst.prodMk (hchange.1.2.comp contMDiff_snd)))


include hActionG hActionH in
/-- Splitting the native cotangent product intertwines the actual separate cotangent actions. -/
theorem cotangentProductHomeomorph_equivariant :
    letI : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
    letI : MulAction (G × H) M :=
      MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) M :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) N :=
      MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) N :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := contMDiffSMul_euclideanProduct (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N
    letI := smoothCotangentMulAction (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    letI : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
      MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : MulAction (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
      MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
    ∀ (gh : G × H) (z : CotangentTotalSpace (n := n + m) (M := M × N)),
      cotangentProductHomeomorph (n := n) (m := m) M N (gh • z) =
        gh • cotangentProductHomeomorph (n := n) (m := m) M N z := by
  classical
  let : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
  let : MulAction (G × H) M :=
    MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) M :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) N :=
    MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) N :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin m)
  let I := 𝓘(ℝ, E)
  let J := 𝓘(ℝ, F)
  let P := 𝓘(ℝ, E × F)
  let K := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m)))
  let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
  let : ChartedSpace (E × F) (M × N) := prodChartedSpace E M F N
  let : IsManifold P ∞ (M × N) := by
    simp only [P, modelWithCornersSelf_prod]
    exact IsManifold.prod M N
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := contMDiffSMul_euclideanProduct (n := n) (m := m)
    (VG := VG) (VH := VH) (G := G) (H := H) M N
  let := smoothCotangentMulAction (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
  let : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
  let : MulAction (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
  intro gh z
  -- Recover the exact inverse-dual formula of the chosen model homeomorphism.
  have hinverse (w : CotangentTotalSpace (n := n + m) (M := M × N)) :
      (cotangentLinearModelHomeomorph e (M × N)).symm w =
        ⟨w.proj, w.snd.comp e.toContinuousLinearMap⟩ := by
    apply (cotangentLinearModelHomeomorph e (M × N)).injective
    rw [Homeomorph.apply_symm_apply]
    change w = ⟨w.proj, (w.snd.comp e.toContinuousLinearMap).comp
      e.symm.toContinuousLinearMap⟩
    cases w with
    | mk p ξ =>
      apply congrArg (TotalSpace.mk p)
      apply ContinuousLinearMap.ext
      intro v
      exact (congrArg ξ (e.apply_symm_apply v)).symm
  have hsplit (w : CotangentTotalSpace (n := n + m) (M := M × N)) :
      cotangentProductHomeomorph (n := n) (m := m) M N w =
        (⟨w.proj.1, (w.snd.comp e.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ E F)⟩,
        ⟨w.proj.2, (w.snd.comp e.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ E F)⟩) := by
    change cotangentProductModelHomeomorph (n := n) (m := m) M N
      ((cotangentLinearModelHomeomorph e (M × N)).symm w) = _
    rw [hinverse]
    rfl
  let dG := Diffeomorph.smul (M := M) 𝓘(ℝ, VG) I ∞ gh.1
  let dH := Diffeomorph.smul (M := N) 𝓘(ℝ, VH) J ∞ gh.2
  let f : M × N → M × N := Prod.map dG.symm dH.symm
  have hf : MDifferentiable P P f := by
    simp only [P, modelWithCornersSelf_prod]
    exact dG.symm.mdifferentiable (by simp) |>.prodMap (dH.symm.mdifferentiable (by simp))
  have hchange := contMDiff_mfderiv_linearModelId e (M × N)
  -- The inverse action derivative is the conjugate of its two diagonal blocks.
  have hderiv (p : M × N) : mfderiv K K f p =
      e.toContinuousLinearMap.comp
        (((mfderiv I I dG.symm p.1).prodMap (mfderiv J J dH.symm p.2)).comp
          e.symm.toContinuousLinearMap) := by
    have h₁ := mfderiv_comp p (hf p)
      (hchange.1.2.mdifferentiable (by simp) p)
    have h₂ := mfderiv_comp p
      (hchange.1.1.mdifferentiable (by simp) (f p))
      ((hf p).comp p (hchange.1.2.mdifferentiable (by simp) p))
    change mfderiv K P f p = (mfderiv P P f p).comp (mfderiv K P id p) at h₁
    change mfderiv K K f p = _ at h₂
    erw [h₂, h₁, hchange.2.1, hchange.2.2]
    have hprod : mfderiv P P f p =
        (mfderiv I I dG.symm p.1).prodMap (mfderiv J J dH.symm p.2) := by
      simp only [P]
      exact mfderiv_prodMap (dG.symm.mdifferentiable (by simp) p.1)
        (dH.symm.mdifferentiable (by simp) p.2)
    rw [hprod]
    rfl
  rw [hsplit, hsplit]
  apply Prod.ext
  · apply congrArg (TotalSpace.mk (gh.1 • z.proj.1))
    apply ContinuousLinearMap.ext
    intro v
    change z.snd ((mfderiv K K f (gh • z.proj))
      (e ((ContinuousLinearMap.inl ℝ E F) v))) =
      z.snd (e ((ContinuousLinearMap.inl ℝ E F)
        ((mfderiv I I dG.symm (gh.1 • z.proj.1)) v)))
    rw [hderiv]
    change z.snd (e (((mfderiv I I dG.symm (gh.1 • z.proj.1)).prodMap
      (mfderiv J J dH.symm (gh.2 • z.proj.2))) (e.symm (e (v, 0))))) = _
    rw [e.symm_apply_apply]
    change z.snd (e (((mfderiv I I dG.symm (gh.1 • z.proj.1)) v),
      ((mfderiv J J dH.symm (gh.2 • z.proj.2)) 0))) =
      z.snd (e (((mfderiv I I dG.symm (gh.1 • z.proj.1)) v), 0))
    rw [map_zero]
    rfl
  · apply congrArg (TotalSpace.mk (gh.2 • z.proj.2))
    apply ContinuousLinearMap.ext
    intro v
    change z.snd ((mfderiv K K f (gh • z.proj))
      (e ((ContinuousLinearMap.inr ℝ E F) v))) =
      z.snd (e ((ContinuousLinearMap.inr ℝ E F)
        ((mfderiv J J dH.symm (gh.2 • z.proj.2)) v)))
    rw [hderiv]
    change z.snd (e (((mfderiv I I dG.symm (gh.1 • z.proj.1)).prodMap
      (mfderiv J J dH.symm (gh.2 • z.proj.2))) (e.symm (e (0, v))))) = _
    rw [e.symm_apply_apply]
    change z.snd (e (((mfderiv I I dG.symm (gh.1 • z.proj.1)) 0),
      ((mfderiv J J dH.symm (gh.2 • z.proj.2)) v))) =
      z.snd (e (0, ((mfderiv J J dH.symm (gh.2 • z.proj.2)) v)))
    rw [map_zero]
    rfl

end AtiyahSinger
