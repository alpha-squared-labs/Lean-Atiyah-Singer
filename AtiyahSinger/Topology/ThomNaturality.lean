/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTotalPullback
public import AtiyahSinger.Topology.CompactSupportFunctoriality
public import AtiyahSinger.Topology.HermitianMetricPullback
public import AtiyahSinger.Topology.HermitianSupportedThom

/-!
# Naturality of the specified compact-support Thom operator

Public module ID: M2250.

The comparisons retain the original supported tensor operator, the existing
homeomorphism transport and the actual proper pullback on compact-support K
theory. Bundle isomorphisms use the already defined `Iso.totalHomeomorph`.
The base-change square uses the original total-space lift `(x,v) ↦ (f(x),v)`
and the metric evaluated at exactly f(x).

Sources: Karoubi IV.1.3 and IV.1.6--1.10 for the naturality of the exterior
construction, and Spin Geometry C.1/C.13 for the supported product. The explicit
proper-map square and arbitrary-metric isomorphism comparison are standard
construction arguments recorded here as project supplements; they are not
attributed to a separately numbered lemma on those pages. Metric independence
removes an auxiliary isometry condition. Properness remains necessary for the
compact-support pullbacks, including the total-space lift.
The isomorphism and proper-map comparisons use the original supported representatives.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

section ExteriorFunctor

open Bundle

attribute [local instance] exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity

/-- Exterior functoriality preserves the actual even and odd subspaces. -/
private theorem exterior_map_mem_evenOdd {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W) (j : ZMod 2)
    (a : ExteriorAlgebra ℂ V) (ha : a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) j) :
    ExteriorAlgebra.map f a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) j := by
  induction a, ha using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow a ha =>
    fin_cases j
    · change a ∈ (CliffordAlgebra.ι (0 : QuadraticForm ℂ V)).range ^ (0 : ℕ) at ha
      rw [pow_zero] at ha
      obtain ⟨z, rfl⟩ := Submodule.mem_one.mp ha
      change ExteriorAlgebra.map f (algebraMap ℂ (ExteriorAlgebra ℂ V) z) ∈
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 0
      simpa only [AlgHom.commutes] using
        (SetLike.algebraMap_mem_graded
          (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W)) z)
    · change a ∈ (CliffordAlgebra.ι (0 : QuadraticForm ℂ V)).range ^ (1 : ℕ) at ha
      rw [pow_one] at ha
      obtain ⟨v, rfl⟩ := ha
      change ExteriorAlgebra.map f (ExteriorAlgebra.ι ℂ v) ∈
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 1
      rw [ExteriorAlgebra.map_apply_ι]
      exact CliffordAlgebra.ι_mem_evenOdd_one (0 : QuadraticForm ℂ W) (f v)
  | add a b ha hb hia hib =>
    simpa only [map_add] using (CliffordAlgebra.evenOdd _ _).add_mem hia hib
  | ι_mul_ι_mul v w a ha hia =>
    simpa only [map_mul, ExteriorAlgebra.map_apply_ι, zero_add] using
      SetLike.mul_mem_graded
        (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (0 : QuadraticForm ℂ W) (f v) (f w)) hia

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exterior functor induces the continuous isomorphism on each parity bundle. -/
private theorem exists_exteriorParity_iso (e : Iso E F) (i : ZMod 2) :
    ∃ u : Iso (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i)
        (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i),
      ∀ x w, (u.linearEquiv x w).val =
        ExteriorAlgebra.map (e.linearEquiv x).toLinearMap w.val := by
  classical
  -- The map of exterior algebras retains every original finite wedge generator.
  have hcontinuous : Continuous (fun z : TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)) ↦
      (⟨z.proj, ExteriorAlgebra.map (e.linearEquiv z.proj).toLinearMap z.snd⟩ :
        TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (F x)))) := by
    apply continuous_iSup_dom.mpr
    intro m
    apply continuous_iSup_dom.mpr
    intro k
    apply continuous_coinduced_dom.mpr
    let D := TotalSpace Unit (fun x : X ↦
      (Fin m → ℂ) × (∀ j : Fin m, Fin (k j) → E x))
    let D' := TotalSpace Unit (fun x : X ↦
      (Fin m → ℂ) × (∀ j : Fin m, Fin (k j) → F x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj, z.snd.1,
        fun j l ↦ (⟨z.proj, z.snd.2 j l⟩ : TotalSpace Unit E))) inferInstance
    let : TopologicalSpace D' := TopologicalSpace.induced
      (fun z : D' ↦ (z.proj, z.snd.1,
        fun j l ↦ (⟨z.proj, z.snd.2 j l⟩ : TotalSpace Unit F))) inferInstance
    have hd : Continuous (fun z : D ↦ (z.proj, z.snd.1,
        fun j l ↦ (⟨z.proj, z.snd.2 j l⟩ : TotalSpace Unit E))) :=
      continuous_induced_dom
    let lift : D → D' := fun z ↦
      ⟨z.proj, z.snd.1, fun j l ↦ e.linearEquiv z.proj (z.snd.2 j l)⟩
    have hlift : Continuous lift := by
      apply continuous_induced_rng.mpr
      exact hd.fst.prodMk (hd.snd.fst.prodMk
        (continuous_pi fun j ↦ continuous_pi fun l ↦
          e.continuous_total.comp
            ((continuous_apply l).comp ((continuous_apply j).comp hd.snd.snd))))
    have hwedge : Continuous (fun z : D' ↦ (⟨z.proj,
        ∑ j : Fin m, z.snd.1 j • ExteriorAlgebra.ιMulti ℂ (k j) (z.snd.2 j)⟩ :
          TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (F x)))) :=
      continuous_iSup_rng (i := m) (continuous_iSup_rng (i := k) continuous_coinduced_rng)
    convert hwedge.comp hlift using 1
    funext z
    simp [Function.comp_def, lift, map_sum, map_smul, ExteriorAlgebra.map_apply_ιMulti]
  -- Exterior functoriality preserves parity, including the scalar and zero-rank cases.
  let P : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
  let Q : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i
  let L (x : X) : P x ≃ₗ[ℂ] Q x :=
    { toFun a := ⟨ExteriorAlgebra.map (e.linearEquiv x).toLinearMap a.val,
        exterior_map_mem_evenOdd _ _ _ a.property⟩
      invFun b := ⟨ExteriorAlgebra.map (e.linearEquiv x).symm.toLinearMap b.val,
        exterior_map_mem_evenOdd _ _ _ b.property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        change ExteriorAlgebra.map (e.linearEquiv x).symm.toLinearMap
          (ExteriorAlgebra.map (e.linearEquiv x).toLinearMap a.val) = a.val
        rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, LinearEquiv.symm_comp,
          ExteriorAlgebra.map_id]
        rfl
      right_inv := by
        intro b
        apply Subtype.ext
        change ExteriorAlgebra.map (e.linearEquiv x).toLinearMap
          (ExteriorAlgebra.map (e.linearEquiv x).symm.toLinearMap b.val) = b.val
        rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, LinearEquiv.comp_symm,
          ExteriorAlgebra.map_id]
        rfl
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
  -- The parity topologies are induced from these same exterior total spaces.
  let H : Hom P Q :=
    { linearMap x := (L x).toLinearMap
      continuous_total := by
        apply continuous_induced_rng.mpr
        have hinc : Continuous (fun z : TotalSpace Unit P ↦
            (⟨z.proj, z.snd.val⟩ : TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) :=
          continuous_induced_dom
        exact hcontinuous.comp hinc }
  exact ⟨H.toIso (fun x ↦ (L x).bijective), fun _ _ ↦ rfl⟩

end ExteriorFunctor

section SupportSquare

open Bundle

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  {E F G H : X → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]
  [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A boundary conjugacy over one compact control preserves the support class. -/
private theorem compactSupportClass_eq_of_boundary_square
    (a : CompactSupportTriple E F) (b : CompactSupportTriple G H)
    (u : Iso E G) (v : Iso F H) (K : Set X) (hK : IsCompact K)
    (ha : a.control ⊆ K) (hb : b.control ⊆ K)
    (hs : ∀ (x : (Kᶜ : Set X)) (w : E x.val),
      v.linearEquiv x.val ((a.enlarge K hK ha).boundary.linearEquiv x w) =
        (b.enlarge K hK hb).boundary.linearEquiv x (u.linearEquiv x.val w)) :
    a.compactSupportClass = b.compactSupportClass := by
  -- Transport the original datum and compare its boundary outside the common control.
  rw [← a.compactSupportClass_congr u v]
  apply CompactSupportTriple.compactSupportClass_eq_of_homotopic
  have heq : ((a.congr u v).enlarge K hK ha).boundary =
      (b.enlarge K hK hb).boundary := by
    apply Iso.ext
    intro x
    apply LinearEquiv.ext
    intro w
    have h := hs x ((u.linearEquiv x.val).symm w)
    rw [LinearEquiv.apply_symm_apply] at h
    have hl := (a.congr u v).enlarge_apply K hK ha x w
    have hc := a.congr_apply u v ⟨x.val, fun hx ↦ x.property (ha hx)⟩ w
    have hv := a.enlarge_apply K hK ha x ((u.linearEquiv x.val).symm w)
    exact hl.trans (hc.trans ((congrArg (v.linearEquiv x.val) hv.symm).trans h))
  refine ⟨K, hK, ha, hb, ?_⟩
  rw [heq]
  exact IsoHomotopy.nonempty_refl _

end SupportSquare

section PullbackFunctor

open Bundle
open scoped TensorProduct

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (E : Y → Type*) [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 600000 in
-- The exterior quotient topology is checked on its original wedge generators.
/-- Implementation adapter for the vector-preserving exterior-parity pullback.
It retains the original exterior quotient topology and the specified pullback topology. -/
private theorem exists_exteriorParity_pullback_iso (f : C(X, Y)) (i : ZMod 2) :
    ∃ e : Iso (fun x : X ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) i)
        (f *ᵖ fun y ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) i),
      ∀ x w, e.linearEquiv x w = w := by
  let W := fun y ↦ ExteriorAlgebra ℂ (E y)
  let V := fun x ↦ ExteriorAlgebra ℂ ((f *ᵖ E) x)
  have hlift : Continuous (fun z : TotalSpace Unit V ↦
      (⟨f z.proj, z.snd⟩ : TotalSpace Unit W)) := by
    apply continuous_iSup_dom.mpr
    intro m
    apply continuous_iSup_dom.mpr
    intro k
    apply continuous_coinduced_dom.mpr
    let D := TotalSpace Unit (fun x : X ↦
      (Fin m → ℂ) × (∀ j : Fin m, Fin (k j) → (f *ᵖ E) x))
    let D' := TotalSpace Unit (fun y : Y ↦
      (Fin m → ℂ) × (∀ j : Fin m, Fin (k j) → E y))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj, z.snd.1,
        fun j l ↦ (⟨z.proj, z.snd.2 j l⟩ : TotalSpace Unit (f *ᵖ E)))) inferInstance
    let : TopologicalSpace D' := TopologicalSpace.induced
      (fun z : D' ↦ (z.proj, z.snd.1,
        fun j l ↦ (⟨z.proj, z.snd.2 j l⟩ : TotalSpace Unit E))) inferInstance
    have hd : Continuous (fun z : D ↦ (z.proj, z.snd.1,
        fun j l ↦ (⟨z.proj, z.snd.2 j l⟩ : TotalSpace Unit (f *ᵖ E)))) :=
      continuous_induced_dom
    have htuple : Continuous (fun z : D ↦ (⟨f z.proj, z.snd⟩ : D')) := by
      apply continuous_induced_rng.mpr
      exact (f.continuous.comp hd.fst).prodMk (hd.snd.fst.prodMk
        (continuous_pi fun j ↦ continuous_pi fun l ↦
          (Pullback.continuous_lift Unit E f).comp
            ((continuous_apply l).comp ((continuous_apply j).comp hd.snd.snd))))
    have hwedge : Continuous (fun z : D' ↦ (⟨z.proj,
        ∑ j : Fin m, z.snd.1 j • ExteriorAlgebra.ιMulti ℂ (k j) (z.snd.2 j)⟩ :
          TotalSpace Unit W)) :=
      continuous_iSup_rng (i := m) (continuous_iSup_rng (i := k) continuous_coinduced_rng)
    exact hwedge.comp htuple
  let P : Y → Type _ := fun y ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) i
  let Q : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) i
  let : IsFiniteRank (f *ᵖ E) := isFiniteRank_pullback (E := E) f
  let : IsFiniteRank Q := isFiniteRank_exteriorParity (E := f *ᵖ E) i
  let : IsFiniteRank (f *ᵖ P) := isFiniteRank_pullback (E := P) f
  have hparity : Continuous (fun z : TotalSpace Unit Q ↦
      (⟨f z.proj, z.snd⟩ : TotalSpace Unit P)) := by
    apply continuous_induced_rng.mpr
    have hinc : Continuous (fun z : TotalSpace Unit Q ↦
        (⟨z.proj, z.snd.val⟩ : TotalSpace Unit V)) := continuous_induced_dom
    exact hlift.comp hinc
  let H : Hom Q (f *ᵖ P) :=
    { linearMap x := (LinearMap.id : Q x →ₗ[ℂ] (f *ᵖ P) x)
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit P f).continuous_iff]
        exact continuous_proj.prodMk hparity }
  exact ⟨H.toIso (fun _ ↦ Function.bijective_id), fun _ _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Check pure tensors before composing the original direct-sum pullback maps.
/-- Implementation adapter for the tensor-sum bundles used by the supported Thom symbol.
The specified continuous isomorphism preserves each original vector. -/
private theorem exists_thomTensor_pullback_iso (J K : FiniteBundle Y) (f : C(X, Y)) :
    ∃ e : Iso
      (fun x : X ↦ ((J.pullback f).Fiber x ⊗[ℂ]
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 0) ×
        ((K.pullback f).Fiber x ⊗[ℂ]
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 1))
      (f *ᵖ fun y : Y ↦ (J.Fiber y ⊗[ℂ]
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 0) ×
        (K.Fiber y ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 1)),
      ∀ x w, e.linearEquiv x w = w := by
  have sum_pullback {G H : Y → Type _}
      [∀ y, AddCommGroup (G y)] [∀ y, Module ℂ (G y)]
      [∀ y, AddCommGroup (H y)] [∀ y, Module ℂ (H y)]
      [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]
      [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H] (f : C(X, Y)) :
      ∃ e : Iso ((f *ᵖ G) ×ᵇ (f *ᵖ H)) (f *ᵖ (G ×ᵇ H)),
        ∀ x w, e.linearEquiv x w = w := by
    let : IsFiniteRank (f *ᵖ G) := isFiniteRank_pullback (E := G) f
    let : IsFiniteRank (f *ᵖ H) := isFiniteRank_pullback (E := H) f
    let : IsFiniteRank (f *ᵖ (G ×ᵇ H)) := isFiniteRank_pullback (E := G ×ᵇ H) f
    let F : Hom ((f *ᵖ G) ×ᵇ (f *ᵖ H)) (f *ᵖ (G ×ᵇ H)) :=
      { linearMap _ := LinearMap.id
        continuous_total := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (G ×ᵇ H) f).continuous_iff]
          apply continuous_proj.prodMk
          apply continuous_induced_rng.mpr
          exact ((Pullback.continuous_lift Unit G f).comp
            (continuous_sum_fst (E := f *ᵖ G) (F := f *ᵖ H))).prodMk
              ((Pullback.continuous_lift Unit H f).comp
                (continuous_sum_snd (E := f *ᵖ G) (F := f *ᵖ H))) }
    exact ⟨F.toIso (fun _ ↦ Function.bijective_id), fun _ _ ↦ rfl⟩
  let P : ZMod 2 → Y → Type _ := fun i y ↦
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) i
  let Q : ZMod 2 → X → Type _ := fun i x ↦
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) i
  let : IsFiniteRank (f *ᵖ E) := isFiniteRank_pullback (E := E) f
  let (i : ZMod 2) : IsFiniteRank (P i) := isFiniteRank_exteriorParity (E := E) i
  let (i : ZMod 2) : IsFiniteRank (Q i) := isFiniteRank_exteriorParity (E := f *ᵖ E) i
  let (i : ZMod 2) : IsFiniteRank (f *ᵖ (P i)) := isFiniteRank_pullback (E := P i) f
  have htensor (B : FiniteBundle Y) (i : ZMod 2) :
      ∃ e : Iso (fun x : X ↦ (B.pullback f).Fiber x ⊗[ℂ] Q i x)
          (f *ᵖ fun y ↦ B.Fiber y ⊗[ℂ] P i y), ∀ x w, e.linearEquiv x w = w := by
    as_aux_lemma =>
    let : IsFiniteRank (f *ᵖ B.Fiber) := isFiniteRank_pullback (E := B.Fiber) f
    obtain ⟨p, hp⟩ := exists_exteriorParity_pullback_iso E f i
    let u : Iso (fun x : X ↦ (B.pullback f).Fiber x ⊗[ℂ] Q i x)
        (fun x : X ↦ (f *ᵖ B.Fiber) x ⊗[ℂ] (f *ᵖ (P i)) x) :=
      (Iso.refl (f *ᵖ B.Fiber)).tensor p
    let t : Iso (f *ᵖ fun y ↦ B.Fiber y ⊗[ℂ] P i y)
        (fun x : X ↦ (f *ᵖ B.Fiber) x ⊗[ℂ] (f *ᵖ (P i)) x) :=
      pullbackTensorIso (E := B.Fiber) (F := P i) f
    have hu (x : X) (a : (B.pullback f).Fiber x) (b : Q i x) :
        u.linearEquiv x (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] p.linearEquiv x b := rfl
    have ht (x : X) (w : (f *ᵖ fun y ↦ B.Fiber y ⊗[ℂ] P i y) x) :
        t.linearEquiv x w = w := rfl
    clear_value u t
    let ti := t.symm
    let e := u.trans ti
    refine ⟨e, ?_⟩
    intro x w
    induction w using TensorProduct.inductionOn with
    | tmul a b =>
        change (t.linearEquiv x).symm (u.linearEquiv x (a ⊗ₜ[ℂ] b)) = a ⊗ₜ[ℂ] b
        apply (t.linearEquiv x).symm_apply_eq.mpr
        have h := congrArg (fun b' ↦ a ⊗ₜ[ℂ] b') (hp x b)
        exact (hu x a b).trans (h.trans (ht x (a ⊗ₜ[ℂ] b)).symm)
    | add a b ha hb =>
        exact ((e.linearEquiv x).map_add a b).trans (congrArg₂ (· + ·) ha hb)
  obtain ⟨u, hu⟩ := htensor J 0
  obtain ⟨v, hv⟩ := htensor K 1
  obtain ⟨s, hs⟩ := sum_pullback
    (G := fun y ↦ J.Fiber y ⊗[ℂ] P 0 y)
    (H := fun y ↦ K.Fiber y ⊗[ℂ] P 1 y) f
  refine ⟨(u.sum v).trans s, ?_⟩
  intro x w
  change s.linearEquiv x (u.linearEquiv x w.1, v.linearEquiv x w.2) = w
  exact (hs x _).trans (Prod.ext (hu x w.1) (hv x w.2))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Compose the same-vector comparison with the two specified iterated-pullback maps.
/-- Implementation adapter from base pullback to the specified total-space lift.
The original iterated-pullback isomorphisms preserve each fiber vector. -/
private theorem exists_thomTensor_totalPullback_iso (J K : FiniteBundle Y) (f : C(X, Y)) :
    ∃ e : Iso
      ((π Unit (f *ᵖ E)) *ᵖ fun x : X ↦ ((J.pullback f).Fiber x ⊗[ℂ]
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 0) ×
        ((K.pullback f).Fiber x ⊗[ℂ]
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 1))
      ((pullbackTotalMap E f) *ᵖ ((π Unit E) *ᵖ fun y : Y ↦ (J.Fiber y ⊗[ℂ]
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 0) ×
        (K.Fiber y ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 1))),
      ∀ x w, e.linearEquiv x w = w := by
  let pX : C(TotalSpace Unit (f *ᵖ E), X) := ⟨π Unit (f *ᵖ E), continuous_proj⟩
  let pY : C(TotalSpace Unit E, Y) := ⟨π Unit E, continuous_proj⟩
  let q := pullbackTotalMap E f
  let S : Y → Type _ := fun y ↦ (J.Fiber y ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 0) ×
    (K.Fiber y ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 1)
  obtain ⟨e, he⟩ := exists_thomTensor_pullback_iso E J K f
  let u := pullbackCompIso (E := S) f pX
  let v := pullbackCompIso (E := S) pY q
  have hu (z : TotalSpace Unit (f *ᵖ E)) (w) : u.linearEquiv z w = w :=
    pullbackCompIso_apply (E := S) f pX z w
  have hv (z : TotalSpace Unit (f *ᵖ E)) (w) : v.linearEquiv z w = w :=
    pullbackCompIso_apply (E := S) pY q z w
  clear_value u v
  let vi := v.symm
  let uv := u.trans vi
  let ep := e.pullback pX
  let result := ep.trans uv
  refine ⟨result, ?_⟩
  intro z w
  change (v.linearEquiv z).symm (u.linearEquiv z (e.linearEquiv z.proj w)) = w
  apply (v.linearEquiv z).symm_apply_eq.mpr
  exact (hu z _).trans ((he z.proj w).trans (hv z w).symm)

end PullbackFunctor

section SupportedThomPullback

open Bundle
open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2500000 in
-- Normalize the original pullback metrics and four-block exterior tensor symbols.
/-- Proper base-change naturality of the supported Thom operator with specified pairings.
The normed fiber structures are pulled back from the given bundle. -/
private theorem supportedThomHom_pullback_of_continuous_pairing
    (J : Y → Type*) [hN : ∀ y, NormedAddCommGroup (J y)] [hI : ∀ y, InnerProductSpace ℂ (J y)]
    [TopologicalSpace (TotalSpace Unit J)] [IsFiniteRank J]
    (hY : Continuous (fun z : TotalSpace Unit (J ×ᵇ J) ↦ inner ℂ z.snd.1 z.snd.2))
    (f : C(X, Y)) (hf : IsProperMap f)
    (hX : Continuous (fun z : TotalSpace Unit ((f *ᵖ J) ×ᵇ (f *ᵖ J)) ↦
      inner ℂ (show J (f z.proj) from z.snd.1) z.snd.2)) :
    let : ∀ x, NormedAddCommGroup ((f *ᵖ J) x) := fun x ↦
      hN (f x)
    let : ∀ x, InnerProductSpace ℂ ((f *ᵖ J) x) := fun x ↦
      hI (f x)
    let : ∀ x, AddCommGroup ((f *ᵖ J) x) := fun x ↦
      (hN (f x)).toAddCommGroup
    let : ∀ x, AddCommMonoid ((f *ᵖ J) x) := fun x ↦
      (hN (f x)).toAddCommGroup.toAddCommMonoid
    let : ∀ x, Module ℂ ((f *ᵖ J) x) := fun x ↦
      (hI (f x)).toModule
    (supportedThomHom (f *ᵖ J) hX).comp (compactSupportKZeroPullback f hf) =
      (compactSupportKZeroPullback (pullbackTotalMap J f)
        ((pullbackTotalMap_properties J f).1 hf)).comp (supportedThomHom J hY) := by
  /- Stage 1: the specified total lift is proper by base change; it is not the
  bundle projection. Fix an original support triple on Y and one admissible
  cutoff rho, neighborhood U and compact enlarged control L. Properness of f
  makes both inverse-image compact controls compact. On X use exactly rho o f,
  the inverse image of U and the inverse image of L, so the two reciprocal
  cutoff maps are precisely the original maps evaluated at f(x).
  Stage 2: the pulled-back metric has the original form h_{f(x)} on the same
  vector v. The canonical vector-preserving exterior, parity, tensor and sum
  pullback identifications carry every block and its denominator to the same
  original formula. Pulling the zero section over L back by the actual total
  lift gives exactly the zero section over the inverse image of L.
  Stage 3: apply the original support-class proper-pullback comparison to this
  same tensor triple. Its canonical bundle identifications yield equality of
  the two displayed values on each original support representative. Their
  surjectivity gives the homomorphism square. The pullback on compact-support K
  theory still requires proper f; arbitrary continuous f is used only for the
  metric construction and cannot be substituted in this theorem. -/
  let : ∀ x, NormedAddCommGroup ((f *ᵖ J) x) := fun x ↦
    hN (f x)
  let : ∀ x, InnerProductSpace ℂ ((f *ᵖ J) x) := fun x ↦
    hI (f x)
  let : ∀ x, AddCommGroup ((f *ᵖ J) x) := fun x ↦
    (hN (f x)).toAddCommGroup
  let : ∀ x, AddCommMonoid ((f *ᵖ J) x) := fun x ↦
    (hN (f x)).toAddCommGroup.toAddCommMonoid
  let : ∀ x, Module ℂ ((f *ᵖ J) x) := fun x ↦
    (hI (f x)).toModule
  change (supportedThomHom (f *ᵖ J) hX).comp (compactSupportKZeroPullback f hf) =
    (compactSupportKZeroPullback (pullbackTotalMap J f)
      ((pullbackTotalMap_properties J f).1 hf)).comp (supportedThomHom J hY)
  let : IsFiniteRank (f *ᵖ J) := isFiniteRank_pullback (E := J) f
  apply AddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := supportBundleTriple_compactSupportClass_surjective x
  obtain ⟨U, hU, hcontrol, L, hL, _hUL, ρ, hzero, hone⟩ :=
    exists_time_cutoff a.datum.control a.datum.isCompact_control
  let q := pullbackTotalMap J f
  have hq : IsProperMap q := (pullbackTotalMap_properties J f).1 hf
  let ρ' := ρ.comp f
  have hU' : IsOpen (f ⁻¹' U) := hU.preimage f.continuous
  have hcontrol' : (a.pullback f hf).datum.control ⊆ f ⁻¹' U := fun _ hx ↦ hcontrol hx
  have hzero' : ∀ x ∈ f ⁻¹' U, ρ' x = 0 := fun x hx ↦ hzero (f x) hx
  have hL' : IsCompact (f ⁻¹' L) := hf.isCompact_preimage hL
  have hone' : ∀ x ∉ f ⁻¹' L, ρ' x = 1 := fun x hx ↦ hone (f x) hx
  change (supportedThomHom (f *ᵖ J) hX) (compactSupportKZeroPullback f hf a.compactSupportClass) =
    compactSupportKZeroPullback q hq ((supportedThomHom J hY) a.compactSupportClass)
  rw [← a.compactSupportClass_pullback f hf]
  rw [supportedThomHom_class (f *ᵖ J) hX
    (a.pullback f hf) ρ' (f ⁻¹' U) hU' hcontrol' hzero' (f ⁻¹' L) hL' hone',
    supportedThomHom_class J hY a ρ U hU hcontrol hzero L hL hone]
  let pY : C(TotalSpace Unit J, Y) := ⟨π Unit J, continuous_proj⟩
  let pX : C(TotalSpace Unit (f *ᵖ J), X) := ⟨π Unit (f *ᵖ J), continuous_proj⟩
  let S : Y → Type _ := fun y ↦ (a.source.Fiber y ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (J y)) 0) ×
    (a.target.Fiber y ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (J y)) 1)
  let T : Y → Type _ := fun y ↦ (a.target.Fiber y ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (J y)) 0) ×
    (a.source.Fiber y ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (J y)) 1)
  let S' : X → Type _ := fun x ↦ ((a.source.pullback f).Fiber x ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ J) x)) 0) ×
    ((a.target.pullback f).Fiber x ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ J) x)) 1)
  let T' : X → Type _ := fun x ↦ ((a.target.pullback f).Fiber x ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ J) x)) 0) ×
    ((a.source.pullback f).Fiber x ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ J) x)) 1)
  let : IsFiniteRank (pY *ᵖ S) := isFiniteRank_pullback (E := S) pY
  let : IsFiniteRank (pY *ᵖ T) := isFiniteRank_pullback (E := T) pY
  let : IsFiniteRank (pX *ᵖ S') := isFiniteRank_pullback (E := S') pX
  let : IsFiniteRank (pX *ᵖ T') := isFiniteRank_pullback (E := T') pX
  let : IsFiniteRank (q *ᵖ (pY *ᵖ S)) := isFiniteRank_pullback (E := pY *ᵖ S) q
  let : IsFiniteRank (q *ᵖ (pY *ᵖ T)) := isFiniteRank_pullback (E := pY *ᵖ T) q
  -- Retain each specified tensor symbol as a function on its own original total space.
  let phiX (z : TotalSpace Unit (f *ᵖ J)) (w : S' z.proj) : T' z.proj :=
    thomTensorSymbol (F := a.source.Fiber (f z.proj))
      (G := a.target.Fiber (f z.proj)) (V := J (f z.proj))
      (show a.source.Fiber (f z.proj) →ₗ[ℂ] a.target.Fiber (f z.proj) from
        (a.pullback f hf).datum.cutoffLinearMap ρ' z.proj)
      (show a.target.Fiber (f z.proj) →ₗ[ℂ] a.source.Fiber (f z.proj) from
        (a.pullback f hf).datum.inverse.cutoffLinearMap ρ' z.proj)
      (show J (f z.proj) from z.snd) w
  let phiY (z : TotalSpace Unit J) (w : S z.proj) : T z.proj :=
    thomTensorSymbol (F := a.source.Fiber z.proj) (G := a.target.Fiber z.proj)
      (V := J z.proj) (a.datum.cutoffLinearMap ρ z.proj)
      (a.datum.inverse.cutoffLinearMap ρ z.proj) z.snd w
  -- The original cutoff and its inverse pull back through the same boundary equivalence.
  have hd (x : X) : (a.pullback f hf).datum.cutoffLinearMap ρ' x =
      a.datum.cutoffLinearMap ρ (f x) := by
    apply LinearMap.ext
    intro w
    by_cases hx : f x ∈ a.datum.control
    · have hx' : x ∈ f ⁻¹' a.datum.control := hx
      simp only [CompactSupportTriple.cutoffLinearMap, SupportBundleTriple.pullback,
        CompactSupportTriple.pullback, dite_eq_left hx', dite_eq_left hx]
    · have hx' : x ∉ f ⁻¹' a.datum.control := hx
      simp only [CompactSupportTriple.cutoffLinearMap, SupportBundleTriple.pullback,
        CompactSupportTriple.pullback, dite_eq_right hx', dite_eq_right hx]
      change ((ρ (f x) : ℝ) : ℂ) •
        (a.datum.boundary.pullback f).linearEquiv ⟨x, hx⟩ w = _
      rw [RelativeTriple.pullback_apply]
      rfl
  have hd' (x : X) : (a.pullback f hf).datum.inverse.cutoffLinearMap ρ' x =
      a.datum.inverse.cutoffLinearMap ρ (f x) := by
    apply LinearMap.ext
    intro w
    by_cases hx : f x ∈ a.datum.control
    · have hx' : x ∈ f ⁻¹' a.datum.control := hx
      simp only [CompactSupportTriple.cutoffLinearMap, SupportBundleTriple.pullback,
        CompactSupportTriple.inverse, CompactSupportTriple.pullback,
        dite_eq_left hx', dite_eq_left hx]
    · have hx' : x ∉ f ⁻¹' a.datum.control := hx
      simp only [CompactSupportTriple.cutoffLinearMap, SupportBundleTriple.pullback,
        CompactSupportTriple.inverse, CompactSupportTriple.pullback,
        dite_eq_right hx', dite_eq_right hx]
      have he : (a.datum.boundary.pullback f).linearEquiv ⟨x, hx⟩ =
          a.datum.boundary.linearEquiv ⟨f x, hx⟩ := by
        apply LinearEquiv.ext
        intro w
        exact RelativeTriple.pullback_apply a.datum.boundary f ⟨x, hx⟩ w
      change ((ρ (f x) : ℝ) : ℂ) •
        ((a.datum.boundary.pullback f).linearEquiv ⟨x, hx⟩).symm w = _
      rw [he]
      rfl
  -- The two pulled-back cutoff maps identify the same four-block Thom symbol.
  have hsymbol (z : TotalSpace Unit (f *ᵖ J)) (w : S' z.proj) :
      phiX z w = phiY (q z) w := by
    change thomTensorSymbol (F := a.source.Fiber (f z.proj))
        (G := a.target.Fiber (f z.proj)) (V := J (f z.proj))
        (show a.source.Fiber (f z.proj) →ₗ[ℂ] a.target.Fiber (f z.proj) from
          (a.pullback f hf).datum.cutoffLinearMap ρ' z.proj)
        (show a.target.Fiber (f z.proj) →ₗ[ℂ] a.source.Fiber (f z.proj) from
          (a.pullback f hf).datum.inverse.cutoffLinearMap ρ' z.proj)
        (show J (f z.proj) from z.snd) w =
      thomTensorSymbol (F := a.source.Fiber (f z.proj))
        (G := a.target.Fiber (f z.proj)) (V := J (f z.proj))
        (a.datum.cutoffLinearMap ρ (f z.proj))
        (a.datum.inverse.cutoffLinearMap ρ (f z.proj))
        (show J (f z.proj) from z.snd) w
    exact congrArg₂ (fun (d : a.source.Fiber (f z.proj) →ₗ[ℂ] a.target.Fiber (f z.proj))
        (d' : a.target.Fiber (f z.proj) →ₗ[ℂ] a.source.Fiber (f z.proj)) ↦
      thomTensorSymbol (F := a.source.Fiber (f z.proj))
        (G := a.target.Fiber (f z.proj)) (V := J (f z.proj)) d d'
        (show J (f z.proj) from z.snd) w) (hd z.proj) (hd' z.proj)
  -- Save the actual boundary formulas on their specified fibers.
  let A : CompactSupportTriple (pX *ᵖ S') (pX *ᵖ T') :=
    supportedThomTriple (f *ᵖ J) hX (a.pullback f hf) ρ' (f ⁻¹' U) hU'
      hcontrol' hzero' (f ⁻¹' L) hL' hone'
  let B : CompactSupportTriple (pY *ᵖ S) (pY *ᵖ T) :=
    supportedThomTriple J hY a ρ U hU hcontrol hzero L hL hone
  have hAvalue (z : (A.controlᶜ : Set (TotalSpace Unit (f *ᵖ J))))
      (w : S' z.val.proj) : A.boundary.linearEquiv z w = phiX z.val w := rfl
  have hBvalue (z : (B.controlᶜ : Set (TotalSpace Unit J)))
      (w : S z.val.proj) : B.boundary.linearEquiv z w = phiY z.val w := rfl
  change A.compactSupportClass = compactSupportKZeroPullback q hq B.compactSupportClass
  rw [← B.compactSupportClass_pullback q hq]
  -- The original tensor comparison has definitionally identical inherited structures.
  have hU : ∃ u : Iso (pX *ᵖ S') (q *ᵖ (pY *ᵖ S)),
      ∀ z w, u.linearEquiv z w = w := by
    have hh := exists_thomTensor_totalPullback_iso J a.source a.target f
    run_tac Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let d ← Lean.Meta.getLocalDeclFromUserName `hh
      goal.assign d.toExpr
      Lean.Elab.Tactic.replaceMainGoal []
  have hV : ∃ v : Iso (pX *ᵖ T') (q *ᵖ (pY *ᵖ T)),
      ∀ z w, v.linearEquiv z w = w := by
    have hh := exists_thomTensor_totalPullback_iso J a.target a.source f
    run_tac Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let d ← Lean.Meta.getLocalDeclFromUserName `hh
      goal.assign d.toExpr
      Lean.Elab.Tactic.replaceMainGoal []
  obtain ⟨u, hu⟩ := hU
  obtain ⟨v, hv⟩ := hV
  let K := A.control
  have hK : IsCompact K := A.isCompact_control
  have hB : (B.pullback q hq).control ⊆ K := fun _ hz ↦ hz
  -- Use the saved formulas to compare the same two endpoints in the boundary square.
  apply compactSupportClass_eq_of_boundary_square A (B.pullback q hq) u v K hK
    (Set.Subset.refl _) hB
  intro z w
  let za : (A.controlᶜ : Set (TotalSpace Unit (f *ᵖ J))) := ⟨z.val, z.property⟩
  let zb : (B.controlᶜ : Set (TotalSpace Unit J)) :=
    ⟨q z.val, fun hz ↦ z.property (hB hz)⟩
  have ha : A.boundary.linearEquiv za w = phiX z.val w := hAvalue za w
  have hb : B.boundary.linearEquiv zb w = phiY (q z.val) w := hBvalue zb w
  have hraw := ha.trans ((hsymbol z.val w).trans hb.symm)
  have hl := A.enlarge_apply K hK (Set.Subset.refl _) z w
  have hr := (B.pullback q hq).enlarge_apply K hK hB z w
  have hp := RelativeTriple.pullback_apply B.boundary q
    ⟨z.val, fun hz ↦ z.property (hB hz)⟩ w
  exact (hv z.val _).trans (hl.trans (hraw.trans (hp.symm.trans
    (hr.symm.trans (congrArg (((B.pullback q hq).enlarge K hK hB).boundary.linearEquiv z)
      (hu z.val w).symm)))))

end SupportedThomPullback

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle
open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

section BundleIso

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1500000 in
-- Normalize metric transport and exterior conjugation on the same original support.
/-- Every complex bundle isomorphism carries the specified Thom operator to the target one. -/
theorem supportedThomHom_iso (hE : ContinuousHermitianMetric E)
    (hF : ContinuousHermitianMetric F) (e : Iso E F) :
    (compactSupportKZeroHomeomorph e.totalHomeomorph).comp hE.supportedThomHom =
      hF.supportedThomHom := by
  /- Stage 1: on E use the transported form h'(u,v)=hF(e(u),e(v)). Its algebraic
  Core is positive definite because every e_x is a complex linear equivalence;
  continuity follows from the original continuous total map applied to both
  vectors. Thus e is an isometry for h' and hF without imposing any relation
  between the originally supplied hE and hF. Metric independence replaces hE
  by this h' in the same original compact-support groups.
  Stage 2: fix one original support triple on X and one admissible cutoff with
  compact control L. The exterior algebra maps induced by e preserve parity and
  intertwine wedge and contraction for these transported metrics. Tensoring
  them with the identity maps on the input bundles conjugates all four blocks
  of the prescribed tensor symbol, including its reverse block and denominator.
  The actual homeomorphism e.totalHomeomorph sends the zero section over L to
  the same zero section in F. No extra sign or new support choice is introduced.
  Stage 3: the existing homeomorphism map is pullback along the inverse actual
  homeomorphism. Proper pullback of support triples and the indicated exterior
  bundle isomorphisms identify these two tensor classes. The specified generator
  formula and surjectivity of original support representatives give equality of
  the displayed homomorphisms. The isomorphism need not preserve the two original
  metrics, and neither global constant rank nor compactness of X is required. -/
  have metricIsoTransport_exists (hF : ContinuousHermitianMetric F) (e : Iso E F) :
      ∃ ht : ContinuousHermitianMetric E, ∀ x (u v : E x),
        (ht.toCore x).inner u v =
          (hF.toCore x).inner (e.linearEquiv x u) (e.linearEquiv x v) := by
    -- Pull back each original Hermitian form by the same specified fiber isomorphism.
    let ht : ContinuousHermitianMetric E :=
      { toCore := fun x ↦
          { inner := fun u v ↦
              (hF.toCore x).inner (e.linearEquiv x u) (e.linearEquiv x v)
            conj_inner_symm u v := (hF.toCore x).conj_inner_symm _ _
            re_inner_nonneg v := (hF.toCore x).re_inner_nonneg _
            add_left u v w := by
              rw [(e.linearEquiv x).map_add, (hF.toCore x).add_left]
            smul_left u v c := by
              rw [(e.linearEquiv x).map_smul, (hF.toCore x).smul_left]
            definite v hv := by
              apply (e.linearEquiv x).injective
              simpa only [map_zero] using (hF.toCore x).definite _ hv }
        continuous_pairing := by
          -- The original sum topology tests continuity on its two total-space projections.
          let pairMap : TotalSpace Unit (E ×ᵇ E) → TotalSpace Unit (F ×ᵇ F) :=
            fun z ↦ ⟨z.proj, e.linearEquiv z.proj z.snd.1,
              e.linearEquiv z.proj z.snd.2⟩
          have hpair : Continuous pairMap := by
            apply continuous_induced_rng.mpr
            exact (e.continuous_total.comp (continuous_sum_fst (E := E) (F := E))).prodMk
              (e.continuous_total.comp (continuous_sum_snd (E := E) (F := E)))
          exact hF.continuous_pairing.comp hpair
        isFiniteRank := inferInstance }
    exact ⟨ht, fun _ _ _ ↦ rfl⟩
  have thom_total_iso (e : Iso E F) (J K : FiniteBundle X)
      (u : ∀ i : ZMod 2,
        Iso (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i)
          (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i)) :
      let q : C(TotalSpace Unit F, TotalSpace Unit E) :=
        ⟨e.totalHomeomorph.symm, e.totalHomeomorph.symm.continuous⟩
      ∃ b : Iso (q *ᵖ ((π Unit E) *ᵖ fun x : X ↦
          (J.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) ×
            (K.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)))
        ((π Unit F) *ᵖ fun x : X ↦
          (J.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) 0) ×
            (K.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) 1)),
        ∀ z w, b.linearEquiv z w =
          ((TensorProduct.congr (LinearEquiv.refl ℂ (J.Fiber z.proj))
            ((u 0).linearEquiv z.proj)).prodCongr
              (TensorProduct.congr (LinearEquiv.refl ℂ (K.Fiber z.proj))
                ((u 1).linearEquiv z.proj))) w := by
    let q : C(TotalSpace Unit F, TotalSpace Unit E) :=
      ⟨e.totalHomeomorph.symm, e.totalHomeomorph.symm.continuous⟩
    let pE : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
    let pF : C(TotalSpace Unit F, X) := ⟨π Unit F, continuous_proj⟩
    let S : X → Type _ := fun x ↦
      (J.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) ×
        (K.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)
    let c := ((Iso.refl J.Fiber).tensor (u 0)).sum ((Iso.refl K.Fiber).tensor (u 1))
    let a := pullbackCompIso (E := S) pE q
    let b := a.trans (c.pullback pF)
    refine ⟨b, ?_⟩
    intro z w
    change c.linearEquiv z.proj (a.linearEquiv z w) = _
    have ha : a.linearEquiv z w = w := pullbackCompIso_apply (E := S) pE q z w
    rw [ha]
    rfl
  -- Transport the target form through the original isomorphism, then remove the old metric.
  obtain ⟨ht, hmetric⟩ := metricIsoTransport_exists hF e
  rw [ContinuousHermitianMetric.supportedThomHom_eq hE ht]
  let : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (ht.toCore x).toNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
    InnerProductSpace.ofCore (ht.toCore x).toCore
  let : ∀ x, NormedAddCommGroup (F x) := fun x ↦ (hF.toCore x).toNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := fun x ↦
    InnerProductSpace.ofCore (hF.toCore x).toCore
  classical
  let ui (i : ZMod 2) := (exists_exteriorParity_iso e i).choose
  have hui (i : ZMod 2) (x : X) (w) :
      ((ui i).linearEquiv x w).val =
        ExteriorAlgebra.map (e.linearEquiv x).toLinearMap w.val :=
    (exists_exteriorParity_iso e i).choose_spec x w
  -- One input representative and one cutoff give both tensor triples and the same base control.
  apply AddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := supportBundleTriple_compactSupportClass_surjective x
  have thom_iso_tensor (x : X)
      (d : a.source.Fiber x →ₗ[ℂ] a.target.Fiber x)
      (d' : a.target.Fiber x →ₗ[ℂ] a.source.Fiber x) (v : E x) :
      let l := e.linearEquiv x
      let u := fun i ↦ (ui i).linearEquiv x
      ((TensorProduct.congr (LinearEquiv.refl ℂ (a.target.Fiber x)) (u 0)).prodCongr
        (TensorProduct.congr (LinearEquiv.refl ℂ (a.source.Fiber x)) (u 1))).toLinearMap.comp
        (thomTensorSymbol d d' v) =
        (thomTensorSymbol d d' (l v)).comp
          ((TensorProduct.congr (LinearEquiv.refl ℂ (a.source.Fiber x)) (u 0)).prodCongr
            (TensorProduct.congr (LinearEquiv.refl ℂ (a.target.Fiber x)) (u 1))).toLinearMap := by
    let V := E x
    let W := F x
    let J := a.source.Fiber x
    let K := a.target.Fiber x
    let l : V ≃ₗ[ℂ] W := e.linearEquiv x
    let u (i : ZMod 2) := (ui i).linearEquiv x
    have hl (v w : V) : inner ℂ (l v) (l w) = inner ℂ v w := (hmetric x v w).symm
    have hu (i : ZMod 2) (a) : (u i a).val = ExteriorAlgebra.map l.toLinearMap a.val :=
      hui i x a
    change ((TensorProduct.congr (LinearEquiv.refl ℂ K) (u 0)).prodCongr
      (TensorProduct.congr (LinearEquiv.refl ℂ J) (u 1))).toLinearMap.comp
      (thomTensorSymbol d d' v) =
      (thomTensorSymbol d d' (l v)).comp
        ((TensorProduct.congr (LinearEquiv.refl ℂ J) (u 0)).prodCongr
          (TensorProduct.congr (LinearEquiv.refl ℂ K) (u 1))).toLinearMap
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    all_goals
      -- Contraction is natural for the pulled-back covector before using the isometry.
      have hcontract (f : V →ₗ[ℂ] W) (c : Module.Dual ℂ W) (a : ExteriorAlgebra ℂ V) :
          CliffordAlgebra.contractLeft c (ExteriorAlgebra.map f a) =
            ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (c.comp f) a) := by
        induction a using CliffordAlgebra.left_induction with
        | algebraMap r =>
          simp only [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, map_zero]
        | add a b ha hb => simp only [map_add, ha, hb]
        | ι_mul w a ha =>
          rw [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
            CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
            ExteriorAlgebra.map_apply_ι, ha]
          rfl
      have hc : (innerₛₗ ℂ (l v)).comp l.toLinearMap = innerₛₗ ℂ v := by
        ext w
        exact hl v w
      have hsymbol (a : ExteriorAlgebra ℂ V) :
          ExteriorAlgebra.map l.toLinearMap (cliffordSymbol v a) =
            cliffordSymbol (l v) (ExteriorAlgebra.map l.toLinearMap a) := by
        change ExteriorAlgebra.map l.toLinearMap
          (ExteriorAlgebra.ι ℂ v * a - CliffordAlgebra.contractLeft (innerₛₗ ℂ v) a) =
          ExteriorAlgebra.ι ℂ (l v) * ExteriorAlgebra.map l.toLinearMap a -
            CliffordAlgebra.contractLeft (innerₛₗ ℂ (l v)) (ExteriorAlgebra.map l.toLinearMap a)
        rw [map_sub, map_mul, ExteriorAlgebra.map_apply_ι, hcontract, hc]
        rfl
      have h₀ (a : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 0) :
          u 1 (cliffordSymbolParity v 0 a) = cliffordSymbolParity (l v) 0 (u 0 a) := by
        apply Subtype.ext
        rw [hu]
        change ExteriorAlgebra.map l.toLinearMap (cliffordSymbol v a.val) =
          cliffordSymbol (l v) (u 0 a).val
        rw [hu, hsymbol]
      have h₁ (a : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 1) :
          u 0 (cliffordSymbolParity v 1 a) = cliffordSymbolParity (l v) 1 (u 1 a) := by
        apply Subtype.ext
        rw [hu]
        change ExteriorAlgebra.map l.toLinearMap (cliffordSymbol v a.val) =
          cliffordSymbol (l v) (u 1 a).val
        rw [hu, hsymbol]
      -- Pure tensors expose the four original matrix blocks and the two parity intertwiners.
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> intro a b <;> apply Prod.ext <;>
        simp only [LinearMap.comp_apply, thomTensorSymbol, LinearMap.prod_apply,
          Function.prod_apply, LinearMap.coprod_apply, LinearMap.neg_apply,
          LinearMap.inl_apply, LinearMap.inr_apply, TensorProduct.map_tmul,
          LinearMap.id_apply, LinearEquiv.coe_coe, LinearEquiv.prodCongr_apply,
          TensorProduct.congr_tmul, LinearEquiv.refl_apply, map_zero, map_neg,
          add_zero, zero_add, h₀, h₁]
  obtain ⟨U, hU, hcontrol, L, hL, _hUL, ρ, hzero, hone⟩ :=
    exists_time_cutoff a.datum.control a.datum.isCompact_control
  let q : C(TotalSpace Unit F, TotalSpace Unit E) :=
    ⟨e.totalHomeomorph.symm, e.totalHomeomorph.symm.continuous⟩
  have hq : IsProperMap q := e.totalHomeomorph.symm.isProperMap
  change compactSupportKZeroPullback q hq
      (AtiyahSinger.ComplexBundle.supportedThomHom E ht.continuous_pairing a.compactSupportClass) =
    AtiyahSinger.ComplexBundle.supportedThomHom F hF.continuous_pairing a.compactSupportClass
  rw [supportedThomHom_class E ht.continuous_pairing a ρ U hU hcontrol hzero L hL hone,
    supportedThomHom_class F hF.continuous_pairing a ρ U hU hcontrol hzero L hL hone]
  let pE : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let pF : C(TotalSpace Unit F, X) := ⟨π Unit F, continuous_proj⟩
  let SE : X → Type _ := fun x ↦
    (a.source.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) ×
      (a.target.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)
  let TE : X → Type _ := fun x ↦
    (a.target.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) ×
      (a.source.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)
  let SF : X → Type _ := fun x ↦
    (a.source.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) 0) ×
      (a.target.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) 1)
  let TF : X → Type _ := fun x ↦
    (a.target.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) 0) ×
      (a.source.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) 1)
  let : IsFiniteRank (pE *ᵖ SE) := isFiniteRank_pullback (E := SE) pE
  let : IsFiniteRank (pE *ᵖ TE) := isFiniteRank_pullback (E := TE) pE
  let : IsFiniteRank (pF *ᵖ SF) := isFiniteRank_pullback (E := SF) pF
  let : IsFiniteRank (pF *ᵖ TF) := isFiniteRank_pullback (E := TF) pF
  let : IsFiniteRank (q *ᵖ (pE *ᵖ SE)) := isFiniteRank_pullback (E := pE *ᵖ SE) q
  let : IsFiniteRank (q *ᵖ (pE *ᵖ TE)) := isFiniteRank_pullback (E := pE *ᵖ TE) q
  let A := supportedThomTriple E ht.continuous_pairing a ρ U hU hcontrol hzero L hL hone
  let B := supportedThomTriple F hF.continuous_pairing a ρ U hU hcontrol hzero L hL hone
  have hAvalue (z : (A.controlᶜ : Set (TotalSpace Unit E))) (w : SE z.val.proj) :
      A.boundary.linearEquiv z w =
        thomTensorSymbol (a.datum.cutoffLinearMap ρ z.val.proj)
          (a.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd w := rfl
  have hBvalue (z : (B.controlᶜ : Set (TotalSpace Unit F))) (w : SF z.val.proj) :
      B.boundary.linearEquiv z w =
        thomTensorSymbol (a.datum.cutoffLinearMap ρ z.val.proj)
          (a.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd w := rfl
  change compactSupportKZeroPullback q hq A.compactSupportClass = B.compactSupportClass
  rw [← A.compactSupportClass_pullback q hq]
  obtain ⟨u, hu⟩ := thom_total_iso e a.source a.target ui
  obtain ⟨v, hv⟩ := thom_total_iso e a.target a.source ui
  let K := B.control
  have hK : IsCompact K := B.isCompact_control
  have ha : (A.pullback q hq).control ⊆ K := by
    intro z hz
    change z.proj ∈ L ∧ (e.linearEquiv z.proj).symm z.snd = 0 at hz
    change z.proj ∈ L ∧ z.snd = 0
    exact ⟨hz.1, (e.linearEquiv z.proj).symm.map_eq_zero_iff.mp hz.2⟩
  clear_value A B
  -- The original boundary maps form a commuting square off this same compact zero section.
  apply compactSupportClass_eq_of_boundary_square (A.pullback q hq) B u v K hK ha
    (Set.Subset.refl _)
  intro z w
  let za : (A.controlᶜ : Set (TotalSpace Unit E)) :=
    ⟨q z.val, fun hz ↦ z.property (ha hz)⟩
  let zb : (B.controlᶜ : Set (TotalSpace Unit F)) := ⟨z.val, z.property⟩
  have hsymbol := LinearMap.congr_fun (thom_iso_tensor z.val.proj
    (a.datum.cutoffLinearMap ρ z.val.proj)
    (a.datum.inverse.cutoffLinearMap ρ z.val.proj)
    ((e.linearEquiv z.val.proj).symm z.val.snd)) w
  simp only [LinearMap.comp_apply, LinearEquiv.apply_symm_apply] at hsymbol
  have hl := (A.pullback q hq).enlarge_apply K hK ha z w
  have hp := RelativeTriple.pullback_apply A.boundary q
    ⟨z.val, fun hz ↦ z.property (ha hz)⟩ w
  have hleft := hl.trans (hp.trans (hAvalue za w))
  have hright (w' : SF z.val.proj) :=
    (B.enlarge_apply K hK (Set.Subset.refl _) z w').trans (hBvalue zb w')
  exact (congrArg (v.linearEquiv z.val) hleft).trans
    ((hv z.val _).trans (hsymbol.trans
      ((congrArg (thomTensorSymbol (a.datum.cutoffLinearMap ρ z.val.proj)
        (a.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd) (hu z.val w).symm).trans
          (hright (u.linearEquiv z.val w)).symm)))

end BundleIso

section ProperBaseChange

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 500000 in
-- Specialize the dependent pullback comparison to the original metric and total map.
/-- Proper base pullback commutes with the actual supported Thom map and its total-space lift. -/
theorem supportedThomHom_pullback (h : ContinuousHermitianMetric E)
    (f : C(X, Y)) (hf : IsProperMap f) :
    (h.pullback f).supportedThomHom.comp (compactSupportKZeroPullback f hf) =
      (compactSupportKZeroPullback (pullbackTotalMap E f)
        ((pullbackTotalMap_properties E f).1 hf)).comp h.supportedThomHom := by
  -- Specialize the independent comparison to the original metric and its actual pullback.
  let : ∀ y, NormedAddCommGroup (E y) := fun y ↦ (h.toCore y).toNormedAddCommGroup
  let : ∀ y, InnerProductSpace ℂ (E y) := fun y ↦
    InnerProductSpace.ofCore (h.toCore y).toCore
  exact supportedThomHom_pullback_of_continuous_pairing E h.continuous_pairing f hf
    (h.pullback f).continuous_pairing

end ProperBaseChange

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_pullback

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (E : Y → Type*) [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- Public access to the established same-vector parity pullback comparison.
This implementation wrapper lets the direct-sum proof reuse the original construction. -/
theorem exteriorParity_pullback_comparison (f : C(X, Y)) (i : ZMod 2) :
    ∃ e : Iso (fun x : X ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) i)
        (f *ᵖ fun y ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) i),
      ∀ x w, e.linearEquiv x w = w := by
  exact exists_exteriorParity_pullback_iso E f i

/-- Public access to the established same-vector Thom tensor pullback comparison.
Both tensor factors, the parity order and the original total topologies are retained. -/
theorem thomTensor_pullback_comparison (J K : FiniteBundle Y) (f : C(X, Y)) :
    ∃ e : Iso
      (fun x : X ↦ ((J.pullback f).Fiber x ⊗[ℂ]
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 0) ×
        ((K.pullback f).Fiber x ⊗[ℂ]
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 1))
      (f *ᵖ fun y : Y ↦ (J.Fiber y ⊗[ℂ]
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 0) ×
        (K.Fiber y ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 1)),
      ∀ x w, e.linearEquiv x w = w := by
  exact exists_thomTensor_pullback_iso E J K f

end AtiyahSinger.ComplexBundle
