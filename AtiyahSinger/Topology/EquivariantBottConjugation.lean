/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.OrthogonalComplexification
public import AtiyahSinger.Analysis.SphereHodgeIndex
public import AtiyahSinger.Geometry.OrthogonalGroupManifold
public import AtiyahSinger.Topology.AntipodalCircleHomotopy
public import AtiyahSinger.Topology.EquivariantBottRepresentation
public import AtiyahSinger.Topology.EquivariantBundleHomotopy
public import AtiyahSinger.Topology.EquivariantProperHomotopy
public import AtiyahSinger.Topology.EquivariantRepresentationNaturality
public import AtiyahSinger.Topology.EquivariantRepresentationNormalForm
public import AtiyahSinger.Topology.OrthogonalLineRepresentationModels
public import AtiyahSinger.Topology.OrthogonalPlaneConjugationHomotopy

/-!
# Complex conjugation on the low-dimensional equivariant Bott groups

Public module ID: M1756.

AL01: the original real matrix action on W extends complex linearly to its
complexification, presented on `EuclideanSpace ℂ (Fin r)`. Coordinatewise
conjugation is an actual proper equivariant map of this space. Its action on
the existing equivariant support group is the previously constructed proper
pullback, not a newly specified endomorphism with the desired value.

For O(1), conjugation sends every class a to minus the determinant line times a.
For SO(2), it fixes every class on the complexification of the real plane. This
space has complex dimension two; it is not the one-dimensional complex rotation
character. Both conclusions quantify over the whole original support quotient.

Source: Atiyah--Singer I, Lemma (2.8), printed p.496. The line proof uses radial
representatives on the original fixed representation bundles and contracts
their conjugate-plus-determinant boundary by the explicit paired path. No Bott
generation or identification with a different exterior carrier is presumed.
The plane calculation uses the proper equivariant real-linear homotopy
u + i v ↦ u + i R(πt)v. Its uniformly compact control is essential for pullback
with compact supports. The original native SO(2) action is the restriction of
the same O(2) matrix action.

The sphere-index module supplies only the existing actual determinant
representation. No sphere index calculation, P07 or final index theorem is
used in either conjugation argument. Both formulas retain the original support
quotient, its actual pullback and coefficient action, and their specified bundle models.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct unitInterval

attribute [local instance] trivialTopology isFiniteRank_trivial sumTopology isFiniteRank_sum
  tensorTopology isFiniteRank_tensor isFiniteRank_pullback

/-- Pullback by actual coordinatewise conjugation on the original O(r) complexification. -/
def orthogonalComplexificationConjugationPullback (r : ℕ) :
    EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (EuclideanSpace ℂ (Fin r)) →+
      EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (EuclideanSpace ℂ (Fin r)) :=
  equivariantSupportTripleKZeroPullback (orthogonalComplexificationConjugation r)
    (orthogonalComplexificationConjugation_equivariant r)
    (orthogonalComplexificationConjugation_isProperMap r)

/-- The same conjugation pullback with the original matrix action restricted to SO(r). -/
def specialOrthogonalComplexificationConjugationPullback (r : ℕ) :
    EquivariantSupportTripleKZero (Matrix.specialOrthogonalGroup (Fin r) ℝ)
        (EuclideanSpace ℂ (Fin r)) →+
      EquivariantSupportTripleKZero (Matrix.specialOrthogonalGroup (Fin r) ℝ)
        (EuclideanSpace ℂ (Fin r)) :=
  equivariantSupportTripleKZeroPullback (orthogonalComplexificationConjugation r)
    (fun A z ↦ orthogonalComplexificationConjugation_equivariant r
      (specialOrthogonalGroupInclusion r A) z)
    (orthogonalComplexificationConjugation_isProperMap r)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxSynthPendingDepth 30 in
set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
-- Keep the original support quotient and all tensor, sum, and cylinder models in one proof.
/-- Conjugation on the complexified real sign line acts by minus the determinant character. -/
theorem orthogonalLineConjugationPullback_eq_neg_det_smul
    (a : EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin 1) ℝ)
      (EuclideanSpace ℂ (Fin 1))) :
    orthogonalComplexificationConjugationPullback 1 a =
      -(finiteRepresentationClass (orthogonalDeterminantRepresentation 1) • a) := by
  classical
  let G := Matrix.orthogonalGroup (Fin 1) ℝ
  let V := EuclideanSpace ℂ (Fin 1)
  let C₀ := {z : ℂ // z ≠ 0}
  let := compactSpace_orthogonalGroup 1
  -- Fix one representative of the supplied original class and its two actual representations.
  obtain ⟨ρ, τ, d, hd, hd0, hdradial, hdclass⟩ :=
    exists_equivariant_representation_radial_representative
      (orthogonalComplexification_unitary 1) a
  let U := Fin ρ.dimension → ℂ
  let W := Fin τ.dimension → ℂ
  let E := FiniteBundle.trivial V ρ.dimension
  let F := FiniteBundle.trivial V τ.dimension
  let ρE : EquivariantStructure G E.Fiber := .ofFiniteRepresentation ρ
  let τF : EquivariantStructure G F.Fiber := .ofFiniteRepresentation τ
  let a₀ := EquivariantSupportBundleTriple.ofBoundary E F d ρE τF hd
  let δ := orthogonalDeterminantRepresentation 1
  let ρ' := orthogonalLineDeterminantTwist ρ
  let τ' := orthogonalLineDeterminantTwist τ
  let f := orthogonalComplexificationConjugation 1
  let b := a₀.pullback f (orthogonalComplexificationConjugation_equivariant 1)
    (orthogonalComplexificationConjugation_isProperMap 1)
  let c := a₀.tensorRepresentation δ
  let s := b.sum c
  let S := E.sum E
  let T := F.sum F
  let σS : EquivariantStructure G S.Fiber :=
    ρE.sum (EquivariantStructure.ofFiniteRepresentation ρ')
  let σT : EquivariantStructure G T.Fiber :=
    τF.sum (EquivariantStructure.ofFiniteRepresentation τ')
  -- The native matrix group consists of the two scalar matrices; keep its actual actions.
  have hcases (A : G) : A = 1 ∨ A = -1 := by
    have h := congrArg Matrix.det
      ((Matrix.mem_orthogonalGroup_iff' (Fin 1) ℝ).mp A.property)
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    rcases mul_self_eq_one_iff.mp h with hA | hA
    · left
      apply Subtype.ext
      ext i j
      fin_cases i
      fin_cases j
      change A.val 0 0 = 1
      simpa only [Matrix.det_fin_one] using hA
    · right
      apply Subtype.ext
      ext i j
      fin_cases i
      fin_cases j
      change A.val 0 0 = -1
      simpa only [Matrix.det_fin_one] using hA
  have haction (A : G) (z : V) : A • z = (A.val.det : ℂ) • z := by
    ext k
    fin_cases k
    change (∑ j : Fin 1, (A.val 0 j : ℂ) * z j) = (A.val.det : ℂ) * z 0
    simp only [Fin.sum_univ_one, Matrix.det_fin_one]
  have hnegdet : (((-1 : G).val.det : ℝ) : ℂ) = -1 := by
    rw [Matrix.det_fin_one]
    change ((-1 : ℝ) : ℂ) = -1
    norm_num
  have hnegaction (z : V) : (-1 : G) • z = -z := by
    rw [haction, hnegdet, neg_one_smul]
  have hinvol (ρ₀ : FiniteContinuousRepresentation G) :
      Function.Involutive (ρ₀.representation (-1 : G)) := by
    intro v
    have hmul : (-1 : G) * (-1 : G) = 1 := by
      apply Subtype.ext
      change (-1 : Matrix (Fin 1) (Fin 1) ℝ) * (-1) = 1
      simp
    have h := congrArg
      (fun R : (Fin ρ₀.dimension → ℂ) →L[ℂ] (Fin ρ₀.dimension → ℂ) ↦ R v)
      (map_mul ρ₀.representation (-1 : G) (-1 : G))
    simpa only [hmul, map_one, one_apply_eq_self,
      mul_apply_eq_comp] using h.symm
  let A : U ≃ₗ[ℂ] U :=
    { toFun := ρ.representation (-1 : G)
      invFun := ρ.representation (-1 : G)
      left_inv := hinvol ρ
      right_inv := hinvol ρ
      map_add' := map_add _
      map_smul' := map_smul _ }
  let B : W ≃ₗ[ℂ] W :=
    { toFun := τ.representation (-1 : G)
      invFun := τ.representation (-1 : G)
      left_inv := hinvol τ
      right_inv := hinvol τ
      map_add' := map_add _
      map_smul' := map_smul _ }
  have hnegS (x : V) (v : U × U) : σS.linearMap (-1 : G) x v = (A v.1, -A v.2) := by
    change (ρ.representation (-1 : G) v.1,
      (((-1 : G).val.det : ℝ) : ℂ) • ρ.representation (-1 : G) v.2) = _
    rw [hnegdet, neg_one_smul]
    rfl
  have hnegT (x : V) (v : W × W) : σT.linearMap (-1 : G) x v = (B v.1, -B v.2) := by
    change (τ.representation (-1 : G) v.1,
      (((-1 : G).val.det : ℝ) : ℂ) • τ.representation (-1 : G) v.2) = _
    rw [hnegdet, neg_one_smul]
    rfl
  -- Use each determinant tensor isomorphism once, for these same two fixed representations.
  obtain ⟨eρ, heρ, heρval, _⟩ := exists_orthogonalLineDeterminant_tensor_iso (X := V) ρ
  obtain ⟨eτ, heτ, heτval, _⟩ := exists_orthogonalLineDeterminant_tensor_iso (X := V) τ
  let e := (pullbackTrivialIso f ρ.dimension).sum eρ
  let g := (pullbackTrivialIso f τ.dimension).sum eτ
  have he : e.IsEquivariant s.2.sourceAction σS := by
    intro Q x v
    apply Prod.ext
    · change (pullbackTrivialIso f ρ.dimension).linearEquiv (Q • x)
        (ρ.representation Q v.1) =
          ρ.representation Q ((pullbackTrivialIso f ρ.dimension).linearEquiv x v.1)
      rw [pullbackTrivialIso_apply, pullbackTrivialIso_apply]
    · exact heρ Q x v.2
  have hg : g.IsEquivariant s.2.targetAction σT := by
    intro Q x v
    apply Prod.ext
    · change (pullbackTrivialIso f τ.dimension).linearEquiv (Q • x)
        (τ.representation Q v.1) =
          τ.representation Q ((pullbackTrivialIso f τ.dimension).linearEquiv x v.1)
      rw [pullbackTrivialIso_apply, pullbackTrivialIso_apply]
    · exact heτ Q x v.2
  let dsum := s.1.datum.congr e g
  obtain ⟨hsum, hsumclass⟩ := exists_equivariantSupportTransport s S T σS σT e g he hg
  have hfinvol : Function.Involutive f := by
    intro z
    ext k
    exact star_star (z k)
  have hf0 : f (0 : V) = 0 := by
    ext k
    exact star_zero _
  have hb0 : b.1.datum.control = ({0} : Set V) := by
    ext z
    change f z ∈ d.control ↔ z ∈ ({0} : Set V)
    rw [hd0]
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hz
      exact hfinvol.injective (hz.trans hf0.symm)
    · rintro rfl
      exact hf0
  have hsum0 : dsum.control = ({0} : Set V) := by
    change b.1.datum.control ∪ c.1.datum.control = _
    rw [hb0]
    change ({0} : Set V) ∪ d.control = _
    rw [hd0, Set.union_self]
  let K := dsum.control
  have hK : IsCompact K := dsum.isCompact_control
  have hKInv (Q : G) (x : V) : Q • x ∈ K ↔ x ∈ K := hsum.invariant_control Q x
  -- Evaluate the original boundary on the actual nonzero complex coordinate.
  let embed : C(ℂ, V) := ⟨fun z ↦ WithLp.toLp 2 (fun _ : Fin 1 ↦ z),
    (PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℂ)).comp (continuous_pi fun _ ↦ continuous_id)⟩
  have hembed0 (z : C₀) : embed z.val ∈ d.controlᶜ := by
    rw [hd0]
    intro hz
    apply z.property
    have hv := congrArg (fun v : V ↦ v 0) (Set.mem_singleton_iff.mp hz)
    exact hv
  let q : C(C₀, (d.controlᶜ : Set V)) :=
    ⟨fun z ↦ ⟨embed z.val, hembed0 z⟩,
      (embed.continuous.comp continuous_subtype_val).subtype_mk hembed0⟩
  let inc : C((d.controlᶜ : Set V), V) := ⟨Subtype.val, continuous_subtype_val⟩
  let flat (k : ℕ) :=
    (pullbackCompIso (E := Bundle.Trivial V (Fin k → ℂ)) inc q).trans
      (pullbackTrivialIso (inc.comp q) k)
  have hflat (k : ℕ) (z : C₀) (v : Fin k → ℂ) : (flat k).linearEquiv z v = v := by
    change (pullbackTrivialIso (inc.comp q) k).linearEquiv z
      ((pullbackCompIso (E := Bundle.Trivial V (Fin k → ℂ)) inc q).linearEquiv z v) = v
    rw [pullbackCompIso_apply, pullbackTrivialIso_apply]
  let aC : Iso (Bundle.Trivial C₀ U) (Bundle.Trivial C₀ W) :=
    (flat ρ.dimension).symm.trans ((Iso.pullback q d.boundary).trans (flat τ.dimension))
  have haC (z : C₀) (v : U) : aC.linearEquiv z v = d.boundary.linearEquiv (q z) v := by
    have hfi : ((flat ρ.dimension).linearEquiv z).symm v = v := by
      apply ((flat ρ.dimension).linearEquiv z).injective
      rw [LinearEquiv.apply_symm_apply, hflat]
    change (flat τ.dimension).linearEquiv z
      (d.boundary.linearEquiv (q z) (((flat ρ.dimension).linearEquiv z).symm v)) = _
    rw [hflat, hfi]
  have haCradial (t : ℝ) (ht : 0 < t) (z : C₀) (v : U) :
      aC.linearEquiv ⟨t • z.val, smul_ne_zero ht.ne' z.property⟩ v = aC.linearEquiv z v := by
    rw [haC, haC]
    have hq : q ⟨t • z.val, smul_ne_zero ht.ne' z.property⟩ =
        ⟨(t : ℂ) • (q z).val, by
          have h := hembed0 ⟨t • z.val, smul_ne_zero ht.ne' z.property⟩
          exact h⟩ := by
      apply Subtype.ext
      ext k
      rfl
    rw [hq]
    exact congrArg (fun L : U ≃ₗ[ℂ] W ↦ L v)
      (hdradial (q z).val t ht (q z).property _)
  have haCanti (z : C₀) (v : U) :
      aC.linearEquiv ⟨-z.val, neg_ne_zero.mpr z.property⟩ (A v) = B (aC.linearEquiv z v) := by
    rw [haC, haC]
    have hq : q ⟨-z.val, neg_ne_zero.mpr z.property⟩ =
        ⟨(-1 : G) • (q z).val,
          fun hz ↦ (q z).property ((hd.invariant_control (-1 : G) (q z).val).mp hz)⟩ := by
      apply Subtype.ext
      change embed (-z.val) = (-1 : G) • embed z.val
      rw [hnegaction]
      ext k
      rfl
    rw [hq]
    exact hd.boundary_intertwines (-1 : G) (q z) v
  obtain ⟨H, L, hH0, hH1, hHanti, hLanti⟩ :=
    exists_antipodal_paired_homotopy_of_radial_iso A B (hinvol ρ) (hinvol τ)
      aC haCradial haCanti
  -- The two ordinary trivial coordinates give the original double-bundle total topology.
  let doubleModel (Y : Type) [TopologicalSpace Y] (k : ℕ) :
      TotalSpace Unit ((Bundle.Trivial Y (Fin k → ℂ)) ×ᵇ
        (Bundle.Trivial Y (Fin k → ℂ))) ≃ₜ Y × ((Fin k → ℂ) × (Fin k → ℂ)) :=
    { toFun z := (z.proj, z.snd)
      invFun z := ⟨z.1, z.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by
        have hc : Continuous (fun z : TotalSpace Unit (Bundle.Trivial Y (Fin k → ℂ)) ↦
            (z.proj, z.snd)) := continuous_induced_dom
        have h₁ := hc.comp (continuous_sum_fst (E := Bundle.Trivial Y (Fin k → ℂ))
          (F := Bundle.Trivial Y (Fin k → ℂ)))
        have h₂ := hc.comp (continuous_sum_snd (E := Bundle.Trivial Y (Fin k → ℂ))
          (F := Bundle.Trivial Y (Fin k → ℂ)))
        exact h₁.fst.prodMk (h₁.snd.prodMk h₂.snd)
      continuous_invFun := by
        apply continuous_induced_rng.mpr
        exact (continuous_induced_rng.mpr
          (continuous_fst.prodMk continuous_snd.fst)).prodMk
          (continuous_induced_rng.mpr (continuous_fst.prodMk continuous_snd.snd)) }
  let doublePull {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
      (p : C(Y, Z)) (k : ℕ) :
      Iso (p *ᵖ ((Bundle.Trivial Z (Fin k → ℂ)) ×ᵇ (Bundle.Trivial Z (Fin k → ℂ))))
        ((Bundle.Trivial Y (Fin k → ℂ)) ×ᵇ (Bundle.Trivial Y (Fin k → ℂ))) :=
    { linearEquiv _ := LinearEquiv.refl ℂ _
      continuous_total := by
        let D := (Bundle.Trivial Z (Fin k → ℂ)) ×ᵇ (Bundle.Trivial Z (Fin k → ℂ))
        have hb := Pullback.continuous_proj Unit D p
        have hv := ((doubleModel Z k).continuous.comp
          (Pullback.continuous_lift Unit D p)).snd
        exact (doubleModel Y k).symm.continuous.comp (hb.prodMk hv)
      continuous_symm := by
        let D := (Bundle.Trivial Z (Fin k → ℂ)) ×ᵇ (Bundle.Trivial Z (Fin k → ℂ))
        apply (inducing_pullbackTotalSpaceEmbedding Unit D p).continuous_iff.mpr
        have hy := (doubleModel Y k).continuous
        exact hy.fst.prodMk ((doubleModel Z k).symm.continuous.comp
          ((p.continuous.comp hy.fst).prodMk hy.snd)) }
  have hcoordNe (x : (Kᶜ : Set V)) : x.val 0 ≠ 0 := by
    intro hz
    apply x.property
    change x.val ∈ dsum.control
    rw [hsum0]
    apply Set.mem_singleton_iff.mpr
    ext k
    fin_cases k
    exact hz
  let coordinate : C((Kᶜ : Set V), C₀) :=
    ⟨fun x ↦ ⟨x.val 0, hcoordNe x⟩,
      ((PiLp.continuous_apply 2 (fun _ : Fin 1 ↦ ℂ) 0).comp
        continuous_subtype_val).subtype_mk hcoordNe⟩
  let Q : C(I × (Kᶜ : Set V), I × C₀) :=
    ⟨fun p ↦ (p.1, coordinate p.2), continuous_fst.prodMk
      (coordinate.continuous.comp continuous_snd)⟩
  let incK : C((Kᶜ : Set V), V) := ⟨Subtype.val, continuous_subtype_val⟩
  let pr : C(I × (Kᶜ : Set V), (Kᶜ : Set V)) := ⟨Prod.snd, continuous_snd⟩
  let originalFlat (k : ℕ) :=
    (pullbackCompIso (E := (Bundle.Trivial V (Fin k → ℂ)) ×ᵇ
      (Bundle.Trivial V (Fin k → ℂ))) incK pr).trans (doublePull (incK.comp pr) k)
  let HH := (originalFlat ρ.dimension).trans ((doublePull Q ρ.dimension).symm.trans
    ((Iso.pullback Q H).trans ((doublePull Q τ.dimension).trans
      (originalFlat τ.dimension).symm)))
  have hHH (t : I) (x : (Kᶜ : Set V)) (v : U × U) :
      HH.linearEquiv (t, x) v = H.linearEquiv (t, coordinate x) v := by
    change ((originalFlat τ.dimension).linearEquiv (t, x)).symm
      (H.linearEquiv (t, coordinate x) ((originalFlat ρ.dimension).linearEquiv (t, x) v)) = _
    have hfirst (k : ℕ) (w : (Fin k → ℂ) × (Fin k → ℂ)) :
        (originalFlat k).linearEquiv (t, x) w = w := by
      change (doublePull (incK.comp pr) k).linearEquiv (t, x)
        ((pullbackCompIso (E := (Bundle.Trivial V (Fin k → ℂ)) ×ᵇ
          (Bundle.Trivial V (Fin k → ℂ))) incK pr).linearEquiv (t, x) w) = w
      rw [pullbackCompIso_apply]
      rfl
    apply ((originalFlat τ.dimension).linearEquiv (t, x)).injective
    rw [LinearEquiv.apply_symm_apply, hfirst, hfirst]
  -- The transported sum has exactly the two boundary blocks to which the circle theorem applies.
  have hsumval (x : (Kᶜ : Set V)) (v : U × U) :
      dsum.boundary.linearEquiv x v =
        (aC.linearEquiv ⟨star (coordinate x).val, star_ne_zero.mpr (coordinate x).property⟩ v.1,
          aC.linearEquiv (coordinate x) v.2) := by
    let xb : (b.1.datum.controlᶜ : Set V) :=
      ⟨x.val, fun hx ↦ x.property (Set.mem_union_left _ hx)⟩
    let xc : (c.1.datum.controlᶜ : Set V) :=
      ⟨x.val, fun hx ↦ x.property (Set.mem_union_right _ hx)⟩
    let xf : (d.controlᶜ : Set V) := ⟨f x.val, xb.property⟩
    let xd : (d.controlᶜ : Set V) := ⟨x.val, xc.property⟩
    have hpre : (e.linearEquiv x.val).symm v = (v.1, (1 : Fin 1 → ℂ) ⊗ₜ[ℂ] v.2) := by
      apply (e.linearEquiv x.val).injective
      rw [LinearEquiv.apply_symm_apply]
      change v = ((pullbackTrivialIso f ρ.dimension).linearEquiv x.val v.1,
        eρ.linearEquiv x.val ((1 : Fin 1 → ℂ) ⊗ₜ[ℂ] v.2))
      rw [pullbackTrivialIso_apply, heρval]
      simp only [Pi.one_apply, one_smul]
      exact Prod.ext rfl rfl
    have hqstar :
        q ⟨star (coordinate x).val, star_ne_zero.mpr (coordinate x).property⟩ = xf := by
      apply Subtype.ext
      ext k
      fin_cases k
      rfl
    have hqcoord : q (coordinate x) = xd := by
      apply Subtype.ext
      ext k
      fin_cases k
      rfl
    calc
      _ = g.linearEquiv x.val
          (s.1.datum.boundary.linearEquiv x (v.1, (1 : Fin 1 → ℂ) ⊗ₜ[ℂ] v.2)) := by
        change g.linearEquiv x.val
          (s.1.datum.boundary.linearEquiv x ((e.linearEquiv x.val).symm v)) = _
        rw [hpre]
      _ = g.linearEquiv x.val
          (((b.1.datum.enlarge _ (b.1.datum.isCompact_control.union c.1.datum.isCompact_control)
              Set.subset_union_left).boundary).linearEquiv x v.1,
            ((c.1.datum.enlarge _ (b.1.datum.isCompact_control.union c.1.datum.isCompact_control)
              Set.subset_union_right).boundary).linearEquiv x ((1 : Fin 1 → ℂ) ⊗ₜ[ℂ] v.2)) := by
        apply congrArg (g.linearEquiv x.val)
        exact RelativeTriple.sum_apply _ _ x _
      _ = (d.boundary.linearEquiv xf v.1, d.boundary.linearEquiv xd v.2) := by
        have hbval := (b.1.datum.enlarge_apply _
          (b.1.datum.isCompact_control.union c.1.datum.isCompact_control)
          Set.subset_union_left x v.1).trans
            (RelativeTriple.pullback_apply d.boundary f xb v.1)
        have hcval := (c.1.datum.enlarge_apply _
          (b.1.datum.isCompact_control.union c.1.datum.isCompact_control)
          Set.subset_union_right x ((1 : Fin 1 → ℂ) ⊗ₜ[ℂ] v.2)).trans
            (RelativeTriple.tensorLeft_tmul (FiniteBundle.trivial V 1).Fiber
              d.boundary xd (1 : Fin 1 → ℂ) v.2)
        change ((pullbackTrivialIso f τ.dimension).linearEquiv x.val _,
          eτ.linearEquiv x.val _) = _
        apply Prod.ext
        · exact (congrArg ((pullbackTrivialIso f τ.dimension).linearEquiv x.val) hbval).trans
            (pullbackTrivialIso_apply f τ.dimension x.val _)
        · exact (congrArg (eτ.linearEquiv x.val) hcval).trans
            ((heτval x.val (1 : Fin 1 → ℂ) (d.boundary.linearEquiv xd v.2)).trans
              (by simp only [Pi.one_apply, one_smul]))
      _ = _ := by rw [haC, haC, hqstar, hqcoord]
  -- The constant endpoint is a global isomorphism for the same two doubled actions.
  let globalL : Iso S.Fiber T.Fiber :=
    { linearEquiv _ := L
      continuous_total := (doubleModel V τ.dimension).symm.continuous.comp
        ((doubleModel V ρ.dimension).continuous.fst.prodMk
          (L.continuous_of_finiteDimensional.comp (doubleModel V ρ.dimension).continuous.snd))
      continuous_symm := (doubleModel V ρ.dimension).symm.continuous.comp
        ((doubleModel V τ.dimension).continuous.fst.prodMk
          (L.symm.continuous_of_finiteDimensional.comp
            (doubleModel V τ.dimension).continuous.snd)) }
  have hSone (x : V) (v : U × U) : σS.linearMap 1 x v = v := by
    change (ρ.representation 1 v.1, ρ'.representation 1 v.2) = v
    simp only [map_one, one_apply_eq_self]
    exact Prod.ext rfl rfl
  have hTone (x : V) (v : W × W) : σT.linearMap 1 x v = v := by
    change (τ.representation 1 v.1, τ'.representation 1 v.2) = v
    simp only [map_one, one_apply_eq_self]
    exact Prod.ext rfl rfl
  have hglobal : globalL.IsEquivariant σS σT := by
    intro R x v
    change L (σS.linearMap R x v) = σT.linearMap R x (L v)
    rcases hcases R with rfl | rfl
    · rw [hSone, hTone]
    · rw [hnegS, hnegT]
      exact hLanti v
  let dend := CompactSupportTriple.ofIso globalL
  have hend : dend.IsEquivariant σS σT := by
    refine ⟨?_, ?_⟩
    · intro R x
      simp [dend, CompactSupportTriple.ofIso]
    · intro R x v
      exact hglobal R x.val v
  have hendK : dend.control ⊆ K := by
    change (∅ : Set V) ⊆ K
    exact Set.empty_subset K
  have hhom : dsum.EquivariantlyHomotopic dend σS σT := by
    refine ⟨{ control := K
              isCompact_control := hK
              invariant_control := hKInv
              left_control := Set.Subset.refl _
              right_control := hendK
              homotopy := { iso := HH, map_zero := ?_, map_one := ?_ }
              intertwines := ?_ }⟩
    · intro x v
      change U × U at v
      have hstart := (hHH 0 x v).trans (hH0 (coordinate x) v)
      have hboundary := (dsum.enlarge_apply K hK (Set.Subset.refl _) x v).trans
        (hsumval x v)
      exact hstart.trans hboundary.symm
    · intro x v
      change U × U at v
      have hfinish := (hHH 1 x v).trans (hH1 (coordinate x) v)
      have hboundary : (dend.enlarge K hK hendK).boundary.linearEquiv x v = L v :=
        dend.enlarge_apply K hK hendK x v
      exact hfinish.trans hboundary.symm
    · intro t R x v
      change U × U at v
      let Ht : C₀ → ((U × U) ≃ₗ[ℂ] (W × W)) := fun z ↦ H.linearEquiv (t, z)
      let xR : (Kᶜ : Set V) :=
        ⟨R • x.val, fun hx ↦ x.property ((hKInv R x.val).mp hx)⟩
      change HH.linearEquiv (t, xR) (σS.linearMap R x.val v) =
        σT.linearMap R x.val (HH.linearEquiv (t, x) v)
      have hleft := hHH t xR (σS.linearMap R x.val v)
      have hright := congrArg (fun w : W × W ↦ σT.linearMap R x.val w) (hHH t x v)
      have hmiddle : H.linearEquiv (t, coordinate xR) (σS.linearMap R x.val v) =
          σT.linearMap R x.val (H.linearEquiv (t, coordinate x) v) := by
        rcases hcases R with rfl | rfl
        · have hcoord : coordinate xR = coordinate x := by
            apply Subtype.ext
            change ((1 : G) • x.val) 0 = x.val 0
            rw [one_smul]
          have hsource := congrArg (H.linearEquiv (t, coordinate xR)) (hSone x.val v)
          let evaluate : C₀ → W × W := fun z ↦ Ht z v
          have hbase := congrArg evaluate hcoord
          exact hsource.trans (hbase.trans (hTone x.val
            (H.linearEquiv (t, coordinate x) v)).symm)
        · have hcoord : coordinate xR =
              ⟨-(coordinate x).val, neg_ne_zero.mpr (coordinate x).property⟩ := by
            apply Subtype.ext
            change ((-1 : G) • x.val) 0 = -(x.val 0)
            rw [hnegaction]
            rfl
          have hsource := congrArg (H.linearEquiv (t, coordinate xR)) (hnegS x.val v)
          let evaluate : C₀ → W × W := fun z ↦ Ht z (A v.1, -A v.2)
          have hbase := congrArg evaluate hcoord
          exact hsource.trans (hbase.trans ((hHanti t (coordinate x) v).trans
            (hnegT x.val (H.linearEquiv (t, coordinate x) v)).symm))
      exact hleft.trans (hmiddle.trans hright.symm)
  -- The actual quotient relations now make this same sum zero.
  let endpoint := EquivariantSupportBundleTriple.ofBoundary S T dend σS σT hend
  have hiso : endpoint.IsIsomorphic (EquivariantSupportBundleTriple.identity T σT) := by
    refine ⟨∅, isCompact_empty, ?_, Set.Subset.refl _, Set.Subset.refl _,
      globalL, Iso.refl T.Fiber, hglobal, ?_, ?_⟩
    · intro R x
      simp
    · intro R x v
      rfl
    · intro x v
      have hleft : (endpoint.1.datum.enlarge ∅ isCompact_empty
          (Set.Subset.refl _)).boundary.linearEquiv x v = globalL.linearEquiv x.val v :=
        endpoint.1.datum.enlarge_apply ∅ isCompact_empty (Set.Subset.refl _) x v
      have hright : ((EquivariantSupportBundleTriple.identity T σT).1.datum.enlarge
          ∅ isCompact_empty (Set.Subset.refl _)).boundary.linearEquiv x
            (globalL.linearEquiv x.val v) = globalL.linearEquiv x.val v :=
        (EquivariantSupportBundleTriple.identity T σT).1.datum.enlarge_apply
          ∅ isCompact_empty (Set.Subset.refl _) x (globalL.linearEquiv x.val v)
      exact hleft.trans hright.symm
  have hzero : endpoint.kZeroClass = 0 :=
    (equivariantSupportTripleKZero_generator_relations.1 _ _ hiso).trans
      (equivariantSupportTripleKZero_generator_relations.2.2 T σT)
  have hsumzero : s.kZeroClass = 0 := hsumclass.symm.trans
    ((equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
      S T σS σT dsum dend hsum hend hhom).trans hzero)
  have hadd : b.kZeroClass + c.kZeroClass = 0 :=
    (equivariantSupportTripleKZero_generator_relations.2.1 b c).symm.trans hsumzero
  have hresult : orthogonalComplexificationConjugationPullback 1 a₀.kZeroClass =
      -(finiteRepresentationClass δ • a₀.kZeroClass) := by
    change equivariantSupportTripleKZeroPullback f
      (orthogonalComplexificationConjugation_equivariant 1)
      (orthogonalComplexificationConjugation_isProperMap 1) a₀.kZeroClass = _
    rw [equivariantSupportTripleKZeroPullback_apply]
    calc
      b.kZeroClass = -c.kZeroClass := eq_neg_of_add_eq_zero_left hadd
      _ = _ := congrArg Neg.neg
        (equivariantSupportRepresentationAction_finiteClass δ a₀).symm
  change a₀.kZeroClass = a at hdclass
  simpa only [hdclass] using hresult

/-- Conjugation fixes every equivariant support class on the complexified real rotation plane. -/
theorem specialOrthogonalPlaneConjugationPullback_eq
    (a : EquivariantSupportTripleKZero (Matrix.specialOrthogonalGroup (Fin 2) ℝ)
      (EuclideanSpace ℂ (Fin 2))) :
    specialOrthogonalComplexificationConjugationPullback 2 a = a := by
  /- Use the established homotopy H(t,u+i*v)=u+i*R(pi*t)v on the
  original complexified real plane. It joins identity to coordinate
  conjugation and intertwines the native SO(2) action. Norm preservation
  provides properness of the whole compact-parameter homotopy.
  Apply the existing equivariant proper-homotopy pullback theorem to
  this H and the displayed original endpoint witnesses. That theorem
  retains one compact control and fixed-action bundle transport on
  the cylinder. Rewrite identity pullback, then evaluate the resulting
  homomorphism equality on a and reverse it to the stated direction. -/
  let := compactSpace_orthogonalGroup 2
  have hc : IsCompact (Matrix.orthogonalGroup (Fin 2) ℝ : Set (Matrix (Fin 2) (Fin 2) ℝ)) :=
    isCompact_iff_compactSpace.mpr inferInstance
  have hd : IsClosed {A : Matrix (Fin 2) (Fin 2) ℝ | A.det = 1} :=
    isClosed_eq continuous_id.matrix_det continuous_const
  have hs : IsCompact (Matrix.specialOrthogonalGroup (Fin 2) ℝ :
      Set (Matrix (Fin 2) (Fin 2) ℝ)) :=
    hc.inter_right hd
  let : CompactSpace (Matrix.specialOrthogonalGroup (Fin 2) ℝ) :=
    isCompact_iff_compactSpace.mp hs
  obtain ⟨H, hp, he⟩ := exists_proper_specialOrthogonalPlaneConjugation_homotopy
  -- Apply proper homotopy invariance to the exact native action and coordinate conjugation.
  have h := equivariantSupportTripleKZeroPullback_eq_of_proper_homotopy
    (ContinuousMap.id (EuclideanSpace ℂ (Fin 2))) (orthogonalComplexificationConjugation 2)
    (fun _ _ ↦ rfl)
    (fun A z ↦ orthogonalComplexificationConjugation_equivariant 2
      (specialOrthogonalGroupInclusion 2 A) z)
    isProperMap_id (orthogonalComplexificationConjugation_isProperMap 2) H he hp
  rw [equivariantSupportTripleKZeroPullback_id] at h
  exact (DFunLike.congr_fun h a).symm

end AtiyahSinger
