/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianCompactness
public import AtiyahSinger.Topology.HermitianMetricPullback
public import AtiyahSinger.Topology.ProjectiveLineExtension
public import AtiyahSinger.Topology.ProjectiveStableDegreeDetection

/-!
# Detection after extending a finite family of actual complex lines

Public module ID: M2023.

Over a compact Hausdorff base and in a specified even degree, successive
projectivizations of a line plus a sufficiently large trivial complement extend
a finite family of actual line bundles to a compact Hausdorff common space.
Their specified sections recover the original lines by actual pullback Isos.
If a rational class in that degree is annihilated by the product of the extended
first Chern classes, its restriction along the common section vanishes.

The proof cancels the newest projective root in its stable degree range and
then pulls back along that same section before treating the preceding root.
It never cancels an Euler class on the original base or assumes injectivity
of an earlier root after a later projectivization.

Source: the projective bundle theorem and its stable-degree splitting argument,
Hatcher, Vector Bundles and K-Theory, Section 3.1; SG III.11--III.12.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory

universe u

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial
  isFiniteRank_pullback hermitianProjectiveTopology hermitianProjectiveLineTopology
  isFiniteRank_hermitianProjectiveLine

set_option maxHeartbeats 1500000 in
-- The finite tower retains dependent original norm and topology witnesses in every pullback.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A finite actual line family admits a common section detecting classes after its root product. -/
theorem exists_projectiveSplitDetection (r k : ℕ)
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (L : Fin r → X → Type u)
    [∀ i x, NormedAddCommGroup (L i x)] [∀ i x, NormedSpace ℂ (L i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))] [∀ i, IsFiniteRank (L i)]
    (hL : ∀ i, ContinuousHermitianMetric (L i))
    (hline : ∀ i x, Module.finrank ℂ (L i x) = 1) :
    ∃ (Q : TopCat.{u}) (_ : CompactSpace Q) (_ : T2Space Q)
      (M : Fin r → Q → Type u) (normM : ∀ i y, NormedAddCommGroup (M i y)),
      letI := normM
      ∃ spaceM : ∀ i y, NormedSpace ℂ (M i y),
        letI := spaceM
        ∃ topologyM : ∀ i, TopologicalSpace (TotalSpace Unit (M i)),
          letI := topologyM
          ∃ finiteM : ∀ i, IsFiniteRank (M i),
            letI := finiteM
            ∃ (_hM : ∀ i, ContinuousHermitianMetric (M i))
              (hlineM : ∀ i y, Module.finrank ℂ (M i y) = 1)
              (p : C(Q, X)) (s : C(X, Q)),
              p.comp s = ContinuousMap.id X ∧
              (∀ i, Nonempty (Iso ((s : X → Q) *ᵖ (M i)) (L i))) ∧
              ∀ a : singularCohomology ℚ Q (2 * k),
                (∏ i : Fin r, singularEvenCohomologyOf ℚ Q 1
                    (singularCohomologyRationalization Q 2 (firstChernClass (M i) (hlineM i)))) *
                    singularEvenCohomologyOf ℚ Q k a = 0 →
                  singularCohomologyPullback ℚ s (2 * k) a = 0 := by
  classical
  induction r generalizing X with
  | zero =>
    let M : Fin 0 → X → Type u := L
    refine ⟨TopCat.of X, inferInstance, inferInstance, M, inferInstance, inferInstance,
      inferInstance, inferInstance, hL, hline, ContinuousMap.id X, ContinuousMap.id X,
      rfl, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro a ha
      have hz : a = 0 := by
        apply singularEvenCohomologyOf_injective ℚ X k
        rw [map_zero]
        simpa using ha
      rw [hz, map_zero]
  | succ r ih =>
    obtain ⟨Y, cY, tY, M, nM, sM, τM, fM, hM, hm, p, s, hps, hiso, hdet⟩ :=
      ih (fun i ↦ L i.succ) (fun i ↦ hL i.succ) (fun i ↦ hline i.succ)
    let := cY
    let := tY
    let := nM
    let := sM
    let := τM
    let := fM
    -- Extend the remaining original line over the same previously constructed space.
    let nL : ∀ i x, NormedAddCommGroup (L i x) := inferInstance
    let sL : ∀ i x, NormedSpace ℂ (L i x) := inferInstance
    let A := (p : Y → X) *ᵖ (L 0)
    let : ∀ y, NormedAddCommGroup (A y) := fun y ↦ nL 0 (p y)
    let : ∀ y, NormedSpace ℂ (A y) := fun y ↦ sL 0 (p y)
    let hA := (hL 0).pullback p
    let N := k + r + 1
    let U := Bundle.Trivial Y (ULift.{u} (EuclideanSpace ℂ (Fin N)))
    let := modelTopology (ULift.{u} (EuclideanSpace ℂ (Fin N))) U
    let := isFiniteRank_model (ULift.{u} (EuclideanSpace ℂ (Fin N))) U
    let hU : ContinuousHermitianMetric U := (nonempty_continuousHermitianMetric U).some
    have hAline : ∀ y, Module.finrank ℂ (A y) = 1 := fun y ↦ hline 0 (p y)
    have hUrank : ∀ y, Module.finrank ℂ (U y) = N := by
      intro y
      exact ULift.moduleEquiv.finrank_eq.trans finrank_euclideanSpace_fin
    obtain ⟨b, v, qsection, hqsection, ⟨eA⟩⟩ :=
      exists_hermitianProjective_sum_line_section A U N hA hU hAline hUrank
    let D := A ×ᵇ U
    let V := EuclideanSpace ℂ (Fin (1 + N))
    let := nativeModelTopology D V
    let := b
    let := v
    let hD := (hA.sum hU).normedNativeModelMetric D (1 + N)
    let Q := HermitianProjectiveBundle (1 + N) D hD
    let T := HermitianProjectiveLine (1 + N) D hD
    let q := hermitianProjectiveProjection (1 + N) D hD
    let : CompactSpace Q := compactSpace_hermitianProjectiveBundle (1 + N) D hD
    let : T2Space Q := t2Space_hermitianProjectiveBundle (1 + N) D hD
    let hT : ContinuousHermitianMetric T := (nonempty_continuousHermitianMetric T).some
    let P (i : Fin r) := (q : Q → Y) *ᵖ (M i)
    let : ∀ i z, NormedAddCommGroup (P i z) := fun i z ↦ nM i (q z)
    let : ∀ i z, NormedSpace ℂ (P i z) := fun i z ↦ sM i (q z)
    let : ∀ i, IsFiniteRank (P i) := fun i ↦ isFiniteRank_pullback (E := M i) q
    let hP (i : Fin r) := (hM i).pullback q
    let hTline : ∀ z, Module.finrank ℂ (T z) = 1 := fun z ↦ z.2.property.2.1
    let hPline (i : Fin r) (z : Q) : Module.finrank ℂ (P i z) = 1 := hm i (q z)
    let nT : ∀ z, NormedAddCommGroup (T z) := inferInstance
    let sT : ∀ z, NormedSpace ℂ (T z) := inferInstance
    let τT : TopologicalSpace (TotalSpace Unit T) := inferInstance
    let fT : IsFiniteRank T := inferInstance
    let nP : ∀ i z, NormedAddCommGroup (P i z) := inferInstance
    let sP : ∀ i z, NormedSpace ℂ (P i z) := inferInstance
    let τP : ∀ i, TopologicalSpace (TotalSpace Unit (P i)) := inferInstance
    let fP : ∀ i, IsFiniteRank (P i) := inferInstance
    let B : Fin (r + 1) → Q → Type u := Fin.cases T P
    let nB : ∀ i z, NormedAddCommGroup (B i z) := Fin.cases nT nP
    let sB : ∀ i z, NormedSpace ℂ (B i z) := Fin.cases sT sP
    let τB : ∀ i, TopologicalSpace (TotalSpace Unit (B i)) := Fin.cases τT τP
    let fB : ∀ i, IsFiniteRank (B i) := Fin.cases fT fP
    let hB : ∀ i, ContinuousHermitianMetric (B i) := Fin.cases hT hP
    let hBline : ∀ i z, Module.finrank ℂ (B i z) = 1 := Fin.cases hTline hPline
    -- The same local sections and their vector-preserving pullback Isos compose.
    change q.comp qsection = ContinuousMap.id Y at hqsection
    let eBase : Iso ((s : X → Y) *ᵖ A) (L 0) := by
      have e := pullbackCompIso (E := L 0) p s
      rw [hps] at e
      exact e.trans (pullbackIdIso (E := L 0))
    let eP (i : Fin r) : Iso ((qsection : Y → Q) *ᵖ (P i)) (M i) := by
      have e := pullbackCompIso (E := M i) q qsection
      rw [hqsection] at e
      exact e.trans (pullbackIdIso (E := M i))
    refine ⟨TopCat.of Q, inferInstance, inferInstance, B, nB, sB, τB, fB, hB, hBline,
      p.comp q, qsection.comp s, ?_, ?_, ?_⟩
    · apply ContinuousMap.ext
      intro x
      change p (q (qsection (s x))) = x
      rw [show q (qsection (s x)) = s x from congrArg (fun f ↦ f (s x)) hqsection]
      exact congrArg (fun f ↦ f x) hps
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact ⟨((pullbackCompIso (E := T) qsection s).symm.trans
          (eA.pullback s)).trans eBase⟩
      · exact ⟨((pullbackCompIso (E := P j) qsection s).symm.trans
          ((eP j).pullback s)).trans (hiso j).some⟩
    · intro a ha
      let roots (i : Fin r) : singularCohomology ℚ Q 2 :=
        singularCohomologyRationalization Q 2 (firstChernClass (P i) (hPline i))
      let t : singularCohomology ℚ Q 2 :=
        singularCohomologyRationalization Q 2 (firstChernClass T hTline)
      let c := singularCohomologyElementarySymmetric ℚ Q (List.ofFn roots) r
      let z := singularCohomologyEvenCup ℚ Q r k c a
      -- The other r roots times a are a homogeneous class of degree 2(r+k).
      have hc : singularEvenCohomologyOf ℚ Q r c =
          ∏ i : Fin r, singularEvenCohomologyOf ℚ Q 1 (roots i) := by
        rw [singularEvenCohomologyOf_elementarySymmetric, ← Fin.univ_val_map,
          Multiset.map_map, Finset.esymm_map_val]
        have hp : (Finset.univ : Finset (Fin r)).powersetCard r = {Finset.univ} := by
          simpa only [Finset.card_univ, Fintype.card_fin] using
            (Finset.powersetCard_self (Finset.univ : Finset (Fin r)))
        rw [hp, Finset.sum_singleton]
        rfl
      have hz : singularEvenCohomologyOf ℚ Q (r + k) z =
          (∏ i : Fin r, singularEvenCohomologyOf ℚ Q 1 (roots i)) *
            singularEvenCohomologyOf ℚ Q k a := by
        rw [singularEvenCohomologyOf_cup, hc]
      have ht : singularCohomologyChangeCoefficients ℚ Q 2
          (hermitianProjectiveChernRoot (1 + N) D hD) = t := by
        rw [singularCohomologyChangeCoefficients_rat]
        rfl
      have hcancel := hermitianProjectiveChernRoot_evenCup_injective ℚ (1 + N) D hD
        (r + k) (by dsimp only [N]; omega)
      rw [ht] at hcancel
      have hzt : singularCohomologyEvenCup ℚ Q (r + k) 1 z t = 0 := by
        apply singularEvenCohomologyOf_injective ℚ Q (r + k + 1)
        rw [singularEvenCohomologyOf_cup, map_zero, hz]
        have ha' : singularEvenCohomologyOf ℚ Q 1 t *
            (∏ i : Fin r, singularEvenCohomologyOf ℚ Q 1 (roots i)) *
              singularEvenCohomologyOf ℚ Q k a = 0 := by
          simpa only [Fin.prod_univ_succ, B, hBline, Fin.cases_zero, Fin.cases_succ] using ha
        rw [mul_comm _ (singularEvenCohomologyOf ℚ Q 1 t), ← mul_assoc]
        exact ha'
      have hz0 : z = 0 := by
        apply hcancel
        change singularCohomologyEvenCup ℚ Q (r + k) 1 z t =
          (singularCohomologyEvenCup ℚ Q (r + k) 1).flip t 0
        rw [map_zero]
        exact hzt
      have hring : (∏ i : Fin r, singularEvenCohomologyOf ℚ Q 1 (roots i)) *
          singularEvenCohomologyOf ℚ Q k a = 0 := by
        rw [← hz, hz0, map_zero]
      -- Pull back only after cancellation, restoring the exact preceding line family.
      have hroot (i : Fin r) : singularEvenCohomologyPullback ℚ qsection
          (singularEvenCohomologyOf ℚ Q 1 (roots i)) =
          singularEvenCohomologyOf ℚ Y 1
            (singularCohomologyRationalization Y 2 (firstChernClass (M i) (hm i))) := by
        rw [singularEvenCohomologyPullback_of, ← singularCohomologyRationalization_naturality]
        apply congrArg (fun c ↦ singularEvenCohomologyOf ℚ Y 1
          (singularCohomologyRationalization Y 2 c))
        let : ∀ y, NormedAddCommGroup (((qsection : Y → Q) *ᵖ (P i)) y) :=
          fun y ↦ nP i (qsection y)
        let : ∀ y, NormedSpace ℂ (((qsection : Y → Q) *ᵖ (P i)) y) :=
          fun y ↦ sP i (qsection y)
        exact (firstChernClass_pullback (P i) (hPline i) qsection).symm.trans
          (firstChernClass_eq_of_iso ((qsection : Y → Q) *ᵖ (P i))
            (fun y ↦ hPline i (qsection y)) (hm i) (eP i))
      have hback := congrArg (singularEvenCohomologyPullback ℚ qsection) hring
      rw [map_mul, map_prod, map_zero, singularEvenCohomologyPullback_of] at hback
      simp_rw [hroot] at hback
      have hs0 := hdet (singularCohomologyPullback ℚ qsection (2 * k) a) hback
      have hcomp := congrArg (fun f ↦ f a)
        ((singularCohomologyFunctor ℚ (2 * k)).map_comp
          (TopCat.ofHom qsection).op (TopCat.ofHom s).op)
      exact hcomp.trans hs0

end AtiyahSinger.ComplexBundle
