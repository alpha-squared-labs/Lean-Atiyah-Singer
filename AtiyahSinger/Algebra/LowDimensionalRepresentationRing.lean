/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationCharacter
public import AtiyahSinger.Analysis.LowSphereHodgeIndex

import AtiyahSinger.Geometry.OrthogonalGroupManifold

/-!
# Low-dimensional representation-ring normalization

Public module ID: M0039.

AL03: the algebraic step in Atiyah--Singer I, Lemma (4.7), printed pp.507--508.
The rings are the existing Grothendieck rings of actual continuous finite
representations of the native matrix groups O(1) and SO(2). The class ξ is
the already constructed determinant representation of O(1), rather than a
new indeterminate or a class chosen to satisfy the desired equations.

Every virtual O(1) representation has unique integer trivial and determinant
multiplicities. The annihilator of 1 - ξ consists of integer multiples of
1 + ξ. Consequently the equation (1 - ξ) a = 1 - ξ needs the separate
augmentation condition dim(a) = 1 to force a = 1. This dimension is the
original representationDimension map. On SO(2), character injectivity
permits cancellation of the nonzero integer two, without cancelling an
arbitrary representation-ring element or constructing a Laurent model.

The ordinary eigenspace decomposition makes explicit the presentation
R(O(1)) = Z[ξ]/(ξ² - 1) used on p.508. The compact-group character argument
is an equivalent way to justify the source's absence of additive 2-torsion
in R(SO(2)); SO(2) is not a finite group. These statements apply to arbitrary
virtual representations. They do not construct a point-pushforward index
or assume that any supplied virtual representation is such an index.

Applications to index normalization also require the sphere-symbol
decomposition, transport between its two poles and the actual index
equations. The SO(2) conclusion uses the compact-group character theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

local notation "ξ" => finiteRepresentationClass (orthogonalDeterminantRepresentation 1)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
-- The original eigenspace decomposition tracks both finite coordinate equivalences.
/-- Every virtual O(1) representation has unique trivial and determinant multiplicities. -/
theorem existsUnique_orthogonalLineRepresentation_decomposition
    (a : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin 1) ℝ)) :
    ∃! p : ℤ × ℤ, a = p.1 • 1 + p.2 • ξ := by
  classical
  let G := Matrix.orthogonalGroup (Fin 1) ℝ
  -- The original one-by-one orthogonal matrices are precisely the two signs.
  let s : G := ⟨-1, by
    rw [Matrix.mem_orthogonalGroup_iff]
    simp⟩
  have hs : s * s = 1 := by
    apply Subtype.ext
    change (-1 : Matrix (Fin 1) (Fin 1) ℝ) * -1 = 1
    simp
  have hsign (g : G) : g = 1 ∨ g = s := by
    have hsq : g.val 0 0 * g.val 0 0 = 1 := by
      have h := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℝ ↦ A 0 0)
        ((Matrix.mem_orthogonalGroup_iff (Fin 1) ℝ).mp g.property)
      simpa [Matrix.mul_apply] using h
    have hroots : g.val 0 0 = 1 ∨ g.val 0 0 = -1 := by
      have hprod : (g.val 0 0 - 1) * (g.val 0 0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hprod with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hroots with h | h
    · left
      apply Subtype.ext
      ext i j
      fin_cases i
      fin_cases j
      exact h
    · right
      apply Subtype.ext
      ext i j
      fin_cases i
      fin_cases j
      exact h
  -- A scalar action is an actual ordered sum of its one-dimensional lines.
  let scalar (χ : G →* ℂ) (hχ : Continuous χ) (n : ℕ) :
      FiniteContinuousRepresentation G :=
    { dimension := n
      representation := .ofMonoidHom
        { toFun := fun g ↦ χ g • ContinuousLinearMap.id ℂ (Fin n → ℂ)
          map_one' := by ext x i; simp
          map_mul' := by
            intro g h
            ext x i
            simp [map_mul, mul_assoc, mul_left_comm] }
      continuous_action := by
        exact (hχ.comp continuous_fst).smul continuous_snd }
  have hscalar (χ : G →* ℂ) (hχ : Continuous χ) (n : ℕ) :
      finiteRepresentationClass (scalar χ hχ n) =
        n • finiteRepresentationClass (scalar χ hχ 1) := by
    have hadd (n m : ℕ) :
        finiteRepresentationClass (scalar χ hχ (n + m)) =
          finiteRepresentationClass (scalar χ hχ n) +
            finiteRepresentationClass (scalar χ hχ m) := by
      rw [← finiteRepresentationClass_directSum]
      apply finiteRepresentationClass_eq_of_isEquivalent
      refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
      intro g
      apply ContinuousLinearMap.ext
      intro x
      let c : (Fin (n + m) → ℂ) ≃L[ℂ] (Fin n → ℂ) × (Fin m → ℂ) :=
        (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n ⊕ Fin m ↦ ℂ)
          finSumFinEquiv.symm).trans
          (ContinuousLinearEquiv.sumPiEquivProdPi ℂ (Fin n) (Fin m) (fun _ ↦ ℂ))
      change χ g • x = c.symm (χ g • c x)
      rw [map_smul, c.symm_apply_apply]
    induction n with
    | zero =>
      have h := hadd 0 0
      simpa using (add_eq_left.mp h.symm)
    | succ n ih =>
      rw [hadd n 1, ih, succ_nsmul]
  let det : G →* ℂ :=
    { toFun := fun g ↦ (g.val.det : ℂ)
      map_one' := by simp
      map_mul' := by
        intro g h
        change (((g.val * h.val).det : ℝ) : ℂ) = _
        rw [Matrix.det_mul, Complex.ofReal_mul] }
  have hdet : Continuous det :=
    Complex.continuous_ofReal.comp continuous_subtype_val.matrix_det
  have htriv : finiteRepresentationClass (scalar 1 continuous_const 1) =
      (1 : RepresentationGrothendieckGroup G) := by
    apply finiteRepresentationClass_eq_of_isEquivalent
    refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
    intro g
    ext x i
    change (1 : ℂ) * x i = x i
    simp
  have hdetline : finiteRepresentationClass (scalar det hdet 1) = ξ := by
    rfl
  have hfinite (ρ : FiniteContinuousRepresentation G) :
      ∃ m n : ℕ, finiteRepresentationClass ρ = m • (1 : RepresentationGrothendieckGroup G) +
        n • ξ := by
    let T : Module.End ℂ (Fin ρ.dimension → ℂ) := (ρ.representation s).toLinearMap
    have hT (x : Fin ρ.dimension → ℂ) : T (T x) = x := by
      change ρ.representation s (ρ.representation s x) = x
      have h := congrArg (fun f : (Fin ρ.dimension → ℂ) →L[ℂ] (Fin ρ.dimension → ℂ) ↦ f x)
        (map_mul ρ.representation s s)
      simpa [hs] using h.symm
    let P := T.eigenspace 1
    let N := T.eigenspace (-1)
    have hPN : IsCompl P N := by
      constructor
      · apply Submodule.disjoint_def.mpr
        intro x hx hy
        have hx' : T x = x := by simpa using Module.End.mem_eigenspace_iff.mp hx
        have hy' : T x = -x := by simpa using Module.End.mem_eigenspace_iff.mp hy
        have hsum : (2 : ℂ) • x = 0 := by
          calc
            (2 : ℂ) • x = x + x := two_smul ℂ x
            _ = T x + x := congrArg (· + x) hx'.symm
            _ = 0 := by rw [hy', neg_add_cancel]
        exact (smul_eq_zero.mp hsum).resolve_left (by norm_num)
      · rw [codisjoint_iff_le_sup]
        intro x _
        apply Submodule.mem_sup.mpr
        refine ⟨(1 / 2 : ℂ) • (x + T x), ?_, (1 / 2 : ℂ) • (x - T x), ?_, ?_⟩
        · apply Module.End.mem_eigenspace_iff.mpr
          simp only [map_smul, map_add, hT, one_smul]
          rw [add_comm]
        · apply Module.End.mem_eigenspace_iff.mpr
          simp only [map_smul, map_sub, hT, neg_one_smul]
          rw [← neg_sub x (T x), smul_neg]
        · calc
            (1 / 2 : ℂ) • (x + T x) + (1 / 2 : ℂ) • (x - T x) =
                (1 / 2 : ℂ) • ((x + T x) + (x - T x)) := (smul_add _ _ _).symm
            _ = x := by
              rw [show (x + T x) + (x - T x) = (2 : ℂ) • x by rw [two_smul]; abel,
                smul_smul]
              norm_num
    -- Choose coordinates only after constructing the original invariant subspaces.
    let p : P ≃L[ℂ] (Fin (Module.finrank ℂ P) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
    let n : N ≃L[ℂ] (Fin (Module.finrank ℂ N) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
    let d := (P.prodEquivOfIsCompl N hPN).toContinuousLinearEquiv
    let c : (Fin (Module.finrank ℂ P + Module.finrank ℂ N) → ℂ) ≃L[ℂ]
        (Fin (Module.finrank ℂ P) → ℂ) × (Fin (Module.finrank ℂ N) → ℂ) :=
      (ContinuousLinearEquiv.piCongrLeft ℂ
        (fun _ : Fin (Module.finrank ℂ P) ⊕ Fin (Module.finrank ℂ N) ↦ ℂ)
        finSumFinEquiv.symm).trans
        (ContinuousLinearEquiv.sumPiEquivProdPi ℂ
          (Fin (Module.finrank ℂ P)) (Fin (Module.finrank ℂ N)) (fun _ ↦ ℂ))
    let e := (c.trans (p.symm.prodCongr n.symm)).trans d
    have hclass :
        finiteRepresentationClass ((scalar 1 continuous_const (Module.finrank ℂ P)).directSum
          (scalar det hdet (Module.finrank ℂ N))) = finiteRepresentationClass ρ := by
      apply finiteRepresentationClass_eq_of_isEquivalent
      refine ⟨ContRepresentation.Equiv.mk e ?_⟩
      intro g
      apply ContinuousLinearMap.ext
      intro x
      change d ((p.symm.prodCongr n.symm)
        (c (c.symm ((1 : ℂ) • (c x).1, det g • (c x).2)))) =
          ρ.representation g (d ((p.symm.prodCongr n.symm) (c x)))
      rw [c.apply_symm_apply]
      simp only [ContinuousLinearEquiv.prodCongr_apply, one_smul, map_smul]
      change (p.symm (c x).1).val + det g • (n.symm (c x).2).val =
        ρ.representation g ((p.symm (c x).1).val + (n.symm (c x).2).val)
      rcases hsign g with rfl | rfl
      · simp [det]
      · have hp : T (p.symm (c x).1).val = (p.symm (c x).1).val := by
          simpa using Module.End.mem_eigenspace_iff.mp (p.symm (c x).1).property
        have hn : T (n.symm (c x).2).val = -(n.symm (c x).2).val := by
          simpa using Module.End.mem_eigenspace_iff.mp (n.symm (c x).2).property
        change (p.symm (c x).1).val + det s • (n.symm (c x).2).val =
          T ((p.symm (c x).1).val + (n.symm (c x).2).val)
        rw [map_add, hp, hn]
        simp [det, s]
    refine ⟨Module.finrank ℂ P, Module.finrank ℂ N, ?_⟩
    rw [← hclass, finiteRepresentationClass_directSum,
      hscalar 1 continuous_const (Module.finrank ℂ P),
      hscalar det hdet (Module.finrank ℂ N), htriv, hdetline]
  -- The quotient is generated additively by these actual finite representations.
  have hex : ∃ p : ℤ × ℤ, a = p.1 • (1 : RepresentationGrothendieckGroup G) + p.2 • ξ := by
    refine Quotient.inductionOn a ?_
    intro z
    change ∃ p : ℤ × ℤ, QuotientAddGroup.mk' (representationRelations G) z =
      p.1 • (1 : RepresentationGrothendieckGroup G) + p.2 • ξ
    induction z using FreeAbelianGroup.induction_on with
    | zero => exact ⟨(0, 0), by simp⟩
    | of ρ =>
      obtain ⟨m, n, h⟩ := hfinite ρ
      refine ⟨((m : ℤ), (n : ℤ)), ?_⟩
      change finiteRepresentationClass ρ = (m : ℤ) • (1 : RepresentationGrothendieckGroup G) +
        (n : ℤ) • ξ
      simpa only [natCast_zsmul] using h
    | neg z ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨(-p.1, -p.2), ?_⟩
      rw [map_neg, hp]
      simp only [neg_zsmul, neg_add]
    | add z w ihz ihw =>
      obtain ⟨p, hp⟩ := ihz
      obtain ⟨q, hq⟩ := ihw
      refine ⟨(p.1 + q.1, p.2 + q.2), ?_⟩
      rw [map_add, hp, hq]
      simp only [add_zsmul]
      abel
  -- Traces at identity and reflection recover the two integer multiplicities.
  have hξ (g : G) : representationCharacter G ξ g = det g := by
    rw [representationCharacter_finiteClass]
    change LinearMap.trace ℂ (Fin 1 → ℂ) (det g • LinearMap.id) = det g
    rw [map_smul]
    simp
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, hp, ?_⟩
  intro q hq
  have heq : q.1 • (1 : RepresentationGrothendieckGroup G) + q.2 • ξ =
      p.1 • (1 : RepresentationGrothendieckGroup G) + p.2 • ξ := hq.symm.trans hp
  have hdets : det s = -1 := by simp [det, s]
  have hsum : (q.1 : ℂ) + q.2 = (p.1 : ℂ) + p.2 := by
    have h := congrArg (fun b ↦ representationCharacter G b 1) heq
    simp only [map_add, map_zsmul, map_one, Pi.add_apply, Pi.smul_apply,
      Pi.one_apply, hξ] at h
    simpa only [map_one, zsmul_eq_mul, mul_one] using h
  have hdiff : (q.1 : ℂ) - q.2 = (p.1 : ℂ) - p.2 := by
    have h := congrArg (fun b ↦ representationCharacter G b s) heq
    simp only [map_add, map_zsmul, map_one, Pi.add_apply, Pi.smul_apply,
      Pi.one_apply, hξ, hdets] at h
    simpa only [zsmul_eq_mul, mul_one, mul_neg_one, sub_eq_add_neg] using h
  have hsumZ : q.1 + q.2 = p.1 + p.2 := by exact_mod_cast hsum
  have hdiffZ : q.1 - q.2 = p.1 - p.2 := by exact_mod_cast hdiff
  apply Prod.ext <;> omega

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
-- The original coefficient comparison unfolds the direct-sum representation presentation.
/-- The exact annihilator of 1 minus the determinant class consists of multiples of 1 plus it. -/
theorem orthogonalLine_one_sub_det_mul_eq_zero_iff
    (a : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin 1) ℝ)) :
    (1 - ξ) * a = 0 ↔ ∃ c : ℤ, a = c • (1 + ξ) := by
  classical
  let G := Matrix.orthogonalGroup (Fin 1) ℝ
  let s : G := ⟨-1, by
    rw [Matrix.mem_orthogonalGroup_iff]
    simp⟩
  have hξ (g : G) : representationCharacter G ξ g = (g.val.det : ℂ) := by
    rw [representationCharacter_finiteClass]
    change LinearMap.trace ℂ (Fin 1 → ℂ) ((g.val.det : ℂ) • LinearMap.id) = _
    rw [map_smul]
    simp
  have hξ1 : representationCharacter G ξ 1 = 1 := by rw [hξ]; simp
  have hξs : representationCharacter G ξ s = -1 := by rw [hξ]; simp [s]
  -- The actual character of the tensor square has both values one.
  -- The proved decomposition separates these two values in the original quotient.
  have hsq : ξ ^ 2 = 1 := by
    obtain ⟨p, hp, _⟩ := existsUnique_orthogonalLineRepresentation_decomposition (ξ ^ 2)
    have hsum : (p.1 : ℂ) + p.2 = 1 := by
      have h := congrArg (fun b ↦ representationCharacter G b 1) hp.symm
      change representationCharacter G (p.1 • 1 + p.2 • ξ) 1 =
        representationCharacter G (ξ ^ 2) 1 at h
      simp only [map_add, map_zsmul, map_one, map_pow, Pi.add_apply, Pi.smul_apply,
        Pi.one_apply, Pi.pow_apply, hξ1] at h
      simpa only [zsmul_eq_mul, mul_one, one_pow] using h
    have hdiff : (p.1 : ℂ) - p.2 = 1 := by
      have h := congrArg (fun b ↦ representationCharacter G b s) hp.symm
      change representationCharacter G (p.1 • 1 + p.2 • ξ) s =
        representationCharacter G (ξ ^ 2) s at h
      simp only [map_add, map_zsmul, map_one, map_pow, Pi.add_apply, Pi.smul_apply,
        Pi.one_apply, Pi.pow_apply, hξs] at h
      simpa only [zsmul_eq_mul, mul_one, mul_neg_one, neg_one_sq, sub_eq_add_neg] using h
    have hsumZ : p.1 + p.2 = 1 := by exact_mod_cast hsum
    have hdiffZ : p.1 - p.2 = 1 := by exact_mod_cast hdiff
    have hp1 : p.1 = 1 := by omega
    have hp2 : p.2 = 0 := by omega
    simpa only [hp1, hp2, one_zsmul, zero_zsmul, add_zero] using hp
  -- Multiplication by 1 - ξ is the difference of the two multiplicities.
  obtain ⟨p, hp, _⟩ := existsUnique_orthogonalLineRepresentation_decomposition a
  have hprod : (1 - ξ) * a =
      (p.1 - p.2) • (1 : RepresentationGrothendieckGroup G) + (p.2 - p.1) • ξ := by
    change a = p.1 • (1 : RepresentationGrothendieckGroup G) + p.2 • ξ at hp
    rw [hp]
    simp only [zsmul_eq_mul, Int.cast_sub]
    linear_combination -(p.2 : RepresentationGrothendieckGroup G) * hsq
  constructor
  · intro h
    have hzero : (0 : RepresentationGrothendieckGroup G) =
        (p.1 - p.2) • 1 + (p.2 - p.1) • ξ := h.symm.trans hprod
    have hcoeff : (p.1 - p.2, p.2 - p.1) = (0, 0) :=
      (existsUnique_orthogonalLineRepresentation_decomposition
        (0 : RepresentationGrothendieckGroup G)).unique hzero (by simp)
    have hpn : p.1 = p.2 := sub_eq_zero.mp (congrArg Prod.fst hcoeff)
    refine ⟨p.1, ?_⟩
    rw [hp, hpn, smul_add]
  · rintro ⟨c, hc⟩
    change a = c • (1 + ξ) at hc
    rw [hc]
    simp only [zsmul_eq_mul]
    linear_combination -(c : RepresentationGrothendieckGroup G) * hsq

/-- The determinant equation together with the actual dimension-one augmentation forces one. -/
theorem orthogonalLine_eq_one_of_one_sub_det_mul_eq_of_dimension
    (a : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin 1) ℝ))
    (hdet : (1 - ξ) * a = 1 - ξ)
    (hdim : representationDimension (Matrix.orthogonalGroup (Fin 1) ℝ) a = 1) :
    a = 1 := by
  let G := Matrix.orthogonalGroup (Fin 1) ℝ
  -- Subtract the trivial line before applying the exact annihilator formula.
  have hker : (1 - ξ) * (a - 1) = 0 := by
    change (1 - ξ) * a = 1 - ξ at hdet
    rw [mul_sub, mul_one, hdet, sub_self]
  obtain ⟨c, hc⟩ := (orthogonalLine_one_sub_det_mul_eq_zero_iff (a - 1)).mp hker
  change a - 1 = c • (1 + ξ) at hc
  -- The original dimension augmentation kills the residual integer multiplicity.
  have hone : representationDimension G 1 = 1 :=
    (representationDimensionRingHom G).map_one
  have hξ : representationDimension G ξ = 1 := by
    rw [representationDimension_finiteClass]
    rfl
  have hc0 : c = 0 := by
    have h := congrArg (representationDimension G) hc
    change representationDimension G a = 1 at hdim
    simp only [map_sub, map_zsmul, map_add, hdim, hone, hξ] at h
    norm_num at h
    omega
  apply sub_eq_zero.mp
  simpa only [hc0, zero_zsmul] using hc

/-- In the actual SO(2) representation ring, twice a class equals two only for the unit class. -/
theorem specialOrthogonalPlane_eq_one_of_two_mul_eq_two
    (a : RepresentationGrothendieckGroup (Matrix.specialOrthogonalGroup (Fin 2) ℝ))
    (h : 2 * a = 2) : a = 1 := by
  classical
  let O := Matrix.orthogonalGroup (Fin 2) ℝ
  let S := Matrix.specialOrthogonalGroup (Fin 2) ℝ
  let V := Matrix (Fin 2) (Fin 2) ℝ
  -- The native determinant-one subgroup is a closed subset of the native compact orthogonal group.
  let : CompactSpace O := compactSpace_orthogonalGroup 2
  have hO : IsCompact (O : Set V) := isCompact_iff_compactSpace.mpr inferInstance
  have hS : IsCompact (S : Set V) := by
    have hdet : IsClosed {A : V | A.det = 1} :=
      isClosed_eq continuous_id.matrix_det continuous_const
    exact hO.inter_right hdet
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  apply representationCharacter_injective S
  funext g
  have hc := congrArg (fun z : RepresentationGrothendieckGroup S ↦
    representationCharacter S z g) h
  have hvalue : representationCharacter S a g = 1 := by
    simp only [map_mul, map_ofNat, Pi.mul_apply, Pi.ofNat_apply] at hc
    linear_combination (1 / 2 : ℂ) * hc
  simpa using hvalue

end AtiyahSinger
