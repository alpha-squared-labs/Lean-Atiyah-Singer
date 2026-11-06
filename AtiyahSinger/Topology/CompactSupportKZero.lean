/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.KZeroFunctor
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Reduced and compactly supported complex K⁰

Public module ID: M1677.

D07: reduced K⁰ is the kernel of evaluation at the base point. For a locally compact
Hausdorff space, compactly supported K⁰ is reduced K⁰ of the actual one-point
compactification. TripleKZeroComparison proves the SG relative bundle-triple
comparison on compact closed pairs, and CompactSupportProduct constructs the
external product. The automorphism degree-minus-one model is developed separately.

Pullback with compact supports requires a proper map. An arbitrary homotopy on the
noncompact base is not asserted to preserve compact supports uniformly.
Sources: SG I.9, Karoubi II.4.1–4.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Reduced complex K⁰ at a specified base point, using the actual evaluation map. -/
def reducedComplexKZero [CompactSpace X] [T2Space X] (x₀ : X) :
    AddSubgroup (ComplexKZero X) :=
  (kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ x₀).toRingHom).ker

/-- A pointed pullback preserves the kernel of evaluation at the base point. -/
theorem complexKZeroPullback_mem_reduced [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀)
    (a : ComplexKZero Y) (ha : a ∈ reducedComplexKZero y₀) :
    complexKZeroPullback f a ∈ reducedComplexKZero x₀ := by
  /- Evaluation at x₀ after precomposition by f is evaluation at y₀, because f is
  pointed. Functoriality of the explicit ring-induced K₀ maps carries this equality
  to K₀. Consequently a class evaluating to zero still evaluates to zero after pullback. -/
  -- The actual evaluation homomorphisms commute with this pointed precomposition.
  have heval : (ContinuousMap.evalAlgHom ℂ ℂ x₀).toRingHom.comp
      (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom =
        (ContinuousMap.evalAlgHom ℂ ℂ y₀).toRingHom := by
    ext b
    change b (f x₀) = b y₀
    rw [hf]
  change kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ x₀).toRingHom
    (kZeroMap (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom a) = 0
  rw [← AddMonoidHom.comp_apply, ← kZeroMap_comp, heval]
  exact ha

/-- Pullback between reduced groups, restricted from the previously defined absolute pullback. -/
def reducedComplexKZeroPullback [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀) :
    reducedComplexKZero y₀ →+ reducedComplexKZero x₀ where
  toFun a := ⟨complexKZeroPullback f a.val,
    complexKZeroPullback_mem_reduced x₀ y₀ f hf a.val a.property⟩
  map_zero' := Subtype.ext (map_zero (complexKZeroPullback f))
  map_add' a b := Subtype.ext (map_add (complexKZeroPullback f) a.val b.val)

/-- Compactly supported K⁰ of a locally compact Hausdorff space. -/
abbrev CompactSupportKZero (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] : Type _ :=
  reducedComplexKZero (∞ : OnePoint X)

/-- Properness ensures continuity of the map extending f by infinity. -/
theorem continuous_onePointMap_of_proper [LocallyCompactSpace X] [T2Space X]
    [LocallyCompactSpace Y] [T2Space Y] (f : C(X, Y)) (hf : IsProperMap f) :
    Continuous (OnePoint.map f) := by
  /- At finite points use continuity of f and the open embeddings into the one-point
  compactifications. A neighborhood of infinity is the complement of a compact set.
  Its inverse image is again such a neighborhood because properness makes the compact
  preimage compact. This verifies continuity at infinity, including compact bases. -/
  apply OnePoint.continuous_map f.continuous
  -- Properness pulls each closed compact complement back to a closed compact set.
  apply Filter.hasBasis_coclosedCompact.tendsto_right_iff.mpr
  intro K hK
  change (f ⁻¹' K)ᶜ ∈ Filter.coclosedCompact X
  exact (hf.isCompact_preimage hK.2).compl_mem_coclosedCompact_of_isClosed
      (hK.1.preimage f.continuous)

/-- The actual extension of a proper map to the one-point compactifications. -/
def properOnePointMap [LocallyCompactSpace X] [T2Space X]
    [LocallyCompactSpace Y] [T2Space Y] (f : C(X, Y)) (hf : IsProperMap f) :
    C(OnePoint X, OnePoint Y) :=
  ⟨OnePoint.map f, continuous_onePointMap_of_proper f hf⟩

/-- Proper pullback in compactly supported K⁰. -/
def compactSupportKZeroPullback [LocallyCompactSpace X] [T2Space X]
    [LocallyCompactSpace Y] [T2Space Y] (f : C(X, Y)) (hf : IsProperMap f) :
    CompactSupportKZero Y →+ CompactSupportKZero X :=
  reducedComplexKZeroPullback ∞ ∞ (properOnePointMap f hf) rfl

open scoped Classical in
/-- Collapse the complement of U, including the point at infinity, to infinity in U⁺. -/
def onePointCollapse (U : Set X) : OnePoint X → OnePoint U :=
  fun z ↦ z.elim ∞ (fun x ↦ if hx : x ∈ U then ((⟨x, hx⟩ : U) : OnePoint U) else ∞)

/-- For open U the collapse map between the actual one-point compactifications is continuous. -/
theorem continuous_onePointCollapse [LocallyCompactSpace X] [T2Space X]
    (U : Set X) (hU : IsOpen U) : Continuous (onePointCollapse U) := by
  /- On U the map is the identity in the open-subspace coordinates. For a compact
  subset K of U, its image in X is compact and hence closed. The inverse image of
  U⁺ minus K is exactly X⁺ minus that image. This verifies continuity at every point
  sent to infinity, both at the boundary of U and at the original infinity. -/
  classical
  apply continuous_def.mpr
  intro s hs
  by_cases hinfty : (∞ : OnePoint U) ∈ s
  · -- At infinity, the omitted compact subset of U remains compact in X.
    have hK := (OnePoint.isOpen_iff_of_mem hinfty).mp hs
    have hcompact : IsCompact (Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' s)ᶜ) :=
      hK.2.image continuous_subtype_val
    have hpre : ((↑) : X → OnePoint X) ⁻¹' (onePointCollapse U ⁻¹' s) =
        (Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' s)ᶜ)ᶜ := by
      ext x
      by_cases hx : x ∈ U <;> simp [onePointCollapse, hx, hinfty]
    apply (OnePoint.isOpen_iff_of_mem (s := onePointCollapse U ⁻¹' s) hinfty).mpr
    rw [hpre, compl_compl]
    exact ⟨hcompact.isClosed, hcompact⟩
  · -- Away from infinity, open-subspace coordinates give the inverse image directly.
    have hopen := (OnePoint.isOpen_iff_of_notMem hinfty).mp hs
    have hpre : ((↑) : X → OnePoint X) ⁻¹' (onePointCollapse U ⁻¹' s) =
        Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' s) := by
      ext x
      by_cases hx : x ∈ U <;> simp [onePointCollapse, hx, hinfty]
    apply (OnePoint.isOpen_iff_of_notMem
      (s := onePointCollapse U ⁻¹' s) hinfty).mpr
    rw [hpre]
    exact hU.isOpenMap_subtype_val _ hopen

/-- K02: extension by an open inclusion, induced contravariantly by the collapse map. -/
def compactSupportKZeroOpenExtension [LocallyCompactSpace X] [T2Space X]
    (U : Set X) (hU : IsOpen U) :
    letI := hU.locallyCompactSpace
    CompactSupportKZero U →+ CompactSupportKZero X :=
  letI := hU.locallyCompactSpace
  reducedComplexKZeroPullback ∞ ∞
    ⟨onePointCollapse U, continuous_onePointCollapse U hU⟩ rfl

/-- On a compact base, restriction from X⁺ gives the comparison with absolute K⁰. -/
def compactSupportKZeroToAbsolute [CompactSpace X] [T2Space X] :
    CompactSupportKZero X →+ ComplexKZero X :=
  (complexKZeroPullback ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩).comp
    (reducedComplexKZero (∞ : OnePoint X)).subtype

set_option backward.isDefEq.respectTransparency.types false in
/-- Compactly supported and absolute K⁰ agree on compact Hausdorff spaces. -/
theorem compactSupportKZeroToAbsolute_bijective [CompactSpace X] [T2Space X] :
    Function.Bijective (compactSupportKZeroToAbsolute (X := X)) := by
  /- For compact X, infinity is isolated in X-plus. Zero extension from each
  clopen component preserves matrix equivalence and block sum, giving maps
  on K-zero by its universal property. Every idempotent splits into its two
  component matrices; rectangular matrix equivalence identifies their sum
  with their block sum. The resulting K-zero decomposition makes finite
  restriction and zero extension inverse on the infinity evaluation kernel. -/
  classical
  -- Compactness isolates infinity, so both disjoint component extensions are continuous.
  let ext0 : C(X, ℂ) →ₙ+* C(OnePoint X, ℂ) := {
    toFun := fun f ↦ OnePoint.continuousMapMk f 0 (by
      simp [Filter.coclosedCompact_eq_cocompact, Filter.cocompact_eq_bot])
    map_zero' := by ext z; cases z using OnePoint.rec <;> simp [OnePoint.continuousMapMk]
    map_add' := fun f g ↦ by ext z; cases z using OnePoint.rec <;> simp [OnePoint.continuousMapMk]
    map_mul' := fun f g ↦ by ext z; cases z using OnePoint.rec <;> simp [OnePoint.continuousMapMk] }
  let extInf : ℂ →ₙ+* C(OnePoint X, ℂ) := {
    toFun := fun c ↦ OnePoint.continuousMapMk (ContinuousMap.const X 0) c (by
      simp [Filter.coclosedCompact_eq_cocompact, Filter.cocompact_eq_bot])
    map_zero' := by ext z; cases z using OnePoint.rec <;> simp [OnePoint.continuousMapMk]
    map_add' := fun a b ↦ by ext z; cases z using OnePoint.rec <;> simp [OnePoint.continuousMapMk]
    map_mul' := fun a b ↦ by ext z; cases z using OnePoint.rec <;> simp [OnePoint.continuousMapMk] }
  let res : C(OnePoint X, ℂ) →+* C(X, ℂ) :=
    (ContinuousMap.compRightAlgHom ℂ ℂ
      ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩).toRingHom
  let ev : C(OnePoint X, ℂ) →+* ℂ :=
    (ContinuousMap.evalAlgHom ℂ ℂ (∞ : OnePoint X)).toRingHom
  -- The 0 component preserves matrix products and both defining K-zero relations.
  let m0 (p : IdempotentMatrix C(X, ℂ)) : IdempotentMatrix C(OnePoint X, ℂ) := {
    size := p.size
    matrix := p.matrix.map ext0
    mul_self := by rw [← Matrix.map_mul, p.mul_self] }
  have hiso0 (p q : IdempotentMatrix C(X, ℂ)) (h : p.IsEquivalent q) :
      kZeroClass C(OnePoint X, ℂ) (m0 p) =
        kZeroClass C(OnePoint X, ℂ) (m0 q) := by
    apply kZeroClass_eq_of_isEquivalent
    obtain ⟨a, b, hab, hba, hpa, hqb⟩ := h
    refine ⟨a.map ext0, b.map ext0, ?_, ?_, ?_, ?_⟩
    · change a.map ext0 * b.map ext0 = p.matrix.map ext0
      rw [← Matrix.map_mul, hab]
    · change b.map ext0 * a.map ext0 = q.matrix.map ext0
      rw [← Matrix.map_mul, hba]
    · change p.matrix.map ext0 * a.map ext0 = a.map ext0
      rw [← Matrix.map_mul, hpa]
    · change q.matrix.map ext0 * b.map ext0 = b.map ext0
      rw [← Matrix.map_mul, hqb]
  have hsum0 (p q : IdempotentMatrix C(X, ℂ)) :
      kZeroClass C(OnePoint X, ℂ) (m0 (p.blockSum q)) =
        kZeroClass C(OnePoint X, ℂ) (m0 p) +
          kZeroClass C(OnePoint X, ℂ) (m0 q) := by
    have hblock : m0 (p.blockSum q) = (m0 p).blockSum (m0 q) := by
      dsimp only [m0, IdempotentMatrix.blockSum]
      congr 1
      ext i j
      simp only [IdempotentMatrix.blockMatrix, Matrix.reindex_apply,
        Matrix.map_apply, Matrix.submatrix_apply]
      cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp
    rw [hblock, kZeroClass_blockSum]
  obtain ⟨s0, hs0, _⟩ := kZero_universal_property
    (fun p ↦ kZeroClass C(OnePoint X, ℂ) (m0 p)) hiso0 hsum0
  -- The Inf component preserves matrix products and both defining K-zero relations.
  let mInf (p : IdempotentMatrix ℂ) : IdempotentMatrix C(OnePoint X, ℂ) := {
    size := p.size
    matrix := p.matrix.map extInf
    mul_self := by rw [← Matrix.map_mul, p.mul_self] }
  have hisoInf (p q : IdempotentMatrix ℂ) (h : p.IsEquivalent q) :
      kZeroClass C(OnePoint X, ℂ) (mInf p) =
        kZeroClass C(OnePoint X, ℂ) (mInf q) := by
    apply kZeroClass_eq_of_isEquivalent
    obtain ⟨a, b, hab, hba, hpa, hqb⟩ := h
    refine ⟨a.map extInf, b.map extInf, ?_, ?_, ?_, ?_⟩
    · change a.map extInf * b.map extInf = p.matrix.map extInf
      rw [← Matrix.map_mul, hab]
    · change b.map extInf * a.map extInf = q.matrix.map extInf
      rw [← Matrix.map_mul, hba]
    · change p.matrix.map extInf * a.map extInf = a.map extInf
      rw [← Matrix.map_mul, hpa]
    · change q.matrix.map extInf * b.map extInf = b.map extInf
      rw [← Matrix.map_mul, hqb]
  have hsumInf (p q : IdempotentMatrix ℂ) :
      kZeroClass C(OnePoint X, ℂ) (mInf (p.blockSum q)) =
        kZeroClass C(OnePoint X, ℂ) (mInf p) +
          kZeroClass C(OnePoint X, ℂ) (mInf q) := by
    have hblock : mInf (p.blockSum q) = (mInf p).blockSum (mInf q) := by
      dsimp only [mInf, IdempotentMatrix.blockSum]
      congr 1
      ext i j
      simp only [IdempotentMatrix.blockMatrix, Matrix.reindex_apply,
        Matrix.map_apply, Matrix.submatrix_apply]
      cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp
    rw [hblock, kZeroClass_blockSum]
  obtain ⟨sInf, hsInf, _⟩ := kZero_universal_property
    (fun p ↦ kZeroClass C(OnePoint X, ℂ) (mInf p)) hisoInf hsumInf
  -- A matrix over the disjoint compact components is the sum of orthogonal idempotents.
  have hsplit (p : IdempotentMatrix C(OnePoint X, ℂ)) :
      kZeroClass C(OnePoint X, ℂ) p =
        kZeroClass C(OnePoint X, ℂ) (m0 (p.map res)) +
          kZeroClass C(OnePoint X, ℂ) (mInf (p.map ev)) := by
    let p0 : IdempotentMatrix C(OnePoint X, ℂ) := {
      size := p.size
      matrix := (p.matrix.map res).map ext0
      mul_self := by rw [← Matrix.map_mul, ← Matrix.map_mul, p.mul_self] }
    let pInf : IdempotentMatrix C(OnePoint X, ℂ) := {
      size := p.size
      matrix := (p.matrix.map ev).map extInf
      mul_self := by rw [← Matrix.map_mul, ← Matrix.map_mul, p.mul_self] }
    have h0infty (f : C(X, ℂ)) : ext0 f ∞ = 0 := rfl
    have h0coe (f : C(X, ℂ)) (x : X) : ext0 f x = f x := rfl
    have hInfInfty (c : ℂ) : extInf c ∞ = c := rfl
    have hInfCoe (c : ℂ) (x : X) : extInf c x = 0 := rfl
    have htotal : p0.matrix + pInf.matrix = p.matrix := by
      ext i j z
      change ext0 (res (p.matrix i j)) z + extInf (ev (p.matrix i j)) z = p.matrix i j z
      cases z using OnePoint.rec <;>
        simp only [h0infty, h0coe, hInfInfty, hInfCoe, zero_add, add_zero] <;> rfl
    have hcross : p0.matrix * pInf.matrix = 0 := by
      ext i j z
      change (∑ k, ext0 (res (p.matrix i k)) * extInf (ev (p.matrix k j))) z = 0
      cases z using OnePoint.rec <;>
        simp [ContinuousMap.sum_apply, h0infty, h0coe, hInfInfty, hInfCoe]
    have hcross' : pInf.matrix * p0.matrix = 0 := by
      ext i j z
      change (∑ k, extInf (ev (p.matrix i k)) * ext0 (res (p.matrix k j))) z = 0
      cases z using OnePoint.rec <;>
        simp [ContinuousMap.sum_apply, h0infty, h0coe, hInfInfty, hInfCoe]
    have hequiv : p.IsEquivalent (p0.blockSum pInf) := by
      let a : Matrix (Fin p.size) (Fin (p.size + p.size)) C(OnePoint X, ℂ) :=
        (Matrix.fromCols p0.matrix pInf.matrix).submatrix id finSumFinEquiv.symm
      let b : Matrix (Fin (p.size + p.size)) (Fin p.size) C(OnePoint X, ℂ) :=
        (Matrix.fromRows p0.matrix pInf.matrix).submatrix finSumFinEquiv.symm id
      have hab : a * b = p.matrix := by
        dsimp only [a, b]
        rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows,
          p0.mul_self, pInf.mul_self, htotal]
        rfl
      have hba : b * a = (p0.blockSum pInf).matrix := by
        change (Matrix.fromRows p0.matrix pInf.matrix).submatrix finSumFinEquiv.symm id *
          (Matrix.fromCols p0.matrix pInf.matrix).submatrix id finSumFinEquiv.symm = _
        rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
          Matrix.fromRows_mul_fromCols, p0.mul_self, pInf.mul_self, hcross, hcross']
        rfl
      refine ⟨a, b, hab, hba, ?_, ?_⟩
      · change p.matrix * a = a
        rw [← hab, Matrix.mul_assoc, hba]
        dsimp only [a, IdempotentMatrix.blockSum, IdempotentMatrix.blockMatrix]
        rw [Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
          Matrix.fromCols_mul_fromBlocks, p0.mul_self, pInf.mul_self]
        simp
      · change (Matrix.fromBlocks p0.matrix 0 0 pInf.matrix).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm *
            (Matrix.fromRows p0.matrix pInf.matrix).submatrix finSumFinEquiv.symm id =
              (Matrix.fromRows p0.matrix pInf.matrix).submatrix finSumFinEquiv.symm id
        rw [Matrix.submatrix_mul_equiv,
          Matrix.fromBlocks_mul_fromRows, p0.mul_self, pInf.mul_self]
        simp
    exact (kZeroClass_eq_of_isEquivalent _ _ hequiv).trans (kZeroClass_blockSum p0 pInf)
  -- Every zero idempotent has zero class, including nonzero ambient sizes.
  have hzero (p : IdempotentMatrix ℂ) (hp : p.matrix = 0) : kZeroClass ℂ p = 0 := by
    have he : p.IsEquivalent (p.blockSum p) := by
      refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
      · simp [hp]
      · simp only [IdempotentMatrix.blockSum, IdempotentMatrix.blockMatrix, hp,
          Matrix.reindex_apply, Matrix.fromBlocks_zero]
        exact Matrix.zero_mul _
      · simp
      · simp
    have h := kZeroClass_eq_of_isEquivalent _ _ he
    rw [kZeroClass_blockSum] at h
    apply add_left_cancel (a := kZeroClass ℂ p)
    simpa only [add_zero] using h.symm
  have hres : (kZeroMap res).comp s0 = AddMonoidHom.id _ := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro p
    change kZeroMap res (s0 (kZeroClass C(X, ℂ) p)) = kZeroClass C(X, ℂ) p
    rw [hs0, kZeroMap_class]
    have hm : (m0 p).map res = p := by
      cases p with
      | mk n M hM =>
        dsimp only [m0, IdempotentMatrix.map]
        congr 1
    rw [hm]
  have hev : (kZeroMap ev).comp s0 = 0 := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro p
    change kZeroMap ev (s0 (kZeroClass C(X, ℂ) p)) = 0
    rw [hs0, kZeroMap_class]
    apply hzero
    ext i j
    rfl
  have hdecomp : s0.comp (kZeroMap res) + sInf.comp (kZeroMap ev) =
      AddMonoidHom.id (ComplexKZero (OnePoint X)) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro p
    change s0 (kZeroMap res (kZeroClass C(OnePoint X, ℂ) p)) +
      sInf (kZeroMap ev (kZeroClass C(OnePoint X, ℂ) p)) = kZeroClass C(OnePoint X, ℂ) p
    rw [kZeroMap_class, kZeroMap_class, hs0, hsInf]
    exact (hsplit p).symm
  -- Restriction and zero extension are inverse on precisely the evaluation kernel.
  constructor
  · intro a b hab
    apply Subtype.ext
    have ha : kZeroMap ev a.val = 0 := a.property
    have hb : kZeroMap ev b.val = 0 := b.property
    have hea := DFunLike.congr_fun hdecomp a.val
    have heb := DFunLike.congr_fun hdecomp b.val
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
      ha, hb, map_zero, add_zero] at hea heb
    change kZeroMap res a.val = kZeroMap res b.val at hab
    exact hea.symm.trans ((congrArg s0 hab).trans heb)
  · intro a
    refine ⟨⟨s0 a, ?_⟩, ?_⟩
    · exact DFunLike.congr_fun hev a
    · exact DFunLike.congr_fun hres a

end AtiyahSinger
