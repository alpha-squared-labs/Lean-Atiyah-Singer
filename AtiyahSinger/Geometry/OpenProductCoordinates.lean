/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OpenManifoldDerivative
public import AtiyahSinger.Geometry.ProductCovectorCoordinates

/-!
# Product open sets in the original concatenated atlas

Public module ID: M1322.

The product of two inherited open submanifolds is identified with its actual
open image in the product manifold. Both sides retain the same concatenated
Euclidean model. This comparison supplies the native clopen product inclusion
used in the original external-product index assembly.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original product of open submanifolds has its native open product image. -/
def openProductDiffeomorph (U : Opens M) (V : Opens N) :
    let W : Opens (M × N) := ⟨(U : Set M) ×ˢ (V : Set N), U.isOpen.prod V.isOpen⟩
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := euclideanProductChartedSpace (n := n) (m := m) U V
    (U × V) ≃ₘ⟮𝓡 (n + m), 𝓡 (n + m)⟯ W := by
  let W : Opens (M × N) := ⟨(U : Set M) ×ˢ (V : Set N), U.isOpen.prod V.isOpen⟩
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let I := 𝓘(ℝ, X × Y)
  let J := 𝓡 (n + m)
  let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let : ChartedSpace (X × Y) (M × N) := prodChartedSpace X M Y N
  let : ChartedSpace (X × Y) (U × V) := prodChartedSpace X U Y V
  let : IsManifold I ∞ (M × N) := by
    rw [show I = (𝓡 n).prod (𝓡 m) from modelWithCornersSelf_prod]
    exact IsManifold.prod M N
  let : IsManifold I ∞ (U × V) := by
    rw [show I = (𝓡 n).prod (𝓡 m) from modelWithCornersSelf_prod]
    exact IsManifold.prod U V
  let a (z : U × V) : M × N := (z.1.val, z.2.val)
  have ha : ContMDiff I I ∞ a := by
    rw [show I = (𝓡 n).prod (𝓡 m) from modelWithCornersSelf_prod]
    exact (contMDiff_subtype_val.comp contMDiff_fst).prodMk
      (contMDiff_subtype_val.comp contMDiff_snd)
  let d := linearModelDiffeomorph c.symm (M × N)
  let e := linearModelDiffeomorph c.symm (U × V)
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := euclideanProductChartedSpace (n := n) (m := m) U V
  -- The same linear model change is used on both sides of the actual inclusion.
  have ha' : ContMDiff J J ∞ a := d.contMDiff.comp (ha.comp e.symm.contMDiff)
  have hv : ContMDiff J I ∞ (fun z : W ↦ (z.val : M × N)) :=
    d.symm.contMDiff.comp contMDiff_subtype_val
  have hb₀ : ContMDiff J (𝓡 n) ∞ (fun z : W ↦ (⟨z.val.1, z.property.1⟩ : U)) := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    rw [show I = (𝓡 n).prod (𝓡 m) from modelWithCornersSelf_prod] at hv
    exact contMDiff_fst.comp hv
  have hb₁ : ContMDiff J (𝓡 m) ∞ (fun z : W ↦ (⟨z.val.2, z.property.2⟩ : V)) := by
    apply (ContMDiff.subtypeVal_comp_iff V _).mp
    rw [show I = (𝓡 n).prod (𝓡 m) from modelWithCornersSelf_prod] at hv
    exact contMDiff_snd.comp hv
  have hb : ContMDiff J I ∞ (fun z : W ↦
      ((⟨z.val.1, z.property.1⟩ : U), (⟨z.val.2, z.property.2⟩ : V))) := by
    rw [show I = (𝓡 n).prod (𝓡 m) from modelWithCornersSelf_prod]
    exact hb₀.prodMk hb₁
  exact {
    toFun z := ⟨a z, z.1.property, z.2.property⟩
    invFun z := (⟨z.val.1, z.property.1⟩, ⟨z.val.2, z.property.2⟩)
    left_inv _ := rfl
    right_inv _ := rfl
    contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (W) _).mp ha'
    contMDiff_invFun := e.contMDiff.comp hb }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
-- Conjugate the actual inclusion derivative by the same linear model change on both sides.
/-- The actual cotangent lift of the open product inclusion splits into the two original lifts. -/
theorem cotangent_openProductDiffeomorph_split (U : Opens M) (V : Opens N) :
    let W : Opens (M × N) := ⟨(U : Set M) ×ˢ (V : Set N), U.isOpen.prod V.isOpen⟩
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := euclideanProductChartedSpace (n := n) (m := m) U V
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) U V
    ∀ z : CotangentTotalSpace (n := n + m) (M := U × V),
      cotangentProductHomeomorph M N
          (cotangentOpenInclusion W
            (cotangentDiffeomorph (openProductDiffeomorph (n := n) (m := m) U V) z)) =
        Prod.map (cotangentOpenInclusion U) (cotangentOpenInclusion V)
          (cotangentProductHomeomorph U V z) := by
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let I := 𝓘(ℝ, X × Y)
  let J := 𝓡 (n + m)
  let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let W : Opens (M × N) := ⟨(U : Set M) ×ˢ (V : Set N), U.isOpen.prod V.isOpen⟩
  let : ChartedSpace (X × Y) (M × N) := prodChartedSpace X M Y N
  let : ChartedSpace (X × Y) (U × V) := prodChartedSpace X U Y V
  let : IsManifold I ∞ (M × N) := by
    rw [show I = (𝓡 n).prod (𝓡 m) from modelWithCornersSelf_prod]
    exact IsManifold.prod M N
  let : IsManifold I ∞ (U × V) := by
    rw [show I = (𝓡 n).prod (𝓡 m) from modelWithCornersSelf_prod]
    exact IsManifold.prod U V
  let a (z : U × V) : M × N := (z.1.val, z.2.val)
  have ha : ContMDiff I I ∞ a := by
    rw [show I = (𝓡 n).prod (𝓡 m) from modelWithCornersSelf_prod]
    exact (contMDiff_subtype_val.comp contMDiff_fst).prodMk
      (contMDiff_subtype_val.comp contMDiff_snd)
  have hDa (z : U × V) : mfderiv I I a z = ContinuousLinearMap.id ℝ (X × Y) := by
    have h₀ : MDifferentiableAt (𝓡 n) (𝓡 n) (Subtype.val : U → M) z.1 :=
      (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
    have h₁ : MDifferentiableAt (𝓡 m) (𝓡 m) (Subtype.val : V → N) z.2 :=
      (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
    have h := mfderiv_prodMap h₀ h₁
    rw [mfderiv_openSubtype_val, mfderiv_openSubtype_val] at h
    change mfderiv ((𝓡 n).prod (𝓡 m)) ((𝓡 n).prod (𝓡 m)) a z = _ at h
    rw [← modelWithCornersSelf_prod] at h
    exact h.trans (by ext v <;> rfl)
  have hM := contMDiff_mfderiv_linearModelId c.symm (M × N)
  have hU := contMDiff_mfderiv_linearModelId c.symm (U × V)
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := euclideanProductChartedSpace (n := n) (m := m) U V
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) U V
  let f := openProductDiffeomorph (n := n) (m := m) U V
  have ha' : ContMDiff I J ∞ a := hM.1.1.comp ha
  have hDa' (z : U × V) : mfderiv I J a z = c.symm.toContinuousLinearMap := by
    have h := mfderiv_comp (f := a) (g := id) z
      (hM.1.1.mdifferentiableAt (by simp)) (ha.mdifferentiableAt (by simp))
    change mfderiv I J a z = _ at h
    rw [hM.2.1, hDa] at h
    exact h.trans (by ext v; rfl)
  have hDaNative (z : U × V) :
      mfderiv J J a z = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + m))) := by
    have h := mfderiv_comp (f := id) (g := a) z
      (ha'.mdifferentiableAt (by simp)) (hU.1.2.mdifferentiableAt (by simp))
    change mfderiv J J a z = _ at h
    rw [hDa', hU.2.2] at h
    exact h.trans (by ext v; exact c.symm_apply_apply v)
  have hf (z : U × V) :
      mfderiv J J f z = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + m))) := by
    have h := mfderiv_comp z ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
      (f.contMDiff.mdifferentiableAt (by simp))
    change mfderiv J J a z = _ at h
    rw [hDaNative, mfderiv_openSubtype_val] at h
    ext v
    exact (DFunLike.congr_fun h v).symm
  -- The inverse derivative is the identity in the same coordinates, so the covector is unchanged.
  have hinv (z : U × V) :
      mfderiv J J f.symm (f z) = ContinuousLinearMap.id ℝ
        (EuclideanSpace ℝ (Fin (n + m))) := by
    have h := mfderiv_comp (f := f.symm) (g := f) (f z)
      (f.contMDiff.mdifferentiableAt (by simp)) (f.symm.contMDiff.mdifferentiableAt (by simp))
    have heq : (f ∘ f.symm) = id := funext fun x ↦ f.apply_symm_apply x
    rw [heq, mfderiv_id, hf] at h
    ext v
    exact (DFunLike.congr_fun h v).symm
  dsimp only
  intro z
  have hlift : cotangentOpenInclusion W (cotangentDiffeomorph f z) =
      (⟨(z.proj.1.val, z.proj.2.val), z.snd⟩ :
        CotangentTotalSpace (n := n + m) (M := M × N)) := by
    change (⟨(z.proj.1.val, z.proj.2.val), z.snd.comp (mfderiv J J f.symm (f z.proj))⟩ :
      CotangentTotalSpace (n := n + m) (M := M × N)) = _
    rw [hinv]
    rfl
  rw [hlift, cotangentProductHomeomorph_apply, cotangentProductHomeomorph_apply]
  rfl

end AtiyahSinger
