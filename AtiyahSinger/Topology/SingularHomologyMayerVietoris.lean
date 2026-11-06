/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularMayerVietoris
public import AtiyahSinger.Topology.SingularCechCochains

/-!
# The original singular homology Mayer–Vietoris sequence

Public module ID: M2148.

The overlap maps by the difference of its actual two inclusions. The next
map is the original sum, corestricted to its categorical image in ambient
singular chains. For an open cover this image computes ambient homology by
the small-chain theorem. The resulting connecting map retains these signs
for comparison with compact-support cap duality.

Source: Hatcher, Algebraic Topology, section 2.1, Mayer–Vietoris and small chains.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual overlap difference and sum of subspace chains, with the sum's original image. -/
def singularMayerVietorisShortComplex (A B : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) := by
  let a : C(↥(A ∩ B), A) := ⟨fun x ↦ ⟨x.val, x.property.1⟩,
    continuous_subtype_val.subtype_mk _⟩
  let b : C(↥(A ∩ B), B) := ⟨fun x ↦ ⟨x.val, x.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩
  let i := (singularChainsFunctor R).map (TopCat.ofHom a)
  let j := (singularChainsFunctor R).map (TopCat.ofHom b)
  let sum := singularSubspaceSumChains R A B
  refine ShortComplex.mk (biprod.lift i (-j)) (Abelian.factorThruImage sum) ?_
  apply (cancel_mono (Abelian.image.ι sum)).mp
  rw [Category.assoc, Abelian.image.fac, zero_comp]
  change biprod.lift i (-j) ≫ biprod.desc (singularSubspaceChains R A)
    (singularSubspaceChains R B) = 0
  rw [biprod.lift_desc, Preadditive.neg_comp, add_neg_eq_zero]
  simp only [i, j, singularSubspaceChains, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original overlap difference and sum-image sequence is short exact for any two subspaces. -/
theorem shortExact_singularMayerVietorisShortComplex (A B : Set X) :
    (singularMayerVietorisShortComplex R A B).ShortExact := by
  let S := singularMayerVietorisShortComplex R A B
  let a : C(↥(A ∩ B), A) := ⟨fun x ↦ ⟨x.val, x.property.1⟩,
    continuous_subtype_val.subtype_mk _⟩
  let b : C(↥(A ∩ B), B) := ⟨fun x ↦ ⟨x.val, x.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩
  let F := (singularChainsFunctor R).map (TopCat.ofHom a)
  let G := (singularChainsFunctor R).map (TopCat.ofHom b)
  let sum := singularSubspaceSumChains R A B
  have hF : F ≫ singularSubspaceChains R A = singularSubspaceChains R (A ∩ B) := by
    simp only [F, singularSubspaceChains, ← Functor.map_comp]
    rfl
  have hG : G ≫ singularSubspaceChains R B = singularSubspaceChains R (A ∩ B) := by
    simp only [G, singularSubspaceChains, ← Functor.map_comp]
    rfl
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let ev := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let D := S.map ev
  let fst := (biprod.fst : singularChains R A ⊞ singularChains R B ⟶ singularChains R A).f n
  let snd := (biprod.snd : singularChains R A ⊞ singularChains R B ⟶ singularChains R B).f n
  have hmono (U : Set X) : Function.Injective ((singularSubspaceChains R U).f n) := by
    let : IsSplitMono ((singularSubspaceChains R U).f n) :=
      isSplitMono_singularChainsMap_of_injective R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) Subtype.val_injective n
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  have hfst (z : (singularChains R ↥(A ∩ B)).X n) : fst (D.f z) = F.f n z :=
    congrArg (fun f ↦ f.f n z) (biprod.lift_fst F (-G))
  have hsnd (z : (singularChains R ↥(A ∩ B)).X n) : snd (D.f z) = -(G.f n z) :=
    congrArg (fun f ↦ f.f n z) (biprod.lift_snd F (-G))
  have hDF : Mono D.f := by
    apply (ModuleCat.mono_iff_injective _).mpr
    intro z w h
    apply hmono (A ∩ B)
    have h' := congrArg fst h
    rw [hfst, hfst] at h'
    have hFn := congrArg (fun f ↦ f.f n) hF
    change F.f n ≫ (singularSubspaceChains R A).f n = _ at hFn
    rw [← hFn]
    exact congrArg ((singularSubspaceChains R A).f n) h'
  have hDG : Epi D.g := by
    change Epi ((Abelian.factorThruImage sum).f n)
    infer_instance
  refine { mono_f := hDF, epi_g := hDG, exact := ?_ }
  apply (ShortComplex.moduleCat_exact_iff D).mpr
  intro z hz
  have hsum : (singularSubspaceChains R A).f n (fst z) +
      (singularSubspaceChains R B).f n (snd z) = 0 := by
    have hfac := congrArg (fun f ↦ f.f n z) (Abelian.image.fac sum)
    change (Abelian.image.ι sum).f n (D.g z) = sum.f n z at hfac
    rw [hz, map_zero] at hfac
    have hdesc := congrArg (fun f ↦ f.f n z)
      (biprod.desc_eq (f := singularSubspaceChains R A) (g := singularSubspaceChains R B))
    exact hdesc.symm.trans hfac.symm
  -- Equal ambient chains in the two subspaces are precisely chains in their actual intersection.
  have hmem : (singularSubspaceChains R A).f n (fst z) ∈
      ((singularSubspaceChains R (A ∩ B)).f n).hom.range := by
    rw [range_singularSubspaceChains_inter]
    refine ⟨⟨fst z, rfl⟩, -snd z, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left hsum).symm
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  have hFc : F.f n c = fst z := by
    apply hmono A
    exact (congrArg (fun f ↦ f.f n c) hF).trans hc
  have hGc : G.f n c = -snd z := by
    apply hmono B
    rw [map_neg]
    exact (congrArg (fun f ↦ f.f n c) hG).trans
      (hc.trans (eq_neg_of_add_eq_zero_left hsum))
  -- The two biproduct projections determine the same original middle-chain element.
  have hext {v w : D.X₂} (hv : fst v = fst w) (hw : snd v = snd w) : v = w := by
    have hsplit (t : D.X₂) :
        (biprod.inl : singularChains R A ⟶ singularChains R A ⊞ singularChains R B).f n
          (fst t) +
        (biprod.inr : singularChains R B ⟶ singularChains R A ⊞ singularChains R B).f n
          (snd t) = t :=
      congrArg (fun f ↦ f.f n t) (biprod.total (X := singularChains R A) (Y := singularChains R B))
    rw [← hsplit v, hv, hw, hsplit w]
  apply hext
  · rw [hfst, hFc]
  · rw [hsnd, hGc, neg_neg]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- For an open two-set cover, inclusion of the original sum-image chains
induces homology isomorphisms. -/
theorem isIso_homologyMap_singularMayerVietorisImageInclusion
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (n : ℕ) : IsIso (homologyMap (Abelian.image.ι (singularSubspaceSumChains R A B)) n) := by
  let sum := singularSubspaceSumChains R A B
  let small := smallSingularChainsInclusion R ({A, B} : Set (Set X))
  let Q := cokernel sum
  -- The small-chain quotient and the sum-image quotient have the same degreewise kernels.
  let e : cokernel small ≅ Q := cokernelIsoOfDegreewiseRangeEq small sum
    (fun k ↦ range_smallSingularChainsInclusion_pair R A B k)
  have hopen : ∀ U ∈ ({A, B} : Set (Set X)), IsOpen U := by
    intro U hU
    rcases Set.mem_insert_iff.mp hU with rfl | hU
    · exact hA
    · exact Set.mem_singleton_iff.mp hU ▸ hB
  have hcov : ⋃₀ ({A, B} : Set (Set X)) = Set.univ := by
    rw [Set.sUnion_pair, hcover]
  obtain ⟨hcontract⟩ := contractible_cokernel_smallSingularChains R {A, B} hopen hcov
  have hzero (k : ℕ) : IsZero (Q.homology k) := by
    have hz : IsZero ((cokernel small).homology k) := by
      rw [IsZero.iff_id_eq_zero]
      simpa using hcontract.homologyMap_eq k
    exact IsZero.of_iso hz
      ((homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) k).mapIso e).symm
  -- Its quotient sequence therefore identifies the image with ambient chains on homology.
  let P := ShortComplex.mk sum (cokernel.π sum) (cokernel.condition sum)
  have hP : P.Exact := ShortComplex.exact_of_g_is_cokernel P (cokernelIsCokernel sum)
  let T := ShortComplex.mk (Abelian.image.ι sum) (cokernel.π sum)
    (Abelian.image_ι_comp_eq_zero (cokernel.condition sum))
  have hT : T.ShortExact := { exact := P.exact_iff_exact_image_ι.mp hP }
  have hmono : Mono (homologyMap T.f n) :=
    (hT.homology_exact₁ (n + 1) n rfl).mono_g ((hzero (n + 1)).eq_of_src _ _)
  have hepi : Epi (homologyMap T.f n) :=
    (hT.homology_exact₂ n).epi_f ((hzero n).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi (homologyMap T.f n)

/-- The ordinary homology boundary from the same sum-image sequence
and its open-cover comparison. -/
def singularHomologyMayerVietorisBoundary
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (n : ℕ) : singularHomology R X (n + 1) ⟶ singularHomology R ↥(A ∩ B) n := by
  let : IsIso (homologyMap (Abelian.image.ι (singularSubspaceSumChains R A B)) (n + 1)) :=
    isIso_homologyMap_singularMayerVietorisImageInclusion R A B hA hB hcover (n + 1)
  exact inv (homologyMap (Abelian.image.ι (singularSubspaceSumChains R A B)) (n + 1)) ≫
    (shortExact_singularMayerVietorisShortComplex R A B).δ (n + 1) n rfl

end AtiyahSinger
