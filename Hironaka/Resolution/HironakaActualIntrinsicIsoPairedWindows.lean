/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualLocalCommonGraphModel
import Hironaka.Resolution.HironakaActualAnalyticSubspaceIntrinsicLifting
import Hironaka.Resolution.HironakaActualHolomorphicStalkSurjection
import Hironaka.Analytic.AnalyticSubsetPreimage

/-!
# Arbitrary intrinsic isomorphisms internally produce true paired original windows

Actual local ambient lifts give original total coordinate representatives
holomorphic only on actual opens. True inverse base-point identities produce
paired subset windows without reciprocal full-ambient mapping assumptions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualIntrinsicIsoPairedWindows
noncomputable section
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceIntrinsicLifting HironakaActualHolomorphicStalkSurjection
  HironakaReducedComplexAnalyticSpaces HironakaActualLocalCommonGraphModel
variable {n m : ℕ} {U : Opens (ComplexModel n)} {V : Opens (ComplexModel m)}
  {C : Set U} {D : Set V}

/-- Actual intrinsic maps internally yield true original coordinate representatives on genuine ambient opens. -/
theorem exists_actual_original_coordinate_window
    (F : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C) (c : C) :
    ∃ (A : Opens (ComplexModel n)) (F₀ : ComplexModel n → ComplexModel m),
      A ≤ U ∧ c.val.val ∈ A ∧ ContDiffOn ℂ ∞ F₀ A ∧
      ∀ y : C,y.val.val ∈ A → F₀ y.val.val = (F.base y).val.val := by
  obtain ⟨O,hcO,f,hf,hCD,hsquare⟩ := exists_actualSubspaceMap_local_holomorphic_lift F hF c
  let A : Opens (ComplexModel n) :=
    ⟨(Subtype.val : U → ComplexModel n) '' (O : Set U),U.isOpen.isOpenMap_subtype_val _ O.isOpen⟩
  let H : U → ComplexModel m := actualOpenVectorExtension O (fun z : O => (f z).val)
  let F₀ : ComplexModel n → ComplexModel m := actualOpenVectorExtension U H
  have hfvec : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ (fun z : O => (f z).val) :=
    (contMDiff_subtype_val (U := V)).comp hf
  have hdiff : DifferentiableOn ℂ F₀ (A : Set (ComplexModel n)) := by
    rintro x ⟨u,hu,rfl⟩
    have hH : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ H u :=
      actualOpenVectorExtension_contMDiffAt O _ ⟨u,hu⟩ hfvec.contMDiffAt
    have hF₀ : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ F₀ u.val :=
      actualOpenVectorExtension_contMDiffAt U H u hH
    exact (mdifferentiableAt_iff_differentiableAt.mp
      (hF₀.mdifferentiableAt (by simp))).differentiableWithinAt
  refine ⟨A,F₀,?_,⟨c.val,hcO,rfl⟩,contDiffOn_of_differentiableOn_complex hdiff A.isOpen,?_⟩
  · rintro x ⟨u,_hu,rfl⟩
    exact u.property
  · intro y hy
    obtain ⟨u,hu,he⟩ := hy
    have huy : u = y.val := Subtype.ext he
    have hyO : y.val ∈ O := huy ▸ hu
    let z : (Subtype.val : O → U) ⁻¹' C := ⟨⟨y.val,hyO⟩,y.property⟩
    have hp := congrArg (fun a => (a.base z).val) hsquare
    change f ⟨y.val,hyO⟩ = (F.base y).val at hp
    calc
      F₀ y.val.val = H y.val := actualOpenVectorExtension_apply U H y.val
      _ = (f ⟨y.val,hyO⟩).val := actualOpenVectorExtension_apply O _ ⟨y.val,hyO⟩
      _ = (F.base y).val.val := congrArg Subtype.val hp

/-- The literal original coordinate carrier of an actual embedded model. -/
def coordinateCarrier (C : Set U) : Set (ComplexModel n) := (Subtype.val : U → ComplexModel n) '' C

private theorem coordinateCarrier_mem (C : Set U) (x : U) : x.val ∈ coordinateCarrier C ↔ x ∈ C := by
  constructor
  · rintro ⟨y,hy,he⟩
    have hxy : y = x := Subtype.ext he
    exact hxy ▸ hy
  · exact fun hx => ⟨x,hx,rfl⟩

private theorem analytic_coordinate_window (C : Set U) (hC : IsComplexAnalyticSubset (n := n) C)
    (A : Opens (ComplexModel n)) (hAU : A ≤ U) :
    IsComplexAnalyticSubset (n := n) ((Subtype.val : A → ComplexModel n) ⁻¹' (coordinateCarrier C ∩ A)) := by
  let i : A → U := fun x => ⟨x.val,hAU x.property⟩
  have he : (Subtype.val : A → ComplexModel n) ⁻¹' (coordinateCarrier C ∩ A) = i ⁻¹' C := by
    ext x
    change (x.val ∈ coordinateCarrier C ∧ x.val ∈ A) ↔ i x ∈ C
    rw [and_iff_left x.property]
    exact coordinateCarrier_mem C (i x)
  rw [he]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_inclusion hAU) hC

/-- ANY original intrinsic iso internally supplies paired genuine original windows and inverse identities ONLY on actual subsets. -/
theorem exists_actual_intrinsic_iso_paired_windows
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := m) D) (c : C) :
    ∃ (A : Opens (ComplexModel n)) (B : Opens (ComplexModel m))
      (F : ComplexModel n → ComplexModel m) (G : ComplexModel m → ComplexModel n),
      A ≤ U ∧ B ≤ V ∧ c.val.val ∈ A ∧ (e.hom.base c).val.val ∈ B ∧
      ContDiffOn ℂ ∞ F A ∧ ContDiffOn ℂ ∞ G B ∧
      IsComplexAnalyticSubset (n := n) ((Subtype.val : A → ComplexModel n) ⁻¹' (coordinateCarrier C ∩ A)) ∧
      IsComplexAnalyticSubset (n := m) ((Subtype.val : B → ComplexModel m) ⁻¹' (coordinateCarrier D ∩ B)) ∧
      (∀ x ∈ coordinateCarrier C ∩ A,F x ∈ coordinateCarrier D ∩ B) ∧
      (∀ y ∈ coordinateCarrier D ∩ B,G y ∈ coordinateCarrier C ∩ A) ∧
      (∀ x ∈ coordinateCarrier C ∩ A,G (F x) = x) ∧
      (∀ y ∈ coordinateCarrier D ∩ B,F (G y) = y) ∧
      (∀ y : C,y.val.val ∈ A → F y.val.val = (e.hom.base y).val.val) ∧
      (∀ y : D,y.val.val ∈ B → G y.val.val = (e.inv.base y).val.val) := by
  have hi : e.inv ≫ subspacePointMap (n := n) C = subspacePointMap (n := m) D := by
    rw [← he,← Category.assoc,e.inv_hom_id,Category.id_comp]
  obtain ⟨A₀,F,hAU,hcA,hF,hFval⟩ := exists_actual_original_coordinate_window e.hom he c
  obtain ⟨B₀,G,hBV,hdB,hG,hGval⟩ := exists_actual_original_coordinate_window e.inv hi (e.hom.base c)
  have hleft (y : C) : e.inv.base (e.hom.base y) = y :=
    congrArg (fun a => a.base y) e.hom_inv_id
  have hright (y : D) : e.hom.base (e.inv.base y) = y :=
    congrArg (fun a => a.base y) e.inv_hom_id
  let A : Opens (ComplexModel n) :=
    ⟨(A₀ : Set (ComplexModel n)) ∩ F ⁻¹' B₀,
      hF.continuousOn.isOpen_inter_preimage A₀.isOpen B₀.isOpen⟩
  let B : Opens (ComplexModel m) :=
    ⟨(B₀ : Set (ComplexModel m)) ∩ G ⁻¹' A₀,
      hG.continuousOn.isOpen_inter_preimage B₀.isOpen A₀.isOpen⟩
  have hAU' : A ≤ U := fun _ hx => hAU hx.1
  have hBV' : B ≤ V := fun _ hy => hBV hy.1
  have hFpoint : F c.val.val = (e.hom.base c).val.val := hFval c hcA
  have hGpoint : G (e.hom.base c).val.val = c.val.val := by
    rw [hGval (e.hom.base c) hdB,hleft c]
  have hcA' : c.val.val ∈ A := ⟨hcA,by change F c.val.val ∈ B₀;rw [hFpoint];exact hdB⟩
  have hdB' : (e.hom.base c).val.val ∈ B := ⟨hdB,by change G (e.hom.base c).val.val ∈ A₀;rw [hGpoint];exact hcA⟩
  have hforwardCarrier : ∀ x ∈ coordinateCarrier C,x ∈ A₀ → F x ∈ coordinateCarrier D := by
    rintro x ⟨u,hu,rfl⟩ hx
    let y : C := ⟨u,hu⟩
    rw [hFval y hx]
    exact ⟨(e.hom.base y).val,(e.hom.base y).property,rfl⟩
  have hbackwardCarrier : ∀ y ∈ coordinateCarrier D,y ∈ B₀ → G y ∈ coordinateCarrier C := by
    rintro y ⟨v,hv,rfl⟩ hy
    let z : D := ⟨v,hv⟩
    rw [hGval z hy]
    exact ⟨(e.inv.base z).val,(e.inv.base z).property,rfl⟩
  have hGF : ∀ x ∈ coordinateCarrier C,x ∈ A₀ → F x ∈ B₀ → G (F x) = x := by
    rintro x ⟨u,hu,rfl⟩ hx hFx
    let y : C := ⟨u,hu⟩
    have hFy := hFval y hx
    rw [hFy] at hFx ⊢
    rw [hGval (e.hom.base y) hFx,hleft y]
  have hFG : ∀ y ∈ coordinateCarrier D,y ∈ B₀ → G y ∈ A₀ → F (G y) = y := by
    rintro y ⟨v,hv,rfl⟩ hy hGy
    let z : D := ⟨v,hv⟩
    have hGz := hGval z hy
    rw [hGz] at hGy ⊢
    rw [hFval (e.inv.base z) hGy,hright z]
  have hFD : ∀ x ∈ coordinateCarrier C ∩ A,F x ∈ coordinateCarrier D ∩ B := by
    intro x hx
    refine ⟨hforwardCarrier x hx.1 hx.2.1,hx.2.2,?_⟩
    change G (F x) ∈ A₀
    rw [hGF x hx.1 hx.2.1 hx.2.2]
    exact hx.2.1
  have hGC : ∀ y ∈ coordinateCarrier D ∩ B,G y ∈ coordinateCarrier C ∩ A := by
    intro y hy
    refine ⟨hbackwardCarrier y hy.1 hy.2.1,hy.2.2,?_⟩
    change F (G y) ∈ B₀
    rw [hFG y hy.1 hy.2.1 hy.2.2]
    exact hy.2.1
  exact ⟨A,B,F,G,hAU',hBV',hcA',hdB',hF.mono inter_subset_left,hG.mono inter_subset_left,
    analytic_coordinate_window C hC A hAU',analytic_coordinate_window D hD B hBV',hFD,hGC,
    (fun x hx => hGF x hx.1 hx.2.1 hx.2.2),(fun y hy => hFG y hy.1 hy.2.1 hy.2.2),
    (fun y hy => hFval y hy.1),(fun y hy => hGval y hy.1)⟩

/-- ANY intrinsic iso internally constructs paired original windows and a genuine ACTUAL common analytic graph object locally. -/
theorem exists_actual_intrinsic_iso_common_graph
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := m) D) (c : C) :
    ∃ (A : Opens (ComplexModel n)) (B : Opens (ComplexModel m))
      (F : ComplexModel n → ComplexModel m),
      A ≤ U ∧ B ≤ V ∧ c.val.val ∈ A ∧ (e.hom.base c).val.val ∈ B ∧
      let W := coordinateCarrier C ∩ (A : Set (ComplexModel n))
      let T := coordinateCarrier D ∩ (B : Set (ComplexModel m))
      ∃ (eW : actualSubspaceLocallyRingedSpace (n := n) ((Subtype.val : A → ComplexModel n) ⁻¹' W) ≅
          actualSubspaceLocallyRingedSpace (n := n+m) (commonGraphSubset A B F W))
        (eD : actualSubspaceLocallyRingedSpace (n := m) ((Subtype.val : B → ComplexModel m) ⁻¹' T) ≅
          actualSubspaceLocallyRingedSpace (n := n+m) (commonGraphSubset A B F W)),
        eW.hom ≫ subspacePointMap (n := n+m) (commonGraphSubset A B F W) =
          subspacePointMap (n := n) ((Subtype.val : A → ComplexModel n) ⁻¹' W) ∧
        eD.hom ≫ subspacePointMap (n := n+m) (commonGraphSubset A B F W) =
          subspacePointMap (n := m) ((Subtype.val : B → ComplexModel m) ⁻¹' T) ∧
        hasAnalyticCharts (modelOver (commonDomain A B) (commonGraphSubset A B F W)) := by
  obtain ⟨A,B,F,G,hAU,hBV,hcA,hdB,hF,hG,hWa,hTa,hFD,hGW,hGF,hFG,_hFval,_hGval⟩ :=
    exists_actual_intrinsic_iso_paired_windows e he hC hD c
  let W := coordinateCarrier C ∩ (A : Set (ComplexModel n))
  let T := coordinateCarrier D ∩ (B : Set (ComplexModel m))
  have hWA : W ⊆ A := inter_subset_right
  have hTB : T ⊆ B := inter_subset_right
  obtain ⟨eW,eD,hw,hd⟩ := actualCommonGraphModelIsos A B W T hWA hTB F G hF hG hFD hGW hGF hFG
  have ha := hasAnalyticCharts_commonGraphModel A B W T hWA hTB F G hF hG hFD hGW hGF hFG hWa
  exact ⟨A,B,F,hAU,hBV,hcA,hdB,eW,eD,hw,hd,ha⟩

end
end Hironaka.HironakaActualIntrinsicIsoPairedWindows
