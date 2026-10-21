/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualTargetOpenBlockProjectionHS
import Hironaka.Resolution.HironakaSmoothSubmersionAdaptedProductCoordinates
import Hironaka.Resolution.HironakaNormalCrossingsLocalBranches
import Hironaka.Analytic.AnalyticIrreducibleComponents

/-! Original holomorphic submersions, true flat-coordinate inverses and
EXISTING intrinsic HS at every order. Coherence only on real chart targets. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalSmoothSubmersionIntrinsicHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves BlowupFlatCoordinates
  HironakaNormalCrossingsLocalBranches HironakaSmoothSubmersionAdaptedProductCoordinates
  HironakaSmoothSubmersionMonomialChartPullback HironakaActualTargetOpenBlockProjectionHS
  HironakaActualProjectionIntrinsicHS HironakaActualBiholomorphicWholeStalkHS
  HironakaActualOpenIntrinsicHS HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalMonomialBasis HironakaActualProductHSProfileReflection

/-- The actual linear image of the TRUE flattening target. -/
def actualFlatLinearTarget {d m : ℕ} {p : ComplexModel d}
    (Φ : LocalHolomorphicEquivAt (n := d) p) (L : ComplexModel d ≃L[ℂ] ComplexModel m) :
    Opens (ComplexModel m) := ⟨L.symm ⁻¹' Φ.target,Φ.isOpen_target.preimage L.symm.continuous⟩

/-- Both true inverse equations and both holomorphic directions on actual opens. -/
def actualFlatLinearDiffeomorph {d m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsComplexManifold d M] {x : M}
    (Φ : LocalHolomorphicEquivAt (n := d) (chartAt (ComplexModel d) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel d) x).target)
    (L : ComplexModel d ≃L[ℂ] ComplexModel m) :
    (⟨flatDomain Φ,isOpen_flatDomain Φ⟩ : Opens M) ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel m)⟯
      actualFlatLinearTarget Φ L := by
  let O : Opens M := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let T := actualFlatLinearTarget Φ L
  let f : O → T := fun p => ⟨L (Φ.toFun (chartAt (ComplexModel d) x p)),by
    change L.symm (L (Φ.toFun _)) ∈ Φ.target
    rw [L.symm_apply_apply]
    exact Φ.mapsTo_toFun p.property.2⟩
  let g : T → O := fun q => ⟨(chartAt (ComplexModel d) x).symm (Φ.invFun (L.symm q)),
    (flatInverse_mem Φ q.property hsrc).1⟩
  have hf : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel m) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff T _).mp
    intro p
    have hΦ : ContMDiffAt 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel d) ∞ Φ.toFun
        (chartAt (ComplexModel d) x (p : M)) :=
      (contDiffAt_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source p.property.2).contMDiffAt
    have he : ContMDiffAt 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel d) ∞
        (chartAt (ComplexModel d) x) (p : M) :=
      (contMDiffOn_chart (n := ∞)).contMDiffAt
      ((chartAt (ComplexModel d) x).open_source.mem_nhds p.property.1)
    exact L.contDiff.contMDiff.contMDiffAt.comp p (hΦ.comp p (he.comp p (contMDiff_subtype_val p)))
  have hg : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel d) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff O _).mp
    intro q
    change ContMDiffAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel d) ∞
      (fun a : T => (chartAt (ComplexModel d) x).symm (Φ.invFun (L.symm a))) q
    have hΦ : ContMDiffAt 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel d) ∞ Φ.invFun (L.symm q) :=
      (contDiffAt_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target q.property).contMDiffAt
    have he : ContMDiffAt 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel d) ∞
        (chartAt (ComplexModel d) x).symm (Φ.invFun (L.symm q)) :=
      (contMDiffOn_chart_symm (n := ∞)).contMDiffAt
      ((chartAt (ComplexModel d) x).open_target.mem_nhds (hsrc (Φ.mapsTo_invFun q.property)))
    exact he.comp q (hΦ.comp q ((L.symm.contDiff.contMDiff.comp contMDiff_subtype_val) q))
  refine ⟨⟨f,g,?_,?_⟩,hf,hg⟩
  · intro p
    apply Subtype.ext
    change (chartAt (ComplexModel d) x).symm (Φ.invFun (L.symm (L (Φ.toFun _))))=p
    rw [L.symm_apply_apply]
    exact flatInverse_flat Φ p.property
  · intro q
    apply Subtype.ext
    change L (Φ.toFun (chartAt (ComplexModel d) x
      ((chartAt (ComplexModel d) x).symm (Φ.invFun (L.symm q)))))=q
    rw [(flatInverse_mem Φ q.property hsrc).2,L.apply_symm_apply]

private theorem actual_hs_pullback_comp {n m l : ℕ} {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    [ChartedSpace (ComplexModel l) Z] [IsComplexManifold l Z]
    {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel l) 𝓘(ℂ,ComplexModel m) ∞ g)
    (A : GermIdeal n X) (hA : A.IsCoherent) (z : Z) (ℓ : ℕ) :
    hilbertSamuelAt (GermIdeal.pullback (m := l) (f ∘ g) A) z ℓ=
      hilbertSamuelAt (GermIdeal.pullback (m := l) g (GermIdeal.pullback (m := m) f A)) z ℓ := by
  unfold hilbertSamuelAt
  rw [←HironakaActualWholeStalkHolomorphicPullback.map_wholeChartStalkIdeal_actual_pullback
    (hf.comp hg) A hA z]
  rw [←HironakaActualWholeStalkHolomorphicPullback.map_wholeChartStalkIdeal_actual_pullback
    hg _ (GermIdealPullbackCalculus.isCoherent_pullback hf hA) z]
  rw [←HironakaActualWholeStalkHolomorphicPullback.map_wholeChartStalkIdeal_actual_pullback hf A hA (g z)]
  rw [HironakaActualBiholomorphicWholeStalkHS.actualHolomorphicGermPullback_comp hf hg z,Ideal.map_map]
  rfl

private theorem actual_hs_block_square {n r : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel (n+r)) Y] [IsComplexManifold (n+r) Y]
    (U : Opens (ComplexModel n)) (V : Opens (ComplexModel (r+n)))
    (himage : ∀ p : V,blockProjection r n p ∈ U)
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U)
    (s : Y ≃ₘ⟮𝓘(ℂ,ComplexModel (n+r)),𝓘(ℂ,ComplexModel (r+n))⟯ V)
    {f : Y → X} (_hf : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hcomm : ∀ p,e (f p)=actualTargetOpenBlockProjection U V himage (s p))
    (A : GermIdeal n X) (hA : A.IsCoherent) (p : Y) (ℓ : ℕ) :
    let := normalExponentFintype r (ℓ+1)
    hilbertSamuelAt (GermIdeal.pullback (m := n+r) f A) p ℓ=
      ∑ α : normalExponentIndex r (ℓ+1),hilbertSamuelAt A (f p) (ℓ-normalExponentDegree α.val) := by
  let b := actualTargetOpenBlockProjection U V himage
  have hb := actualTargetOpenBlockProjection_contMDiff U V himage
  have heq : f=e.symm ∘ (b ∘ s) := by
    funext p
    exact (e.symm_apply_apply (f p)).symm.trans (congrArg e.symm (hcomm p))
  rw [heq,actual_hs_pullback_comp e.symm.contMDiff (hb.comp s.contMDiff) A hA p ℓ]
  have hB := GermIdealPullbackCalculus.isCoherent_pullback e.symm.contMDiff hA
  rw [actual_hs_pullback_comp hb s.contMDiff _ hB p ℓ,
    hilbertSamuelAt_actual_biholomorphic_models s _ (GermIdealPullbackCalculus.isCoherent_pullback hb hB) p ℓ,
    hilbertSamuelAt_actual_target_open_block_projection_convolution U V himage _ hB (s p) ℓ]
  apply Finset.sum_congr rfl
  intro α _
  rw [hilbertSamuelAt_actual_biholomorphic_models e.symm A hA (b (s p))]
  rfl

/-- ONLY original holomorphicity, genuine submersion and original coherence
construct the real local product and compute EVERY EXISTING intrinsic HS order. -/
theorem hilbertSamuelAt_original_submersion_convolution {n r : ℕ} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel (n+r)) Y] [IsComplexManifold (n+r) Y]
    {f : Y → X} (hf : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f)
    (A : GermIdeal n X) (hA : A.IsCoherent) (y : Y)
    (hsub : Manifold.IsSubmersionAt 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f y) (ℓ : ℕ) :
    let := normalExponentFintype r (ℓ+1)
    hilbertSamuelAt (GermIdeal.pullback (m := n+r) f A) y ℓ=
      ∑ α : normalExponentIndex r (ℓ+1),hilbertSamuelAt A (f y) (ℓ-normalExponentDegree α.val) := by
  obtain ⟨_,_,Φ,hsrcΦ,h0Φ,_⟩ := AnalyticIrreducibleComponents.regularAtDim_univ (n := n) (f y)
  obtain ⟨_R,_S,Ψ,_hR0,_hS0,_hSΦ,hsrcΨ,_h0Ψ,_hTarget,_hΨ,hd⟩ :=
    HironakaSmoothSubmersionAdaptedProductCoordinates.exists_adapted_product_coordinates
      (n := n) (r := r) (X := X) (Y := Y) (f := f) (y := y) hsub Φ h0Φ
  let D : Opens X := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let O : Opens Y := ⟨flatDomain Ψ,isOpen_flatDomain Ψ⟩
  let L : ComplexModel (n+r) ≃L[ℂ] ComplexModel (r+n) :=
    (fibreFirstSplit n r).trans (splitCoordinates r n).symm
  have hL : ∀ w,blockProjection r n (L w)=adaptedTargetProjection n r w := by
    intro w
    change (splitCoordinates r n ((splitCoordinates r n).symm (fibreFirstSplit n r w))).2=_
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  let e := actualFlatLinearDiffeomorph Φ hsrcΦ (ContinuousLinearEquiv.refl ℂ (ComplexModel n))
  let s := actualFlatLinearDiffeomorph Ψ hsrcΨ L
  let U := actualFlatLinearTarget Φ (ContinuousLinearEquiv.refl ℂ (ComplexModel n))
  let V := actualFlatLinearTarget Ψ L
  let f0 : O → D := fun p => ⟨f p,(hd p p.property).1⟩
  have hf0 : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f0 :=
    (ContMDiff.subtypeVal_comp_iff D _).mp (hf.comp contMDiff_subtype_val)
  have himage : ∀ p : V,blockProjection r n p ∈ U := by
    intro p
    have hs := congrArg Subtype.val (s.apply_symm_apply p)
    change L (Ψ.toFun (chartAt (ComplexModel (n+r)) y (s.symm p : Y)))=(p : ComplexModel (r+n)) at hs
    have hproj : blockProjection r n p=
        Φ.toFun (chartAt (ComplexModel n) (f y) (f (s.symm p))) := by
      rw [←hs,hL]
      exact (hd (s.symm p) (s.symm p).property).2
    change blockProjection r n p ∈ Φ.target
    rw [hproj]
    exact Φ.mapsTo_toFun (hd (s.symm p) (s.symm p).property).1.2
  have hcomm : ∀ p : O,e (f0 p)=actualTargetOpenBlockProjection U V himage (s p) := by
    intro p
    apply Subtype.ext
    change Φ.toFun (chartAt (ComplexModel n) (f y) (f p))=
      blockProjection r n (L (Ψ.toFun (chartAt (ComplexModel (n+r)) y p)))
    rw [hL]
    exact (hd p p.property).2.symm
  let A0 := GermIdeal.pullback (m := n) (Subtype.val : D → X) A
  have hA0 := GermIdealPullbackCalculus.isCoherent_pullback (f := (Subtype.val : D → X)) contMDiff_subtype_val hA
  let q : O := ⟨y,mem_chart_source _ y,Ψ.center_mem_source⟩
  have hlocal := actual_hs_block_square U V himage e s hf0 hcomm A0 hA0 q ℓ
  have hc1 := actual_hs_pullback_comp (f := (Subtype.val : D → X)) (g := f0)
    contMDiff_subtype_val hf0 A hA q ℓ
  have hc2 := actual_hs_pullback_comp (g := (Subtype.val : O → Y))
    hf contMDiff_subtype_val A hA q ℓ
  have hopen := hilbertSamuelAt_actual_open_pullback (GermIdeal.pullback (m := n+r) f A)
    (GermIdealPullbackCalculus.isCoherent_pullback hf hA) O q ℓ
  have hleft : hilbertSamuelAt (GermIdeal.pullback (m := n+r) f0 A0) q ℓ=
      hilbertSamuelAt (GermIdeal.pullback (m := n+r) f A) y ℓ :=
    hc1.symm.trans (hc2.trans hopen)
  rw [hleft] at hlocal
  exact hlocal.trans (Finset.sum_congr rfl (fun α _ =>
    hilbertSamuelAt_actual_open_pullback A hA D (f0 q) (ℓ-normalExponentDegree α.val)))

/-- ONLY the ORIGINAL genuine submersion and original coherence reflect BOTH
ENTIRE original profiles at ANY TWO actual source points. -/
theorem hilbertSamuelAt_original_submersion_entire_profile_eq_iff {n r : ℕ} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel (n+r)) Y] [IsComplexManifold (n+r) Y]
    {f : Y → X} (hsub : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f)
    (A : GermIdeal n X) (hA : A.IsCoherent) (p q : Y) :
    (∀ ℓ,hilbertSamuelAt (GermIdeal.pullback (m := n+r) f A) p ℓ=
      hilbertSamuelAt (GermIdeal.pullback (m := n+r) f A) q ℓ) ↔
      ∀ ℓ,hilbertSamuelAt A (f p) ℓ=hilbertSamuelAt A (f q) ℓ := by
  let Ip := HironakaHolomorphicJetRankLoci.wholeChartStalkIdeal A (f p) (f p) (mem_chart_source _ (f p))
  let Iq := HironakaHolomorphicJetRankLoci.wholeChartStalkIdeal A (f q) (f q) (mem_chart_source _ (f q))
  have hprod : ∀ y : Y,∀ ℓ,hilbertSamuelAt (GermIdeal.pullback (m := n+r) f A) y ℓ=
      HironakaHolomorphicPointJets.hilbertSamuelValue
        (Ideal.map (HironakaRelativeNormalIdeal.tangentPullback n r).toRingHom
          (HironakaHolomorphicJetRankLoci.wholeChartStalkIdeal A (f y) (f y) (mem_chart_source _ (f y)))) ℓ := by
    intro y ℓ
    rw [hilbertSamuelAt_original_submersion_convolution (n := n) (r := r) hsub.contMDiff A hA y (hsub.isSubmersionAt y) ℓ]
    exact (HironakaActualProductMixedHS.actualProductHilbertSamuel_convolution n r _ ℓ).symm
  simp only [hprod]
  exact actualProductHS_entire_profile_eq_iff n r Ip Iq

end
end Hironaka.HironakaOriginalSmoothSubmersionIntrinsicHS
