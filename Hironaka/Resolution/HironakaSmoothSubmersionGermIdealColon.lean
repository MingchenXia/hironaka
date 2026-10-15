/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionProjectionIdealColon
import Hironaka.Resolution.HironakaSmoothSubmersionComposition
import Hironaka.Analytic.ManifoldFiniteSpanChartTransport
import Hironaka.Analytic.FiniteGermIdealPullbackGenerators
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionGermIdealColon
open Hironaka.HolomorphicIdealSheaves CoherentIdealColon
  InvertibleIdealQuotient HironakaSmoothSubmersionComposition
  HironakaSmoothSubmersionNormalCrossings HironakaRelativeNormalIdeal
  HironakaSmoothSubmersionProjectionIdealColon
noncomputable section
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

theorem holomorphic_adapted_iff (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (F : X → ℂ) :
    (∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
      (fun w => F ((chartAt (ComplexModel n) x).symm (Φ.invFun w))) z) ↔
        HolomorphicAt n F x := by
  have h₁ := LocalHolomorphicFiniteSpanTransport.holomorphicAt_comp_inv_iff Φ
    (f := fun w => F ((chartAt (ComplexModel n) x).symm w))
  rw [h0] at h₁
  have h₂ := CoherentIdealColon.holomorphicAt_iff_holAt_chart
    (x := x) (mem_chart_source (ComplexModel n) x) (f := F)
  have h₂' : HolomorphicAt n F x ↔
      HolomorphicAt n (fun w => F ((chartAt (ComplexModel n) x).symm w))
        (chartAt (ComplexModel n) x x) := by
    simpa only [HolomorphicAt,OkaRelationSheaf.HolAt,mdifferentiableAt_iff_differentiableAt] using h₂
  simpa only [HolomorphicAt,mdifferentiableAt_iff_differentiableAt] using h₁.trans h₂'.symm

def adaptedGerm (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (F : X → ℂ) (hF : HolomorphicAt n F x) : HolGerm (ComplexModel n) :=
  HolGerm.mk (fun w => F ((chartAt (ComplexModel n) x).symm (Φ.invFun w)))
    ((holomorphic_adapted_iff x Φ h0 F).mpr hF)

theorem adaptedGerm_mul (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (F G : X → ℂ) (hF : HolomorphicAt n F x) (hG : HolomorphicAt n G x) :
    adaptedGerm x Φ h0 (G*F) (hG.mul hF) =
      adaptedGerm x Φ h0 G hG * adaptedGerm x Φ h0 F hF := by
  rw [adaptedGerm,adaptedGerm,adaptedGerm,← HolGerm.mk_mul]
  rfl

theorem exists_original_adapted_representative (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (g : HolGerm (ComplexModel n)) :
    ∃ (F : X → ℂ) (hF : HolomorphicAt n F x), adaptedGerm x Φ h0 F hF = g := by
  obtain ⟨H,hH,rfl⟩ := HolGerm.exists_eq_mk g
  let e := chartAt (ComplexModel n) x
  let F : X → ℂ := fun p => H (Φ.toFun (e p))
  have htar : (0 : ComplexModel n) ∈ Φ.target := by
    simpa only [h0] using Φ.mapsTo_toFun Φ.center_mem_source
  have ht : Tendsto Φ.invFun (𝓝 (0 : ComplexModel n)) (𝓝 (e x)) := by
    have hh := (Φ.invFun_holomorphic.differentiableAt
      (Φ.isOpen_target.mem_nhds htar)).continuousAt.tendsto
    have hz : Φ.invFun 0 = e x := by rw [← h0,Φ.left_inv _ Φ.center_mem_source]
    simpa only [hz] using hh
  have heq : (fun w => F (e.symm (Φ.invFun w))) =ᶠ[𝓝 (0 : ComplexModel n)] H := by
    filter_upwards [Φ.isOpen_target.mem_nhds htar,
      ht.eventually (e.open_target.mem_nhds (e.map_source (mem_chart_source _ x)))] with w hw hwe
    dsimp [F]
    rw [e.right_inv hwe,Φ.right_inv w hw]
  have hh : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
      (fun w => F (e.symm (Φ.invFun w))) z :=
    by
      filter_upwards [hH,heq.eventuallyEq_nhds] with z hz he
      exact hz.congr_of_eventuallyEq he
  have hF : HolomorphicAt n F x := (holomorphic_adapted_iff x Φ h0 F).mp hh
  exact ⟨F,hF,HolGerm.mk_eq_mk_iff.mpr heq⟩

def adaptedIdeal (I : GermIdeal n X) (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) : Ideal (HolGerm (ComplexModel n)) :=
  Ideal.span {g | ∃ (F : X → ℂ) (hF : HolomorphicAt n F x),
    I.mem x F ∧ g = adaptedGerm x Φ h0 F hF}

omit [IsComplexManifold n X] in
theorem holomorphicAt_of_mem_coherent (I : GermIdeal n X) (hI : I.IsCoherent)
    {x : X} {F : X → ℂ} (hF : I.mem x F) : HolomorphicAt n F x := by
  obtain ⟨U,hU,hx,s,G,hG,hgen⟩ := hI x
  exact ((hgen x hx F).mp hF).1

theorem mem_adaptedIdeal_iff (I : GermIdeal n X) (hI : I.IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (F : X → ℂ) (hF : HolomorphicAt n F x) :
    adaptedGerm x Φ h0 F hF ∈ adaptedIdeal I x Φ h0 ↔ I.mem x F := by
  classical
  obtain ⟨U,hU,hx,s,G,hG,hgen⟩ := hI x
  have hGh (i : Fin s) : HolomorphicAt n (G i) x :=
    CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU (hG i) hx
  let K := Ideal.span (range fun i => adaptedGerm x Φ h0 (G i) (hGh i))
  have hbridge (H : X → ℂ) (hh : HolomorphicAt n H x) :
      I.mem x H ↔ adaptedGerm x Φ h0 H hh ∈ K :=
    (hgen x hx H).trans ((ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
      x Φ h0 G H).trans (EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span
        _ (fun i => (holomorphic_adapted_iff x Φ h0 (G i)).mpr (hGh i))
        ((holomorphic_adapted_iff x Φ h0 H).mpr hh)))
  have heq : adaptedIdeal I x Φ h0 = K := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro g ⟨H,hh,hmem,rfl⟩
      exact (hbridge H hh).mp hmem
    · apply Ideal.span_le.mpr
      rintro g ⟨i,rfl⟩
      exact Ideal.subset_span ⟨G i,hGh i,
        (hgen x hx (G i)).mpr (isInSpanAt_self ⟨i,rfl⟩ (hGh i)),rfl⟩
  rw [heq]
  exact (hbridge F hF).symm


theorem adaptedIdeal_colon_eq (I L : GermIdeal n X)
    (hI : I.IsCoherent) (hL : L.IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) :
    adaptedIdeal (colon I L) x Φ h0 =
      (adaptedIdeal I x Φ h0).colon (adaptedIdeal L x Φ h0) := by
  ext g
  obtain ⟨F,hF,rfl⟩ := exists_original_adapted_representative x Φ h0 g
  rw [mem_adaptedIdeal_iff _ (isCoherent_colon_of_isCoherent hI hL) x Φ h0 F hF]
  constructor
  · intro hq
    apply Submodule.mem_colon.mpr
    intro b hb
    obtain ⟨G,hG,rfl⟩ := exists_original_adapted_representative x Φ h0 b
    have hLG := (mem_adaptedIdeal_iff L hL x Φ h0 G hG).mp hb
    have hm := (mem_colon_iff.mp hq).2 G hLG
    have hg := (mem_adaptedIdeal_iff I hI x Φ h0 (G*F) (hG.mul hF)).mpr hm
    rw [adaptedGerm_mul] at hg
    simpa only [smul_eq_mul,mul_comm] using hg
  · intro hq
    apply mem_colon_iff.mpr
    refine ⟨hF,?_⟩
    intro G hLG
    have hG := holomorphicAt_of_mem_coherent L hL hLG
    have hb := (mem_adaptedIdeal_iff L hL x Φ h0 G hG).mpr hLG
    have hm := Submodule.mem_colon.mp hq (adaptedGerm x Φ h0 G hG) hb
    apply (mem_adaptedIdeal_iff I hI x Φ h0 (G*F) (hG.mul hF)).mp
    rw [adaptedGerm_mul]
    simpa only [smul_eq_mul,mul_comm] using hm


private theorem adaptedIdeal_eq_span_of_generation (I : GermIdeal n X) (hI : I.IsCoherent)
    (x : X) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) {s : ℕ}
    (G : Fin s → X → ℂ) (hG : ∀ i, HolomorphicAt n (G i) x)
    (hgen : ∀ F, I.mem x F ↔ IsInSpanAt (n := n) (· ∈ range G) x F) :
    adaptedIdeal I x Φ h0 = Ideal.span (range fun i => adaptedGerm x Φ h0 (G i) (hG i)) := by
  ext g
  obtain ⟨F,hF,rfl⟩ := exists_original_adapted_representative x Φ h0 g
  rw [mem_adaptedIdeal_iff I hI x Φ h0 F hF,hgen F]
  exact (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff x Φ h0 G F).trans
    (EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span _
      (fun i => (holomorphic_adapted_iff x Φ h0 (G i)).mpr (hG i))
      ((holomorphic_adapted_iff x Φ h0 F).mpr hF))

section ActualSubmersion
variable {t : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (n+t)) Y] [IsComplexManifold (n+t) Y]
  {f : Y → X}

def actualSourceCoordinates
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (y : Y) : LocalHolomorphicEquivAt (n := n+t) (chartAt (ComplexModel (n+t)) y y) :=
  liftedCoordinatesAdd (hf.isSubmersionAt y) (centeredCoordinates (f y)) (centeredCoordinates_zero _)

theorem actualSourceCoordinates_zero
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (y : Y) : (actualSourceCoordinates hf y).toFun (chartAt (ComplexModel (n+t)) y y) = 0 :=
  (liftedCoordinatesAdd_dictionary (hf.isSubmersionAt y)
    (centeredCoordinates (f y)) (centeredCoordinates_zero _)).2.1

theorem actualSourceInverse_projection
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (y : Y) (w : ComplexModel (n+t)) (hw : w ∈ (actualSourceCoordinates hf y).target) :
    f ((chartAt (ComplexModel (n+t)) y).symm ((actualSourceCoordinates hf y).invFun w)) =
      (chartAt (ComplexModel n) (f y)).symm
        ((centeredCoordinates (f y)).invFun (tangentProjection n t w)) := by
  let Ψ := actualSourceCoordinates hf y
  let Φ := centeredCoordinates (n := n) (f y)
  let e := chartAt (ComplexModel (n+t)) y
  let b := chartAt (ComplexModel n) (f y)
  let z := e.symm (Ψ.invFun w)
  have hd := liftedCoordinatesAdd_dictionary (hf.isSubmersionAt y) Φ (centeredCoordinates_zero _)
  have hv : Ψ.invFun w ∈ Ψ.source := Ψ.mapsTo_invFun hw
  have hve : Ψ.invFun w ∈ e.target := hd.1 hv
  have hz : z ∈ BlowupFlatCoordinates.flatDomain Ψ := by
    refine ⟨e.map_target hve,?_⟩
    change e (e.symm (Ψ.invFun w)) ∈ Ψ.source
    rw [e.right_inv hve]
    exact hv
  have hdf := hd.2.2 z hz
  have heq : Φ.toFun (b (f z)) = tangentProjection n t w := by
    ext j
    have hh := (hdf.2 j).symm
    change Φ.toFun (b (f z)) j = Ψ.toFun (e z) (Fin.castAdd t j) at hh
    dsimp [z] at hh
    rw [e.right_inv hve,Ψ.right_inv w hw] at hh
    exact hh
  change f z = b.symm (Φ.invFun (tangentProjection n t w))
  calc
    f z = b.symm (b (f z)) := (b.left_inv hdf.1.1).symm
    _ = b.symm (Φ.invFun (Φ.toFun (b (f z)))) :=
      congrArg b.symm (Φ.left_inv _ hdf.1.2).symm
    _ = _ := congrArg b.symm (congrArg Φ.invFun heq)

theorem adaptedGerm_original_comp_projection
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (y : Y) (F : X → ℂ) (hF : HolomorphicAt n F (f y)) :
    adaptedGerm y (actualSourceCoordinates hf y) (actualSourceCoordinates_zero hf y)
      (F ∘ f) (hF.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiff.contMDiffAt)) =
      tangentPullback n t
        (adaptedGerm (f y) (centeredCoordinates (f y)) (centeredCoordinates_zero _) F hF) := by
  change HolGerm.mk (fun w => F (f ((chartAt (ComplexModel (n+t)) y).symm
      ((actualSourceCoordinates hf y).invFun w)))) _ = tangentPullback n t
        (HolGerm.mk (fun v => F ((chartAt (ComplexModel n) (f y)).symm
          ((centeredCoordinates (f y)).invFun v))) _)
  rw [tangentPullback,HironakaHolomorphicJetChartInvariance.compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  have htar : (0 : ComplexModel (n+t)) ∈ (actualSourceCoordinates hf y).target := by
    simpa only [actualSourceCoordinates_zero hf y] using
      (actualSourceCoordinates hf y).mapsTo_toFun (actualSourceCoordinates hf y).center_mem_source
  filter_upwards [(actualSourceCoordinates hf y).isOpen_target.mem_nhds htar] with w hw
  exact congrArg F (actualSourceInverse_projection hf y w hw)


theorem adaptedIdeal_actual_pullback
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (I : GermIdeal n X) (hI : I.IsCoherent) (y : Y) :
    adaptedIdeal (GermIdeal.pullback (m := n+t) f I) y
      (actualSourceCoordinates hf y) (actualSourceCoordinates_zero hf y) =
      Ideal.map (tangentPullback n t).toRingHom
        (adaptedIdeal I (f y) (centeredCoordinates (f y)) (centeredCoordinates_zero _)) := by
  classical
  obtain ⟨U,hU,hy,s,G,hG,hgen⟩ := hI (f y)
  have hGh (i : Fin s) : HolomorphicAt n (G i) (f y) :=
    CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU (hG i) hy
  have hfat : ∀ᶠ z in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel (n+t))
      𝓘(ℂ, ComplexModel n) ∞ f z := Eventually.of_forall fun _ => hf.contMDiff.contMDiffAt
  have hpb := FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
    hfat I G hGh (hgen (f y) hy)
  rw [adaptedIdeal_eq_span_of_generation _
    (GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hI) y
    (actualSourceCoordinates hf y) (actualSourceCoordinates_zero hf y)
    (fun i => G i ∘ f) (fun i => (hGh i).comp_contMDiff hfat) hpb,
    adaptedIdeal_eq_span_of_generation I hI (f y)
    (centeredCoordinates (f y)) (centeredCoordinates_zero _) G hGh (hgen (f y) hy),
    Ideal.map_span,← Set.range_comp']
  apply congrArg Ideal.span
  apply congrArg range
  funext i
  exact adaptedGerm_original_comp_projection hf y (G i) (hGh i)


theorem pullback_colon_eq_add
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (I L : GermIdeal n X) (hI : I.IsCoherent) (hL : L.IsCoherent) :
    GermIdeal.pullback (m := n+t) f (colon I L) =
      colon (GermIdeal.pullback (m := n+t) f I) (GermIdeal.pullback (m := n+t) f L) := by
  have hQ := isCoherent_colon_of_isCoherent hI hL
  have hIp := GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hI
  have hLp := GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hL
  have hQp := GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hQ
  have hQP := isCoherent_colon_of_isCoherent hIp hLp
  ext y F
  by_cases hF : HolomorphicAt (n+t) F y
  · have heq : adaptedIdeal (GermIdeal.pullback (m := n+t) f (colon I L)) y
        (actualSourceCoordinates hf y) (actualSourceCoordinates_zero hf y) =
        adaptedIdeal (colon (GermIdeal.pullback (m := n+t) f I)
          (GermIdeal.pullback (m := n+t) f L)) y
          (actualSourceCoordinates hf y) (actualSourceCoordinates_zero hf y) := by
      rw [adaptedIdeal_actual_pullback hf (colon I L) hQ y,
        adaptedIdeal_colon_eq I L hI hL,
        projection_map_colon_eq,
        adaptedIdeal_colon_eq _ _ hIp hLp,
        adaptedIdeal_actual_pullback hf I hI y,
        adaptedIdeal_actual_pullback hf L hL y]
    have h₁ := mem_adaptedIdeal_iff _ hQp y
      (actualSourceCoordinates hf y) (actualSourceCoordinates_zero hf y) F hF
    have h₂ := mem_adaptedIdeal_iff _ hQP y
      (actualSourceCoordinates hf y) (actualSourceCoordinates_zero hf y) F hF
    rw [heq] at h₁
    exact h₁.symm.trans h₂
  · constructor
    · intro hm
      exact (hF (holomorphicAt_of_mem_coherent _ hQp hm)).elim
    · intro hm
      exact (hF (holomorphicAt_of_mem_coherent _ hQP hm)).elim

end ActualSubmersion


theorem pullback_colon_eq {m : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y] {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (I L : GermIdeal n X) (hI : I.IsCoherent) (hL : L.IsCoherent) :
    GermIdeal.pullback (m := m) f (colon I L) =
      colon (GermIdeal.pullback (m := m) f I) (GermIdeal.pullback (m := m) f L) := by
  by_cases hY : Nonempty Y
  · obtain ⟨y⟩ := hY
    obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le
      (HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt (hf.isSubmersionAt y))
    exact pullback_colon_eq_add hf I L hI hL
  · have : IsEmpty Y := not_nonempty_iff.mp hY
    ext y F
    exact (IsEmpty.false y).elim

end
end Hironaka.HironakaSmoothSubmersionGermIdealColon
