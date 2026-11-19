import Hironaka.Analytic.Unibranch.OriginalNativeSmoothLocalProduct
import Hironaka.Analytic.Unibranch.EmbeddedCommonResolutionGeneralAnalyticSubsets
import Hironaka.Resolution.HironakaIntrinsicReducedCentreChartIdeal
import Hironaka.Resolution.HironakaNativePulledIdealComposition
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartier

/-! Whole intrinsic reduced ideals under genuine native analytic smooth maps.
No canonical-centre support correspondence or history is assumed.
Blueprint first: `original-native-smooth-reduced-ideal-pullback.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothReducedIdealPullback
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreIdealModel
  HironakaIntrinsicReducedCentreOpenPullback HironakaNativePulledIdealSheaf
  HironakaNativePulledIdealComposition HironakaSingularSubspaceBlowupCartier
  HironakaSingularModuleSheafStalk HironakaIntrinsicReducedCentreChartIdeal
  SourceReducedComplexSpace OriginalNativeProductWindow OriginalNativeSmoothLocalProduct
open scoped ProductComplexManifold

/-- The entire intrinsic reduced ideal through the SAME actual smooth quotient map. -/
theorem embedded_smooth_stalk_ideal {n m : ℕ} {M N : Type}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    {b : M → N} (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ b)
    {W C : Set N} (hC : IsComplexAnalyticSubset (n := m) C) (hCW : C ⊆ W)
    (w : b ⁻¹' W) :
    Ideal.map ((actualSubspaceMap hb.contMDiff (fun _ hx => hx)).stalkMap w).hom
      (intrinsicCentreStalkRange (actualSubspaceLocallyRingedSpace (n := m) W)
        ((Subtype.val : W → N) ⁻¹' C)
        (actualSubspaceMapTop hb.contMDiff (fun _ hx => hx) w)) =
    intrinsicCentreStalkRange (actualSubspaceLocallyRingedSpace (n := n) (b ⁻¹' W))
      ((Subtype.val : (b ⁻¹' W) → M) ⁻¹' (b ⁻¹' C)) w := by
  calc
    _ = Ideal.map ((actualSubspaceMap hb.contMDiff (fun _ hx => hx)).stalkMap w).hom
        (Ideal.map ((actualSubspaceInclusion (n := m) W).stalkMap
          (actualSubspaceMapTop hb.contMDiff (fun _ hx => hx) w)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := m) C) (b w.val))) :=
      congrArg (Ideal.map ((actualSubspaceMap hb.contMDiff (fun _ hx => hx)).stalkMap w).hom)
        (intrinsicReducedCentreStalkInclusion_range_model hCW _)
    _ = Ideal.map ((actualSubspaceInclusion (n := n) (b ⁻¹' W)).stalkMap w).hom
        (actualWholeSheafStalkIdeal (GermIdeal.pullback (m := n) b (vanishingIdeal C)) w.val) :=
      map_actualSubspace_stalk_ideal_pullback hb.contMDiff (fun _ hx => hx)
        (vanishingIdeal (n := m) C) (CartanIrreducible.cartanCoherence C hC) w
    _ = Ideal.map ((actualSubspaceInclusion (n := n) (b ⁻¹' W)).stalkMap w).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (b ⁻¹' C)) w.val) :=
      congrArg (fun A => Ideal.map ((actualSubspaceInclusion (n := n) (b ⁻¹' W)).stalkMap w).hom
        (actualWholeSheafStalkIdeal A w.val))
        (HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion hb C)
    _ = _ := (intrinsicReducedCentreStalkInclusion_range_model (Set.preimage_mono hCW) w).symm

variable {X Y : SourceReducedComplexSpace}

/-- Literal ambient trace of the original native subset in the actual target window. -/
def ambientTrace (e : LocalEmbedding Y) (P : Opens e.ambient) (S : Set Y.obj.left) : Set P :=
  (Subtype.val : P → e.ambient) ⁻¹' (Subtype.val '' (e.toPoint ⁻¹' S))

theorem ambientTrace_analytic (e : LocalEmbedding Y) (P : Opens e.ambient)
    {S : Set Y.obj.left} (hS : Y.IsAnalyticSubset S) :
    IsComplexAnalyticSubset (n := e.dim) (ambientTrace e P S) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val
    (hS.analytic_image_localEmbedding e)

theorem ambientTrace_subset (e : LocalEmbedding Y) (P : Opens e.ambient) (S : Set Y.obj.left) :
    ambientTrace e P S ⊆ targetCarrier e P := by
  rintro p ⟨c,_,hc⟩
  change p.val ∈ e.carrier
  exact hc ▸ c.property

theorem ambientTrace_point (e : LocalEmbedding Y) (P : Opens e.ambient) (S : Set Y.obj.left)
    (p : targetCarrier e P) :
    (targetInclusion e P).hom.left.base p ∈ S ↔ p.val ∈ ambientTrace e P S := by
  constructor
  · intro hp
    exact ⟨⟨p.val.val,p.property⟩,hp,rfl⟩
  · rintro ⟨c,hc,hcp⟩
    have heq : c = (⟨p.val.val,p.property⟩ : e.carrier) := Subtype.ext hcp
    change e.toPoint ⟨p.val.val,p.property⟩ ∈ S
    exact heq ▸ hc

private theorem map_stalkIdeal_comp {A B D : LocallyRingedSpace}
    (F : B ⟶ A) (q : D ⟶ B)
    (I : SheafOfModules (forgetRing A.toSheafedSpace.sheaf))
    (ι : I ⟶ SheafOfModules.unit (forgetRing A.toSheafedSpace.sheaf)) (z : D) :
    Ideal.map (q.stalkMap z).hom (nativePulledIdealStalkIdeal F I ι (q.base z)) =
      nativePulledIdealStalkIdeal (q ≫ F) I ι z := by
  let A := LinearMap.range (stalkInclusionLinearMap A.toSheafedSpace.sheaf I ι (F.base (q.base z)))
  change Ideal.map (q.stalkMap z).hom (Ideal.map (F.stalkMap (q.base z)).hom A) =
    Ideal.map ((q ≫ F).stalkMap z).hom A
  exact (Ideal.map_map (I := A) (F.stalkMap (q.base z)).hom (q.stalkMap z).hom).trans
    (congrArg (fun h => Ideal.map h A)
      (congrArg CommRingCat.Hom.hom (LocallyRingedSpace.stalkMap_comp (f := q) (g := F) z)).symm)

/-- Whole intrinsic ideal pullback at the SAME original point of an ordinary smooth map. -/
theorem smooth_pulled_stalkIdeal_eq (f : X ⟶ Y) (x : X.obj.left)
    (hsm : IsSmoothAt f x) {S : Set Y.obj.left} (hS : Y.IsAnalyticSubset S) :
    nativePulledIdealStalkIdeal f.hom.left (intrinsicReducedCentreIdealModule Y.obj.left S)
      (intrinsicReducedCentreIdealInclusion Y.obj.left S) x =
      intrinsicCentreStalkRange X.obj.left (f.hom.left.base ⁻¹' S) x := by
  obtain ⟨e,r,P,W,hWP,iS,s,hiS,hs,_,_,hsq,hb,_⟩ :=
    exists_ambient_representation f x hsm ⊤ ⊤ (Set.mem_univ x) (Set.mem_univ _)
  let : LocallyRingedSpace.IsOpenImmersion iS.hom.left := hiS
  let : LocallyRingedSpace.IsOpenImmersion (targetInclusion e P).hom.left :=
    targetInclusion_isOpenImmersion e P
  let q := nativeProjection e r P W hWP
  let b := ambientProjection e r P W hWP
  let C := ambientTrace e P S
  have ht : (targetInclusion e P).hom.left.base ⁻¹' S =
      (Subtype.val : targetCarrier e P → P) ⁻¹' C := by
    ext p
    exact ambientTrace_point e P S p
  have hraw : iS.hom.left ≫ f.hom.left = q.hom.left ≫ (targetInclusion e P).hom.left :=
    congrArg (fun a => a.hom.left) hsq
  have hc : (Subtype.val : windowCarrier e r W → W) ⁻¹' (b ⁻¹' C) =
      iS.hom.left.base ⁻¹' (f.hom.left.base ⁻¹' S) := by
    ext w
    change b w.val ∈ C ↔ f.hom.left.base (iS.hom.left.base w) ∈ S
    have hp := congrArg (fun a => a.base w) hraw
    exact (ambientTrace_point e P S (q.hom.left.base w)).symm.trans
      (iff_of_eq (congrArg (fun y => y ∈ S) hp.symm))
  have hloc : nativePulledIdealStalkIdeal f.hom.left
      (intrinsicReducedCentreIdealModule Y.obj.left S)
      (intrinsicReducedCentreIdealInclusion Y.obj.left S) (iS.hom.left.base s) =
      intrinsicCentreStalkRange X.obj.left (f.hom.left.base ⁻¹' S) (iS.hom.left.base s) := by
    let E := (asIso (iS.hom.left.stalkMap s)).commRingCatIsoToRingEquiv
    apply E.idealComapOrderIso.symm.injective
    change Ideal.map (iS.hom.left.stalkMap s).hom
      (nativePulledIdealStalkIdeal f.hom.left (intrinsicReducedCentreIdealModule Y.obj.left S)
        (intrinsicReducedCentreIdealInclusion Y.obj.left S) (iS.hom.left.base s)) =
      Ideal.map (iS.hom.left.stalkMap s).hom
        (intrinsicCentreStalkRange X.obj.left (f.hom.left.base ⁻¹' S) (iS.hom.left.base s))
    calc
      _ = nativePulledIdealStalkIdeal (iS.hom.left ≫ f.hom.left)
          (intrinsicReducedCentreIdealModule Y.obj.left S)
          (intrinsicReducedCentreIdealInclusion Y.obj.left S) s :=
        map_stalkIdeal_comp f.hom.left iS.hom.left _ _ s
      _ = nativePulledIdealStalkIdeal (q.hom.left ≫ (targetInclusion e P).hom.left)
          (intrinsicReducedCentreIdealModule Y.obj.left S)
          (intrinsicReducedCentreIdealInclusion Y.obj.left S) s :=
        congrArg (fun a => nativePulledIdealStalkIdeal a
          (intrinsicReducedCentreIdealModule Y.obj.left S)
          (intrinsicReducedCentreIdealInclusion Y.obj.left S) s) hraw
      _ = Ideal.map (q.hom.left.stalkMap s).hom
          (nativePulledIdealStalkIdeal (targetInclusion e P).hom.left
            (intrinsicReducedCentreIdealModule Y.obj.left S)
            (intrinsicReducedCentreIdealInclusion Y.obj.left S) (q.hom.left.base s)) :=
        (map_stalkIdeal_comp (targetInclusion e P).hom.left q.hom.left _ _ s).symm
      _ = Ideal.map (q.hom.left.stalkMap s).hom
          (intrinsicCentreStalkRange (targetSpace e P).obj.left
            ((Subtype.val : targetCarrier e P → P) ⁻¹' C) (q.hom.left.base s)) := by
        exact congrArg (Ideal.map (q.hom.left.stalkMap s).hom)
          ((openImmersion_pulled_stalkIdeal_eq (targetInclusion e P).hom.left S _).trans
            (congrArg (fun D => intrinsicCentreStalkRange (targetSpace e P).obj.left D
              (q.hom.left.base s)) ht))
      _ = intrinsicCentreStalkRange (windowSpace e r W).obj.left
          ((Subtype.val : windowCarrier e r W → W) ⁻¹' (b ⁻¹' C)) s :=
        embedded_smooth_stalk_ideal hb (ambientTrace_analytic e P hS) (ambientTrace_subset e P S) s
      _ = intrinsicCentreStalkRange (windowSpace e r W).obj.left
          (iS.hom.left.base ⁻¹' (f.hom.left.base ⁻¹' S)) s :=
        congrArg (fun D => intrinsicCentreStalkRange (windowSpace e r W).obj.left D s) hc
      _ = _ := (openImmersion_pulled_stalkIdeal_eq iS.hom.left (f.hom.left.base ⁻¹' S) s).symm
  exact hs ▸ hloc

/-- Every actual source-open section ideal agrees, with the original scalar maps. -/
theorem smooth_pulled_sectionIdeal_eq (f : X ⟶ Y) (hsm : IsSmoothMorphism f)
    {S : Set Y.obj.left} (hS : Y.IsAnalyticSubset S) (U : Opens X.obj.left.toTopCat) :
    nativePulledIdealSectionIdeal f.hom.left (intrinsicReducedCentreIdealModule Y.obj.left S)
      (intrinsicReducedCentreIdealInclusion Y.obj.left S) U =
      intrinsicReducedCentreSectionIdeal X.obj.left (f.hom.left.base ⁻¹' S) U := by
  ext t
  constructor
  · intro ht x hx hxS
    have hr := ht x hx
    rw [smooth_pulled_stalkIdeal_eq f x (hsm x) hS] at hr
    exact intrinsicCentreStalkRange_le_maximalIdeal X.obj.left (f.hom.left.base ⁻¹' S) x hxS hr
  · intro ht x hx
    rw [smooth_pulled_stalkIdeal_eq f x (hsm x) hS]
    exact ⟨TopCat.Presheaf.germ
      (intrinsicReducedCentreIdealModule X.obj.left (f.hom.left.base ⁻¹' S)).val.presheaf
      U x hx ⟨t,ht⟩,
      stalkInclusionLinearMap_germ X.obj.left.toSheafedSpace.sheaf
        (intrinsicReducedCentreIdealModule X.obj.left (f.hom.left.base ⁻¹' S))
        (intrinsicReducedCentreIdealInclusion X.obj.left (f.hom.left.base ⁻¹' S))
        x U hx ⟨t,ht⟩⟩

/-- Literal equality of the actual unit submodules, including actions/restrictions. -/
theorem smooth_pulled_submodule_eq (f : X ⟶ Y) (hsm : IsSmoothMorphism f)
    {S : Set Y.obj.left} (hS : Y.IsAnalyticSubset S) :
    nativePulledIdealSubmodule f.hom.left (intrinsicReducedCentreIdealModule Y.obj.left S)
      (intrinsicReducedCentreIdealInclusion Y.obj.left S) =
      intrinsicReducedCentreSubmodule X.obj.left (f.hom.left.base ⁻¹' S) := by
  apply PresheafOfModules.Submodule.ext
  intro U
  exact smooth_pulled_sectionIdeal_eq f hsm hS (unop U)

/-- Full native sheaf-module iso, derived from the ordinary smooth morphism. -/
def smooth_pulled_idealIso (f : X ⟶ Y) (hsm : IsSmoothMorphism f)
    {S : Set Y.obj.left} (hS : Y.IsAnalyticSubset S) :
    nativePulledIdealModule f.hom.left (intrinsicReducedCentreIdealModule Y.obj.left S)
      (intrinsicReducedCentreIdealInclusion Y.obj.left S) ≅
      intrinsicReducedCentreIdealModule X.obj.left (f.hom.left.base ⁻¹' S) where
  hom := ⟨PresheafOfModules.Submodule.homOfLE (smooth_pulled_submodule_eq f hsm hS).le⟩
  inv := ⟨PresheafOfModules.Submodule.homOfLE (smooth_pulled_submodule_eq f hsm hS).ge⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

/-- The full original structure-sheaf inclusion triangle. -/
theorem smooth_pulled_idealIso_hom_comp_inclusion (f : X ⟶ Y) (hsm : IsSmoothMorphism f)
    {S : Set Y.obj.left} (hS : Y.IsAnalyticSubset S) :
    (smooth_pulled_idealIso f hsm hS).hom ≫
      intrinsicReducedCentreIdealInclusion X.obj.left (f.hom.left.base ⁻¹' S) =
      nativePulledIdealInclusion f.hom.left (intrinsicReducedCentreIdealModule Y.obj.left S)
        (intrinsicReducedCentreIdealInclusion Y.obj.left S) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (smooth_pulled_submodule_eq f hsm hS).le

/-- The inverse full original structure-sheaf inclusion triangle. -/
theorem smooth_pulled_idealIso_inv_comp_inclusion (f : X ⟶ Y) (hsm : IsSmoothMorphism f)
    {S : Set Y.obj.left} (hS : Y.IsAnalyticSubset S) :
    (smooth_pulled_idealIso f hsm hS).inv ≫
      nativePulledIdealInclusion f.hom.left (intrinsicReducedCentreIdealModule Y.obj.left S)
        (intrinsicReducedCentreIdealInclusion Y.obj.left S) =
      intrinsicReducedCentreIdealInclusion X.obj.left (f.hom.left.base ⁻¹' S) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (smooth_pulled_submodule_eq f hsm hS).ge

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothReducedIdealPullback
