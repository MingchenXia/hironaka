import Hironaka.Analytic.Unibranch.OriginalNativeSmoothSingularLocus
import Hironaka.Resolution.HironakaSmoothSubmersionContactParameterCharts

/-! Internally derived thin target windows for ordinary native smooth maps at
original singular image points. No chosen recipe or centre packet is input.
Blueprint first: `original-native-smooth-thin-window.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothThinWindow
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaSmoothSubmersionOrderedGlobalTrace
  HironakaSmoothSubmersionComposition HironakaSmoothSubmersionContactParameterCharts
  HironakaSmoothSubmersionHistoricalCompanionMasks SourceReducedComplexSpace
  OriginalNativeProductWindow OriginalNativeSmoothLocalProduct
open scoped ProductComplexManifold

variable {X Y : SourceReducedComplexSpace}

def inverseSpace (e : LocalEmbedding Y) {m : ℕ} (A : BlowupTowers.CMfd.{0} m)
    (b : A → e.ambient)
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel e.dim) ∞ b) :
    SourceReducedComplexSpace :=
  ofClosedAnalytic (b ⁻¹' e.carrier)
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff e.analytic)

def inverseProjection (e : LocalEmbedding Y) {m : ℕ} (A : BlowupTowers.CMfd.{0} m)
    (b : A → e.ambient)
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel e.dim) ∞ b) :
    inverseSpace e A b hb ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (actualSubspaceMap hb.contMDiff (fun _ hx => hx) ≫ e.map)
    ((Category.assoc _ _ _).trans ((congrArg (fun a => actualSubspaceMap hb.contMDiff
      (fun _ hx => hx) ≫ a) e.overPoint).trans
        (actualSubspaceMap_point hb.contMDiff (fun _ hx => hx)))))

theorem inverse_whole_ideal (e : LocalEmbedding Y) {m : ℕ} (A : BlowupTowers.CMfd.{0} m)
    (b : A → e.ambient)
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel e.dim) ∞ b) :
    GermIdeal.pullback (m := m) b (vanishingIdeal (n := e.dim) e.carrier) =
      vanishingIdeal (n := m) (b ⁻¹' e.carrier) :=
  HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion hb e.carrier

/-- Ordinary geometric OUTPUT, constructed below; no recipe/history field. -/
structure ThinWindow (f : X ⟶ Y) (x : X.obj.left)
    (V : Opens X.obj.left) (T : Opens Y.obj.left) where
  target : LocalEmbedding Y
  sourceDim : ℕ
  sourceAmbient : BlowupTowers.CMfd.{0} sourceDim
  ambientMap : sourceAmbient → target.ambient
  submersion : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel sourceDim) 𝓘(ℂ,ComplexModel target.dim) ∞ ambientMap
  sourceInclusion : inverseSpace target sourceAmbient ambientMap submersion ⟶ X
  sourcePoint : (inverseSpace target sourceAmbient ambientMap submersion).obj.left
  thin : interior target.carrier = ∅
  isOpenImmersion : LocallyRingedSpace.IsOpenImmersion sourceInclusion.hom.left
  point : sourceInclusion.hom.left.base sourcePoint = x
  square : sourceInclusion ≫ f = inverseProjection target sourceAmbient ambientMap submersion
  source_range : range sourceInclusion.hom.left.base ⊆ (V : Set X.obj.left)
  target_range : range target.toPoint ⊆ (T : Set Y.obj.left)

theorem ThinWindow.target_point {f : X ⟶ Y} {x : X.obj.left}
    {V : Opens X.obj.left} {T : Opens Y.obj.left} (w : ThinWindow f x V T) :
    w.target.toPoint ⟨w.ambientMap w.sourcePoint.val,w.sourcePoint.property⟩ =
      f.hom.left.base x := by
  have h := congrArg (fun a => a.hom.left.base w.sourcePoint) w.square
  exact h.symm.trans (congrArg f.hom.left.base w.point)

theorem ThinWindow.whole_ideal {f : X ⟶ Y} {x : X.obj.left}
    {V : Opens X.obj.left} {T : Opens Y.obj.left} (w : ThinWindow f x V T) :
    GermIdeal.pullback (m := w.sourceDim) w.ambientMap
      (vanishingIdeal (n := w.target.dim) w.target.carrier) =
        vanishingIdeal (n := w.sourceDim) (w.ambientMap ⁻¹' w.target.carrier) :=
  inverse_whole_ideal w.target w.sourceAmbient w.ambientMap w.submersion

private theorem restrictModelMap_eq (e : LocalEmbedding Y) (B : Opens (ComplexModel e.dim))
    (hB : B ≤ e.ambient) :
    e.restrictModelMapWith B hB (e.restrictCarrier B hB) (fun _ => Iff.rfl) =
      actualSubspaceMap (contMDiff_inclusion hB) (fun _ hx => hx) := by
  exact (actualSubspaceMap_comp (opensWithinDiffeo e.ambient B hB).contMDiff
    contMDiff_subtype_val (fun _ hx => hx) (fun _ hx => hx)).symm

/-- The actual thin target and same full native submersion square are OUTPUT. -/
theorem exists_thin_window (f : X ⟶ Y) (x : X.obj.left) (hsm : IsSmoothAt f x)
    (hsing : f.hom.left.base x ∈ intrinsicSingularLocus Y.obj)
    (V : Opens X.obj.left) (T : Opens Y.obj.left) (hxV : x ∈ V) (hfxT : f.hom.left.base x ∈ T) :
    Nonempty (ThinWindow f x V T) := by
  obtain ⟨e,r,P,W,hWP,iS,s,hiS,hs,hV,hT,hsq,_,_⟩ :=
    exists_ambient_representation f x hsm V T hxV hfxT
  let p : P := ambientProjection e r P W hWP s.val
  let G : Set (ComplexModel e.dim) := Subtype.val '' (P : Set e.ambient)
  have hGo : IsOpen G := e.ambient.isOpen.isOpenMap_subtype_val _ P.isOpen
  have hpG : p.val.val ∈ G := ⟨p.val,p.property,rfl⟩
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hGo _ hpG
  let B : Opens (ComplexModel e.dim) := ⟨Metric.ball p.val.val ρ,Metric.isOpen_ball⟩
  have hB : B ≤ e.ambient := by
    intro u hu
    obtain ⟨v,_,hv⟩ := hball hu
    exact hv ▸ v.property
  have hBP (u : B) : Opens.inclusion hB u ∈ P := by
    obtain ⟨v,hvP,hv⟩ := hball u.property
    exact (Subtype.ext hv : v = Opens.inclusion hB u) ▸ hvP
  let eB := e.restrict B hB
  let c : eB.carrier := ⟨⟨p.val.val,Metric.mem_ball_self hρ⟩,s.property⟩
  have hcx : eB.toPoint c = f.hom.left.base x := by
    have hp := congrArg (fun a => a.hom.left.base s) hsq
    exact hp.symm.trans (congrArg f.hom.left.base hs)
  have hthin : interior eB.carrier = ∅ := by
    let : ConnectedSpace eB.ambient := by
      change ConnectedSpace B
      exact isConnected_iff_connectedSpace.mp
        ((convex_ball p.val.val ρ).isConnected (Metric.nonempty_ball.mpr hρ))
    by_contra hne
    have heq : eB.carrier = univ :=
      eB.analytic.eq_univ_of_interior_nonempty (Set.nonempty_iff_ne_empty.mpr hne)
    have hreg : RegularAtDim (n := eB.dim) eB.carrier c.val eB.dim := by
      simpa only [heq] using AnalyticIrreducibleComponents.regularAtDim_univ (n := eB.dim) c.val
    apply hsing
    refine ⟨eB.dim,?_⟩
    exact hcx ▸ (OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff Y eB c eB.dim).mpr hreg
  let F : W → ComplexModel e.dim := fun w => w.val.1.val
  have hF : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (e.dim+r)) 𝓘(ℂ,ComplexModel e.dim) ∞ F :=
    isSubmersion_val_comp (A := BlowupTowers.CMfd.of (n := e.dim) (ComplexModel e.dim))
      (B := BlowupTowers.CMfd.of (n := e.dim+r) W) e.ambient (window_projection_isSubmersion e r W)
  let Ω : Opens W := ⟨F ⁻¹' (B : Set (ComplexModel e.dim)),B.isOpen.preimage hF.contMDiff.continuous⟩
  let b : Ω → B := restrictedOpenMap
    (X := BlowupTowers.CMfd.of (n := e.dim) (ComplexModel e.dim))
    (Y := BlowupTowers.CMfd.of (n := e.dim+r) W) (f := F) Ω B (fun _ hx => hx)
  have hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (e.dim+r)) 𝓘(ℂ,ComplexModel e.dim) ∞ b :=
    restrictedOpenMap_isSubmersion
      (X := BlowupTowers.CMfd.of (n := e.dim) (ComplexModel e.dim))
      (Y := BlowupTowers.CMfd.of (n := e.dim+r) W) hF Ω B (fun _ hx => hx)
  let A := BlowupTowers.CMfd.of (n := e.dim+r) Ω
  let Z := inverseSpace eB A b hb
  let jraw : Z.obj.left ⟶ (windowSpace e r W).obj.left :=
    actualOpenSubspaceMap (n := e.dim+r) (windowCarrier e r W) Ω
  let j : Z ⟶ windowSpace e r W := ObjectProperty.homMk (Over.homMk jraw
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)))
  have hj : LocallyRingedSpace.IsOpenImmersion j.hom.left :=
    actualOpenSubspaceMap_isOpenImmersion (windowCarrier e r W) Ω
  let i := j ≫ iS
  let s' : Z.obj.left := ⟨⟨s.val,Metric.mem_ball_self hρ⟩,s.property⟩
  have hsmall : jraw ≫ (windowFirst e r W).hom.left = (inverseProjection eB A b hb).hom.left := by
    change jraw ≫ (actualSubspaceMap (windowProjection_holomorphic e r W) (fun _ hx => hx) ≫ e.map) =
      actualSubspaceMap hb.contMDiff (fun _ hx => hx) ≫
        (e.restrictModelMapWith B hB (e.restrictCarrier B hB) (fun _ => Iff.rfl) ≫ e.map)
    have hl := actualSubspaceMap_comp (n := e.dim+r) (m := e.dim+r) (p := e.dim)
      (C := b ⁻¹' eB.carrier) (D := windowCarrier e r W) (E := e.carrier)
      (f := (Subtype.val : Ω → W)) (g := windowProjection e r W)
      contMDiff_subtype_val (windowProjection_holomorphic e r W) (fun _ hx => hx) (fun _ hx => hx)
    have hr := actualSubspaceMap_comp (n := e.dim+r) (m := e.dim) (p := e.dim)
      (C := b ⁻¹' eB.carrier) (D := eB.carrier) (E := e.carrier)
      (f := b) (g := Opens.inclusion hB) hb.contMDiff (contMDiff_inclusion hB)
      (fun _ hx => hx) (fun _ hx => hx)
    have hmid : jraw ≫ actualSubspaceMap (windowProjection_holomorphic e r W) (fun _ hx => hx) =
        actualSubspaceMap (C := b ⁻¹' eB.carrier) (D := eB.carrier) hb.contMDiff (fun _ hx => hx) ≫
          actualSubspaceMap (C := eB.carrier) (D := e.carrier) (contMDiff_inclusion hB) (fun _ hx => hx) :=
      hl.symm.trans hr
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ e.map) hmid).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun a => actualSubspaceMap hb.contMDiff (fun _ hx => hx) ≫ (a ≫ e.map))
            (restrictModelMap_eq e B hB).symm)))
  have hsq' : i ≫ f = inverseProjection eB A b hb := by
    have horig : iS ≫ f = windowFirst e r W := hsq.trans (nativeProjection_square e r P W hWP)
    change (j ≫ iS) ≫ f = _
    rw [Category.assoc,horig]
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hsmall
  refine ⟨⟨eB,e.dim+r,A,b,hb,i,s',hthin,?_,?_,hsq',?_,?_⟩⟩
  · exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ j.hom.left hj iS.hom.left hiS
  · exact hs
  · rintro _ ⟨z,rfl⟩
    exact hV ⟨j.hom.left.base z,rfl⟩
  · rintro _ ⟨z,rfl⟩
    let pz : targetCarrier e P := ⟨⟨Opens.inclusion hB z.val,hBP z.val⟩,z.property⟩
    exact hT ⟨pz,rfl⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothThinWindow
