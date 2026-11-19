import Hironaka.Resolution.HironakaG4CertifiedSharpHistory
import Hironaka.Resolution.HironakaG4RetainedRankTowerIso

/-! Read a completed certified sharp history on one literal source open. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4CertifiedSharpSourceView
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdealTowerTransport MaxLocusLocal StepOneTangentChange HironakaG4RetainedRankTowerIso
  HironakaG4CertifiedSharpHistory HironakaG4RetainedPreparationTrace
  HironakaG4RetainedPreparationLowerHistory HironakaG4CompactRelativeSharpDimension
  HironakaG4OrderedRetainedDefectTrace HironakaG4OrderedProcessedMaskHistory
  HironakaG4RelativeOrderedProcessedFinish HironakaG4ProcessedMaskIncidenceOrder
  HironakaG34MaskFoldEquivariance HironakaActualProcessedAllMasksDrop HironakaG4SharpTerminalAtlas

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The literal root of the completed sharper-dimensional history, before
outer restrictions and physical source rebases. -/
structure FinishedSharpHistory {n : ℕ} (hn : 0 < n) (lower : SharpHistoryPredicate.{u} n) where
  base : CMfd.{u} n
  middle : CMfd.{u} n
  endpoint : CMfd.{u} n
  carrier : Set base
  boundary : List (Set base)
  geometry : NativeRetainedGeometry carrier boundary []
  headTower : BlowupTower base middle
  prepared : At carrier boundary boundary.length headTower
  equivariant : IsEquivariant carrier boundary headTower
  preparation : RetainedPreparationTrace hn carrier boundary []
    (originalRetainedPreparationPhases boundary.length) headTower
  lower_histories : usesLowerHistory lower preparation
  window : Opens base
  suffix : BlowupTower (CMfd.of (n := n) (openPreimage headTower window)) endpoint
  masks :
    let v := (Subtype.val : window → base)
    let E := boundary.map (v ⁻¹' ·)
    let e : Fin boundary.length ≃ Fin E.length := finCongr (List.length_map _).symm
    OrderedProcessedMaskHistory hn (v ⁻¹' carrier) E (restrict window headTower) (fun P => P.map e.toEmbedding)
      suffix (descendingMaskLabels (orderedMaskLevel boundary.length) boundary.length).reverse
  terminal : IsSharpTerminalTower ((Subtype.val : window → base) ⁻¹' carrier)
    (boundary.map ((Subtype.val : window → base) ⁻¹' ·)) ((restrict window headTower).append suffix)

variable {hn : 0 < n} {lower : SharpHistoryPredicate.{u} n}

abbrev FinishedSharpHistory.chart (R : FinishedSharpHistory hn lower) := CMfd.of (n := n) R.window
abbrev FinishedSharpHistory.tower (R : FinishedSharpHistory hn lower) : BlowupTower R.chart R.endpoint :=
  (restrict R.window R.headTower).append R.suffix

abbrev FinishedSharpHistory.carrierOn (R : FinishedSharpHistory hn lower) (U : Opens R.chart) : Set U :=
  (fun x : U => (x.val : R.window).val) ⁻¹' R.carrier

abbrev FinishedSharpHistory.boundaryOn (R : FinishedSharpHistory hn lower) (U : Opens R.chart) : List (Set U) :=
  (R.boundary.map ((Subtype.val : R.window → R.base) ⁻¹' ·)).map ((Subtype.val : U → R.chart) ⁻¹' ·)

private theorem exists_full_open_diffeo (A : CMfd.{u} n) (V : Opens A) (hV : ∀ a : A,a ∈ V) :
    ∃ e : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V,
      ∀ a : A,(e a).val = a := by
  have hTop : V = ⊤ := top_unique fun a _ => hV a
  subst V
  obtain ⟨U,e,he⟩ := isOpenHoloEmbedding_diffeomorph (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞)
  have hU : U = ⊤ := top_unique fun a _ => by
    have hPoint : a = (e a).val := he a
    rw [hPoint]
    exact (e a).property
  subst U
  exact ⟨e,fun a => (he a).symm⟩

private theorem exists_top_restriction_isTowerIso (T : BlowupTower X Y) :
    ∃ e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (⊤ : Opens X),
      (∀ x : X,(e x).val = x) ∧
      ∃ η : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T ⊤),
        (∀ y : Y,(η y).val = y) ∧ IsTowerIso e T (restrict ⊤ T) η := by
  induction T with
  | refl =>
    obtain ⟨e,he⟩ := exists_full_open_diffeo X ⊤ (fun _ => trivial)
    exact ⟨e,he,e,he,.refl⟩
  | @step A Z T C π hπ ih =>
    obtain ⟨e,he,χ,hχ,hI⟩ := ih
    let V := openPreimage (.step T C π hπ) (⊤ : Opens X)
    obtain ⟨η,hη⟩ := exists_full_open_diffeo Z V (fun _ => trivial)
    refine ⟨e,he,η,hη,IsTowerIso.step hI _ _ η ?_ ?_⟩
    · intro z
      apply Subtype.ext
      change π (η z).val = (χ (π z)).val
      rw [hη,hχ]
    · ext z
      change (χ z).val ∈ C ↔ z ∈ C
      rw [hχ]

/-- A certified step is the physical restriction of one of its actual
finished roots, up to a biholomorphic presentation of that literal
source. The entire ordered input record pulls back by that same map. -/
theorem exists_finished_sharp_source_view {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
    (h : SharpHistoryStep hn (fun A B N I R => lower (X := A) (Y := B) N I R) W E T) :
    ∃ (R : FinishedSharpHistory hn lower) (U : Opens R.chart)
      (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
      (η : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R.tower U)),
      IsTowerIso e T (restrict U R.tower) η ∧
      let f : X → R.base := fun x => ((e x).val : R.window).val
      W = f ⁻¹' R.carrier ∧ E = R.boundary.map (f ⁻¹' ·) := by
  induction h with
  | @finished A B Z N I geometry P hP hEq prep hLower O S masks terminal =>
    let R : FinishedSharpHistory hn lower :=
      ⟨A,B,Z,N,I,geometry,P,hP,hEq,prep,hLower,O,S,masks,terminal⟩
    obtain ⟨e,he,η,_hη,hIso⟩ := exists_top_restriction_isTowerIso R.tower
    refine ⟨R,⊤,e,η,hIso,?_,?_⟩
    · ext x
      change x.val ∈ N ↔ ((e x).val : O).val ∈ N
      rw [he]
    · apply List.map_congr_left
      intro H _
      ext x
      change x.val ∈ H ↔ ((e x).val : O).val ∈ H
      rw [he]
  | @restrictOpen A B N I P D _ ih =>
    obtain ⟨R,U,e,η,hIso,hN,hE⟩ := ih
    let H : Opens U := ⟨e.symm ⁻¹' (D : Set A),D.isOpen.preimage e.symm.continuous⟩
    let V : Opens R.chart := ⟨(Subtype.val : U → R.chart) '' (H : Set U),U.isOpen.isOpenMap_subtype_val _ H.isOpen⟩
    have hVU : V ≤ U := by
      rintro _ ⟨x,_,rfl⟩
      exact x.property
    have hD (x : A) : x ∈ D ↔ e x ∈ nestedOpens U V := by
      change x ∈ D ↔ (e x).val ∈ V
      constructor
      · intro hx
        exact ⟨e x,by change e.symm (e x) ∈ D; rwa [e.symm_apply_apply],rfl⟩
      · rintro ⟨y,hy,heq⟩
        have hy' : y = e x := Subtype.ext heq
        subst y
        change e.symm (e x) ∈ D at hy
        rwa [e.symm_apply_apply] at hy
    let e' := (diffeoOpens e D (nestedOpens U V) hD).trans (nestedOpensDiffeo hVU)
    have hL := isTowerIso_restrictOpens hD hIso (isTowerIso_mem_openPreimage_iff hIso hD)
    have hI := hL.trans (isTowerIso_restrict_nestedOpens hVU R.tower)
    refine ⟨R,V,e',_,hI,?_,?_⟩
    · rw [hN]
      rfl
    · rw [hE,List.map_map]
      rfl
  | @rebase A A' B N I P φ _ ih =>
    obtain ⟨R,U,e,η,hIso,hN,hE⟩ := ih
    have hI := (transport_isTowerIso φ P).trans hIso
    refine ⟨R,U,φ.trans e,_,hI,?_,?_⟩
    · rw [hN]
      rfl
    · rw [hE,List.map_map]
      rfl

end
end Hironaka.HironakaG4CertifiedSharpSourceView
