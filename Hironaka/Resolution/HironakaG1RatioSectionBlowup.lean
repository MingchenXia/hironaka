import Hironaka.Resolution.HironakaG1RatioBlockUnpadding
import Hironaka.Resolution.HironakaG1ControlledCarrierRestriction
import Hironaka.Resolution.HironakaActualNativeSectionFiniteHistory

/-! A compatible one-step blowup on an actual section and its padded ambient. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1RatioSectionBlowup
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealOpenBiholomorphism RestrictLeCalculus CoefficientIdealRestriction RelativePrincipalizationSpan NormalCrossings RestrictedIdealWeight
  HironakaG1ControlledCarrierRestriction HironakaActualNativeSectionFiniteHistory
  HironakaSmoothSubmersionCoefficientIdeals BlowupStrictSubmanifold ResolutionDriver

private theorem interior_image_subtype_eq_empty {X : Type} [TopologicalSpace X]
    {W : Set X} (D : Set W) (hD : interior D = ∅) :
    interior ((Subtype.val : W → X) '' D) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨y,hy,rfl⟩ := interior_subset hx
  have hi : y ∈ interior D := by
    apply interior_maximal _ (isOpen_interior.preimage continuous_subtype_val) hx
    intro z hz
    obtain ⟨w,hw,he⟩ := interior_subset hz
    exact (Subtype.ext he) ▸ hw
  rw [hD] at hi
  exact hi

set_option maxHeartbeats 1000000 in
/-- Construct the genuine ambient blowup of the image centre and the genuine
native blowup of the original centre. The supported ambient record is the
literal carrier restriction of the padded record. Its whole transformed
section record agrees with the native transform, and its controlled ideal
agrees with that of the padded transform along the strict supported carrier. -/
theorem exists_native_and_padded_section_blowup {n k : ℕ} {X : CMfd.{0} n}
    (hn : 0 < n) (hk : k ≤ n) (P : MarkedIdeal n X) (hP : P.IsWellFormed)
    {W : Set X} (hWc : IsClosed W) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    (hTr : IsTransverse n W P.E)
    (hS : (withN P (P.N ∩ W)).IsWellFormed)
    (D : Set (nativeManifold hk W hW)) (hD : IsClosedSubmanifold k D)
    (hInt : interior D = ∅)
    (hCentre : P.IsAdmissibleCentre ((Subtype.val : W → X) '' D)) :
    ∃ (Y : CMfd.{0} n) (π : Y → X)
      (hπ : IsBlowupAlong n ((Subtype.val : W → X) '' D) π),
      let C := (Subtype.val : W → X) '' D
      let V := geoStrictTransform π C W
      let hV := strictRegular hWc hW D π hπ
      let σ := nativeProjection hk hWc hW D π hπ
      let S := withN P (P.N ∩ W)
      let S' := S.geoTransform C π
      IsBlowupAlong k D σ ∧
      (∀ z : V, π z.val = (σ z).val) ∧
      RestrictEquiv (withN (P.geoTransform C π) S'.N) S' ∧
      nativePullback hk V hV S' = (nativePullback hk W hW S).geoTransform D σ := by
  let C := (Subtype.val : W → X) '' D
  obtain ⟨Y,π,hπ⟩ := ResolutionDriver.exists_blowup C hCentre.1
    (interior_image_subtype_eq_empty D hInt)
  refine ⟨Y,π,hπ,?_⟩
  intro C V hV σ S S'
  have hSC : S.IsAdmissibleCentre C := by
    refine ⟨hCentre.1,?_ ,hCentre.2.2⟩
    rw [cosupp_withN]
    rintro _ ⟨z,hz,rfl⟩
    have h := hCentre.2.1 ⟨z,hz,rfl⟩
    exact ⟨⟨h.1,z.property⟩,fun g hg => (h.2 g hg).mono_set inter_subset_left⟩
  have hI : RestrictLe (P.N ∩ W) P.ideal P.ideal := restrictLe_refl hP.isCoherent
  obtain ⟨_,hF,hB,_⟩ := geoTransform_restricted_ideals P S hP hS
    inter_subset_left rfl hI hI hCentre hSC hπ
  have hσ := nativeProjection_genuine hk hWc hW D hD hInt π hπ
  let T := BlowupTower.step (.refl : BlowupTower X X) C π hπ
  let B := BlowupTower.step (.refl : BlowupTower (nativeManifold hk W hW) _) D σ hσ
  have hLift : Lift hk W hWc hW P.E T V isClosed_closure hV B :=
    Lift.step Lift.refl D hD hInt π hπ hCentre.2.2
  have hWhole := hLift.whole_records hn hP.isSNCDivisor hTr S rfl inter_subset_right
    (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hS.isCoherent h)
  exact ⟨hσ,fun _ => rfl,⟨rfl,rfl,rfl,hF,hB⟩,hWhole.symm⟩


/-- On the graph section, intersecting the padded carrier with that very
section preserves the complete intrinsic input record. -/
theorem nativePullback_withN_inter {n k : ℕ} {X : CMfd.{0} n} (hk : k ≤ n)
    {W : Set X} (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) (P : MarkedIdeal n X) :
    nativePullback hk W hW (withN P (P.N ∩ W)) = nativePullback hk W hW P := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · ext x
    exact ⟨fun h => h.1,fun h => ⟨h,x.property⟩⟩
  · rfl
  · rfl
  · rfl

open HironakaG1NormalGraphFlags HironakaG1IteratedNormalBlockIdeal HironakaBaseChange

/-- The literal graph support in any actual ratio cylinder open image. -/
def sectionSupport {n t : ℕ} {U : Opens (ComplexModel n)} {X : CMfd.{0} (n+t)}
    (e : X → blockOpen U t) (f : U → ComplexModel t) : Set X :=
  e ⁻¹' blockGraph f univ

theorem sectionSupport_closed {n t : ℕ} {U : Opens (ComplexModel n)} {X : CMfd.{0} (n+t)}
    {e : X → blockOpen U t} (he : IsOpenHoloEmbedding (n+t) e)
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f) :
    IsClosed (sectionSupport e f) :=
  (blockGraph_closed_submanifold hf
    (show IsClosedSubmanifold n (univ : Set U) from
      ⟨isClosed_univ, fun x _ => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩)).1.preimage
    he.continuous

theorem sectionSupport_regular {n t : ℕ} {U : Opens (ComplexModel n)} {X : CMfd.{0} (n+t)}
    {e : X → blockOpen U t} (he : IsOpenHoloEmbedding (n+t) e)
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f) :
    ∀ x ∈ sectionSupport e f, RegularAtDim (n := n+t) (sectionSupport e f) x n :=
  fun _x hx => he.regularAtDim_preimage
    (regularAtDim_blockGraph_of hf hx (AnalyticIrreducibleComponents.regularAtDim_univ _))

/-- The graph-supported carrier of the literal padded record is the
preimage of the graph over the original carrier, so it is closed smooth.
Its ordered boundary, ideal coherence and mark are inherited unchanged. -/
theorem blockGraph_supported_isWellFormed {n t : ℕ} {U : Opens (ComplexModel n)}
    {X : CMfd.{0} (n+t)} {e : X → blockOpen U t} (he : IsOpenHoloEmbedding (n+t) e)
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : Q.IsWellFormed) :
    let P := markedPullback (m := n+t) e (blockAmbientMarked f Q)
    let S := withN P (P.N ∩ sectionSupport e f)
    P.IsWellFormed → IsTransverse (n+t) S.N S.E → S.IsWellFormed := by
  intro P S hP hTr
  have hN : S.N = e ⁻¹' blockGraph f Q.N := by
    ext x
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,mem_univ _,h.2⟩⟩
  have hG := blockGraph_closed_submanifold hf hQ.isClosedSubmanifold_N
  refine ⟨?_,hP.isCoherent,hP.isSNCDivisor,hTr⟩
  rw [hN]
  refine ⟨hG.1.preimage he.continuous, fun x hx => ?_⟩
  obtain ⟨k,hk⟩ := hG.2 (e x) hx
  exact ⟨k,he.regularAtDim_preimage hk⟩

/-- One genuine blowup over the literal graph in a normalized reader
cylinder. The native record at the strict section is the whole transform
of the original section record. The two ambient transforms have the same
ordered boundary and agree as restricted marked ideals on that carrier. -/
theorem exists_blockGraph_section_blowup {n t : ℕ} {U : Opens (ComplexModel n)}
    {X : CMfd.{0} (n+t)} (hpos : 0 < n+t)
    {e : X → blockOpen U t} (he : IsOpenHoloEmbedding (n+t) e)
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : Q.IsWellFormed) :
    let P := markedPullback (m := n+t) e (blockAmbientMarked f Q)
    let W := sectionSupport e f
    let hW := sectionSupport_regular he hf
    ∀ (_hP : P.IsWellFormed) (_hTr : IsTransverse (n+t) W P.E)
    (_hTrN : IsTransverse (n+t) (P.N ∩ W) P.E)
    (D : Set (nativeManifold (Nat.le_add_right n t) W hW))
    (_hD : IsClosedSubmanifold n D) (_hInt : interior D = ∅)
    (_hCentre : P.IsAdmissibleCentre ((Subtype.val : W → X) '' D)),
    ∃ (Y : CMfd.{0} (n+t)) (π : Y → X)
      (hπ : IsBlowupAlong (n+t) ((Subtype.val : W → X) '' D) π),
      let C := (Subtype.val : W → X) '' D
      let V := geoStrictTransform π C W
      let hV := strictRegular (sectionSupport_closed he hf) hW D π hπ
      let σ := nativeProjection (Nat.le_add_right n t) (sectionSupport_closed he hf) hW D π hπ
      let S' := (withN P (P.N ∩ W)).geoTransform C π
      IsBlowupAlong n D σ ∧
      (∀ z : V, π z.val = (σ z).val) ∧
      RestrictEquiv (withN (P.geoTransform C π) S'.N) S' ∧
      nativePullback (Nat.le_add_right n t) V hV S' =
        (nativePullback (Nat.le_add_right n t) W hW P).geoTransform D σ := by
  intro P W hW hP hTr hTrN D hD hInt hCentre
  have hS := blockGraph_supported_isWellFormed he hf Q hQ hP hTrN
  obtain ⟨Y,π,hπ,hσ,hSquare,hEquiv,hRecord⟩ := exists_native_and_padded_section_blowup hpos
    (Nat.le_add_right n t) P hP (sectionSupport_closed he hf) hW hTr hS D hD hInt hCentre
  refine ⟨Y,π,hπ,hσ,hSquare,hEquiv,?_⟩
  rw [hRecord, nativePullback_withN_inter]

end
end Hironaka.HironakaG1RatioSectionBlowup
