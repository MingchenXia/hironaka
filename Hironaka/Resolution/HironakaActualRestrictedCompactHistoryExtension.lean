import Hironaka.Resolution.HironakaActualFiniteCompactHistoryExtension

/-! Original-source extension of a finite canonical history on a literal
initial good open. The initial map and all initial record identities are
constructed internally; the global source history and its numerical
comparison are also outputs. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualRestrictedCompactHistoryExtension
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism RelativePrincipalizationSpan
open HironakaActualGeneratedCurrentHistories HironakaActualAnchoredCurrentHistories
open HironakaActualFiniteCompactHistoryExtension HironakaActualRawRecordPullbacks
open HironakaActualGeneratedCurrentValues RestrictEmptyTower
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
variable {n : ℕ}

/-- The actual whole-open identification; its value map is literal inclusion. -/
def wholeTopComparison (X : CMfd.{u} n) : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
 CMfd.of (n := n) (⊤ : Opens X) := by
 refine ⟨⟨(fun x => ⟨x,mem_univ x⟩),Subtype.val,(fun _ => rfl),(fun x => Subtype.ext rfl)⟩,?_,?_⟩
 · exact BlowupRestrictOpen.contMDiff_opens_mk contMDiff_id (fun x => mem_univ x)
 · exact contMDiff_subtype_val

/-- A canonical compact-cosupport history on the LITERAL original good
open internally extends to one global actual original source history.
The complete actual original source Rq value, not a current restart,
agrees at every source point over that original open. -/
theorem exists_actual_restricted_compact_canonical_history_extension
 (hn : 0<n) (q : ℕ) {ι : Type v} (i₀ : ι) {X : CMfd.{u} n}
 (A : ι → MarkedIdeal n X)
 (hA : ∀i x g,(A i).ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) ((A i₀).ideal.mem x) x g → (A i₀).ideal.mem x g)
 (U₀ : Opens X)
 (hB : ∀i,(MarkedIdeal.pullback (Subtype.val : U₀ → X) (A i)).IsWellFormed)
 (hDomain : IsInvDomain q (MarkedIdeal.pullback (Subtype.val : U₀ → X) (A i₀)))
 (hK : IsCompact (MarkedIdeal.pullback (Subtype.val : U₀ → X) (A i₀)).cosupp)
 {Y' : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) U₀) Y')
 (hTarget : ∀i,IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U₀ → X) (A i)) T)
 (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : U₀ → X) (A i₀))
   ((CanonicalCentres.invFamily hn q).inv (MarkedIdeal.pullback (Subtype.val : U₀ → X) (A i₀))) T) :
 ∃(Y : CMfd.{u} n)(S : BlowupTower X Y)(V : Opens Y)
   (η : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
     CMfd.of (n := n) (⊤ : Opens Y')),
   (∀i,IsGeoTestTower (A i) S) ∧
   (∀i,Generated (A i) (MarkedIdeal.pullback (Subtype.val : U₀ → X) (A i)) S T V ⊤ η) ∧
   CentresOver ((Subtype.val : U₀ → X) ''
     (MarkedIdeal.pullback (Subtype.val : U₀ → X) (A i₀)).cosupp) S ∧
   CompactCentres S ∧ V=BlowupTowerTransforms.openPreimage S U₀ ∧
   ∀z : V,z.val∈(geoTransformAlong (A i₀) S).cosupp →
     (CanonicalCentres.invFamily hn q).inv (A i₀) S z.val=
       (CanonicalCentres.invFamily hn q).inv
         (MarkedIdeal.pullback (Subtype.val : U₀ → X) (A i₀)) T (η z).val := by
 let B : ι → MarkedIdeal n (CMfd.of (n := n) U₀) :=
   fun i => MarkedIdeal.pullback (Subtype.val : U₀ → X) (A i)
 let φ := wholeTopComparison (CMfd.of (n := n) U₀)
 have hInitial (i : ι) : MarkedIdeal.pullback (Subtype.val : U₀ → X) (A i)=
     MarkedIdeal.pullback φ (MarkedIdeal.pullback
       (Subtype.val : (⊤ : Opens (CMfd.of (n := n) U₀)) → U₀) (B i)) := by
   have hs := marked_pullback_comp_hhol
     (J := B i) (fun _ _ hg => hg.1)
     (a := (Subtype.val : (⊤ : Opens (CMfd.of (n := n) U₀)) → U₀))
     (b := φ) (d := (id : U₀ → U₀))
     contMDiff_subtype_val φ.contMDiff (fun _ => rfl)
   exact (hs.trans (ContactCanonicalAlong.pullback_id (B i) (hB i).isCoherent)).symm
 obtain ⟨Y,S,V,η,hTest,H,_hAnchor,hOver,hCompact,hWindow⟩ :=
   exists_actual_finite_compact_history_extension i₀ A B hA hB hDomain hK U₀ φ hInitial T hTarget
 refine ⟨Y,S,V,η,hTest,H,hOver,hCompact,hWindow,?_⟩
 intro z hz
 exact actual_family_current_values hn q (A i₀) (B i₀) (hA i₀) hAc hDomain S T V ⊤ η
   (H i₀) hcan z hz

end
end Hironaka.HironakaActualRestrictedCompactHistoryExtension
