import Hironaka.Analytic.Unibranch.OriginalNativeHSCompactShadowWindows
import Hironaka.Analytic.Unibranch.OriginalNativeHSPhaseHistory
import Hironaka.Analytic.Unibranch.OriginalNativeCentreLocalClosedness

/-! Actual attained original invariant level and genuine compatible local
centres near a compact native shadow. All powers/transport/level/good
opens are constructed internally; no global bound or centre packet.
Blueprint FIRST: original-native-shadow-invariant-centre.tex.
The native blowup consumer and dynamic shrinking phase are separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeShadowInvariantCentre
noncomputable section
open Hironaka Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11VanishingWindows HironakaG11VanishingPrincipalization HironakaG11PresWindows
  HironakaG11PresReduction HironakaG11HSPhaseInduction HironakaG11StrictTransformTowers
  HironakaG11CompatibleCanonicalTowers HironakaG11CanonicalFirstStep HironakaG11CompatibleLevelSets
  HironakaG11CompatibleAnalyticCover OriginalNativeHSCompactShadowWindows
  HironakaActualPowerBoundaryExponents HironakaG8LocalHistory ResolutionInvariantOrder
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSeq CanonicalCentres
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain)

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left} (M : Maximum X K) (hK : IsCompact K)
local notation "H" => originalStalkHS X M.point
local notation "n" => H 1 - 1

def commonMark : ℕ := by
  letI : Fintype (M.windows hK).ι := Fintype.ofFinite (M.windows hK).ι
  exact ∏ i, ((M.windows hK).record i).d

def exponent (i : (M.windows hK).ι) : ℕ := commonMark M hK / ((M.windows hK).record i).d

def record (i : (M.windows hK).ι) : MarkedIdeal n (Amb (M.windows hK).window i) := powerMarked ((M.windows hK).record i) (exponent M hK i)

theorem exponent_pos (i : (M.windows hK).ι) : 1 ≤ exponent M hK i := by
  let : Fintype (M.windows hK).ι := Fintype.ofFinite (M.windows hK).ι
  have hp : 0 < commonMark M hK := HironakaG11InvCommonMark.prodMark_pos
    (fun j => ((M.windows hK).record j).d) (fun j => ((M.windows hK).native j).1.one_le_d)
  exact HironakaG11InvCommonMark.one_le_div_of_dvd hp
    (HironakaG11InvCommonMark.dvd_prodMark (fun j => ((M.windows hK).record j).d) i)

theorem record_mark (i : (M.windows hK).ι) : (record M hK i).d = commonMark M hK := by
  let : Fintype (M.windows hK).ι := Fintype.ofFinite (M.windows hK).ι
  exact HironakaG11InvCommonMark.powerMarked_div_d ((M.windows hK).record i)
    (HironakaG11InvCommonMark.dvd_prodMark (fun j => ((M.windows hK).record j).d) i)

theorem record_hs (i : (M.windows hK).ι) : IsHSWindowRecord ((M.windows hK).window i) (record M hK i) H :=
  ((M.windows hK).native i).isHSWindowRecord.powerMarked (exponent_pos M hK i)

theorem domain (i : (M.windows hK).ι) : IsInvDomain n (record M hK i) := (record_hs M hK i).1

def invariant := OriginalNativeHSPhaseHistory.originalInvariant n

theorem presentation (i : (M.windows hK).ι) :
    HSPresentation (invariant M).toResolutionInvariant ((M.windows hK).window i) (record M hK i) H :=
  (record_hs M hK i).hsPresentation (invariant M).toResolutionInvariant

theorem transport : RecordsTransport (invariant M).toResolutionInvariant (record M hK) (mapAdm (M.windows hK).window) :=
  recordsTransport_of_native HironakaG11PresLineStable.nativeLineStability (invariant M) (M.windows hK).window (M.windows hK).record H
    (M.windows hK).native (exponent M hK) (exponent_pos M hK)
    (fun i j => (record_mark M hK i).trans (record_mark M hK j).symm)

theorem cosupp_subset (i : (M.windows hK).ι) : (record M hK i).cosupp ⊆ ((M.windows hK).window i).carrier :=
  HSPresentation.cosupp_subset (presentation M hK) i

theorem cosupp_closed (i : (M.windows hK).ι) : IsClosed (record M hK i).cosupp :=
  GiraudAlong.isClosed_cosupport_along (domain M hK i).isWellFormed.isCoherent
    (domain M hK i).isWellFormed.isClosedSubmanifold_N _

theorem cosupp_mem_iff (i : (M.windows hK).ι) (c : ((M.windows hK).window i).carrier) :
    c.val ∈ (record M hK i).cosupp ↔ originalStalkHS X (((M.windows hK).window i).toLocalEmbedding.toPoint c) = H :=
  HSPresentation.mem_cosupp_iff (presentation M hK) i c

theorem cosupp_image_threshold (i : (M.windows hK).ι) (c : ((M.windows hK).window i).carrier)
    (hc : c.val ∈ (record M hK i).cosupp) : ((M.windows hK).window i).toLocalEmbedding.toPoint c ∈ M.threshold := by
  have hHS := (cosupp_mem_iff M hK i c).mp hc
  have hs : ((M.windows hK).window i).toLocalEmbedding.toPoint c ∈ intrinsicSingularLocus X.obj := by
    have h := ((presentation M hK i BlowupTower.refl trivial).2 ((M.windows hK).window i).analytic c).2.2 hc
    have h2 : c ∈ (EmbeddedBlowupOverlap.chartMorphism ((M.windows hK).window i).toLocalEmbedding).hom.left.base ⁻¹'
        intrinsicSingularLocus X.obj := by
      rw [HironakaG11CompatibleAnalyticCover.preimage_intrinsicSingularLocus_of_isOpenImmersion
        (EmbeddedBlowupOverlap.chartMorphism ((M.windows hK).window i).toLocalEmbedding) ((M.windows hK).window i).isOpenImmersion]
      exact h
    exact h2
  exact ⟨hs, fun ℓ => (congrFun hHS ℓ).ge⟩

def value (i : (M.windows hK).ι) (y : ((M.windows hK).window i).ambient) : ValTy n :=
  (invariant M).toResolutionInvariant.inv (record M hK i) BlowupTower.refl y

theorem value_transport (i j : (M.windows hK).ι) (c : ((M.windows hK).window i).carrier) (c' : ((M.windows hK).window j).carrier)
    (heq : ((M.windows hK).window j).toLocalEmbedding.toPoint c' = ((M.windows hK).window i).toLocalEmbedding.toPoint c)
    (hc : c.val ∈ (record M hK i).cosupp) :
    c'.val ∈ (record M hK j).cosupp ∧ value M hK j c'.val = value M hK i c.val :=
  first_transport (adm_exists_map (M.windows hK).window) (transport M hK) i j c c' heq hc

def piece (i : (M.windows hK).ι) : Set ((M.windows hK).window i).carrier :=
  (Subtype.val : ((M.windows hK).window i).carrier → ((M.windows hK).window i).ambient) ⁻¹'
    ((record M hK i).cosupp ∩ (M.windows hK).footprint i) ∩ ((M.windows hK).window i).toLocalEmbedding.toPoint ⁻¹' K

theorem piece_compact (i : (M.windows hK).ι) : IsCompact (piece M hK i) := by
  let : T2Space X.obj.left := X.property.1
  have hp : IsCompact ((Subtype.val : ((M.windows hK).window i).carrier → ((M.windows hK).window i).ambient) ⁻¹'
      ((record M hK i).cosupp ∩ (M.windows hK).footprint i)) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage'
      (((M.windows hK).footprint_compact i).inter_left (cosupp_closed M hK i))
      (fun y hy => ⟨⟨y, cosupp_subset M hK i hy.1⟩, rfl⟩)
  exact hp.inter_right (hK.isClosed.preimage ((M.windows hK).window i).toLocalEmbedding.isOpenEmbedding_toPoint.continuous)

theorem piece_maximum (i : (M.windows hK).ι) (hne : (piece M hK i).Nonempty) :
    (ResolutionDriver.maxLocus (fun c : ((M.windows hK).window i).carrier => value M hK i c.val) (piece M hK i)).Nonempty := by
  have hu := (invariant M).toResolutionInvariant.isInvValue.usc (record M hK i) (domain M hK i)
    BlowupTower.refl trivial
  have huc : IsInvUSCOn (fun c : ((M.windows hK).window i).carrier => value M hK i c.val) (piece M hK i) :=
    (hu.comp continuous_subtype_val).mono (fun c hc => hc.1.1)
  obtain ⟨c, hc, hm⟩ := huc.exists_isMaxOn (piece_compact M hK i) hne
  exact ⟨c, hc, hm⟩

theorem pieces_nonempty : ∃ i, (piece M hK i).Nonempty := by
  obtain ⟨i, c, hcF, hc⟩ := mem_iUnion.mp ((M.windows hK).cover M.point_mem_shadow)
  have hcQ : c.val ∈ (record M hK i).cosupp := (cosupp_mem_iff M hK i c).mpr (by rw [hc])
  exact ⟨i, c, ⟨⟨hcQ, interior_subset hcF⟩, by
    change ((M.windows hK).window i).toLocalEmbedding.toPoint c ∈ K
    rw [hc]
    exact M.in_compact⟩⟩

theorem exists_level : ∃ l : ValTy n,
    (∀ i, ∀ c ∈ piece M hK i, value M hK i c.val ≤ l) ∧
      ∃ i, ∃ c ∈ piece M hK i, value M hK i c.val = l :=
  exists_global_max (fun i (c : ((M.windows hK).window i).carrier) => value M hK i c.val)
    (piece_maximum M hK) (pieces_nonempty M hK)

def level : ValTy n := (exists_level M hK).choose

theorem level_bound_piece (i : (M.windows hK).ι) (c : ((M.windows hK).window i).carrier) (hc : c ∈ piece M hK i) :
    value M hK i c.val ≤ level M hK := (exists_level M hK).choose_spec.1 i c hc

theorem level_attained : ∃ i, ∃ c ∈ piece M hK i, value M hK i c.val = level M hK :=
  (exists_level M hK).choose_spec.2

theorem level_bounds_shadow (i : (M.windows hK).ι) (c : ((M.windows hK).window i).carrier)
    (hc : c.val ∈ (record M hK i).cosupp) (hcK : ((M.windows hK).window i).toLocalEmbedding.toPoint c ∈ K) :
    value M hK i c.val ≤ level M hK := by
  obtain ⟨j, c', hcF, heq⟩ := mem_iUnion.mp
    ((M.windows hK).cover ⟨hcK, cosupp_image_threshold M hK i c hc⟩)
  obtain ⟨hc', hv⟩ := value_transport M hK i j c c' heq hc
  have hp : c' ∈ piece M hK j := ⟨⟨hc', interior_subset hcF⟩, by
    change ((M.windows hK).window j).toLocalEmbedding.toPoint c' ∈ K
    rw [heq]
    exact hcK⟩
  exact hv ▸ level_bound_piece M hK j c' hp

def goodOpen (i : (M.windows hK).ι) : Opens ((M.windows hK).window i).ambient :=
  ⟨interior {y | y ∉ (record M hK i).cosupp ∨ value M hK i y ≤ level M hK}, isOpen_interior⟩

theorem goodOpen_bounds (i : (M.windows hK).ι) (y : ((M.windows hK).window i).ambient) (hy : y ∈ goodOpen M hK i)
    (hc : y ∈ (record M hK i).cosupp) : value M hK i y ≤ level M hK :=
  (interior_subset hy).resolve_left (fun h => h hc)

theorem goodOpen_contains_shadow (i : (M.windows hK).ι) (c : ((M.windows hK).window i).carrier)
    (hcK : ((M.windows hK).window i).toLocalEmbedding.toPoint c ∈ K) : c.val ∈ goodOpen M hK i := by
  classical
  apply mem_interior_iff_mem_nhds.mpr
  by_cases hc : c.val ∈ (record M hK i).cosupp
  · have hu := (invariant M).toResolutionInvariant.isInvValue.usc (record M hK i) (domain M hK i)
      BlowupTower.refl trivial c.val hc
    filter_upwards [hu] with y hy
    by_cases hyc : y ∈ (record M hK i).cosupp
    · exact Or.inr ((hy hyc).trans (level_bounds_shadow M hK i c hc hcK))
    · exact Or.inl hyc
  · exact mem_of_superset ((cosupp_closed M hK i).isOpen_compl.mem_nhds hc) (fun _ hy => Or.inl hy)

theorem centre_admissible (i : (M.windows hK).ι) :
    (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : goodOpen M hK i → ((M.windows hK).window i).ambient)
      (record M hK i)).IsAdmissibleCentre
      ((Subtype.val : goodOpen M hK i → ((M.windows hK).window i).ambient) ⁻¹'
        {y | y ∈ (record M hK i).cosupp ∧ value M hK i y = level M hK}) :=
  (invariant M).toResolutionInvariant.isInvValue.admissible (record M hK i) (domain M hK i)
    BlowupTower.refl trivial (goodOpen M hK i) (level M hK)
    (fun y hy hyO => goodOpen_bounds M hK i y hyO hy)

def centres : LocalSmoothCentres X (M.windows hK).ι where
  emb i := ((M.windows hK).window i).toLocalEmbedding
  window i := goodOpen M hK i
  centre i := (Subtype.val : goodOpen M hK i → ((M.windows hK).window i).ambient) ⁻¹'
    {y | y ∈ (record M hK i).cosupp ∧ value M hK i y = level M hK}
  isClosedSubmanifold i := (centre_admissible M hK i).1
  centre_subset i := fun _ hc => cosupp_subset M hK i hc.1

theorem centres_compatible : (centres M hK).Compatible := by
  intro i j c c' heq hc
  have ht := value_transport M hK i j ⟨c.val.val, c.property⟩ ⟨c'.val.val, c'.property⟩ heq.symm hc.1
  exact ⟨ht.1, ht.2.trans hc.2⟩

theorem support_threshold : (centres M hK).support ⊆ M.threshold := by
  intro x hx
  obtain ⟨i, c, hc, hcx⟩ := (centres M hK).mem_support.mp hx
  have h := cosupp_image_threshold M hK i ⟨c.val.val, c.property⟩ hc.1
  exact hcx ▸ h

theorem support_singular : (centres M hK).support ⊆ intrinsicSingularLocus X.obj :=
  fun _ hx => (support_threshold M hK hx).1

theorem shadow_covered : K ∩ M.threshold ⊆ OriginalNativeCentreLocalClosedness.coveredOpen (centres M hK) := by
  intro x hx
  obtain ⟨i, c, -, hcx⟩ := mem_iUnion.mp ((M.windows hK).cover hx)
  have hcK : ((M.windows hK).window i).toLocalEmbedding.toPoint c ∈ K := by rw [hcx]; exact hx.1
  let d : (centres M hK).windowCarrier i := ⟨⟨c.val, goodOpen_contains_shadow M hK i c hcK⟩, c.property⟩
  exact mem_iUnion.mpr ⟨i, d, hcx⟩

theorem centre_meets_shadow : (K ∩ (centres M hK).support).Nonempty := by
  obtain ⟨i, c, hc, hv⟩ := level_attained M hK
  let d : (centres M hK).windowCarrier i := ⟨⟨c.val, goodOpen_contains_shadow M hK i c hc.2⟩, c.property⟩
  exact ⟨((M.windows hK).window i).toLocalEmbedding.toPoint c, hc.2,
    (centres M hK).mem_support.mpr ⟨i, d, ⟨hc.1.1, hv⟩, rfl⟩⟩

theorem exists_original_centres (X : SourceReducedComplexSpace) (K : Set X.obj.left)
    (hK : IsCompact K) (hne : (K ∩ intrinsicSingularLocus X.obj).Nonempty) :
    ∃ M : Maximum X K, (centres M hK).Compatible ∧
      (centres M hK).support ⊆ intrinsicSingularLocus X.obj ∧
      (K ∩ M.threshold ⊆ OriginalNativeCentreLocalClosedness.coveredOpen (centres M hK)) ∧
      (K ∩ (centres M hK).support).Nonempty := by
  let M := maximum X K hK hne
  exact ⟨M, centres_compatible M hK, support_singular M hK, shadow_covered M hK, centre_meets_shadow M hK⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeShadowInvariantCentre
