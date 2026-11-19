import Hironaka.Analytic.Unibranch.OriginalNativeHSOpenPrefix

/-! Genuine next canonical ambient head after derived whole-fibre base
shrinking, for ANY retained original prefix. Blueprint FIRST:
original-native-hs-shrinking-successor.tex. A true shadow value bound
retains that shadow; no centre/next-history/phase certificate is input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSShrinkingSuccessor
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  OriginalNativeHSOpenPrefix ResolutionInvariantSeq CanonicalCentres
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

private abbrev invariant (ambientDim : ℕ) := (OriginalNativeHSPhaseHistory.originalInvariant ambientDim).toResolutionInvariant
variable {n : ℕ} (P : Input n) {Y : CMfd.{0} n} (T : BlowupTower P.ambient Y)
  (hT : IsCanonical (chosenRecord P) ((invariant n).inv (chosenRecord P)) T) (L : ValTy n)

include hT in
private theorem transformed_domain : IsInvDomain n (geoTransformAlong (chosenRecord P) T) :=
  InvDomainTowerAlong.isInvDomain_geoTransformAlong (chosen_domain P) T
    ((invariant n).isInvValue.isGeoTestTower_of_isCanonical (chosen_domain P) T hT)

include hT in
private theorem cosupp_closed : IsClosed (geoTransformAlong (chosenRecord P) T).cosupp :=
  GiraudAlong.isClosed_cosupport_along (transformed_domain P T hT).isWellFormed.isCoherent
    (transformed_domain P T hT).isWellFormed.isClosedSubmanifold_N _

def terminalGoodOpen : Opens Y :=
  ⟨interior {z | z ∉ (geoTransformAlong (chosenRecord P) T).cosupp ∨
      (invariant n).inv (chosenRecord P) T z ≤ L}, isOpen_interior⟩

include hT in
theorem contains_shadow_fibres (S : Set P.ambient)
    (hBound : ∀ z ∈ (geoTransformAlong (chosenRecord P) T).cosupp,
      T.proj z ∈ S → (invariant n).inv (chosenRecord P) T z ≤ L) :
    T.proj ⁻¹' S ⊆ terminalGoodOpen P T L := by
  classical
  intro z hz
  apply mem_interior_iff_mem_nhds.mpr
  by_cases hc : z ∈ (geoTransformAlong (chosenRecord P) T).cosupp
  · filter_upwards [(invariant n).isInvValue.usc _ (chosen_domain P) T hT z hc] with y hy
    by_cases hyc : y ∈ (geoTransformAlong (chosenRecord P) T).cosupp
    · exact Or.inr ((hy hyc).trans (hBound z hc hz))
    · exact Or.inl hyc
  · exact mem_of_superset ((cosupp_closed P T hT).isOpen_compl.mem_nhds hc) (fun _ hy => Or.inl hy)

/-- Actual base shrink, excluding the entire image of every bad terminal fibre point. -/
def baseOpen : Opens P.ambient :=
  ⟨(T.proj '' (terminalGoodOpen P T L : Set Y)ᶜ)ᶜ,
    ((HironakaLocalPrincipalization.isProperMap_proj T).isClosedMap _
      (terminalGoodOpen P T L).isOpen.isClosed_compl).isOpen_compl⟩

include hT in
theorem base_contains_shadow (S : Set P.ambient)
    (hBound : ∀ z ∈ (geoTransformAlong (chosenRecord P) T).cosupp,
      T.proj z ∈ S → (invariant n).inv (chosenRecord P) T z ≤ L) : S ⊆ baseOpen P T L := by
  rintro x hx ⟨z, hz, rfl⟩
  exact hz (contains_shadow_fibres P T hT L S hBound hx)

theorem preimage_base_subset : T.proj ⁻¹' (baseOpen P T L : Set P.ambient) ⊆ terminalGoodOpen P T L := by
  intro z hz
  by_contra hnot
  exact hz ⟨z, hnot, rfl⟩

theorem restricted_domain : IsInvDomain n (restrictedRecord P (baseOpen P T L)) :=
  InvDomainTowerAlong.isInvDomain_pullback_val _ (chosen_domain P)

include hT in
private theorem bound_restricted (z : openPreimage T (baseOpen P T L))
    (hz : z ∈ (geoTransformAlong (restrictedRecord P (baseOpen P T L)) (restrict (baseOpen P T L) T)).cosupp) :
    (invariant n).inv (restrictedRecord P (baseOpen P T L)) (restrict (baseOpen P T L) T) z ≤ L := by
  have he := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    (chosen_domain P).isWellFormed.isClosedSubmanifold_N (chosen_domain P).isWellFormed.isCoherent
    (baseOpen P T L) T ((invariant n).isInvValue.isGeoTestTower_of_isCanonical (chosen_domain P) T hT)
  have hzold := (Set.ext_iff.mp he z).mp hz
  have hzgood := preimage_base_subset P T L z.property
  have hv := (interior_subset hzgood).resolve_left (fun h => h hzold)
  exact (restricted_value P T hT (baseOpen P T L) z hzold).symm ▸ hv

def levelCentre : Set (openPreimage T (baseOpen P T L)) :=
  {z | z ∈ (geoTransformAlong (restrictedRecord P (baseOpen P T L)) (restrict (baseOpen P T L) T)).cosupp ∧
    (invariant n).inv (restrictedRecord P (baseOpen P T L)) (restrict (baseOpen P T L) T) z = L}

include hT in
theorem centre_max : levelCentre P T L = ∅ ∨ levelCentre P T L =
    ResolutionDriver.maxLocus ((invariant n).inv (restrictedRecord P (baseOpen P T L)) (restrict (baseOpen P T L) T))
      (geoTransformAlong (restrictedRecord P (baseOpen P T L)) (restrict (baseOpen P T L) T)).cosupp :=
  HironakaG11CompatibleLevelSets.levelSet_eq_empty_or_eq_maxLocus _ _ _ (bound_restricted P T hT L)

include hT in
theorem centre_admissible :
    (geoTransformAlong (restrictedRecord P (baseOpen P T L)) (restrict (baseOpen P T L) T)).IsAdmissibleCentre
      (levelCentre P T L) := by
  rcases centre_max P T hT L with h | h
  · rw [h]
    exact isAdmissibleCentre_empty _
  · rw [h]
    exact (invariant n).isInvValue.isAdmissibleCentre_maxLocus (restricted_domain P T L) _
      (restricted_canonical P T hT (baseOpen P T L))
      ((invariant n).isInvValue.isGeoTestTower_of_isCanonical (restricted_domain P T L) _
        (restricted_canonical P T hT (baseOpen P T L)))

include hT in
private theorem centre_interior : interior (levelCentre P T L) = ∅ := by
  rcases centre_max P T hT L with h | h
  · rw [h, interior_empty]
  · rw [h]
    exact ResolutionInvariantDriver.interior_maxLocus_eq_empty (restricted_domain P T L) _
      ((invariant n).isInvValue.isGeoTestTower_of_isCanonical (restricted_domain P T L) _
        (restricted_canonical P T hT (baseOpen P T L))) _

include hT in
private theorem ambient_exists : ∃ (Z : CMfd.{0} n) (p : Z → openPreimage T (baseOpen P T L)),
    IsBlowupAlong n (levelCentre P T L) p :=
  ResolutionDriver.exists_blowup (Y := CMfd.of (n := n) (openPreimage T (baseOpen P T L)))
    (levelCentre P T L) (centre_admissible P T hT L).1 (centre_interior P T hT L)

def ambient : CMfd.{0} n := (ambient_exists P T hT L).choose

def projection : ambient P T hT L → openPreimage T (baseOpen P T L) :=
  (ambient_exists P T hT L).choose_spec.choose

theorem isBlowup : IsBlowupAlong n (levelCentre P T L) (projection P T hT L) :=
  (ambient_exists P T hT L).choose_spec.choose_spec

def successor : BlowupTower (CMfd.of (n := n) (baseOpen P T L)) (ambient P T hT L) :=
  .step (restrict (baseOpen P T L) T) (levelCentre P T L) (projection P T hT L) (isBlowup P T hT L)

theorem canonical : IsCanonical (restrictedRecord P (baseOpen P T L))
    ((invariant n).inv (restrictedRecord P (baseOpen P T L))) (successor P T hT L) :=
  ⟨restricted_canonical P T hT (baseOpen P T L), centre_max P T hT L⟩

theorem length : (successor P T hT L).length = T.length + 1 := by
  change (restrict (baseOpen P T L) T).length + 1 = _
  rw [length_restrict]

theorem boundary : (geoTransformAlong (restrictedRecord P (baseOpen P T L)) (successor P T hT L)).E =
    (geoTransformAlong (restrictedRecord P (baseOpen P T L)) (restrict (baseOpen P T L) T)).E.map
      (BlowupStrictSubmanifold.geoStrictTransform (projection P T hT L) (levelCentre P T L)) ++
        [(projection P T hT L) ⁻¹' levelCentre P T L] := rfl

theorem surviving_value_lt (z : ambient P T hT L)
    (hz : z ∈ (geoTransformAlong (restrictedRecord P (baseOpen P T L)) (successor P T hT L)).cosupp) :
    (invariant n).inv (restrictedRecord P (baseOpen P T L)) (successor P T hT L) z < L := by
  have htest := (invariant n).isInvValue.isGeoTestTower_of_isCanonical (restricted_domain P T L) _
    (canonical P T hT L)
  have hpz := StepOneWellFounded.proj_mem_cosupp_step
    (restricted_domain P T L).isWellFormed.isClosedSubmanifold_N (restricted_domain P T L).isWellFormed.isCoherent
    (restrict (baseOpen P T L) T) _ _ (isBlowup P T hT L) htest hz
  have hle := bound_restricted P T hT L _ hpz
  by_cases hc : projection P T hT L z ∈ levelCentre P T L
  · have hne : (levelCentre P T L).Nonempty := ⟨_, hc⟩
    exact ((invariant n).isInvValue.decrease _ (restricted_domain P T L) _ _ _ (isBlowup P T hT L)
      (restricted_canonical P T hT (baseOpen P T L)) hne
      ((centre_max P T hT L).resolve_left hne.ne_empty) z hz).1 hc |>.trans_le hle
  · have hlt : (invariant n).inv (restrictedRecord P (baseOpen P T L)) (restrict (baseOpen P T L) T)
        (projection P T hT L z) < L :=
      lt_of_le_of_ne hle (fun h => hc ⟨hpz, h⟩)
    have heq : (invariant n).inv (restrictedRecord P (baseOpen P T L)) (successor P T hT L) z =
        (invariant n).inv (restrictedRecord P (baseOpen P T L)) (restrict (baseOpen P T L) T)
          (projection P T hT L z) := by
      by_cases hne : (levelCentre P T L).Nonempty
      · exact ((invariant n).isInvValue.decrease _ (restricted_domain P T L) _ _ _ (isBlowup P T hT L)
          (restricted_canonical P T hT (baseOpen P T L)) hne
          ((centre_max P T hT L).resolve_left hne.ne_empty) z hz).2 hc
      · exact (invariant n).isInvValue.emptyStep _ (restricted_domain P T L) _ _ _ (isBlowup P T hT L)
          (not_nonempty_iff_eq_empty.mp hne) (restricted_canonical P T hT (baseOpen P T L)) z hz
    exact heq ▸ hlt

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSShrinkingSuccessor
