import Hironaka.Resolution.HironakaG1NativeCrossingExactRatio
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
import Hironaka.Resolution.HironakaG8CommonMarkRecoding

/-! The literal crossing yields unequal legitimate marks and matching normalized histories. -/
set_option autoImplicit false
open Set TopologicalSpace

namespace Hironaka.HironakaG1CrossingUnequalPowerHistory
noncomputable section

open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres ResolutionDriver DivisorExponentAlong
  HironakaActualPowerBoundaryExponents HironakaActualOriginalPowerTransform
  HironakaG8DomainExponents HironakaG8LocalPower HironakaG8LocalHistory
  HironakaG1OriginalUnequalMarkCanonical HironakaG11InvBMClass
  HironakaG1NativeCrossingGeometry HironakaG1NativeCrossingExactRatio HironakaBaseChange

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- Every controlled prefix of a positive whole power has the corresponding
scaled exponent for any actual ambient subset. The transformed record keeps
the entire chronological boundary and cosupport. -/
theorem powered_history_boundary (P : MarkedIdeal n X) (hP : IsInvDomain n P)
    (r : ℕ) (hr : 1 ≤ r) (T : BlowupTower X Y) (hT : IsGeoTestTower P T) :
    let A := geoTransformAlong P T
    let B := geoTransformAlong (powerMarked P r) T
    IsGeoTestTower (powerMarked P r) T ∧ B.E = A.E ∧ B.cosupp = A.cosupp ∧
      B.d = P.d * r ∧ ∀ H : Set Y, ∀ y : Y,
        divExpAlong n B.N B.ideal H y = r * divExpAlong n A.N A.ideal H y := by
  intro A B
  obtain ⟨ht,hEq⟩ := original_power_transform P hP r hr T hT
  have hA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hP T hT
  refine ⟨ht,hEq.E_eq,hEq.cosupp_eq.trans (powerMarked_cosupp A hA hr),?_,?_⟩
  · change (geoTransformAlong (powerMarked P r) T).d = P.d * r
    rw [d_geoTransformAlong]
    rfl
  · intro H y
    refine (divExpAlong_eq_of_restrictEquiv hEq H y).trans ?_
    exact divExpAlong_idealPow hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent hr y

/-- Two independent positive power choices give the same normalized value at
every endpoint and every literal boundary position of a common controlled history. -/
theorem normalized_powered_history_boundary (P : MarkedIdeal n X) (hP : IsInvDomain n P)
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (T : BlowupTower X Y) (hT : IsGeoTestTower P T) :
    let A := geoTransformAlong (powerMarked P r) T
    let B := geoTransformAlong (powerMarked P s) T
    A.E = B.E ∧ A.cosupp = B.cosupp ∧
      ∀ (H : Set Y) (y : Y),
        B.d * divExpAlong n A.N A.ideal H y =
          A.d * divExpAlong n B.N B.ideal H y := by
  intro A B
  obtain ⟨_,hAE,hAC,hAd,hAr⟩ := powered_history_boundary P hP r hr T hT
  obtain ⟨_,hBE,hBC,hBd,hBs⟩ := powered_history_boundary P hP s hs T hT
  refine ⟨hAE.trans hBE.symm,hAC.trans hBC.symm,fun H y => ?_⟩
  change (geoTransformAlong (powerMarked P s) T).d * _ =
    (geoTransformAlong (powerMarked P r) T).d * _
  rw [hAd,hBd,hAr H y,hBs H y]
  ac_rfl

/-- The full invariant ordering on actual endpoint points of a canonical
history is shared by two positive powers, including nonempty source boundaries. -/
theorem powered_history_canonical_order (P : MarkedIdeal n X) (hP : IsInvDomain n P)
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (T : BlowupTower X Y)
    (hCan : IsCanonical P ((canonicalInvariant n).inv P) T)
    (x y : Y) (hx : x ∈ (geoTransformAlong P T).cosupp) (hy : y ∈ (geoTransformAlong P T).cosupp) :
    let A := powerMarked P r
    let B := powerMarked P s
    ((canonicalInvariant n).inv A T x < (canonicalInvariant n).inv A T y ↔
      (canonicalInvariant n).inv B T x < (canonicalInvariant n).inv B T y) := by
  intro A B
  have hCompare (u : ℕ) (hu : 1 ≤ u) :
      ((canonicalInvariant n).inv P T x < (canonicalInvariant n).inv P T y ↔
        (canonicalInvariant n).inv (powerMarked P u) T x <
          (canonicalInvariant n).inv (powerMarked P u) T y) := by
    have hL := locEquiv_powerMarked (κ := Kinds.wp) rfl P hP hu
    have hQ := powerMarked_isInvDomain P hP hu
    have hCQ := (canonicalInvariant_isCanonical_power_iff P hP u hu T).mp hCan
    have hExp : ∀ H ∈ P.E, ∀ z ∈ P.cosupp, z ∈ H →
        (powerMarked P u).d * divExpAlong n P.N P.ideal H z =
          P.d * divExpAlong n (powerMarked P u).N (powerMarked P u).ideal H z := by
      intro H _ z _ _
      change (P.d*u) * divExpAlong n P.N P.ideal H z =
        P.d * divExpAlong n P.N (IdealWeightPowers.idealPow P.ideal u) H z
      rw [divExpAlong_idealPow hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent hu,
        Nat.mul_assoc]
    exact canonicalTwoPairCuts_canonicalInvariant n
      P (powerMarked P u) P (powerMarked P u) hP hQ hP hQ
      hL (SameCarrierDim.of_N_eq rfl) hExp hL (SameCarrierDim.of_N_eq rfl) hExp
      rfl rfl trivial trivial trivial trivial T T hCan hCQ hCan hCQ x hx y hy
  exact (hCompare r hr).symm.trans (hCompare s hs)

/-- On the actual initial analytic crossing, independently chosen distinct
positive powers give genuine unequal marks with the same submark ratio and
compare on all common controlled and canonical histories. -/
theorem exists_crossing_unequal_power_histories {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : r ≠ s) :
    ∃ (X : CMfd.{0} 2) (ι : X → M) (P : MarkedIdeal 2 X) (x : X),
      IsOpenHoloEmbedding 2 ι ∧ ι x = origin ∧ IsInvDomain 2 P ∧ x ∈ P.cosupp ∧
      let A := powerMarked P r
      let B := powerMarked P s
      A.E = [ι ⁻¹' axis 0] ∧ B.E = A.E ∧ A.d = 2*r ∧ B.d = 2*s ∧ A.d ≠ B.d ∧
      divExpAlong 2 A.N A.ideal (ι ⁻¹' axis 0) x = r ∧
      divExpAlong 2 B.N B.ideal (ι ⁻¹' axis 0) x = s ∧
      LocWPEquiv A B ∧
      ∀ {Y : CMfd.{0} 2} (T : BlowupTower X Y),
        (IsCanonical A ((canonicalInvariant 2).inv A) T ↔ IsCanonical B ((canonicalInvariant 2).inv B) T) ∧
        (IsGeoTestTower P T →
          let U := geoTransformAlong A T
          let V := geoTransformAlong B T
          U.E = V.E ∧ U.cosupp = V.cosupp ∧
          ∀ H : Set Y, ∀ y : Y, V.d * divExpAlong 2 U.N U.ideal H y =
            U.d * divExpAlong 2 V.N V.ideal H y) ∧
        (IsCanonical P ((canonicalInvariant 2).inv P) T →
          maxLocus ((canonicalInvariant 2).inv A T) (geoTransformAlong A T).cosupp =
            maxLocus ((canonicalInvariant 2).inv B T) (geoTransformAlong B T).cosupp ∧
          ∀ x y : Y, x ∈ (geoTransformAlong P T).cosupp → y ∈ (geoTransformAlong P T).cosupp →
            ((canonicalInvariant 2).inv A T x < (canonicalInvariant 2).inv A T y ↔
              (canonicalInvariant 2).inv B T x < (canonicalInvariant 2).inv B T y)) := by
  obtain ⟨X,ι,P,x,he,hx,hP,hN,hE,_,hxP,hd,hExp⟩ := exists_actual_crossing_initial_ratio
  let A := powerMarked P r
  let B := powerMarked P s
  have hLd (u : ℕ) : (powerMarked P u).d = 2*u := by
    change P.d*u = 2*u
    rw [hd]
  have hExp' (u : ℕ) (hu : 1 ≤ u) : divExpAlong 2 (powerMarked P u).N
      (powerMarked P u).ideal (ι ⁻¹' axis 0) x = u := by
    change divExpAlong 2 P.N (IdealWeightPowers.idealPow P.ideal u) (ι ⁻¹' axis 0) x = u
    rw [divExpAlong_idealPow hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent hu,
      hExp, Nat.mul_one]
  have hLr := locEquiv_powerMarked (κ := Kinds.wp) rfl P hP hr
  have hLs := locEquiv_powerMarked (κ := Kinds.wp) rfl P hP hs
  refine ⟨X,ι,P,x,he,hx,hP,hxP,hE,rfl,hLd r,hLd s,?_,hExp' r hr,hExp' s hs,hLr.symm.trans hLs,?_⟩
  · rw [hLd,hLd]
    omega
  · intro Y T
    refine ⟨(canonicalInvariant_isCanonical_power_iff P hP r hr T).symm.trans
      (canonicalInvariant_isCanonical_power_iff P hP s hs T),
      normalized_powered_history_boundary P hP hr hs T, ?_⟩
    intro hCan
    refine ⟨(canonicalInvariant_maxLocus_power P hP r hr T hCan).symm.trans
      (canonicalInvariant_maxLocus_power P hP s hs T hCan), ?_⟩
    intro x y hx hy
    exact powered_history_canonical_order P hP hr hs T hCan x y hx hy

#print axioms exists_crossing_unequal_power_histories

end
end Hironaka.HironakaG1CrossingUnequalPowerHistory
