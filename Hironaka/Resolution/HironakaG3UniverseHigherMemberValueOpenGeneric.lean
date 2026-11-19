import Hironaka.Resolution.HironakaG3UniverseMemberCanonicalIH
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseHigherMemberValueOpenGeneric
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue ResolutionInvariantSpec CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniverseOpenDiffeo G3UniverseLiftRestrict G3UniverseMemberLowerIH G3UniverseCanonicalIH
  InvDomainMemberRestriction
noncomputable section

/-- The actual positive-member lower values agree through any equal literal lifted mask. -/
theorem member_value_lift_of_open_eq {n r : ℕ} (hn : 0 < n) {X Y Z : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (T₀ : BlowupTower X Y)
    (hT₀ : IsGeoTestTower (barMarked M) T₀) (T₁ : BlowupTower Y Z) (z : liftCMfd.{u} Y)
    (hD : IsInvDomain r (originalLowerMember M T₀ z))
    (hcan : IsCanonical (originalLowerMember M T₀ z) ((invFamily.{0} hn r).inv (originalLowerMember M T₀ z))
      (restrict (maskA M T₀ ((liftDiffeomorph.{u} Y).symm z)) T₁))
    (hIH : CanonicalLiftValueIH.{u} hn r)
    (V : Opens (liftCMfd.{u} Y))
    (hV : V = preimageOpens (liftDiffeomorph.{u} Y).symm (maskA M T₀ ((liftDiffeomorph.{u} Y).symm z)))
    (y : Z) (hy : T₁.proj y ∈ maskA M T₀ ((liftDiffeomorph.{u} Y).symm z))
    (hyV : (liftTower.{u} T₁).proj ((liftDiffeomorph.{u} Z) y) ∈ V)
    (hcos : (⟨y,hy⟩ : openPreimage T₁ (maskA M T₀ ((liftDiffeomorph.{u} Y).symm z))) ∈
      (geoTransformAlong (originalLowerMember M T₀ z) (restrict (maskA M T₀ ((liftDiffeomorph.{u} Y).symm z)) T₁)).cosupp) :
    let J' := geoTransformAlong (barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T₀)
    let K' := memberRestrict J' (membersThrough J'.E
      (origMembers (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀)) z)
    (invFamily.{u} hn r).inv (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : V → liftCMfd.{u} Y) K')
      (restrict V (liftTower.{u} T₁)) ⟨(liftDiffeomorph.{u} Z) y,hyV⟩ =
      (invFamily.{0} hn r).inv (originalLowerMember M T₀ z)
        (restrict (maskA M T₀ ((liftDiffeomorph.{u} Y).symm z)) T₁) ⟨y,hy⟩ := by
  subst V
  let A := maskA M T₀ ((liftDiffeomorph.{u} Y).symm z)
  let p : openPreimage (liftTower.{u} T₁) (preimageOpens (liftDiffeomorph.{u} Y).symm A) :=
    ⟨(liftDiffeomorph.{u} Z) y,hyV⟩
  have hp : (liftDiffeomorph.{u} _).symm (lifted_restrictEndpoint T₁ A p) = (⟨y,hy⟩ : openPreimage T₁ A) := by
    apply Subtype.ext
    rfl
  have hv := member_lower_canonical_and_values_of_canonical_IH hn M hM T₀ hT₀ T₁ z hD hcan hIH
  have hvp := hv.2.2 p (by rw [hp]; exact hcos)
  rw [hp] at hvp
  exact hvp
/-- Member-value comparison with explicitly corresponding intermediate points. -/
theorem member_value_lift_of_point_eq {n r : ℕ} (hn : 0 < n) {X Y Z : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (T₀ : BlowupTower X Y)
    (hT₀ : IsGeoTestTower (barMarked M) T₀) (T₁ : BlowupTower Y Z) (a : Y) (z : liftCMfd.{u} Y)
    (hez : z = (liftDiffeomorph.{u} Y) a)
    (hD : IsInvDomain r (originalLowerMember M T₀ ((liftDiffeomorph.{u} Y) a)))
    (hcan : IsCanonical (originalLowerMember M T₀ ((liftDiffeomorph.{u} Y) a))
      ((invFamily.{0} hn r).inv (originalLowerMember M T₀ ((liftDiffeomorph.{u} Y) a))) (restrict (maskA M T₀ a) T₁))
    (hIH : CanonicalLiftValueIH.{u} hn r) (V : Opens (liftCMfd.{u} Y))
    (hV : V = maskA (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀) z)
    (y : Z) (hy : T₁.proj y ∈ maskA M T₀ a)
    (hyV : (liftTower.{u} T₁).proj ((liftDiffeomorph.{u} Z) y) ∈ V)
    (hcos : (⟨y,hy⟩ : openPreimage T₁ (maskA M T₀ a)) ∈
      (geoTransformAlong (originalLowerMember M T₀ ((liftDiffeomorph.{u} Y) a)) (restrict (maskA M T₀ a) T₁)).cosupp) :
    let J' := geoTransformAlong (barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T₀)
    let K' := memberRestrict J' (membersThrough J'.E
      (origMembers (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀)) z)
    (invFamily.{u} hn r).inv (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : V → liftCMfd.{u} Y) K')
      (restrict V (liftTower.{u} T₁)) ⟨(liftDiffeomorph.{u} Z) y,hyV⟩ =
      (invFamily.{0} hn r).inv (originalLowerMember M T₀ ((liftDiffeomorph.{u} Y) a))
        (restrict (maskA M T₀ a) T₁) ⟨y,hy⟩ := by
  subst z
  have hV' : V = preimageOpens (liftDiffeomorph.{u} Y).symm (maskA M T₀ a) := by
    rw [hV]
    simpa only [Diffeomorph.symm_apply_apply] using
      G3UniverseStepOneSpecialActual.maskA_liftTower M hM T₀ hT₀ ((liftDiffeomorph.{u} Y) a)
  exact member_value_lift_of_open_eq hn M hM T₀ hT₀ T₁ ((liftDiffeomorph.{u} Y) a) hD hcan hIH V hV' y hy hyV hcos

end
end Hironaka.G3UniverseHigherMemberValueOpenGeneric
