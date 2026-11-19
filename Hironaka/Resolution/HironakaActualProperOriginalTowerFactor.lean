import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen

/-!
# Original total tower factors on the actual proper carrier

Both restricted directions use the ORIGINAL ideal and marking, the native
TOTAL divisor of created births, and the actual controlled-test tower.
No ambient factor equality, nonzero/finite order, or positive mark is assumed.
Blueprint complete before source; all numerical Lean limits are unchanged.
-/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualProperOriginalTowerFactor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  RelativePrincipalizationSpan InvertibleIdealQuotient IdealWeightPowers
  GermIdealPullbackCalculus GermIdealTotalTransform BlowupControlledTransform
  BlowupExceptionalDivisor RestrictLeCalculus MarkedIdealOperationsAlong RestrictedIdealWeight

/-- The ORIGINAL whole pullback lies in the actual total birth factor times
its actual native current ideal, on the SAME proper current carrier. -/
theorem original_tower_factor_forward {n : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hN : IsClosedSubmanifold n M.N)
    (hI : M.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower M T →
      RestrictLe (M.geoTransformAlong T).N
        (GermIdeal.pullback (m := n) T.proj M.ideal)
        ((idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal M.d).mul
          (M.geoTransformAlong T).ideal)
  | _, .refl, _ => by
      rw [geoTransformAlong_refl, BlowupTower.proj_refl,
        BlowupTowerTransforms.exceptionalDivisor_refl_ideal, idealPow_unitIdeal,
        unitIdeal_mul hI, pullback_id hI]
      exact restrictLe_refl hI
  | _, .step T C π hπ, hT => by
      let J := M.geoTransformAlong T
      let W := (J.geoTransform C π).N
      let U := (J.geoTransform C π).ideal
      let F := idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal M.d
      let P := GermIdeal.pullback (m := n) π F
      let B := GermIdeal.pullback (m := n) π J.ideal
      let G := idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) M.d
      have hJ := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
        hN hI T hT.1
      have hJN : IsClosedSubmanifold n J.N := hJ.1
      have hJI : J.ideal.IsCoherent := hJ.2
      have hU : U.IsCoherent :=
        (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
          hN hI (.step T C π hπ) hT).2
      have hImage : ∀ y ∈ W, π y ∈ J.N := fun _ hy =>
        geoStrictTransform_subset_preimage hπ.contMDiff.continuous hJN.1 hy
      have hD : (BlowupTowerTransforms.exceptionalDivisor T).ideal.IsCoherent :=
        isCoherent_ideal _
      have hF : F.IsCoherent := isCoherent_idealPow hD _
      have hP : P.IsCoherent := isCoherent_pullback hπ.contMDiff hF
      have hC : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsCoherent :=
        isCoherent_pullback hπ.contMDiff (isCoherent_vanishingIdeal_centre hπ)
      have hG : G.IsCoherent := isCoherent_idealPow hC _
      have ih := original_tower_factor_forward M hN hI T hT.1
      have hPull : RestrictLe W
          (GermIdeal.pullback (m := n) π (GermIdeal.pullback (m := n) T.proj M.ideal))
          (P.mul B) := by
        have hh := restrictLe_pullback hπ.contMDiff hImage (isCoherent_mul hF hJI) ih
        rw [pullback_mul hπ.contMDiff hF hJI] at hh
        exact hh
      have hOne : RestrictLe W B (G.mul U) := by
        have hh := (MarkedIdealOperationsAlong.MarkedIdeal.restrictLe_pullback_geoTransform
          hJN hJI hT.2 hπ).1
        change RestrictLe W B
          ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) J.d).mul U) at hh
        have hd : J.d = M.d := d_geoTransformAlong M T
        rwa [hd] at hh
      have hMul : RestrictLe W (P.mul B) (P.mul (G.mul U)) :=
        restrictLe_mul (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hP)
          (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent (isCoherent_mul hG hU))
          (restrictLe_refl hP) hOne
      have hFactor : idealPow
          (BlowupTowerTransforms.exceptionalDivisor (.step T C π hπ)).ideal M.d = P.mul G := by
        dsimp only [P, F, G]
        rw [BlowupTowerTransforms.exceptionalDivisor_step_ideal,
          idealPow_mul (isCoherent_pullback hπ.contMDiff hD) hC,
          ← BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff hD]
      change RestrictLe W (GermIdeal.pullback (m := n) (T.proj ∘ π) M.ideal)
        ((idealPow (BlowupTowerTransforms.exceptionalDivisor (.step T C π hπ)).ideal M.d).mul U)
      rw [pullback_comp T.contMDiff_proj hπ.contMDiff hI, hFactor, mul_assoc hP hG hU]
      exact RestrictLeCalculus.RestrictLe.trans hPull hMul

/-- The converse ORIGINAL total factor inclusion, independently transported
on the actual proper carrier through the SAME genuine test tower. -/
theorem original_tower_factor_reverse {n : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hN : IsClosedSubmanifold n M.N)
    (hI : M.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower M T →
      RestrictLe (M.geoTransformAlong T).N
        ((idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal M.d).mul
          (M.geoTransformAlong T).ideal)
        (GermIdeal.pullback (m := n) T.proj M.ideal)
  | _, .refl, _ => by
      rw [geoTransformAlong_refl, BlowupTower.proj_refl,
        BlowupTowerTransforms.exceptionalDivisor_refl_ideal, idealPow_unitIdeal,
        unitIdeal_mul hI, pullback_id hI]
      exact restrictLe_refl hI
  | _, .step T C π hπ, hT => by
      let J := M.geoTransformAlong T
      let W := (J.geoTransform C π).N
      let U := (J.geoTransform C π).ideal
      let F := idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal M.d
      let P := GermIdeal.pullback (m := n) π F
      let B := GermIdeal.pullback (m := n) π J.ideal
      let G := idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) M.d
      have hJ := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
        hN hI T hT.1
      have hJN : IsClosedSubmanifold n J.N := hJ.1
      have hJI : J.ideal.IsCoherent := hJ.2
      have hU : U.IsCoherent :=
        (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
          hN hI (.step T C π hπ) hT).2
      have hImage : ∀ y ∈ W, π y ∈ J.N := fun _ hy =>
        geoStrictTransform_subset_preimage hπ.contMDiff.continuous hJN.1 hy
      have hD : (BlowupTowerTransforms.exceptionalDivisor T).ideal.IsCoherent :=
        isCoherent_ideal _
      have hF : F.IsCoherent := isCoherent_idealPow hD _
      have hP : P.IsCoherent := isCoherent_pullback hπ.contMDiff hF
      have hB : B.IsCoherent := isCoherent_pullback hπ.contMDiff hJI
      have hC : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsCoherent :=
        isCoherent_pullback hπ.contMDiff (isCoherent_vanishingIdeal_centre hπ)
      have hG : G.IsCoherent := isCoherent_idealPow hC _
      have hA : (GermIdeal.pullback (m := n) T.proj M.ideal).IsCoherent :=
        isCoherent_pullback T.contMDiff_proj hI
      have ih := original_tower_factor_reverse M hN hI T hT.1
      have hPull : RestrictLe W (P.mul B)
          (GermIdeal.pullback (m := n) π (GermIdeal.pullback (m := n) T.proj M.ideal)) := by
        have hh := restrictLe_pullback hπ.contMDiff hImage hA ih
        rw [pullback_mul hπ.contMDiff hF hJI] at hh
        exact hh
      have hOne : RestrictLe W (G.mul U) B := by
        have hh := (MarkedIdealOperationsAlong.MarkedIdeal.restrictLe_pullback_geoTransform
          hJN hJI hT.2 hπ).2
        change RestrictLe W
          ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) J.d).mul U) B at hh
        have hd : J.d = M.d := d_geoTransformAlong M T
        rwa [hd] at hh
      have hMul : RestrictLe W (P.mul (G.mul U)) (P.mul B) :=
        restrictLe_mul (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hP)
          (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hB)
          (restrictLe_refl hP) hOne
      have hFactor : idealPow
          (BlowupTowerTransforms.exceptionalDivisor (.step T C π hπ)).ideal M.d = P.mul G := by
        dsimp only [P, F, G]
        rw [BlowupTowerTransforms.exceptionalDivisor_step_ideal,
          idealPow_mul (isCoherent_pullback hπ.contMDiff hD) hC,
          ← BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff hD]
      change RestrictLe W
        ((idealPow (BlowupTowerTransforms.exceptionalDivisor (.step T C π hπ)).ideal M.d).mul U)
        (GermIdeal.pullback (m := n) (T.proj ∘ π) M.ideal)
      rw [pullback_comp T.contMDiff_proj hπ.contMDiff hI, hFactor, mul_assoc hP hG hU]
      exact RestrictLeCalculus.RestrictLe.trans hMul hPull

/-- BOTH genuine original factor directions, with no additional caller datum. -/
theorem original_tower_factor {n : ℕ} {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hN : IsClosedSubmanifold n M.N)
    (hI : M.ideal.IsCoherent) (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    let Q := M.geoTransformAlong T
    let F := idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal M.d
    RestrictLe Q.N (GermIdeal.pullback (m := n) T.proj M.ideal) (F.mul Q.ideal) ∧
      RestrictLe Q.N (F.mul Q.ideal) (GermIdeal.pullback (m := n) T.proj M.ideal) :=
  ⟨original_tower_factor_forward M hN hI T hT,
    original_tower_factor_reverse M hN hI T hT⟩

end
end Hironaka.HironakaActualProperOriginalTowerFactor
