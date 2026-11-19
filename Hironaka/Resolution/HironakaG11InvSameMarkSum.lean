import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.Blowup.BlowupStrictIdeal

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Same-mark sums of marked ideals on a submanifold under admissible blowups

Blueprint: `hironaka-g11-inv-bm-lower.tex`.  Source: Bierstone--Milman 2008, §3 (the "intersection" of marked ideals of
the same mark `d`: `(N, E, 𝔞, d) + (N, E, 𝔟, d) = (N, E, 𝔞 + 𝔟, d)`, Lemma 3.8), Włodarczyk 2005 Lemma `le:operations`
(1).  The library has the calculus for Włodarczyk's sum `(𝔞^ν + 𝔟^μ, μν)` (`MarkedIdealOperationsAlong`); Bierstone--Milman's
lower family of the levels `s + 1` (`HironakaG11InvBMLower.lowerIdealBM`) uses the same-mark sum, whose calculus is the same
argument with the cancellation of `(π^*𝓘_C)^d` along the strict transform of `N`:

* `sumMarked 𝔪₁ 𝔪₂ = (N, E, 𝔞₁ + 𝔞₂, d)`; `cosupp_sumMarked` (`cosupp = cosupp 𝔪₁ ∩ cosupp 𝔪₂` for equal marks),
  `isAdmissibleCentre_sumMarked_iff`;
* `restrictEquiv_geoTransform_of_pullback_eq`: if `π^*𝔞 = (π^*𝓘_C)^d · 𝔟` ambiently (`𝔟` coherent), the transform of
  `(N, E, 𝔞, d)` along an admissible centre is restricted-equivalent to `(N', E', 𝔟, d)` (the transform is determined by
  any ambient factorization of the total transform);
* `geoTransform_sumMarked_restrictEquiv` (one blowup) and **`geoTransformAlong_sumMarked_along`** (towers): the multiple
  test blow-ups of `𝔪₁ + 𝔪₂` are exactly the simultaneous ones of `𝔪₁` and `𝔪₂`, and along them `(𝔪₁ + 𝔪₂)_T` is
  restricted-equivalent to `(𝔪₁)_T + (𝔪₂)_T`;
* `cosupp_geoTransformAlong_sumMarked`: along them the cosupport is the intersection.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11InvSameMarkSum

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers
  Hironaka.RestrictedIdealExtension Hironaka.RestrictedIdealWeight
  Hironaka.GermIdealPullbackCalculus Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupStrictSubmanifold
  Hironaka.MarkedIdealOperationsAlong Hironaka.BlowupTowers
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv IsSubmanifoldPair
  hol_of_isCoherent restrictLe_pullback_geoTransform)

noncomputable section

variable {n : ℕ}

/-! ### The same-mark sum -/

section OneSpace

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The same-mark sum** `(N, E, 𝔞₁ + 𝔞₂, d₁)` (Bierstone--Milman's sum for equal marks), on `N`, `E` and the mark of
the first. -/
def sumMarked (𝔪₁ 𝔪₂ : MarkedIdeal n M) : MarkedIdeal n M where
  N := 𝔪₁.N
  E := 𝔪₁.E
  ideal := sumIdeal 𝔪₁.ideal 𝔪₂.ideal
  d := 𝔪₁.d

@[simp] theorem sumMarked_N (𝔪₁ 𝔪₂ : MarkedIdeal n M) : (sumMarked 𝔪₁ 𝔪₂).N = 𝔪₁.N := rfl
@[simp] theorem sumMarked_E (𝔪₁ 𝔪₂ : MarkedIdeal n M) : (sumMarked 𝔪₁ 𝔪₂).E = 𝔪₁.E := rfl
@[simp] theorem sumMarked_d (𝔪₁ 𝔪₂ : MarkedIdeal n M) : (sumMarked 𝔪₁ 𝔪₂).d = 𝔪₁.d := rfl
theorem sumMarked_ideal (𝔪₁ 𝔪₂ : MarkedIdeal n M) :
    (sumMarked 𝔪₁ 𝔪₂).ideal = sumIdeal 𝔪₁.ideal 𝔪₂.ideal := rfl

variable {𝔪₁ 𝔪₂ : MarkedIdeal n M}

/-- **The cosupport of a same-mark sum is the intersection of the cosupports.** -/
theorem cosupp_sumMarked (h : IsSubmanifoldPair 𝔪₁ 𝔪₂) (hd : 𝔪₁.d = 𝔪₂.d) :
    (sumMarked 𝔪₁ 𝔪₂).cosupp = 𝔪₁.cosupp ∩ 𝔪₂.cosupp := by
  show cosupport n 𝔪₁.N (sumIdeal 𝔪₁.ideal 𝔪₂.ideal) 𝔪₁.d =
    cosupport n 𝔪₁.N 𝔪₁.ideal 𝔪₁.d ∩ cosupport n 𝔪₂.N 𝔪₂.ideal 𝔪₂.d
  rw [← h.N_eq, ← hd]
  exact IdealOrderArithmetic.cosupport_sumIdeal (hol_of_isCoherent h.coh₁) (hol_of_isCoherent h.coh₂) _

/-- **A centre is admissible for a same-mark sum iff it is admissible for both summands.** -/
theorem isAdmissibleCentre_sumMarked_iff (h : IsSubmanifoldPair 𝔪₁ 𝔪₂) (hd : 𝔪₁.d = 𝔪₂.d) {C : Set M} :
    (sumMarked 𝔪₁ 𝔪₂).IsAdmissibleCentre C ↔ 𝔪₁.IsAdmissibleCentre C ∧ 𝔪₂.IsAdmissibleCentre C := by
  simp only [IsAdmissibleCentre, cosupp_sumMarked h hd, subset_inter_iff]
  show _ ∧ _ ∧ NormalCrossings.HasNormalCrossings n C 𝔪₁.E ↔ _
  rw [← h.E_eq]
  tauto

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **The transform is determined by an ambient factorization of the total transform**: if `π^*𝔞 = (π^*𝓘_C)^d · 𝔟`
with `𝔟` coherent, then the transform of `(N, E, 𝔞, d)` along an admissible centre `C` is restricted-equivalent to
`(N', E', 𝔟, d)`. -/
theorem restrictEquiv_geoTransform_of_pullback_eq {𝔪 : MarkedIdeal n M} (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {C : Set M} (hC : 𝔪.IsAdmissibleCentre C) {π : M' → M} (hπ : IsBlowupAlong n C π)
    {𝔟 : GermIdeal n M'} (h𝔟 : 𝔟.IsCoherent)
    (heq : GermIdeal.pullback (m := n) π 𝔪.ideal =
      (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 𝔪.d).mul 𝔟) :
    RestrictEquiv (𝔪.geoTransform C π)
      ⟨(𝔪.geoTransform C π).N, (𝔪.geoTransform C π).E, 𝔟, 𝔪.d⟩ := by
  have h𝔞' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h𝔞 hC hπ
  obtain ⟨a1, a2⟩ := restrictLe_pullback_geoTransform hN h𝔞 hC hπ
  rw [heq] at a1 a2
  set L := idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 𝔪.d with hL
  have hinv : RestrictedIdealQuotient.IsInvertibleAlong n (𝔪.geoTransform C π).N L :=
    isInvertibleAlong_geoStrictTransform hπ 𝔪.N 𝔪.d
  rw [RestrictLeCalculus.mul_comm' L, RestrictLeCalculus.mul_comm' L] at a1 a2
  exact ⟨rfl, rfl, rfl, RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul h𝔞' h𝔟 hinv a2,
    RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul h𝔟 h𝔞' hinv a1⟩

/-- **One blowup of a same-mark sum** along `N`: the transform of `𝔪₁ + 𝔪₂` is restricted-equivalent to the sum of the
transforms. -/
theorem geoTransform_sumMarked_restrictEquiv (h : IsSubmanifoldPair 𝔪₁ 𝔪₂) (hd : 𝔪₁.d = 𝔪₂.d) {C : Set M}
    {π : M' → M} (hπ : IsBlowupAlong n C π) (hC₁ : 𝔪₁.IsAdmissibleCentre C) (hC₂ : 𝔪₂.IsAdmissibleCentre C) :
    RestrictEquiv ((sumMarked 𝔪₁ 𝔪₂).geoTransform C π) (sumMarked (𝔪₁.geoTransform C π) (𝔪₂.geoTransform C π)) := by
  set 𝔰 := sumMarked 𝔪₁ 𝔪₂ with h𝔰
  have hN := h.isClosedSubmanifold
  have hN₂ : IsClosedSubmanifold n 𝔪₂.N := h.N_eq ▸ hN
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have h𝔩 : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsCoherent :=
    isCoherent_pullback hπ.contMDiff hIC
  set 𝔩 := GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) with h𝔩def
  set μ := 𝔪₁.d with hμ
  have h𝔰coh : 𝔰.ideal.IsCoherent := isCoherent_sumIdeal h.coh₁ h.coh₂
  have hC𝔰 : 𝔰.IsAdmissibleCentre C := (isAdmissibleCentre_sumMarked_iff h hd).mpr ⟨hC₁, hC₂⟩
  have h𝔞' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h.coh₁ hC₁ hπ
  have h𝔟' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN₂ h.coh₂ hC₂ hπ
  have h𝔰' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (𝔪 := 𝔰) hN h𝔰coh hC𝔰 hπ
  obtain ⟨a1, a2⟩ := restrictLe_pullback_geoTransform hN h.coh₁ hC₁ hπ
  obtain ⟨b1, b2⟩ := restrictLe_pullback_geoTransform hN₂ h.coh₂ hC₂ hπ
  obtain ⟨s1, s2⟩ := restrictLe_pullback_geoTransform (𝔪 := 𝔰) hN h𝔰coh hC𝔰 hπ
  have hW₂ : (𝔪₂.geoTransform C π).N = (𝔪₁.geoTransform C π).N := by
    rw [geoTransform_N, geoTransform_N, h.N_eq]
  rw [hW₂, ← hd] at b1 b2
  set W := (𝔪₁.geoTransform C π).N with hWdef
  set 𝔞' := (𝔪₁.geoTransform C π).ideal
  set 𝔟' := (𝔪₂.geoTransform C π).ideal
  set 𝔰' := (𝔰.geoTransform C π).ideal
  set L := idealPow 𝔩 μ with hL
  set Xs := sumIdeal 𝔞' 𝔟' with hX
  have hLcoh : L.IsCoherent := isCoherent_idealPow h𝔩 _
  have hXcoh : Xs.IsCoherent := isCoherent_sumIdeal h𝔞' h𝔟'
  have e1 : GermIdeal.pullback (m := n) π 𝔰.ideal =
      sumIdeal (GermIdeal.pullback (m := n) π 𝔪₁.ideal) (GermIdeal.pullback (m := n) π 𝔪₂.ideal) :=
    MarkedIdealOperationsTransform.pullback_sumIdeal hπ.contMDiff (hol_of_isCoherent h.coh₁)
      (hol_of_isCoherent h.coh₂)
  have e2 : sumIdeal (L.mul 𝔞') (L.mul 𝔟') = Xs.mul L := by
    rw [← MarkedIdealOperationsTransform.mul_sumIdeal (hol_of_isCoherent hLcoh) (hol_of_isCoherent h𝔞')
      (hol_of_isCoherent h𝔟'), RestrictLeCalculus.mul_comm']
  have fwd : RestrictLe W (𝔰'.mul L) (Xs.mul L) := by
    rw [RestrictLeCalculus.mul_comm' 𝔰' L, ← e2]
    refine RestrictLeCalculus.RestrictLe.trans s2 ?_
    rw [e1]
    exact restrictLe_sumIdeal (hol_of_isCoherent (IdealWeightPowers.isCoherent_mul hLcoh h𝔞'))
      (hol_of_isCoherent (IdealWeightPowers.isCoherent_mul hLcoh h𝔟')) a1 b1
  have bwd : RestrictLe W (Xs.mul L) (𝔰'.mul L) := by
    rw [RestrictLeCalculus.mul_comm' 𝔰' L, ← e2]
    refine RestrictLeCalculus.RestrictLe.trans ?_ s1
    rw [e1]
    exact restrictLe_sumIdeal (hol_of_isCoherent (isCoherent_pullback hπ.contMDiff h.coh₁))
      (hol_of_isCoherent (isCoherent_pullback hπ.contMDiff h.coh₂)) a2 b2
  have hinv : RestrictedIdealQuotient.IsInvertibleAlong n W L :=
    isInvertibleAlong_geoStrictTransform hπ 𝔪₁.N μ
  exact ⟨rfl, rfl, rfl, RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul h𝔰' hXcoh hinv fwd,
    RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul hXcoh h𝔰' hinv bwd⟩

end OneSpace

/-! ### Along towers -/

section Tower

variable {X : CMfd.{u} n}

/-- **The same-mark sum along towers** (same `N`, `E` and mark, `N` a closed submanifold, coherent ideals): the multiple
test blow-ups of `𝔪₁ + 𝔪₂` are exactly the simultaneous multiple test blow-ups of `𝔪₁` and `𝔪₂`, and along them
`(𝔪₁ + 𝔪₂)_T` is restricted-equivalent to `(𝔪₁)_T + (𝔪₂)_T` (the stages stay pairs on closed submanifolds and the
transforms of the sum have coherent ideals). -/
theorem geoTransformAlong_sumMarked_along (𝔪₁ 𝔪₂ : MarkedIdeal n X) (h : IsSubmanifoldPair 𝔪₁ 𝔪₂)
    (hd : 𝔪₁.d = 𝔪₂.d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (IsGeoTestTower (sumMarked 𝔪₁ 𝔪₂) T ↔ IsGeoTestTower 𝔪₁ T ∧ IsGeoTestTower 𝔪₂ T) ∧
      (IsGeoTestTower 𝔪₁ T → IsGeoTestTower 𝔪₂ T →
        RestrictEquiv (geoTransformAlong (sumMarked 𝔪₁ 𝔪₂) T)
          (sumMarked (geoTransformAlong 𝔪₁ T) (geoTransformAlong 𝔪₂ T)) ∧
        IsSubmanifoldPair (geoTransformAlong 𝔪₁ T) (geoTransformAlong 𝔪₂ T) ∧
        (geoTransformAlong (sumMarked 𝔪₁ 𝔪₂) T).ideal.IsCoherent)
  | _, .refl => ⟨by simp [IsGeoTestTower], fun _ _ =>
      ⟨RestrictEquiv.refl (isCoherent_sumIdeal h.coh₁ h.coh₂), h, isCoherent_sumIdeal h.coh₁ h.coh₂⟩⟩
  | _, .step T C π hπ => by
      obtain ⟨ihT, ihE⟩ := geoTransformAlong_sumMarked_along 𝔪₁ 𝔪₂ h hd T
      have hdT : (geoTransformAlong 𝔪₁ T).d = (geoTransformAlong 𝔪₂ T).d := by
        rw [d_geoTransformAlong, d_geoTransformAlong, hd]
      refine ⟨?_, fun h₁ h₂ => ?_⟩
      · simp only [isGeoTestTower_step_iff]
        constructor
        · rintro ⟨hT, hC⟩
          obtain ⟨hT₁, hT₂⟩ := ihT.mp hT
          obtain ⟨heq, hpair, -⟩ := ihE hT₁ hT₂
          rw [heq.isAdmissibleCentre_iff, isAdmissibleCentre_sumMarked_iff hpair hdT] at hC
          exact ⟨⟨hT₁, hC.1⟩, hT₂, hC.2⟩
        · rintro ⟨⟨hT₁, hC₁⟩, hT₂, hC₂⟩
          obtain ⟨heq, hpair, -⟩ := ihE hT₁ hT₂
          refine ⟨ihT.mpr ⟨hT₁, hT₂⟩, ?_⟩
          rw [heq.isAdmissibleCentre_iff, isAdmissibleCentre_sumMarked_iff hpair hdT]
          exact ⟨hC₁, hC₂⟩
      · obtain ⟨hT₁, hC₁⟩ := (isGeoTestTower_step_iff 𝔪₁ T C π hπ).mp h₁
        obtain ⟨hT₂, hC₂⟩ := (isGeoTestTower_step_iff 𝔪₂ T C π hπ).mp h₂
        obtain ⟨heq, hpair, hcoh𝔰⟩ := ihE hT₁ hT₂
        have hcohA : (sumMarked (geoTransformAlong 𝔪₁ T) (geoTransformAlong 𝔪₂ T)).ideal.IsCoherent :=
          isCoherent_sumIdeal hpair.coh₁ hpair.coh₂
        have hNs : IsClosed (geoTransformAlong (sumMarked 𝔪₁ 𝔪₂) T).N := by
          rw [heq.N_eq]
          exact hpair.isClosedSubmanifold.1
        have hstep := heq.geoTransform_eq hNs hcoh𝔰 hcohA hπ.contMDiff (C := C)
        have hCA : (sumMarked (geoTransformAlong 𝔪₁ T) (geoTransformAlong 𝔪₂ T)).IsAdmissibleCentre C :=
          (isAdmissibleCentre_sumMarked_iff hpair hdT).mpr ⟨hC₁, hC₂⟩
        refine ⟨?_, hpair.geoTransform hπ hC₁ hC₂, ?_⟩
        · rw [geoTransformAlong_step, hstep]
          exact geoTransform_sumMarked_restrictEquiv hpair hdT hπ hC₁ hC₂
        · rw [geoTransformAlong_step, hstep]
          exact HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
            hpair.isClosedSubmanifold hcohA hCA hπ

/-- **Along a simultaneous multiple test blow-up, the cosupport of the transformed same-mark sum is the intersection of the
cosupports.** -/
theorem cosupp_geoTransformAlong_sumMarked (𝔪₁ 𝔪₂ : MarkedIdeal n X) (h : IsSubmanifoldPair 𝔪₁ 𝔪₂)
    (hd : 𝔪₁.d = 𝔪₂.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) (h₁ : IsGeoTestTower 𝔪₁ T)
    (h₂ : IsGeoTestTower 𝔪₂ T) :
    (geoTransformAlong (sumMarked 𝔪₁ 𝔪₂) T).cosupp =
      (geoTransformAlong 𝔪₁ T).cosupp ∩ (geoTransformAlong 𝔪₂ T).cosupp := by
  obtain ⟨heq, hpair, -⟩ := (geoTransformAlong_sumMarked_along 𝔪₁ 𝔪₂ h hd T).2 h₁ h₂
  rw [heq.cosupp_eq, cosupp_sumMarked hpair (by rw [d_geoTransformAlong, d_geoTransformAlong, hd])]

end Tower

end

end Hironaka.HironakaG11InvSameMarkSum
