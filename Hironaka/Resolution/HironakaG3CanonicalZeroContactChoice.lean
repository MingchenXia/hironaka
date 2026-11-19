import Hironaka.Resolution.HironakaG3ContactChoiceAtBase
import Hironaka.Resolution.HironakaG3CanonicalZeroContactData
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3CanonicalZeroContactChoice
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneValueMasked StepOneRegime StepOneCompare
  ResolutionInvariantSpec HomogenizedIdealAlong ContactStageKept TangentDirectionAlong
  G3ContactChoiceAtBase G3CanonicalZeroContactData
noncomputable section

/-- At an actual canonical zero-level point the chosen contact tail agrees with any other valid canonical contact tail through it. -/
theorem canonical_zero_contact_choice_values {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{u} n}
    {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k + 1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM R M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked M) T).cosupp)
    (hs : ¬ IsSpecial M T y) (hzero : level M T y = 0) :
    let j := regimeRun (stepRegime M (level M T y)) T y
    let T₀ := head T j
    let T₁ := tail T j
    let a := T₁.proj y
    let W₀ := maskB M T₀ a
    let w := (tangentChoice M (T₀.proj a)).2
    ∀ (v : X → ℂ) (V : Set X) (W : Opens (split T j).1),
      IsTangentDirectionAlong M.N M.ideal M.d V v →
      (W : Set (split T j).1) ⊆ T₀.proj ⁻¹' V →
      (∀ H ∈ origMembers M T₀, Disjoint (W : Set (split T j).1) H) →
      IsInvDomain k (contactMarkedKept M v T₀ W) →
      IsCanonical (contactMarkedKept M v T₀ W) (R.inv (contactMarkedKept M v T₀ W)) (restrict W T₁) →
      ∀ hW : a ∈ W, ∃ h₀ : a ∈ W₀,
        R.inv (contactMarkedKept M w T₀ W₀) (restrict W₀ T₁) ⟨y,h₀⟩ =
          R.inv (contactMarkedKept M v T₀ W) (restrict W T₁) ⟨y,hW⟩ := by
  dsimp only
  intro v V W hv hWV hEW hDW hCW hW
  let j := regimeRun (stepRegime M (level M T y)) T y
  let T₀ := head T j
  let T₁ := tail T j
  let a := T₁.proj y
  let W₀ := maskB M T₀ a
  let x := T₀.proj a
  let U := (tangentChoice M x).1
  let w := (tangentChoice M x).2
  have hdata := canonical_zero_level_contact_data hn R M hM hmax T hcan y hy hs hzero
  obtain ⟨h₀,hD₀,hC₀,_⟩ := hdata
  have hxU : x ∈ U := (interior_subset h₀).1
  have hu : IsTangentDirectionAlong M.N M.ideal M.d U w := tangentChoice_spec_of_mem M hxU
  have hxV : x ∈ V := hWV hW
  have hW₀U : (W₀ : Set (split T j).1) ⊆ T₀.proj ⁻¹' U := fun _ hz => (interior_subset hz).1
  have hE₀ : ∀ H ∈ origMembers M T₀, Disjoint (W₀ : Set (split T j).1) H :=
    fun H hH => Set.disjoint_left.mpr fun _ hz hzH => (interior_subset hz).2.1 H hH hzH
  have ht := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k + 1) R M hM hmax hn T hcan).1
  have hT : IsGeoTestTower (barMarked M) (T₀.append T₁) := by rw [head_append_tail]; exact ht
  have hY : y ∈ (geoTransformAlong (barMarked M) (T₀.append T₁)).cosupp := by rw [head_append_tail]; exact hy
  exact ⟨h₀, contact_choice_values_at_actual_base R M hM.isWellFormed hM.one_le_d T₀ T₁ hT y hY
    w v U V hu hxU hv hxV W₀ W hW₀U hWV hE₀ hEW hD₀ hC₀ hDW hCW h₀ hW⟩
end
end Hironaka.G3CanonicalZeroContactChoice
