import Hironaka.Resolution.HironakaActualMultiDerivativeBlowup
import Hironaka.Resolution.HironakaActualHistoricalMovingPrefixSupport
import Hironaka.Resolution.HironakaActualFixedInheritedSelector

/-! Whole original forbidden cones survive actual marked normalization at
EVERY derivative order, including orders larger than the member mark.
No target support, target diagram or target HS comparison is an input. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalNormalizedSupport
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualCanonicalBlockJacobian
  HironakaActualFormalBlowupMemberGeneration HironakaActualNormalizedBlowupDerivative
  HironakaActualFormalCoordinatePowerDivision HironakaActualInheritedNestedContactFlag
  HironakaActualHistoricalMovingPrefixSupport HironakaActualFixedInheritedSelector

variable {n : ℕ}

private theorem degree_add_single (β : Fin n →₀ ℕ) (i : Fin n) :
    normalExponentDegree (β+Finsupp.single i 1)=normalExponentDegree β+1 := by
  simp [normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib]

private theorem exists_split_nonzero (β : Fin n →₀ ℕ) (hβ : β≠0) :
    ∃(i : Fin n)(γ : Fin n →₀ ℕ),β i≠0 ∧ γ+Finsupp.single i 1=β ∧
      γ≤β ∧ normalExponentDegree γ<normalExponentDegree β := by
  obtain ⟨i,hi⟩ : ∃i,β i≠0:=by
    by_contra! hzero
    exact hβ (Finsupp.ext hzero)
  have hsingle : Finsupp.single i 1≤β := by
    intro j
    by_cases hji : j=i
    · subst j
      simpa only [Finsupp.single_eq_same] using Nat.one_le_iff_ne_zero.mpr hi
    · simp [Finsupp.single_eq_of_ne hji]
  let γ:=β-Finsupp.single i 1
  have hsum : γ+Finsupp.single i 1=β:=tsub_add_cancel_of_le hsingle
  have hdeg : normalExponentDegree γ+1=normalExponentDegree β:=by
    simpa only [degree_add_single] using congrArg normalExponentDegree hsum
  exact ⟨i,γ,hi,hsum,tsub_le_self,by omega⟩

private theorem support_of_le {γ β : Fin n →₀ ℕ} (hγβ : γ≤β) :
    (↑γ.support : Set (Fin n))⊆β.support := by
  intro i hi
  apply Finsupp.mem_support_iff.mpr
  intro hz
  exact (Finsupp.mem_support_iff.mp hi)
    (Nat.eq_zero_of_le_zero (by simpa only [hz] using hγβ i))

/-- The genuine whole-series chain rule at arbitrary essential derivative
order; no comparison of that order to a member mark is required. -/
theorem actualFormalMultiDerivative_blowup
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (β : Fin n →₀ ℕ) (hβ : (↑β.support : Set (Fin n))⊆A\{e})
    (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalMultiDerivative β (actualFormalBlowup A e b F)=
      (MvPowerSeries.X e)^normalExponentDegree β*
        actualFormalBlowup A e b (actualFormalMultiDerivative β F) := by
  induction β using (measure normalExponentDegree).wf.induction with
  | h β ih =>
    by_cases hz : β=0
    · subst β
      simp [actualFormalMultiDerivative_zero,normalExponentDegree]
    · obtain ⟨i,γ,hi,hsum,hγβ,hdeg⟩:=exists_split_nonzero β hz
      have hγ : (↑γ.support : Set (Fin n))⊆A\{e}:=
        (support_of_le hγβ).trans hβ
      have hiA : i∈A:=(hβ (Finsupp.mem_support_iff.mpr hi)).1
      have hie : i≠e:=by
        simpa only [mem_singleton_iff] using (hβ (Finsupp.mem_support_iff.mpr hi)).2
      rw [←hsum,actualFormalMultiDerivative_add_single,ih γ hdeg hγ,
        Derivation.leibniz,MvPowerSeries.pderiv_pow,
        MvPowerSeries.pderiv_X_of_ne (Ne.symm hie)]
      simp only [mul_zero,smul_eq_mul]
      rw [pderiv_actualFormalBlowup A e b i hiA hie,
        ←actualFormalMultiDerivative_add_single,degree_add_single,pow_succ]
      ring

/-- Every nonpivot essential multi-derivative passes through an arbitrary
exceptional power, even when its order exceeds that power. -/
theorem actualFormalMultiDerivative_exceptional_mul
    (e : Fin n) (μ : ℕ) (β : Fin n →₀ ℕ)
    (hβ : (↑β.support : Set (Fin n))⊆({e} : Set (Fin n))ᶜ)
    (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalMultiDerivative β ((MvPowerSeries.X e)^μ*F)=
      (MvPowerSeries.X e)^μ*actualFormalMultiDerivative β F := by
  induction β using (measure normalExponentDegree).wf.induction with
  | h β ih =>
    by_cases hz : β=0
    · subst β
      rw [actualFormalMultiDerivative_zero,actualFormalMultiDerivative_zero]
    · obtain ⟨i,γ,hi,hsum,hγβ,hdeg⟩:=exists_split_nonzero β hz
      have hγ : (↑γ.support : Set (Fin n))⊆({e} : Set (Fin n))ᶜ:=
        (support_of_le hγβ).trans hβ
      have hie : i≠e:=by
        simpa only [mem_compl_iff,mem_singleton_iff] using hβ (Finsupp.mem_support_iff.mpr hi)
      rw [←hsum,actualFormalMultiDerivative_add_single,ih γ hdeg hγ,
        Derivation.leibniz,MvPowerSeries.pderiv_pow,
        MvPowerSeries.pderiv_X_of_ne (Ne.symm hie)]
      simp only [mul_zero,smul_eq_mul,add_zero]
      rw [←actualFormalMultiDerivative_add_single]

/-- The source's ENTIRE forbidden cone survives actual normalization,
including derivative orders strictly greater than the source mark. -/
theorem actualNormalizedFormalMember_cone_zero_all_orders
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (β : Fin n →₀ ℕ) (hβ : (↑β.support : Set (Fin n))⊆A\{e})
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F∈actualFormalCoordinateIdeal n A^μ)
    (hz : ∀α : Fin n →₀ ℕ,β≤α → MvPowerSeries.coeff α F=0) :
    ∀α : Fin n →₀ ℕ,β≤α →
      MvPowerSeries.coeff α (actualNormalizedFormalMember A e he b μ F hF)=0 := by
  apply (actualFormalMultiDerivative_eq_zero_iff_cone β _).mp
  have hDF : actualFormalMultiDerivative β F=0:=
    (actualFormalMultiDerivative_eq_zero_iff_cone β F).mpr hz
  have hβe : (↑β.support : Set (Fin n))⊆({e} : Set (Fin n))ᶜ:=fun i hi=>(hβ hi).2
  have h:=congrArg (actualFormalMultiDerivative β)
    (actualNormalizedFormalMember_spec A e he b μ F hF)
  rw [actualFormalMultiDerivative_exceptional_mul e μ β hβe,
    actualFormalMultiDerivative_blowup A e b β hβ F,hDF,map_zero,mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left
    (pow_ne_zero μ (actualFormalExceptional_ne_zero e))

/-- All literal old degree-prefix cones of SAME normalized historical
members persist in a free-pivot chart, with every original label. -/
theorem actualNormalizedFormalMembers_whole_prefix_support
    (V : Finset (Fin n →₀ ℕ)) (g : V → MvPowerSeries (Fin n) ℂ)
    (hPrefix : HistoricalWholePrefixSupport V g)
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hB : fixedSelectorEssential V⊆A) (heFree : e∉fixedSelectorEssential V)
    (hF : ∀a : V,g a∈actualFormalCoordinateIdeal n A^normalExponentDegree a.val) :
    HistoricalWholePrefixSupport V (fun a=>
      actualNormalizedFormalMember A e he b (normalExponentDegree a.val) (g a) (hF a)) := by
  intro k a hka c hck
  have hc : (↑c.val.support : Set (Fin n))⊆A\{e} := by
    intro i hi
    have hiB : i∈fixedSelectorEssential V:=⟨c,Finsupp.mem_support_iff.mp hi⟩
    refine ⟨hB hiB,?_⟩
    intro hie
    exact heFree (hie ▸ hiB)
  exact actualNormalizedFormalMember_cone_zero_all_orders A e he b c.val hc
    (normalExponentDegree a.val) (g a) (hF a) (hPrefix k a hka c hck)

end
end Hironaka.HironakaActualHistoricalNormalizedSupport
