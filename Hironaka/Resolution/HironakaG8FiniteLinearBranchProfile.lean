import Hironaka.Resolution.HironakaG8SquarefreePlaneProfile

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG8FiniteLinearBranchProfile
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HolGerm OkaRelationSheaf HironakaRelativeNormalDeformationInitialRelations
  HironakaHolomorphicJetChartInvariance HironakaActualPointGeometricBennett
  ActualHolomorphicGermFactoriality HironakaActualPrincipalHSFormula
  HironakaActualPrincipalJetMultiplication HironakaHolomorphicPointJets

variable {n : ℕ}

abbrev LinearBranch (n : ℕ) := ComplexModel n →L[ℂ] ℂ

private def branchGerm (a : LinearBranch n) : HolGerm (ComplexModel n) :=
  HolGerm.mk a (Eventually.of_forall fun _ => a.differentiableAt)

private theorem prime_branchGerm (a : LinearBranch n) (ha : a ≠ 0) : Prime (branchGerm a) := by
  let := uniqueFactorizationMonoid_holGerm_euclidean n
  apply UniqueFactorizationMonoid.irreducible_iff_prime.mp
  constructor
  · intro hu
    have hv := (HolGerm.isUnit_iff_eval_ne_zero _).mp hu
    exact hv (by rw [branchGerm,HolGerm.eval_mk,map_zero])
  · intro b c h
    by_contra hn
    push Not at hn
    obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk b
    obtain ⟨g,hg,rfl⟩ := HolGerm.exists_eq_mk c
    have hf0 : f 0 = 0 := by
      by_contra hn'
      exact hn.1 ((HolGerm.isUnit_iff_eval_ne_zero _).mpr (by simpa only [HolGerm.eval_mk]))
    have hg0 : g 0 = 0 := by
      by_contra hn'
      exact hn.2 ((HolGerm.isUnit_iff_eval_ne_zero _).mpr (by simpa only [HolGerm.eval_mk]))
    have hEq : (a : ComplexModel n → ℂ) =ᶠ[𝓝 0] fun z => f z * g z :=
      HolGerm.mk_eq_mk_iff.mp (h.trans (HolGerm.mk_mul f g hf hg).symm)
    have hd : fderiv ℂ a (0 : ComplexModel n) = fderiv ℂ (f * g) 0 := hEq.fderiv_eq
    rw [a.fderiv,(hf.self_of_nhds.hasFDerivAt.mul hg.self_of_nhds.hasFDerivAt).fderiv] at hd
    apply ha
    ext z
    simpa [hf0,hg0] using DFunLike.congr_fun hd z

private theorem branchGerm_not_dvd {a b : LinearBranch n}
    (h : ∃ z, a z = 0 ∧ b z ≠ 0) : ¬ branchGerm a ∣ branchGerm b := by
  rintro ⟨d,hd⟩
  obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk d
  obtain ⟨z,haz,hbz⟩ := h
  have heq : (b : ComplexModel n → ℂ) =ᶠ[𝓝 0] fun z => a z * f z :=
    HolGerm.mk_eq_mk_iff.mp (hd.trans (HolGerm.mk_mul _ _ _ _).symm)
  have hh : fderiv ℂ b (0 : ComplexModel n) = fderiv ℂ ((a : ComplexModel n → ℂ) * f) 0 := heq.fderiv_eq
  rw [b.fderiv,(a.hasFDerivAt.mul hf.self_of_nhds.hasFDerivAt).fderiv] at hh
  apply hbz
  simpa [haz] using DFunLike.congr_fun hh z

private def germProduct (L : List (LinearBranch n)) : HolGerm (ComplexModel n) :=
  (L.map branchGerm).prod

private theorem branchGerm_not_dvd_product (a : LinearBranch n) (ha : Prime (branchGerm a))
    (L : List (LinearBranch n)) (hSep : ∀ b ∈ L, ∃ z, a z = 0 ∧ b z ≠ 0) :
    ¬ branchGerm a ∣ germProduct L := by
  induction L with
  | nil => exact fun hd => ha.not_isUnit (isUnit_of_dvd_one hd)
  | cons b L ih =>
    intro hd
    change branchGerm a ∣ branchGerm b * germProduct L at hd
    rcases ha.dvd_mul.mp hd with hb | htail
    · exact branchGerm_not_dvd (hSep b (by simp)) hb
    · exact ih (fun b hb => hSep b (List.mem_cons_of_mem _ hb)) htail

private theorem squarefree_germProduct (L : List (LinearBranch n))
    (hN : ∀ a ∈ L, a ≠ 0)
    (hSep : L.Pairwise (fun a b => ∃ z, a z = 0 ∧ b z ≠ 0)) :
    Squarefree (germProduct L) := by
  let := uniqueFactorizationMonoid_holGerm_euclidean n
  induction L with
  | nil => exact squarefree_one
  | cons a L ih =>
    have ha := prime_branchGerm a (hN a (by simp))
    obtain ⟨hs,hL⟩ := List.pairwise_cons.mp hSep
    have hn := branchGerm_not_dvd_product a ha L hs
    change Squarefree (branchGerm a * germProduct L)
    refine squarefree_mul_iff.mpr ⟨?_,ha.squarefree,ih (fun b hb => hN b (by simp [hb])) hL⟩
    intro d hd hdd
    obtain ⟨u,hu⟩ := hd
    rcases ha.irreducible.isUnit_or_isUnit hu with h | h
    · exact h
    · obtain ⟨v,rfl⟩ := h
      have hDiv : d * (v : HolGerm (ComplexModel n)) ∣ d := ⟨↑v⁻¹,by simp [mul_assoc]⟩
      rw [← hu] at hDiv
      exact (hn (dvd_trans hDiv hdd)).elim

private theorem branchGerm_order_one (a : LinearBranch n) (ha : a ≠ 0) :
    branchGerm a ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ 1 ∧
      branchGerm a ∉ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ 2 := by
  constructor
  · rw [pow_one]
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    rw [branchGerm,HolGerm.eval_mk,map_zero]
  · intro h
    have hZero := (mem_maximalIdeal_pow_iff_iteratedFDeriv
      (Eventually.of_forall fun _ => a.differentiableAt) 2).mp h 1 (by decide)
    apply ha
    ext z
    have hz := congrArg (fun g => g (fun _ => z)) hZero
    simpa using hz

private theorem germProduct_order (L : List (LinearBranch n)) (hN : ∀ a ∈ L, a ≠ 0) :
    germProduct L ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ L.length ∧
      germProduct L ∉ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (L.length+1) := by
  induction L with
  | nil =>
    change (1 : HolGerm (ComplexModel n)) ∈ _ ^ (0 : ℕ) ∧ (1 : HolGerm (ComplexModel n)) ∉ _ ^ (0+1)
    refine ⟨by simp,?_⟩
    rw [pow_one]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
  | cons a L ih =>
    obtain ⟨ha,ha'⟩ := branchGerm_order_one a (hN a (by simp))
    obtain ⟨hL,hL'⟩ := ih (fun b hb => hN b (by simp [hb]))
    exact ⟨(actual_mul_mem_maximal_pow_iff _ _ 1 L.length ha ha').mpr hL,
      fun h => hL' ((actual_mul_mem_maximal_pow_iff _ _ 1 (L.length+1) ha ha').mp h)⟩

/-- The literal finite product of the branch equations. -/
def branchProduct : List (LinearBranch n) → ComplexModel n → ℂ
  | [] => 1
  | a::L => fun z => a z * branchProduct L z

theorem branchProduct_eq_zero_iff (L : List (LinearBranch n)) (z : ComplexModel n) :
    branchProduct L z = 0 ↔ ∃ a ∈ L, a z = 0 := by
  induction L with
  | nil => simp [branchProduct]
  | cons a L ih => simp [branchProduct,mul_eq_zero,ih]

theorem branchProduct_hol (L : List (LinearBranch n)) : HolAt (branchProduct L) 0 := by
  induction L with
  | nil => exact Eventually.of_forall fun _ => differentiableAt_const (1 : ℂ)
  | cons a L ih =>
    have ha : HolAt (a : ComplexModel n → ℂ) 0 := Eventually.of_forall fun _ => a.differentiableAt
    exact ha.mul ih

private theorem mk_branchProduct (L : List (LinearBranch n)) :
    HolGerm.mk (branchProduct L) (branchProduct_hol L) = germProduct L := by
  induction L with
  | nil => exact HolGerm.mk_one
  | cons a L ih =>
    change HolGerm.mk (fun z => a z * branchProduct L z) _ = branchGerm a * germProduct L
    rw [HolGerm.mk_mul _ _ (Eventually.of_forall fun _ => a.differentiableAt) (branchProduct_hol L),ih]
    rfl

private theorem origin_ideal_of_squarefree_equation
    (f : ComplexModel n → ℂ) (hf : HolAt f 0)
    (h : Squarefree (HolGerm.mk f hf)) :
    originalCoherentOriginIdeal (vanishingIdeal (n := n) {z | f z = 0}) =
      Ideal.span {HolGerm.mk f hf} := by
  have hGeo : originalCoherentOriginIdeal (vanishingIdeal (n := n) {z | f z = 0}) =
      AnalyticGermDecomposition.vanishingIdeal {z | f z = 0} := by
    ext g
    obtain ⟨a,ha,rfl⟩ := HolGerm.exists_eq_mk g
    rw [mk_mem_original_vanishing_origin_ideal_iff,AnalyticGermDecomposition.mem_vanishingIdeal_mk]
  rw [hGeo]
  let := uniqueFactorizationMonoid_holGerm_euclidean n
  have hRa : (Ideal.span ({HolGerm.mk f hf} : Set (HolGerm (ComplexModel n)))).IsRadical :=
    isRadical_iff_span_singleton.mp (isRadical_iff_squarefree_or_zero.mpr (Or.inl h))
  apply le_antisymm
  · have hBound := RueckertNullstellensatz.vanishingIdeal_le_radical (Ideal.span {HolGerm.mk f hf})
      (fun _ : Fin 1 => f) (fun _ => ⟨hf,Ideal.subset_span rfl⟩)
    apply (show AnalyticGermDecomposition.vanishingIdeal {z | f z = 0} ≤ _ from ?_).trans
      (hRa.radical_le_iff.mpr le_rfl)
    simpa only [Fin.forall_fin_one] using hBound
  · apply Ideal.span_le.mpr
    rintro g rfl
    exact AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
      (Eventually.of_forall fun _ hz => hz)

/-- An actual reduced hyperplane arrangement has the principal Hilbert–
Samuel profile given by its exact number of nonproportional branches. -/
theorem origin_profile_of_finite_linear_arrangement (L : List (LinearBranch n))
    (hN : ∀ a ∈ L, a ≠ 0)
    (hSep : L.Pairwise (fun a b => ∃ z, a z = 0 ∧ b z ≠ 0))
    (l : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) {z | branchProduct L z = 0}) 0 l =
      Nat.choose (n+l) n - (if L.length ≤ l then Nat.choose (n+(l-L.length)) n else 0) := by
  have hm := mk_branchProduct L
  have hs : Squarefree (HolGerm.mk (branchProduct L) (branchProduct_hol L)) :=
    hm ▸ squarefree_germProduct L hN hSep
  obtain ⟨hOrder,hNext⟩ := germProduct_order L hN
  rw [← hm] at hOrder hNext
  have hne : HolGerm.mk (branchProduct L) (branchProduct_hol L) ≠ 0 :=
    fun h => hNext (h.symm ▸ Ideal.zero_mem _)
  rw [hilbertSamuelAt_model_zero,origin_ideal_of_squarefree_equation _ _ hs]
  have hh := hilbertSamuelValue_actual_principal_order _ hne l
  rwa [actualGermOrder_unique _ hne L.length hOrder hNext] at hh

end
end Hironaka.HironakaG8FiniteLinearBranchProfile

#print axioms Hironaka.HironakaG8FiniteLinearBranchProfile.origin_profile_of_finite_linear_arrangement
