import Hironaka.Resolution.HironakaActualNormalZeroOwnerSupport
import Hironaka.Resolution.HironakaActualFormalFamilyStrictGenerators
import Hironaka.Resolution.HironakaActualFormalStandardMonomialHS

/-!
# Marked order retention for the SAME whole inherited family in a zero normal chart

The old owner partition is carried through the genuine monomial blowup. No new
monomial order, canonical reduced-family replacement, target diagram, target
regularity or target HS equality is supplied. Finite target jets are represented
by actual normalized SOURCE members, using the explicit lower coefficient lifts.
This is the adapted zero-direction statement, not an arbitrary chart adaptation
or an analytic neighbourhood HS-stratum theorem.

Source-only draft: these declarations have not been checked by Lean.
-/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalZeroOwnerConverse
noncomputable section
attribute [local instance] Classical.propDecidable
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalMonomialBlowupReflection
  HironakaActualRelativeStandardnessInheritedDivision HironakaActualNormalZeroOwnerSupport
  HironakaActualReducedBasisDivision HironakaActualFormalFamilyStrictGenerators
  HironakaActualFormalStrictGenerators
  HironakaActualFormalStandardMonomialHS
variable {n : ℕ}

/-- SAME inherited normalized members, at their literal original total-degree marks. -/
def inheritedZeroNormalizedVertex
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily MonomialOrder.degLex I)
    (e : Fin n)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val)
    (a : actualInitialVertices MonomialOrder.degLex I) : MvPowerSeries (Fin n) ℂ :=
  actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0)
    (normalExponentDegree a.val) (B.series a) (hpower a)

private theorem initialExponent_congr
    (F G : MvPowerSeries (Fin n) ℂ) (h : F = G) (hF : F ≠ 0) (hG : G ≠ 0) :
    actualInitialExponent MonomialOrder.degLex F hF = actualInitialExponent MonomialOrder.degLex G hG := by
  subst G
  rfl

private theorem initialExponent_Xpow_mul
    (e : Fin n) (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) :
    ∃ h : (MvPowerSeries.X e)^q * F ≠ 0,
      actualInitialExponent MonomialOrder.degLex ((MvPowerSeries.X e)^q * F) h =
        Finsupp.single e q + actualInitialExponent MonomialOrder.degLex F hF := by
  have h : (MvPowerSeries.X e)^q * F ≠ 0 :=
    mul_ne_zero (pow_ne_zero q (actualFormalExceptional_ne_zero e)) hF
  refine ⟨h, ?_⟩
  simpa only [MvPowerSeries.X_pow_eq, actualInitialExponent_monomial] using
    actualInitialExponent_mul MonomialOrder.degLex
      (MvPowerSeries.monomial (Finsupp.single e q) 1) F (actualMonomial_ne_zero _) hF

private theorem strict_minimum_initial_sum {ι : Type*} [Fintype ι]
    (P : ι → MvPowerSeries (Fin n) ℂ) (a : ι) (ha : P a ≠ 0)
    (hmin : ∀ b, b ≠ a → ∀ hb : P b ≠ 0,
      MonomialOrder.degLex.toSyn (actualInitialExponent MonomialOrder.degLex (P a) ha) <
        MonomialOrder.degLex.toSyn (actualInitialExponent MonomialOrder.degLex (P b) hb)) :
    ∃ hs : (∑ b, P b) ≠ 0,
      actualInitialExponent MonomialOrder.degLex (∑ b, P b) hs =
        actualInitialExponent MonomialOrder.degLex (P a) ha := by
  let α := actualInitialExponent MonomialOrder.degLex (P a) ha
  have hc : MvPowerSeries.coeff α (∑ b, P b) = MvPowerSeries.coeff α (P a) := by
    rw [map_sum]
    apply Finset.sum_eq_single a
    · intro b _ hba
      by_cases hb : P b = 0
      · rw [hb, map_zero]
      · exact coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex (P b) hb α (hmin b hba hb)
    · intro h
      exact (h (Finset.mem_univ a)).elim
  have hl : ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn α →
      MvPowerSeries.coeff β (∑ b, P b) = 0 := by
    intro β hβ
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : P b = 0
    · rw [hb, map_zero]
    · by_cases hba : b = a
      · subst b
        exact coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex (P a) ha β hβ
      · exact coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex (P b) hb β
          (lt_trans hβ (hmin b hba hb))
  have hs : (∑ b, P b) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hc
    exact (actualInitialExponent_spec MonomialOrder.degLex (P a) ha).1 hc.symm
  refine ⟨hs, actualInitialExponent_eq_of_coefficients MonomialOrder.degLex _ hs α ?_ hl⟩
  rw [hc]
  exact (actualInitialExponent_spec MonomialOrder.degLex (P a) ha).1

private theorem distinct_initial_sum {ι : Type*} [Fintype ι]
    (P : ι → MvPowerSeries (Fin n) ℂ) (hs : (∑ a, P a) ≠ 0)
    (hd : ∀ a b, a ≠ b → ∀ ha : P a ≠ 0, ∀ hb : P b ≠ 0,
      actualInitialExponent MonomialOrder.degLex (P a) ha ≠
        actualInitialExponent MonomialOrder.degLex (P b) hb) :
    ∃ a, ∃ ha : P a ≠ 0,
      actualInitialExponent MonomialOrder.degLex (∑ b, P b) hs =
        actualInitialExponent MonomialOrder.degLex (P a) ha := by
  have hsome : ∃ a, P a ≠ 0 := by
    by_contra h
    push Not at h
    exact hs (by simp only [h, Finset.sum_const_zero])
  let T := {a : ι // P a ≠ 0}
  let : Fintype T := Fintype.ofFinite T
  have hT : (Finset.univ : Finset T).Nonempty := by
    obtain ⟨a, ha⟩ := hsome
    exact ⟨⟨a, ha⟩, Finset.mem_univ _⟩
  let w (a : T) := MonomialOrder.degLex.toSyn (actualInitialExponent MonomialOrder.degLex (P a.val) a.property)
  obtain ⟨a, _ha, hmin⟩ := (Finset.univ : Finset T).exists_min_image w hT
  have hstrict : ∀ b, b ≠ a.val → ∀ hb : P b ≠ 0,
      MonomialOrder.degLex.toSyn (actualInitialExponent MonomialOrder.degLex (P a.val) a.property) <
        MonomialOrder.degLex.toSyn (actualInitialExponent MonomialOrder.degLex (P b) hb) := by
    intro b hba hb
    apply lt_of_le_of_ne (hmin (⟨b, hb⟩ : T) (Finset.mem_univ _))
    intro he
    exact hd a.val b hba.symm a.property hb (MonomialOrder.degLex.toSyn.injective he)
  obtain ⟨hs', hhead⟩ := strict_minimum_initial_sum P a.val a.property hstrict
  exact ⟨a.val, a.property, hhead⟩

private theorem pure_tail_weight (e : Fin n) (a : Fin n →₀ ℕ)
    (ha : ∀ i : Fin n, i ≤ e → a i = 0) :
    Finsupp.weight (actualCoordinateWeight (Set.Ici e \ {e})) a = normalExponentDegree a := by
  rw [Finsupp.weight_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ≤ e
  · simp only [ha i hi, zero_smul]
  · have hmem : i ∈ Set.Ici e \ {e} := ⟨le_of_lt (lt_of_not_ge hi), ne_of_gt (lt_of_not_ge hi)⟩
    simp only [actualCoordinateWeight, if_pos hmem, smul_eq_mul, mul_one]

/-- The SAME whole source owner partition rules out cancellation of actual
blown-up product heads. The output retains its literal original owner. -/
theorem actual_normal_zero_blowup_initial_of_inherited_orders
    (I K : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (hD : actualInitialDiagram MonomialOrder.degLex I = actualInitialDiagram MonomialOrder.degLex K)
    (hmem : ∀ a, B.series a ∈ K) (e : Fin n)
    (hpure : ∀ a : actualInitialVertices MonomialOrder.degLex I, ∀ i : Fin n, i ≤ e → a.val i = 0)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val)
    (horder : ∀ a, inheritedZeroNormalizedVertex I B e hpower a ∈
      genuineFormalVariables n ^ normalExponentDegree a.val)
    (F : MvPowerSeries (Fin n) ℂ) (hFK : F ∈ K) (hne : F ≠ 0) :
    ∃ a : actualInitialVertices MonomialOrder.degLex I, ∃ β : Fin n →₀ ℕ,
      inheritedDivisionOwner MonomialOrder.degLex I (β + a.val) = some a ∧
        ∃ hσ : actualFormalBlowup (Set.Ici e) e (fun _ => 0) F ≠ 0,
          actualInitialExponent MonomialOrder.degLex
            (actualFormalBlowup (Set.Ici e) e (fun _ => 0) F) hσ =
              actualMonomialBlowupExponent (Set.Ici e) e (β + a.val) := by
  let σ := actualFormalBlowup (Set.Ici e) e (fun _ => 0)
  let E := actualMonomialBlowupExponent (Set.Ici e) e
  let Q := inheritedFormalQuotient MonomialOrder.degLex I B F
  obtain ⟨hdiv, hsupport⟩ := inherited_formal_ideal_member_division MonomialOrder.degLex I B K hD hmem F hFK
  have hG (a : actualInitialVertices MonomialOrder.degLex I) :
      ∃ hg : σ (B.series a) ≠ 0,
        actualInitialExponent MonomialOrder.degLex (σ (B.series a)) hg = E a.val := by
    obtain ⟨hh, hhead⟩ := actualNormalizedFormalMember_zero_head_of_order e a.val (B.series a)
      (hpure a) (B.monic a) (B.lower a) (hpower a) (horder a)
    let H := inheritedZeroNormalizedVertex I B e hpower a
    have hH : H ≠ 0 := hh
    have hHhead : actualInitialExponent MonomialOrder.degLex H hH = a.val := hhead
    have hprod : (MvPowerSeries.X e)^(normalExponentDegree a.val) * H = σ (B.series a) :=
      actualNormalizedFormalMember_spec _ _ _ _ _ _ _
    have hg : σ (B.series a) ≠ 0 := by
      rw [← hprod]
      exact mul_ne_zero (pow_ne_zero _ (actualFormalExceptional_ne_zero e)) hH
    refine ⟨hg, ?_⟩
    obtain ⟨hp, hphead⟩ := initialExponent_Xpow_mul e (normalExponentDegree a.val) H hH
    calc
      _ = actualInitialExponent MonomialOrder.degLex
          ((MvPowerSeries.X e)^(normalExponentDegree a.val) * H) hp :=
        (initialExponent_congr _ _ hprod hp hg).symm
      _ = Finsupp.single e (normalExponentDegree a.val) + a.val := by rw [hphead, hHhead]
      _ = E a.val := by
        change Finsupp.single e (normalExponentDegree a.val) + a.val =
          a.val + Finsupp.single e _
        rw [pure_tail_weight e a.val (hpure a), add_comm]
  let P (a : actualInitialVertices MonomialOrder.degLex I) := σ (Q a) * σ (B.series a)
  have hsum : (∑ a, P a) = σ F := by
    rw [hdiv]
    simp only [map_sum, map_mul, P, Q]
  have hσF : σ F ≠ 0 := by
    intro hz
    apply hne
    apply actualFormalBlowup_zero_injective (Set.Ici e) e
    simpa only [map_zero] using hz
  have hP (a : actualInitialVertices MonomialOrder.degLex I) (ha : P a ≠ 0) :
      ∃ β : Fin n →₀ ℕ, MvPowerSeries.coeff β (Q a) ≠ 0 ∧
        actualInitialExponent MonomialOrder.degLex (P a) ha = E (β + a.val) := by
    have hQa : Q a ≠ 0 := by
      intro hz
      apply ha
      simp only [P, hz, map_zero, zero_mul]
    obtain ⟨hq, β, hβ, heβ⟩ := exists_source_exponent_of_actualFormalBlowup_zero_initial
      (Set.Ici e) e (Q a) hQa
    obtain ⟨hg, heg⟩ := hG a
    refine ⟨β, hβ, ?_⟩
    rw [actualInitialExponent_mul MonomialOrder.degLex _ _ hq hg, heβ, heg, ← map_add]
  have hdistinct : ∀ a b, a ≠ b → ∀ ha : P a ≠ 0, ∀ hb : P b ≠ 0,
      actualInitialExponent MonomialOrder.degLex (P a) ha ≠
        actualInitialExponent MonomialOrder.degLex (P b) hb := by
    intro a b hab ha hb he
    obtain ⟨β, hβ, hpβ⟩ := hP a ha
    obtain ⟨γ, hγ, hpγ⟩ := hP b hb
    rw [hpβ, hpγ] at he
    have hδ := actualMonomialBlowupExponent_injective (Set.Ici e) e he
    have hoa := hsupport a β hβ
    have hob := hsupport b γ hγ
    rw [hδ, hob] at hoa
    exact hab (Option.some.inj hoa.symm)
  have hsumne : (∑ a, P a) ≠ 0 := by rw [hsum]; exact hσF
  obtain ⟨a, ha, hhead⟩ := distinct_initial_sum P hsumne hdistinct
  obtain ⟨β, hβ, hPa⟩ := hP a ha
  have hσhead : actualInitialExponent MonomialOrder.degLex (σ F) hσF = E (β + a.val) := by
    exact (initialExponent_congr _ _ hsum hsumne hσF).symm.trans (hhead.trans hPa)
  exact ⟨a, β, hsupport a β hβ, hσF, hσhead⟩

/-- EVERY genuine normalized original member has a head in the source
whole diagram. The source division and its old owner are produced internally. -/
theorem actual_normal_zero_normalized_source_initial_mem_of_inherited_orders
    (I K : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (hD : actualInitialDiagram MonomialOrder.degLex I = actualInitialDiagram MonomialOrder.degLex K)
    (hmem : ∀ a, B.series a ∈ K) (e : Fin n)
    (hpure : ∀ a : actualInitialVertices MonomialOrder.degLex I, ∀ i : Fin n, i ≤ e → a.val i = 0)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val)
    (horder : ∀ a, inheritedZeroNormalizedVertex I B e hpower a ∈
      genuineFormalVariables n ^ normalExponentDegree a.val)
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hFK : F ∈ K)
    (hF : F ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ q) (hne : F ≠ 0) :
    ∃ hn : actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
        (fun _ => 0) q F hF ≠ 0,
      actualInitialExponent MonomialOrder.degLex
        (actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
          (fun _ => 0) q F hF) hn ∈ actualInitialDiagram MonomialOrder.degLex I := by
  let σ := actualFormalBlowup (Set.Ici e) e (fun _ => 0)
  let E := actualMonomialBlowupExponent (Set.Ici e) e
  obtain ⟨a, β, _howner, hσF, hσhead⟩ := actual_normal_zero_blowup_initial_of_inherited_orders
    I K B hD hmem e hpure hpower horder F hFK hne
  let H := actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0) q F hF
  have hN : H ≠ 0 := actualNormalizedFormalMember_zero_direction_ne_zero _ _ _ _ F hF hne
  have hproduct : (MvPowerSeries.X e)^q * H = σ F := actualNormalizedFormalMember_spec _ _ _ _ _ _ _
  have heq : Finsupp.single e q + actualInitialExponent MonomialOrder.degLex H hN = E (β + a.val) := by
    obtain ⟨hp, hphead⟩ := initialExponent_Xpow_mul e q H hN
    exact hphead.symm.trans ((initialExponent_congr _ _ hproduct hp hσF).trans hσhead)
  refine ⟨hN, (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex I _).mpr
    ⟨a.val, a.property, ?_⟩⟩
  intro i
  by_cases hie : i = e
  · subst i
    rw [hpure a e le_rfl]
    exact Nat.zero_le _
  · have hi := congrArg (fun c : Fin n →₀ ℕ => c i) heq
    change (Finsupp.single e q) i + actualInitialExponent MonomialOrder.degLex H hN i =
      (β + a.val) i + (Finsupp.single e _) i at hi
    have hi' : actualInitialExponent MonomialOrder.degLex H hN i = β i + a.val i := by
      simpa only [Finsupp.add_apply, Finsupp.single_eq_of_ne hie, zero_add, add_zero] using hi
    change a.val i ≤ actualInitialExponent MonomialOrder.degLex H hN i
    rw [hi']
    exact Nat.le_add_left _ _

/-- The entire target span has exactly the original diagram, even after
arbitrary formal coefficient cancellation. The finite-jet representative is
produced internally by genuine source normalization. -/
theorem actual_normal_zero_inherited_span_diagram_eq_of_orders
    (I K : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (hD : actualInitialDiagram MonomialOrder.degLex I = actualInitialDiagram MonomialOrder.degLex K)
    (hmem : ∀ a, B.series a ∈ K) (e : Fin n)
    (hpure : ∀ a : actualInitialVertices MonomialOrder.degLex I, ∀ i : Fin n, i ≤ e → a.val i = 0)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val)
    (horder : ∀ a, inheritedZeroNormalizedVertex I B e hpower a ∈
      genuineFormalVariables n ^ normalExponentDegree a.val) :
    actualInitialDiagram MonomialOrder.degLex
      (Ideal.span (Set.range (inheritedZeroNormalizedVertex I B e hpower))) =
        actualInitialDiagram MonomialOrder.degLex K := by
  let H := inheritedZeroNormalizedVertex I B e hpower
  let J := Ideal.span (Set.range H)
  let μ (a : actualInitialVertices MonomialOrder.degLex I) := normalExponentDegree a.val
  have hproduct (a : actualInitialVertices MonomialOrder.degLex I) :
      (MvPowerSeries.X e)^(μ a) * H a = actualFormalBlowup (Set.Ici e) e (fun _ => 0) (B.series a) :=
    actualNormalizedFormalMember_spec (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
      (fun _ => 0) (μ a) (B.series a) (hpower a)
  apply Set.Subset.antisymm
  · rintro c ⟨g, hg, hne, hc⟩
    obtain ⟨M, F, hF, hFK, hn, hsame⟩ := exists_normalized_source_with_same_initial_of_mem_span
      (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) K μ B.series H hmem hproduct g hg hne
    obtain ⟨hn', hsource⟩ := actual_normal_zero_normalized_source_initial_mem_of_inherited_orders
      I K B hD hmem e hpure hpower horder M F hFK hF (by
        intro hz
        apply hn
        apply mul_left_cancel₀ (pow_ne_zero M (actualFormalExceptional_ne_zero e))
        rw [actualNormalizedFormalMember_spec, hz, map_zero, mul_zero])
    rw [← hD]
    rw [← hc, hsame]
    exact hsource
  · intro c hc
    rw [← hD] at hc
    obtain ⟨a, ha, hac⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex I c).mp hc
    let a' : actualInitialVertices MonomialOrder.degLex I := ⟨a, ha⟩
    obtain ⟨hn, hhead⟩ := actualNormalizedFormalMember_zero_head_of_order e a (B.series a')
      (hpure a') (B.monic a') (B.lower a') (hpower a') (horder a')
    apply actualInitialDiagram_upper MonomialOrder.degLex J a c _ hac
    exact ⟨H a', Ideal.subset_span ⟨a', rfl⟩, hn, hhead⟩

private def referenceVertexOfDiagramEq
    (I K : Ideal (MvPowerSeries (Fin n) ℂ))
    (hD : actualInitialDiagram MonomialOrder.degLex I = actualInitialDiagram MonomialOrder.degLex K)
    (a : actualInitialVertices MonomialOrder.degLex K) : actualInitialVertices MonomialOrder.degLex I :=
  ⟨a.val, by
    have ha : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) a.val := by
      simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using a.property
    rw [← hD] at ha
    simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using ha⟩

private theorem inherited_strict_eq_same_normalized_span
    (I K : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (hD : actualInitialDiagram MonomialOrder.degLex I = actualInitialDiagram MonomialOrder.degLex K)
    (hmem : ∀ a, B.series a ∈ K) (e : Fin n)
    (hpure : ∀ a : actualInitialVertices MonomialOrder.degLex I, ∀ i : Fin n, i ≤ e → a.val i = 0)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val) :
    actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0) =
      Ideal.span (Set.range (inheritedZeroNormalizedVertex I B e hpower)) := by
  let r := referenceVertexOfDiagramEq I K hD
  let BK : ActualMonicVertexFamily MonomialOrder.degLex K :=
    { series := fun a => B.series (r a)
      mem := fun a => hmem (r a)
      monic := fun a => B.monic (r a)
      lower := fun a => B.lower (r a) }
  have hweight (a : actualInitialVertices MonomialOrder.degLex K) :
      Finsupp.weight (actualCoordinateWeight (Set.Ici e)) a.val = normalExponentDegree a.val := by
    rw [Finsupp.weight_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : e ≤ i
    · simp only [actualCoordinateWeight, Set.mem_Ici, if_pos hi, smul_eq_mul, mul_one]
    · have hz : a.val i = 0 := hpure (r a) i (le_of_lt (lt_of_not_ge hi))
      simp only [hz, zero_smul]
  have hv (a : actualInitialVertices MonomialOrder.degLex K) :
      familyVertexSeries MonomialOrder.degLex K BK a ∈
        actualFormalCoordinateIdeal n (Set.Ici e) ^
          Finsupp.weight (actualCoordinateWeight (Set.Ici e)) a.val := by
    rw [hweight]
    exact hpower (r a)
  rw [actualFormalStrictTransform_eq_family_span MonomialOrder.degLex K BK
    (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0) hv]
  congr 1
  have hnorm (a : actualInitialVertices MonomialOrder.degLex K) :
      familyNormalizedFormalVertex MonomialOrder.degLex K BK (Set.Ici e) e
        (Set.mem_Ici.mpr le_rfl) (fun _ => 0) hv a = inheritedZeroNormalizedVertex I B e hpower (r a) := by
    have hmark : Finsupp.weight (actualCoordinateWeight (Set.Ici e)) a.val =
        normalExponentDegree (r a).val := hweight a
    apply actualNormalizedFormalMember_unique (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
      (fun _ => 0) (normalExponentDegree (r a).val) (B.series (r a)) (hpower (r a))
    calc
      _ = (MvPowerSeries.X e)^(Finsupp.weight (actualCoordinateWeight (Set.Ici e)) a.val) *
          familyNormalizedFormalVertex MonomialOrder.degLex K BK (Set.Ici e) e
            (Set.mem_Ici.mpr le_rfl) (fun _ => 0) hv a := by rw [hmark]
      _ = actualFormalBlowup (Set.Ici e) e (fun _ => 0)
          (familyVertexSeries MonomialOrder.degLex K BK a) :=
        actualNormalizedFormalMember_spec _ _ _ _ _ _ (hv a)
      _ = _ := rfl
  have hrsurj : Function.Surjective r := by
    intro a
    have ha : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex I) a.val := by
      simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using a.property
    rw [hD] at ha
    let b : actualInitialVertices MonomialOrder.degLex K :=
      ⟨a.val, by simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using ha⟩
    exact ⟨b, Subtype.ext rfl⟩
  ext F
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨r a, (hnorm a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hrsurj a
    exact ⟨b, (hnorm b).trans (congrArg (inheritedZeroNormalizedVertex I B e hpower) hb)⟩

/-- ZERO adapted chart converse for the SAME full inherited family and the WHOLE
actual source normal strict ideal. No canonicality, target diagram or HS input. -/
theorem actual_normal_zero_strict_diagram_eq_of_inherited_orders
    (I K : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (hD : actualInitialDiagram MonomialOrder.degLex I = actualInitialDiagram MonomialOrder.degLex K)
    (hmem : ∀ a, B.series a ∈ K) (e : Fin n)
    (hpure : ∀ a : actualInitialVertices MonomialOrder.degLex I, ∀ i : Fin n, i ≤ e → a.val i = 0)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val)
    (horder : ∀ a, inheritedZeroNormalizedVertex I B e hpower a ∈
      genuineFormalVariables n ^ normalExponentDegree a.val) :
    actualInitialDiagram MonomialOrder.degLex
      (actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0)) =
        actualInitialDiagram MonomialOrder.degLex K := by
  rw [inherited_strict_eq_same_normalized_span I K B hD hmem e hpure hpower]
  exact actual_normal_zero_inherited_span_diagram_eq_of_orders I K B hD hmem e hpure hpower horder

/-- Every genuine formal HS value, with its original whole quotient and complex
action, follows from marked order retention at this adapted ZERO chart. -/
theorem genuineFormalHilbertSamuelValue_normal_zero_strict_eq_of_inherited_orders
    (I K : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (hD : actualInitialDiagram MonomialOrder.degLex I = actualInitialDiagram MonomialOrder.degLex K)
    (hmem : ∀ a, B.series a ∈ K) (e : Fin n)
    (hpure : ∀ a : actualInitialVertices MonomialOrder.degLex I, ∀ i : Fin n, i ≤ e → a.val i = 0)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val)
    (horder : ∀ a, inheritedZeroNormalizedVertex I B e hpower a ∈
      genuineFormalVariables n ^ normalExponentDegree a.val) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n
      (actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0)) ℓ =
        genuineFormalHilbertSamuelValue n K ℓ := by
  have hdiagram := actual_normal_zero_strict_diagram_eq_of_inherited_orders
    I K B hD hmem e hpure hpower horder
  rw [genuineFormalHilbertSamuelValue_eq_card_standardIndex,
    genuineFormalHilbertSamuelValue_eq_card_standardIndex]
  simp only [actualStandardIndex, hdiagram]

/-- Natural marked inputs internally produce the adapted vertex support and
then the WHOLE zero-chart diagram and every genuine formal HS value. No caller
support, target diagram, regularity or HS certificate, and no new family. -/
theorem actual_normal_zero_strict_diagram_and_hs_of_inherited_marked_orders
    (I K : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (hD : actualInitialDiagram MonomialOrder.degLex I = actualInitialDiagram MonomialOrder.degLex K)
    (hmem : ∀ a, B.series a ∈ K) (e : Fin n)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val)
    (horder : ∀ a, inheritedZeroNormalizedVertex I B e hpower a ∈
      genuineFormalVariables n ^ normalExponentDegree a.val) :
    (∀ a : actualInitialVertices MonomialOrder.degLex I, ∀ i : Fin n, i ≤ e → a.val i = 0) ∧
      actualInitialDiagram MonomialOrder.degLex
        (actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0)) =
          actualInitialDiagram MonomialOrder.degLex K ∧
      ∀ ℓ : ℕ, genuineFormalHilbertSamuelValue n
        (actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0)) ℓ =
          genuineFormalHilbertSamuelValue n K ℓ := by
  have hpure (a : actualInitialVertices MonomialOrder.degLex I) :
      ∀ i : Fin n, i ≤ e → a.val i = 0 :=
    pure_tail_of_monic_normal_mark_and_normalized_order e a.val (B.series a)
      (B.monic a) (hpower a) (horder a)
  exact ⟨hpure, actual_normal_zero_strict_diagram_eq_of_inherited_orders
    I K B hD hmem e hpure hpower horder,
    genuineFormalHilbertSamuelValue_normal_zero_strict_eq_of_inherited_orders
      I K B hD hmem e hpure hpower horder⟩

/-- The finite polynomial-lift node returns the SAME common denominator,
literal source polynomials and their exact normalized source combination.
The product hypotheses are the actual defining normalization identities. -/
theorem exists_common_polynomial_source_lifts_and_normalization
    {ι : Type*} [Fintype ι] (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (μ : ι → ℕ)
    (G H : ι → MvPowerSeries (Fin n) ℂ)
    (hmem : ∀ i, G i ∈ K)
    (hproduct : ∀ i, (MvPowerSeries.X e)^(μ i) * H i = actualFormalBlowup A e (fun _ => 0) (G i))
    (P : ι → MvPolynomial (Fin n) ℂ) :
    ∃ M : ℕ, (∀ i, μ i ≤ M) ∧ ∃ B : ι → MvPolynomial (Fin n) ℂ,
      (∀ i, actualFormalBlowup A e (fun _ => 0) (B i : MvPowerSeries (Fin n) ℂ) =
        (MvPowerSeries.X e)^(M - μ i) * (P i : MvPowerSeries (Fin n) ℂ)) ∧
      ∃ hF : (∑ i, (B i : MvPowerSeries (Fin n) ℂ) * G i) ∈ actualFormalCoordinateIdeal n A ^ M,
        (∑ i, (B i : MvPowerSeries (Fin n) ℂ) * G i) ∈ K ∧
          actualNormalizedFormalMember A e he (fun _ => 0) M
            (∑ i, (B i : MvPowerSeries (Fin n) ℂ) * G i) hF =
              ∑ i, (P i : MvPowerSeries (Fin n) ℂ) * H i := by
  let s (γ : Fin n →₀ ℕ) := Finsupp.weight (actualCoordinateWeight (A \ {e})) γ
  let M := (Finset.univ : Finset ι).sup (fun i => μ i + (P i).support.sup s)
  have hM (i : ι) : μ i + (P i).support.sup s ≤ M :=
    Finset.le_sup (f := fun j => μ j + (P j).support.sup s) (Finset.mem_univ i)
  have hμ (i : ι) : μ i ≤ M := le_trans (Nat.le_add_right _ _) (hM i)
  let B (i : ι) := zeroChartPolynomialCoefficientLift A e (M - μ i) (P i)
  have hB (i : ι) : actualFormalBlowup A e (fun _ => 0) (B i : MvPowerSeries (Fin n) ℂ) =
      (MvPowerSeries.X e)^(M - μ i) * (P i : MvPowerSeries (Fin n) ℂ) := by
    apply actualFormalBlowup_zero_polynomialCoefficientLift
    intro γ hγ
    have hγs : s γ ≤ (P i).support.sup s := Finset.le_sup hγ
    have hMi := hM i
    change s γ ≤ M - μ i
    omega
  let F : MvPowerSeries (Fin n) ℂ := ∑ i, (B i : MvPowerSeries (Fin n) ℂ) * G i
  have hFK : F ∈ K := K.sum_mem (fun i _ => K.mul_mem_left _ (hmem i))
  have hσ : actualFormalBlowup A e (fun _ => 0) F =
      (MvPowerSeries.X e)^M * ∑ i, (P i : MvPowerSeries (Fin n) ℂ) * H i := by
    simp only [F, map_sum, map_mul]
    calc
      _ = ∑ i, (MvPowerSeries.X e)^M * ((P i : MvPowerSeries (Fin n) ℂ) * H i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hB i, ← hproduct i]
        calc
          _ = (MvPowerSeries.X e)^((M - μ i) + μ i) *
              ((P i : MvPowerSeries (Fin n) ℂ) * H i) := by rw [pow_add]; ring
          _ = _ := by rw [Nat.sub_add_cancel (hμ i)]
      _ = _ := (Finset.mul_sum (Finset.univ : Finset ι)
        (fun i : ι => (P i : MvPowerSeries (Fin n) ℂ) * H i)
        ((MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ)^M)).symm
  have hF : F ∈ actualFormalCoordinateIdeal n A ^ M :=
    (mem_coordinate_power_iff_blowup_zero_exceptional_dvd A e he M F).mpr
      ⟨∑ i, (P i : MvPowerSeries (Fin n) ℂ) * H i, hσ⟩
  exact ⟨M, hμ, B, hB, hF, hFK,
    (actualNormalizedFormalMember_unique A e he (fun _ => 0) M F hF _ hσ.symm).symm⟩

end
end Hironaka.HironakaActualNormalZeroOwnerConverse
