import Hironaka.Resolution.HironakaActualSelectedVertexHomogeneousBasis
import Hironaka.Resolution.HironakaActualReducedBasisDivision

/-!
# One owner partition for the same inherited monic series

The generic inputs are the inherited monic initial exponents, actual membership
in the new whole ideal, and equality of the new diagram. Their original
geometric producers remain separate. The series are not required to be canonical.

Every degree prefix has homogeneous division at every degree. This is a
vector-space decomposition, not a claim that a prefix-generated ideal has the
prefix diagram. The full least-owner recursion uses exactly the same partition.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualRelativeStandardnessInheritedDivision

noncomputable section

open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalStandardMonomialHS
  HironakaActualFormalVertexDivision HironakaActualReducedFormalStandardBasis
  HironakaActualFiniteJetVertexBasis HironakaActualSelectedVertexHomogeneousBasis

variable {n : ℕ}

/-- Original vertex labels and actual inherited monic initial coefficients.
Membership in a new entire ideal is stated separately when it is needed. -/
structure InheritedMonicFamily (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) where
  series : actualInitialVertices m I → MvPowerSeries (Fin n) ℂ
  monic : ∀ a : actualInitialVertices m I, MvPowerSeries.coeff a.val (series a) = 1
  lower : ∀ (a : actualInitialVertices m I) (b : Fin n →₀ ℕ),
    m.toSyn b < m.toSyn a.val → MvPowerSeries.coeff b (series a) = 0

private theorem exists_least_inherited_owner (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (α : Fin n →₀ ℕ)
    (hα : α ∈ actualInitialDiagram m I) :
    ∃ a : actualInitialVertices m I, a.val ≤ α ∧
      ∀ b : actualInitialVertices m I, b.val ≤ α → m.toSyn a.val ≤ m.toSyn b.val := by
  let T : Set (actualInitialVertices m I) := {a | a.val ≤ α}
  let S : Set m.syn := (fun a : actualInitialVertices m I => m.toSyn a.val) '' T
  obtain ⟨a, ha, hle⟩ := (mem_actualInitialDiagram_iff_vertex_le m I α).mp hα
  have hTN : T.Nonempty := ⟨⟨a, ha⟩, hle⟩
  have hSN : S.Nonempty := hTN.image _
  have hw : S.IsWF := Set.IsWF.of_wellFoundedLT S
  obtain ⟨v, hv, he⟩ := hw.min_mem hSN
  refine ⟨v, hv, fun b hb => ?_⟩
  change m.toSyn v.val = hw.min hSN at he
  rw [he]
  exact hw.min_le hSN ⟨b, hb, rfl⟩

/-- The entire diagram is partitioned by the genuine least eligible vertex. -/
def inheritedDivisionOwner (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (α : Fin n →₀ ℕ) :
    Option (actualInitialVertices m I) :=
  if hα : α ∈ actualInitialDiagram m I then
    some (Classical.choose (exists_least_inherited_owner m I α hα)) else none

private theorem inheritedDivisionOwner_spec (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (α : Fin n →₀ ℕ)
    (a : actualInitialVertices m I) (ha : inheritedDivisionOwner m I α = some a) :
    a.val ≤ α ∧ ∀ b : actualInitialVertices m I,
      b.val ≤ α → m.toSyn a.val ≤ m.toSyn b.val := by
  unfold inheritedDivisionOwner at ha
  split_ifs at ha with hα
  · have he := Option.some.inj ha
    rw [← he]
    exact Classical.choose_spec (exists_least_inherited_owner m I α hα)

private theorem inheritedDivisionOwner_le (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (α : Fin n →₀ ℕ)
    (a : actualInitialVertices m I) (ha : inheritedDivisionOwner m I α = some a) :
    a.val ≤ α := (inheritedDivisionOwner_spec m I α a ha).1

private theorem inheritedDivisionOwner_eq_none_iff (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (α : Fin n →₀ ℕ) :
    inheritedDivisionOwner m I α = none ↔ α ∉ actualInitialDiagram m I := by
  by_cases hα : α ∈ actualInitialDiagram m I <;> simp [inheritedDivisionOwner, hα]

/-- The full owner and every degree-prefix owner agree wherever the prefix
diagram contains the exponent. This fixes one common supported partition. -/
theorem inheritedDegreePrefixOwner_compatible
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) (α : Fin n →₀ ℕ)
    (hα : α ∈ actualSelectedVertexDiagram I (actualDegreeBlockVertices I k)) :
    inheritedDivisionOwner MonomialOrder.degLex I α =
      some (actualSelectedVertexOwner I (actualDegreeBlockVertices I k) α hα) := by
  let a := actualSelectedVertexOwner I (actualDegreeBlockVertices I k) α hα
  have ha := actualSelectedVertexOwner_spec I (actualDegreeBlockVertices I k) α hα
  have hD : α ∈ actualInitialDiagram MonomialOrder.degLex I :=
    (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex I α).mpr
      ⟨a.val, a.property, ha.2.1⟩
  cases hb : inheritedDivisionOwner MonomialOrder.degLex I α with
  | none => exact False.elim ((inheritedDivisionOwner_eq_none_iff _ I α).mp hb hD)
  | some b =>
      have hbs := inheritedDivisionOwner_spec MonomialOrder.degLex I α b hb
      have hba := hbs.2 a ha.2.1
      have hdegree : normalExponentDegree b.val ≤ normalExponentDegree a.val := by
        rcases lt_or_eq_of_le hba with hlt | he
        · exact actual_degree_le_of_deglex_lt _ _ hlt
        · rw [MonomialOrder.degLex.toSyn.injective he]
      have hbV : b ∈ actualDegreeBlockVertices I k := hdegree.trans ha.1
      have hab := ha.2.2 b hbV hbs.1
      have hval : b.val = a.val := MonomialOrder.degLex.toSyn.injective (le_antisymm hba hab)
      have heq : b = a := Subtype.ext hval
      change some b = some a
      exact congrArg some heq

/-- The specified inherited's SAME actual series. -/
def inheritedVertexSeries (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily m I) (a : actualInitialVertices m I) : MvPowerSeries (Fin n) ℂ := B.series a

theorem inheritedVertexSeries_coefficient (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I)
    (a : actualInitialVertices m I) :
    MvPowerSeries.coeff (a : Fin n →₀ ℕ) (inheritedVertexSeries m I B a) = 1 := B.monic a

theorem inheritedVertexSeries_coefficient_lower (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I)
    (a : actualInitialVertices m I) (b : Fin n →₀ ℕ)
    (hb : m.toSyn b < m.toSyn (a : Fin n →₀ ℕ)) :
    MvPowerSeries.coeff b (inheritedVertexSeries m I B a) = 0 := B.lower a b hb

/-- Actual well-founded coefficient recursion; every recursive call is strictly lower. -/
def inheritedDivisionCoefficient (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I)
    (F : MvPowerSeries (Fin n) ℂ) (c : Fin n →₀ ℕ) : ℂ :=
  (InvImage.wf m.toSyn (wellFounded_lt : WellFounded ((· < ·) : m.syn → m.syn → Prop))).fix
    (C := fun _ => ℂ) (fun d rec =>
      MvPowerSeries.coeff d F -
        ∑ a : actualInitialVertices m I, ∑ p ∈ Finset.antidiagonal d,
          if h : m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn d then
            if inheritedDivisionOwner m I (p.1+(a : Fin n →₀ ℕ))=some a then
              rec (p.1+(a : Fin n →₀ ℕ)) h *
                MvPowerSeries.coeff p.2 (inheritedVertexSeries m I B a)
            else 0
          else 0) c

/-- The actual recursive correction at an exponent, expressed with the completed coefficient function. -/
def inheritedDivisionTail (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I)
    (F : MvPowerSeries (Fin n) ℂ) (c : Fin n →₀ ℕ) : ℂ :=
  ∑ a : actualInitialVertices m I, ∑ p ∈ Finset.antidiagonal c,
    if m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c then
      if inheritedDivisionOwner m I (p.1+(a : Fin n →₀ ℕ))=some a then
        inheritedDivisionCoefficient m I B F (p.1+(a : Fin n →₀ ℕ)) *
          MvPowerSeries.coeff p.2 (inheritedVertexSeries m I B a)
      else 0
    else 0

/-- The defining genuine recursion equation, without any caller coefficient solution. -/
theorem inheritedDivisionCoefficient_eq (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I) (F : MvPowerSeries (Fin n) ℂ) (c : Fin n →₀ ℕ) :
    inheritedDivisionCoefficient m I B F c=MvPowerSeries.coeff c F-inheritedDivisionTail m I B F c := by
  rw [inheritedDivisionCoefficient,WellFounded.fix_eq]
  simp only [inheritedDivisionTail,inheritedDivisionCoefficient,dite_eq_ite]

/-- Genuine formal quotient series have the ACTUAL disjoint owner coefficients. -/
def inheritedFormalQuotient (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I)
    (F : MvPowerSeries (Fin n) ℂ) (a : actualInitialVertices m I) : MvPowerSeries (Fin n) ℂ :=
  fun b => if inheritedDivisionOwner m I (b+(a : Fin n →₀ ℕ))=some a then
    inheritedDivisionCoefficient m I B F (b+(a : Fin n →₀ ℕ)) else 0

/-- The genuine remainder has zero coefficients at EVERY true diagram exponent. -/
def inheritedFormalRemainder (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I)
    (F : MvPowerSeries (Fin n) ℂ) : MvPowerSeries (Fin n) ℂ :=
  fun c => if c ∈ actualInitialDiagram m I then 0 else inheritedDivisionCoefficient m I B F c

/-- A nonzero actual quotient coefficient forces the SAME genuine owner part. -/
theorem inheritedFormalQuotient_support (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I) (F : MvPowerSeries (Fin n) ℂ)
    (a : actualInitialVertices m I) (b : Fin n →₀ ℕ)
    (hb : MvPowerSeries.coeff b (inheritedFormalQuotient m I B F a) ≠ 0) :
    inheritedDivisionOwner m I (b+(a : Fin n →₀ ℕ))=some a := by
  by_contra h
  exact hb (by simp [MvPowerSeries.coeff_apply,inheritedFormalQuotient,h])

/-- The actual remainder has no nonzero coefficient in the ACTUAL whole ideal diagram. -/
theorem inheritedFormalRemainder_coefficient_diagram (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I) (F : MvPowerSeries (Fin n) ℂ)
    (c : Fin n →₀ ℕ) (hc : c ∈ actualInitialDiagram m I) :
    MvPowerSeries.coeff c (inheritedFormalRemainder m I B F)=0 := by
  simp [MvPowerSeries.coeff_apply,inheritedFormalRemainder,hc]

private theorem inherited_quotient_monomial_coefficient (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I) (F : MvPowerSeries (Fin n) ℂ)
    (a : actualInitialVertices m I) (c : Fin n →₀ ℕ) :
    MvPowerSeries.coeff c (inheritedFormalQuotient m I B F a * MvPowerSeries.monomial a 1)=
      if inheritedDivisionOwner m I c=some a then inheritedDivisionCoefficient m I B F c else 0 := by
  rw [MvPowerSeries.coeff_mul_monomial]
  by_cases hac : (a : Fin n →₀ ℕ) ≤ c
  · simp [hac,MvPowerSeries.coeff_apply,inheritedFormalQuotient,tsub_add_cancel_of_le hac]
  · have ho : inheritedDivisionOwner m I c ≠ some a := fun h => hac (inheritedDivisionOwner_le m I c a h)
    simp [hac,ho]

private theorem inherited_quotient_tail_summand (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I) (F : MvPowerSeries (Fin n) ℂ)
    (a : actualInitialVertices m I) (c : Fin n →₀ ℕ) (p : (Fin n →₀ ℕ) × (Fin n →₀ ℕ))
    (hp : p ∈ Finset.antidiagonal c) :
    MvPowerSeries.coeff p.1 (inheritedFormalQuotient m I B F a) *
        MvPowerSeries.coeff p.2 (inheritedVertexSeries m I B a-MvPowerSeries.monomial a 1)=
      if m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c then
        if inheritedDivisionOwner m I (p.1+(a : Fin n →₀ ℕ))=some a then
          inheritedDivisionCoefficient m I B F (p.1+(a : Fin n →₀ ℕ)) *
            MvPowerSeries.coeff p.2 (inheritedVertexSeries m I B a)
        else 0
      else 0 := by
  have he : p.1+p.2=c := Finset.mem_antidiagonal.mp hp
  by_cases hpa : p.2=(a : Fin n →₀ ℕ)
  · have hs : p.1+(a : Fin n →₀ ℕ)=c := hpa ▸ he
    simp [map_sub,hpa,inheritedVertexSeries_coefficient,hs]
  · have hm : MvPowerSeries.coeff p.2 (MvPowerSeries.monomial (a : Fin n →₀ ℕ) (1 : ℂ))=0 := by
      simp [MvPowerSeries.coeff_monomial,hpa]
    rw [map_sub,hm,sub_zero]
    by_cases hs : m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c
    · rw [if_pos hs]
      simp only [MvPowerSeries.coeff_apply,inheritedFormalQuotient,ite_mul,zero_mul]
    · have hz : MvPowerSeries.coeff p.2 (inheritedVertexSeries m I B a)=0 := by
        by_contra hne
        have hle : m.toSyn (a : Fin n →₀ ℕ) ≤ m.toSyn p.2 := by
          by_contra h
          exact hne (inheritedVertexSeries_coefficient_lower m I B a p.2 (lt_of_not_ge h))
        have hlt : m.toSyn (a : Fin n →₀ ℕ) < m.toSyn p.2 :=
          lt_of_le_of_ne hle (fun h => hpa (m.toSyn.injective h.symm))
        apply hs
        rw [← he,map_add,map_add]
        exact add_lt_add_of_le_of_lt (le_refl _) hlt
      rw [if_neg hs,hz,mul_zero]

private theorem inherited_quotient_product_coefficient (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I) (F : MvPowerSeries (Fin n) ℂ)
    (a : actualInitialVertices m I) (c : Fin n →₀ ℕ) :
    MvPowerSeries.coeff c (inheritedFormalQuotient m I B F a * inheritedVertexSeries m I B a)=
      (if inheritedDivisionOwner m I c=some a then inheritedDivisionCoefficient m I B F c else 0)+
      ∑ p ∈ Finset.antidiagonal c,
        if m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c then
          if inheritedDivisionOwner m I (p.1+(a : Fin n →₀ ℕ))=some a then
            inheritedDivisionCoefficient m I B F (p.1+(a : Fin n →₀ ℕ)) *
              MvPowerSeries.coeff p.2 (inheritedVertexSeries m I B a)
          else 0
        else 0 := by
  have he : inheritedVertexSeries m I B a=MvPowerSeries.monomial a 1+
      (inheritedVertexSeries m I B a-MvPowerSeries.monomial a 1) := by abel
  conv_lhs => rw [he,mul_add,map_add]
  rw [inherited_quotient_monomial_coefficient]
  congr 1
  rw [MvPowerSeries.coeff_mul]
  exact Finset.sum_congr rfl (fun p hp => inherited_quotient_tail_summand m I B F a c p hp)

/-- EVERY actual series has a WHOLE genuine finite-antidiagonal division identity. -/
theorem inherited_formal_vertex_division (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I) (F : MvPowerSeries (Fin n) ℂ) :
    F=(∑ a : actualInitialVertices m I, inheritedFormalQuotient m I B F a*inheritedVertexSeries m I B a)+
      inheritedFormalRemainder m I B F := by
  apply MvPowerSeries.ext
  intro c
  rw [map_add,map_sum]
  simp_rw [inherited_quotient_product_coefficient]
  rw [Finset.sum_add_distrib]
  change MvPowerSeries.coeff c F=
    (∑ a : actualInitialVertices m I,
      if inheritedDivisionOwner m I c=some a then inheritedDivisionCoefficient m I B F c else 0)+
    inheritedDivisionTail m I B F c+MvPowerSeries.coeff c (inheritedFormalRemainder m I B F)
  cases ho : inheritedDivisionOwner m I c with
  | none =>
      have hc := (inheritedDivisionOwner_eq_none_iff m I c).mp ho
      simp only [reduceCtorEq,ite_false,Finset.sum_const_zero,zero_add]
      have hr : MvPowerSeries.coeff c (inheritedFormalRemainder m I B F)=inheritedDivisionCoefficient m I B F c := by
        change (if c ∈ actualInitialDiagram m I then 0 else inheritedDivisionCoefficient m I B F c)=_
        exact if_neg hc
      rw [hr,inheritedDivisionCoefficient_eq]
      ring
  | some a =>
      have hc : c ∈ actualInitialDiagram m I := by
        by_contra hc
        have hn := (inheritedDivisionOwner_eq_none_iff m I c).mpr hc
        rw [ho] at hn
        cases hn
      simp only [Option.some.injEq,Finset.sum_ite_eq,Finset.mem_univ,if_true]
      rw [inheritedFormalRemainder_coefficient_diagram m I B F c hc,add_zero,inheritedDivisionCoefficient_eq]
      exact (sub_add_cancel _ _).symm

/-- Actual membership in the new whole ideal and its unchanged diagram make the
same least-owner remainder vanish. The quotient supports use the same partition. -/
theorem inherited_formal_ideal_member_division (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily m I)
    (J : Ideal (MvPowerSeries (Fin n) ℂ))
    (hD : actualInitialDiagram m I = actualInitialDiagram m J)
    (hmem : ∀ a, B.series a ∈ J) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ J) :
    F = ∑ a : actualInitialVertices m I,
        inheritedFormalQuotient m I B F a * B.series a ∧
      ∀ (a : actualInitialVertices m I) (β : Fin n →₀ ℕ),
        MvPowerSeries.coeff β (inheritedFormalQuotient m I B F a) ≠ 0 →
          inheritedDivisionOwner m I (β + a.val) = some a := by
  have hs : (∑ a : actualInitialVertices m I,
      inheritedFormalQuotient m I B F a * inheritedVertexSeries m I B a) ∈ J :=
    J.sum_mem (fun a _ => J.mul_mem_left _ (hmem a))
  have hidentity := inherited_formal_vertex_division m I B F
  have hrem : inheritedFormalRemainder m I B F = F -
      ∑ a : actualInitialVertices m I,
        inheritedFormalQuotient m I B F a * inheritedVertexSeries m I B a := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hidentity.symm
  have hremJ : inheritedFormalRemainder m I B F ∈ J := by
    rw [hrem]
    exact J.sub_mem hF hs
  have hzero : inheritedFormalRemainder m I B F = 0 := by
    apply eq_zero_of_mem_of_diagram_coefficients_zero m J _ hremJ
    intro c hc
    apply inheritedFormalRemainder_coefficient_diagram m I B F c
    rwa [hD]
  refine ⟨?_, fun a β hβ => inheritedFormalQuotient_support m I B F a β hβ⟩
  rw [hzero, add_zero] at hidentity
  exact hidentity

/-- The literal degree-first component of the same inherited series. -/
def inheritedInitialForm (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (a : actualInitialVertices MonomialOrder.degLex I) : MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.homogeneousComponent (normalExponentDegree a.val) (B.series a)

private theorem inheritedInitialForm_spec (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (a : actualInitialVertices MonomialOrder.degLex I) :
    ∃ hne : inheritedInitialForm I B a ≠ 0,
      actualInitialExponent MonomialOrder.degLex (inheritedInitialForm I B a) hne = a.val ∧
        MvPowerSeries.coeff a.val (inheritedInitialForm I B a) = 1 := by
  have hc : MvPowerSeries.coeff a.val (inheritedInitialForm I B a) = 1 := by
    rw [inheritedInitialForm, MvPowerSeries.coeff_homogeneousComponent,
      if_pos (by simp only [normalExponentDegree, Finsupp.degree_eq_sum])]
    exact B.monic a
  have hne : inheritedInitialForm I B a ≠ 0 := by
    intro h
    have h' := hc
    rw [h, map_zero] at h'
    exact zero_ne_one h'
  refine ⟨hne, ?_, hc⟩
  apply actualInitialExponent_eq_of_coefficients MonomialOrder.degLex _ hne a.val
    (by rw [hc]; exact one_ne_zero)
  intro β hβ
  rw [inheritedInitialForm, MvPowerSeries.coeff_homogeneousComponent]
  split_ifs
  · exact B.lower a β hβ
  · rfl

/-- Selected columns use the original least selected owner and the actual
homogeneous initial forms of the same inherited family. -/
def inheritedSelectedColumn (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (V : Set (actualInitialVertices MonomialOrder.degLex I))
    (α : Fin n →₀ ℕ) : MvPowerSeries (Fin n) ℂ :=
  if hα : α ∈ actualSelectedVertexDiagram I V then
    let a := actualSelectedVertexOwner I V α hα
    MvPowerSeries.monomial (α - a.val) 1 * inheritedInitialForm I B a
  else MvPowerSeries.monomial α 1

private theorem inheritedSelectedColumn_spec (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) (α : Fin n →₀ ℕ) :
    ∃ hne : inheritedSelectedColumn I B V α ≠ 0,
      actualInitialExponent MonomialOrder.degLex (inheritedSelectedColumn I B V α) hne = α ∧
        MvPowerSeries.coeff α (inheritedSelectedColumn I B V α) = 1 := by
  by_cases hα : α ∈ actualSelectedVertexDiagram I V
  · rw [inheritedSelectedColumn, dif_pos hα]
    dsimp only
    let a := actualSelectedVertexOwner I V α hα
    have ha : a.val ≤ α := (actualSelectedVertexOwner_spec I V α hα).2.1
    have hsum : α - a.val + a.val = α := tsub_add_cancel_of_le ha
    obtain ⟨hne, hmin, hc⟩ := inheritedInitialForm_spec I B a
    have hm := actualMonomial_ne_zero (α - a.val)
    refine ⟨mul_ne_zero hm hne, ?_, ?_⟩
    · rw [actualInitialExponent_mul MonomialOrder.degLex _ _ hm hne,
        actualInitialExponent_monomial, hmin, hsum]
    · have h := coeff_mul_actualInitialExponent MonomialOrder.degLex
        (MvPowerSeries.monomial (α - a.val) 1) (inheritedInitialForm I B a) hm hne
      rw [actualInitialExponent_monomial, hmin, hsum,
        MvPowerSeries.coeff_monomial_same, hc, one_mul] at h
      exact h
  · rw [inheritedSelectedColumn, dif_neg hα]
    exact ⟨actualMonomial_ne_zero α, actualInitialExponent_monomial MonomialOrder.degLex α,
      MvPowerSeries.coeff_monomial_same α 1⟩

/-- The inherited family supplies the actual unitriangular columns internally. -/
theorem inheritedSelectedColumn_triangular (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α (inheritedSelectedColumn I B V α) = 1 ∧
      ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn α →
        MvPowerSeries.coeff β (inheritedSelectedColumn I B V α) = 0 := by
  obtain ⟨hne, hmin, hc⟩ := inheritedSelectedColumn_spec I B V α
  refine ⟨hc, fun β hβ => ?_⟩
  apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _ hne β
  rwa [hmin]

private theorem inherited_monomial_homogeneous (α : Fin n →₀ ℕ) :
    (MvPowerSeries.monomial α (1 : ℂ)).IsHomogeneous (Finsupp.degree α) := by
  apply MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mpr
  apply MvPowerSeries.ext
  intro β
  rw [MvPowerSeries.coeff_homogeneousComponent]
  by_cases hβ : β = α
  · subst β
    rw [if_pos rfl]
  · simp only [MvPowerSeries.coeff_monomial, if_neg hβ, ite_self]

/-- Every selected column has precisely the degree of its labelled head. -/
theorem inheritedSelectedColumn_homogeneous (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : InheritedMonicFamily MonomialOrder.degLex I)
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) (α : Fin n →₀ ℕ) :
    (inheritedSelectedColumn I B V α).IsHomogeneous (Finsupp.degree α) := by
  by_cases hα : α ∈ actualSelectedVertexDiagram I V
  · rw [inheritedSelectedColumn, dif_pos hα]
    dsimp only
    let a := actualSelectedVertexOwner I V α hα
    have ha : a.val ≤ α := (actualSelectedVertexOwner_spec I V α hα).2.1
    have hd : Finsupp.degree (α - a.val) + Finsupp.degree a.val = Finsupp.degree α := by
      have h := congrArg Finsupp.degree (tsub_add_cancel_of_le ha)
      simpa only [Finsupp.degree_eq_weight_one, map_add] using h
    have hinit : (inheritedInitialForm I B a).IsHomogeneous (Finsupp.degree a.val) := by
      change (MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
        (B.series a)).IsHomogeneous (Finsupp.degree a.val)
      have hdegree : normalExponentDegree a.val = Finsupp.degree a.val := by
        simp only [normalExponentDegree, Finsupp.degree_eq_sum]
      rw [hdegree]
      intro δ hδ
      exact MvPowerSeries.isHomogeneous_homogeneousComponent (B.series a) (Finsupp.degree a.val) hδ
    have hp : (MvPowerSeries.monomial (α - a.val) (1 : ℂ) *
        inheritedInitialForm I B a).IsHomogeneous
        (Finsupp.degree (α - a.val) + Finsupp.degree a.val) :=
      MvPowerSeries.IsHomogeneous.mul (inherited_monomial_homogeneous (α - a.val)) hinit
    rw [hd] at hp
    exact hp
  · rw [inheritedSelectedColumn, dif_neg hα]
    exact inherited_monomial_homogeneous α

private theorem inherited_homogeneous_component_of_homogeneous (F : MvPowerSeries (Fin n) ℂ)
    (e d : ℕ) (hF : F.IsHomogeneous e) :
    MvPowerSeries.homogeneousComponent d F = if e = d then F else 0 := by
  by_cases he : e = d
  · rw [if_pos he, ← he]
    exact (MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp hF).symm
  · rw [if_neg he]
    apply MvPowerSeries.ext
    intro α
    rw [map_zero, MvPowerSeries.coeff_homogeneousComponent]
    split_ifs with hα
    · exact hF.coeff_eq_zero (by omega)
    · rfl

private theorem inheritedSelectedHomogeneousExpansion
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily MonomialOrder.degLex I)
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) (d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F.IsHomogeneous d) :
    ∃! c : normalExponentIndex n (d + 1) → ℂ,
      (∀ a, normalExponentDegree a.val ≠ d → c a = 0) ∧
        F = ∑ a, c a • inheritedSelectedColumn I B V a.val := by
  let E := actualTriangularJetEquiv n (d + 1) (fun a => inheritedSelectedColumn I B V a.val)
    (fun a => inheritedSelectedColumn_triangular I B V a.val)
  let b := E.symm (Ideal.Quotient.mk (genuineFormalVariables n ^ (d + 1)) F)
  have hjet := E.apply_symm_apply (Ideal.Quotient.mk (genuineFormalVariables n ^ (d + 1)) F)
  change Ideal.Quotient.mk (genuineFormalVariables n ^ (d + 1))
    (∑ a : normalExponentIndex n (d + 1), b a • inheritedSelectedColumn I B V a.val) =
      Ideal.Quotient.mk (genuineFormalVariables n ^ (d + 1)) F at hjet
  have hrem := Ideal.Quotient.eq.mp hjet
  have hcomponent : MvPowerSeries.homogeneousComponent d
      (∑ a : normalExponentIndex n (d + 1), b a • inheritedSelectedColumn I B V a.val) = F := by
    apply MvPowerSeries.ext
    intro α
    by_cases hα : Finsupp.degree α = d
    · rw [MvPowerSeries.coeff_homogeneousComponent, if_pos hα]
      have hα' : normalExponentDegree α < d + 1 := by
        simpa only [normalExponentDegree, ← Finsupp.degree_eq_sum, hα] using Nat.lt_succ_self d
      have hc := (mem_genuineFormalVariables_pow_iff_coefficients_zero n (d + 1) _).mp hrem α hα'
      exact sub_eq_zero.mp hc
    · rw [MvPowerSeries.coeff_homogeneousComponent, if_neg hα, hF.coeff_eq_zero hα]
  let c : normalExponentIndex n (d + 1) → ℂ :=
    fun a => if normalExponentDegree a.val = d then b a else 0
  have hc : F = ∑ a, c a • inheritedSelectedColumn I B V a.val := by
    rw [← hcomponent, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_smul, inherited_homogeneous_component_of_homogeneous _ (Finsupp.degree a.val) d
      (inheritedSelectedColumn_homogeneous I B V a.val)]
    by_cases ha : normalExponentDegree a.val = d
    · have hd : Finsupp.degree a.val = d := by rwa [Finsupp.degree_eq_sum]
      simp only [c, if_pos ha, if_pos hd]
    · have hd : Finsupp.degree a.val ≠ d := by rwa [Finsupp.degree_eq_sum]
      simp only [c, if_neg ha, if_neg hd, smul_zero, zero_smul]
  refine ⟨c, ⟨fun a ha => by simp only [c, if_neg ha], hc⟩, ?_⟩
  intro c' hc'
  apply actualTriangularJetMap_injective (d + 1)
    (fun a => inheritedSelectedColumn I B V a.val)
    (fun a => inheritedSelectedColumn_triangular I B V a.val)
  change Ideal.Quotient.mk (genuineFormalVariables n ^ (d + 1))
    (∑ a, c' a • inheritedSelectedColumn I B V a.val) =
      Ideal.Quotient.mk (genuineFormalVariables n ^ (d + 1))
        (∑ a, c a • inheritedSelectedColumn I B V a.val)
  rw [← hc'.2, ← hc]

/-- BM97(7.2)(2): EVERY homogeneous degree has the unique actual supported
column decomposition for EVERY degree prefix of the same inherited family.
No zero-remainder conclusion is made for members of the prefix-generated ideal. -/
theorem inheritedDegreePrefixHomogeneousExpansion
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : InheritedMonicFamily MonomialOrder.degLex I)
    (k d : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F.IsHomogeneous d) :
    ∃! c : normalExponentIndex n (d + 1) → ℂ,
      (∀ a, normalExponentDegree a.val ≠ d → c a = 0) ∧
        F = ∑ a, c a • inheritedSelectedColumn I B (actualDegreeBlockVertices I k) a.val :=
  inheritedSelectedHomogeneousExpansion I B (actualDegreeBlockVertices I k) d F hF

end

end Hironaka.HironakaActualRelativeStandardnessInheritedDivision

