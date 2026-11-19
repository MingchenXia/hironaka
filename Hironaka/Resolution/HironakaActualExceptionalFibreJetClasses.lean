import Hironaka.Resolution.HironakaActualFormalStandardMonomialHS
import Hironaka.Resolution.HironakaActualPointExceptionalFibreRadial
import Hironaka.Resolution.HironakaActualTangentInitialVertices
import Hironaka.Resolution.HironakaStrictFilteredHilbertSamuel
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Literal exceptional-power classes in actual finite strict jets

Whole exceptional-fibre ideal equality supplies actual nilpotent Nakayama
generation of the SAME displayed monomial classes. The total degree bound is
proved from literal monomial annihilation in the genuine jet quotient.
Numerical dimension arguments are applied only after this concrete map and
its actual surjectivity have been constructed. The dehomogenized whole ideal's
own differential/projection cylinder computes its actual source cardinality;
the genuine radial HS bound closes the equality-case injectivity argument
without an extra cylinder or directrix premise on the original ideal.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualExceptionalFibreJetClasses
noncomputable section

open HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualOriginalFormalHSTransfer HironakaActualFormalStandardMonomialHS
  HironakaActualPointExceptionalFibre HironakaActualPointExceptionalFibreRadial
  HironakaActualTangentInitialVertices HironakaStrictFilteredHilbertSamuel

section NilpotentGeneration
variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Finite nilpotent Nakayama retains the original lifts and every literal iterate. -/
theorem span_iterates_eq_top_of_nilpotent (T : M →ₗ[K] M) (v : ι → M) (q : ℕ)
    (hnil : T ^ q = 0)
    (hmod : Submodule.span K (range v) ⊔ LinearMap.range T = ⊤) :
    Submodule.span K (range (fun a : Fin q × ι => (T ^ a.1.val) (v a.2))) = ⊤ := by
  let W := Submodule.span K (range (fun a : Fin q × ι => (T ^ a.1.val) (v a.2)))
  have hgen (k : ℕ) (hk : k < q) (u : M)
      (hu : u ∈ Submodule.span K (range v)) : (T ^ k) u ∈ W := by
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨(⟨k, hk⟩, i), rfl⟩
    | zero => simpa only [map_zero] using W.zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using W.add_mem hx hy
    | smul c x _ hx => simpa only [map_smul] using W.smul_mem c hx
  have hdown : ∀ r k : ℕ, k + r = q → ∀ x : M, (T ^ k) x ∈ W := by
    intro r
    induction r with
    | zero =>
      intro k hk x
      have he : k = q := by omega
      subst k
      rw [hnil, LinearMap.zero_apply]
      exact W.zero_mem
    | succ r ih =>
      intro k hk x
      have hx : x ∈ Submodule.span K (range v) ⊔ LinearMap.range T := by
        rw [hmod]
        trivial
      obtain ⟨u, hu, z, ⟨y, rfl⟩, he⟩ := Submodule.mem_sup.mp hx
      rw [← he, map_add]
      apply W.add_mem (hgen k (by omega) u hu)
      have hy := ih (k+1) (by omega) y
      simpa only [pow_succ, Module.End.mul_apply] using hy
  apply top_unique
  intro x _
  simpa only [pow_zero, Module.End.one_apply] using hdown q 0 (by omega) x

end NilpotentGeneration

variable {n : ℕ}

/-- Literal whole formal q-jet quotient; q=0 is the zero quotient. -/
abbrev actualExceptionalJetQuotient (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :=
  MvPowerSeries (Fin n) ℂ ⧸ (I ⊔ genuineFormalVariables n ^ q)

/-- The entire ideal on the actual exceptional fibre. -/
def actualExceptionalFibreIdeal (J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) :
    Ideal (MvPowerSeries (Fin n) ℂ) := J ⊔ Ideal.span {MvPowerSeries.X e}

/-- Multiplication by the literal exceptional class on the actual q-jet quotient. -/
def actualExceptionalJetOperator (I : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (q : ℕ) :
    actualExceptionalJetQuotient I q →ₗ[ℂ] actualExceptionalJetQuotient I q :=
  LinearMap.mulLeft ℂ (Ideal.Quotient.mk (I ⊔ genuineFormalVariables n ^ q) (MvPowerSeries.X e))

private theorem actualExceptionalJetOperator_pow_apply (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (q a : ℕ) (z : actualExceptionalJetQuotient I q) :
    (actualExceptionalJetOperator I e q ^ a) z =
      (Ideal.Quotient.mk (I ⊔ genuineFormalVariables n ^ q) (MvPowerSeries.X e)) ^ a * z := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change _ * (_ ^ a * z) = _
    rw [← mul_assoc, ← pow_succ']

private theorem formal_monomial_mem_power (a : Fin n →₀ ℕ) (q : ℕ)
    (ha : q ≤ normalExponentDegree a) :
    MvPowerSeries.monomial a (1 : ℂ) ∈ genuineFormalVariables n ^ q := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
  intro b hb
  have hne : b ≠ a := by intro h; subst b; omega
  simp only [MvPowerSeries.coeff_monomial, if_neg hne]

/-- Genuine total-jet nilpotence, proved from the actual monomial ideal power. -/
theorem actualExceptionalJetOperator_nilpotent (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (q : ℕ) : actualExceptionalJetOperator I e q ^ q = 0 := by
  apply LinearMap.ext
  intro z
  rw [actualExceptionalJetOperator_pow_apply]
  have hz : (Ideal.Quotient.mk (I ⊔ genuineFormalVariables n ^ q) (MvPowerSeries.X e)) ^ q = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, MvPowerSeries.X_pow_eq]
    apply Ideal.mem_sup_right
    apply formal_monomial_mem_power
    simp [normalExponentDegree]
  rw [hz, zero_mul, LinearMap.zero_apply]

/-- The actual quotient projection uses the entire exceptional-fibre equality. -/
def actualExceptionalJetProjection (I J : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (q : ℕ)
    (hIJ : actualExceptionalFibreIdeal I e = actualExceptionalFibreIdeal J e) :
    actualExceptionalJetQuotient I q →ₗ[ℂ]
      actualExceptionalJetQuotient (actualExceptionalFibreIdeal J e) q :=
  (Ideal.Quotient.factorₐ ℂ (sup_le_sup
    (show I ≤ actualExceptionalFibreIdeal J e by rw [← hIJ]; exact le_sup_left) le_rfl)).toLinearMap

@[simp] theorem actualExceptionalJetProjection_mk (I J : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (q : ℕ)
    (hIJ : actualExceptionalFibreIdeal I e = actualExceptionalFibreIdeal J e)
    (F : MvPowerSeries (Fin n) ℂ) :
    actualExceptionalJetProjection I J e q hIJ (Ideal.Quotient.mk _ F) =
      Ideal.Quotient.mk _ F := rfl

/-- The whole exceptional fibre kernel is exactly multiplication by the same exceptional class. -/
theorem actualExceptionalJetProjection_kernel (I J : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (q : ℕ)
    (hIJ : actualExceptionalFibreIdeal I e = actualExceptionalFibreIdeal J e) :
    LinearMap.ker (actualExceptionalJetProjection I J e q hIJ) =
      LinearMap.range (actualExceptionalJetOperator I e q) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hF : F ∈ actualExceptionalFibreIdeal J e ⊔ genuineFormalVariables n ^ q :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    rw [← hIJ] at hF
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hF
    obtain ⟨i, hi, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hw
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    change Ideal.Quotient.mk _ (MvPowerSeries.X e * a) = Ideal.Quotient.mk _ (i + MvPowerSeries.X e * a + z)
    apply Ideal.Quotient.eq.mpr
    have he : MvPowerSeries.X e * a - (i + MvPowerSeries.X e * a + z) = -(i+z) := by abel
    rw [he]
    exact (I ⊔ genuineFormalVariables n ^ q).neg_mem
      ((I ⊔ genuineFormalVariables n ^ q).add_mem (Ideal.mem_sup_left hi) (Ideal.mem_sup_right hz))
  · rintro x ⟨y, rfl⟩
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change MvPowerSeries.X e * F ∈ actualExceptionalFibreIdeal J e ⊔ genuineFormalVariables n ^ q
    exact Ideal.mem_sup_left (Ideal.mem_sup_right
      ((Ideal.span {MvPowerSeries.X e}).mul_mem_right F (Ideal.mem_span_singleton_self _)))

private def fibreMonomialLift (I J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (q : ℕ)
    (β : actualStandardIndex n (actualExceptionalFibreIdeal J e) q) :
    actualExceptionalJetQuotient I q := Ideal.Quotient.mk _ (MvPowerSeries.monomial β.val.val 1)

/-- The actual fibre monomial equivalence supplies the genuine Nakayama relation for these unchanged lifts. -/
theorem actualExceptionalJet_fibre_generators (I J : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (q : ℕ)
    (hIJ : actualExceptionalFibreIdeal I e = actualExceptionalFibreIdeal J e) :
    Submodule.span ℂ (range (fibreMonomialLift I J e q)) ⊔
      LinearMap.range (actualExceptionalJetOperator I e q) = ⊤ := by
  let W := Submodule.span ℂ (range (fibreMonomialLift I J e q))
  let π := actualExceptionalJetProjection I J e q hIJ
  apply top_unique
  intro x _
  obtain ⟨c, hc⟩ := actualStandardQuotientMap_surjective (actualExceptionalFibreIdeal J e) q (π x)
  let u : actualExceptionalJetQuotient I q :=
    Ideal.Quotient.mk _ (actualStandardLift n (actualExceptionalFibreIdeal J e) q c)
  have hu : u ∈ W := by
    change (Ideal.Quotient.mkₐ ℂ (I ⊔ genuineFormalVariables n ^ q))
      (∑ β : actualStandardIndex n (actualExceptionalFibreIdeal J e) q,
        MvPowerSeries.monomial β.val.val (c β)) ∈ W
    rw [map_sum]
    apply W.sum_mem
    intro β _
    have he : MvPowerSeries.monomial β.val.val (c β) =
        c β • MvPowerSeries.monomial β.val.val (1 : ℂ) := by
      simpa only [smul_eq_mul,mul_one] using
        (MvPowerSeries.monomial β.val.val).map_smul (c β) (1 : ℂ)
    rw [he, map_smul]
    exact W.smul_mem _ (Submodule.subset_span ⟨β, rfl⟩)
  have hπu : π u = π x := hc
  have hker : x-u ∈ LinearMap.ker π := by
    change π (x-u) = 0
    rw [map_sub, hπu, sub_self]
  have hrange : x-u ∈ LinearMap.range (actualExceptionalJetOperator I e q) := by
    rw [← actualExceptionalJetProjection_kernel I J e q hIJ]
    exact hker
  exact Submodule.mem_sup.mpr ⟨u, hu, x-u, hrange, by abel⟩

/-- The exact finite total-bounded family; every beta is a true fibre standard exponent. -/
abbrev actualExceptionalJetIndex (J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (q : ℕ) :=
  Σ a : Fin q, actualStandardIndex n (actualExceptionalFibreIdeal J e) (q-a.val)

/-- The unchanged literal t^a beta class in the actual whole target jet quotient. -/
def actualExceptionalJetVector (I J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (q : ℕ)
    (a : actualExceptionalJetIndex J e q) : actualExceptionalJetQuotient I q :=
  Ideal.Quotient.mk _ ((MvPowerSeries.X e) ^ a.1.val * MvPowerSeries.monomial a.2.val.val 1)

/-- The concrete map is constructed before any rank or independence hypothesis. -/
def actualExceptionalJetMap (I J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (q : ℕ) :
    (actualExceptionalJetIndex J e q →₀ ℂ) →ₗ[ℂ] actualExceptionalJetQuotient I q :=
  Finsupp.linearCombination ℂ (actualExceptionalJetVector I J e q)

@[simp] theorem actualExceptionalJetMap_single (I J : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (q : ℕ) (a : actualExceptionalJetIndex J e q) :
    actualExceptionalJetMap I J e q (Finsupp.single a 1) = actualExceptionalJetVector I J e q a := by
  simp [actualExceptionalJetMap]

private theorem exceptional_monomial_high_degree_zero (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (q a : ℕ) (β : Fin n →₀ ℕ) (h : q ≤ a + normalExponentDegree β) :
    (Ideal.Quotient.mk (I ⊔ genuineFormalVariables n ^ q)
      ((MvPowerSeries.X e)^a * MvPowerSeries.monomial β 1)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_sup_right
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]
  apply formal_monomial_mem_power
  simpa [normalExponentDegree, Finsupp.add_apply, Finset.sum_add_distrib] using h

/-- TRUE whole fibre equality produces surjectivity of this SAME total-bounded map. -/
theorem actualExceptionalJetMap_surjective (I J : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (q : ℕ)
    (hIJ : actualExceptionalFibreIdeal I e = actualExceptionalFibreIdeal J e) :
    Function.Surjective (actualExceptionalJetMap I J e q) := by
  rw [← LinearMap.range_eq_top, actualExceptionalJetMap, Finsupp.range_linearCombination]
  have hspan := span_iterates_eq_top_of_nilpotent (actualExceptionalJetOperator I e q)
    (fibreMonomialLift I J e q) q (actualExceptionalJetOperator_nilpotent I e q)
    (actualExceptionalJet_fibre_generators I J e q hIJ)
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨⟨a, β⟩, rfl⟩
  change (actualExceptionalJetOperator I e q ^ a.val) (fibreMonomialLift I J e q β) ∈ _
  rw [actualExceptionalJetOperator_pow_apply]
  change Ideal.Quotient.mk _ ((MvPowerSeries.X e)^a.val * MvPowerSeries.monomial β.val.val 1) ∈ _
  by_cases h : a.val + normalExponentDegree β.val.val < q
  · let β' : actualStandardIndex n (actualExceptionalFibreIdeal J e) (q-a.val) :=
      ⟨⟨β.val.val, by omega⟩, β.property⟩
    exact Submodule.subset_span ⟨⟨a, β'⟩, rfl⟩
  · rw [exceptional_monomial_high_degree_zero I e q a.val β.val.val (by omega)]
    exact Submodule.zero_mem _

/-- The source cardinal is computed from its actual finite sigma index, with no target dimension premise. -/
theorem card_actualExceptionalJetIndex (J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (q : ℕ) :
    Fintype.card (actualExceptionalJetIndex J e q) =
      ∑ a : Fin q, Fintype.card (actualStandardIndex n (actualExceptionalFibreIdeal J e) (q-a.val)) :=
  Fintype.card_sigma

/-- The unconditional whole exceptional-fibre dictionary gives the actual point strict q-jet spanning map. -/
theorem actual_point_strict_exceptional_jetMap_surjective
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) (q : ℕ) :
    Function.Surjective (actualExceptionalJetMap
      (HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b)
      (actualDehomogenizedPointInitialConeIdeal K e b) e q) :=
  actualExceptionalJetMap_surjective _ _ e q
    (actual_point_strict_exceptional_fibre_eq_dehomogenized_initial_cone K e b)

private theorem exponent_split (e : Fin n) (α : Fin n →₀ ℕ) :
    Finsupp.single e (α e) + α.erase e = α := by
  ext i
  by_cases hi : i=e
  · subst i
    simp
  · simp [hi]

private theorem degree_single_add (e : Fin n) (a : ℕ) (β : Fin n →₀ ℕ) :
    normalExponentDegree (Finsupp.single e a + β) = a + normalExponentDegree β := by
  simp [normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib]

private theorem degree_split (e : Fin n) (α : Fin n →₀ ℕ) :
    normalExponentDegree α = α e + normalExponentDegree (α.erase e) := by
  simpa only [degree_single_add] using
    (congrArg normalExponentDegree (exponent_split e α)).symm

private theorem erase_single_add (e : Fin n) (a : ℕ) (β : Fin n →₀ ℕ)
    (hβ : β e=0) : (Finsupp.single e a + β).erase e=β := by
  ext i
  by_cases hi : i=e
  · subst i
    simp [hβ]
  · simp [hi]

/-- A true standard fibre exponent is transverse, because the entire fibre ideal contains Xe. -/
theorem actualExceptionalFibre_standard_exponent_coordinate_zero
    (J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (q : ℕ)
    (β : actualStandardIndex n (actualExceptionalFibreIdeal J e) q) : β.val.val e=0 := by
  by_contra hne
  have hpos : 1 ≤ β.val.val e := Nat.one_le_iff_ne_zero.mpr hne
  have hbase : Finsupp.single e 1 ∈
      actualInitialDiagram MonomialOrder.degLex (actualExceptionalFibreIdeal J e) := by
    refine ⟨MvPowerSeries.monomial (Finsupp.single e 1) 1, ?_,
      actualMonomial_ne_zero _, actualInitialExponent_monomial _ _⟩
    change MvPowerSeries.X e ∈ J ⊔ Ideal.span {MvPowerSeries.X e}
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  exact β.property (actualInitialDiagram_upper _ _ _ _ hbase
    (Finsupp.single_le_iff.mpr hpos))

/-- The explicit map from the total-bounded labels to genuine source standard exponents. -/
def actualExceptionalJetIndexEquivSource
    (K J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (q : ℕ)
    (hCyl : ∀ α : Fin n →₀ ℕ,
      α ∉ actualInitialDiagram MonomialOrder.degLex K ↔
        α.erase e ∉ actualInitialDiagram MonomialOrder.degLex (actualExceptionalFibreIdeal J e)) :
    actualExceptionalJetIndex J e q ≃ actualStandardIndex n K q := by
  let f : actualExceptionalJetIndex J e q → actualStandardIndex n K q := fun a =>
    ⟨⟨Finsupp.single e a.1.val + a.2.val.val, by
      rw [degree_single_add]
      have hβ := a.2.val.property
      have ha := a.1.isLt
      omega⟩, by
      apply (hCyl _).mpr
      rw [erase_single_add e a.1.val a.2.val.val
        (actualExceptionalFibre_standard_exponent_coordinate_zero J e _ a.2)]
      exact a.2.property⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨a,β⟩ := x
    obtain ⟨c,γ⟩ := y
    have he : Finsupp.single e a.val + β.val.val = Finsupp.single e c.val + γ.val.val :=
      congrArg (fun z : actualStandardIndex n K q => z.val.val) hxy
    have ha : a=c := by
      apply Fin.ext
      have h := congrArg (fun α : Fin n →₀ ℕ => α e) he
      simpa only [Finsupp.add_apply,Finsupp.single_eq_same,
        actualExceptionalFibre_standard_exponent_coordinate_zero J e _ β,
        actualExceptionalFibre_standard_exponent_coordinate_zero J e _ γ,add_zero] using h
    subst c
    apply congrArg (Sigma.mk a)
    exact Subtype.ext (Subtype.ext (add_left_cancel he))
  · intro α
    have hd : α.val.val e + normalExponentDegree (α.val.val.erase e) < q := by
      rw [← degree_split]
      exact α.val.property
    let a : Fin q := ⟨α.val.val e,by omega⟩
    let β : actualStandardIndex n (actualExceptionalFibreIdeal J e) (q-a.val) :=
      ⟨⟨α.val.val.erase e,by dsimp only [a]; omega⟩,(hCyl α.val.val).mp α.property⟩
    refine ⟨⟨a,β⟩,?_⟩
    exact Subtype.ext (Subtype.ext (exponent_split e α.val.val))

/-- The true exponent bijection computes the source cardinal, rather than assuming a target basis. -/
theorem card_actualExceptionalJetIndex_eq_source_hs
    (K J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (ℓ : ℕ)
    (hCyl : ∀ α : Fin n →₀ ℕ,
      α ∉ actualInitialDiagram MonomialOrder.degLex K ↔
        α.erase e ∉ actualInitialDiagram MonomialOrder.degLex (actualExceptionalFibreIdeal J e)) :
    Fintype.card (actualExceptionalJetIndex J e (ℓ+1)) =
      genuineFormalHilbertSamuelValue n K ℓ := by
  rw [genuineFormalHilbertSamuelValue_eq_card_standardIndex]
  exact Fintype.card_congr (actualExceptionalJetIndexEquivSource K J e (ℓ+1) hCyl)

private theorem finite_actualExceptionalJetQuotient
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :
    Module.Finite ℂ (actualExceptionalJetQuotient I q) :=
  finiteDimensional_formal_quotient_sup_variables_pow n q I

/-- A numerical equality is used only after constructing this actual surjective map. -/
theorem actualExceptionalJetMap_bijective_of_source_hs_eq
    (I K J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (ℓ : ℕ)
    (hIJ : actualExceptionalFibreIdeal I e = actualExceptionalFibreIdeal J e)
    (hCyl : ∀ α : Fin n →₀ ℕ,
      α ∉ actualInitialDiagram MonomialOrder.degLex K ↔
        α.erase e ∉ actualInitialDiagram MonomialOrder.degLex (actualExceptionalFibreIdeal J e))
    (hHS : genuineFormalHilbertSamuelValue n I ℓ = genuineFormalHilbertSamuelValue n K ℓ) :
    Function.Bijective (actualExceptionalJetMap I J e (ℓ+1)) := by
  let := finite_actualExceptionalJetQuotient I (ℓ+1)
  have hs := actualExceptionalJetMap_surjective I J e (ℓ+1) hIJ
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr hs,hs⟩
  rw [Module.finrank_finsupp_self,card_actualExceptionalJetIndex_eq_source_hs K J e ℓ hCyl]
  exact hHS.symm

/-- This is an assertion about the kernel of the SAME displayed vector map. -/
theorem actualExceptionalJetMap_eq_zero_iff
    (I K J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (ℓ : ℕ)
    (hIJ : actualExceptionalFibreIdeal I e = actualExceptionalFibreIdeal J e)
    (hCyl : ∀ α : Fin n →₀ ℕ,
      α ∉ actualInitialDiagram MonomialOrder.degLex K ↔
        α.erase e ∉ actualInitialDiagram MonomialOrder.degLex (actualExceptionalFibreIdeal J e))
    (hHS : genuineFormalHilbertSamuelValue n I ℓ = genuineFormalHilbertSamuelValue n K ℓ)
    (c : actualExceptionalJetIndex J e (ℓ+1) →₀ ℂ) :
    actualExceptionalJetMap I J e (ℓ+1) c=0 ↔ c=0 := by
  constructor
  · intro hc
    apply (actualExceptionalJetMap_bijective_of_source_hs_eq I K J e ℓ hIJ hCyl hHS).1
    simpa only [map_zero] using hc
  · intro hc
    rw [hc,map_zero]

/-- Derivative stability of the actual WHOLE ideal makes its actual diagram a cylinder. -/
theorem actualInitialDiagram_erase_iff_of_pderiv_stable
    (m : MonomialOrder (Fin n)) (J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n)
    (hD : ∀ F ∈ J, MvPowerSeries.pderiv ℂ e F ∈ J) (α : Fin n →₀ ℕ) :
    α ∈ actualInitialDiagram m J ↔ α.erase e ∈ actualInitialDiagram m J := by
  constructor
  · intro hα
    obtain ⟨a,ha,hle⟩ := (mem_actualInitialDiagram_iff_vertex_le m J α).mp hα
    apply (mem_actualInitialDiagram_iff_vertex_le m J (α.erase e)).mpr
    refine ⟨a,ha,?_⟩
    have haz : a e=0 :=
      actualInitialVertex_coordinate_eq_zero_of_pderiv_stable m J e hD ⟨a,ha⟩
    intro i
    by_cases hi : i=e
    · subst i
      simp [haz]
    · simpa only [Finsupp.erase_ne hi] using hle i
  · intro hα
    apply actualInitialDiagram_upper m J (α.erase e) α hα
    intro i
    by_cases hi : i=e
    · subst i
      simp
    · simp only [Finsupp.erase_ne hi,le_refl]

/-- Projection of the entire fibre ideal preserves every transverse leading exponent. -/
theorem actualInitialDiagram_fibre_iff_of_projection
    (m : MonomialOrder (Fin n)) (J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n)
    (hσ : Ideal.map (actualPointExceptionalProjection e).toRingHom J ≤ J)
    (β : Fin n →₀ ℕ) (hβ : β e=0) :
    β ∈ actualInitialDiagram m (actualExceptionalFibreIdeal J e) ↔
      β ∈ actualInitialDiagram m J := by
  constructor
  · rintro ⟨F,hF,hne,hlead⟩
    obtain ⟨G,hG,Z,hZ,hF⟩ := Submodule.mem_sup.mp hF
    obtain ⟨A,rfl⟩ := Ideal.mem_span_singleton.mp hZ
    have hσF : actualPointExceptionalProjection e F=actualPointExceptionalProjection e G := by
      rw [← hF,map_add,map_mul,actualPointExceptionalProjection_X,if_pos rfl,zero_mul,add_zero]
    have hmem : actualPointExceptionalProjection e F ∈ J := by
      rw [hσF]
      exact hσ (Ideal.mem_map_of_mem _ hG)
    have hc : MvPowerSeries.coeff β (actualPointExceptionalProjection e F) ≠ 0 := by
      rw [coeff_actualPointExceptionalProjection,if_pos hβ,← hlead]
      exact (actualInitialExponent_spec m F hne).1
    have hne' : actualPointExceptionalProjection e F ≠ 0 := by
      intro hz
      exact hc (by rw [hz,map_zero])
    refine ⟨actualPointExceptionalProjection e F,hmem,hne',?_⟩
    apply actualInitialExponent_eq_of_coefficients m _ hne' β hc
    intro γ hγ
    rw [coeff_actualPointExceptionalProjection]
    by_cases hγe : γ e=0
    · rw [if_pos hγe]
      apply coeff_eq_zero_of_lt_actualInitialExponent m F hne γ
      rwa [hlead]
    · rw [if_neg hγe]
  · rintro ⟨F,hF,hne,hlead⟩
    exact ⟨F,Ideal.mem_sup_left hF,hne,hlead⟩

/-- The actual dehomogenized cone is a cylinder without any direction or HS assumption. -/
theorem actual_dehomogenized_initial_cone_diagram_cylinder
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ)
    (α : Fin n →₀ ℕ) :
    α ∉ actualInitialDiagram MonomialOrder.degLex (actualDehomogenizedPointInitialConeIdeal K e b) ↔
      α.erase e ∉ actualInitialDiagram MonomialOrder.degLex
        (actualExceptionalFibreIdeal (actualDehomogenizedPointInitialConeIdeal K e b) e) := by
  apply not_congr
  exact (actualInitialDiagram_erase_iff_of_pderiv_stable _ _ e
    (pderiv_mem_actualDehomogenizedPointInitialConeIdeal K e b) α).trans
      (actualInitialDiagram_fibre_iff_of_projection _ _ e
        (le_of_eq (map_actualDehomogenizedPointInitialConeIdeal_projection K e b))
        (α.erase e) (by simp)).symm

/-- Actual source cardinal = whole dehomogenized-cone HS; no original-cone cylinder is assumed. -/
theorem card_actualExceptionalJetIndex_dehomogenized
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) (ℓ : ℕ) :
    Fintype.card (actualExceptionalJetIndex (actualDehomogenizedPointInitialConeIdeal K e b) e (ℓ+1)) =
      genuineFormalHilbertSamuelValue n (actualDehomogenizedPointInitialConeIdeal K e b) ℓ :=
  card_actualExceptionalJetIndex_eq_source_hs _ _ e ℓ
    (actual_dehomogenized_initial_cone_diagram_cylinder K e b)

/-- The radial bound and HS equality force equality of the two actual dimensions. -/
theorem actual_point_strict_exceptional_jet_source_dimension_eq_of_hs_eq
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) (ℓ : ℕ)
    (hHS : genuineFormalHilbertSamuelValue n
      (HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b) ℓ =
      genuineFormalHilbertSamuelValue n K ℓ) :
    Fintype.card (actualExceptionalJetIndex (actualDehomogenizedPointInitialConeIdeal K e b) e (ℓ+1)) =
      genuineFormalHilbertSamuelValue n
        (HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b) ℓ := by
  apply le_antisymm
  · rw [card_actualExceptionalJetIndex_dehomogenized, hHS]
    exact genuineFormalHilbertSamuelValue_actualDehomogenizedPointInitialConeIdeal_le K e b ℓ
  · have h := LinearMap.finrank_le_finrank_of_surjective
        (actual_point_strict_exceptional_jetMap_surjective K e b (ℓ+1))
    simpa only [Module.finrank_finsupp_self,genuineFormalHilbertSamuelValue] using h

/-- TRUE whole fibre generation + TRUE radial/card formulas make this SAME map bijective. -/
theorem actual_point_strict_exceptional_jetMap_bijective_of_hs_eq
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) (ℓ : ℕ)
    (hHS : genuineFormalHilbertSamuelValue n
      (HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b) ℓ =
      genuineFormalHilbertSamuelValue n K ℓ) :
    Function.Bijective (actualExceptionalJetMap
      (HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b)
      (actualDehomogenizedPointInitialConeIdeal K e b) e (ℓ+1)) := by
  let := finite_actualExceptionalJetQuotient
    (HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b) (ℓ+1)
  have hs := actual_point_strict_exceptional_jetMap_surjective K e b (ℓ+1)
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr hs,hs⟩
  rw [Module.finrank_finsupp_self]
  exact actual_point_strict_exceptional_jet_source_dimension_eq_of_hs_eq K e b ℓ hHS

/-- Equality case forbids every nonzero coefficient vector for these very classes. -/
theorem actual_point_strict_exceptional_jetMap_eq_zero_iff
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) (ℓ : ℕ)
    (hHS : genuineFormalHilbertSamuelValue n
      (HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b) ℓ =
      genuineFormalHilbertSamuelValue n K ℓ)
    (c : actualExceptionalJetIndex (actualDehomogenizedPointInitialConeIdeal K e b) e (ℓ+1) →₀ ℂ) :
    actualExceptionalJetMap
      (HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b)
      (actualDehomogenizedPointInitialConeIdeal K e b) e (ℓ+1) c=0 ↔ c=0 := by
  constructor
  · intro hc
    apply (actual_point_strict_exceptional_jetMap_bijective_of_hs_eq K e b ℓ hHS).1
    simpa only [map_zero] using hc
  · intro hc
    rw [hc,map_zero]

/-- The actual finite sigma-index splits at exponent zero; all remaining labels shift by one. -/
theorem card_actualExceptionalJetIndex_succ
    (J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (q : ℕ) :
    Fintype.card (actualExceptionalJetIndex J e (q+1)) =
      Fintype.card (actualStandardIndex n (actualExceptionalFibreIdeal J e) (q+1)) +
        Fintype.card (actualExceptionalJetIndex J e q) := by
  rw [card_actualExceptionalJetIndex,Fin.sum_univ_succ,card_actualExceptionalJetIndex]
  simp only [Fin.val_zero,Nat.sub_zero,Fin.val_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  have hsub : q+1-(a.val+1)=q-a.val := by omega
  simp only [hsub]

/-- Full HS equality implies the genuine exceptional-symbol cancellation in the WHOLE strict ideal. -/
theorem actual_point_strict_regular_symbol_of_hs_eq
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ)
    (hHS : ∀ ℓ : ℕ, genuineFormalHilbertSamuelValue n
      (HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b) ℓ =
      genuineFormalHilbertSamuelValue n K ℓ) :
    ∀ r : ℕ, ∀ F ∈ genuineFormalVariables n ^ r,
      MvPowerSeries.X e * F ∈
        (HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b) ⊔
          genuineFormalVariables n ^ (r+2) →
      F ∈ (HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b) ⊔
        genuineFormalVariables n ^ (r+1) := by
  let I := HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b
  let J := actualDehomogenizedPointInitialConeIdeal K e b
  have hfinite (q : ℕ) : Module.Finite ℂ (actualExceptionalJetQuotient I (q+1)) :=
    finite_actualExceptionalJetQuotient I (q+1)
  have hXe : (MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ) ∈ genuineFormalVariables n :=
    Ideal.subset_span ⟨e,rfl⟩
  apply (regular_symbol_iff_finrank_quotient_recurrence ℂ I (genuineFormalVariables n)
    (MvPowerSeries.X e) hXe hfinite).mpr
  intro q
  have hdim0 := actual_point_strict_exceptional_jet_source_dimension_eq_of_hs_eq K e b q (hHS q)
  have hdim1 := actual_point_strict_exceptional_jet_source_dimension_eq_of_hs_eq K e b (q+1) (hHS (q+1))
  have hrec := card_actualExceptionalJetIndex_succ J e (q+1)
  rw [hdim0,hdim1] at hrec
  have hfibre : actualExceptionalFibreIdeal I e=actualExceptionalFibreIdeal J e :=
    actual_point_strict_exceptional_fibre_eq_dehomogenized_initial_cone K e b
  have hcount := genuineFormalHilbertSamuelValue_eq_card_standardIndex
    (actualExceptionalFibreIdeal J e) (q+1)
  change Module.finrank ℂ (MvPowerSeries (Fin n) ℂ ⧸
    (actualExceptionalFibreIdeal I e ⊔ genuineFormalVariables n ^ ((q+1)+1))) +
    genuineFormalHilbertSamuelValue n I q = genuineFormalHilbertSamuelValue n I (q+1)
  rw [hfibre]
  rw [← hcount] at hrec
  exact hrec.symm

end
end Hironaka.HironakaActualExceptionalFibreJetClasses
