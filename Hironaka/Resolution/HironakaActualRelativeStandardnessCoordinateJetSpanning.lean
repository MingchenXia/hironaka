import Hironaka.Resolution.HironakaActualExceptionalFibreJetClasses
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Literal standard monomials span actual jets through several coordinate axes

This is a generic whole-fibre algebra interface. The explicit hypotheses are
`J ⊔ I_L = Q ⊔ I_L` and a coordinate-cylinder property of the WHOLE diagram of
`Q`. The map is the EXISTING `actualStandardLift` followed by the quotient for
`J`; its source has precisely the existing actual standard-exponent labels.

Surjectivity is proved by genuine finite coordinate-word nilpotence. Only
afterwards do genuine HS equalities give injectivity of that same map. The
dehomogenized-cone consumer internally uses the actual radial HS bound.

For an actual normal blowup the required mod-tangent-and-exceptional fibre
dictionary and its model cylinder remain separate original-data producers.
This file does not supply them, individual canonical normalized orders, a
normal-only chart transition, or an iterated analytic HS presentation.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualRelativeStandardnessCoordinateJetSpanning

noncomputable section

open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalStandardMonomialHS
  HironakaActualFormalCoordinatePowerDivision HironakaActualPointExceptionalFibre
  HironakaActualPointExceptionalFibreRadial HironakaActualExceptionalFibreJetClasses

/-- Finite coordinate words are used only to prove generation, not as repeated
labels in any later cardinality calculation. -/
theorem nilpotent_coordinate_words_span_top
    {ι M : Type*} [CommRing M] [Algebra ℂ M]
    (W : Submodule ℂ M) (v : ι → M) (q : ℕ)
    (hstable : ∀ i : ι, ∀ u ∈ W, v i * u ∈ W)
    (hnil : ∀ s : List ι, s.length = q → (s.map v).prod = 0)
    (hmod : ∀ x : M, ∃ u ∈ W, ∃ r : ℕ, ∃ i : Fin r → ι,
      ∃ y : Fin r → M, x = u + ∑ k : Fin r, v (i k) * y k) : W = ⊤ := by
  have hword : ∀ s : List ι, ∀ u ∈ W, (s.map v).prod * u ∈ W := by
    intro s
    induction s with
    | nil =>
        intro u hu
        simpa only [List.map_nil, List.prod_nil, one_mul] using hu
    | cons i s ih =>
        intro u hu
        simpa only [List.map_cons, List.prod_cons, mul_assoc] using
          hstable i _ (ih u hu)
  have hdown : ∀ r : ℕ, ∀ s : List ι, s.length + r = q →
      ∀ x : M, (s.map v).prod * x ∈ W := by
    intro r
    induction r with
    | zero =>
        intro s hs x
        rw [hnil s (by omega), zero_mul]
        exact W.zero_mem
    | succ r ih =>
        intro s hs x
        obtain ⟨u, hu, m, i, y, hx⟩ := hmod x
        rw [hx, mul_add, Finset.mul_sum]
        apply W.add_mem (hword s u hu)
        apply W.sum_mem
        intro k _
        have hk := ih (i k :: s) (by simp only [List.length_cons]; omega) (y k)
        simpa only [List.map_cons, List.prod_cons, mul_left_comm, mul_assoc] using hk
  apply top_unique
  intro x _
  simpa only [List.map_nil, List.prod_nil, one_mul] using hdown q [] (by simp) x

variable {n : ℕ}

/-- The entire actual diagram ignores each listed coordinate. -/
def actualCoordinateDiagramCylinder
    (Q : Ideal (MvPowerSeries (Fin n) ℂ)) (L : Set (Fin n)) : Prop :=
  ∀ i ∈ L, ∀ α : Fin n →₀ ℕ,
    α ∈ actualInitialDiagram MonomialOrder.degLex Q ↔
      α.erase i ∈ actualInitialDiagram MonomialOrder.degLex Q

/-- Whole derivative stability of the comparison ideal supplies its diagram
cylinder through the existing actual vertex theorem. -/
theorem actualCoordinateDiagramCylinder_of_partial_stability
    (Q : Ideal (MvPowerSeries (Fin n) ℂ)) (L : Set (Fin n))
    (hD : ∀ i ∈ L, ∀ F ∈ Q, MvPowerSeries.pderiv ℂ i F ∈ Q) :
    actualCoordinateDiagramCylinder Q L := by
  intro i hi α
  exact actualInitialDiagram_erase_iff_of_pderiv_stable
    MonomialOrder.degLex Q i (hD i hi) α

/-- The concrete model map retains every literal existing standard monomial. -/
def actualStandardModelJetMap
    (J Q : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :
    (actualStandardIndex n Q q → ℂ) →ₗ[ℂ]
      (MvPowerSeries (Fin n) ℂ ⧸ (J ⊔ genuineFormalVariables n ^ q)) :=
  (Ideal.Quotient.mkₐ ℂ (J ⊔ genuineFormalVariables n ^ q)).toLinearMap.comp
    (actualStandardLift n Q q)

@[simp] theorem actualStandardModelJetMap_apply
    (J Q : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ)
    (c : actualStandardIndex n Q q → ℂ) :
    actualStandardModelJetMap J Q q c =
      Ideal.Quotient.mk (J ⊔ genuineFormalVariables n ^ q)
        (actualStandardLift n Q q c) := rfl

private theorem diagram_mono
    (I Q : Ideal (MvPowerSeries (Fin n) ℂ)) (hIQ : I ≤ Q) :
    actualInitialDiagram MonomialOrder.degLex I ⊆
      actualInitialDiagram MonomialOrder.degLex Q := by
  rintro α ⟨F, hFI, hF, hα⟩
  exact ⟨F, hIQ hFI, hF, hα⟩

private theorem cylinder_shift_outside
    (Q : Ideal (MvPowerSeries (Fin n) ℂ)) (L : Set (Fin n))
    (hCyl : actualCoordinateDiagramCylinder Q L)
    (i : Fin n) (hi : i ∈ L) (α : Fin n →₀ ℕ)
    (hα : α ∉ actualInitialDiagram MonomialOrder.degLex Q) :
    Finsupp.single i 1 + α ∉ actualInitialDiagram MonomialOrder.degLex Q := by
  intro hshift
  have herase : (Finsupp.single i 1 + α).erase i = α.erase i := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp only [Finsupp.erase_ne hji, Finsupp.add_apply,
        Finsupp.single_eq_of_ne hji, zero_add]
  have hmem := (hCyl i hi (Finsupp.single i 1 + α)).mp hshift
  rw [herase] at hmem
  exact hα ((hCyl i hi α).mpr hmem)

private theorem monomial_mem_total_power
    (α : Fin n →₀ ℕ) (q : ℕ) (hα : q ≤ normalExponentDegree α) :
    MvPowerSeries.monomial α (1 : ℂ) ∈ genuineFormalVariables n ^ q := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
  intro β hβ
  have hne : β ≠ α := by intro h; subst β; omega
  simp only [MvPowerSeries.coeff_monomial, if_neg hne]

private theorem actualStandardModelJetMap_range
    (J Q : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :
    LinearMap.range (actualStandardModelJetMap J Q q) =
      Submodule.span ℂ (range fun a : actualStandardIndex n Q q =>
        Ideal.Quotient.mk (J ⊔ genuineFormalVariables n ^ q)
          (MvPowerSeries.monomial a.val.val (1 : ℂ))) := by
  let π := (Ideal.Quotient.mkₐ ℂ (J ⊔ genuineFormalVariables n ^ q)).toLinearMap
  have heq : actualStandardModelJetMap J Q q =
      Fintype.linearCombination ℂ (fun a : actualStandardIndex n Q q =>
        π (MvPowerSeries.monomial a.val.val (1 : ℂ))) := by
    apply LinearMap.ext
    intro c
    change π (∑ a : actualStandardIndex n Q q,
        MvPowerSeries.monomial a.val.val (c a)) =
      ∑ a : actualStandardIndex n Q q,
        c a • π (MvPowerSeries.monomial a.val.val (1 : ℂ))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← map_smul]
    apply congrArg π
    simpa only [smul_eq_mul, mul_one] using
      (MvPowerSeries.monomial a.val.val).map_smul (c a) (1 : ℂ)
  rw [heq, Fintype.range_linearCombination]
  rfl

/-- A genuine whole fibre identity and a whole coordinate cylinder produce
surjectivity of the SAME literal standard-lift map at every total jet order. -/
theorem actualStandardModelJetMap_surjective
    (J Q : Ideal (MvPowerSeries (Fin n) ℂ)) (L : Set (Fin n))
    (hFibre : J ⊔ actualFormalCoordinateIdeal n L =
      Q ⊔ actualFormalCoordinateIdeal n L)
    (hCyl : actualCoordinateDiagramCylinder Q L) (q : ℕ) :
    Function.Surjective (actualStandardModelJetMap J Q q) := by
  let P := actualFormalCoordinateIdeal n L
  let M := MvPowerSeries (Fin n) ℂ ⧸ (J ⊔ genuineFormalVariables n ^ q)
  let π : MvPowerSeries (Fin n) ℂ →+* M :=
    Ideal.Quotient.mk (J ⊔ genuineFormalVariables n ^ q)
  let v : L → M := fun i => π (MvPowerSeries.X i.val)
  let W : Submodule ℂ M := Submodule.span ℂ
    (range fun a : actualStandardIndex n Q q =>
      π (MvPowerSeries.monomial a.val.val (1 : ℂ)))
  have hstable : ∀ i : L, ∀ u ∈ W, v i * u ∈ W := by
    intro i u hu
    change u ∈ Submodule.span ℂ
      (range fun a : actualStandardIndex n Q q =>
        π (MvPowerSeries.monomial a.val.val (1 : ℂ))) at hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨a, rfl⟩ := hu
        let α := Finsupp.single i.val 1 + a.val.val
        have hprod : v i * π (MvPowerSeries.monomial a.val.val (1 : ℂ)) =
            π (MvPowerSeries.monomial α (1 : ℂ)) := by
          change π (MvPowerSeries.X i.val) *
            π (MvPowerSeries.monomial a.val.val (1 : ℂ)) = _
          rw [← map_mul, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, one_mul]
        rw [hprod]
        by_cases hd : normalExponentDegree α < q
        · have hα : α ∉ actualInitialDiagram MonomialOrder.degLex Q :=
            cylinder_shift_outside Q L hCyl i.val i.property a.val.val a.property
          let b : actualStandardIndex n Q q := ⟨⟨α, hd⟩, hα⟩
          exact Submodule.subset_span ⟨b, rfl⟩
        · have hz : π (MvPowerSeries.monomial α (1 : ℂ)) = 0 := by
            apply Ideal.Quotient.eq_zero_iff_mem.mpr
            exact Ideal.mem_sup_right (monomial_mem_total_power α q (Nat.le_of_not_gt hd))
          rw [hz]
          exact W.zero_mem
    | zero => simpa only [mul_zero] using W.zero_mem
    | add x y _ _ hx hy => simpa only [mul_add] using W.add_mem hx hy
    | smul c x _ hx => simpa only [mul_smul_comm] using W.smul_mem c hx
  have hwordPower : ∀ s : List L,
      (s.map (fun i => (MvPowerSeries.X i.val : MvPowerSeries (Fin n) ℂ))).prod ∈
        genuineFormalVariables n ^ s.length := by
    intro s
    induction s with
    | nil =>
        simp only [List.map_nil, List.prod_nil, List.length_nil, pow_zero,
          Ideal.one_eq_top, Submodule.mem_top]
    | cons i s ih =>
        rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
        exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i.val, rfl⟩) ih
  have hwordMap : ∀ s : List L, (s.map v).prod =
      π ((s.map (fun i => (MvPowerSeries.X i.val : MvPowerSeries (Fin n) ℂ))).prod) := by
    intro s
    induction s with
    | nil =>
        simpa only [List.map_nil, List.prod_nil] using (map_one π).symm
    | cons i s ih =>
        change v i * (s.map v).prod =
          π (MvPowerSeries.X i.val *
            (s.map (fun j => (MvPowerSeries.X j.val : MvPowerSeries (Fin n) ℂ))).prod)
        rw [map_mul, ih]
  have hnil : ∀ s : List L, s.length = q → (s.map v).prod = 0 := by
    intro s hs
    rw [hwordMap]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_sup_right
    simpa only [hs] using hwordPower s
  have hmod : ∀ x : M, ∃ u ∈ W, ∃ r : ℕ, ∃ i : Fin r → L,
      ∃ y : Fin r → M, x = u + ∑ k : Fin r, v (i k) * y k := by
    intro x
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, hc⟩ := actualStandardQuotientMap_surjective (Q ⊔ P) q
      (Ideal.Quotient.mk ((Q ⊔ P) ⊔ genuineFormalVariables n ^ q) F)
    rw [actualStandardQuotientMap_apply] at hc
    let T := actualStandardLift n (Q ⊔ P) q c
    have hT : π T ∈ W := by
      change π (∑ a : actualStandardIndex n (Q ⊔ P) q,
        MvPowerSeries.monomial a.val.val (c a)) ∈ W
      rw [map_sum]
      apply W.sum_mem
      intro a _
      have ha : a.val.val ∉ actualInitialDiagram MonomialOrder.degLex Q := by
        intro h
        exact a.property (diagram_mono Q (Q ⊔ P) le_sup_left h)
      let b : actualStandardIndex n Q q := ⟨a.val, ha⟩
      have he : π (MvPowerSeries.monomial a.val.val (c a)) =
          c a • π (MvPowerSeries.monomial a.val.val (1 : ℂ)) := by
        change (Ideal.Quotient.mkₐ ℂ (J ⊔ genuineFormalVariables n ^ q))
            (MvPowerSeries.monomial a.val.val (c a)) =
          c a • (Ideal.Quotient.mkₐ ℂ (J ⊔ genuineFormalVariables n ^ q))
            (MvPowerSeries.monomial a.val.val (1 : ℂ))
        rw [← map_smul]
        apply congrArg (Ideal.Quotient.mkₐ ℂ (J ⊔ genuineFormalVariables n ^ q))
        simpa only [smul_eq_mul, mul_one] using
          (MvPowerSeries.monomial a.val.val).map_smul (c a) (1 : ℂ)
      rw [he]
      exact W.smul_mem _ (Submodule.subset_span ⟨b, rfl⟩)
    have hdiff : F - T ∈ (Q ⊔ P) ⊔ genuineFormalVariables n ^ q :=
      Ideal.Quotient.eq.mp hc.symm
    have hFibre' : J ⊔ P = Q ⊔ P := hFibre
    rw [← hFibre'] at hdiff
    obtain ⟨U, hU, Z, hZ, hUZ⟩ := Submodule.mem_sup.mp hdiff
    obtain ⟨B, hB, A, hA, hBA⟩ := Submodule.mem_sup.mp hU
    have hquot : π F = π T + π A := by
      rw [← map_add]
      apply Ideal.Quotient.eq.mpr
      have he : F - (T + A) = B + Z := by
        calc
          _ = (F - T) - A := by abel
          _ = (B + A + Z) - A := by rw [← hUZ, ← hBA]
          _ = B + Z := by abel
      rw [he]
      exact (J ⊔ genuineFormalVariables n ^ q).add_mem
        (Ideal.mem_sup_left hB) (Ideal.mem_sup_right hZ)
    change A ∈ Ideal.span (MvPowerSeries.X '' L) at hA
    obtain ⟨r, D, V, hV⟩ := Submodule.mem_span_set'.mp hA
    have hgen (k : Fin r) : ∃ i : L,
        (MvPowerSeries.X i.val : MvPowerSeries (Fin n) ℂ) = (V k).val := by
      obtain ⟨i, hi, he⟩ := (V k).property
      exact ⟨⟨i, hi⟩, he⟩
    choose i hi using hgen
    refine ⟨π T, hT, r, i, (fun k => π (D k)), ?_⟩
    rw [hquot]
    congr 1
    rw [← hV, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    change π (D k * (V k).val) = v (i k) * π (D k)
    rw [← hi k, map_mul, mul_comm]
  have hW : W = ⊤ := nilpotent_coordinate_words_span_top W v q hstable hnil hmod
  rw [← LinearMap.range_eq_top, actualStandardModelJetMap_range]
  exact hW

/-- The dimension bound is a consequence of the concrete surjection, not a
replacement for it. -/
theorem genuineFormalHilbertSamuelValue_le_model_of_fibre
    (J Q : Ideal (MvPowerSeries (Fin n) ℂ)) (L : Set (Fin n))
    (hFibre : J ⊔ actualFormalCoordinateIdeal n L =
      Q ⊔ actualFormalCoordinateIdeal n L)
    (hCyl : actualCoordinateDiagramCylinder Q L) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n J ℓ ≤ genuineFormalHilbertSamuelValue n Q ℓ := by
  let := finiteDimensional_formal_quotient_sup_variables_pow n (ℓ + 1) J
  have h := LinearMap.finrank_le_finrank_of_surjective
    (actualStandardModelJetMap_surjective J Q L hFibre hCyl (ℓ + 1))
  rw [Module.finrank_fintype_fun_eq_card] at h
  rw [genuineFormalHilbertSamuelValue_eq_card_standardIndex Q ℓ]
  exact h

/-- Equal genuine HS values give injectivity of this same actual standard map. -/
theorem actualStandardModelJetMap_bijective_of_hs_eq
    (J Q : Ideal (MvPowerSeries (Fin n) ℂ)) (L : Set (Fin n))
    (hFibre : J ⊔ actualFormalCoordinateIdeal n L =
      Q ⊔ actualFormalCoordinateIdeal n L)
    (hCyl : actualCoordinateDiagramCylinder Q L) (ℓ : ℕ)
    (hHS : genuineFormalHilbertSamuelValue n J ℓ =
      genuineFormalHilbertSamuelValue n Q ℓ) :
    Function.Bijective (actualStandardModelJetMap J Q (ℓ + 1)) := by
  let := finiteDimensional_formal_quotient_sup_variables_pow n (ℓ + 1) J
  have hs := actualStandardModelJetMap_surjective J Q L hFibre hCyl (ℓ + 1)
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr hs, hs⟩
  rw [Module.finrank_fintype_fun_eq_card,
    ← genuineFormalHilbertSamuelValue_eq_card_standardIndex Q ℓ]
  exact hHS.symm

/-- The existing radial theorem and the actual new spanning map internally
identify the model dimension from ORIGINAL source/target HS equality. -/
theorem genuineFormalHilbertSamuelValue_dehomogenizedModel_eq_of_source_hs_eq
    (K J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ)
    (L : Set (Fin n))
    (hFibre : J ⊔ actualFormalCoordinateIdeal n L =
      actualDehomogenizedPointInitialConeIdeal K e b ⊔ actualFormalCoordinateIdeal n L)
    (hCyl : actualCoordinateDiagramCylinder (actualDehomogenizedPointInitialConeIdeal K e b) L)
    (ℓ : ℕ) (hHS : genuineFormalHilbertSamuelValue n J ℓ =
      genuineFormalHilbertSamuelValue n K ℓ) :
    genuineFormalHilbertSamuelValue n J ℓ =
      genuineFormalHilbertSamuelValue n (actualDehomogenizedPointInitialConeIdeal K e b) ℓ := by
  apply le_antisymm
  · exact genuineFormalHilbertSamuelValue_le_model_of_fibre J _ L hFibre hCyl ℓ
  · exact (genuineFormalHilbertSamuelValue_actualDehomogenizedPointInitialConeIdeal_le K e b ℓ).trans
      hHS.symm.le

/-- This consumer asks for actual whole fibre/cylinder data and original HS
equality, and produces actual jet bijectivity without a desired target premise. -/
theorem actualDehomogenizedModelJetMap_bijective_of_source_hs_eq
    (K J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ)
    (L : Set (Fin n))
    (hFibre : J ⊔ actualFormalCoordinateIdeal n L =
      actualDehomogenizedPointInitialConeIdeal K e b ⊔ actualFormalCoordinateIdeal n L)
    (hCyl : actualCoordinateDiagramCylinder (actualDehomogenizedPointInitialConeIdeal K e b) L)
    (ℓ : ℕ) (hHS : genuineFormalHilbertSamuelValue n J ℓ =
      genuineFormalHilbertSamuelValue n K ℓ) :
    Function.Bijective (actualStandardModelJetMap J
      (actualDehomogenizedPointInitialConeIdeal K e b) (ℓ + 1)) :=
  actualStandardModelJetMap_bijective_of_hs_eq J _ L hFibre hCyl ℓ
    (genuineFormalHilbertSamuelValue_dehomogenizedModel_eq_of_source_hs_eq
      K J e b L hFibre hCyl ℓ hHS)

private theorem standardLift_eq_of_bounded_support
    (Q : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ)
    (P : MvPowerSeries (Fin n) ℂ)
    (hP : ∀ α, MvPowerSeries.coeff α P ≠ 0 →
      normalExponentDegree α < q ∧ α ∉ actualInitialDiagram MonomialOrder.degLex Q) :
    actualStandardLift n Q q (fun a => MvPowerSeries.coeff a.val.val P) = P := by
  apply MvPowerSeries.ext
  intro α
  by_cases hd : normalExponentDegree α < q
  · by_cases hn : α ∉ actualInitialDiagram MonomialOrder.degLex Q
    · let a : actualStandardIndex n Q q := ⟨⟨α, hd⟩, hn⟩
      exact actualStandardLift_coefficient Q q (fun a => MvPowerSeries.coeff a.val.val P) a
    · have hmem : α ∈ actualInitialDiagram MonomialOrder.degLex Q := not_not.mp hn
      rw [actualStandardLift_coefficient_outside Q q _ α (Or.inr hmem)]
      symm
      by_contra hne
      exact (hP α hne).2 hmem
  · rw [actualStandardLift_coefficient_outside Q q _ α (Or.inl hd)]
    symm
    by_contra hne
    exact hd (hP α hne).1

/-- All coefficients of a bounded diagram-avoiding tail are separated by the
same concrete model map; no injectivity certificate is supplied by the caller. -/
theorem bounded_diagram_avoiding_series_eq_zero_of_model_hs_eq
    (J Q : Ideal (MvPowerSeries (Fin n) ℂ)) (L : Set (Fin n))
    (hFibre : J ⊔ actualFormalCoordinateIdeal n L =
      Q ⊔ actualFormalCoordinateIdeal n L)
    (hCyl : actualCoordinateDiagramCylinder Q L) (ℓ : ℕ)
    (hHS : genuineFormalHilbertSamuelValue n J ℓ =
      genuineFormalHilbertSamuelValue n Q ℓ)
    (P : MvPowerSeries (Fin n) ℂ)
    (hP : ∀ α, MvPowerSeries.coeff α P ≠ 0 → normalExponentDegree α < ℓ + 1 ∧
      α ∉ actualInitialDiagram MonomialOrder.degLex Q)
    (hmem : P ∈ J ⊔ genuineFormalVariables n ^ (ℓ + 1)) : P = 0 := by
  let c : actualStandardIndex n Q (ℓ + 1) → ℂ :=
    fun a => MvPowerSeries.coeff a.val.val P
  have hLift : actualStandardLift n Q (ℓ + 1) c = P :=
    standardLift_eq_of_bounded_support Q (ℓ + 1) P hP
  have hz : actualStandardModelJetMap J Q (ℓ + 1) c = 0 := by
    rw [actualStandardModelJetMap_apply, hLift]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hc : c = 0 := by
    apply (actualStandardModelJetMap_bijective_of_hs_eq J Q L hFibre hCyl ℓ hHS).1
    simpa only [map_zero] using hz
  rw [hc, map_zero] at hLift
  exact hLift.symm

/-- ORIGINAL source HS equality and the actual radial bound suffice for this
same bounded-tail conclusion once the explicit whole model dictionary is supplied. -/
theorem bounded_diagram_avoiding_series_eq_zero_of_dehomogenized_source_hs_eq
    (K J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ)
    (L : Set (Fin n))
    (hFibre : J ⊔ actualFormalCoordinateIdeal n L =
      actualDehomogenizedPointInitialConeIdeal K e b ⊔ actualFormalCoordinateIdeal n L)
    (hCyl : actualCoordinateDiagramCylinder (actualDehomogenizedPointInitialConeIdeal K e b) L)
    (ℓ : ℕ) (hHS : genuineFormalHilbertSamuelValue n J ℓ =
      genuineFormalHilbertSamuelValue n K ℓ)
    (P : MvPowerSeries (Fin n) ℂ)
    (hP : ∀ α, MvPowerSeries.coeff α P ≠ 0 → normalExponentDegree α < ℓ + 1 ∧
      α ∉ actualInitialDiagram MonomialOrder.degLex (actualDehomogenizedPointInitialConeIdeal K e b))
    (hmem : P ∈ J ⊔ genuineFormalVariables n ^ (ℓ + 1)) : P = 0 :=
  bounded_diagram_avoiding_series_eq_zero_of_model_hs_eq J _ L hFibre hCyl ℓ
    (genuineFormalHilbertSamuelValue_dehomogenizedModel_eq_of_source_hs_eq
      K J e b L hFibre hCyl ℓ hHS) P hP hmem

end

end Hironaka.HironakaActualRelativeStandardnessCoordinateJetSpanning
