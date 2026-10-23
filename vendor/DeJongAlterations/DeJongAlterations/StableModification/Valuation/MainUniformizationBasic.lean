import DeJongAlterations.StableModification.Valuation.DVRCoordinate
import DeJongAlterations.StableModification.Valuation.FunctionField.Places
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Algebraic lemmas for the uniformization of one-dimensional valued fields

This file collects the purely algebraic ingredients of the proof of Theorem 2.1.8 (`valunif`) of
M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §2.2
(`semi-stable.tex`, lines 2177–2232), in the strengthened form of plan `PLAN-SM-VAL.md`, node M2.
Blueprint chapter `sm-val-main.tex`.

Throughout, `K → L` is a field extension, `O` a valuation subring of `L`, `A = O ∩ K` and `κ(·)`
denotes residue fields.

## Main results

* `exists_coeff_valuation_aeval_eq` (**Gauss lemma**): if `T ∈ O` has a residue `T̃`
  transcendental over `κ(A)`, then for every nonzero `P ∈ K[X]` the value `|P(T)|` is the largest
  value of a coefficient of `P`. In other words `O ∩ K(T)` is the Gauss valuation of `K(T)`.
* `range_residueField_adjoin`: under the same hypothesis the residue field of `O ∩ K(T)` is
  `κ(A)(T̃)` inside `κ(O)`; `residueFieldAdjoinEquiv` is the resulting isomorphism.
* `linearIndependent_of_residue` and `finiteDimensional_residueField_adjoin` (plan node V4c,
  the fix of literature issue LI-2 = ERRATA T-LI2): lifts of residues that are linearly
  independent over `κ(A)(x̃)` are linearly independent over `K(x)`, hence
  `[κ(O) : κ(A)(x̃)] ≤ [L : K(x)]`.
* `isStdUnramifiedGenerator_of_ringEquiv`: standard-unramified generators only depend on the
  base field up to an isomorphism compatible with the maps to `L`.
* `isStdUnramifiedGenerator_one_of_surjective`, `exists_isStdUnramifiedGenerator_top`: the
  generators of trivial residue extensions and of the trivial valuation.
-/

noncomputable section

open IsLocalRing Polynomial
open scoped IntermediateField

namespace DeJongAlterations.StableModification.Valuation.MainUniformization

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {O : ValuationSubring L}

/-! ### Lifting polynomials to `O ∩ K` -/

section Lift

/-- A polynomial over `K` whose coefficients lie in `O` comes from a polynomial over `O ∩ K`. -/
theorem exists_map_eq_of_coeff_mem (Q : K[X]) (hQ : ∀ j, algebraMap K L (Q.coeff j) ∈ O) :
    ∃ Q' : (O.comap (algebraMap K L))[X],
      Q'.map (algebraMap (O.comap (algebraMap K L)) K) = Q := by
  have : Q ∈ lifts (algebraMap (O.comap (algebraMap K L)) K) :=
    (lifts_iff_coeff_lifts Q).mpr fun n ↦ ⟨⟨Q.coeff n, hQ n⟩, rfl⟩
  exact this

/-- Evaluation of a lifted polynomial at an element of `O`, computed in `L`. -/
theorem coe_aeval_lift {Q : K[X]} {Q' : (O.comap (algebraMap K L))[X]}
    (hQ' : Q'.map (algebraMap (O.comap (algebraMap K L)) K) = Q) (y : O) :
    ((aeval y Q' : O) : L) = aeval (y : L) Q := by
  rw [coe_aeval_comap, ← hQ', aeval_map_algebraMap]

/-- Coefficients of a lifted polynomial, computed in `K`. -/
theorem coe_coeff_lift {Q : K[X]} {Q' : (O.comap (algebraMap K L))[X]}
    (hQ' : Q'.map (algebraMap (O.comap (algebraMap K L)) K) = Q) (j : ℕ) :
    ((Q'.coeff j : O.comap (algebraMap K L)) : K) = Q.coeff j := by
  rw [← hQ', coeff_map]
  rfl

end Lift

/-! ### The Gauss lemma -/

section Gauss

/-- An index of a coefficient of `P` of largest value. -/
theorem exists_coeff_max (P : K[X]) (hP : P ≠ 0) :
    ∃ i, P.coeff i ≠ 0 ∧ ∀ j, O.valuation (algebraMap K L (P.coeff j)) ≤
      O.valuation (algebraMap K L (P.coeff i)) := by
  classical
  obtain ⟨i, hi, hmax⟩ := P.support.exists_max_image
    (fun j ↦ O.valuation (algebraMap K L (P.coeff j))) (support_nonempty.mpr hP)
  refine ⟨i, mem_support_iff.mp hi, fun j ↦ ?_⟩
  by_cases hj : j ∈ P.support
  · exact hmax j hj
  · rw [notMem_support_iff.mp hj, map_zero, map_zero]
    exact zero_le

/-- Dividing a nonzero polynomial by a coefficient of largest value gives a polynomial with
coefficients in `O`, one of which is `1`. -/
theorem coeff_C_inv_mul_mem {P : K[X]} {i : ℕ} (hc : P.coeff i ≠ 0)
    (hmax : ∀ j, O.valuation (algebraMap K L (P.coeff j)) ≤
      O.valuation (algebraMap K L (P.coeff i))) (j : ℕ) :
    algebraMap K L ((C (P.coeff i)⁻¹ * P).coeff j) ∈ O := by
  have hvc : 0 < O.valuation (algebraMap K L (P.coeff i)) := by
    rw [zero_lt_iff]
    simpa using hc
  rw [← ValuationSubring.valuation_le_one_iff, coeff_C_mul, map_mul, map_mul, map_inv₀]
  exact (inv_mul_le_one₀ hvc).mpr (hmax j)

/-- The normalized coefficient is `1`. -/
theorem coeff_C_inv_mul_self {P : K[X]} {i : ℕ} (hc : P.coeff i ≠ 0) :
    (C (P.coeff i)⁻¹ * P).coeff i = 1 := by
  rw [coeff_C_mul, inv_mul_cancel₀ hc]

/-- A polynomial over `O ∩ K` with a coefficient equal to `1`, evaluated at an element of `O`
whose residue is transcendental over `κ(O ∩ K)`, is a unit of `O`. -/
theorem valuation_aeval_lift_eq_one {T : L} (hT : T ∈ O)
    (htr : Transcendental (ResidueField (O.comap (algebraMap K L))) (residue O ⟨T, hT⟩))
    (Q' : (O.comap (algebraMap K L))[X]) {i : ℕ} (hi : Q'.coeff i = 1) :
    O.valuation ((aeval (⟨T, hT⟩ : O) Q' : O) : L) = 1 := by
  have hne : Q'.map (residue (O.comap (algebraMap K L))) ≠ 0 := by
    intro h
    have := congrArg (fun q ↦ q.coeff i) h
    simp only [coeff_map, hi, map_one, coeff_zero] at this
    exact one_ne_zero this
  have hres : residue O (aeval (⟨T, hT⟩ : O) Q') ≠ 0 := by
    rw [residue_aeval_comap]
    exact fun h ↦ hne (transcendental_iff.mp htr _ h)
  exact (O.valuation_eq_one_iff _).mp ((residue_ne_zero_iff_isUnit _).mp hres)

/-- **Gauss lemma** (the valuation induced on `K(T)` is the Gauss valuation): let `T ∈ O` have a
residue transcendental over `κ(O ∩ K)`. For every nonzero `P ∈ K[X]` there is a coefficient
`P.coeff i ≠ 0` of largest value, and `|P(T)| = |P.coeff i|`. -/
theorem exists_coeff_valuation_aeval_eq {T : L} (hT : T ∈ O)
    (htr : Transcendental (ResidueField (O.comap (algebraMap K L))) (residue O ⟨T, hT⟩))
    {P : K[X]} (hP : P ≠ 0) :
    ∃ i, P.coeff i ≠ 0 ∧ (∀ j, O.valuation (algebraMap K L (P.coeff j)) ≤
        O.valuation (algebraMap K L (P.coeff i))) ∧
      O.valuation (aeval T P) = O.valuation (algebraMap K L (P.coeff i)) := by
  obtain ⟨i, hc, hmax⟩ := exists_coeff_max (O := O) P hP
  refine ⟨i, hc, hmax, ?_⟩
  obtain ⟨Q', hQ'⟩ := exists_map_eq_of_coeff_mem _ (coeff_C_inv_mul_mem hc hmax)
  have hi : Q'.coeff i = 1 := Subtype.ext (by
    rw [coe_coeff_lift hQ', coeff_C_inv_mul_self hc]
    rfl)
  have h1 := valuation_aeval_lift_eq_one hT htr Q' hi
  rw [coe_aeval_lift hQ'] at h1
  have hPQ : aeval T P = algebraMap K L (P.coeff i) * aeval T (C (P.coeff i)⁻¹ * P) := by
    rw [map_mul, aeval_C, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
  rw [hPQ, map_mul, h1, mul_one]

/-- Under the hypothesis of the Gauss lemma, a polynomial `P` with `P(T) ∈ O` has all its
coefficients in `O`. -/
theorem coeff_mem_of_aeval_mem {T : L} (hT : T ∈ O)
    (htr : Transcendental (ResidueField (O.comap (algebraMap K L))) (residue O ⟨T, hT⟩))
    {P : K[X]} (hP : aeval T P ∈ O) (j : ℕ) : algebraMap K L (P.coeff j) ∈ O := by
  rcases eq_or_ne P 0 with rfl | hP0
  · rw [coeff_zero, map_zero]
    exact O.zero_mem
  obtain ⟨i, -, hmax, hv⟩ := exists_coeff_valuation_aeval_eq hT htr hP0
  rw [← ValuationSubring.valuation_le_one_iff] at hP ⊢
  exact (hmax j).trans (hv ▸ hP)

/-- An element of `O` whose residue is transcendental over `κ(O ∩ K)` is transcendental over
`K`. -/
theorem transcendental_of_transcendental_residue {T : L} (hT : T ∈ O)
    (htr : Transcendental (ResidueField (O.comap (algebraMap K L))) (residue O ⟨T, hT⟩)) :
    Transcendental K T := by
  rw [transcendental_iff]
  intro P hP
  by_contra hP0
  obtain ⟨i, hc, -, hv⟩ := exists_coeff_valuation_aeval_eq hT htr hP0
  rw [hP, map_zero, eq_comm, Valuation.zero_iff] at hv
  exact hc ((_root_.map_eq_zero_iff _ (algebraMap K L).injective).mp hv)

end Gauss

/-! ### The residue field of `O ∩ K(T)` -/

section ResidueAdjoin

variable {T : L}

/-- `T` lies in `O ∩ K(T)`. -/
theorem self_mem_comap_adjoin (hT : T ∈ O) :
    (⟨T, IntermediateField.mem_adjoin_simple_self K T⟩ : K⟮T⟯) ∈
      O.comap (algebraMap K⟮T⟯ L) := hT

/-- The residue of `T` in `κ(O)` is the image of its residue in `κ(O ∩ K(T))`. -/
theorem algebraMap_residue_self (hT : T ∈ O) :
    algebraMap (ResidueField (O.comap (algebraMap K⟮T⟯ L))) (ResidueField O)
        (residue _ ⟨_, self_mem_comap_adjoin hT⟩) = residue O ⟨T, hT⟩ := rfl

/-- Elements of `K` lie in `K(T)`. -/
theorem algebraMap_mem_comap_adjoin (a : O.comap (algebraMap K L)) :
    algebraMap K K⟮T⟯ a ∈ O.comap (algebraMap K⟮T⟯ L) := a.2

/-- The residues of elements of `O ∩ K` in `κ(O)` come from `κ(O ∩ K(T))`. -/
theorem algebraMap_residue_comap (a : O.comap (algebraMap K L)) :
    algebraMap (ResidueField (O.comap (algebraMap K⟮T⟯ L))) (ResidueField O)
        (residue _ ⟨_, algebraMap_mem_comap_adjoin (T := T) a⟩) =
      algebraMap (ResidueField (O.comap (algebraMap K L))) (ResidueField O)
        (residue _ a) := rfl

variable (hT : T ∈ O)
  (htr : Transcendental (ResidueField (O.comap (algebraMap K L))) (residue O ⟨T, hT⟩))

include htr in
/-- **The residue field of the Gauss valuation**: if `T̃` is transcendental over `κ(O ∩ K)`,
the image of `κ(O ∩ K(T))` in `κ(O)` is `κ(O ∩ K)(T̃)`. -/
theorem range_residueField_adjoin :
    (algebraMap (ResidueField (O.comap (algebraMap K⟮T⟯ L))) (ResidueField O)).fieldRange =
      (IntermediateField.adjoin (ResidueField (O.comap (algebraMap K L)))
        {residue O ⟨T, hT⟩}).toSubfield := by
  set A := O.comap (algebraMap K L)
  set R := O.comap (algebraMap K⟮T⟯ L)
  set f := algebraMap (ResidueField R) (ResidueField O)
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    obtain ⟨w, rfl⟩ := residue_surjective w
    obtain ⟨⟨w, hwK⟩, hwO⟩ := w
    change f (residue R ⟨⟨w, hwK⟩, hwO⟩) ∈ _
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K w).mp hwK
    have hw : w ∈ O := hwO
    by_cases hs : aeval T s = 0
    · have hw0 : (⟨⟨w, hwK⟩, hwO⟩ : R) = 0 := by
        apply Subtype.ext
        apply Subtype.ext
        change w = 0
        rw [hrs, hs, div_zero]
      rw [hw0, map_zero, map_zero]
      exact zero_mem _
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hs (map_zero _)
    obtain ⟨i, hci, hmax, hv⟩ := exists_coeff_valuation_aeval_eq hT htr hs0
    set c := s.coeff i
    set s' := C c⁻¹ * s
    set r' := C c⁻¹ * r
    have hcL : algebraMap K L c ≠ 0 := (_root_.map_ne_zero _).mpr hci
    have hs'r' : w = aeval T r' / aeval T s' := by
      rw [hrs, map_mul, map_mul, aeval_C, mul_div_mul_left _ _ ((_root_.map_ne_zero _).mpr
        (inv_ne_zero hci))]
    have hs'eq : aeval T s' = (algebraMap K L c)⁻¹ * aeval T s := by
      rw [map_mul, aeval_C, map_inv₀]
    have hs'0 : aeval T s' ≠ 0 := by
      rw [hs'eq]
      exact mul_ne_zero (inv_ne_zero hcL) hs
    have hr'eq : aeval T r' = w * aeval T s' := by
      rw [hs'r', div_mul_cancel₀ _ hs'0]
    have hs'mem : ∀ j, algebraMap K L (s'.coeff j) ∈ O := coeff_C_inv_mul_mem hci hmax
    obtain ⟨S', hS'⟩ := exists_map_eq_of_coeff_mem _ hs'mem
    have hS'i : S'.coeff i = 1 := Subtype.ext (by
      rw [coe_coeff_lift hS', coeff_C_inv_mul_self hci]
      rfl)
    have hS'unit := valuation_aeval_lift_eq_one hT htr S' hS'i
    have hr'mem : aeval T r' ∈ O := by
      rw [hr'eq]
      refine mul_mem hw ?_
      rw [← coe_aeval_lift hS' ⟨T, hT⟩]
      exact (aeval (⟨T, hT⟩ : O) S').2
    obtain ⟨R', hR'⟩ := exists_map_eq_of_coeff_mem _ (coeff_mem_of_aeval_mem hT htr hr'mem)
    -- the residue of `w` is `R̄'(T̃) / S̄'(T̃)`
    have hunit : IsUnit (aeval (⟨T, hT⟩ : O) S') :=
      (O.valuation_eq_one_iff _).mpr hS'unit
    have hwO' : (⟨w, hw⟩ : O) * aeval (⟨T, hT⟩ : O) S' = aeval (⟨T, hT⟩ : O) R' := by
      apply Subtype.ext
      change w * ((aeval (⟨T, hT⟩ : O) S' : O) : L) = ((aeval (⟨T, hT⟩ : O) R' : O) : L)
      rw [coe_aeval_lift hS', coe_aeval_lift hR']
      exact hr'eq.symm
    have hfw : f (residue R ⟨⟨w, hwK⟩, hwO⟩) = residue O ⟨w, hw⟩ := rfl
    rw [hfw]
    have hres : residue O ⟨w, hw⟩ = residue O (aeval (⟨T, hT⟩ : O) R') /
        residue O (aeval (⟨T, hT⟩ : O) S') := by
      rw [← hwO', map_mul, mul_div_assoc, div_self, mul_one]
      exact (residue_ne_zero_iff_isUnit _).mpr hunit
    rw [hres, residue_aeval_comap, residue_aeval_comap]
    refine div_mem ?_ ?_
    · exact IntermediateField.algebra_adjoin_le_adjoin _ _ (aeval_mem_adjoin_singleton _ _)
    · exact IntermediateField.algebra_adjoin_le_adjoin _ _ (aeval_mem_adjoin_singleton _ _)
  · rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨a, rfl⟩ | h)
    · obtain ⟨a, rfl⟩ := residue_surjective a
      exact ⟨_, algebraMap_residue_comap (T := T) a⟩
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact ⟨_, algebraMap_residue_self hT⟩

include htr in
/-- The residues of elements of `O ∩ K(T)` lie in `κ(O ∩ K)(T̃)`. -/
theorem algebraMap_residueField_mem_adjoin
    (w : ResidueField (O.comap (algebraMap K⟮T⟯ L))) :
    algebraMap (ResidueField (O.comap (algebraMap K⟮T⟯ L))) (ResidueField O) w ∈
      IntermediateField.adjoin (ResidueField (O.comap (algebraMap K L))) {residue O ⟨T, hT⟩} := by
  have : algebraMap (ResidueField (O.comap (algebraMap K⟮T⟯ L))) (ResidueField O) w ∈
      (algebraMap (ResidueField (O.comap (algebraMap K⟮T⟯ L))) (ResidueField O)).fieldRange :=
    ⟨w, rfl⟩
  rw [range_residueField_adjoin hT htr] at this
  exact this

/-- The isomorphism `κ(O ∩ K(T)) ≃ κ(O ∩ K)(T̃)` of the Gauss lemma, compatible with the maps to
`κ(O)`. -/
def residueFieldAdjoinEquiv :
    ResidueField (O.comap (algebraMap K⟮T⟯ L)) ≃+*
      IntermediateField.adjoin (ResidueField (O.comap (algebraMap K L))) {residue O ⟨T, hT⟩} :=
  RingEquiv.ofBijective ((algebraMap (ResidueField (O.comap (algebraMap K⟮T⟯ L)))
      (ResidueField O)).codRestrict _ (algebraMap_residueField_mem_adjoin hT htr)) <| by
    refine ⟨fun a b h ↦ (algebraMap _ (ResidueField O)).injective
      (congrArg Subtype.val h), ?_⟩
    rintro ⟨z, hz⟩
    have hz' : z ∈ (algebraMap (ResidueField (O.comap (algebraMap K⟮T⟯ L)))
        (ResidueField O)).fieldRange := by
      rw [range_residueField_adjoin hT htr]
      exact hz
    obtain ⟨w, rfl⟩ := hz'
    exact ⟨w, rfl⟩

/-- `residueFieldAdjoinEquiv` is the residue field map. -/
theorem coe_residueFieldAdjoinEquiv (w : ResidueField (O.comap (algebraMap K⟮T⟯ L))) :
    ((residueFieldAdjoinEquiv hT htr w : _) : ResidueField O) =
      algebraMap (ResidueField (O.comap (algebraMap K⟮T⟯ L))) (ResidueField O) w := rfl

end ResidueAdjoin

/-! ### Residue degrees (plan node V4c) -/

section ResidueDegree

/-- Every element of `K(x)` is a quotient of polynomial values with nonzero denominator. -/
theorem exists_eq_div_of_mem_adjoin {x w : L} (hw : w ∈ K⟮x⟯) :
    ∃ r s : K[X], aeval x s ≠ 0 ∧ w = aeval x r / aeval x s := by
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K w).mp hw
  by_cases hs : aeval x s = 0
  · refine ⟨0, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
    rw [hrs, hs, div_zero, map_zero, zero_div]
  · exact ⟨r, s, hs, hrs⟩

variable {x : L} (hx : x ∈ O)
  (htr : Transcendental (ResidueField (O.comap (algebraMap K L))) (residue O ⟨x, hx⟩))

include htr in
/-- **Lifts of independent residues, polynomial form** (plan node V4c): let `x ∈ O` have residue
`x̃` transcendental over `κ(O ∩ K)` and let `yᵢ ∈ O` have residues linearly independent over
`κ(O ∩ K)(x̃)`. If `∑ Pᵢ(x) yᵢ = 0` with `Pᵢ ∈ K[X]`, then all `Pᵢ = 0`. -/
theorem eq_zero_of_sum_aeval_mul_eq_zero {ι : Type*} [Fintype ι] (y : ι → O)
    (hy : LinearIndependent (IntermediateField.adjoin (ResidueField (O.comap (algebraMap K L)))
      {residue O ⟨x, hx⟩}) fun i ↦ residue O (y i))
    (P : ι → K[X]) (hP : ∑ i, aeval x (P i) * (y i : L) = 0) (i : ι) : P i = 0 := by
  classical
  by_contra hPi
  set S := Finset.univ.sigma fun i ↦ (P i).support
  have hSne : S.Nonempty := ⟨⟨i, (P i).natDegree⟩, Finset.mem_sigma.mpr
    ⟨Finset.mem_univ _, natDegree_mem_support_of_nonzero hPi⟩⟩
  obtain ⟨⟨i₀, n₀⟩, h₀, hmax⟩ := S.exists_max_image
    (fun q ↦ O.valuation (algebraMap K L ((P q.1).coeff q.2))) hSne
  have hc : (P i₀).coeff n₀ ≠ 0 := mem_support_iff.mp (Finset.mem_sigma.mp h₀).2
  set c := (P i₀).coeff n₀
  have hmax' : ∀ j n, O.valuation (algebraMap K L ((P j).coeff n)) ≤
      O.valuation (algebraMap K L c) := by
    intro j n
    by_cases hn : n ∈ (P j).support
    · exact hmax ⟨j, n⟩ (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hn⟩)
    · rw [notMem_support_iff.mp hn, map_zero, map_zero]
      exact zero_le
  have hmem : ∀ j n, algebraMap K L ((C c⁻¹ * P j).coeff n) ∈ O := fun j n ↦ by
    have hvc : 0 < O.valuation (algebraMap K L c) := by
      rw [zero_lt_iff]
      simpa using hc
    rw [← ValuationSubring.valuation_le_one_iff, coeff_C_mul, map_mul, map_mul, map_inv₀]
    exact (inv_mul_le_one₀ hvc).mpr (hmax' j n)
  choose Q hQ using fun j ↦ exists_map_eq_of_coeff_mem _ (hmem j)
  -- the relation in `O`
  set z : O := ∑ j, aeval (⟨x, hx⟩ : O) (Q j) * y j
  have hz : z = 0 := by
    apply Subtype.ext
    have : ((z : O) : L) = (algebraMap K L c)⁻¹ * ∑ j, aeval x (P j) * (y j : L) := by
      simp only [z, AddSubmonoidClass.coe_finsetSum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      change ((aeval (⟨x, hx⟩ : O) (Q j) : O) : L) * (y j : L) = _
      rw [coe_aeval_lift (hQ j), map_mul, aeval_C, map_inv₀, mul_assoc]
    rw [this, hP, mul_zero]
    rfl
  -- reduce it
  set F := IntermediateField.adjoin (ResidueField (O.comap (algebraMap K L)))
    {residue O ⟨x, hx⟩}
  have hg : ∀ j, aeval (residue O ⟨x, hx⟩)
      ((Q j).map (residue (O.comap (algebraMap K L)))) ∈ F := fun j ↦
    IntermediateField.algebra_adjoin_le_adjoin _ _ (aeval_mem_adjoin_singleton _ _)
  have hrel : ∑ j, (⟨_, hg j⟩ : F) • residue O (y j) = 0 := by
    have h1 := congrArg (residue O) hz
    rw [map_zero, map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, residue_aeval_comap, IntermediateField.smul_def, smul_eq_mul]
  have h0 := (Fintype.linearIndependent_iff.mp hy) _ hrel i₀
  have h0' : aeval (residue O ⟨x, hx⟩) ((Q i₀).map (residue (O.comap (algebraMap K L)))) = 0 :=
    congrArg Subtype.val h0
  have hQ0 := transcendental_iff.mp htr _ h0'
  have hcoeff := congrArg (fun q ↦ q.coeff n₀) hQ0
  have hQn : (Q i₀).coeff n₀ = 1 := Subtype.ext (by
    rw [coe_coeff_lift (hQ i₀), coeff_C_mul, inv_mul_cancel₀ hc]
    rfl)
  simp only [coeff_map, hQn, map_one, coeff_zero] at hcoeff
  exact one_ne_zero hcoeff

include htr in
/-- **Lifts of independent residues** (plan node V4c, Temkin's LI-2 gap): if `x ∈ O` has residue
`x̃` transcendental over `κ(O ∩ K)`, then lifts `yᵢ ∈ O` of elements of `κ(O)` that are linearly
independent over `κ(O ∩ K)(x̃)` are linearly independent over `K(x)`. -/
theorem linearIndependent_of_residue {ι : Type*} [Fintype ι] (y : ι → O)
    (hy : LinearIndependent (IntermediateField.adjoin (ResidueField (O.comap (algebraMap K L)))
      {residue O ⟨x, hx⟩}) fun i ↦ residue O (y i)) :
    LinearIndependent K⟮x⟯ fun i ↦ (y i : L) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose r s hs hrs using fun j ↦ exists_eq_div_of_mem_adjoin (g j).2
  set D := ∏ j, aeval x (s j)
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦ hs j
  set P : _ → K[X] := fun j ↦ r j * ∏ k ∈ Finset.univ.erase j, s k
  have hPj : ∀ j, aeval x (P j) = (g j : L) * D := by
    intro j
    simp only [P, map_mul, map_prod, D]
    rw [← Finset.mul_prod_erase Finset.univ (fun k ↦ aeval x (s k)) (Finset.mem_univ j),
      hrs j, ← mul_assoc, div_mul_cancel₀ _ (hs j)]
  have hsum : ∑ j, aeval x (P j) * (y j : L) = 0 := by
    have : ∑ j, aeval x (P j) * (y j : L) = D * ∑ j, g j • (y j : L) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hPj, IntermediateField.smul_def, smul_eq_mul]
      ring
    rw [this, hg, mul_zero]
  have hPi := eq_zero_of_sum_aeval_mul_eq_zero hx htr y hy P hsum i
  have : (g i : L) * D = 0 := by rw [← hPj, hPi, map_zero]
  exact Subtype.ext ((mul_eq_zero.mp this).resolve_right hD)

include htr in
/-- **The residue degree bound** `[κ(O) : κ(O ∩ K)(x̃)] ≤ [L : K(x)]` (plan node V4c). -/
theorem rank_residueField_adjoin_le [FiniteDimensional K⟮x⟯ L] :
    Module.rank (IntermediateField.adjoin (ResidueField (O.comap (algebraMap K L)))
      {residue O ⟨x, hx⟩}) (ResidueField O) ≤ Module.finrank K⟮x⟯ L := by
  classical
  refine rank_le fun t ht ↦ ?_
  choose y hy using fun z : ResidueField O ↦ residue_surjective z
  have hli : LinearIndependent (IntermediateField.adjoin
      (ResidueField (O.comap (algebraMap K L))) {residue O ⟨x, hx⟩})
      (fun i : t ↦ residue O (y i)) := by
    have : (fun i : t ↦ residue O (y i)) = fun i : t ↦ (i : ResidueField O) :=
      funext fun i ↦ hy i
    rw [this]
    exact ht
  have := (linearIndependent_of_residue hx htr (fun i : t ↦ y i) hli).fintype_card_le_finrank
  simpa using this

include htr in
/-- `κ(O)` is finite over `κ(O ∩ K)(x̃)` when `L` is finite over `K(x)`. -/
theorem finiteDimensional_residueField_adjoin [FiniteDimensional K⟮x⟯ L] :
    FiniteDimensional (IntermediateField.adjoin (ResidueField (O.comap (algebraMap K L)))
      {residue O ⟨x, hx⟩}) (ResidueField O) :=
  Module.rank_lt_aleph0_iff.mp
    ((rank_residueField_adjoin_le hx htr).trans_lt Cardinal.natCast_lt_aleph0)

end ResidueDegree

/-! ### Standard-unramified generators: change of base field and trivial cases -/

section Generators

variable {F₁ F₂ l : Type*} [Field F₁] [Field F₂] [Field l] [Algebra F₁ l] [Algebra F₂ l]
  {B : ValuationSubring l}

/-- **Change of base field**: a standard-unramified generator over `F₁` is one over `F₂` if
`F₁ ≅ F₂` compatibly with the maps to `l`. -/
theorem isStdUnramifiedGenerator_of_ringEquiv (e : F₁ ≃+* F₂)
    (he : ∀ a, algebraMap F₂ l (e a) = algebraMap F₁ l a) {z : l}
    (hz : IsStdUnramifiedGenerator F₁ B z) : IsStdUnramifiedGenerator F₂ B z := by
  have hcomp : (algebraMap F₂ l).comp (e : F₁ →+* F₂) = algebraMap F₁ l := RingHom.ext he
  have hint := hz.isIntegral_field
  -- the minimal polynomial
  set q := (minpoly F₁ z).map (e : F₁ →+* F₂) with hq
  have hqm : q.Monic := (minpoly.monic hint).map _
  have hqz : aeval z q = 0 := by
    rw [hq, aeval_def, eval₂_map, hcomp, ← aeval_def, minpoly.aeval]
  have hqirr : Irreducible q :=
    (MulEquiv.irreducible_iff (Polynomial.mapEquiv e)).mpr (minpoly.irreducible hint)
  have hmin : minpoly F₂ z = q := (minpoly.eq_of_irreducible_of_monic hqirr hqz hqm).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro w hw'
    clear hw'
    have hw : w ∈ IntermediateField.adjoin F₁ {z} := hz.adjoin_eq_top ▸ IntermediateField.mem_top
    induction hw using IntermediateField.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ hx
    | algebraMap a =>
      rw [← he a]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => exact add_mem hx hy
    | inv x _ hx => exact inv_mem hx
    | mul x y _ _ hx hy => exact mul_mem hx hy
  · let φ : B.comap (algebraMap F₁ l) →+* B.comap (algebraMap F₂ l) :=
      (e : F₁ →+* F₂).restrict _ _ fun a ha ↦ by
        change algebraMap F₂ l (e a) ∈ B
        rw [he]
        exact ha
    have := IsIntegral.map_of_comp_eq φ (RingHom.id l) (by ext a; exact he a) hz.isIntegral
    exact this
  · rw [hmin, hq, derivative_map, aeval_def, eval₂_map, hcomp, ← aeval_def]
    exact hz.valuation_aeval_derivative

/-- If `F → l` is surjective, then `1` is a standard-unramified generator. -/
theorem isStdUnramifiedGenerator_one_of_surjective (B : ValuationSubring l)
    (h : Function.Surjective (algebraMap F₁ l)) : IsStdUnramifiedGenerator F₁ B 1 := by
  refine ⟨DVRCoordinate.adjoin_one_eq_top_of_surjective h, isIntegral_one, ?_⟩
  rw [minpoly.one, derivative_sub, derivative_X, derivative_one, sub_zero, map_one, map_one]

/-- A finite separable extension has a nonzero standard-unramified generator for the trivial
valuation. -/
theorem exists_isStdUnramifiedGenerator_top [FiniteDimensional F₁ l] [Algebra.IsSeparable F₁ l] :
    ∃ x : l, x ≠ 0 ∧ IsStdUnramifiedGenerator F₁ (⊤ : ValuationSubring l) x := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element F₁ l
  by_cases hx0 : x = 0
  · refine ⟨1, one_ne_zero, isStdUnramifiedGenerator_one_of_surjective _ fun w ↦ ?_⟩
    have hw : w ∈ (⊥ : IntermediateField F₁ l) := by
      rw [← IntermediateField.adjoin_zero, ← hx0, hx]
      exact IntermediateField.mem_top
    exact IntermediateField.mem_bot.mp hw
  have hint : IsIntegral F₁ x := Algebra.IsIntegral.isIntegral x
  refine ⟨x, hx0, hx, isIntegral_comap_of_coeff_mem _ hint fun _ ↦ trivial, ?_⟩
  have hne : aeval x (derivative (minpoly F₁ x)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable F₁ x).aeval_derivative_ne_zero (minpoly.aeval F₁ x)
  have : IsUnit (⟨_, trivial⟩ : (⊤ : ValuationSubring l)) :=
    isUnit_iff_ne_zero.mpr fun h ↦ hne (congrArg Subtype.val h)
  exact ((⊤ : ValuationSubring l).valuation_eq_one_iff _).mp this

end Generators

end DeJongAlterations.StableModification.Valuation.MainUniformization
