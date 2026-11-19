import Hironaka.Resolution.HironakaActualCanonicalDirectionPivot
import Hironaka.Resolution.HironakaActualFormalBlowupAllDirections
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Genuine triangular shears preserve the SAME actual initial diagram and canonical reduced family. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualCanonicalTriangularShear
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualCanonicalDirectionPivot
  HironakaActualFormalBlowupAllDirections
variable {n : ℕ}

private def MonicAt (m : MonomialOrder (Fin n)) (F : MvPowerSeries (Fin n) ℂ)
    (a : Fin n →₀ ℕ) : Prop :=
  MvPowerSeries.coeff a F=1 ∧ ∀ β, m.toSyn β < m.toSyn a → MvPowerSeries.coeff β F=0

private theorem monicAt_ne_zero (m : MonomialOrder (Fin n)) (F : MvPowerSeries (Fin n) ℂ)
    (a : Fin n →₀ ℕ) (h : MonicAt m F a) : F ≠ 0 := by
  intro hz
  have hh := h.1
  rw [hz,map_zero] at hh
  exact zero_ne_one hh

private theorem monicAt_initial (m : MonomialOrder (Fin n)) (F : MvPowerSeries (Fin n) ℂ)
    (a : Fin n →₀ ℕ) (h : MonicAt m F a) :
    actualInitialExponent m F (monicAt_ne_zero m F a h)=a :=
  actualInitialExponent_eq_of_coefficients m F _ a (by rw [h.1]; exact one_ne_zero) h.2

private theorem monicAt_mul (m : MonomialOrder (Fin n))
    (F G : MvPowerSeries (Fin n) ℂ) (a c : Fin n →₀ ℕ)
    (hF : MonicAt m F a) (hG : MonicAt m G c) : MonicAt m (F*G) (a+c) := by
  have hFn := monicAt_ne_zero m F a hF
  have hGn := monicAt_ne_zero m G c hG
  have hFa := monicAt_initial m F a hF
  have hGc := monicAt_initial m G c hG
  have hprod := actualInitialExponent_mul m F G hFn hGn
  rw [hFa,hGc] at hprod
  constructor
  · have hc := coeff_mul_actualInitialExponent m F G hFn hGn
    simpa only [hFa,hGc,hF.1,hG.1,one_mul] using hc
  · intro β hβ
    apply coeff_eq_zero_of_lt_actualInitialExponent m (F*G) (mul_ne_zero hFn hGn) β
    rwa [hprod]

private theorem monicAt_one (m : MonomialOrder (Fin n)) :
    MonicAt m (1 : MvPowerSeries (Fin n) ℂ) 0 := by
  constructor
  · simp
  · intro β hβ
    rw [map_zero] at hβ
    exact False.elim ((not_lt_of_ge (m.zero_le (m.toSyn β))) hβ)

private theorem monicAt_X (m : MonomialOrder (Fin n)) (i : Fin n) :
    MonicAt m (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ) (Finsupp.single i 1) := by
  constructor
  · simp
  · intro β hβ
    have hne : β ≠ Finsupp.single i 1 := by
      intro h
      exact (ne_of_lt hβ) (congrArg m.toSyn h)
    simp only [MvPowerSeries.coeff_X,if_neg hne]

/-- Actual triangular coordinate formulas have their unchanged monic minima. -/
theorem actualFormalCenterShear_coordinate_initial_data (m : MonomialOrder (Fin n))
    (f : Fin n) (b : Fin n → ℂ)
    (htri : ∀ i : Fin n, i ≠ f → b i ≠ 0 →
      m.toSyn (Finsupp.single i 1) < m.toSyn (Finsupp.single f 1)) (i : Fin n) :
    MvPowerSeries.coeff (Finsupp.single i 1) (actualFormalCenterShearCoordinates Set.univ f b i)=1 ∧
      ∀ β, m.toSyn β < m.toSyn (Finsupp.single i 1) →
        MvPowerSeries.coeff β (actualFormalCenterShearCoordinates Set.univ f b i)=0 := by
  by_cases hi : i=f
  · subst i
    simpa only [MonicAt,actualFormalCenterShearCoordinates,Set.mem_sdiff,Set.mem_univ,
      Set.mem_singleton_iff,not_true_eq_false,and_false,if_false,add_zero] using monicAt_X m f
  · by_cases hb : b i=0
    · simpa [MonicAt,actualFormalCenterShearCoordinates,hi,hb] using monicAt_X m i
    · have hif : Finsupp.single i 1 ≠ Finsupp.single f 1 := by
        intro h
        exact hi (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) h)
      constructor
      · simp [actualFormalCenterShearCoordinates,hi,MvPowerSeries.coeff_X,hif]
      · intro β hβ
        have hβi : β ≠ Finsupp.single i 1 := by
          intro h
          exact (ne_of_lt hβ) (congrArg m.toSyn h)
        have hβf : β ≠ Finsupp.single f 1 := by
          intro h
          exact (ne_of_lt (hβ.trans (htri i hi hb))) (congrArg m.toSyn h)
        simp [actualFormalCenterShearCoordinates,hi,MvPowerSeries.coeff_X,hβi,hβf]

private theorem coordinate_power_monic (m : MonomialOrder (Fin n)) (f : Fin n) (b : Fin n → ℂ)
    (htri : ∀ i : Fin n, i ≠ f → b i ≠ 0 →
      m.toSyn (Finsupp.single i 1) < m.toSyn (Finsupp.single f 1)) (i : Fin n) (k : ℕ) :
    MonicAt m ((actualFormalCenterShearCoordinates Set.univ f b i)^k) (Finsupp.single i k) := by
  induction k with
  | zero => simpa only [pow_zero,Finsupp.single_zero] using monicAt_one m
  | succ k ih =>
    simpa only [pow_succ,Finsupp.single_add] using
      monicAt_mul m _ _ (Finsupp.single i k) (Finsupp.single i 1) ih
        (actualFormalCenterShear_coordinate_initial_data m f b htri i)

private theorem monicAt_finset_prod {ι : Type*} [DecidableEq ι]
    (m : MonomialOrder (Fin n)) (s : Finset ι) (F : ι → MvPowerSeries (Fin n) ℂ)
    (a : ι → (Fin n →₀ ℕ)) (h : ∀ i ∈ s, MonicAt m (F i) (a i)) :
    MonicAt m (∏ i ∈ s,F i) (∑ i ∈ s,a i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,Finset.sum_empty] using monicAt_one m
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact monicAt_mul m _ _ _ _ (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem shear_coordinate_product_monic (m : MonomialOrder (Fin n))
    (f : Fin n) (b : Fin n → ℂ)
    (htri : ∀ i : Fin n, i ≠ f → b i ≠ 0 →
      m.toSyn (Finsupp.single i 1) < m.toSyn (Finsupp.single f 1)) (α : Fin n →₀ ℕ) :
    MonicAt m (α.prod (fun i k => (actualFormalCenterShearCoordinates Set.univ f b i)^k)) α := by
  have h := monicAt_finset_prod m α.support
    (fun i => (actualFormalCenterShearCoordinates Set.univ f b i)^(α i))
    (fun i => Finsupp.single i (α i)) (fun i _ => coordinate_power_monic m f b htri i (α i))
  have hexp : (∑ i ∈ α.support,Finsupp.single i (α i))=α := by
    simpa only [Finsupp.sum] using α.sum_single
  simpa only [Finsupp.prod,hexp] using h

/-- Genuine whole formal triangular substitution preserves the unchanged actual minimum. -/
theorem actualFormalCenterShear_initialExponent (m : MonomialOrder (Fin n))
    (f : Fin n) (b : Fin n → ℂ)
    (htri : ∀ i : Fin n, i ≠ f → b i ≠ 0 →
      m.toSyn (Finsupp.single i 1) < m.toSyn (Finsupp.single f 1))
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) :
    ∃ hSF : actualFormalCenterShear Set.univ f b F ≠ 0,
      actualInitialExponent m (actualFormalCenterShear Set.univ f b F) hSF=
        actualInitialExponent m F hF := by
  let a := actualInitialExponent m F hF
  have hcoeff : MvPowerSeries.coeff a (actualFormalCenterShear Set.univ f b F)=MvPowerSeries.coeff a F := by
    rw [actualFormalCenterShear,MvPowerSeries.substAlgHom_apply,
      MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
        (actualFormalCenterShearCoordinates_constant_zero Set.univ f b)) F a]
    rw [finsum_eq_single _ a]
    · rw [(shear_coordinate_product_monic m f b htri a).1,smul_eq_mul,mul_one]
    · intro β hβ
      by_cases hc : MvPowerSeries.coeff β F=0
      · rw [hc,zero_smul]
      · have hlt : m.toSyn a < m.toSyn β := by
          apply lt_of_le_of_ne ((actualInitialExponent_spec m F hF).2 β hc)
          intro he
          exact hβ (m.toSyn.injective he).symm
        rw [(shear_coordinate_product_monic m f b htri β).2 a hlt,smul_zero]
  have hSF : actualFormalCenterShear Set.univ f b F ≠ 0 := by
    intro hz
    have hn := (actualInitialExponent_spec m F hF).1
    rw [← hcoeff,hz,map_zero] at hn
    exact hn rfl
  refine ⟨hSF,?_⟩
  apply actualInitialExponent_eq_of_coefficients m _ hSF a
  · rw [hcoeff]
    exact (actualInitialExponent_spec m F hF).1
  · intro γ hγ
    rw [actualFormalCenterShear,MvPowerSeries.substAlgHom_apply,
      MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
        (actualFormalCenterShearCoordinates_constant_zero Set.univ f b)) F γ]
    apply finsum_eq_zero_of_forall_eq_zero
    intro β
    by_cases hc : MvPowerSeries.coeff β F=0
    · rw [hc,zero_smul]
    · have hlt := hγ.trans_le ((actualInitialExponent_spec m F hF).2 β hc)
      rw [(shear_coordinate_product_monic m f b htri β).2 γ hlt,smul_zero]

/-- Both entire diagram directions retain the literal original diagram under the genuine triangular shear. -/
theorem actualInitialDiagram_map_centerShear (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (f : Fin n) (b : Fin n → ℂ)
    (htri : ∀ i : Fin n, i ≠ f → b i ≠ 0 →
      m.toSyn (Finsupp.single i 1) < m.toSyn (Finsupp.single f 1)) :
    actualInitialDiagram m (Ideal.map (actualFormalCenterShear Set.univ f b).toRingHom I)=
      actualInitialDiagram m I := by
  ext α
  constructor
  · rintro ⟨G,hGI,hGn,hGα⟩
    obtain ⟨F,hFI,rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (actualFormalCenterShear Set.univ f b).toRingHom
      (actualFormalCenterShearAlgEquiv Set.univ f b).surjective).mp hGI
    have hFn : F ≠ 0 := by
      intro hz
      subst F
      exact hGn (map_zero _)
    obtain ⟨hSF,hinit⟩ := actualFormalCenterShear_initialExponent m f b htri F hFn
    exact ⟨F,hFI,hFn,hinit.symm.trans hGα⟩
  · rintro ⟨F,hFI,hFn,hFα⟩
    obtain ⟨hSF,hinit⟩ := actualFormalCenterShear_initialExponent m f b htri F hFn
    exact ⟨actualFormalCenterShear Set.univ f b F,Ideal.mem_map_of_mem _ hFI,hSF,hinit.trans hFα⟩

private def shearPolynomialCoordinate (f : Fin n) (b : Fin n → ℂ) (i : Fin n) :
    MvPolynomial (Fin n) ℂ :=
  MvPolynomial.X i+if i ≠ f then MvPolynomial.C (b i)*MvPolynomial.X f else 0

private theorem shearPolynomialCoordinate_coe (f : Fin n) (b : Fin n → ℂ) (i : Fin n) :
    (shearPolynomialCoordinate f b i : MvPowerSeries (Fin n) ℂ)=
      actualFormalCenterShearCoordinates Set.univ f b i := by
  by_cases hi : i=f <;> simp [shearPolynomialCoordinate,actualFormalCenterShearCoordinates,hi]

private def shearPolynomialProduct (f : Fin n) (b : Fin n → ℂ) (α : Fin n →₀ ℕ) :
    MvPolynomial (Fin n) ℂ := α.prod (fun i k => (shearPolynomialCoordinate f b i)^k)

private theorem shearPolynomialProduct_coe (f : Fin n) (b : Fin n → ℂ) (α : Fin n →₀ ℕ) :
    (shearPolynomialProduct f b α : MvPowerSeries (Fin n) ℂ)=
      α.prod (fun i k => (actualFormalCenterShearCoordinates Set.univ f b i)^k) := by
  change MvPolynomial.coeToMvPowerSeries.ringHom
      (∏ i ∈ α.support,(shearPolynomialCoordinate f b i)^(α i))=
    ∏ i ∈ α.support,(actualFormalCenterShearCoordinates Set.univ f b i)^(α i)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow]
  exact congrArg (fun F : MvPowerSeries (Fin n) ℂ => F^(α i)) (shearPolynomialCoordinate_coe f b i)

private theorem shearPolynomialCoordinate_degreeOf_le (f : Fin n) (b : Fin n → ℂ)
    (i j : Fin n) (hi : i ≠ f) :
    (shearPolynomialCoordinate f b j).degreeOf i ≤ if j=i then 1 else 0 := by
  dsimp only [shearPolynomialCoordinate]
  apply (MvPolynomial.degreeOf_add_le i _ _).trans
  apply max_le
  · by_cases hj : j=i
    · subst j
      simp only [MvPolynomial.degreeOf_X_self,if_true,le_refl]
    · simp only [MvPolynomial.degreeOf_X,Ne.symm hj,if_false,zero_le]
  · by_cases hj : j ≠ f
    · rw [if_pos hj]
      exact (MvPolynomial.degreeOf_C_mul_le (MvPolynomial.X f) i (b j)).trans
        (by rw [MvPolynomial.degreeOf_X_of_ne hi]; exact Nat.zero_le _)
    · rw [if_neg hj,MvPolynomial.degreeOf_zero]
      exact Nat.zero_le _

private theorem shearPolynomialProduct_degreeOf_le (f : Fin n) (b : Fin n → ℂ)
    (α : Fin n →₀ ℕ) (i : Fin n) (hi : i ≠ f) :
    (shearPolynomialProduct f b α).degreeOf i ≤ α i := by
  have hsum : (∑ j ∈ α.support,α j*(if j=i then 1 else 0))=α i := by
    by_cases hs : i ∈ α.support
    · simp [hs]
    · have hz : α i=0 := Finsupp.notMem_support_iff.mp hs
      simp [hs,hz]
  calc
    _ ≤ ∑ j ∈ α.support,((shearPolynomialCoordinate f b j)^(α j)).degreeOf i :=
      MvPolynomial.degreeOf_prod_le i α.support _
    _ ≤ ∑ j ∈ α.support,α j*(if j=i then 1 else 0) := by
      apply Finset.sum_le_sum
      intro j _
      exact (MvPolynomial.degreeOf_pow_le i _ _).trans
        (Nat.mul_le_mul_left (α j) (shearPolynomialCoordinate_degreeOf_le f b i j hi))
    _=α i := hsum

private theorem shear_coordinate_product_support_le (f : Fin n) (b : Fin n → ℂ)
    (α γ : Fin n →₀ ℕ)
    (hγ : MvPowerSeries.coeff γ
      (α.prod (fun i k => (actualFormalCenterShearCoordinates Set.univ f b i)^k)) ≠ 0)
    (i : Fin n) (hi : i ≠ f) : γ i ≤ α i := by
  have hpoly : MvPolynomial.coeff γ (shearPolynomialProduct f b α) ≠ 0 := by
    rwa [← shearPolynomialProduct_coe,MvPolynomial.coeff_coe] at hγ
  exact (MvPolynomial.le_degreeOf_of_mem_support i (MvPolynomial.mem_support_iff.mpr hpoly)).trans
    (shearPolynomialProduct_degreeOf_le f b α i hi)

/-- The genuine shear preserves the ENTIRE same diagram-complement support. -/
theorem actualFormalCenterShear_normal_support (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (f : Fin n) (b : Fin n → ℂ)
    (hv : ∀ a : actualInitialVertices m I, a.val f=0)
    (F : MvPowerSeries (Fin n) ℂ)
    (hF : ∀ α ∈ actualInitialDiagram m I, MvPowerSeries.coeff α F=0) :
    ∀ γ ∈ actualInitialDiagram m I,
      MvPowerSeries.coeff γ (actualFormalCenterShear Set.univ f b F)=0 := by
  intro γ hγ
  rw [actualFormalCenterShear,MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (actualFormalCenterShearCoordinates_constant_zero Set.univ f b)) F γ]
  apply finsum_eq_zero_of_forall_eq_zero
  intro α
  by_cases hc : MvPowerSeries.coeff γ
      (α.prod (fun i k => (actualFormalCenterShearCoordinates Set.univ f b i)^k))=0
  · rw [hc,smul_zero]
  · have hle : γ.erase f ≤ α.erase f := by
      intro i
      by_cases hi : i=f
      · subst i
        simp
      · simpa only [Finsupp.erase_ne hi] using shear_coordinate_product_support_le f b α γ hc i hi
    have hγer : γ.erase f ∈ actualInitialDiagram m I :=
      (actualInitialDiagram_erase_iff_of_vertices_zero m I f hv γ).mp hγ
    have hαer : α.erase f ∈ actualInitialDiagram m I :=
      actualInitialDiagram_upper m I _ _ hγer hle
    have hα : α ∈ actualInitialDiagram m I :=
      (actualInitialDiagram_erase_iff_of_vertices_zero m I f hv α).mpr hαer
    rw [hF α hα,zero_smul]

private theorem shearPolynomialCoordinate_homogeneous (f : Fin n) (b : Fin n → ℂ) (i : Fin n) :
    (shearPolynomialCoordinate f b i).IsHomogeneous 1 := by
  dsimp only [shearPolynomialCoordinate]
  split_ifs
  · exact (MvPolynomial.isHomogeneous_X _ _).add (MvPolynomial.isHomogeneous_C_mul_X _ _)
  · simpa only [add_zero] using (MvPolynomial.isHomogeneous_X ℂ i)

private theorem shearPolynomialProduct_homogeneous (f : Fin n) (b : Fin n → ℂ) (α : Fin n →₀ ℕ) :
    (shearPolynomialProduct f b α).IsHomogeneous (normalExponentDegree α) := by
  have hh := MvPolynomial.IsHomogeneous.prod α.support
    (fun i => (shearPolynomialCoordinate f b i)^(α i)) (fun i => α i)
    (fun i _ => by simpa only [one_mul] using (shearPolynomialCoordinate_homogeneous f b i).pow (α i))
  have hsum : (∑ i ∈ α.support, α i) = normalExponentDegree α := by
    exact α.sum_fintype (fun _ k => k) (fun _ => rfl)
  simpa only [shearPolynomialProduct,Finsupp.prod,hsum] using hh

private theorem degree_split (f : Fin n) (γ : Fin n →₀ ℕ) :
    normalExponentDegree γ=γ f+normalExponentDegree (γ.erase f) := by
  have he : Finsupp.single f (γ f)+γ.erase f=γ := by
    ext i
    by_cases hi : i=f
    · subst i
      simp
    · simp [hi]
  have h := (congrArg normalExponentDegree he).symm
  simpa [normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib] using h

private theorem shear_monomial_diagram_coefficient (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (f : Fin n) (b : Fin n → ℂ)
    (htri : ∀ i : Fin n, i ≠ f → b i ≠ 0 →
      m.toSyn (Finsupp.single i 1) < m.toSyn (Finsupp.single f 1))
    (hv : ∀ a : actualInitialVertices m I, a.val f=0)
    (a : actualInitialVertices m I) (γ : Fin n →₀ ℕ) (hγ : γ ∈ actualInitialDiagram m I) :
    MvPowerSeries.coeff γ (actualFormalCenterShear Set.univ f b (MvPowerSeries.monomial a.val 1))=
      if γ=a.val then 1 else 0 := by
  rw [actualFormalCenterShear,MvPowerSeries.substAlgHom_monomial]
  simp only [map_one,one_mul]
  by_cases hγa : γ=a.val
  · rw [if_pos hγa,hγa]
    exact (shear_coordinate_product_monic m f b htri a.val).1
  · rw [if_neg hγa]
    by_contra hc
    have hγer : γ.erase f ∈ actualInitialDiagram m I :=
      (actualInitialDiagram_erase_iff_of_vertices_zero m I f hv γ).mp hγ
    have hle : γ.erase f ≤ a.val := by
      intro i
      by_cases hi : i=f
      · subst i
        simp
      · simpa only [Finsupp.erase_ne hi] using shear_coordinate_product_support_le f b a.val γ hc i hi
    have hminimal : Minimal (· ∈ actualInitialDiagram m I) a.val := by
      simpa only [actualInitialVertices,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using a.property
    have herase : γ.erase f=a.val := le_antisymm hle (hminimal.2 hγer hle)
    have hpoly : MvPolynomial.coeff γ (shearPolynomialProduct f b a.val) ≠ 0 := by
      rwa [← shearPolynomialProduct_coe,MvPolynomial.coeff_coe] at hc
    have hdeg : normalExponentDegree γ=normalExponentDegree a.val := by
      simpa only [Finsupp.weight_eq_sum,Pi.one_apply,smul_eq_mul,mul_one,normalExponentDegree] using
        shearPolynomialProduct_homogeneous f b a.val hpoly
    have hsplit := degree_split f γ
    have hcoord : γ f=0 := by rw [herase] at hsplit; omega
    apply hγa
    ext i
    by_cases hi : i=f
    · subst i
      rw [hcoord,hv a]
    · have hh := congrArg (fun β : Fin n →₀ ℕ => β i) herase
      simpa only [Finsupp.erase_ne hi] using hh

/-- The genuine same-exponent vertex dictionary under the ACTUAL triangular shear. -/
def actualCenterShearVertex (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (f : Fin n) (b : Fin n → ℂ)
    (htri : ∀ i : Fin n, i ≠ f → b i ≠ 0 →
      m.toSyn (Finsupp.single i 1) < m.toSyn (Finsupp.single f 1))
    (a : actualInitialVertices m I) :
    actualInitialVertices m (Ideal.map (actualFormalCenterShear Set.univ f b).toRingHom I) :=
  ⟨a.val,by simpa only [actualInitialVertices,actualInitialDiagram_map_centerShear m I f b htri]
    using a.property⟩

/-- Genuine covariance of the SAME canonical reduced member, with no independent choice of vertices. -/
theorem actualFormalCenterShear_actualReducedVertexSeries (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (f : Fin n) (b : Fin n → ℂ)
    (htri : ∀ i : Fin n, i ≠ f → b i ≠ 0 →
      m.toSyn (Finsupp.single i 1) < m.toSyn (Finsupp.single f 1))
    (hv : ∀ a : actualInitialVertices m I, a.val f=0) (a : actualInitialVertices m I) :
    actualFormalCenterShear Set.univ f b (actualReducedVertexSeries m I a)=
      actualReducedVertexSeries m
        (Ideal.map (actualFormalCenterShear Set.univ f b).toRingHom I)
          (actualCenterShearVertex m I f b htri a) := by
  have hnormal : ∀ α ∈ actualInitialDiagram m I,
      MvPowerSeries.coeff α (actualReducedVertexSeries m I a-MvPowerSeries.monomial a.val 1)=0 := by
    intro α hα
    rw [map_sub,actualReducedVertexSeries_coefficient_diagram m I a α hα,MvPowerSeries.coeff_monomial]
    exact sub_self _
  have hshearnormal := actualFormalCenterShear_normal_support m I f b hv _ hnormal
  apply actualReducedVertexSeries_unique m
    (Ideal.map (actualFormalCenterShear Set.univ f b).toRingHom I)
    (actualCenterShearVertex m I f b htri a) _
    (Ideal.mem_map_of_mem _ (actualReducedVertexSeries_mem m I a))
  intro γ hγ
  have hγI : γ ∈ actualInitialDiagram m I := by
    rwa [actualInitialDiagram_map_centerShear m I f b htri] at hγ
  have hh := hshearnormal γ hγI
  rw [map_sub,map_sub] at hh
  have heq := sub_eq_zero.mp hh
  exact heq.trans (shear_monomial_diagram_coefficient m I f b htri hv a γ hγI)

end
end Hironaka.HironakaActualCanonicalTriangularShear
