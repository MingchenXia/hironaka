import Hironaka.Geometry.MonomialBlowupRegularBaseSNCIntersection

/-! Original remaining component equations on actual regular SNC intersections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCQuotientParameters

open SpecIdealSheaf Scheme.IdealSheafData MonomialBlowupRegularBaseSNCIntersection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original nonzero equation of an actual principal regular-local quotient is itself a parameter. -/
theorem original_principal_parameter {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (t : R) (ht : t ∈ maximalIdeal R) (htne : t ≠ 0)
    [IsRegularLocalRing (R ⧸ Ideal.span {t})] : t ∉ maximalIdeal R ^ 2 := by
  let : IsDomain R := Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing R
  have hne : (Ideal.span {t} : Ideal R) ≠ ⊥ := by
    intro h
    apply htne
    have hm : t ∈ (⊥ : Ideal R) := h ▸ Ideal.subset_span (Set.mem_singleton t)
    exact hm
  have hheight : (Ideal.span {t} : Ideal R).height ≤ 1 :=
    Ideal.height_span_singleton_le_one (by simpa only [mem_maximalIdeal, mem_nonunits_iff] using ht)
  obtain ⟨b, _, hb, _, hspan⟩ :=
    SNCSubdivisorAlgebra.exists_regular_kernel_generator (Ideal.Quotient.mk (Ideal.span {t}))
      Ideal.Quotient.mk_surjective (by simpa only [Ideal.mk_ker] using hne)
      (by simpa only [Ideal.mk_ker] using hheight)
  have hspan' : Ideal.span {b} = Ideal.span {t} := by simpa only [Ideal.mk_ker] using hspan
  have hbt : t ∣ b := Ideal.mem_span_singleton.mp (by
    rw [← hspan']; exact Ideal.subset_span (Set.mem_singleton _))
  intro h
  obtain ⟨c, hc⟩ := hbt
  apply hb
  rw [hc]
  exact (maximalIdeal R ^ 2).mul_mem_right c h

universe u
variable {A : Type u} [CommRing A]

local instance componentDecidableEq (D : (Spec (CommRingCat.of A)).IdealSheafData) :
    DecidableEq (DivisorComponent D) := Classical.typeDecidableEq _

/-- Inserting the original actual component equation gives the exact original intersection ideal sum. -/
theorem intersectionIdeal_insert_equation
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (J : Finset (DivisorComponent D))
    (C : DivisorComponent D) (t : A)
    (heq : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val) :
    intersectionIdeal D (insert C J) = Ideal.span {t} ⊔ intersectionIdeal D J := by
  classical
  apply (specIdealSheafEquiv A).symm.injective
  change specIdealSheaf A (intersectionIdeal D (insert C J)) =
    specIdealSheaf A (Ideal.span {t} ⊔ intersectionIdeal D J)
  have hsup : specIdealSheaf A (Ideal.span {t} ⊔ intersectionIdeal D J) =
      specIdealSheaf A (Ideal.span {t}) ⊔ specIdealSheaf A (intersectionIdeal D J) :=
    (specIdealSheafEquiv A).symm.map_sup _ _
  rw [intersectionIdeal_spec, hsup, heq, intersectionIdeal_spec]
  unfold componentIntersection
  apply le_antisymm
  · refine iSup_le fun C' ↦ iSup_le fun hC' ↦ ?_
    rcases Finset.mem_insert.mp hC' with h | h
    · subst C'
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup_of_le C' (le_iSup_of_le h le_rfl))
  · apply sup_le
    · exact le_iSup_of_le C (le_iSup_of_le (Finset.mem_insert_self C J) le_rfl)
    · refine iSup_le fun C' ↦ iSup_le fun hC' ↦ ?_
      exact le_iSup_of_le C' (le_iSup_of_le (Finset.mem_insert_of_mem hC') le_rfl)

variable [IsRegularRing A]

/-- The literal image of a remaining SNC equation is nonzero and a local parameter on the actual intersection quotient. -/
theorem remaining_equation_local_parameter
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (J : Finset (DivisorComponent D)) (hJ : J.Nonempty)
    (C : DivisorComponent D) (hC : C ∉ J) (t : A)
    (heq : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (p : Ideal A) [p.IsPrime] (hIp : intersectionIdeal D J ≤ p) (ht : t ∈ p) :
    let L := Localization.AtPrime p
    let I := (intersectionIdeal D J).map (algebraMap A L)
    let Q := L ⧸ I
    ∃ hlocal : IsLocalRing Q,
      letI := hlocal
      Ideal.Quotient.mk I (algebraMap A L t) ∈ maximalIdeal Q ∧
      Ideal.Quotient.mk I (algebraMap A L t) ∉ maximalIdeal Q ^ 2 := by
  classical
  let L := Localization.AtPrime p
  let I := (intersectionIdeal D J).map (algebraMap A L)
  let a : L := algebraMap A L t
  let Q := L ⧸ I
  have hdata := intersection_local_data D hD J hJ p hIp
  let : IsRegularLocalRing Q := hdata.1
  have hinsert : intersectionIdeal D (insert C J) ≤ p := by
    rw [intersectionIdeal_insert_equation D J C t heq]
    exact sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ht)) hIp
  have hnext := intersection_local_data D hD (insert C J) (Finset.insert_nonempty C J) p hinsert
  have hmap : (intersectionIdeal D (insert C J)).map (algebraMap A L) =
      I ⊔ Ideal.span {a} := by
    rw [intersectionIdeal_insert_equation D J C t heq, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton, sup_comm]
  have hne : Ideal.Quotient.mk I a ≠ 0 := by
    intro hzero
    have ha : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    have hEq : (intersectionIdeal D (insert C J)).map (algebraMap A L) = I := by
      rw [hmap, sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))]
    have hh : (insert C J).card = J.card := by
      exact_mod_cast hnext.2.symm.trans ((congrArg Ideal.height hEq).trans hdata.2)
    rw [Finset.card_insert_of_notMem hC] at hh
    omega
  have hqideal : (Ideal.span {a}).map (Ideal.Quotient.mk I) =
      Ideal.span {Ideal.Quotient.mk I a} := by rw [Ideal.map_span, Set.image_singleton]
  let e : (Q ⧸ Ideal.span {Ideal.Quotient.mk I a}) ≃+* L ⧸ I ⊔ Ideal.span {a} :=
    (Ideal.quotEquivOfEq hqideal.symm).trans (DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {a}))
  let : IsRegularLocalRing (L ⧸ I ⊔ Ideal.span {a}) := by rw [← hmap]; exact hnext.1
  let : IsRegularLocalRing (Q ⧸ Ideal.span {Ideal.Quotient.mk I a}) :=
    IsRegularLocalRing.of_ringEquiv e.symm
  have haL : a ∈ maximalIdeal L := (IsLocalization.AtPrime.to_map_mem_maximal_iff L p t).mpr ht
  have haQ : Ideal.Quotient.mk I a ∈ maximalIdeal Q := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective]
    exact Ideal.mem_map_of_mem (Ideal.Quotient.mk I) haL
  exact ⟨inferInstance, haQ, original_principal_parameter _ haQ hne⟩

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCQuotientParameters
