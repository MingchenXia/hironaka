/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Algebra.RegularQuotient

/-!
# Regular quotients by finite independent cotangent parameters

The ideal, quotient ring, generator bounds, and dimension drop are constructed
from the given family. No quotient regularity or dimension certificate is assumed.
-/

open IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace DeJongAlterations.Algebra.RegularQuotientFamily

private theorem sumExtend_inl {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    {v : ι → V} (h : LinearIndependent K v) (i : ι) :
    Module.Basis.sumExtend h (Sum.inl i) = v i := by
  classical
  unfold Module.Basis.sumExtend
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, Module.Basis.coe_extend]
  rfl

/-- An independent cotangent family extends to actual minimal maximal-ideal generators. -/
theorem exists_family_generators (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {ι : Type*} [Fintype ι] (t : ι → maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i ↦ (maximalIdeal R).toCotangent (t i))) :
    ∃ (n : ℕ) (x : Fin n → R),
      Ideal.span (Set.range (fun i ↦ (t i : R)) ∪ Set.range x) = maximalIdeal R ∧
        (maximalIdeal R).spanFinrank = Fintype.card ι + n := by
  classical
  let m := maximalIdeal R
  let J := Module.Basis.sumExtendIndex hli
  let b := Module.Basis.sumExtend hli
  have : Finite (ι ⊕ J) := Module.Finite.finite_basis b
  have : Finite J := Finite.of_injective (Sum.inr : J → ι ⊕ J) Sum.inr_injective
  let : Fintype J := Fintype.ofFinite J
  let n := Fintype.card J
  let e : Fin n ≃ J := (Fintype.equivFin J).symm
  let b' := b.reindex (Equiv.sumCongr (Equiv.refl ι) e.symm)
  choose x hx using fun j : Fin n ↦ m.toCotangent_surjective (b' (Sum.inr j))
  let y : ι ⊕ Fin n → m := Sum.elim t x
  have hy : m.toCotangent ∘ y = b' := by
    funext i
    cases i with
    | inl i =>
      simpa [y, b', Module.Basis.reindex_apply, b] using
        (sumExtend_inl hli i).symm
    | inr j => exact hx j
  have hcot : Submodule.span (ResidueField R) (m.toCotangent '' Set.range y) = ⊤ := by
    rw [← Set.range_comp, hy]
    exact b'.span_eq
  have hspan : Submodule.span R (Set.range y) = ⊤ :=
    CotangentSpace.span_image_eq_top_iff.mp hcot
  refine ⟨n, fun j ↦ (x j : R), ?_, ?_⟩
  · have hring : Ideal.span (Set.range fun i ↦ (y i : R)) = m := by
      calc
        Ideal.span (Set.range fun i ↦ (y i : R)) =
            (Submodule.span R (Set.range y)).map m.subtype := by
          rw [Submodule.map_span, ← Set.range_comp]
          rfl
        _ = m := by rw [hspan, Submodule.map_top, Submodule.range_subtype]
    have hrange : Set.range (fun i ↦ (y i : R)) =
        Set.range (fun i ↦ (t i : R)) ∪ Set.range (fun j ↦ (x j : R)) := by
      ext z
      simp only [Set.mem_range, Set.mem_union]
      constructor
      · rintro ⟨i, rfl⟩
        cases i with
        | inl i => exact Or.inl ⟨i, rfl⟩
        | inr j => exact Or.inr ⟨j, rfl⟩
      · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
        · exact ⟨Sum.inl i, rfl⟩
        · exact ⟨Sum.inr j, rfl⟩
    rw [hrange] at hring
    exact hring
  · rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    simpa only [Fintype.card_sum, Fintype.card_fin] using Module.finrank_eq_card_basis b'

/-- Killing a specified family leaves only the complementary maximal-ideal generators. -/
theorem maximalIdeal_spanFinrank_le_of_surjective_kill_family
    {R S ι : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f) (t : ι → R)
    (hft : ∀ i, f (t i) = 0) (n : ℕ) (x : Fin n → R)
    (hgen : Ideal.span (Set.range t ∪ Set.range x) = maximalIdeal R) :
    (maximalIdeal S).spanFinrank ≤ n := by
  have hzero : Ideal.span (f '' Set.range t) = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    change f (t i) = 0
    exact hft i
  have hgenS : Ideal.span (Set.range fun j ↦ f (x j)) = maximalIdeal S := by
    calc
      Ideal.span (Set.range fun j ↦ f (x j)) = Ideal.span (f '' Set.range x) := by
        rw [← Set.range_comp]
        rfl
      _ = Ideal.map f (Ideal.span (Set.range t ∪ Set.range x)) := by
        rw [Ideal.map_span, Set.image_union, Ideal.span_union, hzero, bot_sup_eq]
      _ = maximalIdeal S := by rw [hgen, map_maximalIdeal_of_surjective f hf]
  rw [← hgenS]
  apply (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans
  simpa using (Set.ncard_image_le (f := fun i : Fin n ↦ f (x i)) Set.finite_univ)

/-- A family quotient loses at most the number of family members in Krull dimension. -/
theorem ringKrullDim_le_quotient_family_add_card (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {ι : Type*} [Fintype ι]
    (t : ι → maximalIdeal R) :
    ringKrullDim R ≤
      ringKrullDim (R ⧸ Ideal.span (Set.range fun i ↦ (t i : R))) + Fintype.card ι := by
  have hcard : (Set.range fun i ↦ (t i : R)).encard ≤ Fintype.card ι := by
    simpa only [Set.image_univ, Set.encard_univ, ENat.card_eq_coe_fintype_card] using
      Set.encard_image_le (fun i ↦ (t i : R)) Set.univ
  have hdim := Ideal.height_le_ringKrullDim_quotient_add_encard
    (p := maximalIdeal R) (Set.range fun i ↦ (t i : R)) (by
      rintro _ ⟨i, rfl⟩
      exact (t i).property)
  rw [maximalIdeal_height_eq_ringKrullDim] at hdim
  apply hdim.trans
  gcongr
  exact_mod_cast hcard

/-- The actual quotient by a finite independent cotangent family is regular. -/
theorem isRegularLocalRing_quotient_family (R : Type*) [CommRing R]
    [IsRegularLocalRing R] {ι : Type*} [Fintype ι] (t : ι → maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i ↦ (maximalIdeal R).toCotangent (t i))) :
    IsRegularLocalRing (R ⧸ Ideal.span (Set.range fun i ↦ (t i : R))) := by
  let I := Ideal.span (Set.range fun i ↦ (t i : R))
  let Q := R ⧸ I
  have hle : I ≤ maximalIdeal R := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (t i).property
  have hproper : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hle
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨n, x, hgen, hrank⟩ := exists_family_generators R t hli
  have hft (i : ι) : Ideal.Quotient.mk I (t i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hqgen := maximalIdeal_spanFinrank_le_of_surjective_kill_family
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (fun i ↦ (t i : R)) hft n x hgen
  have hdim := ringKrullDim_le_quotient_family_add_card R t
  have hregular : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    (isRegularLocalRing_iff R).mp inferInstance
  rw [← hregular, hrank] at hdim
  have hn : (n : WithBot ℕ∞) ≤ ringKrullDim Q :=
    ENat.WithBot.add_le_add_natCast_right_iff.mp (by
      simpa only [Nat.cast_add, add_comm (Fintype.card ι : WithBot ℕ∞)] using hdim)
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  exact (show ((maximalIdeal Q).spanFinrank : WithBot ℕ∞) ≤ n from by
    exact_mod_cast hqgen).trans hn

/-- Quotienting by independent cotangent parameters drops dimension by their exact number. -/
theorem ringKrullDim_quotient_family_add_card_eq (R : Type*) [CommRing R]
    [IsRegularLocalRing R] {ι : Type*} [Fintype ι] (t : ι → maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i ↦ (maximalIdeal R).toCotangent (t i))) :
    ringKrullDim (R ⧸ Ideal.span (Set.range fun i ↦ (t i : R))) + Fintype.card ι =
      ringKrullDim R := by
  let I := Ideal.span (Set.range fun i ↦ (t i : R))
  let Q := R ⧸ I
  let : IsRegularLocalRing Q := isRegularLocalRing_quotient_family R t hli
  obtain ⟨n, x, hgen, hrank⟩ := exists_family_generators R t hli
  have hft (i : ι) : Ideal.Quotient.mk I (t i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hqgen := maximalIdeal_spanFinrank_le_of_surjective_kill_family
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (fun i ↦ (t i : R)) hft n x hgen
  have hRrank : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    (isRegularLocalRing_iff R).mp inferInstance
  have hQrank : ((maximalIdeal Q).spanFinrank : WithBot ℕ∞) = ringKrullDim Q :=
    (isRegularLocalRing_iff Q).mp inferInstance
  apply le_antisymm
  · rw [← hRrank, hrank, ← hQrank]
    exact_mod_cast (Nat.add_le_add_right hqgen (Fintype.card ι)).trans_eq (Nat.add_comm _ _)
  · exact ringKrullDim_le_quotient_family_add_card R t

end DeJongAlterations.Algebra.RegularQuotientFamily
