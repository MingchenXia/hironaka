/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Regular local quotients by parameters

The finite-basis helper is extracted, with its proof retained, from
`EnvelopeProperty/EnvelopeProperty/Local/BoundaryPresentation.lean`, SHA256
`c2f9fa142b440589aeea8fbe6e389f1bd8340adc87b1da0a2afbe091cb030bd0`.
Only pure linear algebra is reused; no analytic EnvelopeProperty module is imported.
-/

open IsLocalRing

namespace DeJongAlterations.Algebra.RegularQuotient

/-- A nonzero vector `v` of a finite dimensional vector space is the first vector `b 0` of a basis
`b` indexed by `Fin (M + 1)`. -/
theorem exists_basis_fin_zero_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {v : V} (hv : v ≠ 0) :
    ∃ (M : ℕ) (b : Module.Basis (Fin (M + 1)) K V), b 0 = v := by
  classical
  have hs : LinearIndepOn K id ({v} : Set V) := (linearIndepOn_singleton_iff K).2 hv
  set b := Module.Basis.extend hs
  have : Finite (hs.extend (Set.subset_univ _)) := Module.Finite.finite_basis b
  let a0 : hs.extend (Set.subset_univ _) := ⟨v, Module.Basis.subset_extend hs rfl⟩
  have : Fintype {x : hs.extend (Set.subset_univ _) // x ≠ a0} := Fintype.ofFinite _
  let eM := Fintype.equivFin {x : hs.extend (Set.subset_univ _) // x ≠ a0}
  let g : Fin (Fintype.card {x : hs.extend (Set.subset_univ _) // x ≠ a0} + 1) ≃
      hs.extend (Set.subset_univ _) :=
    (finSuccEquiv _).trans ((Equiv.optionCongr eM.symm).trans (Equiv.optionSubtypeNe a0))
  refine ⟨_, b.reindex g.symm, ?_⟩
  have hg : g 0 = a0 := by
    simp only [g, Equiv.trans_apply, finSuccEquiv_zero, Equiv.optionCongr_apply,
      Option.map_none]
    rfl
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, Module.Basis.coe_extend, hg]

/-- A principal quotient loses at most one dimension, derived from the local height inequality. -/
theorem ringKrullDim_le_quotient_parameter_add_one (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {t : R} (ht : t ∈ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {t}) + 1 := by
  simpa only [maximalIdeal_height_eq_ringKrullDim] using
    (Ideal.height_le_ringKrullDim_quotient_add_one (p := maximalIdeal R) ht)

/-- A parameter belongs to an internally constructed minimal family of maximal-ideal generators. -/
theorem exists_parameter_generators (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (t : R) (ht : t ∈ maximalIdeal R)
    (ht2 : t ∉ maximalIdeal R ^ 2) :
    ∃ (n : ℕ) (x : Fin n → R),
      Ideal.span (insert t (Set.range x)) = maximalIdeal R ∧
        (maximalIdeal R).spanFinrank = n + 1 := by
  classical
  let m := maximalIdeal R
  let v : CotangentSpace R := m.toCotangent ⟨t, ht⟩
  have hv : v ≠ 0 := fun h ↦ ht2 ((m.toCotangent_eq_zero ⟨t, ht⟩).mp h)
  obtain ⟨n, b, hb⟩ := exists_basis_fin_zero_eq (K := ResidueField R) hv
  choose x hx using fun i : Fin n ↦ m.toCotangent_surjective (b i.succ)
  let y : Fin (n + 1) → m := Fin.cons ⟨t, ht⟩ x
  have hy : m.toCotangent ∘ y = b := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [Function.comp_apply, y, Fin.cons_zero] using hb.symm
    · exact hx j
  have hcot : Submodule.span (ResidueField R) (m.toCotangent '' Set.range y) = ⊤ := by
    rw [← Set.range_comp, hy]
    exact b.span_eq
  have hspan : Submodule.span R (Set.range y) = ⊤ :=
    CotangentSpace.span_image_eq_top_iff.mp hcot
  refine ⟨n, fun i ↦ (x i : R), ?_, ?_⟩
  · have hring : Ideal.span (Set.range fun i ↦ (y i : R)) = m := by
      calc
        Ideal.span (Set.range fun i ↦ (y i : R)) =
            (Submodule.span R (Set.range y)).map m.subtype := by
          rw [Submodule.map_span, ← Set.range_comp]
          rfl
        _ = m := by rw [hspan, Submodule.map_top, Submodule.range_subtype]
    have hrange : (fun i ↦ (y i : R)) = Fin.cons t (fun i ↦ (x i : R)) := by
      funext i
      refine Fin.cases rfl (fun _ ↦ rfl) i
    simpa only [hrange, Fin.range_cons] using hring
  · rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b

/-- A surjective local-ring map killing one generator drops the maximal-ideal generator bound. -/
theorem maximalIdeal_spanFinrank_le_of_surjective_kill_generator
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f) {t : R} (hft : f t = 0)
    (n : ℕ) (x : Fin n → R)
    (hgen : Ideal.span (insert t (Set.range x)) = maximalIdeal R) :
    (maximalIdeal S).spanFinrank ≤ n := by
  have hgenS : Ideal.span (Set.range fun i ↦ f (x i)) = maximalIdeal S := by
    rw [← map_maximalIdeal_of_surjective f hf, ← hgen, Ideal.map_span,
      Set.image_insert_eq, hft, Ideal.span_insert_zero, ← Set.range_comp]
    rfl
  rw [← hgenS]
  apply (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans
  simpa using (Set.ncard_image_le (f := fun i : Fin n ↦ f (x i)) Set.finite_univ)

/-- The actual principal quotient by a nonzero cotangent parameter is regular. -/
theorem isRegularLocalRing_quotient_parameter (R : Type*) [CommRing R]
    [IsRegularLocalRing R] (t : R) (ht : t ∈ maximalIdeal R)
    (ht2 : t ∉ maximalIdeal R ^ 2) : IsRegularLocalRing (R ⧸ Ideal.span {t}) := by
  let Q := R ⧸ Ideal.span {t}
  have hle : Ideal.span {t} ≤ maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem (maximalIdeal R)).mpr ht
  have hproper : Ideal.span {t} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hle
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {t})) Ideal.Quotient.mk_surjective
  obtain ⟨n, x, hgen, hrank⟩ := exists_parameter_generators R t ht ht2
  have hft : Ideal.Quotient.mk (Ideal.span {t}) t = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton t))
  have hqgen := maximalIdeal_spanFinrank_le_of_surjective_kill_generator
    (Ideal.Quotient.mk (Ideal.span {t})) Ideal.Quotient.mk_surjective hft n x hgen
  have hdim := ringKrullDim_le_quotient_parameter_add_one R ht
  have hregular : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    (isRegularLocalRing_iff R).mp inferInstance
  rw [← hregular, hrank] at hdim
  have hn : (n : WithBot ℕ∞) ≤ ringKrullDim Q :=
    ENat.WithBot.add_le_add_one_right_iff.mp (by
      simpa only [Nat.cast_add, Nat.cast_one] using hdim)
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  exact (show ((maximalIdeal Q).spanFinrank : WithBot ℕ∞) ≤ n from by
    exact_mod_cast hqgen).trans hn

/-- The actual parameter quotient has dimension exactly one less than the regular local ring. -/
theorem ringKrullDim_quotient_parameter_add_one_eq (R : Type*) [CommRing R]
    [IsRegularLocalRing R] (t : R) (ht : t ∈ maximalIdeal R)
    (ht2 : t ∉ maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span {t}) + 1 = ringKrullDim R := by
  let Q := R ⧸ Ideal.span {t}
  let : IsRegularLocalRing Q := isRegularLocalRing_quotient_parameter R t ht ht2
  obtain ⟨n, x, hgen, hrank⟩ := exists_parameter_generators R t ht ht2
  have hft : Ideal.Quotient.mk (Ideal.span {t}) t = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton t))
  have hqgen := maximalIdeal_spanFinrank_le_of_surjective_kill_generator
    (Ideal.Quotient.mk (Ideal.span {t})) Ideal.Quotient.mk_surjective hft n x hgen
  have hRrank : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    (isRegularLocalRing_iff R).mp inferInstance
  have hQrank : ((maximalIdeal Q).spanFinrank : WithBot ℕ∞) = ringKrullDim Q :=
    (isRegularLocalRing_iff Q).mp inferInstance
  apply le_antisymm
  · rw [← hRrank, hrank, ← hQrank]
    exact_mod_cast Nat.add_le_add_right hqgen 1
  · exact ringKrullDim_le_quotient_parameter_add_one R ht

end DeJongAlterations.Algebra.RegularQuotient
