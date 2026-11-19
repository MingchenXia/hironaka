import Hironaka.Resolution.HironakaActualHilbertSamuelWellFounded
import Hironaka.Resolution.HironakaActualProductHSProfileReflection
import Mathlib.Order.PiLex

/-! The actual entire Hilbert--Samuel lexicographic order in fixed ambient
dimension, with its genuine smooth-product order embedding. Only profiles
realized by actual whole formal or analytic ideals enter the well-founded
types. No phase decrease, maximum, resolving history or scheduler is assumed.
Blueprint: `hironaka-actual-hilbert-samuel-lex-order-20261102.tex`. -/
set_option autoImplicit false
open Set
namespace Hironaka.HironakaActualHilbertSamuelLexOrder
noncomputable section
open HolGerm HironakaHolomorphicPointJets
  HironakaActualOriginalFormalHSTransfer HironakaActualHilbertSamuelWellFounded
  HironakaRelativeNormalIdeal HironakaActualProductHSProfileReflection

/-- Genuine entire formal HS profiles, with the native lexicographic function order. -/
abbrev ActualLexHilbertSamuelProfile (n : ℕ) :=
  {H : Lex (ℕ → ℕ) // ∃ I : Ideal (MvPowerSeries (Fin n) ℂ),
    ofLex H = genuineFormalHilbertSamuelValue n I}

/-- The SAME increasing pair supplied by the actual pointwise WQO is lexicographically increasing. -/
theorem actual_hilbertSamuel_lex_wellQuasiOrdered (n : ℕ) :
    WellQuasiOrdered ((· ≤ ·) : ActualLexHilbertSamuelProfile n →
      ActualLexHilbertSamuelProfile n → Prop) := by
  intro H
  let Hp : ℕ → ActualHilbertSamuelProfile n :=
    fun j => ⟨ofLex (H j).val, (H j).property⟩
  obtain ⟨i, j, hij, hle⟩ := actual_hilbertSamuel_wellQuasiOrdered n Hp
  refine ⟨i, j, hij, ?_⟩
  change (H i).val ≤ (H j).val
  exact Pi.toLex_monotone hle

/-- Strict lexicographic descent of genuine entire profiles in fixed dimension is well founded. -/
theorem actual_hilbertSamuel_lex_wellFounded (n : ℕ) :
    WellFoundedLT (ActualLexHilbertSamuelProfile n) := by
  let : WellQuasiOrderedLE (ActualLexHilbertSamuelProfile n) :=
    ⟨actual_hilbertSamuel_lex_wellQuasiOrdered n⟩
  infer_instance

/-- Genuine entire analytic HS profiles, with the SAME native lexicographic order. -/
abbrev ActualAnalyticLexHilbertSamuelProfile (n : ℕ) :=
  {H : Lex (ℕ → ℕ) // ∃ I : Ideal (HolGerm (ComplexModel n)),
    ofLex H = hilbertSamuelValue I}

/-- Actual whole Taylor extension realizes the SAME analytic profile in the formal subtype. -/
theorem actual_analyticHilbertSamuel_lex_wellQuasiOrdered (n : ℕ) :
    WellQuasiOrdered ((· ≤ ·) : ActualAnalyticLexHilbertSamuelProfile n →
      ActualAnalyticLexHilbertSamuelProfile n → Prop) := by
  let f : ActualAnalyticLexHilbertSamuelProfile n → ActualLexHilbertSamuelProfile n :=
    fun H => ⟨H.val, by
      obtain ⟨I, hI⟩ := H.property
      obtain ⟨K, hK⟩ := analytic_hilbertSamuel_realizable I
      exact ⟨K, hI.trans hK⟩⟩
  intro H
  obtain ⟨i, j, hij, hle⟩ := actual_hilbertSamuel_lex_wellQuasiOrdered n (fun j => f (H j))
  exact ⟨i, j, hij, hle⟩

/-- The analytic realized subtype has a genuine well-founded strict lexicographic order. -/
theorem actual_analyticHilbertSamuel_lex_wellFounded (n : ℕ) :
    WellFoundedLT (ActualAnalyticLexHilbertSamuelProfile n) := by
  let : WellQuasiOrderedLE (ActualAnalyticLexHilbertSamuelProfile n) :=
    ⟨actual_analyticHilbertSamuel_lex_wellQuasiOrdered n⟩
  infer_instance

/-- No sequence of actual whole formal ideals has infinitely decreasing entire HS lexicographic values. -/
theorem no_strictAnti_actual_hilbertSamuel_lex {n : ℕ}
    (I : ℕ → Ideal (MvPowerSeries (Fin n) ℂ)) :
    ¬ StrictAnti (fun j => toLex (genuineFormalHilbertSamuelValue n (I j))) := by
  intro hanti
  let H : ℕ → ActualLexHilbertSamuelProfile n :=
    fun j => ⟨toLex (genuineFormalHilbertSamuelValue n (I j)), I j, rfl⟩
  obtain ⟨i, j, hij, hle⟩ := actual_hilbertSamuel_lex_wellQuasiOrdered n H
  exact (hanti hij).not_ge hle

/-- The SAME lexicographic no-descent law for genuine whole analytic ideals. -/
theorem no_strictAnti_analytic_hilbertSamuel_lex {n : ℕ}
    (I : ℕ → Ideal (HolGerm (ComplexModel n))) :
    ¬ StrictAnti (fun j => toLex (hilbertSamuelValue (I j))) := by
  intro hanti
  let H : ℕ → ActualAnalyticLexHilbertSamuelProfile n :=
    fun j => ⟨toLex (hilbertSamuelValue (I j)), I j, rfl⟩
  obtain ⟨i, j, hij, hle⟩ := actual_analyticHilbertSamuel_lex_wellQuasiOrdered n H
  exact (hanti hij).not_ge hle

/-- The genuine whole smooth product preserves and reflects the first differing original HS order. -/
theorem actualProductHS_lex_lt_iff (d t : ℕ)
    (I K : Ideal (HolGerm (ComplexModel d))) :
    (toLex (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom I)) <
      toLex (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom K))) ↔
        toLex (hilbertSamuelValue I) < toLex (hilbertSamuelValue K) := by
  constructor
  · rintro ⟨ℓ, hp, hlt⟩
    have h := (actualProductHS_prefix_eq_iff d t ℓ I K).mp hp
    exact ⟨ℓ, h, ((actualProductHS_comparison_of_lower_orders d t ℓ I K h).2.1).mp hlt⟩
  · rintro ⟨ℓ, hp, hlt⟩
    exact ⟨ℓ, (actualProductHS_prefix_eq_iff d t ℓ I K).mpr hp,
      ((actualProductHS_comparison_of_lower_orders d t ℓ I K hp).2.1).mpr hlt⟩

/-- Equality of the SAME actual entire smooth-product profiles is exactly original profile equality. -/
theorem actualProductHS_lex_eq_iff (d t : ℕ)
    (I K : Ideal (HolGerm (ComplexModel d))) :
    (toLex (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom I)) =
      toLex (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom K))) ↔
        toLex (hilbertSamuelValue I) = toLex (hilbertSamuelValue K) := by
  simpa only [toLex_inj, funext_iff] using actualProductHS_entire_profile_eq_iff d t I K

/-- Weak comparison is preserved and reflected by the SAME actual smooth product. -/
theorem actualProductHS_lex_le_iff (d t : ℕ)
    (I K : Ideal (HolGerm (ComplexModel d))) :
    (toLex (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom I)) ≤
      toLex (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom K))) ↔
        toLex (hilbertSamuelValue I) ≤ toLex (hilbertSamuelValue K) := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
  exact or_congr (actualProductHS_lex_lt_iff d t I K) (actualProductHS_lex_eq_iff d t I K)

private def chosenAnalyticIdeal (d : ℕ) (H : ActualAnalyticLexHilbertSamuelProfile d) :
    Ideal (HolGerm (ComplexModel d)) := H.property.choose

private theorem chosenAnalyticIdeal_spec (d : ℕ) (H : ActualAnalyticLexHilbertSamuelProfile d) :
    ofLex H.val = hilbertSamuelValue (chosenAnalyticIdeal d H) := H.property.choose_spec

private def actualSmoothProductProfile (d t : ℕ) (H : ActualAnalyticLexHilbertSamuelProfile d) :
    ActualAnalyticLexHilbertSamuelProfile (d+t) :=
  ⟨toLex (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom (chosenAnalyticIdeal d H))),
    _, rfl⟩

/-- An actual order embedding on genuinely realized analytic profiles, induced by whole smooth product. -/
def actualSmoothProductHilbertSamuelEmbedding (d t : ℕ) :
    ActualAnalyticLexHilbertSamuelProfile d ↪o ActualAnalyticLexHilbertSamuelProfile (d+t) :=
  OrderEmbedding.ofMapLEIff (actualSmoothProductProfile d t) (by
    intro H K
    change toLex (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom
      (chosenAnalyticIdeal d H))) ≤ toLex (hilbertSamuelValue
      (Ideal.map (tangentPullback d t).toRingHom (chosenAnalyticIdeal d K))) ↔ H.val ≤ K.val
    rw [actualProductHS_lex_le_iff]
    rw [←chosenAnalyticIdeal_spec d H, ←chosenAnalyticIdeal_spec d K]
    rfl)

/-- On EVERY original ideal, the embedding is exactly the profile of its actual whole ideal extension. -/
theorem actualSmoothProductHilbertSamuelEmbedding_apply (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) :
    (actualSmoothProductHilbertSamuelEmbedding d t
      ⟨toLex (hilbertSamuelValue I), I, rfl⟩).val =
        toLex (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom I)) := by
  change toLex (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom
    (chosenAnalyticIdeal d ⟨toLex (hilbertSamuelValue I), I, rfl⟩))) = _
  apply (actualProductHS_lex_eq_iff d t _ I).mpr
  exact congrArg toLex (chosenAnalyticIdeal_spec d ⟨toLex (hilbertSamuelValue I), I, rfl⟩).symm

end
end Hironaka.HironakaActualHilbertSamuelLexOrder
