import Hironaka.Resolution.HironakaActualZeroSectionStabilization
import Hironaka.Resolution.HironakaActualRelativeTaylorCoefficients
import Hironaka.Resolution.HironakaActualReducedFormalStandardBasis
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Whole actual diagrams and canonical division under a zero-section embedding

The actual original analytic ideal is Taylor-extended internally. The genuine
first-block inclusion is proved to preserve degLex; arbitrary renamings are
not assumed to preserve it. All added normal vertex labels are guarded by
properness. Blueprint: hironaka-actual-zero-section-canonical-basis-extension.tex.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualZeroSectionFormalBasis

noncomputable section

open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualZeroSectionStabilization HironakaActualCoefficientPresentationCentrePower
  HironakaActualRelativeTaylorCoefficients HironakaActualTaylorCoordinateNaturality
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalInitialDiagram
  HironakaActualFormalVertexDivision HironakaActualReducedFormalStandardBasis

variable {d t : ℕ}

private theorem joined_zero_degree (a : Fin d →₀ ℕ) :
    (actualJoinedExponent a (0 : Fin t →₀ ℕ)).degree = a.degree := by
  rw [actualJoinedExponent_tangent_embedding, Finsupp.embDomain_eq_mapDomain,
    Finsupp.degree_mapDomain]

private theorem joined_zero_lex_lt_iff (a b : Fin d →₀ ℕ) :
    toLex (actualJoinedExponent a (0 : Fin t →₀ ℕ)) <
        toLex (actualJoinedExponent b (0 : Fin t →₀ ℕ)) ↔ toLex a < toLex b := by
  rw [Finsupp.Lex.lt_iff, Finsupp.Lex.lt_iff]
  constructor
  · rintro ⟨i, hi, hab⟩
    revert hi hab
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · intro hj hab
      refine ⟨j, ?_, ?_⟩
      · intro k hk
        have hkj : k.castAdd t < j.castAdd t := hk
        simpa [actualJoinedExponent] using hj (k.castAdd t) hkj
      · simpa [actualJoinedExponent] using hab
    · intro _hj hab
      simp [actualJoinedExponent] at hab
  · rintro ⟨i, hi, hab⟩
    refine ⟨i.castAdd t, ?_, ?_⟩
    · intro j hj
      revert hj
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · intro hk
        have hki : k < i := hk
        simpa [actualJoinedExponent] using hi k hki
      · intro hk
        have hh : d + k.val < i.val := hk
        omega
    · simpa [actualJoinedExponent] using hab

/-- The actual specific ordered block inclusion preserves BOTH degLex directions. -/
theorem degLex_joined_zero_lt_iff (a b : Fin d →₀ ℕ) :
    MonomialOrder.degLex.toSyn (actualJoinedExponent a (0 : Fin t →₀ ℕ)) <
        MonomialOrder.degLex.toSyn (actualJoinedExponent b (0 : Fin t →₀ ℕ)) ↔
      MonomialOrder.degLex.toSyn a < MonomialOrder.degLex.toSyn b := by
  change toDegLex (actualJoinedExponent a (0 : Fin t →₀ ℕ)) <
      toDegLex (actualJoinedExponent b (0 : Fin t →₀ ℕ)) ↔ toDegLex a < toDegLex b
  rw [Finsupp.DegLex.lt_iff, Finsupp.DegLex.lt_iff]
  simp only [ofDegLex_toDegLex, joined_zero_degree, joined_zero_lex_lt_iff]

/-- The actual formal plane trace kills the whole new block. -/
def formalZeroSectionTrace (d t : ℕ) :
    MvPowerSeries (Fin (d+t)) ℂ →ₐ[ℂ] MvPowerSeries (Fin d) ℂ :=
  MvPowerSeries.killCompl (actualTangentFormalEmbedding d t)

theorem coeff_formalZeroSectionTrace (F : MvPowerSeries (Fin (d+t)) ℂ)
    (a : Fin d →₀ ℕ) :
    MvPowerSeries.coeff a (formalZeroSectionTrace d t F) =
      MvPowerSeries.coeff (actualJoinedExponent a (0 : Fin t →₀ ℕ)) F := by
  rw [actualJoinedExponent_tangent_embedding]
  rfl

theorem formalZeroSectionTrace_rename (F : MvPowerSeries (Fin d) ℂ) :
    formalZeroSectionTrace d t (MvPowerSeries.rename (Fin.castAdd t) F) = F :=
  MvPowerSeries.killCompl_rename_app F

theorem tangent_rename_ne_zero (F : MvPowerSeries (Fin d) ℂ) (hF : F ≠ 0) :
    MvPowerSeries.rename (Fin.castAdd t) F ≠ 0 := by
  intro hz
  have he := congrArg (formalZeroSectionTrace d t) hz
  rw [formalZeroSectionTrace_rename, map_zero] at he
  exact hF he

/-- Whole renamed series retain their real initial exponent, with no prescribed diagram. -/
theorem actualInitialExponent_tangent_rename (F : MvPowerSeries (Fin d) ℂ) (hF : F ≠ 0) :
    actualInitialExponent MonomialOrder.degLex (MvPowerSeries.rename (Fin.castAdd t) F)
        (tangent_rename_ne_zero F hF) =
      actualJoinedExponent (actualInitialExponent MonomialOrder.degLex F hF)
        (0 : Fin t →₀ ℕ) := by
  apply actualInitialExponent_eq_of_coefficients
  · rw [coefficient_tangent_rename_joined, if_pos rfl]
    exact (actualInitialExponent_spec MonomialOrder.degLex F hF).1
  · intro c hc
    rw [← actualJoinedExponent_split c] at hc ⊢
    rw [coefficient_tangent_rename_joined]
    by_cases hnormal : actualNormalExponent c = 0
    · rw [if_pos hnormal]
      rw [hnormal] at hc
      exact coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex F hF
        _ ((degLex_joined_zero_lt_iff _ _).mp hc)
    · rw [if_neg hnormal]

/-- The true formal extension plus the actual normal coordinate ideal. -/
def formalZeroSectionIdeal (d t : ℕ) (K : Ideal (MvPowerSeries (Fin d) ℂ)) :
    Ideal (MvPowerSeries (Fin (d+t)) ℂ) :=
  Ideal.map (MvPowerSeries.rename (Fin.castAdd t)).toRingHom K ⊔
    actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)

private theorem mem_normal_formal_ideal_iff (F : MvPowerSeries (Fin (d+t)) ℂ) :
    F ∈ actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t) ↔
      ∀ a : Fin d →₀ ℕ,
        MvPowerSeries.coeff (actualJoinedExponent a (0 : Fin t →₀ ℕ)) F = 0 := by
  rw [← pow_one (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)),
    mem_actualFormalCoordinateIdeal_pow_iff]
  constructor
  · intro h a
    apply h
    rw [actualJoinedExponent_normal_weight]
    simp [normalExponentDegree]
  · intro h c hc
    have he := actualJoinedExponent_split c
    have hdegree : normalExponentDegree (actualNormalExponent c) < 1 := by
      rw [← actualJoinedExponent_normal_weight d t (actualTangentExponent c)
        (actualNormalExponent c), he]
      exact hc
    have hnormal : actualNormalExponent c = 0 := (Finsupp.degree_eq_zero_iff _).mp (by
      have hz : normalExponentDegree (actualNormalExponent c) = 0 := by omega
      simpa only [normalExponentDegree, Finsupp.degree_eq_sum] using hz)
    have hz := h (actualTangentExponent c)
    rw [hnormal] at he
    rwa [he] at hz

private theorem normal_formal_ideal_eq_ker :
    actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t) =
      RingHom.ker (formalZeroSectionTrace d t).toRingHom := by
  ext F
  rw [mem_normal_formal_ideal_iff]
  change (∀ a, MvPowerSeries.coeff (actualJoinedExponent a (0 : Fin t →₀ ℕ)) F = 0) ↔
    formalZeroSectionTrace d t F = 0
  constructor
  · intro h
    apply MvPowerSeries.ext
    intro a
    rw [coeff_formalZeroSectionTrace, map_zero]
    exact h a
  · intro h a
    have hc := congrArg (MvPowerSeries.coeff a) h
    simpa only [coeff_formalZeroSectionTrace, map_zero] using hc

/-- BOTH entire formal trace directions follow from the genuine coordinate kernel. -/
theorem formalZeroSectionIdeal_eq_comap (K : Ideal (MvPowerSeries (Fin d) ℂ)) :
    formalZeroSectionIdeal d t K = Ideal.comap (formalZeroSectionTrace d t).toRingHom K := by
  apply le_antisymm
  · apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro F hF
      change formalZeroSectionTrace d t (MvPowerSeries.rename (Fin.castAdd t) F) ∈ K
      rwa [formalZeroSectionTrace_rename]
    · intro F hF
      have hz : formalZeroSectionTrace d t F = 0 := by
        rw [normal_formal_ideal_eq_ker] at hF
        exact hF
      change formalZeroSectionTrace d t F ∈ K
      rw [hz]
      exact K.zero_mem
  · intro F hF
    have hker : F - MvPowerSeries.rename (Fin.castAdd t) (formalZeroSectionTrace d t F) ∈
        actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t) := by
      rw [normal_formal_ideal_eq_ker]
      change formalZeroSectionTrace d t
        (F - MvPowerSeries.rename (Fin.castAdd t) (formalZeroSectionTrace d t F)) = 0
      rw [map_sub, formalZeroSectionTrace_rename, sub_self]
    have hbase : MvPowerSeries.rename (Fin.castAdd t) (formalZeroSectionTrace d t F) ∈
        formalZeroSectionIdeal d t K :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hF)
    have hsum := (formalZeroSectionIdeal d t K).add_mem hbase (Ideal.mem_sup_right hker)
    have he : MvPowerSeries.rename (Fin.castAdd t) (formalZeroSectionTrace d t F) +
        (F - MvPowerSeries.rename (Fin.castAdd t) (formalZeroSectionTrace d t F)) = F := by abel
    exact he ▸ hsum

private theorem ideal_map_map_of_pointwise_commutation
    {R S T U : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T] [CommSemiring U]
    (f : R →+* S) (g : S →+* U) (h : R →+* T) (k : T →+* U)
    (he : ∀ x, g (f x) = k (h x)) (I : Ideal R) :
    Ideal.map g (Ideal.map f I) = Ideal.map k (Ideal.map h I) := by
  rw [Ideal.map_map, Ideal.map_map]
  have hcomp : g.comp f = k.comp h := RingHom.ext he
  rw [hcomp]

/-- The WHOLE analytic input J is sent to this SAME actual formal ideal internally. -/
theorem actualTaylor_zeroSectionIdeal (I : Ideal (HolGerm (ComplexModel d))) :
    Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (actualZeroSectionIdeal d t I) =
      formalZeroSectionIdeal d t (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I) := by
  have hbase : Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom
      (Ideal.map (tangentPullback d t).toRingHom I) =
      Ideal.map (MvPowerSeries.rename (Fin.castAdd t)).toRingHom
        (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I) := by
    exact ideal_map_map_of_pointwise_commutation
      (tangentPullback d t).toRingHom (actualUnshiftedTaylorAlgHom (d+t)).toRingHom
      (actualUnshiftedTaylorAlgHom d).toRingHom (MvPowerSeries.rename (Fin.castAdd t)).toRingHom
      (fun g => DFunLike.congr_fun (actualUnshiftedTaylor_tangentPullback d t) g) I
  rw [actualZeroSectionIdeal, Ideal.map_sup, hbase, map_normalIdeal_originalTaylor]
  rfl

private theorem normal_unit_mem (K : Ideal (MvPowerSeries (Fin d) ℂ)) (j : Fin t) :
    (MvPowerSeries.X (j.natAdd d) : MvPowerSeries (Fin (d+t)) ℂ) ∈
      formalZeroSectionIdeal d t K :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨j.natAdd d, ⟨j, rfl⟩, rfl⟩)

private theorem normal_unit_diagram (K : Ideal (MvPowerSeries (Fin d) ℂ)) (j : Fin t) :
    (Finsupp.single (j.natAdd d) 1 : Fin (d+t) →₀ ℕ) ∈
      actualInitialDiagram MonomialOrder.degLex (formalZeroSectionIdeal d t K) := by
  refine ⟨MvPowerSeries.monomial (Finsupp.single (j.natAdd d) 1) 1, ?_,
    actualMonomial_ne_zero _, actualInitialExponent_monomial _ _⟩
  simpa only [MvPowerSeries.X_def] using normal_unit_mem K j

private theorem joined_zero_diagram (K : Ideal (MvPowerSeries (Fin d) ℂ))
    (a : Fin d →₀ ℕ) (ha : a ∈ actualInitialDiagram MonomialOrder.degLex K) :
    actualJoinedExponent a (0 : Fin t →₀ ℕ) ∈
      actualInitialDiagram MonomialOrder.degLex (formalZeroSectionIdeal d t K) := by
  obtain ⟨F, hFK, hF, he⟩ := ha
  refine ⟨MvPowerSeries.rename (Fin.castAdd t) F,
    Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hFK), tangent_rename_ne_zero F hF, ?_⟩
  rw [actualInitialExponent_tangent_rename F hF, he]

/-- Every actual whole diagram coefficient is identified, including unit and zero ideals. -/
theorem mem_actualInitialDiagram_zeroSection_joined_iff
    (K : Ideal (MvPowerSeries (Fin d) ℂ)) (a : Fin d →₀ ℕ) (c : Fin t →₀ ℕ) :
    actualJoinedExponent a c ∈
        actualInitialDiagram MonomialOrder.degLex (formalZeroSectionIdeal d t K) ↔
      c ≠ 0 ∨ a ∈ actualInitialDiagram MonomialOrder.degLex K := by
  constructor
  · intro h
    by_cases hc : c = 0
    · right
      subst c
      obtain ⟨F, hFK, hF, he⟩ := h
      have htrace : formalZeroSectionTrace d t F ∈ K := by
        rwa [formalZeroSectionIdeal_eq_comap] at hFK
      have hcoeff : MvPowerSeries.coeff a (formalZeroSectionTrace d t F) ≠ 0 := by
        rw [coeff_formalZeroSectionTrace, ← he]
        exact (actualInitialExponent_spec MonomialOrder.degLex F hF).1
      have hne : formalZeroSectionTrace d t F ≠ 0 := by
        intro hz
        exact hcoeff (by rw [hz, map_zero])
      refine ⟨formalZeroSectionTrace d t F, htrace, hne, ?_⟩
      apply actualInitialExponent_eq_of_coefficients
      · exact hcoeff
      · intro b hb
        rw [coeff_formalZeroSectionTrace]
        apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex F hF
        rw [he]
        exact (degLex_joined_zero_lt_iff b a).mpr hb
    · exact Or.inl hc
  · rintro (hc | ha)
    · obtain ⟨j, hj⟩ : ∃ j : Fin t, c j ≠ 0 := by
        by_contra h
        apply hc
        ext j
        exact not_ne_iff.mp (fun hj => h ⟨j, hj⟩)
      apply actualInitialDiagram_upper MonomialOrder.degLex _
        (Finsupp.single (j.natAdd d) 1) (actualJoinedExponent a c) (normal_unit_diagram K j)
      intro i
      by_cases hi : i = j.natAdd d
      · subst i
        have hpos : 1 ≤ c j := by omega
        simpa [actualJoinedExponent] using hpos
      · simp only [Finsupp.single_eq_of_ne hi]
        exact Nat.zero_le _
    · have hz := joined_zero_diagram (t := t) K a ha
      apply actualInitialDiagram_upper MonomialOrder.degLex _ _ _ hz
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [actualJoinedExponent]

private theorem zero_mem_diagram_iff_top (K : Ideal (MvPowerSeries (Fin d) ℂ)) :
    (0 : Fin d →₀ ℕ) ∈ actualInitialDiagram MonomialOrder.degLex K ↔ K = ⊤ := by
  constructor
  · rintro ⟨F, hFK, hF, he⟩
    have hc : MvPowerSeries.constantCoeff F ≠ 0 := by
      change MvPowerSeries.coeff 0 F ≠ 0
      rw [← he]
      exact (actualInitialExponent_spec MonomialOrder.degLex F hF).1
    exact K.eq_top_of_isUnit_mem hFK
      (MvPowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hc))
  · intro h
    subst K
    refine ⟨MvPowerSeries.monomial 0 1, trivial, actualMonomial_ne_zero _, ?_⟩
    exact actualInitialExponent_monomial _ _

private theorem joined_zero_le_iff (a b : Fin d →₀ ℕ) :
    actualJoinedExponent a (0 : Fin t →₀ ℕ) ≤ actualJoinedExponent b (0 : Fin t →₀ ℕ) ↔ a ≤ b := by
  constructor
  · intro h i
    simpa [actualJoinedExponent] using h (i.castAdd t)
  · intro h i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [actualJoinedExponent] using h j
    · simp [actualJoinedExponent]

private theorem joined_zero_injective :
    Function.Injective (fun a : Fin d →₀ ℕ => actualJoinedExponent a (0 : Fin t →₀ ℕ)) := by
  intro a b h
  ext i
  have he := congrArg (fun c : Fin (d+t) →₀ ℕ => c (i.castAdd t)) h
  simpa [actualJoinedExponent] using he

private theorem normal_eq_zero_of_le_joined_zero (b : Fin (d+t) →₀ ℕ)
    (a : Fin d →₀ ℕ) (h : b ≤ actualJoinedExponent a (0 : Fin t →₀ ℕ)) :
    actualNormalExponent b = 0 := by
  ext j
  have hj : b (j.natAdd d) = 0 := by
    simpa [actualJoinedExponent] using h (j.natAdd d)
  simpa [actualNormalExponent] using hj

private theorem joined_zero_mem_vertices_iff (K : Ideal (MvPowerSeries (Fin d) ℂ))
    (a : Fin d →₀ ℕ) :
    actualJoinedExponent a (0 : Fin t →₀ ℕ) ∈
      actualInitialVertices MonomialOrder.degLex (formalZeroSectionIdeal d t K) ↔
      a ∈ actualInitialVertices MonomialOrder.degLex K := by
  simp only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · intro h
    have ha : a ∈ actualInitialDiagram MonomialOrder.degLex K := by
      simpa only [mem_actualInitialDiagram_zeroSection_joined_iff, ne_eq, not_true_eq_false, false_or]
        using h.prop
    have hm : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) a := by
      refine ⟨ha, ?_⟩
      intro b hb hba
      exact (joined_zero_le_iff a b).mp
        (h.2 (joined_zero_diagram K b hb) ((joined_zero_le_iff b a).mpr hba))
    simpa [actualInitialVertices] using hm
  · intro ha
    have hm : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) a := by
      simpa [actualInitialVertices] using ha
    refine ⟨joined_zero_diagram K a hm.prop, ?_⟩
    intro b hb hba
    have hn := normal_eq_zero_of_le_joined_zero b a hba
    have he : actualJoinedExponent (actualTangentExponent b) (0 : Fin t →₀ ℕ) = b := by
      simpa only [hn] using actualJoinedExponent_split b
    have hb0 : actualTangentExponent b ∈ actualInitialDiagram MonomialOrder.degLex K := by
      rw [← he, mem_actualInitialDiagram_zeroSection_joined_iff] at hb
      exact hb.resolve_left (not_ne_iff.mpr rfl)
    rw [← he] at hba ⊢
    exact (joined_zero_le_iff a _).mpr (hm.2 hb0 ((joined_zero_le_iff _ a).mp hba))

/-- The original actual vertices are genuine minimal vertices after the embedding. -/
def zeroSectionLiftVertex (K : Ideal (MvPowerSeries (Fin d) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex K) :
    actualInitialVertices MonomialOrder.degLex (formalZeroSectionIdeal d t K) :=
  ⟨actualJoinedExponent a.val (0 : Fin t →₀ ℕ), (joined_zero_mem_vertices_iff K a.val).mpr a.property⟩

private theorem normal_single_le_cases (j : Fin t) (b : Fin (d+t) →₀ ℕ)
    (hb : b ≤ Finsupp.single (j.natAdd d) 1) :
    b = 0 ∨ b = Finsupp.single (j.natAdd d) 1 := by
  by_cases hj : b (j.natAdd d) = 0
  · left
    ext i
    by_cases hi : i = j.natAdd d
    · subst i
      exact hj
    · have hz : b i = 0 :=
        Nat.eq_zero_of_le_zero (by simpa [Finsupp.single_eq_of_ne hi] using hb i)
      simpa [Finsupp.single_eq_of_ne hi] using hz
  · right
    ext i
    by_cases hi : i = j.natAdd d
    · subst i
      have hi := hb (j.natAdd d)
      simp only [Finsupp.single_eq_same] at hi ⊢
      omega
    · have hz : b i = 0 :=
        Nat.eq_zero_of_le_zero (by simpa [Finsupp.single_eq_of_ne hi] using hb i)
      simpa [Finsupp.single_eq_of_ne hi] using hz

private theorem zero_mem_big_diagram_iff (K : Ideal (MvPowerSeries (Fin d) ℂ)) :
    (0 : Fin (d+t) →₀ ℕ) ∈
      actualInitialDiagram MonomialOrder.degLex (formalZeroSectionIdeal d t K) ↔ K = ⊤ := by
  have hz : (0 : Fin (d+t) →₀ ℕ) =
      actualJoinedExponent (0 : Fin d →₀ ℕ) (0 : Fin t →₀ ℕ) := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [actualJoinedExponent]
  rw [hz, mem_actualInitialDiagram_zeroSection_joined_iff]
  simp only [ne_eq, not_true_eq_false, false_or, zero_mem_diagram_iff_top]

private theorem normal_single_mem_vertices (K : Ideal (MvPowerSeries (Fin d) ℂ))
    (hK : K ≠ ⊤) (j : Fin t) :
    (Finsupp.single (j.natAdd d) 1 : Fin (d+t) →₀ ℕ) ∈
      actualInitialVertices MonomialOrder.degLex (formalZeroSectionIdeal d t K) := by
  have hm : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex (formalZeroSectionIdeal d t K))
      (Finsupp.single (j.natAdd d) 1) := by
    refine ⟨normal_unit_diagram K j, ?_⟩
    intro b hb hbj
    rcases normal_single_le_cases j b hbj with rfl | rfl
    · exact (hK ((zero_mem_big_diagram_iff K).mp hb)).elim
    · exact le_rfl
  simpa [actualInitialVertices] using hm

/-- New normal unit labels are actual minimal vertices ONLY in the proper case. -/
def zeroSectionNormalVertex (K : Ideal (MvPowerSeries (Fin d) ℂ))
    (hK : K ≠ ⊤) (j : Fin t) :
    actualInitialVertices MonomialOrder.degLex (formalZeroSectionIdeal d t K) :=
  ⟨Finsupp.single (j.natAdd d) 1, normal_single_mem_vertices K hK j⟩

private theorem actual_zeroSection_vertex_cases (K : Ideal (MvPowerSeries (Fin d) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex (formalZeroSectionIdeal d t K)) :
    (∃ b : actualInitialVertices MonomialOrder.degLex K, a = zeroSectionLiftVertex K b) ∨
      ∃ (hK : K ≠ ⊤) (j : Fin t), a = zeroSectionNormalVertex K hK j := by
  have hmin : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex (formalZeroSectionIdeal d t K)) a.val := by
    simpa [actualInitialVertices] using a.property
  by_cases hn : actualNormalExponent a.val = 0
  · left
    have he : actualJoinedExponent (actualTangentExponent a.val) (0 : Fin t →₀ ℕ) = a.val := by
      simpa only [hn] using actualJoinedExponent_split a.val
    have hb : actualTangentExponent a.val ∈ actualInitialVertices MonomialOrder.degLex K :=
      (joined_zero_mem_vertices_iff K _).mp (he.symm ▸ a.property)
    exact ⟨⟨_, hb⟩, Subtype.ext he.symm⟩
  · right
    obtain ⟨j, hj⟩ : ∃ j : Fin t, a.val (j.natAdd d) ≠ 0 := by
      by_contra h
      apply hn
      ext j
      change a.val (j.natAdd d) = 0
      exact not_ne_iff.mp (fun hj => h ⟨j, hj⟩)
    have hle : (Finsupp.single (j.natAdd d) 1 : Fin (d+t) →₀ ℕ) ≤ a.val := by
      intro i
      by_cases hi : i = j.natAdd d
      · subst i
        simp only [Finsupp.single_eq_same]
        omega
      · simp only [Finsupp.single_eq_of_ne hi]
        exact Nat.zero_le _
    have he : a.val = Finsupp.single (j.natAdd d) 1 :=
      le_antisymm (hmin.2 (normal_unit_diagram K j) hle) hle
    have hK : K ≠ ⊤ := by
      intro htop
      have haz : a.val ≤ 0 := hmin.2 ((zero_mem_big_diagram_iff K).mpr htop)
        (show (0 : Fin (d+t) →₀ ℕ) ≤ a.val from bot_le)
      have hz := haz (j.natAdd d)
      rw [he, Finsupp.single_eq_same, Finsupp.zero_apply] at hz
      omega
    exact ⟨hK, j, Subtype.ext he⟩

/-- The label type has no additional normal labels for the unit ideal. -/
def ZeroSectionVertexIndex (K : Ideal (MvPowerSeries (Fin d) ℂ)) :=
  (actualInitialVertices MonomialOrder.degLex K) ⊕ {_j : Fin t // K ≠ ⊤}

def zeroSectionVertexMap (K : Ideal (MvPowerSeries (Fin d) ℂ)) :
    ZeroSectionVertexIndex (t := t) K →
      actualInitialVertices MonomialOrder.degLex (formalZeroSectionIdeal d t K)
  | .inl a => zeroSectionLiftVertex K a
  | .inr j => zeroSectionNormalVertex K j.property j.val

private theorem lift_normal_ne (K : Ideal (MvPowerSeries (Fin d) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex K) (hK : K ≠ ⊤) (j : Fin t) :
    zeroSectionLiftVertex K a ≠ zeroSectionNormalVertex K hK j := by
  intro h
  have he := congrArg (fun v : actualInitialVertices MonomialOrder.degLex
    (formalZeroSectionIdeal d t K) => v.val (j.natAdd d)) h
  simp [zeroSectionLiftVertex, zeroSectionNormalVertex, actualJoinedExponent] at he

/-- An actual bijection, including genuine minimality, exhaustiveness and strict de-duplication. -/
def zeroSectionVertexEquiv (K : Ideal (MvPowerSeries (Fin d) ℂ)) :
    ZeroSectionVertexIndex (t := t) K ≃
      actualInitialVertices MonomialOrder.degLex (formalZeroSectionIdeal d t K) :=
  Equiv.ofBijective (zeroSectionVertexMap K) ⟨by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact joined_zero_injective (congrArg Subtype.val h)
      | inr b => exact (lift_normal_ne K a b.property b.val h).elim
    | inr a =>
      cases b with
      | inl b => exact (lift_normal_ne K b a.property a.val h.symm).elim
      | inr b =>
        apply congrArg Sum.inr
        apply Subtype.ext
        have he : (Finsupp.single (a.val.natAdd d) 1 : Fin (d+t) →₀ ℕ) =
            Finsupp.single (b.val.natAdd d) 1 := congrArg Subtype.val h
        apply Fin.ext
        have hh := congrArg Fin.val
          (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) he)
        change d + a.val.val = d + b.val.val at hh
        omega, by
    intro a
    rcases actual_zeroSection_vertex_cases K a with ⟨b, hb⟩ | ⟨hK, j, hj⟩
    · exact ⟨.inl b, hb.symm⟩
    · exact ⟨.inr ⟨j, hK⟩, hj.symm⟩⟩

/-- Every whole canonical division remainder is the renamed genuine trace remainder. -/
theorem actualFormalRemainder_zeroSection (K : Ideal (MvPowerSeries (Fin d) ℂ))
    (F : MvPowerSeries (Fin (d+t)) ℂ) :
    actualFormalRemainder MonomialOrder.degLex (formalZeroSectionIdeal d t K) F =
      MvPowerSeries.rename (Fin.castAdd t)
        (actualFormalRemainder MonomialOrder.degLex K (formalZeroSectionTrace d t F)) := by
  symm
  apply actualFormalRemainder_unique
  · rw [formalZeroSectionIdeal_eq_comap]
    change formalZeroSectionTrace d t (F - MvPowerSeries.rename (Fin.castAdd t)
      (actualFormalRemainder MonomialOrder.degLex K (formalZeroSectionTrace d t F))) ∈ K
    rw [map_sub, formalZeroSectionTrace_rename]
    exact sub_actualFormalRemainder_mem MonomialOrder.degLex K _
  · intro c hc
    rw [← actualJoinedExponent_split c] at hc ⊢
    rw [coefficient_tangent_rename_joined]
    rcases (mem_actualInitialDiagram_zeroSection_joined_iff K _ _).mp hc with hn | ht
    · rw [if_neg hn]
    · split_ifs
      · exact actualFormalRemainder_coefficient_diagram MonomialOrder.degLex K _ _ ht
      · rfl

/-- The entire canonical reduced series at every original label is literally renamed. -/
theorem actualReducedVertexSeries_zeroSection_lift (K : Ideal (MvPowerSeries (Fin d) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex K) :
    actualReducedVertexSeries MonomialOrder.degLex (formalZeroSectionIdeal d t K)
        (zeroSectionLiftVertex K a) =
      MvPowerSeries.rename (Fin.castAdd t) (actualReducedVertexSeries MonomialOrder.degLex K a) := by
  have htrace : formalZeroSectionTrace d t
      (MvPowerSeries.monomial (actualJoinedExponent a.val (0 : Fin t →₀ ℕ)) 1) =
      MvPowerSeries.monomial a.val 1 := by
    rw [actualJoinedExponent_tangent_embedding]
    exact MvPowerSeries.killCompl_monomial_embDomain _ _
  change MvPowerSeries.monomial (actualJoinedExponent a.val (0 : Fin t →₀ ℕ)) 1 -
      actualFormalRemainder MonomialOrder.degLex (formalZeroSectionIdeal d t K)
        (MvPowerSeries.monomial (actualJoinedExponent a.val (0 : Fin t →₀ ℕ)) 1) =
    MvPowerSeries.rename (Fin.castAdd t) (MvPowerSeries.monomial a.val 1 -
      actualFormalRemainder MonomialOrder.degLex K (MvPowerSeries.monomial a.val 1))
  rw [actualFormalRemainder_zeroSection, htrace, map_sub, MvPowerSeries.rename_monomial]
  rw [actualJoinedExponent_tangent_embedding, Finsupp.embDomain_eq_mapDomain]
  rfl

/-- The genuine additional canonical reduced member is exactly the original new coordinate. -/
theorem actualReducedVertexSeries_zeroSection_normal (K : Ideal (MvPowerSeries (Fin d) ℂ))
    (hK : K ≠ ⊤) (j : Fin t) :
    actualReducedVertexSeries MonomialOrder.degLex (formalZeroSectionIdeal d t K)
        (zeroSectionNormalVertex K hK j) = MvPowerSeries.X (j.natAdd d) := by
  change MvPowerSeries.X (j.natAdd d) -
    actualFormalRemainder MonomialOrder.degLex (formalZeroSectionIdeal d t K)
      (MvPowerSeries.X (j.natAdd d)) = _
  rw [actualFormalRemainder_eq_zero_of_mem MonomialOrder.degLex _ _ (normal_unit_mem K j), sub_zero]

end

end Hironaka.HironakaActualZeroSectionFormalBasis
