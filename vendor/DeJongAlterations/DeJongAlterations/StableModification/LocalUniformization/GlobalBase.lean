import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Spec

/-!
# Localizing the base of a curve over a valuation ring

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.1 (`cofinprop`, `semi-stable.tex` lines 2972–2975): "we can replace `R` with its
localization beneath `x`, so now `x` is in the special fiber". For a valuation ring `O` of a field
`K` and an overring `O ≤ B` (in the application `B = 𝒪_𝔵 ∩ K`), `B` is the localization of `O`
at the prime `𝔭 = 𝔪_B ∩ O` (`isLocalization_atPrime`), and when `Spec O` is finite (`O` of finite
height, the situation of the de Jong route) it is even a localization `O_f` at a single element
(`exists_isLocalization_away`), so `Spec B → Spec O` is an open immersion
(`isOpenImmersion_specInclusion`) onto the generizations of `𝔭` (`mem_range_specInclusion_iff`).
Blueprint `lem:sm-cofinal-base` (`sm-local-uniformization.tex`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

variable {K : Type u} [Field K] (O B : ValuationSubring K) (h : O ≤ B)

/-- The inclusion `O → B` of valuation rings of `K`, as an algebra. -/
abbrev inclusionAlgebra : Algebra O B := (ValuationSubring.inclusion O B h).toAlgebra

/-- An element of `O` outside `𝔭 = 𝔪_B ∩ O` is a unit of `B`. -/
theorem isUnit_inclusion_of_not_mem {s : O} (hs : s ∉ O.idealOfLE B h) :
    IsUnit (ValuationSubring.inclusion O B h s) := by
  by_contra hu
  exact hs ((mem_maximalIdeal _).mpr hu)

/-- **`B` is the localization of `O` at `𝔭 = 𝔪_B ∩ O`.** -/
theorem isLocalization_atPrime :
    letI := inclusionAlgebra O B h
    IsLocalization.AtPrime B (O.idealOfLE B h) := by
  let := inclusionAlgebra O B h
  refine (isLocalization_iff _ _).mpr ⟨fun ⟨s, hs⟩ ↦ isUnit_inclusion_of_not_mem O B h hs,
    fun b ↦ ?_, fun {x y} hxy ↦ ⟨1, ?_⟩⟩
  · by_cases hb : (b : K) ∈ O
    · refine ⟨⟨⟨b, hb⟩, 1⟩, Subtype.ext ?_⟩
      change (b : K) * ((1 : O) : K) = b
      simp
    · have hinv : (b : K)⁻¹ ∈ O := (O.mem_or_inv_mem b).resolve_left hb
      have hb0 : (b : K) ≠ 0 := fun h0 ↦ hb (h0 ▸ O.zero_mem)
      have hs : (⟨_, hinv⟩ : O) ∈ (O.idealOfLE B h).primeCompl := by
        intro hmem
        change ValuationSubring.inclusion O B h ⟨_, hinv⟩ ∈ maximalIdeal B at hmem
        apply (mem_maximalIdeal _).mp hmem
        refine IsUnit.of_mul_eq_one b (Subtype.ext ?_)
        change (b : K)⁻¹ * b = 1
        exact inv_mul_cancel₀ hb0
      refine ⟨⟨1, ⟨_, hinv⟩, hs⟩, Subtype.ext ?_⟩
      change (b : K) * (b : K)⁻¹ = 1
      exact mul_inv_cancel₀ hb0
  · simp only [OneMemClass.coe_one, one_mul]
    have hK := congrArg (fun z : B ↦ (z : K)) hxy
    exact Subtype.ext hK

/-- In a ring with finitely many primes, for every prime `𝔭` there is `f ∉ 𝔭` lying in every prime
not contained in `𝔭`. -/
theorem exists_not_mem_forall_mem {R : Type*} [CommRing R] [Finite (PrimeSpectrum R)]
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    ∃ f : R, f ∉ 𝔭 ∧ ∀ q : PrimeSpectrum R, ¬ q.asIdeal ≤ 𝔭 → f ∈ q.asIdeal := by
  classical
  have : Fintype (PrimeSpectrum R) := Fintype.ofFinite _
  have hex : ∀ q : PrimeSpectrum R, ∃ g : R, ¬ q.asIdeal ≤ 𝔭 → g ∈ q.asIdeal ∧ g ∉ 𝔭 := by
    intro q
    by_cases hq : q.asIdeal ≤ 𝔭
    · exact ⟨1, fun h ↦ absurd hq h⟩
    · obtain ⟨g, hgq, hg𝔭⟩ := Set.not_subset.mp hq
      exact ⟨g, fun _ ↦ ⟨hgq, hg𝔭⟩⟩
  choose g hg using hex
  let F := Finset.univ.filter fun q : PrimeSpectrum R ↦ ¬ q.asIdeal ≤ 𝔭
  refine ⟨∏ q ∈ F, g q, ?_, fun q hq ↦ ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨q, hqF, hmem⟩
    exact ((hg q (Finset.mem_filter.mp hqF).2).2 hmem)
  · have hqF : q ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
    rw [← Finset.mul_prod_erase F g hqF]
    exact Ideal.mul_mem_right _ _ (hg q hq).1

/-- **Over a base of finite height, `B` is a localization `O_f`.** -/
theorem exists_isLocalization_away [Finite (PrimeSpectrum O)] :
    letI := inclusionAlgebra O B h
    ∃ f : O, IsLocalization.Away f B := by
  let := inclusionAlgebra O B h
  have hloc := isLocalization_atPrime O B h
  obtain ⟨f, hf𝔭, hf⟩ := exists_not_mem_forall_mem (O.idealOfLE B h)
  refine ⟨f, (isLocalization_iff _ _).mpr ⟨?_, fun b ↦ ?_, fun {x y} hxy ↦ ⟨1, ?_⟩⟩⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact (isUnit_inclusion_of_not_mem O B h hf𝔭).pow n
  · obtain ⟨⟨a, s, hs⟩, hb⟩ := IsLocalization.surj (O.idealOfLE B h).primeCompl b
    -- `f` lies in every prime containing `s`, hence in the radical of `(s)`
    have hrad : f ∈ (Ideal.span {s}).radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro q ⟨hsq, hq⟩
      refine hf ⟨q, hq⟩ fun hle ↦ hs (hle ?_)
      exact hsq (Ideal.mem_span_singleton_self s)
    obtain ⟨n, hn⟩ := hrad
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hn
    refine ⟨⟨a * t, ⟨f ^ n, n, rfl⟩⟩, ?_⟩
    have hsu : IsUnit (algebraMap O B s) := isUnit_inclusion_of_not_mem O B h hs
    have hb' : b * algebraMap O B s = algebraMap O B a := hb
    change b * algebraMap O B (f ^ n) = algebraMap O B (a * t)
    rw [← ht, map_mul, map_mul, ← hb']
    ring
  · simp only [OneMemClass.coe_one, one_mul]
    have hK := congrArg (fun z : B ↦ (z : K)) hxy
    exact Subtype.ext hK

/-- The morphism `Spec B → Spec O`. -/
abbrev specInclusion : Spec (.of B) ⟶ Spec (.of O) :=
  Spec.map (CommRingCat.ofHom (ValuationSubring.inclusion O B h))

/-- **Over a base of finite height, `Spec B → Spec O` is an open immersion.** -/
theorem isOpenImmersion_specInclusion [Finite (PrimeSpectrum O)] :
    IsOpenImmersion (specInclusion O B h) := by
  let := inclusionAlgebra O B h
  obtain ⟨f, hf⟩ := exists_isLocalization_away O B h
  exact IsOpenImmersion.of_isLocalization (S := B) f

/-- `Spec B → Spec O` is an open immersion. -/
instance instIsOpenImmersionSpecInclusion [Finite (PrimeSpectrum O)] :
    IsOpenImmersion (specInclusion O B h) :=
  isOpenImmersion_specInclusion O B h

include h in
/-- Over a base of finite height, `B` has finitely many primes. -/
theorem finite_primeSpectrum [Finite (PrimeSpectrum O)] : Finite (PrimeSpectrum B) :=
  have : Finite (Spec (.of O)) := inferInstanceAs (Finite (PrimeSpectrum O))
  Finite.of_injective (fun p : Spec (.of B) ↦ specInclusion O B h p)
    (specInclusion O B h).isOpenEmbedding.injective

/-- The image of `Spec B → Spec O` consists of the primes contained in `𝔭 = 𝔪_B ∩ O`. -/
theorem mem_range_specInclusion_iff (q : Spec (.of O)) :
    q ∈ Set.range (specInclusion O B h) ↔ q.asIdeal ≤ O.idealOfLE B h := by
  let := inclusionAlgebra O B h
  have := isLocalization_atPrime O B h
  have hr := PrimeSpectrum.localization_comap_range (R := O) B (O.idealOfLE B h).primeCompl
  change q ∈ Set.range (PrimeSpectrum.comap (algebraMap O B)) ↔ _
  rw [hr]
  change Disjoint ((O.idealOfLE B h).primeCompl : Set O) q.asIdeal ↔ _
  constructor
  · intro hd x hx
    by_contra hx'
    exact Set.disjoint_left.mp hd hx' hx
  · intro hle
    exact Set.disjoint_left.mpr fun x hx hxq ↦ hx (hle hxq)

/-- The closed point of `Spec B` maps to `𝔭 = 𝔪_B ∩ O`. -/
theorem specInclusion_closedPoint :
    (specInclusion O B h (closedPoint B)).asIdeal = O.idealOfLE B h :=
  rfl

end DeJongAlterations.StableModification.LocalUniformization
