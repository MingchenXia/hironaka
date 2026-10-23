import DeJongAlterations.StableModification.Limits.FlatDescent.Criteria
import Mathlib.RingTheory.PicardGroup

/-!
# The local criterion of flatness with explicit multipliers

Let `R` be a noetherian ring, `P` a noetherian flat `R`-algebra, `K ⊆ P` an ideal, `I ⊆ R` an
ideal and `a ∈ R`. An ideal `𝔟 ⊆ R` is *`a`-good* (`IsGood K a 𝔟`) if every
`x ∈ K ∩ 𝔟P` has some `a ^ k x ∈ 𝔟K`. If `I` is `a`-good and `P ⧸ (K + IP)` is flat over
`R ⧸ I` after inverting `a` (in the elementwise form of hypothesis `h2`), then every
`x ∈ K ∩ 𝔟P` is multiplied into `𝔟K` by some `s ≡ a ^ N (mod IP)`
(`exists_mul_mem_of_localCriterion`). This is the form of the local criterion of flatness
(EGA 0_III 10.2.1, Stacks 00ML) used in the descent of flatness along directed unions; the proof
is a noetherian composition-series argument on ideals followed by Krull's intersection theorem.

Blueprint: `lem:sm-fd-local-criterion` in `sm-flat-descent.tex`.
-/

namespace DeJongAlterations.StableModification.Limits.FlatDescent

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]

/-- An ideal `𝔟` of `R` is `a`-good for the ideal `K` of `P` if every element of `K ∩ 𝔟P` is
multiplied into `𝔟K` by a power of `a`. -/
def IsGood (K : Ideal P) (a : R) (𝔟 : Ideal R) : Prop :=
  ∀ x ∈ K ⊓ 𝔟.map (algebraMap R P), ∃ k : ℕ,
    algebraMap R P a ^ k * x ∈ 𝔟.map (algebraMap R P) * K

lemma isGood_top (K : Ideal P) (a : R) : IsGood K a ⊤ := by
  intro x hx
  refine ⟨0, ?_⟩
  rw [Ideal.map_top, Ideal.top_mul, pow_zero, one_mul]
  exact (Submodule.mem_inf.mp hx).1

/-- Step 1: every ideal containing `I` is `a`-good. -/
lemma isGood_of_le {K : Ideal P} {a : R} {I : Ideal R} (h1 : IsGood K a I)
    (h2 : ∀ 𝔟 : Ideal R, I ≤ 𝔟 → ∀ x ∈ (K ⊔ I.map (algebraMap R P)) ⊓ 𝔟.map (algebraMap R P),
      ∃ k : ℕ, algebraMap R P a ^ k * x ∈
        𝔟.map (algebraMap R P) * K ⊔ I.map (algebraMap R P))
    {𝔟 : Ideal R} (h𝔟 : I ≤ 𝔟) : IsGood K a 𝔟 := by
  intro x hx
  obtain ⟨hxK, hx𝔟⟩ := Submodule.mem_inf.mp hx
  obtain ⟨k, hk⟩ := h2 𝔟 h𝔟 x (Submodule.mem_inf.mpr ⟨Ideal.mem_sup_left hxK, hx𝔟⟩)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hk
  have hyK : y ∈ K := Ideal.mul_le_right hy
  have hzK : z ∈ K := by
    have : z = algebraMap R P a ^ k * x - y := by rw [← hyz]; ring
    rw [this]
    exact K.sub_mem (K.mul_mem_left _ hxK) hyK
  obtain ⟨l, hl⟩ := h1 z (Submodule.mem_inf.mpr ⟨hzK, hz⟩)
  have hl' : algebraMap R P a ^ l * z ∈ 𝔟.map (algebraMap R P) * K :=
    Ideal.mul_mono (Ideal.map_mono h𝔟) le_rfl hl
  refine ⟨k + l, ?_⟩
  have : algebraMap R P a ^ (k + l) * x =
      algebraMap R P a ^ l * y + algebraMap R P a ^ l * z := by
    rw [← mul_add, hyz]; ring
  rw [this]
  exact add_mem (Ideal.mul_mem_left _ _ hy) hl'

/-- Step 2: if `𝔟 + (t)` and `(𝔟 : t)` are `a`-good, so is `𝔟`. -/
lemma isGood_of_sup_span_singleton [Module.Flat R P] {K : Ideal P} {a : R} {𝔟 : Ideal R}
    (t : R) (hsup : IsGood K a (𝔟 ⊔ Ideal.span {t})) (hcolon : IsGood K a (𝔟.colon {t})) :
    IsGood K a 𝔟 := by
  intro x hx
  obtain ⟨hxK, hx𝔟⟩ := Submodule.mem_inf.mp hx
  have hx' : x ∈ (𝔟 ⊔ Ideal.span {t}).map (algebraMap R P) :=
    Ideal.map_mono le_sup_left hx𝔟
  obtain ⟨k, hk⟩ := hsup x (Submodule.mem_inf.mpr ⟨hxK, hx'⟩)
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.sup_mul] at hk
  obtain ⟨y, hy, w', hw', hyw⟩ := Submodule.mem_sup.mp hk
  obtain ⟨w, hwK, rfl⟩ := Ideal.mem_span_singleton_mul.mp hw'
  have htw : algebraMap R P t * w ∈ 𝔟.map (algebraMap R P) := by
    have : algebraMap R P t * w = algebraMap R P a ^ k * x - y := by rw [← hyw]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hx𝔟) (Ideal.mul_le_left hy)
  have hwc := mem_map_colon_of_mul_mem 𝔟 t htw
  obtain ⟨l, hl⟩ := hcolon w (Submodule.mem_inf.mpr ⟨hwK, hwc⟩)
  have hspan : Ideal.span {t} * 𝔟.colon {t} ≤ 𝔟 := by
    rw [Ideal.span_singleton_mul_le_iff]
    intro z hz
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hz
    rwa [mul_comm]
  have hmap : Ideal.span {algebraMap R P t} * (𝔟.colon {t}).map (algebraMap R P) ≤
      𝔟.map (algebraMap R P) := by
    have := Ideal.map_mono (f := algebraMap R P) hspan
    rwa [Ideal.map_mul, Ideal.map_span, Set.image_singleton] at this
  have hlt : algebraMap R P t * (algebraMap R P a ^ l * w) ∈ 𝔟.map (algebraMap R P) * K := by
    have h3 : algebraMap R P t * (algebraMap R P a ^ l * w) ∈
        Ideal.span {algebraMap R P t} * ((𝔟.colon {t}).map (algebraMap R P) * K) :=
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hl
    rw [← mul_assoc] at h3
    exact Ideal.mul_mono hmap le_rfl h3
  refine ⟨k + l, ?_⟩
  have : algebraMap R P a ^ (k + l) * x =
      algebraMap R P a ^ l * y + algebraMap R P t * (algebraMap R P a ^ l * w) := by
    rw [pow_add, mul_comm (algebraMap R P a ^ k), mul_assoc, ← hyw]; ring
  rw [this]
  exact add_mem (Ideal.mul_mem_left _ _ hy) hlt

/-- Step 3: every ideal containing a power of `I` is `a`-good. -/
lemma isGood_of_pow_le [IsNoetherianRing R] [Module.Flat R P] {K : Ideal P} {a : R}
    {I : Ideal R} (h1 : IsGood K a I)
    (h2 : ∀ 𝔟 : Ideal R, I ≤ 𝔟 → ∀ x ∈ (K ⊔ I.map (algebraMap R P)) ⊓ 𝔟.map (algebraMap R P),
      ∃ k : ℕ, algebraMap R P a ^ k * x ∈
        𝔟.map (algebraMap R P) * K ⊔ I.map (algebraMap R P)) :
    ∀ (n : ℕ) (𝔟 : Ideal R), I ^ n ≤ 𝔟 → IsGood K a 𝔟 := by
  classical
  intro n
  induction n with
  | zero =>
    intro 𝔟 h𝔟
    rw [pow_zero, Ideal.one_eq_top, top_le_iff] at h𝔟
    rw [h𝔟]
    exact isGood_top K a
  | succ n ih =>
    intro 𝔟 h𝔟
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (I ^ n) : (I ^ n).FG)
    -- descend along `𝔟 ⊔ span s ⊇ 𝔟 ⊔ span s' ⊇ ⋯ ⊇ 𝔟`
    have key : ∀ s' : Finset R, (s' : Set R) ⊆ ((I ^ n : Ideal R) : Set R) →
        IsGood K a (𝔟 ⊔ Ideal.span s') → IsGood K a 𝔟 := by
      intro s'
      induction s' using Finset.induction_on with
      | empty =>
        intro _ h
        simpa using h
      | insert t s' _ ihs =>
        intro hsub h
        have ht : t ∈ I ^ n := hsub (Finset.mem_insert_self t s')
        have hsub' : (s' : Set R) ⊆ ((I ^ n : Ideal R) : Set R) :=
          fun z hz => hsub (Finset.mem_insert_of_mem hz)
        apply ihs hsub'
        apply isGood_of_sup_span_singleton t
        · have e : 𝔟 ⊔ Ideal.span (s' : Set R) ⊔ Ideal.span {t} =
              𝔟 ⊔ Ideal.span ((insert t s' : Finset R) : Set R) := by
            rw [Finset.coe_insert, Ideal.span_insert, sup_assoc, sup_comm (Ideal.span _)]
          rw [e]
          exact h
        · apply isGood_of_le h1 h2
          intro z hz
          rw [Submodule.mem_colon_singleton, smul_eq_mul]
          apply Ideal.mem_sup_left
          apply h𝔟
          rw [pow_succ']
          exact Ideal.mul_mem_mul hz ht
    have hs' : Ideal.span (s : Set R) = I ^ n := hs
    apply key s (by intro z hz; rw [← hs']; exact Ideal.subset_span hz)
    rw [hs']
    exact ih _ le_sup_right

/-- **Lemma `lem:sm-fd-local-criterion`.** The local criterion of flatness with explicit
multipliers. -/
theorem exists_mul_mem_of_localCriterion [IsNoetherianRing R] [IsNoetherianRing P]
    [Module.Flat R P] {K : Ideal P} {a : R} {I : Ideal R} (h1 : IsGood K a I)
    (h2 : ∀ 𝔟 : Ideal R, I ≤ 𝔟 → ∀ x ∈ (K ⊔ I.map (algebraMap R P)) ⊓ 𝔟.map (algebraMap R P),
      ∃ k : ℕ, algebraMap R P a ^ k * x ∈
        𝔟.map (algebraMap R P) * K ⊔ I.map (algebraMap R P))
    (𝔟 : Ideal R) {x : P} (hx : x ∈ K ⊓ 𝔟.map (algebraMap R P)) :
    ∃ (N : ℕ) (s : P), s - algebraMap R P a ^ N ∈ I.map (algebraMap R P) ∧
      s * x ∈ 𝔟.map (algebraMap R P) * K := by
  let D : Ideal P := 𝔟.map (algebraMap R P) * K
  let xb : P ⧸ D := Ideal.Quotient.mk D x
  have hpow : ∀ n : ℕ, ∃ k : ℕ, algebraMap R P a ^ k • xb ∈
      I.map (algebraMap R P) ^ n • (⊤ : Submodule P (P ⧸ D)) := by
    intro n
    have hgood := isGood_of_pow_le h1 h2 n (𝔟 ⊔ I ^ n) le_sup_right
    obtain ⟨hxK, hx𝔟⟩ := Submodule.mem_inf.mp hx
    obtain ⟨k, hk⟩ := hgood x (Submodule.mem_inf.mpr ⟨hxK, Ideal.map_mono le_sup_left hx𝔟⟩)
    refine ⟨k, ?_⟩
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.sup_mul] at hk
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hk
    have hzpow : z ∈ I.map (algebraMap R P) ^ n := Ideal.mul_le_left hz
    have : algebraMap R P a ^ k • xb = z • (1 : P ⧸ D) := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, ← map_mul,
        ← hyz, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, zero_add]
    rw [this]
    exact Submodule.smul_mem_smul hzpow Submodule.mem_top
  obtain ⟨N, s, hs, hsx⟩ := exists_sub_pow_mem_smul_eq_zero (I.map (algebraMap R P))
    (algebraMap R P a) xb hpow
  refine ⟨N, s, hs, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
  exact hsx

end DeJongAlterations.StableModification.Limits.FlatDescent
