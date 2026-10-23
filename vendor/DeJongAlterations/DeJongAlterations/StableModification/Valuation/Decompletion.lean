import DeJongAlterations.StableModification.Valuation.Analytic.Hensel
import DeJongAlterations.StableModification.Valuation.CompositionUnramified
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Decompletion of standard-unramified extensions

This file formalizes the converse direction of the decompletion criterion, Proposition 2.2.1
(`unramcrit1`) of M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), §2.2 (`semi-stable.tex`, lines 2100–2140), in the form needed for the induction of
Theorem 2.1.8: the generator is produced with a **prescribed residue** and with reduced minimal
polynomial `g̃ · X^m`, which is the *adapted* form consumed by the composition criterion
`IsStdUnramifiedGenerator.compose_of_adapted` (plan `PLAN-SM-VAL.md`, node M0).
Blueprint: `sm-val-uniformization-dec.tex`, `prop:sm-val-decompletion`.

## Setting

`L/K` is a finite separable extension, `B` a valuation subring of `L` and `A = B ∩ K`. The
"completions" are given abstractly: `E` is an analytic field (complete, non-trivially normed,
non-archimedean) with a dense map `K → E`, and `M` is a finite normed extension of `E` with a map
`L → M` over `K`, such that `B = {y ∈ L | ‖y‖_M ≤ 1}` (hypothesis `hB`). In the typical case `B`
has height one, `M = L̂` and `E = K̂` is the closure of `K` in `M`.

## Main results

* `exists_isStdUnramifiedGenerator_of_finrank_le` (**decompletion criterion with prescribed
  residue**): if `[M : E] ≤ [κ(B) : κ(A)]` and `η ∈ κ(B)` is a nonzero separable generator of
  `κ(B)/κ(A)`, then `L/K` has a standard-unramified generator `x` at `B` with `x̄ = η` whose
  minimal polynomial over `A` reduces to `minpoly η · X^m`.
* `exists_isStdUnramifiedGenerator_of_isStdUnramified`, `isStdUnramified_of_isStdUnramified`:
  Temkin's formulation, assuming `L` dense in `M` and `M/E` standard-unramified.

## Method

Temkin decomposes `K̂ ⊗_K L` into the completions at all extensions of the valuation. Here only
the given completion `M` is used. Let `Ω` be an algebraic closure of `E` with its spectral norm;
every `K`-embedding `τ : L → Ω` defines a valuation ring `B_τ = {y | ‖τ y‖ ≤ 1}` of `L` over `A`
(`embRing`). The generator `x` is chosen in the integral closure of `A` with residue `η` and with
`‖τ x‖ < 1` whenever `B_τ ≠ B` (`exists_good_element`, using that the centres on the integral
closure are maximal ideals, `centerIdeal_isMaximal`). Over `E` the minimal polynomial `f` of `x`
factors as `g h` with `g` the minimal polynomial of `x` in `M`. If `B_τ = B` then `τ x` is a root
of `g` (`aeval_eq_zero_of_forall_mem_iff`, an approximation argument), so by separability the roots
of `h` are the `τ x` with `B_τ ≠ B`, which are small; hence `h ≡ X^m` modulo the maximal ideal
(`norm_coeff_lt_one_of_forall_roots`), while the reduction of `g` is the minimal polynomial of
`η` by the degree bound `[M : E] ≤ [κ(B) : κ(A)]`.
-/

noncomputable section

open IsLocalRing Polynomial

namespace DeJongAlterations.StableModification.Valuation.Decompletion

open Analytic

/-! ### Valuation rings defined by absolute values -/

section NormRing

variable {L F : Type*} [Field L] [NormedField F]

/-- If a valuation subring `V` of `L` is the preimage of the unit ball under `φ : L → F`, then
`v_V(y) < 1` iff `‖φ y‖ < 1`. -/
theorem valuation_lt_one_iff_of_forall_mem_iff {V : ValuationSubring L} {φ : L →+* F}
    (hV : ∀ y, y ∈ V ↔ ‖φ y‖ ≤ 1) (y : L) : V.valuation y < 1 ↔ ‖φ y‖ < 1 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hpos : 0 < ‖φ y‖ := norm_pos_iff.mpr ((map_ne_zero φ).mpr hy)
  rw [← not_le, ← not_le, Valuation.one_le_val_iff _ hy, V.valuation_le_one_iff, hV, map_inv₀,
    norm_inv, inv_le_one₀ hpos]

/-- If a valuation subring `V` of `L` is the preimage of the unit ball under `φ : L → F`, then
`v_V(y) = 1` iff `‖φ y‖ = 1`. -/
theorem valuation_eq_one_iff_of_forall_mem_iff {V : ValuationSubring L} {φ : L →+* F}
    (hV : ∀ y, y ∈ V ↔ ‖φ y‖ ≤ 1) (y : L) : V.valuation y = 1 ↔ ‖φ y‖ = 1 := by
  rw [le_antisymm_iff, le_antisymm_iff, V.valuation_le_one_iff, hV, ← not_lt, ← not_lt,
    valuation_lt_one_iff_of_forall_mem_iff hV]
  simp only [not_lt]

variable [IsUltrametricDist F]

/-- The valuation subring `{y | ‖φ y‖ ≤ 1}` of `L` defined by a homomorphism `φ` into a
non-archimedean normed field (for `φ` a `K`-embedding into an algebraic closure of `K̂`, this is
the extension `B_τ` of the valuation of `K` in the proof of the decompletion criterion). -/
def embRing (φ : L →+* F) : ValuationSubring L :=
  (unitBall F).comap φ

@[simp]
theorem mem_embRing {φ : L →+* F} {y : L} : y ∈ embRing φ ↔ ‖φ y‖ ≤ 1 := by
  rw [embRing, ValuationSubring.mem_comap, mem_unitBall]

end NormRing

/-! ### Comparing valuation rings with the same restriction -/

/-- In a linearly ordered commutative group with zero, `a < 1` and `b ≤ 1` give `a * b < 1`. -/
theorem mul_lt_one_of_lt_of_le' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a < 1) (hb : b ≤ 1) : a * b < 1 := by
  rw [mul_comm]
  exact Right.mul_lt_one_of_le_of_lt hb ha

section SameRestriction

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- `v_V(y) < 1` iff `y ∈ V` and `y⁻¹ ∉ V` (or `y = 0`). -/
theorem valuation_lt_one_iff_mem_and (V : ValuationSubring L) (y : L) :
    V.valuation y < 1 ↔ y ∈ V ∧ (y = 0 ∨ y⁻¹ ∉ V) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [← not_le, Valuation.one_le_val_iff _ hy, V.valuation_le_one_iff]
  constructor
  · intro h
    refine ⟨?_, Or.inr h⟩
    rcases V.mem_or_inv_mem y with h' | h'
    · exact h'
    · exact absurd h' h
  · rintro ⟨-, h | h⟩
    · exact absurd h hy
    · exact h

/-- Two valuation subrings of `L` with the same restriction to `K` agree on which elements of `K`
have value `< 1`. -/
theorem valuation_algebraMap_lt_one_iff_of_comap_eq {B V : ValuationSubring L}
    (hV : V.comap (algebraMap K L) = B.comap (algebraMap K L)) (c : K) :
    V.valuation (algebraMap K L c) < 1 ↔ B.valuation (algebraMap K L c) < 1 := by
  have hmem : ∀ d : K, algebraMap K L d ∈ V ↔ algebraMap K L d ∈ B := fun d ↦ by
    rw [← ValuationSubring.mem_comap, hV, ValuationSubring.mem_comap]
  rw [valuation_lt_one_iff_mem_and, valuation_lt_one_iff_mem_and, hmem, ← map_inv₀, hmem]

/-- An element integral over `B ∩ K` lies in every valuation subring with the same restriction. -/
theorem mem_of_isIntegral_of_comap_eq {B V : ValuationSubring L}
    (hV : V.comap (algebraMap K L) = B.comap (algebraMap K L)) {z : L}
    (hz : IsIntegral (B.comap (algebraMap K L)) z) : z ∈ V :=
  mem_of_isIntegral_comap V (hV ▸ hz)

/-- An element of `K` has value `< 1` for `B` iff it lies in the maximal ideal of `B ∩ K`. -/
theorem mem_maximalIdeal_comap_iff (B : ValuationSubring L) (a : B.comap (algebraMap K L)) :
    a ∈ maximalIdeal (B.comap (algebraMap K L)) ↔ B.valuation (algebraMap K L a) < 1 := by
  rw [← comap_maximalIdeal_comap B, Ideal.mem_comap, B.valuation_lt_one_iff]
  rfl

end SameRestriction

/-! ### Centres on the integral closure -/

section Center

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The inclusion of the integral closure of `B ∩ K` into a valuation subring `V` of `L` with the
same restriction to `K`. -/
def toCenter (B V : ValuationSubring L)
    (hV : V.comap (algebraMap K L) = B.comap (algebraMap K L)) :
    integralClosure (B.comap (algebraMap K L)) L →+* V :=
  (integralClosure (B.comap (algebraMap K L)) L).val.toRingHom.codRestrict V.toSubring
    fun z ↦ mem_of_isIntegral_of_comap_eq hV z.2

/-- The centre `𝔪_V ∩ Ā` of a valuation subring `V` of `L` over `A = B ∩ K` on the integral
closure `Ā` of `A` in `L`. -/
def centerIdeal (B V : ValuationSubring L)
    (hV : V.comap (algebraMap K L) = B.comap (algebraMap K L)) :
    Ideal (integralClosure (B.comap (algebraMap K L)) L) :=
  (maximalIdeal V).comap (toCenter B V hV)

theorem mem_centerIdeal {B V : ValuationSubring L}
    {hV : V.comap (algebraMap K L) = B.comap (algebraMap K L)}
    {z : integralClosure (B.comap (algebraMap K L)) L} :
    z ∈ centerIdeal B V hV ↔ V.valuation (z : L) < 1 := by
  rw [centerIdeal, Ideal.mem_comap, V.valuation_lt_one_iff]
  rfl

instance centerIdeal_isPrime (B V : ValuationSubring L)
    (hV : V.comap (algebraMap K L) = B.comap (algebraMap K L)) :
    (centerIdeal B V hV).IsPrime :=
  Ideal.comap_isPrime _ _

/-- **Centres are maximal** (blueprint `lem:sm-val-dec-center-maximal`): for `L/K` algebraic, the
centre `𝔪_V ∩ Ā` of a valuation ring `V` over `A` is a maximal ideal of `Ā`. -/
theorem centerIdeal_isMaximal (B V : ValuationSubring L)
    (hV : V.comap (algebraMap K L) = B.comap (algebraMap K L)) :
    (centerIdeal B V hV).IsMaximal := by
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := B.comap (algebraMap K L))
  have : (centerIdeal B V hV).comap
      (algebraMap (B.comap (algebraMap K L)) (integralClosure (B.comap (algebraMap K L)) L)) =
      maximalIdeal (B.comap (algebraMap K L)) := by
    ext a
    rw [Ideal.mem_comap, mem_centerIdeal, mem_maximalIdeal_comap_iff]
    exact valuation_algebraMap_lt_one_iff_of_comap_eq hV a
  rw [this]
  infer_instance

end Center

/-! ### Choice of the generator -/

section Choice

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Separating two extensions** (blueprint `lem:sm-val-dec-separating`): if `V ≠ B` are
valuation rings of the algebraic extension `L` with the same restriction `A` to `K`, some
`a ∈ Ā` has `v_V(a) < 1` and `v_B(a) = 1`. -/
theorem exists_isIntegral_valuation_lt_one_valuation_eq_one [Algebra.IsAlgebraic K L]
    {B V : ValuationSubring L} (hV : V.comap (algebraMap K L) = B.comap (algebraMap K L))
    (hne : V ≠ B) :
    ∃ a : L, IsIntegral (B.comap (algebraMap K L)) a ∧ V.valuation a < 1 ∧ B.valuation a = 1 := by
  set P := centerIdeal (K := K) B B rfl
  set Q := centerIdeal B V hV
  have hPQ : Q ≠ P := by
    intro h
    apply hne
    refine (eq_of_comap_eq_of_valuation_lt_one_iff hV.symm fun z hz ↦ ?_).symm
    have := congrArg (fun I ↦ (⟨z, hz⟩ : integralClosure (B.comap (algebraMap K L)) L) ∈ I) h
    simp only [Q, P, eq_iff_iff, mem_centerIdeal] at this
    exact this.symm
  have hQP : ¬ Q ≤ P := fun hle ↦
    hPQ ((centerIdeal_isMaximal B V hV).eq_of_le (centerIdeal_isMaximal B B rfl).ne_top hle)
  obtain ⟨a, haQ, haP⟩ := Set.not_subset.mp hQP
  refine ⟨a, a.2, mem_centerIdeal.mp haQ, ?_⟩
  have h1 : B.valuation (a : L) ≤ 1 :=
    (B.valuation_le_one_iff _).mpr (mem_of_isIntegral_comap B a.2)
  exact le_antisymm h1 (not_lt.mp fun h ↦ haP (mem_centerIdeal.mpr h))

/-- **Residues are represented by integral elements** (blueprint
`lem:sm-val-dec-residue-lift`): for `L/K` algebraic, every element of `κ(B)` is the residue of an
element integral over `B ∩ K`. -/
theorem exists_isIntegral_residue_eq [Algebra.IsAlgebraic K L] (B : ValuationSubring L)
    (η : ResidueField B) :
    ∃ z : L, ∃ hz : IsIntegral (B.comap (algebraMap K L)) z,
      residue B ⟨z, mem_of_isIntegral_comap B hz⟩ = η := by
  obtain ⟨b, rfl⟩ := residue_surjective η
  obtain ⟨s, t, hs, ht, hsv, hst⟩ := exists_isIntegral_mul_eq (k := K) B b.2
  set P := centerIdeal (K := K) B B rfl
  have hsP : (⟨s, hs⟩ : integralClosure (B.comap (algebraMap K L)) L) ∉ P := by
    rw [mem_centerIdeal]
    simp [hsv]
  obtain ⟨s', i, hi, hsi⟩ := (centerIdeal_isMaximal B B rfl).exists_inv hsP
  have hz : IsIntegral (B.comap (algebraMap K L)) (t * s') := ht.mul s'.2
  refine ⟨t * s', hz, ?_⟩
  rw [eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, B.valuation_lt_one_iff]
  have hsi' : (s' : L) * s + i = 1 := congrArg Subtype.val hsi
  have hdiff : ((b - ⟨t * s', mem_of_isIntegral_comap B hz⟩ : B) : L) = (b : L) * i := by
    change (b : L) - t * s' = _
    rw [← hst]
    linear_combination (-(b : L)) * hsi'
  rw [hdiff, map_mul]
  have hb : B.valuation (b : L) ≤ 1 := (B.valuation_le_one_iff _).mpr b.2
  exact Right.mul_lt_one_of_le_of_lt hb (mem_centerIdeal.mp hi)

/-- **Primitive perturbations** (blueprint `lem:sm-val-dec-primitive`): if `L = K(u)` is finite
separable and the powers of `π ∈ K` are pairwise distinct, then `L = K(x₀ + π^(N+1) u)` for some
`N`. -/
theorem exists_adjoin_add_pow_smul_eq_top [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (x₀ : L) {u : L} (hu : IntermediateField.adjoin K {u} = ⊤) {π : K}
    (hπ : Function.Injective fun n : ℕ ↦ π ^ n) :
    ∃ N : ℕ, IntermediateField.adjoin K {x₀ + algebraMap K L π ^ (N + 1) * u} = ⊤ := by
  have : Finite (IntermediateField K L) :=
    Field.finite_intermediateField_of_exists_primitive_element K L ⟨u, hu⟩
  obtain ⟨N, N', hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun N : ℕ ↦ IntermediateField.adjoin K {x₀ + algebraMap K L π ^ (N + 1) * u})
  refine ⟨N, ?_⟩
  set F := IntermediateField.adjoin K {x₀ + algebraMap K L π ^ (N + 1) * u}
  have h1 : x₀ + algebraMap K L π ^ (N + 1) * u ∈ F :=
    IntermediateField.mem_adjoin_simple_self K _
  have h2 : x₀ + algebraMap K L π ^ (N' + 1) * u ∈ F := by
    have := IntermediateField.mem_adjoin_simple_self K (x₀ + algebraMap K L π ^ (N' + 1) * u)
    have heq' : IntermediateField.adjoin K {x₀ + algebraMap K L π ^ (N + 1) * u} =
        IntermediateField.adjoin K {x₀ + algebraMap K L π ^ (N' + 1) * u} := heq
    rwa [← heq'] at this
  have hc : π ^ (N + 1) - π ^ (N' + 1) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hne (Nat.succ_injective (hπ h))
  have hu' : u = (algebraMap K L (π ^ (N + 1) - π ^ (N' + 1)))⁻¹ *
      ((x₀ + algebraMap K L π ^ (N + 1) * u) - (x₀ + algebraMap K L π ^ (N' + 1) * u)) := by
    have : algebraMap K L (π ^ (N + 1) - π ^ (N' + 1)) ≠ 0 :=
      (map_ne_zero (algebraMap K L)).mpr hc
    field_simp
    simp only [map_sub, map_pow]
    ring
  have huF : u ∈ F := by
    rw [hu']
    exact F.mul_mem (F.inv_mem (F.algebraMap_mem _)) (F.sub_mem h1 h2)
  exact top_le_iff.mp (hu ▸ IntermediateField.adjoin_simple_le_iff.mpr huF)

/-- Simultaneous separation (first half of blueprint `lem:sm-val-dec-good-element`): for a finite
set `T` of valuation rings `V ≠ B` over `A`, some `a ∈ Ā` is a unit of `B` and lies in the
maximal ideal of every `V ∈ T`. -/
theorem exists_isIntegral_valuation_lt_one_forall [Algebra.IsAlgebraic K L]
    (B : ValuationSubring L) (T : Finset (ValuationSubring L))
    (hT : ∀ V ∈ T, V.comap (algebraMap K L) = B.comap (algebraMap K L) ∧ V ≠ B) :
    ∃ a : L, IsIntegral (B.comap (algebraMap K L)) a ∧ B.valuation a = 1 ∧
      ∀ V ∈ T, V.valuation a < 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, isIntegral_one, map_one _, fun V hV ↦ absurd hV (Finset.notMem_empty V)⟩
  | insert V₀ T _ ih =>
    obtain ⟨a, ha, haB, haT⟩ := ih fun V hV ↦ hT V (Finset.mem_insert_of_mem hV)
    obtain ⟨hV₀, hne⟩ := hT V₀ (Finset.mem_insert_self V₀ T)
    obtain ⟨a₀, ha₀, ha₀V, ha₀B⟩ := exists_isIntegral_valuation_lt_one_valuation_eq_one hV₀ hne
    refine ⟨a * a₀, ha.mul ha₀, by rw [map_mul, haB, ha₀B, one_mul], fun V hV ↦ ?_⟩
    rw [map_mul]
    rcases Finset.mem_insert.mp hV with rfl | hV
    · exact Right.mul_lt_one_of_le_of_lt
        ((V.valuation_le_one_iff _).mpr (mem_of_isIntegral_of_comap_eq hV₀ ha)) ha₀V
    · have hVc : V.comap (algebraMap K L) = B.comap (algebraMap K L) :=
        (hT V (Finset.mem_insert_of_mem hV)).1
      exact mul_lt_one_of_lt_of_le' (haT V hV)
        ((V.valuation_le_one_iff _).mpr (mem_of_isIntegral_of_comap_eq hVc ha₀))

/-- **Choice of the generator** (blueprint `lem:sm-val-dec-good-element`): for a finite set `T` of
valuation rings `V ≠ B` of `L` over `A`, an element `π ∈ K` with `0 < v_B(π) < 1` and
`η ∈ κ(B)`, there is `x ∈ Ā` with `L = K(x)`, `x̄ = η` and `v_V(x) < 1` for all `V ∈ T`. -/
theorem exists_good_element [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : ValuationSubring L) (T : Finset (ValuationSubring L))
    (hT : ∀ V ∈ T, V.comap (algebraMap K L) = B.comap (algebraMap K L) ∧ V ≠ B) {π : K}
    (hπB : B.valuation (algebraMap K L π) < 1) (hπ0 : π ≠ 0) (η : ResidueField B) :
    ∃ x : L, ∃ hx : IsIntegral (B.comap (algebraMap K L)) x,
      IntermediateField.adjoin K {x} = ⊤ ∧ residue B ⟨x, mem_of_isIntegral_comap B hx⟩ = η ∧
        ∀ V ∈ T, V.valuation x < 1 := by
  set A := B.comap (algebraMap K L)
  obtain ⟨a, ha, haB, haT⟩ := exists_isIntegral_valuation_lt_one_forall (K := K) B T hT
  have haU : IsUnit (⟨a, mem_of_isIntegral_comap B ha⟩ : B) := (B.valuation_eq_one_iff _).mpr haB
  set abar := residue B ⟨a, mem_of_isIntegral_comap B ha⟩
  have habar : abar ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr haU
  obtain ⟨y₁, hy₁, hy₁res⟩ := exists_isIntegral_residue_eq (K := K) B (η * abar⁻¹)
  have hx₀ : IsIntegral A (y₁ * a) := hy₁.mul ha
  have hx₀res : residue B ⟨y₁ * a, mem_of_isIntegral_comap B hx₀⟩ = η := by
    have : (⟨y₁ * a, mem_of_isIntegral_comap B hx₀⟩ : B) =
        ⟨y₁, mem_of_isIntegral_comap B hy₁⟩ * ⟨a, mem_of_isIntegral_comap B ha⟩ := rfl
    rw [this, map_mul, hy₁res, inv_mul_cancel_right₀ habar]
  -- an integral primitive element
  obtain ⟨u₀, hu₀⟩ := Field.exists_primitive_element K L
  have hu₀alg : IsAlgebraic A u₀ :=
    (IsFractionRing.isAlgebraic_iff A K L).mpr (Algebra.IsAlgebraic.isAlgebraic u₀)
  obtain ⟨c, hc0, hcu⟩ := hu₀alg.exists_integral_multiple
  set u := c • u₀
  have hcK : (c : K) ≠ 0 := fun h ↦ hc0 (Subtype.ext h)
  have hu : IntermediateField.adjoin K {u} = ⊤ := by
    have hu' : u = algebraMap K L c * u₀ := by
      show c • u₀ = _
      rw [Algebra.smul_def]
      rfl
    refine top_le_iff.mp (hu₀ ▸ IntermediateField.adjoin_simple_le_iff.mpr ?_)
    have : u₀ = (algebraMap K L c)⁻¹ * u := by
      rw [hu', ← mul_assoc, inv_mul_cancel₀ ((_root_.map_ne_zero _).mpr hcK), one_mul]
    rw [this]
    exact IntermediateField.mul_mem _ (IntermediateField.inv_mem _
      (IntermediateField.algebraMap_mem _ _)) (IntermediateField.mem_adjoin_simple_self K u)
  have hπ : Function.Injective fun n : ℕ ↦ π ^ n := by
    set γ := B.valuation (algebraMap K L π)
    have hγ0 : γ ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (_root_.map_ne_zero _).mpr hπ0
    have key : ∀ n k : ℕ, γ ^ (n + (k + 1)) ≠ γ ^ n := by
      intro n k h
      rw [pow_add] at h
      have h1 : γ ^ (k + 1) = 1 :=
        mul_left_cancel₀ (pow_ne_zero n hγ0) (h.trans (mul_one _).symm)
      exact ((pow_lt_one_iff (Nat.succ_ne_zero k)).mpr hπB).ne h1
    intro n m h
    have h' : π ^ n = π ^ m := h
    have hv : γ ^ n = γ ^ m := by
      have := congrArg (fun z ↦ B.valuation (algebraMap K L z)) h'
      simpa only [map_pow] using this
    by_contra hnm
    rcases lt_or_gt_of_ne hnm with hnm | hnm
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnm
      exact key n k (by rw [← add_assoc]; exact hv.symm)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnm
      exact key m k (by rw [← add_assoc]; exact hv)
  obtain ⟨N, hN⟩ := exists_adjoin_add_pow_smul_eq_top (y₁ * a) hu hπ
  have hπA : IsIntegral A (algebraMap K L π) := by
    have hmem : π ∈ A := by
      rw [ValuationSubring.mem_comap, ← B.valuation_le_one_iff]
      exact hπB.le
    have : algebraMap K L π = algebraMap A L ⟨π, hmem⟩ := rfl
    rw [this]
    exact isIntegral_algebraMap
  set x := y₁ * a + algebraMap K L π ^ (N + 1) * u
  have hx : IsIntegral A x := hx₀.add ((hπA.pow _).mul hcu)
  have hsmall : ∀ V : ValuationSubring L, V.comap (algebraMap K L) = A →
      V.valuation (algebraMap K L π ^ (N + 1) * u) < 1 := by
    intro V hV
    rw [map_mul, map_pow]
    refine mul_lt_one_of_lt_of_le' ?_ ?_
    · exact (pow_lt_one_iff (Nat.succ_ne_zero N)).mpr
        ((valuation_algebraMap_lt_one_iff_of_comap_eq hV π).mpr hπB)
    · exact (V.valuation_le_one_iff _).mpr (mem_of_isIntegral_of_comap_eq hV hcu)
  refine ⟨x, hx, hN, ?_, fun V hV ↦ ?_⟩
  · have hsplit : (⟨x, mem_of_isIntegral_comap B hx⟩ : B) =
        ⟨y₁ * a, mem_of_isIntegral_comap B hx₀⟩ +
          ⟨algebraMap K L π ^ (N + 1) * u, mem_of_isIntegral_comap B ((hπA.pow _).mul hcu)⟩ :=
      rfl
    rw [hsplit, map_add, hx₀res, add_eq_left, residue_eq_zero_iff, B.valuation_lt_one_iff]
    exact hsmall B rfl
  · have hVc := (hT V hV).1
    refine Valuation.map_add_lt _ ?_ (hsmall V hVc)
    rw [map_mul]
    exact Right.mul_lt_one_of_le_of_lt
      ((V.valuation_le_one_iff _).mpr (mem_of_isIntegral_of_comap_eq hVc hy₁)) (haT V hV)

end Choice

/-! ### Ultrametric estimates for polynomials -/

section Estimates

variable {E : Type*} [NormedField E] [IsUltrametricDist E]

omit [IsUltrametricDist E] in
/-- (Blueprint `lem:sm-val-dec-poly-estimates`.) If the coefficients of `P` have norm at most
`C` and `‖z‖ ≤ 1`, then `‖P(z)‖ ≤ C`. -/
theorem norm_aeval_le_of_norm_coeff_le {F : Type*} [NormedField F] [IsUltrametricDist F]
    [NormedAlgebra E F] {z : F} (hz : ‖z‖ ≤ 1) (P : E[X]) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ j, ‖P.coeff j‖ ≤ C) : ‖aeval z P‖ ≤ C := by
  rw [aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun j _ ↦ ?_
  rw [norm_smul, norm_pow]
  calc ‖P.coeff j‖ * ‖z‖ ^ j ≤ C * 1 :=
        mul_le_mul (hP j) (pow_le_one₀ (norm_nonneg _) hz) (by positivity) hC
    _ = C := mul_one C

/-- (Blueprint `lem:sm-val-dec-poly-estimates`.) Coefficient bound for a product of
polynomials over a non-archimedean field. -/
theorem norm_coeff_mul_le (P Q : E[X]) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hP : ∀ i, ‖P.coeff i‖ ≤ C) (hQ : ∀ j, ‖Q.coeff j‖ ≤ D) (n : ℕ) :
    ‖(P * Q).coeff n‖ ≤ C * D := by
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hC hD) fun ij _ ↦ ?_
  rw [norm_mul]
  exact mul_le_mul (hP _) (hQ _) (norm_nonneg _) hC

/-- A product of elements of norm at most one has norm at most one. -/
theorem norm_multiset_prod_le_one {Ω : Type*} [NormedField Ω] {s : Multiset Ω}
    (hs : ∀ β ∈ s, ‖β‖ ≤ 1) : ‖s.prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (hs a (Multiset.mem_cons_self a t)) (norm_nonneg _)
      (ih fun β hβ ↦ hs β (Multiset.mem_cons_of_mem hβ))

/-- A nonempty product of elements of norm `< 1` has norm `< 1`. -/
theorem norm_multiset_prod_lt_one {Ω : Type*} [NormedField Ω] {s : Multiset Ω} (hs0 : s ≠ 0)
    (hs : ∀ β ∈ s, ‖β‖ < 1) : ‖s.prod‖ < 1 := by
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hs0
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [Multiset.prod_cons, norm_mul]
  calc ‖a‖ * ‖t.prod‖ ≤ ‖a‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_multiset_prod_le_one fun β hβ ↦
          (hs β (Multiset.mem_cons_of_mem hβ)).le) (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact hs a ha

omit [IsUltrametricDist E] in
/-- **Monic polynomials with small roots** (blueprint `lem:sm-val-dec-small-roots`): if all roots
of the monic `h ∈ E[X]` in an algebraically closed non-archimedean extension `Ω` have norm `< 1`,
then all coefficients of `h` below the leading one have norm `< 1`. -/
theorem norm_coeff_lt_one_of_forall_roots {Ω : Type*} [NormedField Ω] [IsUltrametricDist Ω]
    [NormedAlgebra E Ω] [IsAlgClosed Ω] {h : E[X]} (hm : h.Monic)
    (hroots : ∀ β ∈ (h.map (algebraMap E Ω)).roots, ‖β‖ < 1) {j : ℕ} (hj : j < h.natDegree) :
    ‖h.coeff j‖ < 1 := by
  classical
  set H := h.map (algebraMap E Ω)
  have hsplit : H.Splits := IsAlgClosed.splits H
  have hdeg : H.natDegree = h.natDegree := natDegree_map _
  have hHm : H.Monic := hm.map _
  have hcoeff := coeff_eq_esymm_roots_of_splits hsplit (k := j) (by rw [hdeg]; exact hj.le)
  rw [hHm.leadingCoeff, one_mul, coeff_map] at hcoeff
  rw [← norm_algebraMap' Ω (h.coeff j), hcoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]
  have hk : H.natDegree - j ≠ 0 := by omega
  unfold Multiset.esymm
  by_cases h0 : H.roots.powersetCard (H.natDegree - j) = 0
  · rw [h0, Multiset.map_zero, Multiset.sum_zero, norm_zero]
    exact zero_lt_one
  obtain ⟨t, ht, hle⟩ := IsUltrametricDist.exists_norm_multiset_sum_le
    (H.roots.powersetCard (H.natDegree - j)) (f := Multiset.prod)
  obtain ⟨htle, htcard⟩ := Multiset.mem_powersetCard.mp (ht h0)
  refine hle.trans_lt
    (norm_multiset_prod_lt_one ?_ fun β hβ ↦ hroots β (Multiset.mem_of_le htle hβ))
  intro h0'
  rw [h0', Multiset.card_zero] at htcard
  exact hk htcard.symm

end Estimates

/-! ### The setting of the decompletion criterion -/

section Setting

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {E M : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  [NormedField M] [IsUltrametricDist M] [NormedAlgebra E M]
  [Algebra K E] [Algebra L M] [Algebra K M] [IsScalarTower K E M] [IsScalarTower K L M]

omit [IsUltrametricDist E] [IsUltrametricDist M] in
/-- Elements of `K` have the same norm in `E` and in `M`. -/
theorem norm_algebraMap_algebraMap (c : K) :
    ‖algebraMap L M (algebraMap K L c)‖ = ‖algebraMap K E c‖ := by
  rw [← IsScalarTower.algebraMap_apply K L M, IsScalarTower.algebraMap_apply K E M,
    norm_algebraMap']

omit [NormedField M] [IsUltrametricDist M] [NormedAlgebra E M] [Algebra L M] [Algebra K M]
  [IsScalarTower K E M] [IsScalarTower K L M] [Algebra K L] [Field L] in
/-- A dense subfield of a non-trivially normed non-archimedean field contains an element of norm
strictly between `0` and `1`. -/
theorem exists_norm_algebraMap_lt_one (hdense : DenseRange (algebraMap K E)) :
    ∃ π : K, 0 < ‖algebraMap K E π‖ ∧ ‖algebraMap K E π‖ < 1 := by
  obtain ⟨e, he0, he1⟩ := NormedField.exists_norm_lt_one E
  obtain ⟨π, hπ⟩ := Metric.denseRange_iff.mp hdense e ‖e‖ he0
  rw [dist_eq_norm] at hπ
  have h := norm_eq_of_norm_sub_lt hπ
  exact ⟨π, h ▸ he0, h ▸ he1⟩

omit [IsUltrametricDist E] [IsUltrametricDist M] in
/-- An element of `B ∩ K` is in the maximal ideal iff its norm in `E` is `< 1`. -/
theorem mem_maximalIdeal_comap_iff_norm {B : ValuationSubring L}
    (hB : ∀ y, y ∈ B ↔ ‖algebraMap L M y‖ ≤ 1) (a : B.comap (algebraMap K L)) :
    a ∈ maximalIdeal (B.comap (algebraMap K L)) ↔ ‖algebraMap K E (a : K)‖ < 1 := by
  rw [mem_maximalIdeal_comap_iff, valuation_lt_one_iff_of_forall_mem_iff hB,
    norm_algebraMap_algebraMap (E := E)]

omit [IsUltrametricDist E] [IsUltrametricDist M] in
/-- An element of `K` of norm at most one in `E` lies in `B ∩ K`. -/
theorem mem_comap_of_norm_le_one {B : ValuationSubring L}
    (hB : ∀ y, y ∈ B ↔ ‖algebraMap L M y‖ ≤ 1) {c : K} (hc : ‖algebraMap K E c‖ ≤ 1) :
    c ∈ B.comap (algebraMap K L) := by
  rw [ValuationSubring.mem_comap, hB, norm_algebraMap_algebraMap (E := E)]
  exact hc

omit [IsUltrametricDist E] [IsUltrametricDist M] in
/-- The valuation ring `B_τ` defined by a `K`-embedding `τ` of `L` into a normed `E`-algebra has
the same restriction to `K` as `B` (blueprint `lem:sm-val-dec-norm-ring`). -/
theorem comap_embRing {Ω : Type*} [NormedField Ω] [IsUltrametricDist Ω] [NormedAlgebra E Ω]
    [Algebra K Ω] [IsScalarTower K E Ω] {B : ValuationSubring L}
    (hB : ∀ y, y ∈ B ↔ ‖algebraMap L M y‖ ≤ 1) (τ : L →ₐ[K] Ω) :
    (embRing τ.toRingHom).comap (algebraMap K L) = B.comap (algebraMap K L) := by
  ext c
  rw [ValuationSubring.mem_comap, mem_embRing, ValuationSubring.mem_comap, hB,
    norm_algebraMap_algebraMap (E := E)]
  change ‖τ (algebraMap K L c)‖ ≤ 1 ↔ _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K E Ω, norm_algebraMap']

/-- **Embeddings inducing `B` see the local factor** (blueprint
`lem:sm-val-dec-isometric-root`): let `τ : L → Ω` be a `K`-embedding into a non-archimedean
`E`-algebra with `B_τ = B`, let `x ∈ B`, and let `P ∈ E[X]` be monic with `P(x) = 0` in `M`.
Then `P(τ x) = 0`. -/
theorem aeval_eq_zero_of_forall_mem_iff {Ω : Type*} [NormedField Ω] [IsUltrametricDist Ω]
    [NormedAlgebra E Ω] [Algebra K Ω] [IsScalarTower K E Ω]
    {B : ValuationSubring L} (hB : ∀ y, y ∈ B ↔ ‖algebraMap L M y‖ ≤ 1)
    (hdense : DenseRange (algebraMap K E)) (τ : L →ₐ[K] Ω) (hτ : ∀ y, y ∈ B ↔ ‖τ y‖ ≤ 1)
    {x : L} (hx : x ∈ B) {P : E[X]} (hPm : P.Monic) (hPx : aeval (algebraMap L M x) P = 0) :
    aeval (τ x) P = 0 := by
  obtain ⟨π, hπ0, hπ1⟩ := exists_norm_algebraMap_lt_one hdense
  set r := ‖algebraMap K E π‖
  have hxM : ‖algebraMap L M x‖ ≤ 1 := (hB x).mp hx
  have hxΩ : ‖τ x‖ ≤ 1 := (hτ x).mp hx
  have hτπ : ‖τ (algebraMap K L π)‖ = r := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K E Ω, norm_algebraMap']
  by_contra hne
  have hδ : 0 < ‖aeval (τ x) P‖ := norm_pos_iff.mpr hne
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ hπ1
  have hrN : 0 < r ^ N := pow_pos hπ0 N
  obtain ⟨Q, -, -, hQ⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hdense hPm hrN
  -- `‖Q(x)‖_M ≤ r ^ N`
  have h1 : ‖algebraMap L M (aeval x Q)‖ ≤ r ^ N := by
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap E, ← sub_zero (aeval _ (Q.map _)),
      ← hPx, ← map_sub]
    exact norm_aeval_le_of_norm_coeff_le hxM _ hrN.le fun j ↦ by
      rw [coeff_sub]
      exact (hQ j).le
  -- hence `‖Q(τ x)‖ ≤ r ^ N`
  have h2 : ‖aeval (τ x) Q‖ ≤ r ^ N := by
    have hmem : aeval x Q * (algebraMap K L π ^ N)⁻¹ ∈ B := by
      rw [hB, map_mul, map_inv₀, map_pow, norm_mul, norm_inv, norm_pow,
        norm_algebraMap_algebraMap (E := E), mul_inv_le_iff₀ hrN, one_mul]
      exact h1
    have := (hτ _).mp hmem
    rw [map_mul, map_inv₀, map_pow, norm_mul, norm_inv, norm_pow, hτπ, mul_inv_le_iff₀ hrN,
      one_mul, ← aeval_algHom_apply] at this
    exact this
  -- and `‖P(τ x)‖ ≤ r ^ N`, a contradiction
  have h3 : ‖aeval (τ x) P‖ ≤ r ^ N := by
    have hdiff : ‖aeval (τ x) (P - Q.map (algebraMap K E))‖ ≤ r ^ N :=
      norm_aeval_le_of_norm_coeff_le hxΩ _ hrN.le fun j ↦ by
        rw [coeff_sub, norm_sub_rev]
        exact (hQ j).le
    have : aeval (τ x) P = aeval (τ x) (P - Q.map (algebraMap K E)) + aeval (τ x) Q := by
      rw [map_sub, aeval_map_algebraMap, sub_add_cancel]
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hdiff h2)
  exact lt_irrefl _ (h3.trans_lt hN)

variable [CompleteSpace E]

/-- **Decompletion criterion with prescribed residue** (Temkin, Proposition 2.2.1, converse
direction, adapted form; blueprint `prop:sm-val-decompletion`). Let `L/K` be finite separable,
`B` a valuation subring of `L` with `B = {y | ‖y‖_M ≤ 1}` for a finite normed extension `M` of an
analytic field `E` in which `K` is dense, and assume `[M : E] ≤ [κ(B) : κ(A)]`, `A = B ∩ K`. For
every nonzero `η ∈ κ(B)` separable over `κ(A)` with `κ(B) = κ(A)(η)` there is a
standard-unramified generator `x` of `L/K` at `B` with residue `η` whose minimal polynomial over
`A` reduces to `minpoly η · X^m`. -/
theorem exists_isStdUnramifiedGenerator_of_finrank_le
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [FiniteDimensional E M]
    (B : ValuationSubring L) (hB : ∀ y, y ∈ B ↔ ‖algebraMap L M y‖ ≤ 1)
    (hdense : DenseRange (algebraMap K E))
    (hdeg : Module.finrank E M ≤
      Module.finrank (ResidueField (B.comap (algebraMap K L))) (ResidueField B))
    {η : ResidueField B} (hη0 : η ≠ 0)
    (hgen : IntermediateField.adjoin (ResidueField (B.comap (algebraMap K L))) {η} = ⊤)
    (hsep : IsSeparable (ResidueField (B.comap (algebraMap K L))) η) :
    ∃ x : L, ∃ hx : IsStdUnramifiedGenerator K B x, residue B ⟨x, hx.mem⟩ = η ∧
      ∃ m : ℕ, (minpoly (B.comap (algebraMap K L)) x).map (residue (B.comap (algebraMap K L))) =
        minpoly (ResidueField (B.comap (algebraMap K L))) η * X ^ m := by
  classical
  set A := B.comap (algebraMap K L)
  set κA := ResidueField A
  -- an algebraic closure `Ω` of `E` with its spectral norm
  let : NontriviallyNormedField (AlgebraicClosure E) :=
    spectralNorm.nontriviallyNormedField E (AlgebraicClosure E)
  let : NormedAlgebra E (AlgebraicClosure E) := spectralNorm.normedAlgebra E (AlgebraicClosure E)
  have : IsUltrametricDist (AlgebraicClosure E) := IsUltrametricDist.of_normedAlgebra E
  let : Fintype (L →ₐ[K] AlgebraicClosure E) := Fintype.ofFinite _
  -- the finite set of the valuation rings `B_τ ≠ B`
  set T : Finset (ValuationSubring L) :=
    (Finset.univ.image fun τ : L →ₐ[K] AlgebraicClosure E ↦ embRing τ.toRingHom).filter (· ≠ B)
  have hcomap : ∀ τ : L →ₐ[K] AlgebraicClosure E,
      (embRing τ.toRingHom).comap (algebraMap K L) = A := fun τ ↦ comap_embRing (E := E) hB τ
  have hT : ∀ V ∈ T, V.comap (algebraMap K L) = A ∧ V ≠ B := by
    intro V hV
    simp only [T, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hV
    obtain ⟨⟨τ, rfl⟩, hne⟩ := hV
    exact ⟨hcomap τ, hne⟩
  obtain ⟨π, hπ0, hπ1⟩ := exists_norm_algebraMap_lt_one hdense
  have hπB : B.valuation (algebraMap K L π) < 1 := by
    rw [valuation_lt_one_iff_of_forall_mem_iff hB, norm_algebraMap_algebraMap (E := E)]
    exact hπ1
  have hπ0' : π ≠ 0 := by
    rintro rfl
    simp at hπ0
  obtain ⟨x, hxint, hxtop, hxres, hxT⟩ := exists_good_element B T hT hπB hπ0' η
  have hxB : x ∈ B := mem_of_isIntegral_comap B hxint
  have hxv : B.valuation x = 1 := by
    have : IsUnit (⟨x, hxB⟩ : B) :=
      (residue_ne_zero_iff_isUnit _).mp (by rw [hxres]; exact hη0)
    exact (B.valuation_eq_one_iff _).mp this
  have hxM : ‖algebraMap L M x‖ = 1 := (valuation_eq_one_iff_of_forall_mem_iff hB x).mp hxv
  set xM := algebraMap L M x
  have hxK : IsIntegral K x := hxint.tower_top
  set f := minpoly K x
  set fA := minpoly A x
  have hf : f = fA.map (algebraMap A K) := minpoly.isIntegrallyClosed_eq_field_fractions' K hxint
  have hfsep : f.Separable := Algebra.IsSeparable.isSeparable K x
  -- the local factor `g`
  have hxMint : IsIntegral E xM := Algebra.IsIntegral.isIntegral xM
  set g := minpoly E xM
  have hgm : g.Monic := minpoly.monic hxMint
  have hg1 : ∀ j, ‖g.coeff j‖ ≤ 1 := by
    have h := NormedAlgebra.norm_eq_spectralNorm E xM
    rw [hxM] at h
    exact (spectralValue_le_one_iff hgm).mp h.symm.le
  have hgdvd : g ∣ f.map (algebraMap K E) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, aeval_algebraMap_apply, minpoly.aeval, map_zero]
  obtain ⟨h, hgh⟩ := hgdvd
  have hfEm : (f.map (algebraMap K E)).Monic := (minpoly.monic hxK).map _
  have hhm : h.Monic := hgm.of_mul_monic_left (hgh ▸ hfEm)
  -- the roots of the complementary factor `h` are small
  have hroots : ∀ β ∈ (h.map (algebraMap E (AlgebraicClosure E))).roots, ‖β‖ < 1 := by
    intro β hβ
    have hβh : aeval β h = 0 := by
      rw [mem_roots (hhm.map _).ne_zero, IsRoot.def, eval_map_algebraMap] at hβ
      exact hβ
    have hβf : β ∈ f.aroots (AlgebraicClosure E) := by
      rw [mem_aroots]
      refine ⟨minpoly.ne_zero hxK, ?_⟩
      rw [← aeval_map_algebraMap E, hgh, map_mul, hβh, mul_zero]
    set τ₀ := (IntermediateField.algHomAdjoinIntegralEquiv K hxK).symm ⟨β, hβf⟩
    set e : L →ₐ[K] IntermediateField.adjoin K {x} :=
      (IntermediateField.equivOfEq hxtop.symm).toAlgHom.comp
        IntermediateField.topEquiv.symm.toAlgHom
    set τ := τ₀.comp e
    have hτx : τ x = β := by
      have : e x = IntermediateField.AdjoinSimple.gen K x := rfl
      simp only [τ, AlgHom.comp_apply, this,
        IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen, τ₀]
    by_cases hτB : embRing τ.toRingHom = B
    · exfalso
      have hτ : ∀ y, y ∈ B ↔ ‖τ y‖ ≤ 1 := fun y ↦ by
        rw [← hτB, mem_embRing]
        rfl
      have hgβ : aeval β g = 0 := hτx ▸
        aeval_eq_zero_of_forall_mem_iff hB hdense τ hτ hxB hgm (minpoly.aeval E xM)
      have hsq : Squarefree (f.map (algebraMap K (AlgebraicClosure E))) := hfsep.map.squarefree
      have hfac : f.map (algebraMap K (AlgebraicClosure E)) =
          g.map (algebraMap E (AlgebraicClosure E)) *
            h.map (algebraMap E (AlgebraicClosure E)) := by
        rw [IsScalarTower.algebraMap_eq K E (AlgebraicClosure E), ← Polynomial.map_map, hgh,
          Polynomial.map_mul]
      have hd1 : X - C β ∣ g.map (algebraMap E (AlgebraicClosure E)) :=
        dvd_iff_isRoot.mpr (by rw [IsRoot.def, eval_map_algebraMap]; exact hgβ)
      have hd2 : X - C β ∣ h.map (algebraMap E (AlgebraicClosure E)) :=
        dvd_iff_isRoot.mpr (by rw [IsRoot.def, eval_map_algebraMap]; exact hβh)
      exact not_isUnit_X_sub_C β (hsq _ (hfac ▸ mul_dvd_mul hd1 hd2))
    · have hmem : embRing τ.toRingHom ∈ T := by
        simp only [T, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨τ, rfl⟩, hτB⟩
      have := hxT _ hmem
      rw [valuation_lt_one_iff_of_forall_mem_iff (fun y ↦ mem_embRing)] at this
      rw [← hτx]
      exact this
  have hh1 : ∀ j, j < h.natDegree → ‖h.coeff j‖ < 1 :=
    fun j hj ↦ norm_coeff_lt_one_of_forall_roots hhm hroots hj
  have hhle : ∀ j, ‖h.coeff j‖ ≤ 1 := by
    intro j
    rcases lt_trichotomy j h.natDegree with hj | rfl | hj
    · exact (hh1 j hj).le
    · rw [hhm.coeff_natDegree, norm_one]
    · rw [coeff_eq_zero_of_natDegree_lt hj, norm_zero]
      exact zero_le_one
  -- approximations of `g` and `h` over `K`
  obtain ⟨G, hGm, hGdeg, hG⟩ := exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
    hdense hgm (by norm_num : (1 / 2 : ℝ) > 0)
  obtain ⟨H, hHm, hHdeg, hH⟩ := exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
    hdense hhm (by norm_num : (1 / 2 : ℝ) > 0)
  have happrox : ∀ {p : E[X]} {P : K[X]}, (∀ n, ‖(P.map (algebraMap K E)).coeff n - p.coeff n‖ <
      1 / 2) → ∀ n, ‖(P.map (algebraMap K E)).coeff n‖ ≤ max (1 / 2) ‖p.coeff n‖ := by
    intro p P hP n
    have := IsUltrametricDist.norm_add_le_max ((P.map (algebraMap K E)).coeff n - p.coeff n)
      (p.coeff n)
    rw [sub_add_cancel] at this
    exact this.trans (max_le_max (hP n).le le_rfl)
  have hGle : ∀ n, ‖(G.map (algebraMap K E)).coeff n‖ ≤ 1 := fun n ↦
    (happrox hG n).trans (max_le (by norm_num) (hg1 n))
  have hHle : ∀ n, ‖(H.map (algebraMap K E)).coeff n‖ ≤ 1 := fun n ↦
    (happrox hH n).trans (max_le (by norm_num) (hhle n))
  have hHlt : ∀ n, n < h.natDegree → ‖(H.map (algebraMap K E)).coeff n‖ < 1 := fun n hn ↦
    (happrox hH n).trans_lt (max_lt (by norm_num) (hh1 n hn))
  have hlifts : ∀ P : K[X], (∀ n, ‖(P.map (algebraMap K E)).coeff n‖ ≤ 1) →
      P ∈ lifts (algebraMap A K) := by
    intro P hP
    refine (lifts_iff_coeff_lifts P).mpr fun n ↦
      ⟨⟨P.coeff n, mem_comap_of_norm_le_one (E := E) hB ?_⟩, rfl⟩
    rw [← coeff_map]
    exact hP n
  obtain ⟨GA, hGA, hGAdeg, hGAm⟩ := lifts_and_natDegree_eq_and_monic (hlifts G hGle) hGm
  obtain ⟨HA, hHA, hHAdeg, hHAm⟩ := lifts_and_natDegree_eq_and_monic (hlifts H hHle) hHm
  have hcoeA : ∀ (P : A[X]) (n : ℕ), ((P.coeff n : A) : K) = (P.map (algebraMap A K)).coeff n :=
    fun P n ↦ by rw [coeff_map]; rfl
  -- the reduction of `f_A` is `Ḡ · H̄`
  have hred : fA.map (residue A) = GA.map (residue A) * HA.map (residue A) := by
    rw [← Polynomial.map_mul]
    ext n
    rw [coeff_map, coeff_map, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      mem_maximalIdeal_comap_iff_norm (E := E) hB]
    have hc : (((fA.coeff n - (GA * HA).coeff n : A)) : K) = f.coeff n - (G * H).coeff n := by
      rw [AddSubgroupClass.coe_sub, hcoeA, hcoeA, ← hf, Polynomial.map_mul, hGA, hHA]
    rw [hc, map_sub, ← coeff_map, ← coeff_map, Polynomial.map_mul, hgh, ← coeff_sub]
    have hsplit : g * h - G.map (algebraMap K E) * H.map (algebraMap K E) =
        g * (h - H.map (algebraMap K E)) +
          (g - G.map (algebraMap K E)) * H.map (algebraMap K E) := by
      ring
    rw [hsplit, coeff_add]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · calc ‖(g * (h - H.map (algebraMap K E))).coeff n‖ ≤ 1 * (1 / 2) :=
            norm_coeff_mul_le _ _ zero_le_one (by norm_num) hg1 (fun j ↦ by
              rw [coeff_sub, norm_sub_rev]
              exact (hH j).le) n
        _ < 1 := by norm_num
    · calc ‖((g - G.map (algebraMap K E)) * H.map (algebraMap K E)).coeff n‖ ≤ (1 / 2) * 1 :=
            norm_coeff_mul_le _ _ (by norm_num) zero_le_one (fun j ↦ by
              rw [coeff_sub, norm_sub_rev]
              exact (hG j).le) hHle n
        _ < 1 := by norm_num
  -- `H̄ = X ^ deg h`
  have hHbar : HA.map (residue A) = X ^ h.natDegree := by
    ext n
    rw [coeff_map, coeff_X_pow]
    rcases lt_trichotomy n h.natDegree with hn | rfl | hn
    · rw [if_neg hn.ne, residue_eq_zero_iff, mem_maximalIdeal_comap_iff_norm (E := E) hB, hcoeA,
        hHA, ← coeff_map]
      exact hHlt n hn
    · rw [if_pos rfl, hHdeg, ← hHAdeg, hHAm.coeff_natDegree, map_one]
    · rw [if_neg hn.ne', coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  -- `Ḡ` is the minimal polynomial of `η`
  have hηint : IsIntegral κA η := hsep.isIntegral
  have hmdeg : (minpoly κA η).natDegree = Module.finrank κA (ResidueField B) := by
    rw [← IntermediateField.adjoin.finrank hηint, hgen, IntermediateField.finrank_top']
  have hGbar : GA.map (residue A) = minpoly κA η := by
    refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hηint) (hGAm.map _) ?_ ?_
    · apply minpoly.dvd
      rw [← hxres, ← residue_aeval_comap, residue_eq_zero_iff, B.valuation_lt_one_iff,
        coe_aeval_comap, valuation_lt_one_iff_of_forall_mem_iff hB]
      have hGx : aeval x GA = aeval x G := by rw [← hGA, aeval_map_algebraMap]
      rw [hGx, ← aeval_algebraMap_apply, ← aeval_map_algebraMap E, ← sub_zero (aeval _ (G.map _)),
        ← minpoly.aeval E xM, ← map_sub]
      refine (norm_aeval_le_of_norm_coeff_le hxM.le _ (by norm_num) fun j ↦ ?_).trans_lt
        (by norm_num : (1 / 2 : ℝ) < 1)
      rw [coeff_sub]
      exact (hG j).le
    · rw [hGAm.natDegree_map, hGAdeg, ← hGdeg, hmdeg]
      exact (minpoly.natDegree_le xM).trans hdeg
  have hfac : fA.map (residue A) = minpoly κA η * X ^ h.natDegree := by
    rw [hred, hGbar, hHbar]
  -- `f'(x)` is a unit of `B`
  have hderiv : B.valuation (aeval x (derivative f)) = 1 := by
    set a : B := aeval (⟨x, hxB⟩ : B) (derivative fA)
    have ha : (a : L) = aeval x (derivative f) := by
      rw [coe_aeval_comap]
      exact aeval_derivative_minpoly_comap_eq B hxint
    have hne : residue B a ≠ 0 := by
      rw [residue_aeval_comap, ← derivative_map, hfac, hxres, derivative_mul, map_add, map_mul,
        map_mul, minpoly.aeval, zero_mul, add_zero]
      refine mul_ne_zero (hsep.aeval_derivative_ne_zero (minpoly.aeval κA η)) ?_
      rw [map_pow, aeval_X]
      exact pow_ne_zero _ hη0
    rw [← ha, ← B.valuation_eq_one_iff]
    exact (residue_ne_zero_iff_isUnit a).mp hne
  exact ⟨x, ⟨hxtop, hxint, hderiv⟩, hxres, h.natDegree, hfac⟩

end Setting

/-! ### Temkin's formulation: residue fields of dense subfields -/

section ResidueMap

variable {L F N : Type*} [Field L] [Field F] [NormedField N] [IsUltrametricDist N]
  (φ : L →+* F) (ι₁ : L →+* N) (ι₂ : F →+* N) (hι : ∀ y, ι₂ (φ y) = ι₁ y)
  {V : ValuationSubring L} {W : ValuationSubring F}
  (hV : ∀ y, y ∈ V ↔ ‖ι₁ y‖ ≤ 1) (hW : ∀ z, z ∈ W ↔ ‖ι₂ z‖ ≤ 1)

include hι hV hW

/-- The restriction `V → W` of a homomorphism `φ : L → F` compatible with norms. -/
def normRestrict : V →+* W :=
  φ.restrict V W fun y hy ↦ by rw [hW, hι]; exact (hV y).mp hy

omit [IsUltrametricDist N] in
theorem coe_normRestrict (y : V) : (normRestrict φ ι₁ ι₂ hι hV hW y : F) = φ y := rfl

instance isLocalHom_normRestrict : IsLocalHom (normRestrict φ ι₁ ι₂ hι hV hW) := by
  refine ⟨fun a ha ↦ ?_⟩
  rw [W.valuation_eq_one_iff, valuation_eq_one_iff_of_forall_mem_iff hW, coe_normRestrict, hι]
    at ha
  rw [V.valuation_eq_one_iff, valuation_eq_one_iff_of_forall_mem_iff hV]
  exact ha

/-- If `φ` has dense image for the norms, the residue map `κ(V) → κ(W)` is bijective. -/
theorem bijective_residueField_map_normRestrict
    (hd : ∀ z : F, ∃ y : L, ‖ι₂ (z - φ y)‖ < 1) :
    Function.Bijective (ResidueField.map (normRestrict φ ι₁ ι₂ hι hV hW)) := by
  refine ⟨(ResidueField.map _).injective, fun w ↦ ?_⟩
  obtain ⟨z, rfl⟩ := residue_surjective w
  obtain ⟨y, hy⟩ := hd z
  have hyV : y ∈ V := by
    rw [hV, ← hι]
    have h := IsUltrametricDist.norm_add_le_max (ι₂ (z : F)) (ι₂ ((φ y) - z))
    rw [← map_add, add_sub_cancel] at h
    refine h.trans (max_le ((hW _).mp z.2) ?_)
    rw [← neg_sub, map_neg, norm_neg]
    exact hy.le
  refine ⟨residue V ⟨y, hyV⟩, ?_⟩
  rw [ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    W.valuation_lt_one_iff, valuation_lt_one_iff_of_forall_mem_iff hW]
  exact hy

end ResidueMap

section Temkin

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {E M : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] [CompleteSpace E]
  [NormedField M] [IsUltrametricDist M] [NormedAlgebra E M]
  [Algebra K E] [Algebra L M] [Algebra K M] [IsScalarTower K E M] [IsScalarTower K L M]

omit [IsUltrametricDist E] [CompleteSpace E] in
theorem mem_comap_unitBall_iff (z : E) :
    z ∈ (unitBall M).comap (algebraMap E M) ↔ ‖algebraMap E M z‖ ≤ 1 := by
  rw [ValuationSubring.mem_comap, mem_unitBall]

/-- Every element of the unit ball of a finite extension `M` of a complete field `E` is integral
over `M° ∩ E` (the spectral norm). -/
theorem isIntegral_comap_unitBall [FiniteDimensional E M] {b : M} (hb : b ∈ unitBall M) :
    IsIntegral ((unitBall M).comap (algebraMap E M)) b := by
  have hbE : IsIntegral E b := Algebra.IsIntegral.isIntegral b
  refine isIntegral_comap_of_coeff_mem _ hbE fun i ↦ ?_
  rw [mem_unitBall, norm_algebraMap']
  have h2 : spectralNorm E M b ≤ 1 := by
    rw [← NormedAlgebra.norm_eq_spectralNorm E b]
    exact mem_unitBall.mp hb
  exact (spectralValue_le_one_iff (minpoly.monic hbE)).mp h2 i

omit [IsUltrametricDist E] [CompleteSpace E] in
/-- **Residue degrees under completion** (blueprint `cor:sm-val-decompletion-temkin`): if `K` is
dense in `E` and `L` is dense in `M`, the residue extension of `B` over `A = B ∩ K` has the same
degree as that of `M°` over `M° ∩ E`, and the same separability. -/
theorem finrank_residueField_eq_of_denseRange (B : ValuationSubring L)
    (hB : ∀ y, y ∈ B ↔ ‖algebraMap L M y‖ ≤ 1) (hdK : DenseRange (algebraMap K E))
    (hdL : DenseRange (algebraMap L M)) :
    Module.finrank (ResidueField (B.comap (algebraMap K L))) (ResidueField B) =
        Module.finrank (ResidueField ((unitBall M).comap (algebraMap E M)))
          (ResidueField (unitBall M)) ∧
      (Algebra.IsSeparable (ResidueField ((unitBall M).comap (algebraMap E M)))
          (ResidueField (unitBall M)) →
        Algebra.IsSeparable (ResidueField (B.comap (algebraMap K L))) (ResidueField B)) := by
  set A := B.comap (algebraMap K L)
  set Mc := (unitBall M).comap (algebraMap E M)
  have hι₁ : ∀ c : K, algebraMap E M (algebraMap K E c) = algebraMap L M (algebraMap K L c) :=
    fun c ↦ by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hA : ∀ c : K, c ∈ A ↔ ‖algebraMap L M (algebraMap K L c)‖ ≤ 1 := fun c ↦ by
    rw [ValuationSubring.mem_comap, hB]
  have hdA : ∀ z : E, ∃ c : K, ‖algebraMap E M (z - algebraMap K E c)‖ < 1 := by
    intro z
    obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp hdK z 1 one_pos
    exact ⟨c, by rw [norm_algebraMap', ← dist_eq_norm]; exact hc⟩
  have hdB : ∀ z : M, ∃ y : L, ‖RingHom.id M (z - algebraMap L M y)‖ < 1 := by
    intro z
    obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp hdL z 1 one_pos
    exact ⟨y, by rw [RingHom.id_apply, ← dist_eq_norm]; exact hy⟩
  set φA := normRestrict (algebraMap K E) ((algebraMap L M).comp (algebraMap K L))
    (algebraMap E M) hι₁ (V := A) (W := Mc) hA (mem_comap_unitBall_iff (M := M))
  set φB := normRestrict (algebraMap L M) (algebraMap L M) (RingHom.id M) (fun _ ↦ rfl)
    (V := B) (W := unitBall M) hB (fun z ↦ mem_unitBall)
  set i := RingEquiv.ofBijective _ (bijective_residueField_map_normRestrict (algebraMap K E)
    ((algebraMap L M).comp (algebraMap K L)) (algebraMap E M) hι₁ (V := A) (W := Mc) hA
    (mem_comap_unitBall_iff (M := M)) hdA)
  set j := RingEquiv.ofBijective _ (bijective_residueField_map_normRestrict (algebraMap L M)
    (algebraMap L M) (RingHom.id M) (fun _ ↦ rfl) (V := B) (W := unitBall M) hB
    (fun z ↦ mem_unitBall) hdB)
  have hcomm : (algebraMap (ResidueField Mc) (ResidueField (unitBall M))).comp i.toRingHom =
      j.toRingHom.comp (algebraMap (ResidueField A) (ResidueField B)) := by
    ext a
    obtain ⟨a, rfl⟩ := residue_surjective a
    change algebraMap (ResidueField Mc) (ResidueField (unitBall M))
        (ResidueField.map φA (residue A a)) =
      ResidueField.map φB (algebraMap (ResidueField A) (ResidueField B) (residue A a))
    rw [ResidueField.map_residue]
    change residue (unitBall M) (algebraMap Mc (unitBall M) (φA a)) =
      ResidueField.map φB (residue B (algebraMap A B a))
    rw [ResidueField.map_residue]
    congr 1
    exact Subtype.ext (hι₁ a)
  refine ⟨Algebra.finrank_eq_of_equiv_equiv i j hcomm, fun hsep ↦ ?_⟩
  refine Algebra.IsSeparable.of_equiv_equiv i.symm j.symm ?_
  ext z
  obtain ⟨a, rfl⟩ := i.surjective z
  have h1 := RingHom.congr_fun hcomm a
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at h1 ⊢
  rw [h1, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]

/-- **Decompletion criterion, Temkin's form, with prescribed residue** (Temkin,
Proposition 2.2.1; blueprint `cor:sm-val-decompletion-temkin`): if `L` is dense in `M` and `M/E`
is standard-unramified at the unit ball, then for every nonzero generator `η` of `κ(B)/κ(A)`
the conclusion of `exists_isStdUnramifiedGenerator_of_finrank_le` holds. -/
theorem exists_isStdUnramifiedGenerator_of_isStdUnramified
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [FiniteDimensional E M]
    (B : ValuationSubring L) (hB : ∀ y, y ∈ B ↔ ‖algebraMap L M y‖ ≤ 1)
    (hdK : DenseRange (algebraMap K E)) (hdL : DenseRange (algebraMap L M))
    (hunr : IsStdUnramified E (unitBall M)) {η : ResidueField B} (hη0 : η ≠ 0)
    (hgen : IntermediateField.adjoin (ResidueField (B.comap (algebraMap K L))) {η} = ⊤) :
    ∃ x : L, ∃ hx : IsStdUnramifiedGenerator K B x, residue B ⟨x, hx.mem⟩ = η ∧
      ∃ m : ℕ, (minpoly (B.comap (algebraMap K L)) x).map (residue (B.comap (algebraMap K L))) =
        minpoly (ResidueField (B.comap (algebraMap K L))) η * X ^ m := by
  obtain ⟨z, hz⟩ := hunr
  have hint : ∀ b ∈ unitBall M, IsIntegral ((unitBall M).comap (algebraMap E M)) b :=
    fun b hb ↦ isIntegral_comap_unitBall hb
  obtain ⟨hdeg, hsep⟩ := finrank_residueField_eq_of_denseRange B hB hdK hdL
  have : Algebra.IsSeparable (ResidueField (B.comap (algebraMap K L))) (ResidueField B) :=
    hsep (hz.isSeparable_residueField hint)
  refine exists_isStdUnramifiedGenerator_of_finrank_le B hB hdK ?_ hη0 hgen
    (Algebra.IsSeparable.isSeparable _ η)
  rw [hdeg, hz.finrank_residueField_eq hint]

/-- **Decompletion criterion, Temkin's form** (Temkin, Proposition 2.2.1, converse direction):
if `L/K` is finite separable, `L` is dense in `M`, `K` is dense in `E` and `M/E` is
standard-unramified at the unit ball, then `L/K` is standard-unramified at `B`. -/
theorem isStdUnramified_of_isStdUnramified
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [FiniteDimensional E M]
    (B : ValuationSubring L) (hB : ∀ y, y ∈ B ↔ ‖algebraMap L M y‖ ≤ 1)
    (hdK : DenseRange (algebraMap K E)) (hdL : DenseRange (algebraMap L M))
    (hunr : IsStdUnramified E (unitBall M)) : IsStdUnramified K B := by
  obtain ⟨z, hz⟩ := hunr
  have hint : ∀ b ∈ unitBall M, IsIntegral ((unitBall M).comap (algebraMap E M)) b :=
    fun b hb ↦ isIntegral_comap_unitBall hb
  obtain ⟨hdeg, hsep⟩ := finrank_residueField_eq_of_denseRange B hB hdK hdL
  have : Algebra.IsSeparable (ResidueField (B.comap (algebraMap K L))) (ResidueField B) :=
    hsep (hz.isSeparable_residueField hint)
  have hpos : 0 < Module.finrank (ResidueField (B.comap (algebraMap K L))) (ResidueField B) := by
    rw [hdeg, hz.finrank_residueField_eq hint]
    exact Module.finrank_pos
  have : FiniteDimensional (ResidueField (B.comap (algebraMap K L))) (ResidueField B) :=
    Module.finite_of_finrank_pos hpos
  obtain ⟨η₀, hη₀⟩ := Field.exists_primitive_element (ResidueField (B.comap (algebraMap K L)))
    (ResidueField B)
  by_cases h0 : η₀ = 0
  · have hgen : IntermediateField.adjoin (ResidueField (B.comap (algebraMap K L)))
        {(1 : ResidueField B)} = ⊤ := by
      rw [← hη₀, h0, IntermediateField.adjoin_zero, IntermediateField.adjoin_one]
    obtain ⟨x, hx, -⟩ := exists_isStdUnramifiedGenerator_of_isStdUnramified B hB hdK hdL ⟨z, hz⟩
      one_ne_zero hgen
    exact ⟨x, hx⟩
  · obtain ⟨x, hx, -⟩ := exists_isStdUnramifiedGenerator_of_isStdUnramified B hB hdK hdL ⟨z, hz⟩
      h0 hη₀
    exact ⟨x, hx⟩

end Temkin

end DeJongAlterations.StableModification.Valuation.Decompletion
