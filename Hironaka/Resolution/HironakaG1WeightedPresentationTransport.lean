import Hironaka.Resolution.HironakaG1FiniteWeightedBlocks

/-! Matching weighted presentations modulo their normalized block references. -/
set_option autoImplicit false

open Set
open scoped BigOperators Manifold ContDiff

namespace Hironaka.HironakaG1WeightedPresentationTransport

private theorem pow_sup_le_pow_sup {R : Type*} [CommRing R] (A B : Ideal R) (d : ℕ) :
    (A ⊔ B) ^ d ≤ A ^ d ⊔ B := by
  induction d with
  | zero => simp [Ideal.one_eq_top]
  | succ d ih =>
    simp only [pow_succ]
    refine (mul_le_mul' ih le_rfl).trans ?_
    simp only [Ideal.sup_mul, Ideal.mul_sup]
    have hBA : B * A ≤ B := Ideal.mul_le_left
    have hAB : A ^ d * B ≤ B := Ideal.mul_le_right
    have hBB : B * B ≤ B := Ideal.mul_le_left
    exact sup_le (sup_le le_sup_left (hBA.trans le_sup_right))
      (sup_le (hAB.trans le_sup_right) (hBB.trans le_sup_right))

private theorem sum_le_of_summands_le {S R : Type*} [CommRing R]
    (s : Finset S) (I : S → Ideal R) (K : Ideal R) (h : ∀ i ∈ s, I i ≤ K) :
    ∑ i ∈ s, I i ≤ K := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Ideal.add_eq_sup]
    exact sup_le (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem summand_le_sum {S R : Type*} [CommRing R] (s : Finset S)
    (I : S → Ideal R) {i : S} (hi : i ∈ s) : I i ≤ ∑ j ∈ s, I j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.notMem_empty i hi).elim
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Ideal.add_eq_sup]
    rcases Finset.mem_insert.mp hi with rfl | hs
    · exact le_sup_left
    · exact (ih hs).trans le_sup_right

/-- The reference ideal is the sum of the block ideals at their own
normalized exponents. -/
def blockPowerReference {S R : Type*} [Fintype S] [CommRing R]
    (e : S → ℕ) (A : S → Ideal R) : Ideal R :=
  ∑ i, A i ^ e i

/-- Block containment modulo the target normalized reference is sufficient
for inclusion of the normalized references. -/
theorem blockPowerReference_le_of_modulo {S R : Type*} [Fintype S] [CommRing R]
    (e : S → ℕ) (A B : S → Ideal R)
    (h : ∀ i, A i ≤ B i ⊔ blockPowerReference e B) :
    blockPowerReference e A ≤ blockPowerReference e B := by
  apply sum_le_of_summands_le
  intro i _
  have hi : B i ^ e i ≤ blockPowerReference e B :=
    summand_le_sum Finset.univ (fun j => B j ^ e j) (Finset.mem_univ i)
  exact (pow_le_pow_left' (h i) _).trans
    ((pow_sup_le_pow_sup (B i) (blockPowerReference e B) _).trans (sup_le hi le_rfl))

/-- The normalized reference is invariant under mutually compatible changes
of generators modulo the full normalized ideals. Equality of individual
whole block spans is a sufficient special case. -/
theorem blockPowerReference_eq_of_mutual_modulo {S R : Type*} [Fintype S] [CommRing R]
    (e : S → ℕ) (A B : S → Ideal R)
    (hAB : ∀ i, A i ≤ B i ⊔ blockPowerReference e B)
    (hBA : ∀ i, B i ≤ A i ⊔ blockPowerReference e A) :
    blockPowerReference e A = blockPowerReference e B :=
  le_antisymm (blockPowerReference_le_of_modulo e A B hAB)
    (blockPowerReference_le_of_modulo e B A hBA)

private theorem span_le_modulo_of_generator_change {ι κ R : Type*} [CommRing R]
    (c : ι → R) (d : κ → R) (K : Ideal R)
    (h : ∀ j, ∃ y ∈ Ideal.span (range d), c j - y ∈ K) :
    Ideal.span (range c) ≤ Ideal.span (range d) ⊔ K := by
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  obtain ⟨y, hy, he⟩ := h j
  have hm := (Ideal.span (range d) ⊔ K).add_mem (Ideal.mem_sup_left hy) (Ideal.mem_sup_right he)
  rwa [add_comm y, sub_add_cancel] at hm

/-- A presentation change may include errors from other blocks once they
belong to the normalized reference. In both directions it is enough to
match each generator with any element of the corresponding block span. -/
theorem blockPowerReference_eq_of_generator_changes {S R : Type*} [Fintype S] [CommRing R]
    {ι κ : S → Type*} (e : S → ℕ) (c : (i : S) → ι i → R) (d : (i : S) → κ i → R)
    (hCD : ∀ i j, ∃ y ∈ Ideal.span (range (d i)), c i j - y ∈
      blockPowerReference e (fun a => Ideal.span (range (d a))))
    (hDC : ∀ i j, ∃ y ∈ Ideal.span (range (c i)), d i j - y ∈
      blockPowerReference e (fun a => Ideal.span (range (c a)))) :
    blockPowerReference e (fun i => Ideal.span (range (c i))) =
      blockPowerReference e (fun i => Ideal.span (range (d i))) :=
  blockPowerReference_eq_of_mutual_modulo e _ _
    (fun i => span_le_modulo_of_generator_change (c i) (d i) _ (hCD i))
    (fun i => span_le_modulo_of_generator_change (d i) (c i) _ (hDC i))

/-- An unchanged source generator raised to its normalized block exponent
contributes an allowed error in every other block. -/
theorem blockGenerator_power_mem_reference {S R : Type*} [Fintype S] [CommRing R]
    {τ : S → Type*} (e : S → ℕ) (c : (i : S) → τ i → R) (i : S) (j : τ i) :
    c i j ^ e i ∈ blockPowerReference e (fun a => Ideal.span (range (c a))) := by
  have hi : c i j ∈ Ideal.span (range (c i)) := Ideal.subset_span ⟨j, rfl⟩
  exact (summand_le_sum Finset.univ (fun a => (Ideal.span (range (c a))) ^ e a)
    (Finset.mem_univ i)) (Ideal.pow_mem_pow hi _)



/-- A weighted change of basis may add multiples of a full normalized
power from another unchanged block. The original block spans may change. -/
theorem blockPowerReference_eq_of_crossBlock_shear {S R : Type*} [Fintype S] [CommRing R]
    {τ : S → Type*} (e : S → ℕ) (c d : (i : S) → τ i → R)
    (target source : S) (hDifferent : source ≠ target) (b : τ source)
    (a : τ target → R)
    (hTarget : ∀ j, d target j = c target j + a j * c source b ^ e source)
    (hOther : ∀ i, i ≠ target → ∀ j, d i j = c i j) :
    blockPowerReference e (fun i => Ideal.span (range (c i))) =
      blockPowerReference e (fun i => Ideal.span (range (d i))) := by
  have hc := blockGenerator_power_mem_reference e c source b
  have hd := blockGenerator_power_mem_reference e d source b
  rw [hOther source hDifferent b] at hd
  apply blockPowerReference_eq_of_generator_changes e c d
  · intro i j
    refine ⟨d i j, Ideal.subset_span ⟨j, rfl⟩, ?_⟩
    by_cases hi : i = target
    · subst i
      rw [hTarget]
      have he : c target j - (c target j + a j * c source b ^ e source) =
          -(a j * c source b ^ e source) := by ring
      rw [he]
      exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ hd)
    · rw [hOther i hi j, sub_self]
      exact Ideal.zero_mem _
  · intro i j
    refine ⟨c i j, Ideal.subset_span ⟨j, rfl⟩, ?_⟩
    by_cases hi : i = target
    · subst i
      rw [hTarget, add_sub_cancel_left]
      exact Ideal.mul_mem_left _ _ hc
    · rw [hOther i hi j, sub_self]
      exact Ideal.zero_mem _

/-- The cross-weight shear criterion strictly extends equality of each
block span. These exponents arise from weights `(1,2)` with one label
in each block and common mark two. -/
theorem exists_crossWeight_shear_with_different_block_span :
    ∃ c d : (i : Fin 2) → Unit → ℤ,
      blockPowerReference (![2, 1] : Fin 2 → ℕ) (fun i => Ideal.span (range (c i))) =
        blockPowerReference (![2, 1] : Fin 2 → ℕ) (fun i => Ideal.span (range (d i))) ∧
      Ideal.span (range (c 0)) ≠ Ideal.span (range (d 0)) := by
  let c : (i : Fin 2) → Unit → ℤ := fun i _ => if i = 0 then 2 else 6
  let d : (i : Fin 2) → Unit → ℤ := fun i _ => if i = 0 then 8 else 6
  refine ⟨c, d, ?_, ?_⟩
  · apply blockPowerReference_eq_of_crossBlock_shear _ c d 0 1 (by decide) () (fun _ => 1)
    · intro j
      norm_num [c, d]
    · intro i hi j
      simp [c, d, hi]
  · intro h
    have hMem : (2 : ℤ) ∈ Ideal.span (range (d 0)) := by
      rw [← h]
      exact Ideal.subset_span ⟨(), rfl⟩
    have hRange : range (d 0) = {(8 : ℤ)} := by
      ext z
      simp [d]
    rw [hRange, Ideal.mem_span_singleton] at hMem
    norm_num at hMem

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaG1FiniteWeightedBlocks HironakaActualWeightedCoefficientCompression
  HironakaSmoothSubmersionGermIdealColon HironakaG8LocalHistory

/-- The generator changes are tested in a common adapted analytic chart at
each point. The two presentations may have different sets of labels in a
matched block, with equality of the actual cross marks. -/
def HasFilteredBlockChange {n : ℕ} {X : CMfd.{0} n}
    (S : Type*) [Fintype S] (τ υ : S → Type*) [∀ i, Fintype (τ i)] [∀ i, Fintype (υ i)]
    (w : S → ℕ) (P Q B : MarkedIdeal n X) (x : X) : Prop :=
  let e := fun i => weightedCommonMark (blockWeights (τ := τ) w) / w i
  ∃ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (c : (i : S) → τ i → HolGerm (ComplexModel n))
    (d : (i : S) → υ i → HolGerm (ComplexModel n)),
      adaptedIdeal P.ideal x Φ h0 =
        weightedCompression (blockWeights (τ := τ) w) (fun a => c a.1 a.2) ∧
      adaptedIdeal Q.ideal x Φ h0 =
        weightedCompression (blockWeights (τ := υ) w) (fun a => d a.1 a.2) ∧
      adaptedIdeal B.ideal x Φ h0 =
        blockPowerReference e (fun i => Ideal.span (range (c i))) ∧
      (∀ i j, ∃ y ∈ Ideal.span (range (d i)), c i j - y ∈
        blockPowerReference e (fun a => Ideal.span (range (d a)))) ∧
      (∀ i j, ∃ y ∈ Ideal.span (range (c i)), d i j - y ∈
        blockPowerReference e (fun a => Ideal.span (range (c a))))

/-- The mutual filtered changes supply the matched coherent reference
needed by the proper-carrier local-test comparison. -/
theorem locWPEquiv_of_filteredBlockChanges
    {n k l q : ℕ} {X : CMfd.{0} n}
    (S : Type*) [Fintype S] (τ υ : S → Type*)
    [∀ i, Fintype (τ i)] [∀ i, Fintype (υ i)]
    [∀ i, Nonempty (τ i)] [∀ i, Nonempty (υ i)]
    (w : S → ℕ) (hw : ∀ i, 0 < w i)
    (hCross : weightedCommonMark (blockWeights (τ := τ) w) =
      weightedCommonMark (blockWeights (τ := υ) w))
    (P Q B : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q) (hB : IsInvDomain q B)
    (hPN : P.N = B.N) (hQN : Q.N = B.N) (hPE : B.E = P.E) (hQE : B.E = Q.E)
    (hPM : P.d = B.d) (hQM : Q.d = B.d)
    (hAt : ∀ x ∈ P.N, HasFilteredBlockChange S τ υ w P Q B x) :
    LocWPEquiv P Q := by
  apply locWPEquiv_of_independent_finiteBlockAdaptedPresentations S S τ υ w w hw hw
    P Q B hP hQ hB hPN hQN hPE hQE hPM hQM
  · intro x hx
    obtain ⟨Φ, h0, c, d, hPComp, hQComp, hRef, _, _⟩ := hAt x hx
    exact ⟨Φ, h0, c, hPComp, hRef⟩
  · intro x hx
    have hxP : x ∈ P.N := by rwa [hPN, ← hQN]
    obtain ⟨Φ, h0, c, d, hPComp, hQComp, hRef, hCD, hDC⟩ := hAt x hxP
    refine ⟨Φ, h0, d, hQComp, ?_⟩
    have hEq := blockPowerReference_eq_of_generator_changes
      (fun i => weightedCommonMark (blockWeights (τ := τ) w) / w i) c d hCD hDC
    rw [hRef, hEq]
    unfold blockPowerReference
    rw [hCross]

end Hironaka.HironakaG1WeightedPresentationTransport
