import Hironaka.Resolution.HironakaG1NonuniformVertexReduction

/-! Finite sums of weight-block reductions and their proper-carrier test class. -/
set_option autoImplicit false

open Set
open scoped BigOperators Manifold ContDiff

namespace Hironaka.HironakaG1FiniteWeightedBlocks

open HironakaG1NonuniformVertexReduction HironakaActualWeightedCoefficientCompression

private theorem sum_ideals_le {S R : Type*} [CommRing R] (s : Finset S)
    (I : S → Ideal R) (K : Ideal R) (h : ∀ i ∈ s, I i ≤ K) :
    ∑ i ∈ s, I i ≤ K := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Ideal.add_eq_sup]
    exact sup_le (h i (Finset.mem_insert_self _ _))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

private theorem summand_le {S R : Type*} [CommRing R] (s : Finset S)
    (I : S → Ideal R) {i : S} (hi : i ∈ s) :
    I i ≤ ∑ j ∈ s, I j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.notMem_empty i hi).elim
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Ideal.add_eq_sup]
    rcases Finset.mem_insert.mp hi with rfl | hs
    · exact le_sup_left
    · exact (ih hs).trans le_sup_right

/-- Ideal reductions combine over any finite set of blocks. The offsets add. -/
theorem sum_reductions {S R : Type*} [CommRing R] (s : Finset S)
    (A K : S → Ideal R) (r : S → ℕ)
    (hLe : ∀ i ∈ s, A i ≤ K i)
    (hRed : ∀ i ∈ s, A i * K i ^ r i = K i ^ (r i + 1)) :
    (∑ i ∈ s, A i) ≤ (∑ i ∈ s, K i) ∧
    (∑ i ∈ s, A i) * (∑ i ∈ s, K i) ^ (∑ i ∈ s, r i) =
      (∑ i ∈ s, K i) ^ ((∑ i ∈ s, r i) + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hLeft := hLe a (Finset.mem_insert_self _ _)
    have hLeft' := hRed a (Finset.mem_insert_self _ _)
    obtain ⟨hRight, hRight'⟩ := ih
      (fun i hi => hLe i (Finset.mem_insert_of_mem hi))
      (fun i hi => hRed i (Finset.mem_insert_of_mem hi))
    simp only [Finset.sum_insert ha]
    exact ⟨by rw [Ideal.add_eq_sup, Ideal.add_eq_sup]; exact sup_le_sup hLeft hRight,
      add_reductions hLeft hRight hLeft' hRight'⟩

/-- Each label receives its block's positive weight. The common mark is
computed over all labels, including every label occurrence in every block. -/
def blockWeights {S : Type*} {τ : S → Type*} (w : S → ℕ) : (Σ i, τ i) → ℕ :=
  fun a => w a.1

/-- The whole weighted compression reduces to the sum of the corresponding
powers of the whole uncompressed block spans, at the actual cross mark. -/
theorem finite_block_compression_reduction {S R : Type*} [Fintype S] [CommRing R]
    {τ : S → Type*} [∀ i, Fintype (τ i)] [∀ i, Nonempty (τ i)]
    (w : S → ℕ) (hw : ∀ i, 0 < w i) (c : (i : S) → τ i → R) :
    let e := fun i => weightedCommonMark (blockWeights (τ := τ) w) / w i
    let K := ∑ i, (Ideal.span (range (c i))) ^ e i
    let J := weightedCompression (blockWeights (τ := τ) w) (fun a => c a.1 a.2)
    let r := ∑ i, Fintype.card (τ i) * (e i - 1)
    J ≤ K ∧ J * K ^ r = K ^ (r + 1) := by
  classical
  intro e K J r
  let A (i : S) := Ideal.span (range fun j => c i j ^ e i)
  let B (i : S) := (Ideal.span (range (c i))) ^ e i
  let q (i : S) := Fintype.card (τ i) * (e i - 1)
  have hEach (i : S) : A i ≤ B i ∧ A i * (B i) ^ q i = (B i) ^ (q i + 1) := by
    obtain ⟨j⟩ := (inferInstance : Nonempty (τ i))
    have he : 1 ≤ e i :=
      compressionExponent_pos (blockWeights (τ := τ) w) (fun a => hw a.1) ⟨i, j⟩
    exact purePowers_reduce_block (c i) (e i) he
  have hSum : J = ∑ i, A i := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact (summand_le Finset.univ A (Finset.mem_univ i))
        (Ideal.subset_span ⟨j, rfl⟩)
    · apply sum_ideals_le
      intro i _
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨⟨i, j⟩, rfl⟩
  rw [hSum]
  exact sum_reductions Finset.univ A B q (fun i _ => (hEach i).1) (fun i _ => (hEach i).2)

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan IdealWeightPowers BlowupTowers MarkedIdeals
  MarkedIdealOperationsAlong.MarkedIdeal ResolutionInvariantSpec
  HironakaG1CarrierPowerReduction HironakaSmoothSubmersionGermIdealColon
  HironakaG8LocalHistory InvertibleIdealQuotient GermIdealPullbackCalculus

/-- Stalk data for a finite-block actual analytic compression and its
reference. The same chart is used for the two ideals at this point. -/
def HasFiniteBlockAdaptedPresentation {n : ℕ} {X : CMfd.{0} n}
    (S : Type*) [Fintype S] (τ : S → Type*) [∀ i, Fintype (τ i)]
    (w : S → ℕ) (P B : MarkedIdeal n X) (x : X) : Prop :=
  ∃ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (c : (i : S) → τ i → HolGerm (ComplexModel n)),
      adaptedIdeal P.ideal x Φ h0 =
        weightedCompression (blockWeights (τ := τ) w) (fun a => c a.1 a.2) ∧
      adaptedIdeal B.ideal x Φ h0 =
        ∑ i, (Ideal.span (range (c i))) ^ (weightedCommonMark (blockWeights (τ := τ) w) / w i)

/-- The finite-block stalk reductions give a full proper-carrier weak
test comparison with a coherent common reference. -/
theorem locWPEquiv_of_finiteBlockAdaptedPresentations
    {n k l : ℕ} {X : CMfd.{0} n} (S : Type*) [Fintype S]
    (τ : S → Type*) [∀ i, Fintype (τ i)] [∀ i, Nonempty (τ i)]
    (w : S → ℕ) (hw : ∀ i, 0 < w i)
    (P B : MarkedIdeal n X) (hP : IsInvDomain k P) (hB : IsInvDomain l B)
    (hN : P.N = B.N) (hE : B.E = P.E)
    (hMark : P.d = B.d)
    (hAt : ∀ x ∈ P.N, HasFiniteBlockAdaptedPresentation S τ w P B x) :
    LocWPEquiv P B := by
  let r := ∑ i, Fintype.card (τ i) * (weightedCommonMark (blockWeights (τ := τ) w) / w i - 1)
  let J := P.ideal
  let I := B.ideal
  have hJ : J.IsCoherent := hP.isWellFormed.isCoherent
  have hI : I.IsCoherent := hB.isWellFormed.isCoherent
  have hPower : idealPow I 1 = I := FactorizationFromResolution.idealPow_one_of_isCoherent hI
  have hStalk (x : X) (hx : x ∈ P.N) :
      (∀ f, J.mem x f → I.mem x f) ∧
        (∀ f, (idealPow I (1 + r)).mem x f → (J.mul (idealPow I r)).mem x f) := by
    obtain ⟨Φ, h0, c, hComp, hRef⟩ := hAt x hx
    have h := finite_block_compression_reduction w hw c
    have hLe : adaptedIdeal J x Φ h0 ≤ adaptedIdeal I x Φ h0 := by
      change adaptedIdeal P.ideal x Φ h0 ≤ adaptedIdeal B.ideal x Φ h0
      rw [hComp, hRef]
      exact h.1
    have hProduct : adaptedIdeal (J.mul (idealPow I r)) x Φ h0 =
        adaptedIdeal (idealPow I (1 + r)) x Φ h0 := by
      rw [adaptedIdeal_mul_exact _ _ hJ (isCoherent_idealPow hI r) x Φ h0,
        adaptedIdeal_power_exact I hI x Φ h0, adaptedIdeal_power_exact I hI x Φ h0]
      change adaptedIdeal P.ideal x Φ h0 * adaptedIdeal B.ideal x Φ h0 ^ r =
        adaptedIdeal B.ideal x Φ h0 ^ (1 + r)
      rw [hComp, hRef, Nat.add_comm 1 r]
      exact h.2
    constructor
    · intro f hf
      have hh := GermIdeal.IsCoherent.holomorphicAt_mem hJ hf
      exact (mem_adaptedIdeal_iff I hI x Φ h0 f hh).mp
        (hLe ((mem_adaptedIdeal_iff J hJ x Φ h0 f hh).mpr hf))
    · intro f hf
      have hh := GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_idealPow hI (1 + r)) hf
      exact (mem_adaptedIdeal_iff _ (isCoherent_mul hJ (isCoherent_idealPow hI r))
        x Φ h0 f hh).mp (hProduct.symm ▸
          (mem_adaptedIdeal_iff _ (isCoherent_idealPow hI (1 + r)) x Φ h0 f hh).mpr hf)
  apply locWPEquiv_of_restricted_power_reduction (e := 1) (r := r) le_rfl hP hB hN hE
    (by rwa [one_mul])
  · change RestrictedIdealWeight.RestrictLe P.N J (idealPow I 1)
    rw [hPower]
    intro x hx f hf
    have hMem := (hStalk x hx).1 f hf
    exact IsInSpanAt.restrict (isInSpanAt_self hMem (GermIdeal.IsCoherent.holomorphicAt_mem hI hMem))
  · intro x hx f hf
    have hMem := (hStalk x hx).2 f hf
    exact IsInSpanAt.restrict (isInSpanAt_self hMem
      (GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_mul hJ (isCoherent_idealPow hI r)) hMem))


/-- Independently chosen finite block families have the same test class
whenever their actual normalized block spans realize the same coherent
reference on their common proper carrier. -/
theorem locWPEquiv_of_independent_finiteBlockAdaptedPresentations
    {n k l q : ℕ} {X : CMfd.{0} n} (S T : Type*) [Fintype S] [Fintype T]
    (τ : S → Type*) [∀ i, Fintype (τ i)] [∀ i, Nonempty (τ i)]
    (υ : T → Type*) [∀ i, Fintype (υ i)] [∀ i, Nonempty (υ i)]
    (w : S → ℕ) (v : T → ℕ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (P Q B : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hB : IsInvDomain q B)
    (hPN : P.N = B.N) (hQN : Q.N = B.N) (hPE : B.E = P.E) (hQE : B.E = Q.E)
    (hPM : P.d = B.d) (hQM : Q.d = B.d)
    (hAtP : ∀ x ∈ P.N, HasFiniteBlockAdaptedPresentation S τ w P B x)
    (hAtQ : ∀ x ∈ Q.N, HasFiniteBlockAdaptedPresentation T υ v Q B x) :
    LocWPEquiv P Q :=
  (locWPEquiv_of_finiteBlockAdaptedPresentations S τ w hw P B hP hB hPN hPE hPM hAtP).trans
    (locWPEquiv_of_finiteBlockAdaptedPresentations T υ v hv Q B hQ hB hQN hQE hQM hAtQ).symm

end Hironaka.HironakaG1FiniteWeightedBlocks
