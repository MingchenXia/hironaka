import Hironaka.Resolution.HironakaG1WeightedChartTransport

/-! Crossed powers of normalized finite block references in actual charts. -/
set_option autoImplicit false

open Set
open scoped BigOperators Manifold ContDiff

namespace Hironaka.HironakaG1WeightedCrossMark

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  RelativePrincipalizationSpan IdealWeightPowers GermIdealPullbackCalculus InvertibleIdealQuotient
  HironakaG1FiniteWeightedBlocks HironakaActualWeightedCoefficientCompression
  HironakaG1WeightedPresentationTransport HironakaG1WeightedChartTransport
  HironakaSmoothSubmersionGermIdealColon HironakaG8LocalHistory
  HironakaActualPowerBoundaryExponents HironakaG1CarrierPowerReduction

/-- A reduction survives taking whole powers on both sides with the same
offset. The multiplication identity is raised to the chosen power. -/
theorem reduction_pow {R : Type*} [CommRing R] {J K : Ideal R} {r : ℕ}
    (hle : J ≤ K) (h : J * K ^ r = K ^ (r + 1)) (a : ℕ) :
    J ^ a ≤ K ^ a ∧ J ^ a * (K ^ a) ^ r = (K ^ a) ^ (r + 1) := by
  refine ⟨pow_le_pow_left' hle a, ?_⟩
  have hPow := congrArg (fun L : Ideal R => L ^ a) h
  rw [mul_pow, ← pow_mul, ← pow_mul] at hPow
  rw [← pow_mul, ← pow_mul, Nat.mul_comm a r, Nat.mul_comm a (r + 1)]
  exact hPow

/-- Coordinate transport commutes with the whole crossed power of a
normalized block reference. -/
theorem map_crossed_blockPowerReference {S R A : Type*} [Fintype S] [CommRing R] [CommRing A]
    {τ : S → Type*} (φ : R →+* A) (e : S → ℕ) (c : (i : S) → τ i → R) (a : ℕ) :
    Ideal.map φ ((blockPowerReference e (fun i => Ideal.span (range (c i)))) ^ a) =
      (blockPowerReference e (fun i => Ideal.span (range (φ ∘ c i)))) ^ a := by
  rw [Ideal.map_pow, map_blockPowerReference_generators]

variable {n : ℕ} {X : CMfd.{0} n}

/-- One source family gives its original compression and the crossed power
of its normalized reference in its own adapted coordinates. -/
def HasPoweredBlockReference
    (S : Type*) [Fintype S] (τ : S → Type*) [∀ i, Fintype (τ i)]
    (w : S → ℕ) (P B : MarkedIdeal n X) (a : ℕ) (x : X) : Prop :=
  ∃ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (c : (i : S) → τ i → HolGerm (ComplexModel n)),
      adaptedIdeal P.ideal x Φ hΦ =
        weightedCompression (blockWeights (τ := τ) w) (fun j => c j.1 j.2) ∧
      adaptedIdeal B.ideal x Φ hΦ =
        (blockPowerReference (fun i => weightedCommonMark (blockWeights (τ := τ) w) / w i)
          (fun i => Ideal.span (range (c i)))) ^ a

/-- Starting with the original unpowered stalk presentation, construct the
crossed compression's proper-carrier weak comparison to the crossed
coherent reference. -/
theorem locWPEquiv_powerMarked_of_poweredBlockReference
    {k l : ℕ} (S : Type*) [Fintype S] (τ : S → Type*)
    [∀ i, Fintype (τ i)] [∀ i, Nonempty (τ i)]
    (w : S → ℕ) (hw : ∀ i, 0 < w i)
    (P B : MarkedIdeal n X) (hP : IsInvDomain k P) (hB : IsInvDomain l B)
    (a : ℕ) (ha : 1 ≤ a) (hN : P.N = B.N) (hE : B.E = P.E)
    (hMark : P.d * a = B.d)
    (hAt : ∀ x ∈ P.N, HasPoweredBlockReference S τ w P B a x) :
    LocWPEquiv (powerMarked P a) B := by
  let r := ∑ i, Fintype.card (τ i) * (weightedCommonMark (blockWeights (τ := τ) w) / w i - 1)
  let I := B.ideal
  let J := (powerMarked P a).ideal
  have hPP := powerMarked_isInvDomain P hP ha
  have hJ : J.IsCoherent := hPP.isWellFormed.isCoherent
  have hI : I.IsCoherent := hB.isWellFormed.isCoherent
  have hPower : idealPow I 1 = I := FactorizationFromResolution.idealPow_one_of_isCoherent hI
  have hStalk (x : X) (hx : x ∈ P.N) :
      (∀ f, J.mem x f → I.mem x f) ∧
        (∀ f, (idealPow I (1 + r)).mem x f → (J.mul (idealPow I r)).mem x f) := by
    obtain ⟨Φ, hΦ, c, hComp, hRef⟩ := hAt x hx
    have hRed := finite_block_compression_reduction w hw c
    have hCross := reduction_pow hRed.1 hRed.2 a
    have hAdapt : adaptedIdeal J x Φ hΦ = (adaptedIdeal P.ideal x Φ hΦ) ^ a :=
      adaptedIdeal_power_exact P.ideal hP.isWellFormed.isCoherent x Φ hΦ a
    have hLe : adaptedIdeal J x Φ hΦ ≤ adaptedIdeal I x Φ hΦ := by
      rw [hAdapt, hComp]
      change _ ≤ adaptedIdeal B.ideal x Φ hΦ
      rw [hRef]
      exact hCross.1
    have hEq : adaptedIdeal (J.mul (idealPow I r)) x Φ hΦ =
        adaptedIdeal (idealPow I (1 + r)) x Φ hΦ := by
      rw [adaptedIdeal_mul_exact _ _ hJ (isCoherent_idealPow hI r) x Φ hΦ,
        adaptedIdeal_power_exact I hI x Φ hΦ, adaptedIdeal_power_exact I hI x Φ hΦ, hAdapt, hComp]
      change _ * adaptedIdeal B.ideal x Φ hΦ ^ r = adaptedIdeal B.ideal x Φ hΦ ^ (1 + r)
      rw [hRef, Nat.add_comm 1 r]
      exact hCross.2
    constructor
    · intro f hf
      have hh := GermIdeal.IsCoherent.holomorphicAt_mem hJ hf
      exact (mem_adaptedIdeal_iff I hI x Φ hΦ f hh).mp
        (hLe ((mem_adaptedIdeal_iff J hJ x Φ hΦ f hh).mpr hf))
    · intro f hf
      have hh := GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_idealPow hI (1 + r)) hf
      exact (mem_adaptedIdeal_iff _ (isCoherent_mul hJ (isCoherent_idealPow hI r))
        x Φ hΦ f hh).mp (hEq.symm ▸
          (mem_adaptedIdeal_iff _ (isCoherent_idealPow hI (1 + r)) x Φ hΦ f hh).mpr hf)
  apply locWPEquiv_of_restricted_power_reduction (e := 1) (r := r) le_rfl hPP hB hN hE
  · change P.d * a = 1 * B.d
    rwa [one_mul]
  · change RestrictedIdealWeight.RestrictLe P.N J (idealPow I 1)
    rw [hPower]
    intro x hx f hf
    have hMem := (hStalk x hx).1 f hf
    exact IsInSpanAt.restrict (isInSpanAt_self hMem (GermIdeal.IsCoherent.holomorphicAt_mem hI hMem))
  · intro x hx f hf
    have hMem := (hStalk x hx).2 f hf
    exact IsInSpanAt.restrict (isInSpanAt_self hMem
      (GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_mul hJ (isCoherent_idealPow hI r)) hMem))


/-- The two differently marked sources are given in their own actual
charts. Their crossed normalized references agree after the actual
holomorphic transition, with one coherent reference realized on the left. -/
def HasCrossedIndependentBlockReference
    (S T : Type*) [Fintype S] [Fintype T] (τ : S → Type*) (υ : T → Type*)
    [∀ i, Fintype (τ i)] [∀ i, Fintype (υ i)]
    (w : S → ℕ) (v : T → ℕ) (P Q B : MarkedIdeal n X) (x : X) : Prop :=
  ∃ (Φ Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hΘ : Θ.toFun (chartAt (ComplexModel n) x x) = 0)
    (c : (i : S) → τ i → HolGerm (ComplexModel n))
    (d : (i : T) → υ i → HolGerm (ComplexModel n)),
    let R := blockPowerReference (fun i => weightedCommonMark (blockWeights (τ := τ) w) / w i)
      (fun i => Ideal.span (range (c i)))
    let K := blockPowerReference (fun i => weightedCommonMark (blockWeights (τ := υ) v) / v i)
      (fun i => Ideal.span (range (d i)))
    adaptedIdeal P.ideal x Φ hΦ =
      weightedCompression (blockWeights (τ := τ) w) (fun a => c a.1 a.2) ∧
    adaptedIdeal Q.ideal x Θ hΘ =
      weightedCompression (blockWeights (τ := υ) v) (fun a => d a.1 a.2) ∧
    adaptedIdeal B.ideal x Φ hΦ = R ^ Q.d ∧
    Ideal.map (adaptedChartGermEquiv x Φ Θ hΦ hΘ).toRingEquiv.toRingHom (R ^ Q.d) = K ^ P.d

/-- Actual coordinate transport supplies the two promised crossed whole
reference identities in their original respective charts. -/
theorem HasCrossedIndependentBlockReference.each_side
    {S T : Type*} [Fintype S] [Fintype T] {τ : S → Type*} {υ : T → Type*}
    [∀ i, Fintype (τ i)] [∀ i, Fintype (υ i)]
    {w : S → ℕ} {v : T → ℕ} {P Q B : MarkedIdeal n X} {x : X}
    (h : HasCrossedIndependentBlockReference S T τ υ w v P Q B x) :
    HasPoweredBlockReference S τ w P B Q.d x ∧ HasPoweredBlockReference T υ v Q B P.d x := by
  obtain ⟨Φ, Θ, hΦ, hΘ, c, d, hP, hQ, hRef, hCross⟩ := h
  refine ⟨⟨Φ, hΦ, c, hP, hRef⟩, ⟨Θ, hΘ, d, hQ, ?_⟩⟩
  rw [← map_adaptedIdeal_transition B.ideal x Φ Θ hΦ hΘ, hRef]
  exact hCross

/-- Cross the actual positive source marks and compare two independent
presentations at the product mark. Different vertex blocks, labels and
weights are permitted. The ordered boundary and stage cosupports stay
part of the full weak test comparison. -/
theorem locWPEquiv_crossed_of_independentBlockReferences
    {k l q : ℕ} (S T : Type*) [Fintype S] [Fintype T]
    (τ : S → Type*) (υ : T → Type*)
    [∀ i, Fintype (τ i)] [∀ i, Fintype (υ i)]
    [∀ i, Nonempty (τ i)] [∀ i, Nonempty (υ i)]
    (w : S → ℕ) (v : T → ℕ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (P Q B : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q) (hB : IsInvDomain q B)
    (hPN : P.N = B.N) (hQN : Q.N = B.N) (hPE : B.E = P.E) (hQE : B.E = Q.E)
    (hPM : P.d = weightedCommonMark (blockWeights (τ := τ) w))
    (hQM : Q.d = weightedCommonMark (blockWeights (τ := υ) v))
    (hMark : B.d = weightedCommonMark (blockWeights (τ := τ) w) *
      weightedCommonMark (blockWeights (τ := υ) v))
    (hAt : ∀ x ∈ P.N, HasCrossedIndependentBlockReference S T τ υ w v P Q B x) :
    LocWPEquiv (powerMarked P Q.d) (powerMarked Q P.d) ∧ LocWPEquiv P Q ∧
      (powerMarked P Q.d).d = B.d ∧ (powerMarked Q P.d).d = B.d ∧
      (powerMarked P Q.d).E = B.E ∧ (powerMarked Q P.d).E = B.E := by
  have hM : P.d * Q.d = B.d := by rw [hPM, hQM, hMark]
  have hM' : Q.d * P.d = B.d := (Nat.mul_comm _ _).trans hM
  have hL := locWPEquiv_powerMarked_of_poweredBlockReference S τ w hw P B hP hB
    Q.d hQ.one_le_d hPN hPE hM (fun x hx => (hAt x hx).each_side.1)
  have hR := locWPEquiv_powerMarked_of_poweredBlockReference T υ v hv Q B hQ hB
    P.d hP.one_le_d hQN hQE hM'
    (fun x hx => (hAt x (by rwa [hPN, ← hQN])).each_side.2)
  have hBoth := hL.trans hR.symm
  have hPO := HironakaG8LocalPower.locEquiv_powerMarked (κ := Kinds.wp) rfl P hP hQ.one_le_d
  have hQO := HironakaG8LocalPower.locEquiv_powerMarked (κ := Kinds.wp) rfl Q hQ hP.one_le_d
  exact ⟨hBoth, hPO.trans (hBoth.trans hQO.symm), hM, hM', hPE.symm, hQE.symm⟩

end

end Hironaka.HironakaG1WeightedCrossMark
