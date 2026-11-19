import Hironaka.Resolution.HironakaG1UniformVertexReduction
import Hironaka.Resolution.HironakaG1CarrierPowerReduction

/-! Combining reductions across two independently weighted generator blocks. -/
set_option autoImplicit false

open Set TopologicalSpace
open scoped BigOperators Manifold ContDiff

namespace Hironaka.HironakaG1NonuniformVertexReduction

open HironakaActualWeightedCoefficientCompression HironakaG1UniformVertexReduction

private theorem sum_ideals_le {S R : Type*} [CommRing R] (s : Finset S)
    (f : S → Ideal R) (K : Ideal R) (h : ∀ i ∈ s, f i ≤ K) :
    ∑ i ∈ s, f i ≤ K := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Ideal.add_eq_sup]
    exact sup_le (h i (Finset.mem_insert_self _ _))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

private theorem block_term_le {R : Type*} [CommRing R] {A B K L : Ideal R}
    {r i j : ℕ}
    (hReduce : A * K ^ r = K ^ (r + 1))
    (hi : r + 1 ≤ i) :
    K ^ i * L ^ j ≤ (A + B) * (K + L) ^ (i + j - 1) := by
  let u := i - (r + 1)
  have hi' : i = (r + 1) + u := by dsimp [u]; omega
  have hExp : r + u + j = i + j - 1 := by omega
  calc
    K ^ i * L ^ j = A * (K ^ (r + u) * L ^ j) := by
      rw [hi', pow_add, ← hReduce, pow_add]
      simp only [mul_assoc]
    _ ≤ (A + B) * ((K + L) ^ (r + u) * (K + L) ^ j) := by
      rw [Ideal.add_eq_sup (I := A), Ideal.add_eq_sup (I := K)]
      exact mul_le_mul' le_sup_left
        (mul_le_mul' (pow_le_pow_left' le_sup_left _) (pow_le_pow_left' le_sup_right _))
    _ = _ := by rw [← pow_add, hExp]

/-- If two ideal reductions hold separately, their sum is a reduction of
the sum. An exponent larger than the sum of the two offsets forces at
least one of the two block reductions to apply in each term. -/
theorem add_reductions {R : Type*} [CommRing R] {A B K L : Ideal R} {r s : ℕ}
    (hAK : A ≤ K) (hBL : B ≤ L)
    (hA : A * K ^ r = K ^ (r + 1))
    (hB : B * L ^ s = L ^ (s + 1)) :
    (A + B) * (K + L) ^ (r + s) = (K + L) ^ (r + s + 1) := by
  apply le_antisymm
  · rw [pow_succ']
    exact mul_le_mul' (by rw [Ideal.add_eq_sup, Ideal.add_eq_sup]; exact sup_le_sup hAK hBL) le_rfl
  · rw [add_pow]
    apply sum_ideals_le
    intro i hi
    have hBound : i ≤ r + s + 1 := by have := Finset.mem_range.mp hi; omega
    let j := r + s + 1 - i
    have hij : i + j = r + s + 1 := by dsimp [j]; omega
    have hji : j + i = r + s + 1 := by omega
    refine Ideal.mul_le_left.trans ?_
    change K ^ i * L ^ j ≤ _
    by_cases hir : r + 1 ≤ i
    · have h := block_term_le (B := B) (L := L) hA (j := j) hir
      simpa only [hij, Nat.add_sub_cancel] using h
    · have hjs : s + 1 ≤ j := by omega
      have h := block_term_le (B := A) (L := K) hB (j := i) hjs
      rw [hji, Nat.add_sub_cancel, add_comm B A, add_comm L K, mul_comm (L ^ j)] at h
      exact h

/-- A block compressed by a pure power is a reduction of the corresponding
power of the uncompressed ideal. -/
theorem purePowers_reduce_block {ι R : Type*} [Fintype ι] [CommRing R]
    (c : ι → R) (e : ℕ) (he : 1 ≤ e) :
    let K := (Ideal.span (range c)) ^ e
    let J := Ideal.span (range fun i => c i ^ e)
    let r := Fintype.card ι * (e - 1)
    J ≤ K ∧ J * K ^ r = K ^ (r + 1) := by
  intro K J r
  have hI (i : ι) : c i ∈ Ideal.span (range c) := Ideal.subset_span ⟨i, rfl⟩
  refine ⟨Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Ideal.pow_mem_pow (hI i) e), ?_⟩
  have hBound : Fintype.card ι * (e - 1) < e + e * r := by
    have hr : r ≤ e * r := by simpa only [one_mul] using Nat.mul_le_mul_right r he
    change r < e + e * r
    omega
  have h := purePowers_mul_span_pow c e (e * r) hBound
  change J * (Ideal.span (range c)) ^ (e * r) =
    (Ideal.span (range c)) ^ (e + e * r) at h
  change J * ((Ideal.span (range c)) ^ e) ^ r =
    ((Ideal.span (range c)) ^ e) ^ (r + 1)
  rw [← pow_mul, ← pow_mul, Nat.mul_succ, Nat.add_comm (e * r) e]
  exact h

/-- A compression with two blocks at possibly different weights has a
reduction ideal determined by each block's uncompressed span at the
corresponding normalized exponent. -/
theorem two_block_compression_reduction {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] [CommRing R] (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (c : ι → R) (d : κ → R) :
    let w : ι ⊕ κ → ℕ := Sum.elim (fun _ => u) (fun _ => v)
    let e := weightedCommonMark w / u
    let f := weightedCommonMark w / v
    let K := (Ideal.span (range c)) ^ e + (Ideal.span (range d)) ^ f
    let J := weightedCompression w (Sum.elim c d)
    let r := Fintype.card ι * (e - 1) + Fintype.card κ * (f - 1)
    J ≤ K ∧ J * K ^ r = K ^ (r + 1) := by
  intro w e f K J r
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  obtain ⟨j⟩ := (inferInstance : Nonempty κ)
  have hw : ∀ a, 0 < w a := by
    intro a
    cases a
    · exact hu
    · exact hv
  have he : 1 ≤ e := compressionExponent_pos w hw (Sum.inl i)
  have hf : 1 ≤ f := compressionExponent_pos w hw (Sum.inr j)
  let J₀ := Ideal.span (range fun i => c i ^ e)
  let J₁ := Ideal.span (range fun j => d j ^ f)
  have hJ : J = J₀ + J₁ := by
    change Ideal.span (range fun a => Sum.elim c d a ^ (weightedCommonMark w / w a)) = _
    rw [Ideal.add_eq_sup, ← Ideal.span_union]
    congr 1
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      cases a with
      | inl a => exact Or.inl ⟨a, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl a, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
  obtain ⟨h₀, h₀r⟩ := purePowers_reduce_block c e he
  obtain ⟨h₁, h₁r⟩ := purePowers_reduce_block d f hf
  rw [hJ]
  exact ⟨by exact sup_le_sup h₀ h₁,
    add_reductions h₀ h₁ h₀r h₁r⟩


open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan IdealWeightPowers BlowupTowers MarkedIdeals
  MarkedIdealOperationsAlong.MarkedIdeal ResolutionInvariantSpec
  HironakaG1CarrierPowerReduction HironakaSmoothSubmersionGermIdealColon
  HironakaG8LocalHistory InvertibleIdealQuotient GermIdealPullbackCalculus

/-- The blockwise hypothesis at a genuine analytic stalk. The reference is
the sum of the two block ideal powers at their respective exponents. -/
def HasTwoBlockAdaptedPresentation {n : ℕ} {X : CMfd.{0} n}
    (ι κ : Type*) [Fintype ι] [Fintype κ] (u v : ℕ)
    (P B : MarkedIdeal n X) (x : X) : Prop :=
  let w : ι ⊕ κ → ℕ := Sum.elim (fun _ => u) (fun _ => v)
  ∃ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (c : ι → HolGerm (ComplexModel n)) (d : κ → HolGerm (ComplexModel n)),
      adaptedIdeal P.ideal x Φ h0 = weightedCompression w (Sum.elim c d) ∧
      adaptedIdeal B.ideal x Φ h0 =
        (Ideal.span (range c)) ^ (weightedCommonMark w / u) +
          (Ideal.span (range d)) ^ (weightedCommonMark w / v)

/-- The two-block reduction gives the full local test class on the actual
proper carrier. The reference ideal may be assembled in different adapted
coordinates at different points. -/
theorem locWPEquiv_of_twoBlockAdaptedPresentations
    {n k l : ℕ} {X : CMfd.{0} n} (ι κ : Type*) [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (P B : MarkedIdeal n X) (hP : IsInvDomain k P) (hB : IsInvDomain l B)
    (hN : P.N = B.N) (hE : B.E = P.E)
    (hMark : P.d = B.d)
    (hAt : ∀ x ∈ P.N, HasTwoBlockAdaptedPresentation ι κ u v P B x) :
    LocWPEquiv P B := by
  let w : ι ⊕ κ → ℕ := Sum.elim (fun _ => u) (fun _ => v)
  let r := Fintype.card ι * (weightedCommonMark w / u - 1) +
    Fintype.card κ * (weightedCommonMark w / v - 1)
  let J := P.ideal
  let I := B.ideal
  have hJ : J.IsCoherent := hP.isWellFormed.isCoherent
  have hI : I.IsCoherent := hB.isWellFormed.isCoherent
  have hPower : idealPow I 1 = I := FactorizationFromResolution.idealPow_one_of_isCoherent hI
  have hStalk (x : X) (hx : x ∈ P.N) :
      (∀ f, J.mem x f → I.mem x f) ∧
        (∀ f, (idealPow I (1 + r)).mem x f → (J.mul (idealPow I r)).mem x f) := by
    obtain ⟨Φ, h0, c, d, hComp, hRef⟩ := hAt x hx
    have h := two_block_compression_reduction u v hu hv c d
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


open HironakaActualCoherentWeightedCoefficientMarked HironakaActualHistoricalInitialAffineDictionary
  IdealOrderArithmetic RestrictedIdealExtension

private theorem range_elim {ι κ A : Type*} (c : ι → A) (d : κ → A) :
    range (Sum.elim c d) = range c ∪ range d := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨i, rfl⟩
    | inr i => exact Or.inr ⟨i, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr i, rfl⟩

private theorem adaptedIdeal_sum_exact {n : ℕ} {X : CMfd.{0} n}
    (A B : GermIdeal n X) (hA : A.IsCoherent) (hB : B.IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) :
    adaptedIdeal (sumIdeal A B) x Φ h0 = adaptedIdeal A x Φ h0 + adaptedIdeal B x Φ h0 := by
  obtain ⟨U, hU, hxU, a, c, hc, hGenC⟩ := hA x
  obtain ⟨V, hV, hxV, b, d, hd, hGenD⟩ := hB x
  have hCh (i : Fin a) := CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU (hc i) hxU
  have hDh (j : Fin b) := CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hV (hd j) hxV
  have hh (i : Fin a ⊕ Fin b) : HolomorphicAt n (Sum.elim c d i) x := by
    cases i with
    | inl i => exact hCh i
    | inr j => exact hDh j
  have hGen (g : X → ℂ) : (sumIdeal A B).mem x g ↔
      IsInSpanAt (n := n) (· ∈ range (Sum.elim c d)) x g := by
    rw [mem_sumIdeal_iff, range_elim]
    constructor
    · intro hg
      apply IsInSpanAt.trans _ hg
      rintro f (hf | hf)
      · exact ((hGenC x hxU f).mp hf).mono (fun _ hz => Or.inl hz)
      · exact ((hGenD x hxV f).mp hf).mono (fun _ hz => Or.inr hz)
    · intro hg
      apply hg.mono
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact Or.inl ((hGenC x hxU _).mpr (isInSpanAt_self ⟨i, rfl⟩ (hCh i)))
      · exact Or.inr ((hGenD x hxV _).mpr (isInSpanAt_self ⟨i, rfl⟩ (hDh i)))
  rw [actual_native_adapted_ideal_of_whole_generation _ x Φ h0 _ hh hGen,
    actual_native_adapted_ideal_of_whole_generation A x Φ h0 c hCh (hGenC x hxU),
    actual_native_adapted_ideal_of_whole_generation B x Φ h0 d hDh (hGenD x hxV),
    Ideal.add_eq_sup, ← Ideal.span_union]
  congr 1
  have he : (fun i => adaptedGerm x Φ h0 (Sum.elim c d i) (hh i)) =
      Sum.elim (fun i => adaptedGerm x Φ h0 (c i) (hCh i))
        (fun j => adaptedGerm x Φ h0 (d j) (hDh j)) := by
    funext i
    cases i <;> rfl
  rw [he, range_elim]

/-- The coherent reference ideal for an actual two-block holomorphic family. -/
def twoBlockReference {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [Fintype ι] [Fintype κ] (u v : ℕ) (c : ι → X → ℂ) (d : κ → X → ℂ) :
    GermIdeal n X :=
  let w : ι ⊕ κ → ℕ := Sum.elim (fun _ => u) (fun _ => v)
  sumIdeal (idealPow (finiteFunctionIdeal c) (weightedCommonMark w / u))
    (idealPow (finiteFunctionIdeal d) (weightedCommonMark w / v))

/-- Actual holomorphic generator blocks supply the corresponding adapted
presentation of the compressed ideal and its coherent reference. -/
theorem hasTwoBlockAdaptedPresentation_of_functions {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [Fintype ι] [Fintype κ] (u v : ℕ)
    (c : ι → X → ℂ) (d : κ → X → ℂ)
    (hc : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (c i))
    (hd : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (d i))
    (N : Set X) (E : List (Set X)) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) :
    let w : ι ⊕ κ → ℕ := Sum.elim (fun _ => u) (fun _ => v)
    HasTwoBlockAdaptedPresentation ι κ u v
      (⟨N, E, weightedFunctionIdeal w (Sum.elim c d), weightedCommonMark w⟩ : MarkedIdeal n X)
      ⟨N, E, twoBlockReference u v c d, weightedCommonMark w⟩ x := by
  intro w
  have hCh (i : ι) : HolomorphicAt n (c i) x := Filter.Eventually.of_forall fun y => hc i y
  have hDh (j : κ) : HolomorphicAt n (d j) x := Filter.Eventually.of_forall fun y => hd j y
  let C := fun i => adaptedGerm x Φ h0 (c i) (hCh i)
  let D := fun j => adaptedGerm x Φ h0 (d j) (hDh j)
  have hBase (a : ι ⊕ κ) : HolomorphicAt n (Sum.elim c d a) x := by
    cases a with
    | inl i => exact hCh i
    | inr j => exact hDh j
  let z : ι ⊕ κ → X → ℂ := fun a y => Sum.elim c d a y ^ (weightedCommonMark w / w a)
  have hz (a : ι ⊕ κ) : HolomorphicAt n (z a) x :=
    BlowupDerivativeIdeal.holomorphicAt_pow (hBase a) _
  refine ⟨Φ, h0, C, D, ?_, ?_⟩
  · change adaptedIdeal (finiteFunctionIdeal z) x Φ h0 = weightedCompression w (Sum.elim C D)
    rw [actual_native_adapted_ideal_of_whole_generation _ x Φ h0 z hz (fun _ => Iff.rfl)]
    congr 1
    apply congrArg range
    funext a
    have hh : adaptedGerm x Φ h0 (z a) (hz a) =
        (adaptedGerm x Φ h0 (Sum.elim c d a) (hBase a)) ^ (weightedCommonMark w / w a) :=
      HolGerm.mk_pow _ ((holomorphic_adapted_iff x Φ h0 (Sum.elim c d a)).mpr (hBase a)) _
    rw [hh]
    cases a <;> rfl
  · let I := finiteFunctionIdeal (n := n) c
    let J := finiteFunctionIdeal (n := n) d
    let e := weightedCommonMark w / u
    let f := weightedCommonMark w / v
    change adaptedIdeal (sumIdeal (idealPow I e) (idealPow J f)) x Φ h0 =
      (Ideal.span (range C)) ^ e + (Ideal.span (range D)) ^ f
    have hI := isCoherent_finiteFunctionIdeal (n := n) c hc
    have hJ := isCoherent_finiteFunctionIdeal (n := n) d hd
    rw [adaptedIdeal_sum_exact _ _ (isCoherent_idealPow hI e) (isCoherent_idealPow hJ f),
      adaptedIdeal_power_exact I hI, adaptedIdeal_power_exact J hJ,
      actual_native_adapted_ideal_of_whole_generation I x Φ h0 c hCh (fun _ => Iff.rfl),
      actual_native_adapted_ideal_of_whole_generation J x Φ h0 d hDh (fun _ => Iff.rfl)]


/-- The actual compression over two different weight blocks has the weak
class of the coherent sum of their normalized whole block powers. -/
theorem locWPEquiv_twoBlockFunctions_reference {n k l : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (c : ι → X → ℂ) (d : κ → X → ℂ)
    (hc : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (c i))
    (hd : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (d i))
    (N : Set X) (E : List (Set X))
    (hP : IsInvDomain k (⟨N, E,
      weightedFunctionIdeal (Sum.elim (fun _ => u) (fun _ => v)) (Sum.elim c d),
      weightedCommonMark (Sum.elim (fun _ : ι => u) (fun _ : κ => v))⟩ : MarkedIdeal n X))
    (hB : IsInvDomain l (⟨N, E, twoBlockReference u v c d,
      weightedCommonMark (Sum.elim (fun _ : ι => u) (fun _ : κ => v))⟩ : MarkedIdeal n X)) :
    LocWPEquiv (X := X) ⟨N, E,
      weightedFunctionIdeal (Sum.elim (fun _ => u) (fun _ => v)) (Sum.elim c d),
      weightedCommonMark (Sum.elim (fun _ : ι => u) (fun _ : κ => v))⟩
      ⟨N, E, twoBlockReference u v c d, weightedCommonMark (Sum.elim (fun _ : ι => u) (fun _ : κ => v))⟩ := by
  apply locWPEquiv_of_twoBlockAdaptedPresentations ι κ u v hu hv _ _ hP hB rfl rfl rfl
  intro x hx
  obtain ⟨_, _, _, Φ, _, h0, _⟩ := hP.isWellFormed.isClosedSubmanifold_N.2 x hx
  exact hasTwoBlockAdaptedPresentation_of_functions u v c d hc hd N E x Φ h0


/-- Two independent holomorphic two-block compressions have the same
proper-carrier weak test class when the whole ideal of each matched weight
block agrees. The ordered boundary and literal common mark are retained. -/
theorem locWPEquiv_twoBlockFunctions_of_equal_spans {n k l j : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (c c' : ι → X → ℂ) (d d' : κ → X → ℂ)
    (hc : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (c i))
    (hc' : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (c' i))
    (hd : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (d i))
    (hd' : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (d' i))
    (hC : finiteFunctionIdeal (n := n) c = finiteFunctionIdeal c')
    (hD : finiteFunctionIdeal (n := n) d = finiteFunctionIdeal d')
    (N : Set X) (E : List (Set X))
    (hP : IsInvDomain k (⟨N, E,
      weightedFunctionIdeal (Sum.elim (fun _ => u) (fun _ => v)) (Sum.elim c d),
      weightedCommonMark (Sum.elim (fun _ : ι => u) (fun _ : κ => v))⟩ : MarkedIdeal n X))
    (hQ : IsInvDomain l (⟨N, E,
      weightedFunctionIdeal (Sum.elim (fun _ => u) (fun _ => v)) (Sum.elim c' d'),
      weightedCommonMark (Sum.elim (fun _ : ι => u) (fun _ : κ => v))⟩ : MarkedIdeal n X))
    (hB : IsInvDomain j (⟨N, E, twoBlockReference u v c d,
      weightedCommonMark (Sum.elim (fun _ : ι => u) (fun _ : κ => v))⟩ : MarkedIdeal n X)) :
    LocWPEquiv (X := X) ⟨N, E,
      weightedFunctionIdeal (Sum.elim (fun _ => u) (fun _ => v)) (Sum.elim c d),
      weightedCommonMark (Sum.elim (fun _ : ι => u) (fun _ : κ => v))⟩
      ⟨N, E, weightedFunctionIdeal (Sum.elim (fun _ => u) (fun _ => v)) (Sum.elim c' d'),
        weightedCommonMark (Sum.elim (fun _ : ι => u) (fun _ : κ => v))⟩ := by
  have hRef : twoBlockReference u v c d = twoBlockReference u v c' d' := by
    unfold twoBlockReference
    rw [hC, hD]
  have hB' : IsInvDomain j (⟨N, E, twoBlockReference u v c' d',
      weightedCommonMark (Sum.elim (fun _ : ι => u) (fun _ : κ => v))⟩ : MarkedIdeal n X) := by
    rw [← hRef]
    exact hB
  have hp := locWPEquiv_twoBlockFunctions_reference u v hu hv c d hc hd N E hP hB
  have hq := locWPEquiv_twoBlockFunctions_reference u v hu hv c' d' hc' hd' N E hQ hB'
  rw [← hRef] at hq
  exact hp.trans hq.symm

end Hironaka.HironakaG1NonuniformVertexReduction
