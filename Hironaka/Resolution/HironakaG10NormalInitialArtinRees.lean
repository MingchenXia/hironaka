import Hironaka.Resolution.HironakaRelativeNormalAffineDNCDictionary
import Hironaka.Resolution.HironakaG10ChowUniformArtinRees

/-!
# Uniform Artin--Rees from actual nearby normal initial ideals

The actual neighbourhood-uniform homogeneous initial-ideal producer supplies
one finite original family. Filtered division derives the maximum of its true
homogeneous degrees as an Artin--Rees exponent, using the already proved whole
Krull ideal-closure theorem. The final source theorem assumes only original
coherence and produces one exponent on one neighbourhood containing zero.

The centre is the actual coordinate ideal, and the nearby stalks are translated
along `(a, 0)`. General coherent centres still need the full coherent graph
bridge; this file does not close the general analytic-space uniformity theorem
or the original G10 flattening goal.

Mathematics first: work/hironaka-codex-20261112/G10-INITIAL-DEGREE-MATHEMATICS.md.
Blueprint: `hironaka-g10-normal-initial-artin-rees.tex`.
Source: Hironaka (1975), Lemma 3.2, printed p. 531 (PDF p. 30).
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff BigOperators

namespace Hironaka.HironakaG10NormalInitialArtinRees

noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalAnalyticCoefficients
  HironakaRelativeNormalGraphCentralAnalyticClosure
  HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalDeformationFiniteRelationsSpread
  HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalNearbyPolynomialCoefficientGerms
  HironakaRelativeNormalAffineDNCDictionary HironakaG10ChowUniformArtinRees

/-! The elementary polynomial step uses existing homogeneous-component APIs.
It does not assert a new Noetherian polynomial-ring or Rees-ring result. -/

private theorem homogeneousComponent_mul_right
    {A : Type*} [CommRing A] {σ : Type*}
    {q m : ℕ} {P : MvPolynomial σ A} (hP : P.IsHomogeneous q) (hm : q ≤ m)
    (Q : MvPolynomial σ A) :
    MvPolynomial.homogeneousComponent m (Q * P) =
      MvPolynomial.homogeneousComponent (m-q) Q * P := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | add Q Q' hQ hQ' =>
      simp only [add_mul, map_add, hQ, hQ']
  | monomial β a =>
      rw [MvPolynomial.homogeneousComponent_of_mem
        ((MvPolynomial.isHomogeneous_monomial a rfl).mul hP),
        MvPolynomial.homogeneousComponent_of_mem
          (MvPolynomial.isHomogeneous_monomial a rfl)]
      by_cases he : m = β.degree + q
      · have he' : m-q = β.degree := by omega
        simp only [if_pos he, if_pos he']
      · have he' : m-q ≠ β.degree := by omega
        simp only [if_neg he, if_neg he', zero_mul]

/-! An element of the genuine initial ideal has an actual original germ lift.
This merely exposes the witnesses already supplied by the whole kernel API. -/

private theorem exists_actual_normal_initial_lift (d t q : ℕ)
    (L : Ideal (HolGerm (ComplexModel (d+t))))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hP : P.IsHomogeneous q) (hPL : P ∈ originalNormalInitialIdeal d t L) :
    ∃ g : HolGerm (ComplexModel (d+t)), g ∈ L ∧ g ∈ normalIdeal d t ^ q ∧
      g-normalPolynomialEval d t P ∈ normalIdeal d t ^ (q+1) := by
  let := tangentAlgebra d t
  change normalAssociatedSymbolMap d t L P = 0 at hPL
  have hmem : normalPolynomialEval d t P ∈ L ⊔ normalIdeal d t ^ (q+1) := by
    have h := (normalAssociatedSymbolMap_eq_zero_iff d t L P).mp hPL q
    simpa only [MvPolynomial.homogeneousComponent_eq_self hP] using h
  obtain ⟨a, haq, haP⟩ := exists_original_germ_homogeneous_kernel_relation d t q L P hP hmem
  refine ⟨a.2.val, a.2.property.1, ?_, ?_⟩
  · simpa only [haq] using a.2.property.2
  · have hrem : a.2.val-normalPolynomialEval d t (originalNormalRelation d t L a) ∈
        normalIdeal d t ^ (a.1+1) :=
      originalNormalInitialSymbol_remainder d t a.1 a.2.val a.2.property.2
    simpa only [haq, haP] using hrem

/-- One genuine filtered reduction from bounded actual homogeneous initial
generators. The remainder gains one normal order and stays in the same ideal. -/
theorem normal_filtered_one_step {ι : Type*} [Fintype ι] (d t α : ℕ)
    (L : Ideal (HolGerm (ComplexModel (d+t))))
    (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (q : ι → ℕ)
    (hq : ∀ i, q i ≤ α) (hP : ∀ i, (P i).IsHomogeneous (q i))
    (hspan : originalNormalInitialIdeal d t L = Ideal.span (range P))
    (m : ℕ) (hm : α ≤ m) :
    L ⊓ normalIdeal d t ^ m ≤
      normalIdeal d t ^ (m-α) * (L ⊓ normalIdeal d t ^ α) ⊔
        (L ⊓ normalIdeal d t ^ (m+1)) := by
  classical
  let := tangentAlgebra d t
  let N := normalIdeal d t
  let K := N^(m-α) * (L ⊓ N^α)
  intro f hf
  let S := originalNormalInitialSymbol d t m f hf.2
  have hShom : S.IsHomogeneous m :=
    originalNormalInitialSymbol_homogeneous d t m f hf.2
  have hS : S ∈ originalNormalInitialIdeal d t L :=
    originalNormalRelation_mem_initialIdeal d t L ⟨m, ⟨f, hf.1, hf.2⟩⟩
  rw [hspan] at hS
  obtain ⟨C, hC⟩ := Ideal.mem_span_range_iff_exists_fun.mp hS
  let Q := fun i => MvPolynomial.homogeneousComponent (m-q i) (C i)
  have hQ : ∀ i, (Q i).IsHomogeneous (m-q i) := fun i =>
    MvPolynomial.homogeneousComponent_isHomogeneous _ _
  have hsum : ∑ i, Q i * P i = S := by
    calc
      _ = ∑ i, MvPolynomial.homogeneousComponent m (C i * P i) :=
        Finset.sum_congr rfl fun i _ =>
          (homogeneousComponent_mul_right (hP i) ((hq i).trans hm) (C i)).symm
      _ = MvPolynomial.homogeneousComponent m (∑ i, C i * P i) := by rw [map_sum]
      _ = S := by rw [hC, MvPolynomial.homogeneousComponent_eq_self hShom]
  have hPi : ∀ i, P i ∈ originalNormalInitialIdeal d t L := by
    intro i
    rw [hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  choose g hgL hgN hgr using fun i =>
    exists_actual_normal_initial_lift d t (q i) L (P i) (hP i) (hPi i)
  have hlow : ∀ i, N^(α-q i) * (L ⊓ N^(q i)) ≤ L ⊓ N^α := by
    intro i
    apply Ideal.mul_le.mpr
    intro a ha b hb
    refine ⟨L.mul_mem_left a hb.1, ?_⟩
    change a * b ∈ N^α
    have hab := Ideal.mul_mem_mul ha hb.2
    simpa only [← pow_add, Nat.sub_add_cancel (hq i)] using hab
  have hterm : ∀ i, normalPolynomialEval d t (Q i) * g i ∈ K := by
    intro i
    have hQi : normalPolynomialEval d t (Q i) ∈ N^(m-q i) :=
      normalPolynomialEval_mem_pow_of_homogeneous d t (m-q i) (Q i) (hQ i)
    have hgi : g i ∈ L ⊓ N^(q i) := ⟨hgL i, hgN i⟩
    have he : m-q i = (m-α)+(α-q i) := by have := hq i; omega
    have hle : N^(m-q i) * (L ⊓ N^(q i)) ≤ K := by
      calc
        _ = N^(m-α) * (N^(α-q i) * (L ⊓ N^(q i))) := by
          rw [he, pow_add, mul_assoc]
        _ ≤ K := mul_le_mul' le_rfl (hlow i)
    exact hle (Ideal.mul_mem_mul hQi hgi)
  let c := ∑ i, normalPolynomialEval d t (Q i) * g i
  have hcK : c ∈ K := Ideal.sum_mem _ fun i _ => hterm i
  have hKL : K ≤ L := Ideal.mul_le_right.trans inf_le_left
  have hcL : c ∈ L := hKL hcK
  have hdiff : normalPolynomialEval d t S-c ∈ N^(m+1) := by
    have hterm' : ∀ i, normalPolynomialEval d t (Q i) *
        (normalPolynomialEval d t (P i)-g i) ∈ N^(m+1) := by
      intro i
      have hQi : normalPolynomialEval d t (Q i) ∈ N^(m-q i) :=
        normalPolynomialEval_mem_pow_of_homogeneous d t (m-q i) (Q i) (hQ i)
      have hri : normalPolynomialEval d t (P i)-g i ∈ N^(q i+1) := by
        simpa only [neg_sub] using (N^(q i+1)).neg_mem (hgr i)
      have hh := Ideal.mul_mem_mul hQi hri
      have he : (m-q i)+(q i+1) = m+1 := by have := (hq i).trans hm; omega
      simpa only [← pow_add, he] using hh
    have hh := (N^(m+1)).sum_mem (fun i (_ : i ∈ Finset.univ) => hterm' i)
    have hev : normalPolynomialEval d t S =
        ∑ i, normalPolynomialEval d t (Q i) * normalPolynomialEval d t (P i) := by
      rw [← hsum, map_sum]
      simp only [map_mul]
    simpa only [mul_sub, Finset.sum_sub_distrib, ← hev, c] using hh
  have hrem : f-c ∈ N^(m+1) := by
    have hh := (N^(m+1)).add_mem
      (originalNormalInitialSymbol_remainder d t m f hf.2) hdiff
    simpa only [S, sub_add_sub_cancel] using hh
  change f ∈ K ⊔ (L ⊓ N^(m+1))
  exact Submodule.mem_sup.mpr ⟨c, hcK, f-c, ⟨L.sub_mem hf.1 hcL, hrem⟩,
    by ring⟩

/-- Bounded genuine homogeneous initial generators give that very bound as an
Artin--Rees number. This does not call the existential stalk Artin--Rees lemma. -/
theorem isArtinReesNumber_of_normal_initial_generators {ι : Type*} [Fintype ι]
    (d t α : ℕ) (L : Ideal (HolGerm (ComplexModel (d+t))))
    (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (q : ι → ℕ)
    (hq : ∀ i, q i ≤ α) (hP : ∀ i, (P i).IsHomogeneous (q i))
    (hspan : originalNormalInitialIdeal d t L = Ideal.span (range P)) :
    IsArtinReesNumber L (normalIdeal d t) α := by
  let := isNoetherianRing_holGerm_euclidean (d+t)
  let N := normalIdeal d t
  intro m hm
  let K := N^(m-α) * (L ⊓ N^α)
  have htail : ∀ n, m ≤ n →
      L ⊓ N^n ≤ K ⊔ (L ⊓ N^(n+1)) := by
    intro n hn
    have hh := normal_filtered_one_step d t α L P q hq hP hspan n (hm.trans hn)
    have hpow : N^(n-α) ≤ N^(m-α) :=
      Ideal.pow_le_pow_right (Nat.sub_le_sub_right hn α)
    exact hh.trans (sup_le_sup (mul_le_mul' hpow le_rfl) le_rfl)
  have happrox : ∀ k : ℕ, L ⊓ N^m ≤ K ⊔ (L ⊓ N^(m+k)) := by
    intro k
    induction k with
    | zero => simpa only [Nat.add_zero] using
        (show L ⊓ N^m ≤ K ⊔ (L ⊓ N^m) from le_sup_right)
    | succ k ih =>
        have hh := htail (m+k) (by omega)
        have hh' : K ⊔ (L ⊓ N^(m+k)) ≤ K ⊔ (L ⊓ N^(m+(k+1))) :=
          sup_le le_sup_left (by simpa only [Nat.add_assoc] using hh)
        exact ih.trans hh'
  intro f hf
  apply actual_ideal_mem_of_all_normal_approximations K N (actual_normalIdeal_ne_top d t) f
  intro k
  have hh := happrox k hf
  exact (sup_le_sup le_rfl (inf_le_right.trans
    (Ideal.pow_le_pow_right (by omega : k ≤ m+k)))) hh

/-- Original coherence supplies ONE exponent and ONE neighbourhood containing
the origin for all translated original ideals along the coordinate centre.
No finite family, degree bound, kernel, or Artin--Rees certificate is input. -/
theorem exists_original_coordinate_uniform_artinRees (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ α : ℕ, ∃ B : Set (ComplexModel d), IsOpen B ∧ (0 : ComplexModel d) ∈ B ∧
      ∀ a ∈ B, IsArtinReesNumber
        (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a)))
        (normalIdeal d t) α := by
  classical
  let := tangentAlgebra d t
  obtain ⟨_N, B, hB, h0B, _hcent, _hchain, hc, hmodels⟩ :=
    exists_original_whole_nearby_normal_initial_ideal d t I hI
  let S := actualOriginalRelationFamily d t I
  choose q hq using fun P : ↥S =>
    actualOriginalHomogeneousRelations_homogeneous d t (originalCoherentOriginIdeal I)
      P.val P.property
  let α : ℕ := Finset.univ.sup q
  refine ⟨α, B, hB, h0B, fun a ha => ?_⟩
  let P := fun Q : ↥S => actualNearbyCoefficientPolynomial d t Q.val a (hc a ha Q)
  apply isArtinReesNumber_of_normal_initial_generators d t α
    (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a)))
    P q
  · exact fun Q => Finset.le_sup (Finset.mem_univ Q)
  · exact fun Q => actualNearbyCoefficientPolynomial_homogeneous d t Q.val a
      (hc a ha Q) (hq Q)
  · exact (hmodels a ha).2.2.1.symm

end

end Hironaka.HironakaG10NormalInitialArtinRees
