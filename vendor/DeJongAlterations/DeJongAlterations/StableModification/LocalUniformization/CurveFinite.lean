import DeJongAlterations.StableModification.Valuation.MainUniformizationHeight
import DeJongAlterations.StableModification.Valuation.MainUniformizationBasic
import DeJongAlterations.StableModification.Valuation.FunctionField.Places

/-!
# Finitely many valuations with a given transcendental residue

Let `K ⊆ L` be fields, `R'` a valuation ring of `K`, and `b ∈ L` transcendental over `K` with
`L/K(b)` finite. This file proves that only finitely many valuation rings `V` of `L` with
`V ∩ K = R'` contain `b` with residue transcendental over the residue field of `R'`
(`finite_setOf_transcendental_residue`). It is the finiteness input of our proof of M. Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Proposition 4.3.3
(`locunifprop`, `semi-stable.tex` lines 3048–3081): the valuations which have to be made centred
at generic points of fibres before an element `b` becomes regular at the centre of a given
valuation form a finite set.

## Main results

* `comap_adjoin_eq_of_transcendental` (**the Gauss valuation is unique**): all such `V` have the
  same trace on `K(b)` (the Gauss lemma `MainUniformization.exists_coeff_valuation_aeval_eq`).
* `eq_of_le_of_comap_eq` (**incomparability**): two valuation rings `V₁ ⊆ V₂` of an algebraic
  extension `L/F` with the same trace on `F` are equal (Abhyankar's inequality for the residue
  extension and `ringKrullDim_le_trdeg`).
* `card_le_finrank_of_comap_eq` (**at most `[L : F]` extensions**): approximation for
  incomparable valuation rings and linear independence of the approximating elements.
* `finite_setOf_transcendental_residue`.

Blueprint: `lem:sm-lu-curve-gauss-unique`, `lem:sm-lu-curve-extensions-finite`,
`lem:sm-lu-curve-finite-transcendental` (`sm-local-uniformization-curve.tex`).
-/

noncomputable section

open IsLocalRing Polynomial
open scoped IntermediateField

namespace DeJongAlterations.StableModification.LocalUniformization.Curve

open DeJongAlterations.StableModification.Valuation
open Valuation.MainUniformization Valuation.FunctionField

/-! ### Incomparability over an algebraic extension -/

section Incomparable

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- A valuation subring of a field which is a field (as a ring) is the whole field. -/
theorem eq_top_of_isField {E : Type*} [Field E] (D : ValuationSubring E) (hD : IsField D) :
    D = ⊤ := by
  refine top_unique fun x _ ↦ ?_
  by_contra hx
  have hinv : x⁻¹ ∈ D := (D.mem_or_inv_mem x).resolve_left hx
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ D.zero_mem)
  have hne : (⟨x⁻¹, hinv⟩ : D) ≠ 0 := fun h ↦ inv_ne_zero hx0 (congrArg Subtype.val h)
  obtain ⟨y, hy⟩ := hD.mul_inv_cancel hne
  have hyx : (y : E) = x := by
    have h := congrArg Subtype.val hy
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h
    field_simp at h
    exact h
  exact hx (hyx ▸ y.2)

/-- **Incomparability** (blueprint `lem:sm-lu-curve-extensions-finite`, first part): if `L/F` is
algebraic and `V₁ ⊆ V₂` are valuation rings of `L` with the same trace on `F`, then `V₁ = V₂`.

Proof: `V₁` is composed of `V₂` and a valuation ring `D` of `κ(V₂)` containing `κ(V₂ ∩ F)`; the
residue extension `κ(V₂)/κ(V₂ ∩ F)` is algebraic (Abhyankar), so `D` has dimension `0`, i.e. `D`
is the whole residue field. -/
theorem eq_of_le_of_comap_eq [Algebra.IsAlgebraic F L] {V₁ V₂ : ValuationSubring L} (h : V₁ ≤ V₂)
    (hc : V₁.comap (algebraMap F L) = V₂.comap (algebraMap F L)) : V₁ = V₂ := by
  set D := decompose V₂ h
  have hK : ∀ x : ResidueField (V₂.comap (algebraMap F L)),
      algebraMap (ResidueField (V₂.comap (algebraMap F L))) (ResidueField V₂) x ∈ D := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    rw [ResidueField.algebraMap_residue]
    refine ⟨algebraMap _ V₂ a, ?_, rfl⟩
    have ha : (a : F) ∈ V₁.comap (algebraMap F L) := by
      rw [hc]
      exact a.2
    exact ha
  have hdim := ringKrullDim_le_trdeg D hK
  have htr' := trdeg_residueField_comap_le (K := F) V₂
  have h0 : Algebra.trdeg F L = 0 := trdeg_eq_zero_iff.mpr inferInstance
  have hle : ringKrullDim D ≤ (0 : ℕ) := by
    refine hdim.trans ?_
    have : Cardinal.toENat (Algebra.trdeg (ResidueField (V₂.comap (algebraMap F L)))
        (ResidueField V₂)) ≤ 0 := by
      have := Cardinal.toENat.monotone' (htr'.trans h0.le)
      simpa using this
    exact_mod_cast this
  have : Ring.KrullDimLE 0 D := Ring.krullDimLE_iff.mpr hle
  have hD : D = ⊤ := eq_top_of_isField D Ring.KrullDimLE.isField_of_isDomain
  exact (decompose_eq_top_iff V₂ h).mp hD

/-- **At most `[L : F]` valuation rings of `L` have a given trace on `F`** (blueprint
`lem:sm-lu-curve-extensions-finite`): for `L/F` finite and a finite set `S` of valuation rings of
`L` all with trace `G` on `F`, `|S| ≤ [L : F]`. The members of `S` are pairwise incomparable
(`eq_of_le_of_comap_eq`); approximating elements `y_O ≡ 1` at `O` and `≡ 0` at the other members
are linearly independent over `F`. -/
theorem card_le_finrank_of_comap_eq [FiniteDimensional F L] (G : ValuationSubring F)
    (S : Finset (ValuationSubring L)) (hS : ∀ O ∈ S, O.comap (algebraMap F L) = G) :
    S.card ≤ Module.finrank F L := by
  classical
  have : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
  -- approximating elements
  have hy : ∀ O : S, ∃ y : L, O.1.valuation (y - 1) < 1 ∧
      ∀ O' ∈ S.erase O.1, O'.valuation y < 1 := by
    intro ⟨O, hO⟩
    refine exists_valuation_sub_one_lt_one O (S.erase O) fun O' hO' ↦ ?_
    obtain ⟨hne, hO'S⟩ := Finset.mem_erase.mp hO'
    have hc : O.comap (algebraMap F L) = O'.comap (algebraMap F L) := by
      rw [hS O hO, hS O' hO'S]
    exact ⟨fun hle ↦ hne (eq_of_le_of_comap_eq hle hc).symm,
      fun hle ↦ hne (eq_of_le_of_comap_eq hle hc.symm)⟩
  choose y hy1 hyS using hy
  have hli : LinearIndependent F y := by
    rw [linearIndependent_iff']
    intro t g hsum i hi
    by_contra hgi
    set t' := t.filter (fun k ↦ g k ≠ 0) with ht'
    have hit' : i ∈ t' := Finset.mem_filter.mpr ⟨hi, hgi⟩
    obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image t' (fun k ↦ G.valuation (g k)) ⟨i, hit'⟩
    obtain ⟨hkt, hgk⟩ := Finset.mem_filter.mp hk
    have hOk := hS k.1 k.2
    set d : S → F := fun j ↦ g j / g k with hd
    have hdk : d k = 1 := by simp [hd, div_self hgk]
    have hdG : ∀ j ∈ t, d j ∈ G := by
      intro j hj
      by_cases hgj : g j = 0
      · simp [hd, hgj, G.zero_mem]
      rw [← G.valuation_le_one_iff, hd, map_div₀]
      have hpos : 0 < G.valuation (g k) := by
        rw [zero_lt_iff]
        simpa using hgk
      exact (div_le_one₀ hpos).mpr (hkmax j (Finset.mem_filter.mpr ⟨hj, hgj⟩))
    have hd1 : ∀ j ∈ t, k.1.valuation (algebraMap F L (d j)) ≤ 1 := by
      intro j hj
      rw [ValuationSubring.valuation_le_one_iff]
      have : d j ∈ k.1.comap (algebraMap F L) := by
        rw [hOk]
        exact hdG j hj
      exact this
    have hsumd : ∑ j ∈ t, algebraMap F L (d j) * y j = 0 := by
      have : ∑ j ∈ t, algebraMap F L (d j) * y j =
          (algebraMap F L (g k))⁻¹ * ∑ j ∈ t, g j • y j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hd, map_div₀, Algebra.smul_def]
        ring
      rw [this, hsum, mul_zero]
    have hlt : k.1.valuation (∑ j ∈ t, algebraMap F L (d j) * y j - 1) < 1 := by
      rw [← Finset.add_sum_erase t _ hkt, hdk, map_one, one_mul, add_sub_right_comm]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (hy1 k) ?_)
      refine Valuation.map_sum_lt _ one_ne_zero fun j hj ↦ ?_
      obtain ⟨hjk, hjt⟩ := Finset.mem_erase.mp hj
      rw [map_mul]
      have hyj : k.1.valuation (y j) < 1 :=
        hyS j k.1 (Finset.mem_erase.mpr ⟨fun h ↦ hjk (Subtype.ext h).symm, k.2⟩)
      calc k.1.valuation (algebraMap F L (d j)) * k.1.valuation (y j)
          ≤ 1 * k.1.valuation (y j) := by gcongr; exact hd1 j hjt
        _ < 1 := by rw [one_mul]; exact hyj
    rw [hsumd, zero_sub, Valuation.map_neg, map_one] at hlt
    exact lt_irrefl _ hlt
  have := hli.fintype_card_le_finrank
  simpa using this

end Incomparable

/-! ### The Gauss valuation is unique -/

section Gauss

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Comparisons of values of elements of `K` depend only on the trace `V ∩ K`. -/
theorem valuation_le_iff_of_comap_eq {V₁ V₂ : ValuationSubring L}
    (hc : V₁.comap (algebraMap K L) = V₂.comap (algebraMap K L)) (x x' : K) :
    V₁.valuation (algebraMap K L x) ≤ V₁.valuation (algebraMap K L x') ↔
      V₂.valuation (algebraMap K L x) ≤ V₂.valuation (algebraMap K L x') := by
  by_cases hx' : x' = 0
  · subst hx'
    simp only [map_zero, le_zero_iff, Valuation.zero_iff, FaithfulSMul.algebraMap_eq_zero_iff]
  have key : ∀ V : ValuationSubring L, V.valuation (algebraMap K L x) ≤
      V.valuation (algebraMap K L x') ↔ x / x' ∈ V.comap (algebraMap K L) := by
    intro V
    have hpos : 0 < V.valuation (algebraMap K L x') := by
      rw [zero_lt_iff]
      simpa using hx'
    rw [ValuationSubring.mem_comap, ← ValuationSubring.valuation_le_one_iff, map_div₀, map_div₀,
      div_le_one₀ hpos]
  rw [key, key, hc]

/-- The transcendental-residue condition: `b ∈ V` and its residue is transcendental over the
residue field of `V ∩ K`. -/
def HasTranscendentalResidue (V : ValuationSubring L) (b : L) : Prop :=
  ∃ hb : b ∈ V, Transcendental (ResidueField (V.comap (algebraMap K L))) (residue V ⟨b, hb⟩)

omit [Field K] [Algebra K L] in
/-- **The Gauss valuation is unique** (blueprint `lem:sm-lu-curve-gauss-unique`): two valuation
rings of `L` with the same trace on `K` in which `b` has a residue transcendental over the
residue field of that trace have the same trace on `K(b)`. -/
theorem comap_adjoin_eq_of_transcendental {K : Type*} [Field K] [Algebra K L]
    {V₁ V₂ : ValuationSubring L} {b : L}
    (hc : V₁.comap (algebraMap K L) = V₂.comap (algebraMap K L))
    (h₁ : HasTranscendentalResidue (K := K) V₁ b) (h₂ : HasTranscendentalResidue (K := K) V₂ b) :
    V₁.comap (algebraMap K⟮b⟯ L) = V₂.comap (algebraMap K⟮b⟯ L) := by
  -- one inclusion, then symmetry
  have key : ∀ {V₁ V₂ : ValuationSubring L},
      V₁.comap (algebraMap K L) = V₂.comap (algebraMap K L) →
      HasTranscendentalResidue (K := K) V₁ b → HasTranscendentalResidue (K := K) V₂ b →
      V₁.comap (algebraMap K⟮b⟯ L) ≤ V₂.comap (algebraMap K⟮b⟯ L) := by
    intro V₁ V₂ hc ⟨hb₁, ht₁⟩ ⟨hb₂, ht₂⟩ y hy
    rw [ValuationSubring.mem_comap] at hy ⊢
    obtain ⟨r, s, hs, hrs⟩ := exists_eq_div_of_mem_adjoin y.2
    have hy' : algebraMap K⟮b⟯ L y = aeval b r / aeval b s := hrs
    rw [hy'] at hy ⊢
    by_cases hr : r = 0
    · rw [hr, map_zero, zero_div]
      exact V₂.zero_mem
    have hs0 : s ≠ 0 := fun h ↦ hs (by rw [h, map_zero])
    obtain ⟨i, -, hmax₁r, hv₁r⟩ := exists_coeff_valuation_aeval_eq hb₁ ht₁ hr
    obtain ⟨j, -, hmax₁s, hv₁s⟩ := exists_coeff_valuation_aeval_eq hb₁ ht₁ hs0
    obtain ⟨i₂, -, hmax₂r, hv₂r⟩ := exists_coeff_valuation_aeval_eq hb₂ ht₂ hr
    obtain ⟨j₂, -, hmax₂s, hv₂s⟩ := exists_coeff_valuation_aeval_eq hb₂ ht₂ hs0
    have hspos₁ : 0 < V₁.valuation (aeval b s) := by
      rw [zero_lt_iff]
      simpa using hs
    have hspos₂ : 0 < V₂.valuation (aeval b s) := by
      rw [zero_lt_iff]
      simpa using hs
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀, div_le_one₀ hspos₁, hv₁r,
      hv₁s] at hy
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀, div_le_one₀ hspos₂, hv₂r, hv₂s]
    have h1 := (valuation_le_iff_of_comap_eq hc _ _).mp (hmax₁r i₂)
    have h2 := (valuation_le_iff_of_comap_eq hc _ _).mp hy
    exact h1.trans (h2.trans (hmax₂s j))
  exact le_antisymm (key hc h₁ h₂) (key hc.symm h₂ h₁)

/-- **Finitely many valuations with a given transcendental residue** (blueprint
`lem:sm-lu-curve-finite-transcendental`): for `b` transcendental over `K` with `L/K(b)` finite
and a valuation ring `R'` of `K`, only finitely many valuation rings `V` of `L` with
`V ∩ K = R'` contain `b` with residue transcendental over `κ(R')`. -/
theorem finite_setOf_transcendental_residue (R' : ValuationSubring K) (b : L)
    [FiniteDimensional K⟮b⟯ L] :
    {V : ValuationSubring L | V.comap (algebraMap K L) = R' ∧
      HasTranscendentalResidue (K := K) V b}.Finite := by
  classical
  set T := {V : ValuationSubring L | V.comap (algebraMap K L) = R' ∧
      HasTranscendentalResidue (K := K) V b}
  rcases T.eq_empty_or_nonempty with hT | ⟨V₀, hV₀⟩
  · rw [hT]
    exact Set.finite_empty
  have hG : ∀ V ∈ T, V.comap (algebraMap K⟮b⟯ L) = V₀.comap (algebraMap K⟮b⟯ L) :=
    fun V hV ↦ comap_adjoin_eq_of_transcendental (hV.1.trans hV₀.1.symm) hV.2 hV₀.2
  by_contra hinf
  obtain ⟨S, hSsub, hScard⟩ := Set.Infinite.exists_subset_card_eq hinf
    (Module.finrank K⟮b⟯ L + 1)
  have := card_le_finrank_of_comap_eq (V₀.comap (algebraMap K⟮b⟯ L)) S
    fun O hO ↦ hG O (hSsub hO)
  omega

end Gauss

/-! ### Transcendence of residues from units -/

section Residue

/-- **Transcendence of a residue from units**: if `A → B` is a map of local rings compatible with
the residue fields and `p(b)` is a unit for every monic `p ∈ A[X]`, then the residue of `b` is
transcendental over the residue field of `A`. -/
theorem transcendental_residue_of_isUnit_aeval {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra (ResidueField A) (ResidueField B)]
    (hcomp : ∀ a : A, algebraMap (ResidueField A) (ResidueField B) (residue A a) =
      residue B (algebraMap A B a))
    {b : B} (h : ∀ p : A[X], p.Monic → IsUnit (aeval b p)) :
    Transcendental (ResidueField A) (residue B b) := by
  rintro ⟨q, hq0, hq⟩
  have hmon : (q * C q.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hq0
  have hq' : aeval (residue B b) (q * C q.leadingCoeff⁻¹) = 0 := by
    rw [map_mul, hq, zero_mul]
  obtain ⟨p, hp, -, hpm⟩ := lifts_and_natDegree_eq_and_monic
    (map_surjective (residue A) residue_surjective _) hmon
  have hres : residue B (aeval b p) = 0 := by
    rw [← hq', ← hp, aeval_def, aeval_def, eval₂_map, hom_eval₂]
    congr 1
    ext a
    exact (hcomp a).symm
  exact (residue_ne_zero_iff_isUnit _).mpr (h p hpm) hres

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The **residue-transcendence condition** over a valuation ring `R'` of `K`: `p(b)` is a unit of
`V` for every monic `p ∈ K[X]` with coefficients in `R'`. -/
def IsResidueTranscendental (R' : ValuationSubring K) (V : ValuationSubring L) (b : L) : Prop :=
  ∀ p : K[X], p.Monic → (∀ i, p.coeff i ∈ R') → V.valuation (aeval b p) = 1

/-- The residue-transcendence condition gives a residue transcendental over `κ(V ∩ K)`. -/
theorem IsResidueTranscendental.hasTranscendentalResidue {V : ValuationSubring L} {b : L}
    (h : IsResidueTranscendental (V.comap (algebraMap K L)) V b) (hb : b ∈ V) :
    HasTranscendentalResidue (K := K) V b := by
  refine ⟨hb, transcendental_residue_of_isUnit_aeval (fun a ↦ ResidueField.algebraMap_residue a)
    fun p hp ↦ ?_⟩
  rw [V.valuation_eq_one_iff, coe_aeval_comap]
  rw [← aeval_map_algebraMap K]
  exact h _ (hp.map _) fun i ↦ by rw [coeff_map]; exact (p.coeff i).2

/-- The residue-transcendence condition in the form used by the cofinality lemmas of
`LocalUniformization`, for the valuation `V.valuation` and its restriction to `K`. -/
theorem IsResidueTranscendental.exists_transcendental {V : ValuationSubring L} {b : L}
    (h : IsResidueTranscendental (V.comap (algebraMap K L)) V b) (hb : b ∈ V) :
    ∃ t : V.valuation.valuationSubring, Transcendental
      (ResidueField (V.valuation.comap (algebraMap K L)).valuationSubring)
      (residue V.valuation.valuationSubring t) := by
  have hbV : b ∈ V.valuation.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, ValuationSubring.valuation_le_one_iff]
    exact hb
  refine ⟨⟨b, hbV⟩, transcendental_residue_of_isUnit_aeval (fun _ ↦ rfl) fun p hp ↦ ?_⟩
  have hcoe : ((aeval (⟨b, hbV⟩ : V.valuation.valuationSubring) p :
      V.valuation.valuationSubring) : L) = aeval b (p.map (algebraMap (V.valuation.comap (algebraMap K L)).valuationSubring K)) := by
    rw [aeval_map_algebraMap]
    exact (aeval_algHom_apply (IsScalarTower.toAlgHom (V.valuation.comap (algebraMap K L)).valuationSubring
      V.valuation.valuationSubring L)
      ⟨b, hbV⟩ p).symm
  have key : V.valuation (aeval b (p.map (algebraMap (V.valuation.comap (algebraMap K L)).valuationSubring K))) = 1 := by
    refine h _ (hp.map _) fun i ↦ ?_
    rw [coeff_map]
    have := (p.coeff i).2
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      ValuationSubring.valuation_le_one_iff] at this
    exact this
  rw [ValuationSubring.valuation_eq_one_iff, hcoe,
    ← (Valuation.isEquiv_valuation_valuationSubring _).eq_one_iff_eq_one]
  exact key

/-- The residue-transcendence condition from units over a local subring `A ⊆ L` containing the
image of `R'`: if `p(b)` is a unit of `V` for every `p ∈ A[X]` with a coefficient outside `𝔪_A`
(the conclusion of `exists_valuationSubring_valuation_aeval_eq_one`), then `b` satisfies the
residue-transcendence condition over `R'`. -/
theorem isResidueTranscendental_of_valuation_aeval {A : Subring L} [IsLocalRing A]
    {R' : ValuationSubring K} (hR' : ∀ c ∈ R', algebraMap K L c ∈ A) {V : ValuationSubring L}
    {b : L} (h : ∀ p : A[X], p ∉ (maximalIdeal A).map (C : A →+* A[X]) →
      V.valuation (aeval b p) = 1) :
    IsResidueTranscendental R' V b := by
  intro p hp hcoef
  have hlift : p.map (algebraMap K L) ∈ lifts (algebraMap A L) :=
    (lifts_iff_coeff_lifts _).mpr fun n ↦ ⟨⟨_, hR' _ (hcoef n)⟩, by rw [coeff_map]; rfl⟩
  obtain ⟨p', hp', -, hpm'⟩ := lifts_and_natDegree_eq_and_monic hlift (hp.map _)
  have heval : aeval b p' = aeval b p := by
    rw [aeval_def, eval₂_eq_eval_map, hp', aeval_def, eval₂_eq_eval_map]
  rw [← heval]
  refine h p' fun hmem ↦ ?_
  have := Ideal.mem_map_C_iff.mp hmem p'.natDegree
  rw [hpm'.coeff_natDegree] at this
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr this)

end Residue

end DeJongAlterations.StableModification.LocalUniformization.Curve
