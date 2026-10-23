import DeJongAlterations.Geometry.AffineBlowupBirational
import DeJongAlterations.Geometry.AffineBlowupCover
import DeJongAlterations.Modification

/-!
# Affine blow-ups over arbitrary domains

Basic facts on the native affine blow-up `affineBlowup I ⟶ Spec R` (Codex's
`DeJongAlterations.affineBlowup`, the `Proj` of the Rees algebra) which hold without any
Noetherian hypothesis, as needed over the (non-Noetherian) valuation rings of M. Temkin,
*Stable modification of relative curves*, §4.3 (`references/temkin10-stable-modification`,
T:2970–3046), where blow-ups `Bl_{(u,π)}` and `Bl_{(π,T-a)}` of curves over a valuation ring are
used.

## Main results

* `isModification_affineBlowupStructure`: for a domain `R` and a nonzero finitely generated
  ideal `I`, the blow-up is a modification in the sense of de Jong 2.17
  (`lem:sm-blowup-modification-nonnoeth`). Codex's global versions assume a locally Noetherian
  base; here only the affine blow-up is needed.
* `iSup_affineBlowupChartOpen_of_span`: the charts `D₊(gᵢT)` of a generating family `gᵢ` of `I`
  cover the blow-up.
* `affineBlowupStructure_restrict_isIso_of_mul_mem`: if `f ∈ I` is nonzero and every `a ∈ I`
  satisfies `sⁿ a ∈ (f)`, then the blow-up is an isomorphism over `D(s)` (the ideal becomes
  principal there). This identifies the modification locus beyond the vanishing locus of `I`.
* `isIso_morphismRestrict_iSup`: a morphism which is an isomorphism over each of a family of
  opens is an isomorphism over their union.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.Blowups

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section General

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- **Blow-ups of domains are modifications** (`lem:sm-blowup-modification-nonnoeth`): for a
domain `R` and a nonzero finitely generated ideal `I`, the affine blow-up
`affineBlowup I ⟶ Spec R` is proper, birational and has integral source. No Noetherian
hypothesis is needed. -/
theorem isModification_affineBlowupStructure [IsDomain R] (hI : I ≠ ⊥) (hfg : I.FG) :
    IsModification (affineBlowupStructure I) := by
  let : IsIntegral (affineBlowup I) := Geometry.ProjIntegral.isIntegral_affineBlowup I hI
  let : IsProper (affineBlowupStructure I) := affineBlowupStructure_isProper I hfg
  exact { sourceIntegral := inferInstance
          targetIntegral := inferInstance
          birational := affineBlowupStructure_birationalOver I hI }

/-- A homogeneous prime of the Rees algebra containing the degree-one elements `gᵢT` of a
generating family of `I` contains every degree-one element `aT`, `a ∈ I`. -/
theorem reesDegreeOne_mem_of_span {ι : Type*} (g : ι → R) (hg : ∀ i, g i ∈ I)
    (hspan : Ideal.span (Set.range g) = I) (P : Ideal (reesAlgebra I))
    (hP : ∀ i, reesDegreeOne I (g i) (hg i) ∈ P) {a : R} (ha : a ∈ I) :
    reesDegreeOne I a ha ∈ P := by
  have ha' : a ∈ Ideal.span (Set.range g) := hspan ▸ ha
  -- induction on the span, carrying membership in `I` along
  suffices H : ∀ b ∈ Ideal.span (Set.range g), ∀ hb : b ∈ I, reesDegreeOne I b hb ∈ P from
    H a ha' ha
  intro b hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨i, rfl⟩ := hb
    intro _
    exact hP i
  | zero =>
    intro hz
    have h0 : reesDegreeOne I 0 hz = 0 := by
      apply Subtype.ext
      simp [reesDegreeOne]
    rw [h0]
    exact P.zero_mem
  | add b c _ _ hib hic =>
    intro hbc
    have hb : b ∈ I := hspan ▸ (by assumption : b ∈ Ideal.span (Set.range g))
    have hc : c ∈ I := hspan ▸ (by assumption : c ∈ Ideal.span (Set.range g))
    have hadd : reesDegreeOne I (b + c) hbc = reesDegreeOne I b hb + reesDegreeOne I c hc := by
      apply Subtype.ext
      exact (Polynomial.monomial 1).map_add b c
    rw [hadd]
    exact P.add_mem (hib hb) (hic hc)
  | smul r b _ hib =>
    intro hrb
    have hb : b ∈ I := hspan ▸ (by assumption : b ∈ Ideal.span (Set.range g))
    have hmul : reesDegreeOne I (r • b) hrb =
        algebraMap R (reesAlgebra I) r * reesDegreeOne I b hb := by
      apply Subtype.ext
      exact (Polynomial.C_mul_monomial (a := r) (b := b) (n := 1)).symm
    rw [hmul]
    exact P.mul_mem_left _ (hib hb)

/-- **The charts of a generating family cover the blow-up.** If `gᵢ` generate `I`, the basic
opens `D₊(gᵢT)` cover `affineBlowup I`. -/
theorem iSup_affineBlowupChartOpen_of_span {ι : Type*} (g : ι → R) (hg : ∀ i, g i ∈ I)
    (hspan : Ideal.span (Set.range g) = I) :
    (⨆ i, affineBlowupChartOpen I (g i) (hg i)) = ⊤ := by
  apply top_le_iff.mp
  intro x hx
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp ((iSup_affineBlowupChartOpen I).ge hx)
  by_contra hnot
  have hP : ∀ i, reesDegreeOne I (g i) (hg i) ∈ x.asHomogeneousIdeal.toIdeal := by
    intro i
    by_contra h
    exact hnot (Opens.mem_iSup.mpr ⟨i, h⟩)
  exact ha (reesDegreeOne_mem_of_span I g hg hspan x.asHomogeneousIdeal.toIdeal hP a.property)

/-- Two generators: the charts `D₊(gT)` and `D₊(hT)` cover the blow-up of `(g, h)`. -/
theorem affineBlowupChartOpen_sup_of_span_pair (g h : R) (hI : Ideal.span {g, h} = I) :
    affineBlowupChartOpen I g (hI ▸ Ideal.subset_span (Set.mem_insert _ _)) ⊔
      affineBlowupChartOpen I h (hI ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)) = ⊤ := by
  have hg : g ∈ I := hI ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hh : h ∈ I := hI ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have H := iSup_affineBlowupChartOpen_of_span I (fun b : Bool => if b then g else h)
    (fun b => by cases b <;> simp [hg, hh]) (by
      rw [← hI]
      congr 1
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨b, rfl⟩
        cases b <;> simp
      · rintro (rfl | rfl)
        · exact ⟨true, rfl⟩
        · exact ⟨false, rfl⟩)
  rw [← H]
  apply le_antisymm
  · exact sup_le (le_iSup_of_le true (le_of_eq rfl)) (le_iSup_of_le false (le_of_eq rfl))
  · exact iSup_le fun b => by cases b <;> simp

end General

section Principal

/-! ### Isomorphism where the ideal becomes principal -/

variable {R : Type u} [CommRing R] (I : Ideal R) {f : R} (s : R)

/-- If every element of `I` has some `sⁿ`-multiple in `(f)`, the same holds for `Iⁿ` and `fⁿ`. -/
theorem exists_pow_mul_eq_of_mem_pow (hs : ∀ a ∈ I, ∃ (n : ℕ) (r : R), s ^ n * a = r * f)
    (n : ℕ) {c : R} (hc : c ∈ I ^ n) : ∃ (N : ℕ) (r : R), s ^ N * c = r * f ^ n := by
  induction n generalizing c with
  | zero => exact ⟨0, c, by simp⟩
  | succ n ih =>
    rw [pow_succ'] at hc
    refine Submodule.smul_induction_on hc ?_ ?_
    · intro a ha b hb
      obtain ⟨N₁, r₁, h₁⟩ := hs a ha
      obtain ⟨N₂, r₂, h₂⟩ := ih hb
      refine ⟨N₁ + N₂, r₁ * r₂, ?_⟩
      change s ^ (N₁ + N₂) * (a * b) = r₁ * r₂ * f ^ (n + 1)
      calc s ^ (N₁ + N₂) * (a * b) = (s ^ N₁ * a) * (s ^ N₂ * b) := by ring
        _ = (r₁ * f) * (r₂ * f ^ n) := by rw [h₁, h₂]
        _ = r₁ * r₂ * f ^ (n + 1) := by ring
    · rintro x y ⟨N₁, r₁, h₁⟩ ⟨N₂, r₂, h₂⟩
      refine ⟨N₁ + N₂, s ^ N₂ * r₁ + s ^ N₁ * r₂, ?_⟩
      calc s ^ (N₁ + N₂) * (x + y) = s ^ N₂ * (s ^ N₁ * x) + s ^ N₁ * (s ^ N₂ * y) := by ring
        _ = _ := by rw [h₁, h₂]; ring

/-- If every element of `I` has some `sⁿ`-multiple in `(f)`, then the inverse image of `D(s)`
in the blow-up lies in the chart `D₊(fT)`. -/
theorem affineBlowupStructure_preimage_basicOpen_le_chart (hf : f ∈ I)
    (hs : ∀ a ∈ I, ∃ (n : ℕ) (r : R), s ^ n * a = r * f) :
    affineBlowupStructure I ⁻¹ᵁ PrimeSpectrum.basicOpen s ≤ affineBlowupChartOpen I f hf := by
  rw [affineBlowupStructure_preimage_basicOpen]
  intro x hx
  let P := x.asHomogeneousIdeal.toIdeal
  change algebraMap R (reesAlgebra I) s ∉ P at hx
  change reesDegreeOne I f hf ∉ P
  intro hfT
  apply x.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn p hp
  change p ∈ P
  obtain ⟨N, r, hNr⟩ := exists_pow_mul_eq_of_mem_pow I s hs n (p.2 n)
  have hmul : algebraMap R (reesAlgebra I) s ^ N * p =
      algebraMap R (reesAlgebra I) r * reesDegreeOne I f hf ^ n := by
    apply Subtype.ext
    change C s ^ N * (p : R[X]) = C r * monomial 1 f ^ n
    conv_lhs => rw [(mem_reesGrading_iff I n p).mp hp]
    rw [← C_pow, monomial_pow, one_mul, C_mul_monomial, C_mul_monomial, hNr]
  have hmem : algebraMap R (reesAlgebra I) s ^ N * p ∈ P := by
    rw [hmul]
    exact P.mul_mem_left _ (P.pow_mem_of_mem hfT n hn)
  exact (x.isPrime.mem_or_mem hmem).resolve_left fun h => hx (x.isPrime.mem_of_pow_mem N h)

variable [IsDomain R]

/-- Elements of the chart `R[I/f]` have `sⁿ`-multiples in `R` when `sⁿ I ⊆ (f)`. -/
theorem affineBlowupFractionChart_exists_pow_mul (hf0 : f ≠ 0)
    (hs : ∀ a ∈ I, ∃ (n : ℕ) (r : R), s ^ n * a = r * f)
    (y : affineBlowupFractionChart I f) :
    ∃ (b : R) (m : ℕ), algebraMap R (affineBlowupFractionChart I f) b =
      algebraMap R (affineBlowupFractionChart I f) s ^ m * y := by
  have hf' : algebraMap R (FractionRing R) f ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hf0
  -- the set of elements with an `sⁿ`-multiple in `R`
  let T : Subalgebra R (FractionRing R) :=
    { carrier := {y | ∃ (b : R) (m : ℕ), algebraMap R (FractionRing R) b =
        algebraMap R (FractionRing R) s ^ m * y}
      mul_mem' := by
        rintro y z ⟨b, m, hb⟩ ⟨c, n, hc⟩
        refine ⟨b * c, m + n, ?_⟩
        rw [map_mul, hb, hc]
        ring
      add_mem' := by
        rintro y z ⟨b, m, hb⟩ ⟨c, n, hc⟩
        refine ⟨s ^ n * b + s ^ m * c, m + n, ?_⟩
        rw [map_add, map_mul, map_mul, map_pow, map_pow, hb, hc]
        ring
      algebraMap_mem' := fun r => ⟨r, 0, by simp⟩ }
  have hle : affineBlowupFractionChart I f ≤ T := by
    apply Algebra.adjoin_le
    rintro _ ⟨a, rfl⟩
    obtain ⟨n, r, hnr⟩ := hs a a.2
    refine ⟨r, n, ?_⟩
    change algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) s ^ n *
      (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) f)
    rw [← mul_div_assoc, ← map_pow, ← map_mul, hnr, map_mul, mul_div_cancel_right₀ _ hf']
  obtain ⟨b, m, hb⟩ := hle y.2
  exact ⟨b, m, Subtype.ext (by simpa using hb)⟩

omit [IsDomain R] in
/-- A ring map `R ⟶ B` whose localization at `s` is bijective induces an isomorphism of
spectra over `D(s)`. -/
theorem isIso_specMap_restrict_basicOpen {B : Type u} [CommRing B] (φ : R →+* B)
    (hφ : Function.Bijective (Localization.awayMap φ s)) :
    IsIso ((Spec.map (CommRingCat.ofHom φ)) ∣_ PrimeSpectrum.basicOpen s) := by
  let F := Spec.map (CommRingCat.ofHom φ)
  let eR := basicOpenIsoSpecAway (R := CommRingCat.of R) s
  let eS := basicOpenIsoSpecAway (R := CommRingCat.of B) (φ s)
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen s
  let V : (Spec (CommRingCat.of B)).Opens := PrimeSpectrum.basicOpen (φ s)
  let q := Spec.map (CommRingCat.ofHom (R := Localization.Away s)
    (S := Localization.Away (φ s)) (Localization.awayMap φ s))
  have : IsIso q := by
    change IsIso (Spec.map (RingEquiv.ofBijective _ hφ).toCommRingCatIso.hom)
    infer_instance
  have hR : eR.inv ≫ U.ι =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) := by
    rw [Iso.inv_comp_eq]
    exact (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R) s).symm
  have hS : eS.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ s)))) = V.ι :=
    basicOpenIsoSpecAway_hom_SpecMap _
  have hcomm :
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ s)))) ≫ F =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) := by
    dsimp only [q, F]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a : 2
    simp [Localization.awayMap, IsLocalization.Away.map]
  have hpre : F ⁻¹ᵁ U = V := by
    dsimp only [F, U, V]
    exact SpecMap_preimage_basicOpen _ _
  have heq : F ∣_ U = (Scheme.isoOfEq _ hpre).hom ≫ eS.hom ≫ q ≫ eR.inv := by
    apply (cancel_mono U.ι).mp
    rw [morphismRestrict_ι]
    have h' := congrArg (fun k => eS.hom ≫ k) hcomm
    rw [← Category.assoc, hS] at h'
    simp only [Category.assoc, hR]
    change (F ⁻¹ᵁ U).ι ≫ F = (Scheme.isoOfEq _ hpre).hom ≫ eS.hom ≫ q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s)))
    rw [← h', ← Category.assoc, Scheme.isoOfEq_hom_ι]
  change IsIso (F ∣_ U)
  rw [heq]
  infer_instance

/-- **The blow-up is an isomorphism where the ideal becomes principal.** Let `R` be a domain,
`f ∈ I` nonzero and `s ∈ R` such that every `a ∈ I` has `sⁿ a ∈ (f)` for some `n`. Then the
blow-up `affineBlowup I ⟶ Spec R` is an isomorphism over `D(s)`. -/
theorem affineBlowupStructure_restrict_isIso_of_mul_mem (hf : f ∈ I) (hf0 : f ≠ 0)
    (hs : ∀ a ∈ I, ∃ (n : ℕ) (r : R), s ^ n * a = r * f) :
    IsIso (affineBlowupStructure I ∣_ PrimeSpectrum.basicOpen s) := by
  let i := affineBlowupChartInclusion I f hf hf0
  let π := affineBlowupStructure I
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen s
  have hV : π ⁻¹ᵁ U ≤ i.opensRange := by
    rw [affineBlowupChartInclusion_opensRange]
    exact affineBlowupStructure_preimage_basicOpen_le_chart I s hf hs
  have : IsIso (i ∣_ π ⁻¹ᵁ U) := isIso_morphismRestrict_of_le_opensRange i _ hV
  have hbij : Function.Bijective
      (Localization.awayMap (algebraMap R (affineBlowupFractionChart I f)) s) := by
    constructor
    · apply Localization.awayMap_injective_iff.mpr
      intro a ha
      refine ⟨0, ?_⟩
      have ha0 : a = 0 := affineBlowupFractionChart_algebraMap_injective I f
        (by simpa only [map_zero] using ha)
      simp [ha0]
    · apply Localization.awayMap_surjective_iff.mpr
      exact affineBlowupFractionChart_exists_pow_mul I s hf0 hs
  have : IsIso ((i ≫ π) ∣_ U) := by
    dsimp only [i, π, U]
    rw [affineBlowupChartInclusion_structure]
    exact isIso_specMap_restrict_basicOpen s _ hbij
  have : IsIso ((i ∣_ π ⁻¹ᵁ U) ≫ π ∣_ U) := by
    rw [← morphismRestrict_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (f := i ∣_ π ⁻¹ᵁ U) (π ∣_ U)

end Principal

section Union

variable {X Y : Scheme.{u}}

/-- A morphism which is an isomorphism over each member of a family of opens is an isomorphism
over their union. -/
theorem isIso_morphismRestrict_iSup (f : X ⟶ Y) {ι : Type*} (U : ι → Y.Opens)
    (hU : ∀ i, IsIso (f ∣_ U i)) : IsIso (f ∣_ ⨆ i, U i) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
  refine ⟨(⨆ i, U i).ι ⁻¹ᵁ U i, hi, ?_⟩
  have := hU i
  exact isIso_morphismRestrict_restrict_of_le f _ (U i) (le_iSup U i)

/-- Binary version of `isIso_morphismRestrict_iSup`. -/
theorem isIso_morphismRestrict_sup (f : X ⟶ Y) (U V : Y.Opens) [IsIso (f ∣_ U)]
    [IsIso (f ∣_ V)] : IsIso (f ∣_ (U ⊔ V)) := by
  have h := isIso_morphismRestrict_iSup f (fun b : Bool => if b then U else V)
    (fun b => by cases b <;> simpa)
  have hUV : (⨆ b : Bool, if b then U else V) = U ⊔ V := by
    apply le_antisymm
    · exact iSup_le fun b => by cases b <;> simp
    · exact sup_le (le_iSup_of_le true (le_of_eq rfl)) (le_iSup_of_le false (le_of_eq rfl))
  rw [hUV] at h
  exact h

end Union

end DeJongAlterations.StableModification.Blowups
