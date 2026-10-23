import DeJongAlterations.StableModification.Blowups.Extension
import DeJongAlterations.StableModification.ValuationRing.HenselSections
import DeJongAlterations.StableModification.DeJong.BaseStepSections

/-!
# Sections of étale schemes over strictly henselian local rings

M. Temkin, *Stable modification of relative curves*, proof of Prop 4.3.1 (T:2972–2975), works
locally at a point `x` of the closed fibre of a curve `C` over a valuation ring `R` with
separably closed fraction field, and extends a blow-up of a neighbourhood of `x` "trivially" to
all of `C`. As recorded in `ERRATA.md` (DJA-T33) this needs the modification locus to be closed
in `C`. The fix uses that `R` is strictly henselian: the locus `Z` is étale over a closed
subscheme `Spec R/J` of `Spec R`, so it splits as `Z₀ ⊔ Z₁` with `Z₀ ≅ Spec R/J` the image of a
section through `x`; after removing `Z₁` from the neighbourhood the locus is `Z₀`, which is closed
in `C` because `Spec R/J` is proper over `R`.

This file provides the algebraic and scheme-theoretic part of that argument
(blueprint `sm-boundary-separation.tex`, `lem:sm-transport-section` and
`lem:sm-transport-locus`).

## Main results

* `henselianLocalRing_of_surjective`: quotients of henselian local rings are henselian.
* `isSepClosed_residueField_of_surjective`: a surjection of local rings identifies the residue
  fields.
* `exists_algHom_residueField_of_etale`: over a local ring with separably closed residue field,
  every prime of an étale algebra lying over the maximal ideal is the kernel of a rational point.
* `exists_section_of_etale`: an étale scheme over a henselian local ring with separably closed
  residue field has a section through every point of the closed fibre.
* `exists_open_isClosed_locus`: the shrinking step of the T33 fix.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.Blowups

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Algebra

/-- **Quotients of henselian local rings are henselian.** If `f : A → B` is a surjective ring
map from a henselian local ring onto a nontrivial ring, then `B` is a henselian local ring. -/
theorem henselianLocalRing_of_surjective {A B : Type*} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Nontrivial B] (f : A →+* B) (hf : Function.Surjective f) :
    HenselianLocalRing B := by
  have : IsLocalRing B := IsLocalRing.of_surjective' f hf
  have : IsLocalHom f := hf.isLocalHom f
  have hm : (maximalIdeal B).comap f = maximalIdeal A := IsLocalRing.maximalIdeal_comap f
  refine ⟨fun p hp b₀ hb₀ hu ↦ ?_⟩
  -- lift the monic polynomial and the approximate root
  have hlift : p ∈ Polynomial.lifts f := (Polynomial.lifts_iff_coeff_lifts p).mpr fun n ↦ hf _
  obtain ⟨P, hPp, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hp
  obtain ⟨a₀, rfl⟩ := hf b₀
  have h₁ : P.eval a₀ ∈ maximalIdeal A := by
    rw [← hm, Ideal.mem_comap, ← Polynomial.eval_map_apply, hPp]
    exact hb₀
  have h₂ : IsUnit (P.derivative.eval a₀) := by
    apply isUnit_of_map_unit f
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hPp]
    exact hu
  obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian P hPm a₀ h₁ h₂
  refine ⟨f a, ?_, ?_⟩
  · rw [Polynomial.IsRoot, ← hPp, Polynomial.eval_map_apply, ha.eq_zero, map_zero]
  · rw [← map_sub]
    rw [← hm] at ha'
    exact ha'

/-- Separable closedness is transported along isomorphisms of fields. -/
theorem isSepClosed_of_bijective {k k' : Type*} [Field k] [Field k'] [IsSepClosed k]
    (f : k →+* k') (hf : Function.Bijective f) : IsSepClosed k' := by
  let := f.toAlgebra
  have : Algebra.IsAlgebraic k k' := ⟨fun x ↦ by
    obtain ⟨y, rfl⟩ := hf.2 x
    exact isAlgebraic_algebraMap y⟩
  exact Algebra.IsAlgebraic.isSepClosed (F := k)

/-- A surjection of local rings identifies their residue fields; in particular it transports
separable closedness of the residue field. -/
theorem isSepClosed_residueField_of_surjective {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [IsSepClosed (ResidueField A)] (f : A →+* B)
    (hf : Function.Surjective f) : IsSepClosed (ResidueField B) := by
  have : IsLocalHom f := hf.isLocalHom f
  refine isSepClosed_of_bijective (ResidueField.map f) ⟨(ResidueField.map f).injective, ?_⟩
  intro y
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨residue A a, ResidueField.map_residue f a⟩

/-- **Rational points of étale algebras over a strictly henselian base.** Let `V` be a local
ring with separably closed residue field and `A` an étale `V`-algebra. Every prime `q` of `A`
lying over the maximal ideal of `V` is the kernel of a `V`-algebra map `A → κ(V)`: the residue
field extension `κ(q)/κ(V)` is finite separable, hence trivial. -/
theorem exists_algHom_residueField_of_etale {V A : Type u} [CommRing V] [IsLocalRing V]
    [IsSepClosed (ResidueField V)] [CommRing A] [Algebra V A] [Algebra.Etale V A]
    (q : Ideal A) [q.IsPrime] (hq : q.comap (algebraMap V A) = maximalIdeal V) :
    ∃ φ : A →ₐ[V] ResidueField V, RingHom.ker φ = q := by
  have : q.LiesOver (maximalIdeal V) := ⟨hq.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal V) q
  have hsep : Algebra.IsSeparable (maximalIdeal V).ResidueField q.ResidueField := inferInstance
  have h₀ := Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal V)
  let f₀ : ResidueField V →+* (maximalIdeal V).ResidueField :=
    algebraMap (V ⧸ maximalIdeal V) _
  let e₀ : ResidueField V ≃+* (maximalIdeal V).ResidueField := RingEquiv.ofBijective f₀ h₀
  have : IsSepClosed (maximalIdeal V).ResidueField := isSepClosed_of_bijective f₀ h₀
  let e : (maximalIdeal V).ResidueField ≃+* q.ResidueField :=
    RingEquiv.ofBijective _ (IsSepClosed.algebraMap_bijective _ _)
  let φ : A →+* ResidueField V :=
    e₀.symm.toRingHom.comp (e.symm.toRingHom.comp (algebraMap A q.ResidueField))
  refine ⟨{ toRingHom := φ, commutes' := fun v ↦ ?_ }, ?_⟩
  · change e₀.symm (e.symm (algebraMap A q.ResidueField (algebraMap V A v))) =
      Ideal.Quotient.mk _ v
    rw [RingEquiv.symm_apply_eq, RingEquiv.symm_apply_eq]
    change algebraMap A q.ResidueField (algebraMap V A v) =
      algebraMap (maximalIdeal V).ResidueField q.ResidueField
        (algebraMap (V ⧸ maximalIdeal V) _ (Ideal.Quotient.mk _ v))
    rw [← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply V (V ⧸ maximalIdeal V) (maximalIdeal V).ResidueField,
      ← IsScalarTower.algebraMap_apply V (maximalIdeal V).ResidueField q.ResidueField,
      ← IsScalarTower.algebraMap_apply V A q.ResidueField]
  · ext a
    change e₀.symm (e.symm (algebraMap A q.ResidueField a)) = 0 ↔ a ∈ q
    rw [map_eq_zero_iff _ e₀.symm.injective, map_eq_zero_iff _ e.symm.injective,
      ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]

end Algebra

section Schemes

/-- **Sections of étale schemes over a strictly henselian local ring.** Let `V` be a henselian
local ring with separably closed residue field and `p : X ⟶ Spec V` étale. Every point `x` of
the closed fibre is the image of the closed point under a section of `p`. -/
theorem exists_section_of_etale {V : Type u} [CommRing V] [HenselianLocalRing V]
    [IsSepClosed (ResidueField V)] {X : Scheme.{u}} (p : X ⟶ Spec (.of V)) [Etale p]
    (x : X) (hx : p x = closedPoint V) :
    ∃ s : Spec (.of V) ⟶ X, s ≫ p = 𝟙 _ ∧ s (closedPoint V) = x := by
  obtain ⟨_, ⟨X', hX', rfl⟩, hxX', -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let φ : CommRingCat.of V ⟶ Γ(X, X') := (Scheme.ΓSpecIso (.of V)).inv ≫ p.appLE ⊤ X' le_top
  have hφ : φ.hom.Etale := by
    have h := HasRingHomProperty.appLE (P := @Etale) p inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨X', hX'⟩ le_top
    exact (RingHom.Etale.respectsIso.cancel_left_isIso _ _).mpr h
  algebraize [φ.hom]
  have : Algebra.Etale V Γ(X, X') := hφ
  have hsq : hX'.fromSpec ≫ p = Spec.map φ := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hX' le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  let q := hX'.primeIdealOf ⟨x, hxX'⟩
  have hqx : hX'.fromSpec q = x := hX'.fromSpec_primeIdealOf _
  have hq : q.asIdeal.comap (algebraMap V Γ(X, X')) = maximalIdeal V := by
    have h : (Spec.map φ) q = closedPoint V := by
      rw [← hsq, Scheme.Hom.comp_apply, hqx, hx]
    exact congrArg PrimeSpectrum.asIdeal h
  obtain ⟨ψ, hψ⟩ := exists_algHom_residueField_of_etale q.asIdeal hq
  obtain ⟨σ, hσ, hσq⟩ := ValuationRing.exists_section_of_isSmoothAt q.asIdeal ψ hψ
  refine ⟨σ ≫ hX'.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, hsq]
    exact hσ
  · rw [Scheme.Hom.comp_apply]
    have : σ (closedPoint V) = q := PrimeSpectrum.ext hσq
    rw [this]
    exact hqx

/-- **The T33 shrinking step** (`ERRATA.md` DJA-T33). Let `A` be a henselian local ring with
separably closed residue field, `g : C ⟶ Spec A` separated, `U ⊆ C` open and `φ : U ⟶ M` an
étale `A`-morphism to an `A`-scheme `q : M ⟶ Spec A`. Let `i : Spec Ā ⟶ M` be a closed
immersion lying over the closed subscheme `Spec Ā ⊆ Spec A` (`A → Ā` surjective), and `x ∈ U` a
point of the closed fibre with `φ x ∈ i(Spec Ā)`. Then there is an open `x ∈ U₀ ⊆ U` such that
the locus `U₀ ∩ φ⁻¹(i(Spec Ā))` is closed in `C`: it is the image of a section of the étale
`φ⁻¹(i(Spec Ā)) ⟶ Spec Ā` through `x`, which is proper over `A`; its only point on the
closed fibre is `x`. -/
theorem exists_open_isClosed_locus {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)] {C : Scheme.{u}} (g : C ⟶ Spec (.of A)) [IsSeparated g]
    (U : C.Opens) {M : Scheme.{u}} (q : M ⟶ Spec (.of A)) (φ : U.toScheme ⟶ M) [Etale φ]
    (hφ : φ ≫ q = U.ι ≫ g) {Ā : Type u} [CommRing Ā] [Algebra A Ā]
    (hĀ : Function.Surjective (algebraMap A Ā)) (i : Spec (.of Ā) ⟶ M) [IsClosedImmersion i]
    (hi : i ≫ q = Spec.map (CommRingCat.ofHom (algebraMap A Ā)))
    (x : C) (hxU : x ∈ U) (hx : g x = closedPoint A) (hxi : φ ⟨x, hxU⟩ ∈ Set.range i) :
    ∃ U₀ : C.Opens, U₀ ≤ U ∧ x ∈ U₀ ∧
      IsClosed ((U₀ : Set C) ∩ U.ι '' (φ ⁻¹' Set.range i)) ∧
      ∀ y ∈ (U₀ : Set C) ∩ U.ι '' (φ ⁻¹' Set.range i), g y = closedPoint A → y = x := by
  classical
  let pZ : pullback i φ ⟶ Spec (.of Ā) := pullback.fst i φ
  let jZ : pullback i φ ⟶ U.toScheme := pullback.snd i φ
  obtain ⟨a, ha⟩ := hxi
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := φ) a
    (⟨x, hxU⟩ : U) ha
  have : Nontrivial Ā := PrimeSpectrum.nontrivial a
  have : IsLocalHom (algebraMap A Ā) := hĀ.isLocalHom _
  have : HenselianLocalRing Ā := henselianLocalRing_of_surjective _ hĀ
  have : IsSepClosed (ResidueField Ā) := isSepClosed_residueField_of_surjective _ hĀ
  -- the point `z` lies over the closed point of `Spec Ā`
  have hz : pZ z = closedPoint Ā := by
    apply PrimeSpectrum.comap_injective_of_surjective (algebraMap A Ā) hĀ
    have h1 : (Spec.map (CommRingCat.ofHom (algebraMap A Ā))) (pZ z) = closedPoint A := by
      rw [← hi, Scheme.Hom.comp_apply]
      change q (i (pullback.fst i φ z)) = _
      rw [hz1, ha, ← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply]
      exact hx
    refine h1.trans (PrimeSpectrum.ext ?_)
    exact (IsLocalRing.maximalIdeal_comap (algebraMap A Ā)).symm
  -- separatedness of `pZ`
  have : IsSeparated (pZ ≫ Spec.map (CommRingCat.ofHom (algebraMap A Ā))) := by
    have h : pZ ≫ Spec.map (CommRingCat.ofHom (algebraMap A Ā)) = jZ ≫ U.ι ≫ g := by
      rw [← hi, ← Category.assoc, pullback.condition, Category.assoc, hφ]
    rw [h]
    infer_instance
  have : IsSeparated pZ := IsSeparated.of_comp pZ (Spec.map (CommRingCat.ofHom (algebraMap A Ā)))
  obtain ⟨s, hs, hsz⟩ := exists_section_of_etale pZ z hz
  have hclopen : IsClopen (Set.range s) := DeJong.isClopen_range_of_comp_eq_id pZ s hs
  have hinj : Function.Injective jZ := jZ.isClosedEmbedding.injective
  -- the bad part of the locus
  let Bad : Set U.toScheme := jZ '' (Set.range s)ᶜ
  have hBad : IsClosed Bad := jZ.isClosedEmbedding.isClosedMap _ hclopen.isOpen.isClosed_compl
  let U₀' : U.toScheme.Opens := ⟨Badᶜ, hBad.isOpen_compl⟩
  have hnotBad : ∀ b, jZ (s b) ∉ Bad := by
    rintro b ⟨z', hz', hzz'⟩
    exact hz' ⟨b, (hinj hzz').symm⟩
  have heq : ((U.ι ''ᵁ U₀' : C.Opens) : Set C) ∩ U.ι '' (φ ⁻¹' Set.range i) =
      Set.range (s ≫ jZ ≫ U.ι) := by
    ext y
    constructor
    · rintro ⟨⟨y', hy', rfl⟩, ⟨y'', ⟨a', ha'⟩, hy''⟩⟩
      have : y'' = y' := U.ι.isOpenEmbedding.injective hy''
      subst this
      obtain ⟨z', hz'1, hz'2⟩ := Scheme.Pullback.exists_preimage_pullback a' y'' ha'
      by_cases hz' : z' ∈ Set.range s
      · obtain ⟨b, rfl⟩ := hz'
        exact ⟨b, by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact congrArg _ hz'2⟩
      · exact absurd ⟨z', hz', hz'2⟩ hy'
    · rintro ⟨b, rfl⟩
      refine ⟨⟨jZ (s b), hnotBad b, rfl⟩, jZ (s b), ⟨pZ (s b), ?_⟩, rfl⟩
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hcomp : (s ≫ jZ ≫ U.ι) ≫ g = Spec.map (CommRingCat.ofHom (algebraMap A Ā)) := by
    rw [Category.assoc, Category.assoc, ← hφ, ← Category.assoc jZ, ← pullback.condition,
      Category.assoc, hi, ← Category.assoc, hs, Category.id_comp]
  refine ⟨U.ι ''ᵁ U₀', ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    rw [← hz2, ← hsz]
    exact hnotBad _
  · rw [heq]
    have : IsProper ((s ≫ jZ ≫ U.ι) ≫ g) := by
      rw [hcomp]
      have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap A Ā))) :=
        IsClosedImmersion.spec_of_surjective _ hĀ
      infer_instance
    exact isClosed_range_of_isProper_comp (s ≫ jZ ≫ U.ι) g
  · rw [heq]
    rintro _ ⟨b, rfl⟩ hb
    have hb' : b = closedPoint Ā := by
      apply PrimeSpectrum.comap_injective_of_surjective (algebraMap A Ā) hĀ
      have h1 : (Spec.map (CommRingCat.ofHom (algebraMap A Ā))) b = closedPoint A := by
        rw [← hcomp, Scheme.Hom.comp_apply]
        exact hb
      refine h1.trans (PrimeSpectrum.ext ?_)
      exact (IsLocalRing.maximalIdeal_comap (algebraMap A Ā)).symm
    rw [hb', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hsz, hz2]
    rfl

end Schemes

end DeJongAlterations.StableModification.Blowups
