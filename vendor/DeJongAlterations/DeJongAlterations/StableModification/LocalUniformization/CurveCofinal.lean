import DeJongAlterations.StableModification.LocalUniformization.CurveLocal

/-!
# Local rings of strictly semi-stable modifications exhaust a valuation ring

Let `O` be a valuation ring of finite height of a separably closed field `K`, and `C → Spec O` an
integral, quasi-compact, separated, strictly semi-stable relative curve with function field `L`.
Let `W` be a valuation ring of `L` centred on `C` with `W ∩ K = O`. This file proves
(`exists_affine_mem_range`, blueprint `prop:sm-lu-curve-exhaustion`): for every finite set
`F ⊆ W` there is a strictly semi-stable modification `C₁ → C` and an affine open `U ⊆ C₁`
containing the centre of `W` with `F ⊆ Γ(C₁, U) ⊆ W` (inside `L`). In Temkin's words (M.
Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.3, `semi-stable.tex` lines 3076–3078): `∪ 𝒪_{C̄ᵢ, x̄ᵢ} = 𝒪̄` over the strictly
semi-stable modifications.

Temkin derives this from the cofinality of strictly semi-stable modifications among all
modifications (Proposition 4.3.1, applied to graph closures), which is available only for
modifications with finitely many points over closed points with transcendental residue field
(`ERRATA.md` T41). The proof here avoids it:

* the valuations `V` with `V ∩ K = O` in which some `b ∈ F` has a residue transcendental over
  `κ(O)` form a finite set (`Curve.finite_setOf_transcendental_residue`); the claim of
  Proposition 4.3.1 (`exists_mem_gammaSet_of_transcendental`, a variant of
  `LocalUniformization.centreClaim` for an arbitrary valuation with a transcendental residue)
  and T43M's iteration (`LocalUniformization.exists_subset_gammaZeroSet`) give a strictly
  semi-stable modification `C₁` on which all of them are centred at generic points of fibres;
* if `b ∈ F` is not in the local ring `𝒪_{C₁,x₁}` at the centre `x₁` of `W` (integrally closed,
  since strictly semi-stable curves are normal), then
  - if `W` has a transcendental residue, `x₁` is a generic point of its fibre, and a valuation ring
    dominating `𝒪_{C₁,x₁}` not containing `b` (Mathlib, Stacks 090P) contradicts the uniqueness
    of the valuation centred at `x₁` (`ValCurves.IsCentre.eq_of_mem_fibreGenericSet`);
  - otherwise `x₁` is a closed point, and a valuation ring dominating `𝒪_{C₁,x₁}` along which `b`
    has transcendental residue (`Curve.exists_valuationSubring_valuation_aeval_eq_one`) is one of
    the finitely many valuations above, hence centred at a generic point of a fibre: impossible.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
open scoped IntermediateField

universe u

namespace DeJongAlterations.StableModification.LocalUniformization.Curve

open ValCurves RiemannZariskiSpace Curves Blowups Algebra.NodeBlowupChart
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ### Residue transcendence in the two forms -/

section Residue

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A residue transcendental in the sense of the cofinality lemmas gives the
residue-transcendence condition. -/
theorem isResidueTranscendental_of_transcendental {V : ValuationSubring L}
    {t : V.valuation.valuationSubring}
    (ht : Transcendental (ResidueField (V.valuation.comap (algebraMap K L)).valuationSubring)
      (residue V.valuation.valuationSubring t)) :
    IsResidueTranscendental (V.comap (algebraMap K L)) V t := by
  intro p hp hcoef
  have hlift : p ∈ lifts (algebraMap (V.valuation.comap (algebraMap K L)).valuationSubring K) :=
    (lifts_iff_coeff_lifts _).mpr fun n ↦ ⟨⟨p.coeff n, by
      rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
        ValuationSubring.valuation_le_one_iff]
      exact hcoef n⟩, rfl⟩
  obtain ⟨p', hp', -, hp'm⟩ := lifts_and_natDegree_eq_and_monic hlift hp
  have hcoe : ((aeval t p' : V.valuation.valuationSubring) : L) = aeval (t : L) p := by
    rw [← hp', aeval_map_algebraMap]
    exact (aeval_algHom_apply (IsScalarTower.toAlgHom (V.valuation.comap
      (algebraMap K L)).valuationSubring V.valuation.valuationSubring L) t p').symm
  have hres : residue V.valuation.valuationSubring (aeval t p') ≠ 0 := by
    intro h0
    have h1 : aeval (residue V.valuation.valuationSubring t)
        (p'.map (residue (V.valuation.comap (algebraMap K L)).valuationSubring)) = 0 := by
      rw [← h0, aeval_def, eval₂_map, aeval_def, hom_eval₂]
      rfl
    exact (hp'm.map _).ne_zero ((transcendental_iff.mp ht) _ h1)
  have hu := (residue_ne_zero_iff_isUnit _).mp hres
  rw [ValuationSubring.valuation_eq_one_iff, hcoe,
    ← (Valuation.isEquiv_valuation_valuationSubring _).eq_one_iff_eq_one] at hu
  exact hu

end Residue

/-! ### Centres over the closed point -/

section Closed

variable {K : Type u} [Field K] {O : ValuationSubring K}

/-- A point of an `O`-scheme lying over the closed point, with algebraic residue field extension,
is closed. -/
theorem isClosed_of_fiberTrdeg_eq_zero {X : Scheme.{u}} (g : X ⟶ Spec (.of O)) [IsSeparated g]
    {x : X} (hx : g x = closedPoint O) (h0 : fiberTrdeg g x = 0) : IsClosed ({x} : Set X) := by
  have halg : IsAlgebraicAt g x := (isAlgebraicAt_iff_fiberTrdeg_eq_zero g x).mpr h0
  have hT : IsClosed (g ⁻¹' {closedPoint O}) :=
    (isClosed_singleton_closedPoint O).preimage g.continuous
  exact isClosed_singleton_of_isClosed_subtype hT hx
    (isClosed_singleton_preimage_of_isAlgebraicAt g hx halg)

/-- A valuation ring `V` of an `O`-algebra `L` with `V ∩ K = O`, centred at a point `y` of an
`O`-scheme, has its centre over the closed point of `Spec O`. -/
theorem apply_eq_closedPoint_of_isCentre {L : Type u} [Field L] [Algebra K L] {X : Scheme.{u}}
    {η : Spec (.of L) ⟶ X} (q : X ⟶ Spec (.of O))
    (hq : η ≫ q = Spec.map (CommRingCat.ofHom ((algebraMap K L).comp O.subtype)))
    {V : RiemannZariskiSpace L} {y : X} (hy : IsCentre η V y)
    (hV : V.valuationSubring.comap (algebraMap K L) = O) : q y = closedPoint O := by
  refine PrimeSpectrum.ext (Ideal.ext fun o ↦ ?_)
  rw [(hy.ringHom q _ hq o).2]
  change _ ↔ o ∈ maximalIdeal O
  rw [mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hlt hu
    obtain ⟨o', ho'⟩ := isUnit_iff_exists_inv.mp hu
    have h1 : V.valuationSubring.valuation ((algebraMap K L).comp O.subtype o') ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff]
      have : (o' : K) ∈ V.valuationSubring.comap (algebraMap K L) := by rw [hV]; exact o'.2
      exact this
    have h2 : V.valuationSubring.valuation ((algebraMap K L).comp O.subtype o) *
        V.valuationSubring.valuation ((algebraMap K L).comp O.subtype o') = 1 := by
      rw [← map_mul, ← map_mul, ho', map_one, map_one]
    have h3 : V.valuationSubring.valuation ((algebraMap K L).comp O.subtype o) *
        V.valuationSubring.valuation ((algebraMap K L).comp O.subtype o') < 1 :=
      mul_lt_one_of_lt_of_le hlt h1
    rw [h2] at h3
    exact lt_irrefl _ h3
  · intro hnu
    by_cases ho : (o : K) = 0
    · have : o = 0 := Subtype.ext ho
      rw [this, map_zero, map_zero]
      exact zero_lt_one
    have hinv : (o : K)⁻¹ ∉ O := fun h ↦
      hnu (isUnit_iff_exists_inv.mpr ⟨⟨_, h⟩, Subtype.ext (mul_inv_cancel₀ ho)⟩)
    have hinvV : algebraMap K L (o : K)⁻¹ ∉ V.valuationSubring := fun h ↦ hinv (by
      have h' : (o : K)⁻¹ ∈ V.valuationSubring.comap (algebraMap K L) := h
      rwa [hV] at h')
    rw [← ValuationSubring.valuation_le_one_iff, not_le, map_inv₀] at hinvV
    have hpos : 0 < V.valuationSubring.valuation (algebraMap K L (o : K)) := by
      rw [zero_lt_iff]
      simpa using ho
    exact (one_lt_inv₀ hpos).mp hinvV

end Closed

/-! ### The claim of Proposition 4.3.1 for a valuation with a transcendental residue -/

section Claim

variable {K : Type u} [Field K] [IsSepClosed K] {O : ValuationSubring K} [Finite (PrimeSpectrum O)]

/-- **Temkin's claim for a valuation with a transcendental residue** (variant of
`LocalUniformization.centreClaim`, T:2967–3016, with the hypothesis `𝔵 ∈ ⋃ Γ(C')` replaced by the
existence of an element with residue transcendental over the residue field of `𝒪_𝔵 ∩ K`, which
is what its proof uses). Let `C` be an integral separated strictly semi-stable relative curve
over `O` (finite height, `K` separably closed), `f₁ : C₁ → C` a strictly semi-stable
modification and `V` a valuation of `K(C)` centred at a closed point of `C₁`. Then there is a
strictly semi-stable modification `C₂` dominating `C₁` with `V ∈ Γ(C₂)`. -/
theorem exists_mem_gammaSet_of_transcendental {C : Scheme.{u}} [IsIntegral C] [C.IsSeparated]
    (φ : C ⟶ Spec (.of O)) [Flat φ] (hC : IsStrictlySemistable φ ⊤)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) {C₁ : Scheme.{u}} [IsIntegral C₁] (f₁ : C₁ ⟶ C)
    [IsModification f₁] (hss₁ : IsStrictlySemistable (f₁ ≫ φ) ⊤)
    (V : RiemannZariskiSpace C.functionField) {x₁ : C₁} (hcl : IsClosed ({x₁} : Set C₁))
    (hVx : IsCentre (genericLift f₁) V x₁)
    (hres : letI := functionFieldAlgebra φ
      ∃ t : V.valuationSubring.valuation.valuationSubring, Transcendental
        (ResidueField (V.valuationSubring.valuation.comap
          (algebraMap K C.functionField)).valuationSubring)
        (residue V.valuationSubring.valuation.valuationSubring t)) :
    ∃ (C₂ : Scheme.{u}) (_ : IsIntegral C₂) (f₂ : C₂ ⟶ C) (_ : IsModification f₂),
      (∃ g : C₂ ⟶ C₁, g ≫ f₁ = f₂) ∧ IsStrictlySemistable (f₂ ≫ φ) ⊤ ∧
        V ∈ gammaSet (f₂ ≫ φ) (genericLift f₂) := by
  have : DeJong.IsNodalCurve φ := hC.isNodalCurve
  let := functionFieldAlgebra φ
  have hK := genericPt_comp φ
  have htr : Algebra.trdeg K C.functionField ≤ 1 := (trdeg_functionField_eq φ).le.trans hdim
  set vL := V.valuationSubring.valuation
  have hVeq : rzOf vL = V := rzOf_eq V
  rw [← hVeq] at hVx ⊢
  have hq₁ : genericLift f₁ ≫ f₁ ≫ φ =
      Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)) := by
    rw [← Category.assoc, genericLift_comp, hK]
  have hOB := LocalUniformization.le_of_isCentre vL (f₁ ≫ φ) hq₁ hVx
  have hidx := asIdeal_eq_idealOfLE vL (f₁ ≫ φ) hq₁ hVx
  have hx' : x₁ ∈ baseOpen O _ hOB (f₁ ≫ φ) := (mem_baseOpen_iff O _ hOB (f₁ ≫ φ)).mpr hidx.le
  have hxc : baseRestrict O _ hOB (f₁ ≫ φ) ⟨x₁, hx'⟩ = closedPoint _ :=
    (baseRestrict_apply_eq_closedPoint_iff O _ hOB (f₁ ≫ φ) _).mpr (PrimeSpectrum.ext hidx)
  obtain ⟨t, ht⟩ := hres
  -- if the centre is generic in its fibre there is nothing to do
  have hdone : ∀ {C₂ : Scheme.{u}} [IsIntegral C₂] (f₂ : C₂ ⟶ C) [IsModification f₂]
      (g : C₂ ⟶ C₁), g ≫ f₁ = f₂ → IsStrictlySemistable (f₂ ≫ φ) ⊤ → ∀ y₂,
      IsCentre (genericLift f₂) (rzOf vL) y₂ → fiberTrdeg (f₂ ≫ φ) y₂ = 1 →
      ∃ (C₃ : Scheme.{u}) (_ : IsIntegral C₃) (f₃ : C₃ ⟶ C) (_ : IsModification f₃),
        (∃ g : C₃ ⟶ C₁, g ≫ f₁ = f₃) ∧ IsStrictlySemistable (f₃ ≫ φ) ⊤ ∧
          rzOf vL ∈ gammaSet (f₃ ≫ φ) (genericLift f₃) :=
    fun f₂ _ g hg hss₂ y₂ hV₂ hy₂ ↦
      ⟨_, inferInstance, f₂, inferInstance, ⟨g, hg⟩, hss₂, y₂, hy₂, hV₂⟩
  by_cases hgen : fiberTrdeg (f₁ ≫ φ) x₁ = 1
  · exact hdone f₁ (𝟙 _) (Category.id_comp _) hss₁ x₁ hVx hgen
  have h0 : fiberTrdeg (f₁ ≫ φ) x₁ = 0 :=
    Cardinal.eq_zero_of_le_one_of_ne_one (fiberTrdeg_le_one φ hdim f₁ x₁) hgen
  -- the smooth stage, for a smooth chart at a closed point of a strictly semi-stable modification
  have hsmooth : ∀ {C₂ : Scheme.{u}} [IsIntegral C₂] (f₂ : C₂ ⟶ C) [IsModification f₂]
      (g : C₂ ⟶ C₁), g ≫ f₁ = f₂ → IsStrictlySemistable (f₂ ≫ φ) ⊤ → ∀ {y₂ : C₂},
      IsClosed ({y₂} : Set C₂) → IsCentre (genericLift f₂) (rzOf vL) y₂ →
      fiberTrdeg (f₂ ≫ φ) y₂ = 0 → ∀ (hy : y₂ ∈ baseOpen O _ hOB (f₂ ≫ φ)),
      baseRestrict O _ hOB (f₂ ≫ φ) ⟨y₂, hy⟩ = closedPoint _ →
      HasSmoothChart (baseRestrict O _ hOB (f₂ ≫ φ)) ⟨y₂, hy⟩ →
      ∃ (C₃ : Scheme.{u}) (_ : IsIntegral C₃) (f₃ : C₃ ⟶ C) (_ : IsModification f₃),
        (∃ g : C₃ ⟶ C₁, g ≫ f₁ = f₃) ∧ IsStrictlySemistable (f₃ ≫ φ) ⊤ ∧
          rzOf vL ∈ gammaSet (f₃ ≫ φ) (genericLift f₃) := by
    intro C₂ _ f₂ _ g hg hss₂ y₂ hcl₂ hV₂ h0₂ hy hyc hch
    obtain ⟨C₃, _, f₃, _, ⟨g', hg'⟩, hss₃, hV₃⟩ :=
      exists_smoothStep φ hK hdim vL htr ht hOB f₂ hss₂ hcl₂ hV₂ h0₂ hy hyc hch
    exact ⟨C₃, inferInstance, f₃, inferInstance, ⟨g' ≫ g, by rw [Category.assoc, hg, hg']⟩,
      hss₃, hV₃⟩
  -- a chart at `x₁` over `B`
  have hss₁' := isStrictlySemistable_baseRestrict O _ hOB (f₁ ≫ φ) hss₁
  obtain ⟨U, hxU, hcase⟩ := exists_chart hss₁' ⟨x₁, hx'⟩ hxc
  rcases hcase with ⟨e, he, hecomp⟩ | ⟨c, e, he, hecomp⟩
  · exact hsmooth f₁ (𝟙 _) (Category.id_comp _) hss₁ hcl hVx h0 hx' hxc
      (hasSmoothChart_of_etale _ U e hecomp _ hxU)
  have hcoord : ∀ i : Fin 2, coordinate c i ∉ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal →
      HasSmoothChart (baseRestrict O _ hOB (f₁ ≫ φ)) ⟨x₁, hx'⟩ := fun i hi ↦
    hasSmoothChart_of_node (baseRestrict O _ hOB (f₁ ≫ φ)) U.ι c e hecomp ⟨⟨x₁, hx'⟩, hxU⟩ i hi
  by_cases hu : coordinate c 0 ∈ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal
  swap
  · exact hsmooth f₁ (𝟙 _) (Category.id_comp _) hss₁ hcl hVx h0 hx' hxc (hcoord 0 hu)
  by_cases hv : coordinate c 1 ∈ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal
  swap
  · exact hsmooth f₁ (𝟙 _) (Category.id_comp _) hss₁ hcl hVx h0 hx' hxc (hcoord 1 hv)
  -- the origin of a node chart: the node stage, then the smooth stage
  have : Nonempty (baseOpen O _ hOB (f₁ ≫ φ)).toScheme := ⟨⟨x₁, hx'⟩⟩
  have : IsIntegral (baseOpen O _ hOB (f₁ ≫ φ)).toScheme :=
    isIntegral_of_isOpenImmersion (baseOpen O _ hOB (f₁ ≫ φ)).ι
  have : Nonempty U.toScheme := ⟨⟨⟨x₁, hx'⟩, hxU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : IsDomain (U.toScheme.presheaf.stalk ⟨⟨x₁, hx'⟩, hxU⟩) :=
    AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegral (X := U.toScheme)
  have hc : c ≠ 0 := node_param_ne_zero c e ⟨⟨x₁, hx'⟩, hxU⟩ hu hv
  obtain ⟨C₂, _, f₂, _, g, _, hg, hss₂, y₂, hV₂, hgy₂, hy₂, hch⟩ :=
    exists_nodeStep φ hK vL htr ht hOB f₁ hss₁ hcl hVx hx' hxc U hxU hc e hecomp hu hv
  have : IsSeparated (f₂ ≫ φ) := inferInstance
  by_cases hgen₂ : fiberTrdeg (f₂ ≫ φ) y₂ = 1
  · exact hdone f₂ g hg hss₂ y₂ hV₂ hgen₂
  have hdim₁ : fiberTrdeg (f₁ ≫ φ) (genericPoint C₁) ≤ 1 := fiberTrdeg_le_one φ hdim f₁ _
  have hcl₂ : IsClosed ({y₂} : Set C₂) := by
    rcases mem_fibreGenericSet_or_isClosed (φ := f₁ ≫ φ) hdim₁ g (x₁ := y₂)
        (by rw [hgy₂]; exact hcl) with h | h
    · exfalso
      apply hgen₂
      have h' : fiberTrdeg (g ≫ f₁ ≫ φ) y₂ = 1 := h
      rwa [← Category.assoc, hg] at h'
    · exact h
  have h0₂ : fiberTrdeg (f₂ ≫ φ) y₂ = 0 :=
    Cardinal.eq_zero_of_le_one_of_ne_one (fiberTrdeg_le_one φ hdim f₂ y₂) hgen₂
  have hyc : baseRestrict O _ hOB (f₂ ≫ φ) ⟨y₂, hy₂⟩ = closedPoint _ := by
    rw [baseRestrict_apply_eq_closedPoint_iff]
    change (f₂ ≫ φ) y₂ = _
    rw [← hg, Category.assoc, Scheme.Hom.comp_apply, hgy₂]
    exact (baseRestrict_apply_eq_closedPoint_iff O _ hOB (f₁ ≫ φ) _).mp hxc
  exact hsmooth f₂ g hg hss₂ hcl₂ hV₂ h0₂ hy₂ hyc hch

/-- A valuation with a transcendental residue centred at a closed point of a strictly semi-stable
curve lies in `⋃ Γ(C')` (`LocalUniformization.unionGammaSet`). -/
theorem mem_unionGammaSet_of_transcendental {C : Scheme.{u}} [IsIntegral C] [C.IsSeparated]
    (φ : C ⟶ Spec (.of O)) [Flat φ] (hC : IsStrictlySemistable φ ⊤)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (V : RiemannZariskiSpace C.functionField) {x : C}
    (hcl : IsClosed ({x} : Set C)) (hVx : IsCentre (genericPt C) V x)
    (hres : letI := functionFieldAlgebra φ
      ∃ t : V.valuationSubring.valuation.valuationSubring, Transcendental
        (ResidueField (V.valuationSubring.valuation.comap
          (algebraMap K C.functionField)).valuationSubring)
        (residue V.valuationSubring.valuation.valuationSubring t)) :
    V ∈ unionGammaSet φ := by
  have hss : IsStrictlySemistable (𝟙 C ≫ φ) ⊤ := by rwa [Category.id_comp]
  obtain ⟨C₂, _, f₂, _, -, -, hV⟩ := exists_mem_gammaSet_of_transcendental φ hC hdim (𝟙 C) hss V
    hcl (by rwa [genericLift_id]) hres
  exact ⟨C₂, inferInstance, f₂, inferInstance, hV⟩

end Claim

/-- A valuation ring centred at a point of an open `U` contains the sections over `U`. -/
theorem mem_ofOpen_of_extension' {L : Type u} [Field L] {X : Scheme.{u}} {η : Spec (.of L) ⟶ X}
    {V : RiemannZariskiSpace L} {x : X} (h : IsCentre η V x) {U : X.Opens} (hx : x ∈ U) :
    ∃ hU : η ⁻¹ᵁ U = ⊤, V ∈ ofRingHom (sectionsToField η U hU) := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  exact mem_ofOpen_of_extension ψ hψ hx

/-! ### Exhaustion of a valuation ring by local rings of strictly semi-stable modifications -/

section Exhaustion

variable {K : Type u} [Field K] [IsSepClosed K] {O : ValuationSubring K} [Finite (PrimeSpectrum O)]

/-- **Strictly semi-stable affine pieces exhaust a valuation ring** (blueprint
`prop:sm-lu-curve-exhaustion`; Temkin, proof of Proposition 4.3.3, T:3076–3078). Let `C` be an
integral, quasi-compact, separated, strictly semi-stable relative curve over `O` (finite height,
`K` separably closed) with function field `L` finite over `K(b)` for every `b` transcendental
over `K`, and `W ∈ RZ_L(C)` with `W ∩ K = O`. For every finite set `F ⊆ W` there are a strictly
semi-stable modification `f₁ : C₁ → C` and an affine open `U ⊆ C₁` such that `Γ(C₁, U) ⊆ W` and
`F ⊆ Γ(C₁, U)` inside `L`. -/
theorem exists_affine_mem_range {C : Scheme.{u}} [IsIntegral C] [CompactSpace C] [C.IsSeparated]
    (φ : C ⟶ Spec (.of O)) [Flat φ] (hC : IsStrictlySemistable φ ⊤)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    (hfd : letI := functionFieldAlgebra φ
      ∀ b : C.functionField, Transcendental K b → FiniteDimensional K⟮b⟯ C.functionField)
    (W : RiemannZariskiSpace C.functionField) (hW : W ∈ rzSpace C)
    (hWK : letI := functionFieldAlgebra φ
      W.valuationSubring.comap (algebraMap K C.functionField) = O)
    (F : Finset C.functionField) (hF : ∀ b ∈ F, b ∈ W.valuationSubring) :
    ∃ (C₁ : Scheme.{u}) (_ : IsIntegral C₁) (f₁ : C₁ ⟶ C) (_ : IsModification f₁),
      IsStrictlySemistable (f₁ ≫ φ) ⊤ ∧ ∃ (U : C₁.Opens) (_ : IsAffineOpen U)
        (hηU : genericLift f₁ ⁻¹ᵁ U = ⊤),
        W ∈ ofRingHom (sectionsToField (genericLift f₁) U hηU) ∧
        ∀ b ∈ F, b ∈ (sectionsToField (genericLift f₁) U hηU).range := by
  classical
  let := functionFieldAlgebra φ
  have : DeJong.IsNodalCurve φ := hC.isNodalCurve
  have hK := genericPt_comp φ
  -- the residue-transcendence condition for `W`
  let hasTr : Prop := ∃ t ∈ W.valuationSubring, IsResidueTranscendental O W.valuationSubring t
  -- the finitely many valuations to be made centred at generic points of fibres
  let 𝒱₀ : Set (RiemannZariskiSpace C.functionField) := {V | V.valuationSubring.comap (algebraMap K C.functionField) = O ∧
    (∃ b ∈ F, b ∈ V.valuationSubring ∧ IsResidueTranscendental O V.valuationSubring b) ∧
    ∃ x : C, IsClosed ({x} : Set C) ∧ IsCentre (genericPt C) V x}
  let 𝒱₁ : Set (RiemannZariskiSpace C.functionField) :=
    {V | V = W ∧ hasTr ∧ ∃ x : C, IsClosed ({x} : Set C) ∧ IsCentre (genericPt C) V x}
  have hfin₀ : 𝒱₀.Finite := by
    have hsub : 𝒱₀ ⊆ ⋃ b ∈ F, RiemannZariskiSpace.valuationSubring ⁻¹'
        {V' : ValuationSubring C.functionField | V'.comap (algebraMap K C.functionField) = O ∧
          HasTranscendentalResidue (K := K) V' b} := by
      rintro V ⟨hVO, ⟨b, hb, hbV, hVb⟩, -⟩
      refine Set.mem_iUnion₂.mpr ⟨b, hb, hVO, ?_⟩
      rw [← hVO] at hVb
      exact hVb.hasTranscendentalResidue hbV
    refine Set.Finite.subset (Set.Finite.biUnion F.finite_toSet fun b _ ↦ ?_) hsub
    refine Set.Finite.preimage (fun _ _ _ _ h ↦ RiemannZariskiSpace.ext h) ?_
    by_cases hb : Transcendental K b
    · have := hfd b hb
      exact finite_setOf_transcendental_residue O b
    · convert Set.finite_empty
      ext V'
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rintro - ⟨hbV, htr⟩
      exact hb (Valuation.MainUniformization.transcendental_of_transcendental_residue hbV htr)
  have hfin₁ : 𝒱₁.Finite := (Set.finite_singleton W).subset fun V hV ↦ hV.1
  have hsub : ∀ V ∈ 𝒱₀ ∪ 𝒱₁, V ∈ unionGammaSet φ ∧
      ∃ x : C, IsClosed ({x} : Set C) ∧ IsCentre (genericPt C) V x := by
    rintro V (⟨hVO, ⟨b, -, hbV, hVb⟩, x, hx, hVx⟩ | ⟨rfl, ⟨t, htW, hWt⟩, x, hx, hVx⟩)
    · rw [← hVO] at hVb
      exact ⟨mem_unionGammaSet_of_transcendental φ hC hdim V hx hVx
        (hVb.exists_transcendental hbV), x, hx, hVx⟩
    · rw [← hWK] at hWt
      exact ⟨mem_unionGammaSet_of_transcendental φ hC hdim _ hx hVx
        (hWt.exists_transcendental htW), x, hx, hVx⟩
  obtain ⟨C₁, _, f₁, _, hss₁, hΓ⟩ :=
    exists_subset_gammaZeroSet hdim hC (centreClaim φ hC hdim) (hfin₀.union hfin₁) hsub
  refine ⟨C₁, inferInstance, f₁, inferInstance, hss₁, ?_⟩
  -- the centres of `W`
  obtain ⟨x, hWx⟩ := exists_isCentre_of_mem_ofScheme hW
  obtain ⟨x₁, hWx₁, hfx₁⟩ := hWx.exists_of_universallyClosed f₁ (genericLift_comp f₁)
  have : C₁.IsSeparated := isSeparated_of_isSeparated f₁
  have hnormal : IsNormalScheme C₁ := isNormalScheme_of_isStrictlySemistable_spec hss₁
  have hdim₁ : fiberTrdeg (f₁ ≫ φ) (genericPoint C₁) ≤ 1 := fiberTrdeg_le_one φ hdim f₁ _
  let := genericLiftAlgebra f₁
  have hη : functionFieldPoint C₁ C.functionField = genericLift f₁ := functionFieldPoint_genericLiftAlgebra f₁
  have hsurj := (genericLiftAlgebra_bijective f₁).2
  have hq₁ : genericLift f₁ ≫ f₁ ≫ φ =
      Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)) := by
    rw [← Category.assoc, genericLift_comp, hK]
  have hφx : φ x = closedPoint O := apply_eq_closedPoint_of_isCentre φ hK hWx hWK
  -- a transcendental residue from a centre of positive fibre dimension
  have htr_of : ∀ {X : Scheme.{u}} {η : Spec (.of C.functionField) ⟶ X} (q : X ⟶ Spec (.of O)),
      η ≫ q = Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)) →
      ∀ {y : X}, IsCentre η W y → fiberTrdeg q y ≠ 0 → hasTr := by
    intro X η q hq y hWy hy
    have hWy' : IsCentre η (rzOf W.valuationSubring.valuation) y := by rwa [rzOf_eq]
    obtain ⟨t, ht⟩ := exists_transcendental_residue W.valuationSubring.valuation
      (LocalUniformization.le_of_isCentre _ q hq hWy') q hq hWy'
      (asIdeal_eq_idealOfLE _ q hq hWy') hy
    have := isResidueTranscendental_of_transcendental ht
    rw [hWK] at this
    exact ⟨t, (W.valuationSubring.valuation_le_one_iff _).mp t.2, this⟩
  have hWx₁' : IsCentre (functionFieldPoint C₁ C.functionField) W x₁ := hη ▸ hWx₁
  have hWA := le_localSubring_of_isCentre hWx₁'
  have : IsIntegrallyClosed (C₁.presheaf.stalk x₁) := (hnormal x₁).2
  have : IsIntegrallyClosedIn (localSubring C₁ C.functionField x₁).toSubring C.functionField :=
    isIntegrallyClosedIn_localSubring hsurj
  -- every element of `F` lies in the local ring `𝒪_{C₁,x₁}`
  have key : ∀ b ∈ F, b ∈ (localSubring C₁ C.functionField x₁).toSubring := by
    intro b hb
    by_contra hbA
    by_cases hT : hasTr
    · -- `x₁` is a generic point of its fibre
      have hgen : x₁ ∈ fibreGenericSet (f₁ ≫ φ) := by
        by_cases hxcl : IsClosed ({x} : Set C)
        · obtain ⟨ξ, hξ, hWξ⟩ := (hΓ (Or.inr ⟨rfl, hT, x, hxcl, hWx⟩)).1
          rwa [hWξ.unique hWx₁] at hξ
        · have hx1 : x ∈ fibreGenericSet φ := by
            by_contra hn
            exact hxcl (isClosed_of_fiberTrdeg_eq_zero φ hφx
              (Cardinal.eq_zero_of_le_one_of_ne_one (fiberTrdeg_le_one_self φ hdim x) hn))
          obtain ⟨ξ, hξ, hWξ⟩ := gammaSet_subset_gammaSet φ f₁ hdim ⟨x, hx1, hWx⟩
          rwa [hWξ.unique hWx₁] at hξ
      obtain ⟨V, hAV, hbV⟩ := LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn hbA
      have hVx₁ : IsCentre (genericLift f₁) ⟨V⟩ x₁ := hη ▸ isCentre_of_localSubring_le hAV
      have := isDominant_genericLift f₁
      have hWV := hWx₁.eq_of_mem_fibreGenericSet (f₁ ≫ φ) hnormal hdim₁
        (genericLift_residueFieldMap_surjective f₁) hgen hVx₁
      rw [hWV] at hF
      exact hbV (hF b hb)
    · -- `x₁` is a closed point which is not generic in its fibre
      have hx0 : fiberTrdeg φ x = 0 := by
        by_contra h
        exact hT (htr_of φ hK hWx h)
      have hxcl : IsClosed ({x} : Set C) := isClosed_of_fiberTrdeg_eq_zero φ hφx hx0
      have hx₁gen : x₁ ∉ fibreGenericSet (f₁ ≫ φ) := by
        intro h
        rw [mem_fibreGenericSet_iff] at h
        exact hT (htr_of (f₁ ≫ φ) hq₁ hWx₁ (by rw [h]; exact one_ne_zero))
      -- the image of `O` lies in `𝒪_{C₁,x₁}`
      obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU₀, -⟩ :=
        C₁.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₁) isOpen_univ
      have hU₀η : functionFieldPoint C₁ C.functionField ⁻¹ᵁ U₀ = ⊤ :=
        functionFieldPoint_preimage hU₀ (genericPoint_mem_of_mem hxU₀)
      have hOA : ∀ c ∈ O, algebraMap K C.functionField c ∈ (localSubring C₁ C.functionField x₁).toSubring := by
        intro c hc
        have hle := range_sectionsToField_le_of_comp (f₁ ≫ φ) (hη ▸ hq₁) (U := ⊤) (U' := U₀)
          le_top (by simp) hU₀η
        rw [range_sectionsToField_SpecMap_top] at hle
        exact range_sectionsToField_le_localSubring hU₀ hxU₀ hU₀η (hle ⟨⟨c, hc⟩, rfl⟩)
      obtain ⟨hle, hloc⟩ := hWA
      have hdomW : ∀ a : (localSubring C₁ C.functionField x₁).toSubring, a ∈ maximalIdeal _ →
          (a : C.functionField) ∈ W.valuationSubring.nonunits := by
        intro a ha
        by_contra hnu
        rw [ValuationSubring.mem_nonunits_iff, not_lt] at hnu
        have h1 : W.valuationSubring.valuation (a : C.functionField) = 1 :=
          le_antisymm ((W.valuationSubring.valuation_le_one_iff _).mpr (hle a.2)) hnu
        have hu : IsUnit (Subring.inclusion hle a) :=
          (W.valuationSubring.valuation_eq_one_iff ⟨a, hle a.2⟩).mpr h1
        exact (mem_maximalIdeal _).mp ha (hloc.map_nonunit _ hu)
      obtain ⟨V, hAV, hdomV, hbV, hunit⟩ := exists_valuationSubring_valuation_aeval_eq_one
        _ W.valuationSubring hle hdomW (hF b hb) hbA
      have hAV' : localSubring C₁ C.functionField x₁ ≤ V.toLocalSubring := by
        refine ⟨hAV, ⟨fun a ha ↦ ?_⟩⟩
        by_contra hna
        have h1 := hdomV a ((mem_maximalIdeal _).mpr hna)
        rw [ValuationSubring.mem_nonunits_iff] at h1
        have h2 := (V.valuation_eq_one_iff ⟨a, hAV a.2⟩).mp ha
        exact lt_irrefl _ (h2 ▸ h1)
      have hVx₁ : IsCentre (genericLift f₁) ⟨V⟩ x₁ := hη ▸ isCentre_of_localSubring_le hAV'
      -- `V ∩ K = O`
      have hVO : V.comap (algebraMap K C.functionField) = O := by
        ext c
        constructor
        · intro hc
          by_contra hcO
          have hc0 : c ≠ 0 := fun h ↦ hcO (h ▸ O.zero_mem)
          have hinv : c⁻¹ ∈ O := (O.mem_or_inv_mem c).resolve_left hcO
          have hW1 : W.valuationSubring.valuation (algebraMap K C.functionField c⁻¹) < 1 := by
            have h1 : W.valuationSubring.valuation (algebraMap K C.functionField c⁻¹) ≤ 1 := by
              rw [ValuationSubring.valuation_le_one_iff]
              have : c⁻¹ ∈ W.valuationSubring.comap (algebraMap K C.functionField) := by rw [hWK]; exact hinv
              exact this
            refine lt_of_le_of_ne h1 fun h2 ↦ hcO ?_
            have : c ∈ W.valuationSubring.comap (algebraMap K C.functionField) := by
              rw [ValuationSubring.mem_comap, ← ValuationSubring.valuation_le_one_iff]
              rw [map_inv₀, map_inv₀, inv_eq_one] at h2
              exact h2.le
            rwa [hWK] at this
          set a : (localSubring C₁ C.functionField x₁).toSubring := ⟨_, hOA _ hinv⟩
          have ha : a ∈ maximalIdeal _ := by
            rw [mem_maximalIdeal, mem_nonunits_iff]
            intro hu
            have := (hu.map (Subring.inclusion hle))
            rw [ValuationSubring.valuation_eq_one_iff] at this
            exact lt_irrefl _ (this ▸ hW1)
          have hV1 := hdomV a ha
          rw [ValuationSubring.mem_nonunits_iff] at hV1
          have hVc : V.valuation (algebraMap K C.functionField c) ≤ 1 := (V.valuation_le_one_iff _).mpr hc
          have hpos : 0 < V.valuation (algebraMap K C.functionField c) := by
            rw [zero_lt_iff]
            exact (Valuation.ne_zero_iff _).mpr ((_root_.map_ne_zero _).mpr hc0)
          change V.valuation (algebraMap K C.functionField c⁻¹) < 1 at hV1
          rw [map_inv₀, map_inv₀] at hV1
          exact absurd hVc (not_le.mpr ((inv_lt_one₀ hpos).mp hV1))
        · intro hc
          exact hAV (hOA c hc)
      have hVb := isResidueTranscendental_of_valuation_aeval hOA hunit
      have hVx : IsCentre (genericPt C) ⟨V⟩ x := by
        have := hVx₁.comp f₁
        rwa [genericLift_comp, hfx₁] at this
      obtain ⟨ξ, hξ, hVξ⟩ := (hΓ (Or.inl ⟨hVO, ⟨b, hb, hbV, hVb⟩, x, hxcl, hVx⟩)).1
      rw [hVξ.unique hVx₁] at hξ
      exact hx₁gen hξ
  -- one affine open containing `x₁` on which all elements of `F` are sections
  obtain ⟨U, hU, hxU, hFU⟩ := exists_affineOpen_of_mem_localSubring F key
  have hηU : genericLift f₁ ⁻¹ᵁ U = ⊤ := hη ▸ functionFieldPoint_preimage hU
    (genericPoint_mem_of_mem hxU)
  obtain ⟨hηU', hWU⟩ := mem_ofOpen_of_extension' hWx₁ hxU
  refine ⟨U, hU, hηU, ?_, fun b hb ↦ ?_⟩
  · rwa [sectionsToField_congr rfl hηU hηU']
  · rw [sectionsToField_congr hη.symm hηU (functionFieldPoint_preimage hU
      (genericPoint_mem_of_mem hxU))]
    exact hFU b hb

end Exhaustion

end DeJongAlterations.StableModification.LocalUniformization.Curve
