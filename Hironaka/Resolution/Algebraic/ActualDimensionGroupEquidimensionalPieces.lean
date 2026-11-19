import Hironaka.Resolution.Algebraic.ActualDimensionGroupChartDimension
import Hironaka.Resolution.Algebraic.ActualDimensionGroupRegularLocus
import Hironaka.Scheme.ReducedEquidimensional
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure
import Hironaka.Scheme.BlowUp.AffineBlowUp.Basic
import Hironaka.Scheme.Snc.RelativeDimensionConstant
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! The actual clopen dimension-group pieces, with their SAME original chart
maps, as native reduced equidimensional algebraic inputs. The native smooth-
locus relative-dimension condition is derived from actual component geometry.
Source-first proof: `actual-dimension-group-equidimensional-pieces-20261101.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
universe u

namespace Hironaka.Resolution.Algebraic.ActualDimensionGroupEquidimensionalPieces
noncomputable section
open ActualDimensionGroupBlowup ActualDimensionGroupChartDimension
  ActualDimensionGroupRegularLocus

variable (R : Type u) [CommRing R] (k : Type u) [Field k]
  [Algebra k R] [Algebra.FiniteType k R]

include k in
private theorem dimension_exists_nat (d : dimensionIndex R) :
    ∃ n : ℕ, (n : WithBot ℕ∞) = d.val := by
  obtain ⟨q,hq⟩ := d.property
  have : q.val.IsPrime := q.property.isPrime
  obtain ⟨n,hn,_⟩ := Hironaka.Algebra.FunctionFieldDimension.exists_dimension_and_trdeg
    k (R ⧸ q.val) (FractionRing (R ⧸ q.val))
  exact ⟨n,hn.symm.trans hq⟩

/-- The finite dimension is chosen from the actual occurring original component. -/
def dimensionNat (d : dimensionIndex R) : ℕ := Nat.find (dimension_exists_nat R k d)

theorem dimensionNat_spec (d : dimensionIndex R) :
    (dimensionNat R k d : WithBot ℕ∞) = d.val := Nat.find_spec (dimension_exists_nat R k d)

private theorem standardSmooth_away_of_minimal_component_dimension
    [PerfectField k] (s : R) (q : minimalPrimes R) (hs : s ∉ q.val) (n : ℕ)
    (hn : ringKrullDim (R ⧸ q.val) = n)
    [Algebra.IsStandardSmooth k (Localization.Away s)] :
    Algebra.IsStandardSmoothOfRelativeDimension n k (Localization.Away s) := by
  let C := Localization.Away s
  let p : Ideal C := q.val.map (algebraMap R C)
  have : q.val.IsPrime := q.property.isPrime
  have hd : Disjoint (Submonoid.powers s : Set R) (q.val : Set R) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hs
  have : p.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) C q.val q.property.isPrime hd
  have hUnder : p.under R = q.val :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers s) C q.property.isPrime hd
  have hp : p ∈ minimalPrimes C := by
    have hm : p ∈ ((⊥ : Ideal R).map (algebraMap R C)).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map (Submonoid.powers s) C (⊥ : Ideal R)]
      change p.under R ∈ minimalPrimes R
      rw [hUnder]
      exact q.property
    simpa only [Ideal.map_bot] using hm
  have : Nontrivial C := by
    by_contra h
    have : Subsingleton C := not_nontrivial_iff_subsingleton.mp h
    exact (show p ≠ ⊤ from Ideal.IsPrime.ne_top inferInstance) (Subsingleton.elim _ _)
  have : IsLocalization.AtPrime (Localization.AtPrime p) q.val := by
    simpa only [hUnder] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers s) (Localization.AtPrime p) p)
  let e : Localization.AtPrime q.val ≃ₐ[k] Localization.AtPrime p :=
    (IsLocalization.algEquiv q.val.primeCompl
      (Localization.AtPrime q.val) (Localization.AtPrime p)).restrictScalars k
  let eκ : q.val.ResidueField ≃ₐ[k] p.ResidueField := IsLocalRing.ResidueField.mapAlgEquiv e
  obtain ⟨m,hm,htr⟩ := Hironaka.Algebra.FunctionFieldDimension.exists_dimension_and_trdeg
    k (R ⧸ q.val) q.val.ResidueField
  have hmn : m = n := by exact_mod_cast hm.symm.trans hn
  have htrp : Algebra.trdeg k p.ResidueField = n := by
    rw [← eκ.trdeg_eq,htr,hmn]
  have hzero : ringKrullDim (Localization.AtPrime p) = 0 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p,
      (Ideal.height_eq_zero_iff (I := p)).mpr hp]
    rfl
  apply isStandardSmoothOfRelativeDimension_of_ringKrullDim_add_trdeg p n
  rw [hzero,htrp]
  simp

private instance spec_locallyOfFiniteType :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

omit [Algebra.FiniteType k R] in
private theorem localization_structure_relative_dimension (s : R) (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k (Localization.Away s)] :
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  rw [← Spec.map_comp]
  change SmoothOfRelativeDimension n
    (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away s))))
  exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).mpr
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).mpr inferInstance))

/-- Primitive actual component dimensions imply the ENTIRE native smooth-locus condition. -/
theorem affine_smoothLocus_of_component_dimensions [CharZero k] [IsReduced R] (n : ℕ)
    (hdim : ∀ q : minimalPrimes R, ringKrullDim (R ⧸ q.val) = n) :
    SmoothOfRelativeDimension n
      ((Spec.map (CommRingCat.ofHom (algebraMap k R))).smoothLocus.ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  classical
  let f := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let U : (Spec (.of R)).Opens := f.smoothLocus
  have data : ∀ x : U, ∃ s : R,
      s ∉ (show PrimeSpectrum R from x.val).asIdeal ∧
        Algebra.IsStandardSmoothOfRelativeDimension n k (Localization.Away s) := by
    intro x
    let p : PrimeSpectrum R := x.val
    have : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
      (mem_smoothLocus_iff_regular_localization R k p).mp x.property
    have : Algebra.IsSmoothAt k p.asIdeal :=
      Algebra.IsSmoothAt.of_isRegularLocalRing_of_perfectField (k := k) p.asIdeal
    obtain ⟨s,hs,hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth_of_finiteType
      (k := k) p.asIdeal
    obtain ⟨q,hq,hqp⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
    have : Algebra.IsStandardSmooth k (Localization.Away s) := hstd
    exact ⟨s,hs,standardSmooth_away_of_minimal_component_dimension R k s ⟨q,hq⟩
      (fun h => hs (hqp h)) n (hdim ⟨q,hq⟩)⟩
  choose s hs hstd using data
  let m (x : U) := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (s x))))
  have hm (x : U) : SmoothOfRelativeDimension n (m x ≫ f) := by
    have := hstd x
    exact localization_structure_relative_dimension R k (s x) n
  have hrange (x : U) : Set.range (m x) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z,rfl⟩
    have := hm x
    have : Smooth (m x ≫ f) := SmoothOfRelativeDimension.smooth n (m x ≫ f)
    have hpre : (m x) ⁻¹ᵁ U = ⊤ := by
      change (m x) ⁻¹ᵁ f.smoothLocus = ⊤
      rw [Scheme.Hom.preimage_smoothLocus_eq,(m x ≫ f).smoothLocus_eq_top]
    change z ∈ (m x) ⁻¹ᵁ U
    rw [hpre]
    trivial
  let g (x : U) : Spec (.of (Localization.Away (s x))) ⟶ U :=
    IsOpenImmersion.lift U.ι (m x) (hrange x)
  have hg (x : U) : g x ≫ U.ι = m x := IsOpenImmersion.lift_fac _ _ _
  have hoi (x : U) : IsOpenImmersion (g x) := by
    have : IsOpenImmersion (g x ≫ U.ι) := by rw [hg]; dsimp [m]; infer_instance
    exact IsOpenImmersion.of_comp _ U.ι
  have hcov (x : U) : x ∈ (g x).opensRange := by
    have hx : U.ι x ∈ (m x).opensRange := by
      change x.val ∈ (Spec.map
        (CommRingCat.ofHom (algebraMap R (Localization.Away (s x))))).opensRange
      rw [Scheme.Hom.opensRange_localizationAway (R := .of R) (s x)]
      exact hs x
    obtain ⟨z,hz⟩ := hx
    refine ⟨z,U.ι.isOpenEmbedding.injective ?_⟩
    calc
      U.ι (g x z) = m x z := by rw [← Scheme.Hom.comp_apply,hg]
      _ = U.ι x := hz
  let 𝒰 : U.toScheme.AffineOpenCover := {
    I₀ := U
    X x := .of (Localization.Away (s x))
    f x := g x
    idx x := x
    covers x := hcov x
    map_prop := hoi }
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  apply IsZariskiLocalAtSource.of_openCover
    (P := @SmoothOfRelativeDimension n) 𝒰.cover
  change ∀ x : U, SmoothOfRelativeDimension n (g x ≫ (U.ι ≫ f))
  intro x
  rw [← Category.assoc,hg]
  exact hm x

private def separationElement (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) : dimensionSeparationIdeal R :=
  ⟨a.val,(le_iSup (fun e => complementIdeal R (dimensionGroupIdeal R) e) d) a.property⟩

private theorem chart_range_subset_piece (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    Set.range (affineBlowUp.chart (dimensionSeparationIdeal R) (separationElement R d a)) ⊆
      Set.range (dimensionPartOpen R d).ι := by
  rw [Scheme.Opens.range_ι]
  intro x hx
  change x ∈ (affineBlowUp.chart (dimensionSeparationIdeal R) (separationElement R d a)).opensRange at hx
  rw [affineBlowUp.opensRange_chart] at hx
  exact Opens.mem_iSup.mpr ⟨a,hx⟩

/-- The SAME actual native chart, factored through its original clopen dimension piece. -/
def pieceChart (d : dimensionIndex R) (a : complementIdeal R (dimensionGroupIdeal R) d) :
    Spec (.of (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val)) ⟶
      (dimensionPartOpen R d).toScheme :=
  IsOpenImmersion.lift (dimensionPartOpen R d).ι
    (affineBlowUp.chart (dimensionSeparationIdeal R) (separationElement R d a))
    (chart_range_subset_piece R d a)

theorem pieceChart_comp_inclusion (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    pieceChart R d a ≫ (dimensionPartOpen R d).ι =
      affineBlowUp.chart (dimensionSeparationIdeal R) (separationElement R d a) :=
  IsOpenImmersion.lift_fac _ _ _

instance pieceChart_isOpenImmersion (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) : IsOpenImmersion (pieceChart R d a) := by
  have : IsOpenImmersion (pieceChart R d a ≫ (dimensionPartOpen R d).ι) := by
    rw [pieceChart_comp_inclusion]
    exact affineBlowUp.isOpenImmersion_chart (dimensionSeparationIdeal R) (separationElement R d a)
  exact IsOpenImmersion.of_comp _ (dimensionPartOpen R d).ι

private theorem pieceChart_covers (d : dimensionIndex R) (x : (dimensionPartOpen R d).toScheme) :
    ∃ a : complementIdeal R (dimensionGroupIdeal R) d, x ∈ (pieceChart R d a).opensRange := by
  have hx := x.property
  obtain ⟨a,ha⟩ := Opens.mem_iSup.mp hx
  have hchart : (dimensionPartOpen R d).ι x ∈
      (affineBlowUp.chart (dimensionSeparationIdeal R) (separationElement R d a)).opensRange := by
    rw [affineBlowUp.opensRange_chart]
    exact ha
  obtain ⟨y,hy⟩ := hchart
  refine ⟨a,y,(dimensionPartOpen R d).ι.isOpenEmbedding.injective ?_⟩
  exact (congrArg (fun f => f y) (pieceChart_comp_inclusion R d a)).trans hy

/-- An internally constructed native affine chart cover of the SAME original clopen piece. -/
def pieceAffineOpenCover (d : dimensionIndex R) :
    (dimensionPartOpen R d).toScheme.AffineOpenCover where
  I₀ := complementIdeal R (dimensionGroupIdeal R) d
  X a := .of (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val)
  f a := pieceChart R d a
  idx x := (pieceChart_covers R d x).choose
  covers x := (pieceChart_covers R d x).choose_spec

private instance piece_over (d : dimensionIndex R) :
    (dimensionPartOpen R d).toScheme.Over (Spec (.of k)) :=
  ⟨(dimensionPartOpen R d).ι ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R))⟩

private instance piece_finiteType (d : dimensionIndex R) :
    FiniteType ((dimensionPartOpen R d).toScheme ↘ Spec (.of k)) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : IsLocallyNoetherian (affineBlowUp (dimensionSeparationIdeal R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (affineBlowUp.π (dimensionSeparationIdeal R))
  change FiniteType ((dimensionPartOpen R d).ι ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R)))
  infer_instance

private instance piece_isSeparated (d : dimensionIndex R) :
    IsSeparated ((dimensionPartOpen R d).toScheme ↘ Spec (.of k)) := by
  change IsSeparated ((dimensionPartOpen R d).ι ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R)))
  infer_instance

omit [Algebra.FiniteType k R] in
/-- The chart's structure map is literally its original canonical coefficient map. -/
theorem pieceChart_comp_structure (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    pieceChart R d a ≫ ((dimensionPartOpen R d).toScheme ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap k (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val))) := by
  change pieceChart R d a ≫ ((dimensionPartOpen R d).ι ≫
    affineBlowUp.π (dimensionSeparationIdeal R) ≫ _) = _
  rw [← Category.assoc,pieceChart_comp_inclusion]
  dsimp only [separationElement]
  rw [← Category.assoc,affineBlowUp.chart_π,← Spec.map_comp]
  rfl

private theorem smoothLocus_relative_dimension_congr {X Y : Scheme.{u}} (f g : X ⟶ Y)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) (n : ℕ) :
    SmoothOfRelativeDimension n (f.smoothLocus.ι ≫ f) ↔
      SmoothOfRelativeDimension n (g.smoothLocus.ι ≫ g) := by
  subst h
  rfl

/-- Native reduced equidimensionality is DERIVED for the SAME actual clopen piece. -/
theorem piece_isReducedEquidimensional [CharZero k] [IsReduced R] (d : dimensionIndex R) :
    (dimensionPartOpen R d).toScheme.IsReducedEquidimensional k := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  apply Scheme.IsReducedEquidimensional.of_openCover
    (pieceAffineOpenCover R d).openCover (dimensionNat R k d)
  · intro a
    change IsReduced (Spec (.of (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val)))
    have := (dimension_group_chart_equidimensional R k d a).1
    infer_instance
  · change ∀ a : complementIdeal R (dimensionGroupIdeal R) d,
      SmoothOfRelativeDimension (dimensionNat R k d)
        ((pieceChart R d a ≫ ((dimensionPartOpen R d).toScheme ↘ Spec (.of k))).smoothLocus.ι ≫
          (pieceChart R d a ≫ ((dimensionPartOpen R d).toScheme ↘ Spec (.of k))))
    intro a
    let C := affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val
    have : IsReduced C := (dimension_group_chart_equidimensional R k d a).1
    have : Algebra.FiniteType R C :=
      affineBlowUpAlgebra_finiteType R (dimensionSeparationIdeal R) (IsNoetherian.noetherian _) a.val
    have : Algebra.FiniteType k C :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R) inferInstance
    have h := affine_smoothLocus_of_component_dimensions C k (dimensionNat R k d) fun q =>
      ((dimension_group_chart_equidimensional R k d a).2 q).trans (dimensionNat_spec R k d).symm
    exact (smoothLocus_relative_dimension_congr _ _ (pieceChart_comp_structure R k d a)
      (dimensionNat R k d)).mpr h

/-- The original clopen piece with its actual finite-type separated structure map. -/
abbrev pieceAlgScheme (d : dimensionIndex R) : AlgScheme k :=
  AlgScheme.of (k := k) (dimensionPartOpen R d).toScheme

/-- An actual native input object, without any supplied equidimensionality certificate. -/
abbrev pieceReducedEquidimensionalScheme [CharZero k] [IsReduced R] (d : dimensionIndex R) :
    ReducedEquidimensionalScheme k :=
  ⟨pieceAlgScheme R k d,piece_isReducedEquidimensional R k d⟩

/-- This object's map back is the SAME original inclusion into the actual separation blowup. -/
def pieceToBlowup [CharZero k] [IsReduced R] (d : dimensionIndex R) :
    (pieceReducedEquidimensionalScheme R k d).obj.left ⟶
      affineBlowUp (dimensionSeparationIdeal R) := (dimensionPartOpen R d).ι

theorem pieceToBlowup_comp_structure [CharZero k] [IsReduced R] (d : dimensionIndex R) :
    pieceToBlowup R k d ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) =
        (pieceReducedEquidimensionalScheme R k d).obj.hom := rfl

end
end Hironaka.Resolution.Algebraic.ActualDimensionGroupEquidimensionalPieces
