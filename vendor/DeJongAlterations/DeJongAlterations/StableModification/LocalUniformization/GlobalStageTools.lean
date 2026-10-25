import DeJongAlterations.StableModification.LocalUniformization.GlobalChartMap
import DeJongAlterations.StableModification.LocalUniformization.ModelStages

/-!
# Tools for the global stages of local uniformization

Auxiliary statements for the global form of M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), Proposition 4.3.1 (T:2967–3016):

* `chartRingHom_algebraMap`: the ring map of an étale chart over the localized base `B` is a
  `B`-algebra map into `L` (the chart compatibility `hιC` of T43M's stages).
* `fiberTrdeg_comp_of_isOpenImmersion`, `fiberTrdeg_of_isOpenImmersion`: open immersions do not
  change residue fields.
* `residue_comap_transcendental`, `residue_comap_isAlgebraic`,
  `exists_transcendental_residue_comap`:
  passing residues between a valuation of `L` and its restriction to a subfield `L₀` with `L/L₀`
  algebraic (Temkin T:2997–2999: "Consider the valued fields `L` and `K` as earlier", here
  `L₀ = K(T)` inside the function field of the curve).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

open ValCurves RiemannZariskiSpace Curves Blowups
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Charts

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O B : ValuationSubring K}
  (hOB : O ≤ B) [Finite (PrimeSpectrum O)]

/-- **The chart ring map is a `B`-algebra map.** Let `η : Spec L → X` with `η ≫ g = Spec (O ⊆ L)`,
`e : U → Spec N` a chart of an open `U ⊆ X_B` over `Spec B`, and `ι : N → L` the ring map of
`η` restricted to `U`, followed by `e`. Then `ι(b) = b` for `b ∈ B ⊆ K ⊆ L`. -/
theorem chartRingHom_algebraMap {X : Scheme.{u}} (g : X ⟶ Spec (.of O)) {η : Spec (.of L) ⟶ X}
    (hη : η ≫ g = Spec.map (CommRingCat.ofHom ((algebraMap K L).comp O.subtype)))
    (U : (baseOpen O B hOB g).toScheme.Opens) {N : Type u} [CommRing N] [Algebra B N]
    (e : U.toScheme ⟶ Spec (.of N))
    (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap B N)) = U.ι ≫ baseRestrict O B hOB g)
    {ηY : Spec (.of L) ⟶ U.toScheme} (hηY : ηY ≫ U.ι ≫ (baseOpen O B hOB g).ι = η) {ι : N →+* L}
    (hι : Spec.map (CommRingCat.ofHom ι) = ηY ≫ e) (r : B) :
    ι (algebraMap B N r) = algebraMap K L r := by
  let := inclusionAlgebra O B hOB
  have hloc := isLocalization_atPrime O B hOB
  have h1 : Spec.map (CommRingCat.ofHom ((ι.comp (algebraMap B N)).comp (algebraMap O B))) =
      Spec.map (CommRingCat.ofHom ((algebraMap K L).comp O.subtype)) := by
    rw [← hη, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, hι,
      Category.assoc, Category.assoc, reassoc_of% he, ← hηY]
    change ηY ≫ U.ι ≫ baseRestrict O B hOB g ≫ specInclusion O B hOB = _
    rw [baseRestrict_comp]
    simp only [Category.assoc]
  have h2 : (ι.comp (algebraMap B N)).comp (algebraMap O B) = (algebraMap K L).comp O.subtype :=
    CommRingCat.hom_ext_iff.mp (Spec.map_injective h1)
  have h3 : ι.comp (algebraMap B N) = (algebraMap K L).comp B.subtype := by
    refine IsLocalization.ringHom_ext (O.idealOfLE B hOB).primeCompl (RingHom.ext fun o ↦ ?_)
    have := congrArg (fun f ↦ f o) h2
    simp only [RingHom.comp_apply] at this ⊢
    exact this
  exact congrArg (fun f ↦ f r) h3

end Charts

section FibreDimension

/-- Open immersions have fibre transcendence degree zero. -/
theorem fiberTrdeg_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    fiberTrdeg f x = 0 :=
  (isAlgebraicAt_iff_fiberTrdeg_eq_zero f x).mp isAlgebraicAt_of_isIso_stalkMap

/-- Precomposing with an open immersion does not change the fibre transcendence degree. -/
theorem fiberTrdeg_comp_of_isOpenImmersion {X Y Z : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (g : Y ⟶ Z) (x : X) : fiberTrdeg (j ≫ g) x = fiberTrdeg g (j x) := by
  rw [fiberTrdeg_comp, fiberTrdeg_of_isOpenImmersion j, add_zero]

/-- Postcomposing with an open immersion does not change the fibre transcendence degree. -/
theorem fiberTrdeg_comp_isOpenImmersion {X Y Z : Scheme.{u}} (g : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j] (x : X) : fiberTrdeg (g ≫ j) x = fiberTrdeg g x := by
  rw [fiberTrdeg_comp, fiberTrdeg_of_isOpenImmersion j, zero_add]

end FibreDimension

section Residues

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {Γ₁ : Type u}
  [LinearOrderedCommGroupWithZero Γ₁] (vL : Valuation L Γ₁)
  {L₀ : Type u} [Field L₀] [Algebra K L₀] [Algebra L₀ L] [IsScalarTower K L₀ L]

local notation "K₀" => Valuation.valuationSubring (Valuation.comap (algebraMap K L) vL)
local notation "V" => Valuation.valuationSubring vL
local notation "V₀" => Valuation.valuationSubring (Valuation.comap (algebraMap L₀ L) vL)

/-- The restriction of `vL` to a subfield `L₀ ⊇ K` extends the restriction to `K`. -/
instance hasExtension_comap_comap :
    (vL.comap (algebraMap K L)).HasExtension (vL.comap (algebraMap L₀ L)) := by
  refine ⟨?_⟩
  have : (vL.comap (algebraMap L₀ L)).comap (algebraMap K L₀) = vL.comap (algebraMap K L) := by
    ext x
    simp [IsScalarTower.algebraMap_apply K L₀ L]
  rw [this]
  exact Valuation.IsEquiv.refl

/-- The residue field maps form a tower `K̃ → L̃₀ → L̃`. -/
instance isScalarTower_residueField :
    IsScalarTower (ResidueField K₀) (ResidueField V₀) (ResidueField V) := by
  refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
  obtain ⟨b, rfl⟩ := residue_surjective c
  change residue V (algebraMap K₀ V b) = residue V (algebraMap V₀ V (algebraMap K₀ V₀ b))
  congr 1
  apply Subtype.ext
  simp [IsScalarTower.algebraMap_apply K L₀ L]

/-- **Transcendence of residues passes from `L₀` to `L`.** -/
theorem residue_comap_transcendental {s : V₀}
    (hs : Transcendental (ResidueField K₀) (residue V₀ s)) :
    Transcendental (ResidueField K₀) (residue V (algebraMap V₀ V s)) := by
  rw [← Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap]
  exact (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective _ _)).mpr hs

/-- **Algebraicity of residues passes from `L` to `L₀`.** -/
theorem residue_comap_isAlgebraic {s : V₀}
    (hs : IsAlgebraic (ResidueField K₀) (residue V (algebraMap V₀ V s))) :
    IsAlgebraic (ResidueField K₀) (residue V₀ s) := by
  rw [← Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap] at hs
  exact (isAlgebraic_algebraMap_iff (FaithfulSMul.algebraMap_injective _ _)).mp hs

/-- **A transcendental residue on `L` gives one on `L₀`** when `L/L₀` is algebraic (Abhyankar's
inequality for `L/L₀`: the residue extension is algebraic). -/
theorem exists_transcendental_residue_comap [Algebra.IsAlgebraic L₀ L] {t : V}
    (ht : Transcendental (ResidueField K₀) (residue V t)) :
    ∃ s : V₀, Transcendental (ResidueField K₀) (residue V₀ s) := by
  by_contra hcon
  push Not at hcon
  have h0 : Algebra.trdeg L₀ L = 0 := trdeg_eq_zero_iff.mpr inferInstance
  have hab := (relRatRank_add_trdeg_le (vL.comap (algebraMap L₀ L)) vL).trans h0.le
  have hres : Algebra.trdeg (ResidueField V₀) (ResidueField V) = 0 :=
    nonpos_iff_eq_zero.mp (le_add_self.trans hab)
  have : Algebra.IsAlgebraic (ResidueField V₀) (ResidueField V) := trdeg_eq_zero_iff.mp hres
  have : Algebra.IsAlgebraic (ResidueField K₀) (ResidueField V₀) := ⟨fun z ↦ by
    obtain ⟨s, rfl⟩ := residue_surjective z
    exact Classical.not_not.mp (hcon s)⟩
  have : Algebra.IsAlgebraic (ResidueField K₀) (ResidueField V) :=
    Algebra.IsAlgebraic.trans (ResidueField K₀) (ResidueField V₀) (ResidueField V)
  exact ht (Algebra.IsAlgebraic.isAlgebraic _)

end Residues

end DeJongAlterations.StableModification.LocalUniformization
