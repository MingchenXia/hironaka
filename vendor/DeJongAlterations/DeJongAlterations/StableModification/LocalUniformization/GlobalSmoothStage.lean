import DeJongAlterations.StableModification.LocalUniformization.GlobalStageTools
import DeJongAlterations.StableModification.Blowups.SeparationCharts

/-!
# The smooth stage of local uniformization on a global curve

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Proposition
4.3.1, stage 2 (T:2997–3016): if the centre `x` of `𝔵 ∈ 𝔊⁰₀` on a strictly semi-stable curve is
a closed point at which the curve is smooth, a blow-up `Bl_{(π_a, T - a)}` in an étale coordinate
`T` makes the centre the generic point of an exceptional component, i.e. `𝔵 ∈ Γ(C')`.

Here the curve is `C₁ → C → Spec O` (a strictly semi-stable modification of `C`), `𝔵` is a
valuation `vL` of `L = K(C)`, and the étale coordinate is a smooth chart of `X_B = C₁ ×_O B`
(`B = 𝒪_𝔵 ∩ K`, the localization beneath the centre) at the centre `x₁`
(`Blowups.HasSmoothChart`). The valuation theory is T43M's `exists_transcendental_residue_sub`
on the subfield `𝒪L = K(T) ⊆ L` (Temkin's "the same argument as in the first stage shows that we
can actually assume that `C = Spec(A)`"), the centre computation T43M's `smoothBlowup_centre`
and `one_le_fiberTrdeg_smoothBlowupCentre` on `L` itself, and the globalization BND's transport
with the extension of `GlobalTransport`. Blueprint `lem:sm-cofinal-smooth-step`
(`sm-local-uniformization.tex`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

open ValCurves RiemannZariskiSpace Curves Blowups
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [IsSepClosed K] {O : ValuationSubring K} [Finite (PrimeSpectrum O)]
  {C : Scheme.{u}} [IsIntegral C] (φ : C ⟶ Spec (.of O)) [Algebra K C.functionField]
  (hK : genericPt C ≫ φ =
    Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)))
  (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
  {Γ₁ : Type u} [LinearOrderedCommGroupWithZero Γ₁] (vL : Valuation C.functionField Γ₁)

local notation "K₀" => Valuation.valuationSubring
  (Valuation.comap (algebraMap K (Scheme.functionField C)) vL)
local notation "𝒪L" => Valuation.valuationSubring vL

/-- In `K⟮T⟯`, the generator generates. -/
theorem adjoin_gen_eq_top {F E : Type*} [Field F] [Field E] [Algebra F E] (α : E) :
    IntermediateField.adjoin F {IntermediateField.AdjoinSimple.gen F α} = ⊤ := by
  apply IntermediateField.map_injective (IntermediateField.val (IntermediateField.adjoin F {α}))
  rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
    IntermediateField.fieldRange_val]
  rfl

include hK hdim in
/-- **The smooth stage on a global curve** (`lem:sm-cofinal-smooth-step`; Temkin, Proposition
4.3.1, stage 2, T:2997–3016). Let `f₁ : C₁ → C` be a strictly semi-stable modification, `vL`
centred at a closed point `x₁` of `C₁` of fibre dimension zero lying over `𝔭 = 𝔪_{vL} ∩ O`, with
a smooth chart of `X_B` at `x₁`. Then there is a strictly semi-stable modification `C₂ → C`
dominating `C₁` with `vL ∈ Γ(C₂)`. -/
theorem exists_smoothStep (htr : Algebra.trdeg K C.functionField ≤ 1)
    {t : 𝒪L} (ht : Transcendental (ResidueField K₀) (residue 𝒪L t)) (hOB : O ≤ K₀)
    {C₁ : Scheme.{u}} [IsIntegral C₁] (f₁ : C₁ ⟶ C) [IsModification f₁] [IsSeparated (f₁ ≫ φ)]
    (hss₁ : IsStrictlySemistable (f₁ ≫ φ) ⊤) {x₁ : C₁} (hcl : IsClosed ({x₁} : Set C₁))
    (hV : IsCentre (genericLift f₁) (rzOf vL) x₁) (h0 : fiberTrdeg (f₁ ≫ φ) x₁ = 0)
    (hx' : x₁ ∈ baseOpen O K₀ hOB (f₁ ≫ φ))
    (hxc : baseRestrict O K₀ hOB (f₁ ≫ φ) ⟨x₁, hx'⟩ = closedPoint K₀)
    (hch : HasSmoothChart (baseRestrict O K₀ hOB (f₁ ≫ φ)) ⟨x₁, hx'⟩) :
    ∃ (C₂ : Scheme.{u}) (_ : IsIntegral C₂) (f₂ : C₂ ⟶ C) (_ : IsModification f₂),
      (∃ g : C₂ ⟶ C₁, g ≫ f₁ = f₂) ∧ IsStrictlySemistable (f₂ ≫ φ) ⊤ ∧
        rzOf vL ∈ gammaSet (f₂ ≫ φ) (genericLift f₂) := by
  -- the chart as an open of `X_B`
  obtain ⟨Y, ιY, hιY, e, he, ⟨y₀, hy₀⟩, hecomp⟩ := hch
  let U := ιY.opensRange
  let φU : U.toScheme ⟶ Spec (.of K₀[X]) := ιY.isoOpensRange.inv ≫ e
  have : Etale φU := by dsimp only [φU]; infer_instance
  have hφU : φU ≫ smoothModel K₀ = U.ι ≫ baseRestrict O K₀ hOB (f₁ ≫ φ) := by
    rw [Category.assoc, hecomp, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  have hxU : (⟨x₁, hx'⟩ : (baseOpen O K₀ hOB (f₁ ≫ φ)).toScheme) ∈ U := ⟨y₀, hy₀⟩
  let xU : U.toScheme := ⟨⟨x₁, hx'⟩, hxU⟩
  -- the ring map of the chart
  have hq₁ : genericLift f₁ ≫ f₁ ≫ φ =
      Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)) := by
    rw [← Category.assoc, genericLift_comp, hK]
  obtain ⟨ηY, ι, hηY, hι, hιinj, hcenY, hιV⟩ :=
    exists_chartRingHom vL (genericLift_apply f₁) (U.ι ≫ (baseOpen O K₀ hOB (f₁ ≫ φ)).ι) φU
      (y := xU) hV
  have hιC : ∀ r : K₀, ι (Polynomial.C r) = algebraMap K C.functionField r :=
    chartRingHom_algebraMap hOB (f₁ ≫ φ) hq₁ U φU hφU hηY hι
  set T := ι X with hTdef
  have hT : vL T ≤ 1 := (hιV X).1
  -- the residue of `T` is algebraic over `K̃` (the centre is a closed point of its fibre)
  have hcenN : IsCentre (Spec.map (CommRingCat.ofHom ι)) (rzOf vL) (φU xU) := by
    rw [hι]
    exact hcenY.comp φU
  obtain ⟨ψ, hψ, hψy⟩ := hcenN
  have hψq : toSpecValuationSubring (rzOf vL) ≫ ψ ≫ smoothModel K₀ =
      Spec.map (CommRingCat.ofHom
        ((algebraMap K C.functionField).comp (ValuationSubring.subtype K₀))) := by
    rw [← Category.assoc, hψ, smoothModel, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hιC
  have hψx : ψ (closedPoint 𝒪L) = φU xU := hψy
  have hqy : (smoothModel K₀ (ψ (closedPoint 𝒪L))).asIdeal =
      ValuationSubring.idealOfLE K₀ K₀ le_rfl := by
    rw [hψx, ← Scheme.Hom.comp_apply, hφU, Scheme.Hom.comp_apply]
    change (baseRestrict O K₀ hOB (f₁ ≫ φ) ⟨x₁, hx'⟩).asIdeal = _
    rw [hxc]
    rfl
  have halg0 : fiberTrdeg (smoothModel K₀) (ψ (closedPoint 𝒪L)) = 0 := by
    have e1 : fiberTrdeg (U.ι ≫ (baseOpen O K₀ hOB (f₁ ≫ φ)).ι ≫ (f₁ ≫ φ)) xU = 0 := by
      rw [fiberTrdeg_comp_of_isOpenImmersion, fiberTrdeg_comp_of_isOpenImmersion]
      exact h0
    have e2 : U.ι ≫ (baseOpen O K₀ hOB (f₁ ≫ φ)).ι ≫ (f₁ ≫ φ) =
        φU ≫ smoothModel K₀ ≫ specInclusion O K₀ hOB := by
      rw [← baseRestrict_comp, ← Category.assoc, ← hφU, Category.assoc]
    rw [e2, fiberTrdeg_comp, fiberTrdeg_comp_isOpenImmersion] at e1
    rw [hψx]
    exact (add_eq_zero.mp e1).1
  have hTpre : ((Spec.preimage ψ X : 𝒪L) : C.functionField) = T := by
    have h1 : Spec.preimage ψ ≫ CommRingCat.ofHom (algebraMap 𝒪L C.functionField) =
        CommRingCat.ofHom ι := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, ← hψ]
    have := congrArg (fun f ↦ f.hom X) h1
    simpa using this
  have hTmem : T ∈ 𝒪L := (Valuation.mem_valuationSubring_iff vL T).mpr hT
  have halgT : IsAlgebraic (ResidueField K₀) (residue 𝒪L ⟨T, hTmem⟩) := by
    have h := isAlgebraic_residue vL (O' := K₀) le_rfl (smoothModel K₀) ψ hψq hqy halg0
      ((Spec (.of K₀[X])).presheaf.germ ⊤ (ψ (closedPoint 𝒪L)) trivial
        ((Scheme.ΓSpecIso (.of K₀[X])).inv X))
    rw [stalkClosedPointTo_germ] at h
    convert h using 2
    exact Subtype.ext hTpre.symm
  -- the subfield `𝒪L = K(T)`
  let F := IntermediateField.adjoin K {T}
  let T₀ := IntermediateField.AdjoinSimple.gen K T
  let vF := vL.comap (algebraMap F C.functionField)
  have hgen : IntermediateField.adjoin K {T₀} = ⊤ := adjoin_gen_eq_top T
  have hT₀ : vF T₀ ≤ 1 := hT
  -- `T` is transcendental over `K`, so `L/K(T)` is algebraic
  have hιeval' : ι = (aeval T : K[X] →ₐ[K] C.functionField).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap K₀ K)) := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp [hιC]
    · simp [hTdef]
  have hTtr : Transcendental K T := by
    intro ⟨p, hp0, hp⟩
    let q := IsLocalization.integerNormalization (nonZeroDivisors K₀) p
    obtain ⟨b, -, hmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors K₀) p
    have hq : ι q = 0 := by
      rw [hιeval']
      change aeval T (q.map (algebraMap K₀ K)) = 0
      rw [hmap, Algebra.smul_def, map_mul, hp, mul_zero]
    have hq0 : q = 0 := (map_eq_zero_iff ι hιinj).mp hq
    exact hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).mp hq0)
  have hF1 : 1 ≤ Algebra.trdeg K F := by
    have hT₀tr : Transcendental K T₀ := by
      rw [← transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective F C.functionField)]
      exact hTtr
    have h : AlgebraicIndependent K (fun _ : PUnit ↦ T₀) :=
      algebraicIndependent_unique_type_iff.mpr hT₀tr
    simpa using h.cardinalMk_le_trdeg
  have hFL : Algebra.IsAlgebraic F C.functionField := by
    have hadd := trdeg_add_eq K F (A := C.functionField)
    have h1 : 1 + Algebra.trdeg F C.functionField ≤ 1 :=
      (add_le_add_left hF1 _).trans (hadd.le.trans htr)
    exact trdeg_eq_zero_iff.mp (Cardinal.eq_zero_of_one_add_le_one h1)
  obtain ⟨s₁, hs₁⟩ := exists_transcendental_residue_comap vL (L₀ := F) ht
  have halg₀ : IsAlgebraic (ResidueField K₀)
      (residue vF.valuationSubring ⟨T₀, (Valuation.mem_valuationSubring_iff vF T₀).mpr hT₀⟩) :=
    residue_comap_isAlgebraic vL (L₀ := F) (by convert halgT using 3; exact rfl)
  -- Temkin's linear coordinate `(T - a)/π`
  obtain ⟨a, π, ha, hπ, hπ1, hval, s₀, hs₀, hs₀tr⟩ :=
    exists_transcendental_residue_sub (vL.comap (algebraMap K C.functionField)) vF T₀ hgen hT₀
      hs₁ halg₀
  -- the coordinate `s = (T - a)/π` in `L`, with transcendental residue
  have hs₀L : ((s₀ : F) : C.functionField) =
      (T - algebraMap K C.functionField a) / algebraMap K C.functionField π := by
    rw [show ((s₀ : F) : C.functionField) = algebraMap F C.functionField (s₀ : F) from rfl, hs₀,
      map_div₀, map_sub, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rfl
  let s : 𝒪L := algebraMap vF.valuationSubring 𝒪L s₀
  have hsL : (s : C.functionField) =
      (T - algebraMap K C.functionField a) / algebraMap K C.functionField π := hs₀L
  have hstr : Transcendental (ResidueField K₀) (residue 𝒪L s) :=
    residue_comap_transcendental vL (L₀ := F) hs₀tr
  -- the blow-up `Bl_{(π, T - a)}` of the chart
  let a' : K₀ := ⟨a, ha⟩
  let π' : K₀ := ⟨π, hπ1.le⟩
  have hπ' : π' ≠ 0 := fun h ↦ hπ (congrArg Subtype.val h)
  have : Fact (π' ≠ 0) := ⟨hπ'⟩
  have hιa : ι (Polynomial.C a') = algebraMap K C.functionField a := hιC a'
  have hιπ : ι (Polynomial.C π') = algebraMap K C.functionField π := hιC π'
  have hs' : (ι X - ι (Polynomial.C a')) / ι (Polynomial.C π') = (s : C.functionField) := by
    rw [hsL, hιa, hιπ]
  have hπlt : vL (algebraMap K C.functionField π) < 1 := hπ1
  have hTalt : vL (ι (X - Polynomial.C a')) < 1 := by
    rw [map_sub, hιa]
    change vF (T₀ - algebraMap K F a) < 1
    rw [hval]
    exact hπlt
  have hxi : φU xU ∈ Set.range (smoothLocus π' a') := by
    rw [range_smoothLocus]
    intro hmem
    apply hmem
    change smoothCenter π' a' ≤ (φU xU).asIdeal
    rw [smoothCenter, Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact ((hιV _).2).mpr (by rw [hιπ]; exact hπlt)
    · exact ((hιV _).2).mpr hTalt
  obtain ⟨X₂, β, P, J, p₁, p₂, hβ, hss₂, hJ, hp₁, hp₁₂, hJβ, hover⟩ :=
    exists_smoothBlowup_globalTransport O K₀ hOB (f₁ ≫ φ) hss₁ π' a' U φU hφU hx' hxU hcl hxc hxi
  have : IsModification (β ≫ f₁) := IsModification.comp β f₁
  have : IsIntegral X₂ := hβ.sourceIntegral
  -- the centre of `vL` on `X₂`
  obtain ⟨y₂, hV₂, hβy₂⟩ :=
    hV.exists_of_universallyClosed β (genericLift_comp_of_comp f₁ (β ≫ f₁) β rfl)
  obtain ⟨pt, rfl⟩ := hover y₂ hβy₂
  have hrange : Set.range (genericLift (β ≫ f₁)) ⊆ Set.range J := by
    rintro _ ⟨z, rfl⟩
    rw [genericLift_apply]
    have : Nonempty P := ⟨pt⟩
    have : IsIntegral P := isIntegral_of_isOpenImmersion J
    exact ⟨genericPoint P, genericPoint_eq_of_isOpenImmersion J⟩
  let ηP := IsOpenImmersion.lift J (genericLift (β ≫ f₁)) hrange
  have hηP : ηP ≫ J = genericLift (β ≫ f₁) := IsOpenImmersion.lift_fac _ _ _
  have hcenP : IsCentre ηP (rzOf vL) pt := IsCentre.of_isOpenImmersion J hηP hV₂
  have hp₂η : ηP ≫ p₂ = ηY := by
    rw [← cancel_mono (U.ι ≫ (baseOpen O K₀ hOB (f₁ ≫ φ)).ι), Category.assoc, ← hJβ,
      ← Category.assoc, hηP, genericLift_comp_of_comp f₁ (β ≫ f₁) β rfl, hηY]
  have hηB : (ηP ≫ p₁) ≫ affineBlowupStructure (smoothCenter π' a') =
      Spec.map (CommRingCat.ofHom ι) := by
    rw [Category.assoc, hp₁₂, ← Category.assoc, hp₂η, hι]
  have hO : ∀ q, ι q ∈ (rzOf vL).valuationSubring := fun q ↦
    (Valuation.mem_valuationSubring_iff vL _).mpr (hιV q).1
  have hsmem : (ι X - ι (Polynomial.C a')) / ι (Polynomial.C π') ∈ (rzOf vL).valuationSubring := by
    rw [hs']
    exact s.2
  obtain ⟨-, huniq⟩ := smoothBlowup_centre π' a' hιinj (rzOf vL) hO hsmem hηB
  have hp₁pt := huniq _ (hcenP.comp p₁)
  -- the residue of `S = (T - a)/π` is transcendental: the centre is generic in its fibre
  have hres : ∀ q : K₀[X], (⟨smoothChartRingHom π' a' hιinj q,
      smoothChartRingHom_mem π' a' hιinj hO hsmem q⟩ : (rzOf vL).valuationSubring) ∈
        maximalIdeal (rzOf vL).valuationSubring ↔ ∀ i, q.coeff i ∈ maximalIdeal K₀ := by
    intro q
    have hg : smoothChartRingHom π' a' hιinj = Polynomial.eval₂RingHom
        ((ValuationSubring.subtype 𝒪L).comp (algebraMap K₀ 𝒪L)) (s : C.functionField) := by
      refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
      · rw [smoothChartRingHom_C, hιC]
        simp
      · rw [smoothChartRingHom_X, hs']
        simp
    have heq : (⟨smoothChartRingHom π' a' hιinj q, smoothChartRingHom_mem π' a' hιinj hO hsmem q⟩ :
        𝒪L) = q.eval₂ (algebraMap K₀ 𝒪L) s := by
      apply Subtype.ext
      change smoothChartRingHom π' a' hιinj q = ValuationSubring.subtype 𝒪L _
      rw [Polynomial.hom_eval₂, hg]
      rfl
    have hresq : residue 𝒪L (q.eval₂ (algebraMap K₀ 𝒪L) s) =
        aeval (residue 𝒪L s) (q.map (residue K₀)) := by
      rw [Polynomial.hom_eval₂, aeval_def, eval₂_map]
      rfl
    change (_ : 𝒪L) ∈ maximalIdeal 𝒪L ↔ _
    rw [heq, ← residue_eq_zero_iff, hresq]
    constructor
    · intro h i
      have h0 := (injective_iff_map_eq_zero _).mp (transcendental_iff_injective.mp hstr) _ h
      have := congrArg (coeff · i) h0
      simpa [coeff_map, residue_eq_zero_iff] using this
    · intro h
      have h0 : q.map (residue K₀) = 0 := by
        ext i
        simpa [coeff_map, residue_eq_zero_iff] using h i
      rw [h0, map_zero]
  have h1 := one_le_fiberTrdeg_smoothBlowupCentre π' a' hιinj (rzOf vL) hO hsmem hres
  rw [← hp₁pt] at h1
  -- the fibre dimension of the new centre is one
  have hcompP : J ≫ (β ≫ f₁) ≫ φ =
      p₁ ≫ smoothBlowupMorphism π' a' ≫ specInclusion O K₀ hOB := by
    have e1 : J ≫ (β ≫ f₁) ≫ φ = p₂ ≫ U.ι ≫ (baseOpen O K₀ hOB (f₁ ≫ φ)).ι ≫ f₁ ≫ φ := by
      simp only [Category.assoc]
      rw [reassoc_of% hJβ]
    rw [e1, ← baseRestrict_comp, ← reassoc_of% hφU, ← reassoc_of% hp₁₂, smoothBlowupMorphism,
      Category.assoc]
  have hlow : 1 ≤ fiberTrdeg ((β ≫ f₁) ≫ φ) (J pt) := by
    have := fiberTrdeg_comp_of_isOpenImmersion J ((β ≫ f₁) ≫ φ) pt
    rw [hcompP, fiberTrdeg_comp, fiberTrdeg_comp_isOpenImmersion] at this
    rw [← this]
    exact h1.trans le_self_add
  have hup : fiberTrdeg ((β ≫ f₁) ≫ φ) (J pt) ≤ 1 := fiberTrdeg_le_one φ hdim (β ≫ f₁) _
  refine ⟨X₂, inferInstance, β ≫ f₁, inferInstance, ⟨β, rfl⟩, ?_, J pt, le_antisymm hup hlow, hV₂⟩
  rw [Category.assoc]
  exact hss₂

end DeJongAlterations.StableModification.LocalUniformization
