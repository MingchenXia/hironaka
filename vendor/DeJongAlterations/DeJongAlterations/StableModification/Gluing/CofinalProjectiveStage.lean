/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45C)
-/
import DeJongAlterations.StableModification.Gluing.CofinalProjectiveTransport
import DeJongAlterations.StableModification.LocalUniformization.GlobalNodeStage

/-!
# The two stages of local uniformization with projectivity

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Proposition
4.3.1, stages 1 and 2 (T:2976–3016), in lane T43A's global form
(`LocalUniformization.exists_smoothStep`, `LocalUniformization.exists_nodeStep`), rerun with the
projective transports of `Gluing.CofinalProjectiveTransport`, so that each stage produces a
modification `g : C₂ → C₁` with `PreservesProjective g`: `C₂` is projective over every ring over
which `C₁` is projective and of finite presentation (`PLAN-T5.md` node A4).

* `exists_smoothStep_projective`: stage 2, the blow-up `Bl_{(π, T - a)}` in a smooth chart (the
  proof of T43A's `exists_smoothStep`, verbatim but for the transport);
* `exists_nodeStep_projective`: stage 1 at the origin of a node chart `uv = c`. Temkin blows up
  `(u, π)` with `|u| = |π|`; its centre `V(u, π)` is a curve, so its trivial extension is not
  known to be projective. After exchanging `u` and `v` if necessary we have `|v| ≤ |u|`, hence
  `c = π² b'`, and we blow up `(u, v, π)` instead (`Gluing.LocusBlowup`): its centre is the
  modification locus, the valuation is centred in the smooth open `{u/π invertible}` of its
  `π`-chart (`LocusBlowup.locusBlowup_centre`), and the result has a smooth chart at the new centre,
  as Temkin's stage 1 does.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Polynomial

universe u

namespace DeJongAlterations.StableModification.Gluing.CofinalProjective

open ValCurves RiemannZariskiSpace Curves Blowups LocalUniformization Algebra.NodeBlowupChart
  NodeBlowupCover
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A morphism `g : Y → Z` **preserves projectivity**: for every ring `E` and every
`p : Z → Spec E` projective and of finite presentation, `g ≫ p` is projective. -/
def PreservesProjective {Y Z : Scheme.{u}} (g : Y ⟶ Z) : Prop :=
  ∀ {E : Type u} [CommRing E] (p : Z ⟶ Spec (.of E)), IsProjectiveOver p →
    LocallyOfFinitePresentation p → IsProjectiveOver (g ≫ p)

variable {K : Type u} [Field K] [IsSepClosed K] {O : ValuationSubring K} [Finite (PrimeSpectrum O)]
  {C : Scheme.{u}} [IsIntegral C] (φ : C ⟶ Spec (.of O)) [Algebra K C.functionField]
  (hK : genericPt C ≫ φ =
    Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)))
  (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
  {Γ₁ : Type u} [LinearOrderedCommGroupWithZero Γ₁] (vL : Valuation C.functionField Γ₁)

local notation "K₀" => Valuation.valuationSubring
  (Valuation.comap (algebraMap K (Scheme.functionField C)) vL)
local notation "𝒪L" => Valuation.valuationSubring vL

include hK hdim in
/-- **The smooth stage on a global curve, with projectivity** (`lem:sm-cofinal-smooth-step` of
`sm-local-uniformization.tex`, lane T43A's `LocalUniformization.exists_smoothStep`, rerun with
`exists_smoothBlowup_globalTransport_projective`; Temkin, Proposition 4.3.1, stage 2,
T:2997–3016). The modification `C₂ → C₁` preserves projectivity over affine bases. Let
`f₁ : C₁ → C` be a strictly semi-stable modification, `vL` centred at a closed point `x₁` of `C₁`
of fibre dimension zero lying over `𝔭 = 𝔪_{vL} ∩ O`, with
a smooth chart of `X_B` at `x₁`. Then there is a strictly semi-stable modification `C₂ → C`
dominating `C₁` with `vL ∈ Γ(C₂)`. -/
theorem exists_smoothStep_projective (htr : Algebra.trdeg K C.functionField ≤ 1)
    {t : 𝒪L} (ht : Transcendental (ResidueField K₀) (residue 𝒪L t)) (hOB : O ≤ K₀)
    {C₁ : Scheme.{u}} [IsIntegral C₁] (f₁ : C₁ ⟶ C) [IsModification f₁] [IsSeparated (f₁ ≫ φ)]
    (hss₁ : IsStrictlySemistable (f₁ ≫ φ) ⊤) {x₁ : C₁} (hcl : IsClosed ({x₁} : Set C₁))
    (hV : IsCentre (genericLift f₁) (rzOf vL) x₁) (h0 : fiberTrdeg (f₁ ≫ φ) x₁ = 0)
    (hx' : x₁ ∈ baseOpen O K₀ hOB (f₁ ≫ φ))
    (hxc : baseRestrict O K₀ hOB (f₁ ≫ φ) ⟨x₁, hx'⟩ = closedPoint K₀)
    (hch : HasSmoothChart (baseRestrict O K₀ hOB (f₁ ≫ φ)) ⟨x₁, hx'⟩) :
    ∃ (C₂ : Scheme.{u}) (_ : IsIntegral C₂) (f₂ : C₂ ⟶ C) (_ : IsModification f₂),
      (∃ g : C₂ ⟶ C₁, g ≫ f₁ = f₂ ∧ PreservesProjective g) ∧
        IsStrictlySemistable (f₂ ≫ φ) ⊤ ∧ rzOf vL ∈ gammaSet (f₂ ≫ φ) (genericLift f₂) := by
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
  obtain ⟨X₂, β, P, J, p₁, p₂, hβ, hss₂, hJ, hp₁, hp₁₂, hJβ, hover, hproj⟩ :=
    exists_smoothBlowup_globalTransport_projective O K₀ hOB (f₁ ≫ φ) hss₁ π' a' U φU hφU hx' hxU
      hcl hxc hxi
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
  refine ⟨X₂, inferInstance, β ≫ f₁, inferInstance, ⟨β, rfl, fun p hp hlfp ↦ hproj p hp hlfp⟩,
    ?_, J pt, le_antisymm hup hlow, hV₂⟩
  rw [Category.assoc]
  exact hss₂

include hK in
/-- **The projective node stage, with `|v| ≤ |u|`** (the projective replacement of Temkin's stage 1,
T:2976–2990). Let `f₁ : C₁ → C` be a strictly semi-stable modification, `vL` centred at a closed
point `x₁` of `C₁` over `𝔭 = 𝔪_{vL} ∩ O`, the origin of a node chart `e : U → Spec B[u,v]/(uv - c)`
of `X_B`, `ι` the induced map of the chart to `K(C)` (`LocalUniformization.exists_chartRingHom`),
and `|v| ≤ |u|`. Then there is a strictly semi-stable modification `C₂ → C` dominating `C₁` through
a projectivity-preserving `g`, such that the centre `y₂` of `vL` on `C₂` lies over `x₁` and `C₂` has
a smooth chart at `y₂`. -/
theorem exists_nodeStep_projective_aux (htr : Algebra.trdeg K C.functionField ≤ 1)
    {t : 𝒪L} (ht : Transcendental (ResidueField K₀) (residue 𝒪L t)) (hOB : O ≤ K₀)
    {C₁ : Scheme.{u}} [IsIntegral C₁] (f₁ : C₁ ⟶ C) [IsModification f₁] [IsSeparated (f₁ ≫ φ)]
    (hss₁ : IsStrictlySemistable (f₁ ≫ φ) ⊤) {x₁ : C₁} (hcl : IsClosed ({x₁} : Set C₁))
    (hV : IsCentre (genericLift f₁) (rzOf vL) x₁) (hx' : x₁ ∈ baseOpen O K₀ hOB (f₁ ≫ φ))
    (hxc : baseRestrict O K₀ hOB (f₁ ≫ φ) ⟨x₁, hx'⟩ = closedPoint K₀)
    (U : (baseOpen O K₀ hOB (f₁ ≫ φ)).toScheme.Opens)
    (hxU : (⟨x₁, hx'⟩ : (baseOpen O K₀ hOB (f₁ ≫ φ)).toScheme) ∈ U) {c : K₀} (hc : c ≠ 0)
    (e : U.toScheme ⟶ Spec (.of (Node K₀ c))) [Etale e]
    (he : e ≫ nodeModel c = U.ι ≫ baseRestrict O K₀ hOB (f₁ ≫ φ))
    (hu : coordinate c 0 ∈ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal)
    (hv : coordinate c 1 ∈ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal)
    (ηY : Spec (.of C.functionField) ⟶ U.toScheme) (ι : Node K₀ c →+* C.functionField)
    (hηY : ηY ≫ U.ι ≫ (baseOpen O K₀ hOB (f₁ ≫ φ)).ι = genericLift f₁)
    (hι : Spec.map (CommRingCat.ofHom ι) = ηY ≫ e) (hιinj : Function.Injective ι)
    (hιV : ∀ n, vL (ι n) ≤ 1 ∧ (n ∈ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal ↔ vL (ι n) < 1))
    (hle : vL (ι (coordinate c 1)) ≤ vL (ι (coordinate c 0))) :
    ∃ (C₂ : Scheme.{u}) (_ : IsIntegral C₂) (f₂ : C₂ ⟶ C) (_ : IsModification f₂)
      (g : C₂ ⟶ C₁) (_ : IsModification g), g ≫ f₁ = f₂ ∧ PreservesProjective g ∧
      IsStrictlySemistable (f₂ ≫ φ) ⊤ ∧
      ∃ y₂ : C₂, IsCentre (genericLift f₂) (rzOf vL) y₂ ∧ g y₂ = x₁ ∧
        ∃ hy₂ : y₂ ∈ baseOpen O K₀ hOB (f₂ ≫ φ),
          HasSmoothChart (baseRestrict O K₀ hOB (f₂ ≫ φ)) ⟨y₂, hy₂⟩ := by
  have : IsDomain (Node K₀ c) := Algebra.NodeDomain.nodeQuotient_isDomain c hc
  let xU : U.toScheme := ⟨⟨x₁, hx'⟩, hxU⟩
  have hq₁ : genericLift f₁ ≫ f₁ ≫ φ =
      Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)) := by
    rw [← Category.assoc, genericLift_comp, hK]
  have hιC : ∀ r : K₀, ι (algebraMap K₀ (Node K₀ c) r) = algebraMap K C.functionField r :=
    chartRingHom_algebraMap hOB (f₁ ≫ φ) hq₁ U e he hηY hι
  have hO : ∀ r, vL (ι r) ≤ 1 := fun r ↦ (hιV r).1
  have hu0 : ι (coordinate c 0) ≠ 0 :=
    (map_ne_zero_iff ι hιinj).mpr (Algebra.NodeDomain.nodeCoordinate_ne_zero c hc 0)
  -- Temkin's parameter `π` with `|u| = |π|` and `c = π b`
  obtain ⟨π, b, hπ, hb, hcπb, hvπ⟩ :=
    exists_node_parameter_of_trdeg (vL.comap (algebraMap K C.functionField)) vL htr ht hc hιC hO
      hu0
  have hulev : vL (ι (coordinate c 0)) < 1 := ((hιV _).2).mp hu
  have hπm : π ∈ maximalIdeal K₀ := by
    rw [ValuationSubring.valuation_lt_one_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one]
    change vL (algebraMap K C.functionField π) < 1
    rw [← hvπ]
    exact hulev
  subst hcπb
  -- `|v| = |b| ≤ |π|`, so `b = π b'`
  have hπK : (π : K) ≠ 0 := fun h ↦ hπ (Subtype.ext h)
  have hπL : algebraMap K C.functionField π ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K C.functionField).injective).mpr hπK
  have hvb : vL (ι (coordinate (π * b) 1)) = vL (algebraMap K C.functionField b) := by
    have huv := congrArg ι (coordinate_mul_coordinate π b)
    rw [map_mul, map_mul, hιC, hιC] at huv
    have h := congrArg vL huv
    rw [map_mul, map_mul, hvπ] at h
    exact mul_left_cancel₀ ((map_ne_zero vL).mpr hπL) h
  have hb' : (b : K) / (π : K) ∈ K₀ := by
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply, map_div₀, map_div₀,
      div_le_one₀ (zero_lt_iff.mpr ((map_ne_zero vL).mpr hπL)), ← hvb, ← hvπ]
    exact hle
  obtain ⟨b', rfl⟩ : ∃ b' : K₀, b = π * b' := ⟨⟨_, hb'⟩, Subtype.ext (by
    change (b : K) = (π : K) * ((b : K) / (π : K))
    field_simp)⟩
  have : Fact (π ≠ 0) := ⟨hπ⟩
  have : Fact (b' ≠ 0) := ⟨right_ne_zero_of_mul hb⟩
  have : Fact (π * b' ≠ 0) := ⟨hb⟩
  -- the centre lies on the locus `V(u, v, π)`
  have hxi : e xU ∈ Set.range (nodeLocus π (π * b')) := by
    rw [range_nodeLocus]
    intro hmem
    have hπe : algebraMap K₀ (Node K₀ (π * (π * b'))) π ∈ (e xU).asIdeal := by
      have h1 : (nodeModel (π * (π * b')) (e xU)) = closedPoint K₀ := by
        rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
        exact hxc
      have h2 : π ∈ (nodeModel (π * (π * b')) (e xU)).asIdeal := by
        rw [h1]
        exact hπm
      exact h2
    rcases hmem with (h | h) | h
    · exact h hu
    · exact h hv
    · exact h hπe
  obtain ⟨X₂, β, P, J, p₁, p₂, hβ, hss₂, hJ, hp₁, hp₁₂, hJβ, hover, hproj⟩ :=
    exists_locusBlowup_globalTransport_projective O K₀ hOB (f₁ ≫ φ) hss₁ π b' U e he hx' hxU hcl
      hxc hxi
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
  have hηB : (ηP ≫ p₁) ≫ affineBlowupStructure (LocusBlowup.locusIdeal π b') =
      Spec.map (CommRingCat.ofHom ι) := by
    rw [Category.assoc, hp₁₂, ← Category.assoc, hp₂η, hι]
  have hO' : ∀ r, ι r ∈ (rzOf vL).valuationSubring := fun r ↦
    (Valuation.mem_valuationSubring_iff vL _).mpr (hO r)
  have hvu : vL (ι (coordinate (π * (π * b')) 0)) =
      vL (ι (algebraMap K₀ (Node K₀ (π * (π * b'))) π)) := by rw [hιC, hvπ]
  have hvne : vL (ι (algebraMap K₀ (Node K₀ (π * (π * b'))) π)) ≠ 0 := by
    rw [hιC]
    exact (map_ne_zero vL).mpr hπL
  have hu₁ : ι (coordinate (π * (π * b')) 0) / ι (algebraMap K₀ _ π) ∈
      (rzOf vL).valuationSubring := by
    refine (Valuation.mem_valuationSubring_iff vL _).mpr ?_
    rw [map_div₀, hvu, div_self hvne]
  have hu₁' : ι (algebraMap K₀ _ π) / ι (coordinate (π * (π * b')) 0) ∈
      (rzOf vL).valuationSubring := by
    refine (Valuation.mem_valuationSubring_iff vL _).mpr ?_
    rw [map_div₀, hvu, div_self hvne]
  have hv₁ : ι (coordinate (π * (π * b')) 1) / ι (algebraMap K₀ _ π) ∈
      (rzOf vL).valuationSubring := by
    refine (Valuation.mem_valuationSubring_iff vL _).mpr ?_
    rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hvne), ← hvu]
    exact hle
  have hsm : p₁ pt ∈ LocusBlowup.locusBlowupSmoothOpen π b' :=
    (LocusBlowup.locusBlowup_centre π b' hιinj (rzOf vL) hO' hu₁ hu₁' hv₁ hηB).2 _
      (hcenP.comp p₁)
  -- a smooth chart at the new centre, on the `π`-chart of the blow-up
  obtain ⟨w, hw, hwp⟩ := hsm
  have hy₂ : J pt ∈ baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ) := by
    rw [mem_baseOpen_iff]
    have : ((β ≫ f₁) ≫ φ) (J pt) = (f₁ ≫ φ) x₁ := by
      rw [← hβy₂]
      rfl
    rw [this]
    exact (mem_baseOpen_iff O K₀ hOB (f₁ ≫ φ)).mp hx'
  let Q := pullback (LocusBlowup.piChartInclusion π b') p₁
  have hQrange : Set.range (pullback.snd (LocusBlowup.piChartInclusion π b') p₁ ≫ J) ⊆
      Set.range (baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).ι := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι, SetLike.mem_coe, mem_baseOpen_iff]
    have heq : (pullback.snd (LocusBlowup.piChartInclusion π b') p₁ ≫ J) ≫ (β ≫ f₁) ≫ φ =
        (pullback.snd (LocusBlowup.piChartInclusion π b') p₁ ≫ p₂ ≫ U.ι) ≫
          (baseOpen O K₀ hOB (f₁ ≫ φ)).ι ≫ f₁ ≫ φ := by
      simp only [Category.assoc]
      rw [reassoc_of% hJβ]
    rw [← Scheme.Hom.comp_apply, heq, Scheme.Hom.comp_apply]
    exact (mem_baseOpen_iff O K₀ hOB (f₁ ≫ φ)).mp
      ((pullback.snd (LocusBlowup.piChartInclusion π b') p₁ ≫ p₂ ≫ U.ι) q).2
  let ι₂ : Q ⟶ (baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).toScheme :=
    IsOpenImmersion.lift (baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).ι
      (pullback.snd (LocusBlowup.piChartInclusion π b') p₁ ≫ J) hQrange
  have hι₂ : ι₂ ≫ (baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).ι =
      pullback.snd (LocusBlowup.piChartInclusion π b') p₁ ≫ J := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion ι₂ := by
    have : IsOpenImmersion (ι₂ ≫ (baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).ι) := by
      rw [hι₂]
      infer_instance
    exact IsOpenImmersion.of_comp ι₂ (baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).ι
  have hQe : pullback.fst (LocusBlowup.piChartInclusion π b') p₁ ≫ nodeModel b' =
      ι₂ ≫ baseRestrict O K₀ hOB ((β ≫ f₁) ≫ φ) := by
    rw [← cancel_mono (specInclusion O K₀ hOB), Category.assoc, Category.assoc,
      baseRestrict_comp, reassoc_of% hι₂, ← LocusBlowup.piChartInclusion_morphism π b']
    simp only [Category.assoc]
    rw [reassoc_of% pullback.condition]
    rw [reassoc_of% hJβ, ← baseRestrict_comp, ← reassoc_of% he, reassoc_of% hp₁₂]
  obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := LocusBlowup.piChartInclusion π b') (g := p₁) w pt hwp
  have hch := hasSmoothChart_of_node (baseRestrict O K₀ hOB ((β ≫ f₁) ≫ φ)) ι₂ b'
    (pullback.fst (LocusBlowup.piChartInclusion π b') p₁) hQe q 0 (by rw [hq₁]; exact hw)
  have hι₂q : ι₂ q = ⟨J pt, hy₂⟩ := by
    apply Subtype.ext
    change ((baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).ι) (ι₂ q) = J pt
    rw [← Scheme.Hom.comp_apply, hι₂, Scheme.Hom.comp_apply, hq₂]
  refine ⟨X₂, inferInstance, β ≫ f₁, inferInstance, β, hβ, rfl,
    fun p hp hlfp ↦ hproj p hp hlfp, ?_, J pt, hV₂, hβy₂, hy₂, ?_⟩
  · rw [Category.assoc]
    exact hss₂
  · rw [← hι₂q]
    exact hch

include hK in
/-- **The node stage on a global curve, with projectivity** (the projective form of lane T43A's
`LocalUniformization.exists_nodeStep`, `lem:sm-cofinal-node-step`; Temkin, Proposition 4.3.1,
stage 1, T:2976–2990, with the blow-up of `(u, v, π)` instead of `(u, π)`, after exchanging `u` and
`v` so that `|v| ≤ |u|`). Let `f₁ : C₁ → C` be a strictly semi-stable modification and `vL` centred
at a closed point `x₁` of `C₁` over `𝔭 = 𝔪_{vL} ∩ O`, the origin of a node chart
`e : U → Spec B[u,v]/(uv - c)` of `X_B` (`c ≠ 0`). Then there is a strictly semi-stable
modification `C₂ → C` dominating `C₁` through a projectivity-preserving modification `g`, such
that the centre `y₂` of `vL` on `C₂` lies over `x₁` and `C₂` has a smooth chart at `y₂`. -/
theorem exists_nodeStep_projective (htr : Algebra.trdeg K C.functionField ≤ 1)
    {t : 𝒪L} (ht : Transcendental (ResidueField K₀) (residue 𝒪L t)) (hOB : O ≤ K₀)
    {C₁ : Scheme.{u}} [IsIntegral C₁] (f₁ : C₁ ⟶ C) [IsModification f₁] [IsSeparated (f₁ ≫ φ)]
    (hss₁ : IsStrictlySemistable (f₁ ≫ φ) ⊤) {x₁ : C₁} (hcl : IsClosed ({x₁} : Set C₁))
    (hV : IsCentre (genericLift f₁) (rzOf vL) x₁) (hx' : x₁ ∈ baseOpen O K₀ hOB (f₁ ≫ φ))
    (hxc : baseRestrict O K₀ hOB (f₁ ≫ φ) ⟨x₁, hx'⟩ = closedPoint K₀)
    (U : (baseOpen O K₀ hOB (f₁ ≫ φ)).toScheme.Opens)
    (hxU : (⟨x₁, hx'⟩ : (baseOpen O K₀ hOB (f₁ ≫ φ)).toScheme) ∈ U) {c : K₀} (hc : c ≠ 0)
    (e : U.toScheme ⟶ Spec (.of (Node K₀ c))) [Etale e]
    (he : e ≫ nodeModel c = U.ι ≫ baseRestrict O K₀ hOB (f₁ ≫ φ))
    (hu : coordinate c 0 ∈ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal)
    (hv : coordinate c 1 ∈ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal) :
    ∃ (C₂ : Scheme.{u}) (_ : IsIntegral C₂) (f₂ : C₂ ⟶ C) (_ : IsModification f₂)
      (g : C₂ ⟶ C₁) (_ : IsModification g), g ≫ f₁ = f₂ ∧ PreservesProjective g ∧
      IsStrictlySemistable (f₂ ≫ φ) ⊤ ∧
      ∃ y₂ : C₂, IsCentre (genericLift f₂) (rzOf vL) y₂ ∧ g y₂ = x₁ ∧
        ∃ hy₂ : y₂ ∈ baseOpen O K₀ hOB (f₂ ≫ φ),
          HasSmoothChart (baseRestrict O K₀ hOB (f₂ ≫ φ)) ⟨y₂, hy₂⟩ := by
  have : IsDomain (Node K₀ c) := Algebra.NodeDomain.nodeQuotient_isDomain c hc
  let xU : U.toScheme := ⟨⟨x₁, hx'⟩, hxU⟩
  obtain ⟨ηY, ι, hηY, hι, hιinj, -, hιV⟩ :=
    exists_chartRingHom vL (genericLift_apply f₁) (U.ι ≫ (baseOpen O K₀ hOB (f₁ ≫ φ)).ι) e
      (y := xU) hV
  by_cases hle : vL (ι (coordinate c 1)) ≤ vL (ι (coordinate c 0))
  · exact exists_nodeStep_projective_aux φ hK vL htr ht hOB f₁ hss₁ hcl hV hx' hxc U hxU hc e he
      hu hv ηY ι hηY hι hιinj hιV hle
  -- exchange `u` and `v`
  let σ : CommRingCat.of (Node K₀ c) ⟶ CommRingCat.of (Node K₀ c) :=
    (nodeSwap c).toRingEquiv.toCommRingCatIso.hom
  have : IsIso (Spec.map σ) := inferInstance
  let e' := e ≫ Spec.map σ
  have : Etale e' := inferInstance
  have hσ : Spec.map σ ≫ nodeModel c = nodeModel c := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a : 2
    exact (nodeSwap c).commutes a
  have he' : e' ≫ nodeModel c = U.ι ≫ baseRestrict O K₀ hOB (f₁ ≫ φ) := by
    rw [Category.assoc, hσ, he]
  have hpt : ∀ n, n ∈ (e' xU).asIdeal ↔ nodeSwap c n ∈ (e xU).asIdeal := fun n ↦ by
    rw [Scheme.Hom.comp_apply, Spec.map_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    rfl
  have hu' : coordinate c 0 ∈ (e' xU).asIdeal := by
    rw [hpt, nodeSwap_coordinate0]
    exact hv
  have hv' : coordinate c 1 ∈ (e' xU).asIdeal := by
    rw [hpt, nodeSwap_coordinate1]
    exact hu
  let ι' : Node K₀ c →+* C.functionField := ι.comp (nodeSwap c).toRingEquiv.toRingHom
  have hι' : Spec.map (CommRingCat.ofHom ι') = ηY ≫ e' := by
    change Spec.map (σ ≫ CommRingCat.ofHom ι) = _
    rw [Spec.map_comp, hι, Category.assoc]
  have hιinj' : Function.Injective ι' := hιinj.comp (nodeSwap c).injective
  have hιV' : ∀ n, vL (ι' n) ≤ 1 ∧ (n ∈ (e' xU).asIdeal ↔ vL (ι' n) < 1) := fun n ↦ by
    rw [hpt]
    exact hιV (nodeSwap c n)
  have hle' : vL (ι' (coordinate c 1)) ≤ vL (ι' (coordinate c 0)) := by
    change vL (ι (nodeSwap c (coordinate c 1))) ≤ vL (ι (nodeSwap c (coordinate c 0)))
    rw [nodeSwap_coordinate0, nodeSwap_coordinate1]
    exact (not_le.mp hle).le
  exact exists_nodeStep_projective_aux φ hK vL htr ht hOB f₁ hss₁ hcl hV hx' hxc U hxU hc e' he'
    hu' hv' ηY ι' hηY hι' hιinj' hιV' hle'

end DeJongAlterations.StableModification.Gluing.CofinalProjective
