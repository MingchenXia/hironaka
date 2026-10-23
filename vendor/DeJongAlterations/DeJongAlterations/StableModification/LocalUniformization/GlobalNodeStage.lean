import DeJongAlterations.StableModification.LocalUniformization.GlobalSmoothStage

/-!
# The node stage of local uniformization on a global curve

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Proposition
4.3.1, stage 1 (T:2976–2990): if the centre `x` of `𝔵 ∈ 𝔊⁰₀` on a strictly semi-stable curve is
the origin of a node chart `R[u,v]/(uv - c)`, then `|u| = |π|` for some `π ∈ R` with `π ∣ c`, and
after the blow-up `Bl_{(u,π)}` the centre lies in the smooth open `{π/u invertible}`.

Here, as in `GlobalSmoothStage`, the curve is a strictly semi-stable modification `C₁ → C` over
`Spec O`, `𝔵` is a valuation `vL` of `K(C)`, and the chart lives on `X_B`, `B = 𝒪_𝔵 ∩ K`. The
valuation theory is T43M's `exists_node_parameter_of_trdeg`, the centre computation T43M's
`nodeBlowup_centre_of_valuation_eq`, the globalization BND's transport with the extension of
`GlobalTransport`; the output is a smooth chart of the new curve at the new centre
(`Blowups.hasSmoothChart_of_node` on the `u`-chart of the blow-up), the input of the smooth
stage. Blueprint `lem:sm-cofinal-node-step` (`sm-local-uniformization.tex`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Polynomial

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

open ValCurves RiemannZariskiSpace Curves Blowups Algebra.NodeBlowupChart NodeBlowupCover
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [IsSepClosed K] {O : ValuationSubring K} [Finite (PrimeSpectrum O)]
  {C : Scheme.{u}} [IsIntegral C] (φ : C ⟶ Spec (.of O)) [Algebra K C.functionField]
  (hK : genericPt C ≫ φ =
    Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)))
  {Γ₁ : Type u} [LinearOrderedCommGroupWithZero Γ₁] (vL : Valuation C.functionField Γ₁)

local notation "K₀" => Valuation.valuationSubring
  (Valuation.comap (algebraMap K (Scheme.functionField C)) vL)
local notation "𝒪L" => Valuation.valuationSubring vL

include hK in
/-- **The node stage on a global curve** (`lem:sm-cofinal-node-step`; Temkin, Proposition 4.3.1,
stage 1, T:2976–2990). Let `f₁ : C₁ → C` be a strictly semi-stable modification and `vL` centred at
a closed point `x₁` of `C₁` over `𝔭 = 𝔪_{vL} ∩ O`, the origin of a node chart
`e : U → Spec B[u,v]/(uv - c)` of `X_B` (`c ≠ 0`). Then there is a strictly semi-stable
modification `C₂ → C` dominating `C₁` such that the centre `y₂` of `vL` on `C₂` lies over `x₁`
and `C₂` has a smooth chart at `y₂`. -/
theorem exists_nodeStep (htr : Algebra.trdeg K C.functionField ≤ 1)
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
      (g : C₂ ⟶ C₁) (_ : IsModification g), g ≫ f₁ = f₂ ∧ IsStrictlySemistable (f₂ ≫ φ) ⊤ ∧
      ∃ y₂ : C₂, IsCentre (genericLift f₂) (rzOf vL) y₂ ∧ g y₂ = x₁ ∧
        ∃ hy₂ : y₂ ∈ baseOpen O K₀ hOB (f₂ ≫ φ),
          HasSmoothChart (baseRestrict O K₀ hOB (f₂ ≫ φ)) ⟨y₂, hy₂⟩ := by
  have : IsDomain (Node K₀ c) := Algebra.NodeDomain.nodeQuotient_isDomain c hc
  let xU : U.toScheme := ⟨⟨x₁, hx'⟩, hxU⟩
  have hq₁ : genericLift f₁ ≫ f₁ ≫ φ =
      Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)) := by
    rw [← Category.assoc, genericLift_comp, hK]
  obtain ⟨ηY, ι, hηY, hι, hιinj, -, hιV⟩ :=
    exists_chartRingHom vL (genericLift_apply f₁) (U.ι ≫ (baseOpen O K₀ hOB (f₁ ≫ φ)).ι) e
      (y := xU) hV
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
  have : Fact (π ≠ 0) := ⟨hπ⟩
  have : Fact (b ≠ 0) := ⟨hb⟩
  -- the centre lies on the locus `V(u, v, π)`
  have hxi : e xU ∈ Set.range (nodeLocus π b) := by
    rw [range_nodeLocus]
    intro hmem
    have hπe : algebraMap K₀ (Node K₀ (π * b)) π ∈ (e xU).asIdeal := by
      have h1 : (nodeModel (π * b) (e xU)) = closedPoint K₀ := by
        rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
        exact hxc
      have h2 : π ∈ (nodeModel (π * b) (e xU)).asIdeal := by
        rw [h1]
        exact hπm
      exact h2
    rcases hmem with (h | h) | h
    · exact h hu
    · exact h hv
    · exact h hπe
  obtain ⟨X₂, β, P, J, p₁, p₂, hβ, hss₂, hJ, hp₁, hp₁₂, hJβ, hover⟩ :=
    exists_nodeBlowup_globalTransport O K₀ hOB (f₁ ≫ φ) hss₁ π b U e he hx' hxU hcl hxc hxi
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
  have hηB : (ηP ≫ p₁) ≫ affineBlowupStructure (centerIdeal π b) =
      Spec.map (CommRingCat.ofHom ι) := by
    rw [Category.assoc, hp₁₂, ← Category.assoc, hp₂η, hι]
  have hvπ' : vL (ι (coordinate (π * b) 0)) = vL (ι (algebraMap K₀ _ π)) := by
    rw [hιC, hvπ]
  have hsm : p₁ pt ∈ nodeBlowupSmoothOpen π b :=
    (nodeBlowup_centre_of_valuation_eq π b hιinj vL hO hvπ' hηB).2 _ (hcenP.comp p₁)
  -- a smooth chart at the new centre, on the `u`-chart of the blow-up
  obtain ⟨w, hw, hwp⟩ := hsm
  have hy₂ : J pt ∈ baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ) := by
    rw [mem_baseOpen_iff]
    have : ((β ≫ f₁) ≫ φ) (J pt) = (f₁ ≫ φ) x₁ := by
      rw [← hβy₂]
      rfl
    rw [this]
    exact (mem_baseOpen_iff O K₀ hOB (f₁ ≫ φ)).mp hx'
  let Q := pullback (uChartInclusion π b) p₁
  have hQrange : Set.range (pullback.snd (uChartInclusion π b) p₁ ≫ J) ⊆
      Set.range (baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).ι := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι, SetLike.mem_coe, mem_baseOpen_iff]
    have heq : (pullback.snd (uChartInclusion π b) p₁ ≫ J) ≫ (β ≫ f₁) ≫ φ =
        (pullback.snd (uChartInclusion π b) p₁ ≫ p₂ ≫ U.ι) ≫
          (baseOpen O K₀ hOB (f₁ ≫ φ)).ι ≫ f₁ ≫ φ := by
      simp only [Category.assoc]
      rw [reassoc_of% hJβ]
    rw [← Scheme.Hom.comp_apply, heq, Scheme.Hom.comp_apply]
    exact (mem_baseOpen_iff O K₀ hOB (f₁ ≫ φ)).mp
      ((pullback.snd (uChartInclusion π b) p₁ ≫ p₂ ≫ U.ι) q).2
  let ι₂ : Q ⟶ (baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).toScheme :=
    IsOpenImmersion.lift (baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).ι
      (pullback.snd (uChartInclusion π b) p₁ ≫ J) hQrange
  have hι₂ : ι₂ ≫ (baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).ι =
      pullback.snd (uChartInclusion π b) p₁ ≫ J := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion ι₂ := by
    have : IsOpenImmersion (ι₂ ≫ (baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).ι) := by
      rw [hι₂]
      infer_instance
    exact IsOpenImmersion.of_comp ι₂ (baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).ι
  have hQe : pullback.fst (uChartInclusion π b) p₁ ≫ nodeModel π =
      ι₂ ≫ baseRestrict O K₀ hOB ((β ≫ f₁) ≫ φ) := by
    rw [← cancel_mono (specInclusion O K₀ hOB), Category.assoc, Category.assoc,
      baseRestrict_comp, reassoc_of% hι₂, ← uChartInclusion_nodeBlowupMorphism π b]
    simp only [Category.assoc]
    rw [reassoc_of% pullback.condition, nodeBlowupMorphism]
    simp only [Category.assoc]
    rw [reassoc_of% hJβ, ← baseRestrict_comp, ← reassoc_of% he, reassoc_of% hp₁₂]
  obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := uChartInclusion π b)
    (g := p₁) w pt hwp
  have hch := hasSmoothChart_of_node (baseRestrict O K₀ hOB ((β ≫ f₁) ≫ φ)) ι₂ π
    (pullback.fst (uChartInclusion π b) p₁) hQe q 1 (by rw [hq₁]; exact hw)
  have hι₂q : ι₂ q = ⟨J pt, hy₂⟩ := by
    apply Subtype.ext
    change ((baseOpen O K₀ hOB ((β ≫ f₁) ≫ φ)).ι) (ι₂ q) = J pt
    rw [← Scheme.Hom.comp_apply, hι₂, Scheme.Hom.comp_apply, hq₂]
  refine ⟨X₂, inferInstance, β ≫ f₁, inferInstance, β, hβ, rfl, ?_, J pt, hV₂, hβy₂, hy₂, ?_⟩
  · rw [Category.assoc]
    exact hss₂
  · rw [← hι₂q]
    exact hch

end DeJongAlterations.StableModification.LocalUniformization
