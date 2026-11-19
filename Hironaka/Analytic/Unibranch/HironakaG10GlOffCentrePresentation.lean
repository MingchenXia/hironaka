import Hironaka.Analytic.Unibranch.HironakaG10GlStrictFlatAssembly
import Hironaka.Analytic.Unibranch.HironakaG10GermFlattenerSquareTransport
import Hironaka.Analytic.Unibranch.ComplexSpaceLocalEmbedding
import Hironaka.Analytic.HolomorphicGermNoetherian

/-!
# Pulled torsion presentations off the centre, and `hT` from presentations over the centre only

Lane G10GL, run 0081, item GL-3a (`work/hironaka-run0081-20261117/G10GL/STATUS.md`).  Off the centre the blowup is a
local isomorphism and the strict transform is the old family (`stepProj_isIsoOver`, `strict_openImmersionOn`), so the
strict-source stalk itself is a pulled torsion presentation (`HironakaG10GlStrictFlatAssembly.PulledPresentation`)
with the generator `1` of the (unit) pulled centre: its flattener is the transported pointed flattener of `f`
(`HironakaG10FlatFamilyEquivTransport.wholeFamilyFlattener_equiv` through the isomorphic stalk square).

* `pulledPresentation_of_not_mem_nonunitLocus` — the presentation at every point of the strict source over the unit
  locus of the centre (no chart, no named input);
* `nonempty_pulledPresentation_of_centre` — presentations everywhere from presentations over the centre;
* `hT_of_presentation_centre` — **`hT` (literal binder) from N5, presentations at the points of the strict source over
  the centre, and the fibre comparison (hfib)**.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GlOffCentrePresentation

open Hironaka HironakaG10PNIdealFamily HironakaG10HirIdealGerms
  HironakaSingularModuleSheafStalk HironakaG10ChowArtinReesCentre HironakaG10HirFlatQuotient
  HironakaG10FlatFamilyEquivTransport
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation
  Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction Hironaka.Analytic.Unibranch.HironakaG10GlStrictFlatAssembly
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10ChowNativeIsoCriterion Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction

noncomputable section

/-- Every stalk of a reduced complex space is noetherian (a quotient of a germ ring of `ℂⁿ`; the same proof as
`PrimeNov16AnalyticNormalizationBranches.original_stalk_noetherian`, which is not in this import closure). -/
theorem stalk_noetherian (X : SourceReducedComplexSpace) (x : X.obj.left) :
    IsNoetherianRing (X.obj.left.presheaf.stalk x).carrier := by
  let e := LocalEmbedding.ofPoint X x
  obtain ⟨c, hcx⟩ := LocalEmbedding.mem_range_ofPoint X x
  change e.toPoint c = x at hcx
  let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  let E := ((asIso (e.map.stalkMap c)).commRingCatIsoToRingEquiv).trans
    (HironakaActualAnalyticSubspace.actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c)
  have := isNoetherianRing_holGerm_euclidean e.dim
  have ht := isNoetherianRing_of_ringEquiv _ E.symm
  change IsNoetherianRing (X.obj.left.presheaf.stalk (e.toPoint c)).carrier at ht
  exact Eq.mp (congrArg (fun t : X.obj.left =>
    IsNoetherianRing (X.obj.left.presheaf.stalk t).carrier) hcx) ht

/-- Saturating the zero ideal by `1` gives the zero ideal. -/
theorem powerSat_bot_one (B : Type*) [CommRing B] : powerSat (⊥ : Ideal B) 1 = ⊥ := by
  ext a
  simp only [mem_powerSat, one_pow, one_mul, Submodule.mem_bot, exists_const]

/-- The base stalk map of one step is an isomorphism over the unit locus of the centre. -/
theorem isIso_stepσ_stalkMap (s : Stage) (c : AdmissibleCentre s.f) (x' : (nextWith s c).X.obj.left)
    (hc : (stepσ s c).hom.left.base x' ∉ nonunitLocus c.B c.b) :
    IsIso ((stepσ s c).hom.left.stalkMap x') := by
  let _ := c.finiteType
  exact isIso_stalkMap_of_isIsoOver (stepProj_isIsoOver c.B c.b c.dense) x' hc

/-- The strict-transform stalk map is an isomorphism over the unit locus of the centre. -/
theorem isIso_stepQ_stalkMap (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left)
    (hc : (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'') ∉ nonunitLocus c.B c.b) :
    IsIso ((stepQ s c).hom.left.stalkMap y'') := by
  let _ := c.finiteType
  apply isIso_stalkMap_of_isOpenImmersionOn (strict_openImmersionOn c.B c.b c.dense s.f) y''
  exact hc

/-- Off the centre, the flattener of the strict-family stalk map is the transported pointed flattener of `f`
(isomorphic stalk square). -/
theorem flattener_of_not_mem_nonunitLocus (s : Stage) (c : AdmissibleCentre s.f)
    (y'' : (nextWith s c).Y.obj.left)
    (hc : (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'') ∉ nonunitLocus c.B c.b)
    (h : s.f.hom.left.base ((stepQ s c).hom.left.base y'') =
      (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y''))
    (P : Ideal (s.X.obj.left.presheaf.stalk
      ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y''))))
    (hP : IsPointFlattenerAt s.f _ ((stepQ s c).hom.left.base y'') h P) :
    IsFlattenerIdeal ((nextWith s c).f.hom.left.stalkMap y'').hom
      (Ideal.map ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y'')).hom P) := by
  have hσ := isIso_stepσ_stalkMap s c ((nextWith s c).f.hom.left.base y'') hc
  have hq := isIso_stepQ_stalkMap s c y'' hc
  let e := (asIso ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y''))).commRingCatIsoToRingEquiv
  let d := (asIso ((stepQ s c).hom.left.stalkMap y'')).commRingCatIsoToRingEquiv
  have H : (nextWith s c).f.hom.left ≫ (stepσ s c).hom.left = (stepQ s c).hom.left ≫ s.f.hom.left :=
    congrArg (fun k => k.hom.left) (stepQ_comp s c)
  have hsquare : ((nextWith s c).f.hom.left.stalkMap y'').hom.comp e.toRingHom =
      d.toRingHom.comp (fibreStalkMap s.f _ _ h) := by
    ext r
    change ((nextWith s c).f.hom.left.stalkMap y'').hom
        ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y'') r) =
      (stepQ s c).hom.left.stalkMap y'' (fibreStalkMap s.f _ _ h r)
    have heq : ((nextWith s c).f.hom.left.stalkMap y'').hom
        ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y'') r) =
        (((nextWith s c).f.hom.left ≫ (stepσ s c).hom.left).stalkMap y'').hom r := by
      rw [LocallyRingedSpace.stalkMap_comp]
      rfl
    rw [heq, stalkMap_eq_of_eq _ _ H y'' h r, LocallyRingedSpace.stalkMap_comp]
    rfl
  have hI : ∀ J : Ideal (s.X.obj.left.presheaf.stalk
      ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y''))),
      (∀ _i : Unit, (quotMap (fibreStalkMap s.f _ _ h) J).Flat) ↔ P ≤ J := fun J =>
    (forall_const Unit).trans (hP J)
  have hnew := wholeFamilyFlattener_equiv (fun _ : Unit => fibreStalkMap s.f _ _ h)
    (fun _ : Unit => ((nextWith s c).f.hom.left.stalkMap y'').hom) id Function.surjective_id e
    (fun _ => d) (fun _ => hsquare) P hI
  intro J
  exact (forall_const Unit).symm.trans (hnew J)

/-- **The pulled torsion presentation off the centre**: the strict-source stalk itself, with the generator `1`. -/
def pulledPresentation_of_not_mem_nonunitLocus (s : Stage) (c : AdmissibleCentre s.f)
    (y'' : (nextWith s c).Y.obj.left)
    (hc : (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'') ∉ nonunitLocus c.B c.b) :
    PulledPresentation s c y'' where
  B := (nextWith s c).Y.obj.left.presheaf.stalk y''
  noetherian := stalk_noetherian _ y''
  ψ := ((nextWith s c).f.hom.left.stalkMap y'').hom
  g := 1
  span_g := by
    have hrange : centreIdeal c ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'')) = ⊤ := by
      by_contra h
      exact hc h
    rw [hrange, Ideal.map_top, Ideal.span_singleton_one]
  β := (Ideal.quotEquivOfEq (by rw [map_one, powerSat_bot_one])).trans (RingEquiv.quotientBot _)
  comm a := rfl
  flattener h P hP := flattener_of_not_mem_nonunitLocus s c y'' hc h P hP
  local_ := by
    refine (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_).trans
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    exact map_nonunit ((nextWith s c).f.hom.left.stalkMap y'').hom a ha

/-- Presentations everywhere from presentations over the centre. -/
theorem nonempty_pulledPresentation_of_centre
    (hpres : ∀ (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left),
      (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'') ∈ nonunitLocus c.B c.b →
      Nonempty (PulledPresentation s c y''))
    (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left) :
    Nonempty (PulledPresentation s c y'') := by
  by_cases hc : (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'') ∈ nonunitLocus c.B c.b
  · exact hpres s c y'' hc
  · exact ⟨pulledPresentation_of_not_mem_nonunitLocus s c y'' hc⟩

/-- **`hT` (Hironaka's Lemma 4.4.5, literal binder of the final splice) from N5 (G10HT's native form), pulled torsion
presentations at the points of the strict source over the centre, and the fibre comparison (hfib).** -/
theorem hT_of_presentation_centre
    (hN5 : ∀ (s : Stage) (c : AdmissibleCentre s.f) (x' : (nextWith s c).X.obj.left)
      (I : Ideal (s.X.obj.left.presheaf.stalk ((stepσ s c).hom.left.base x')))
      (G : (nextWith s c).X.obj.left.presheaf.stalk x'), IsRegular G →
      Ideal.map ((stepσ s c).hom.left.stalkMap x').hom (centreIdeal c ((stepσ s c).hom.left.base x')) =
        Ideal.span {G} →
      strictIdeal ((stepσ s c).hom.left.stalkMap x').hom I (centreIdeal c ((stepσ s c).hom.left.base x')) G =
        powerSat (Ideal.map ((stepσ s c).hom.left.stalkMap x').hom I) G)
    (hpres : ∀ (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left),
      (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'') ∈ nonunitLocus c.B c.b →
      Nonempty (PulledPresentation s c y''))
    (hfib : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support →
              ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base y' →
                ∃ y'' : (nextWith s c).Y.obj.left, (stepQ s c).hom.left.base y'' = y ∧
                  (nextWith s c).f.hom.left.base y'' = y' ∧
                  Ideal.comap ((stepQ s c).hom.left.stalkMap y'').hom
                      (fibreIdealAt (nextWith s c).f y'') ≤
                    fibreIdealAt s.f ((stepQ s c).hom.left.base y'')) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z :=
  hT_of_presentation hN5 (nonempty_pulledPresentation_of_centre hpres) hfib

end

end Hironaka.Analytic.Unibranch.HironakaG10GlOffCentrePresentation
