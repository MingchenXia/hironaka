import Hironaka.Analytic.Unibranch.HironakaG10GlOffCentrePresentation

/-!
# GL-4 (`hfib`): the fibre comparison off the centre, and the reduction to points over the centre

Lane G10N5, run 0081, round 2 (`hfib` of `HironakaG10GlOffCentrePresentation.hT_of_presentation_centre`, Hironaka
1975, Lemma 4.4.5, proof, p. 538: the isomorphism (ii) of fibres, spread along `Z₁`).  For a pair `(y, y')` of a point
of the old source and a point of the new base:

* `FibreGood` — if `y' ∈ |Z₁|` and `f y = σ y'`, a point `y''` of the strict transform over `(y, y')` has an
  injective fibre map `𝒪_{Y,y}/𝔪 → 𝒪_{Y',y''}/𝔪`;
* `fibreGood_of_not_mem` — **off the centre** this always holds (`strict_covers`, isomorphic stalk maps);
* `eventually_fibreGood_of_local` — **properness**: if it holds near every pair `(y, x')` over `x'`, it holds for all
  pairs over all `y'` near `x'` (tube lemma over the compact fibre);
* `hfib_of_centre` — `hfib` (literal binder) from the same local statement at points over the centre only.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10NfFibreReduction

open Hironaka HironakaG10ChowFibreAlgebra HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction

noncomputable section

/-! ### Algebra: fibre ideals along isomorphisms -/

/-- A ring isomorphism of local rings maps the maximal ideal onto the maximal ideal. -/
theorem map_maximalIdeal_of_equiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) : Ideal.map (e : A →+* B) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B := by
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map (e.symm : B →+* A)
    simp only [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp ha this
  · intro b hb
    have hb' : e.symm b ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map (e : A →+* B)
      simp only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp hb this
    have := Ideal.mem_map_of_mem (e : A →+* B) hb'
    simpa using this

/-! ### The fibre comparison at one pair -/

/-- **The fibre comparison at one pair** `(y, y')`: if `y' ∈ |Z₁|` and `f y = σ y'`, some point `y''` of the strict
transform over `(y, y')` has an injective fibre map. -/
def FibreGood (s : Stage) (c : AdmissibleCentre s.f) (Z₁ : LocalFlattener (nextWith s c).f)
    (p : s.Y.obj.left × (nextWith s c).X.obj.left) : Prop :=
  p.2 ∈ Z₁.support → s.f.hom.left.base p.1 = (stepσ s c).hom.left.base p.2 →
    ∃ y'' : (nextWith s c).Y.obj.left, (stepQ s c).hom.left.base y'' = p.1 ∧
      (nextWith s c).f.hom.left.base y'' = p.2 ∧
      Ideal.comap ((stepQ s c).hom.left.stalkMap y'').hom (fibreIdealAt (nextWith s c).f y'') ≤
        fibreIdealAt s.f ((stepQ s c).hom.left.base y'')

/-- **Off the centre** the strict transform contains the whole fibre product and its fibre maps are isomorphisms. -/
theorem exists_fibre_of_not_mem (s : Stage) (c : AdmissibleCentre s.f) (y : s.Y.obj.left)
    (y' : (nextWith s c).X.obj.left) (hc : (stepσ s c).hom.left.base y' ∉ nonunitLocus c.B c.b)
    (hy : s.f.hom.left.base y = (stepσ s c).hom.left.base y') :
    ∃ y'' : (nextWith s c).Y.obj.left, (stepQ s c).hom.left.base y'' = y ∧
      (nextWith s c).f.hom.left.base y'' = y' ∧
      Ideal.comap ((stepQ s c).hom.left.stalkMap y'').hom (fibreIdealAt (nextWith s c).f y'') ≤
        fibreIdealAt s.f ((stepQ s c).hom.left.base y'') := by
  have : c.B.IsFiniteType := c.finiteType
  obtain ⟨y'', hp, hq⟩ := strict_covers c.B c.b c.dense s.f y y' hc hy
  refine ⟨y'', hq, hp, ?_⟩
  subst hp
  have hσ := HironakaG10GlOffCentrePresentation.isIso_stepσ_stalkMap s c ((nextWith s c).f.hom.left.base y'') hc
  have hq' := HironakaG10GlOffCentrePresentation.isIso_stepQ_stalkMap s c y'' hc
  -- the fibre ideal of `f'` is the image of that of `f`
  have hsq : (stepQ s c).hom.left ≫ s.f.hom.left = (nextWith s c).f.hom.left ≫ (stepσ s c).hom.left :=
    (congrArg (fun H : (nextWith s c).Y ⟶ s.X => H.hom.left) (strictP_comp c.B c.b c.dense s.f)).symm
  have hσfib : lrsFibreIdeal (stepσ s c).hom.left ((nextWith s c).f.hom.left.base y'') =
      IsLocalRing.maximalIdeal _ :=
    map_maximalIdeal_of_equiv (asIso ((stepσ s c).hom.left.stalkMap
      ((nextWith s c).f.hom.left.base y''))).commRingCatIsoToRingEquiv
  have h1 : lrsFibreIdeal ((nextWith s c).f.hom.left ≫ (stepσ s c).hom.left) y'' =
      fibreIdealAt (nextWith s c).f y'' := by
    rw [lrsFibreIdeal_comp, hσfib]
    rfl
  have h2 : fibreIdealAt (nextWith s c).f y'' =
      Ideal.map ((stepQ s c).hom.left.stalkMap y'').hom
        (fibreIdealAt s.f ((stepQ s c).hom.left.base y'')) := by
    rw [← h1, ← hsq, lrsFibreIdeal_comp]
  rw [h2]
  exact (Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso ((stepQ s c).hom.left.stalkMap y''))).le

theorem fibreGood_of_not_mem (s : Stage) (c : AdmissibleCentre s.f) (Z₁ : LocalFlattener (nextWith s c).f)
    (p : s.Y.obj.left × (nextWith s c).X.obj.left)
    (hc : (stepσ s c).hom.left.base p.2 ∉ nonunitLocus c.B c.b) : FibreGood s c Z₁ p :=
  fun _ hy => exists_fibre_of_not_mem s c p.1 p.2 hc hy

/-! ### Properness: from pairs over `x'` to all pairs over nearby points -/

/-- **Tube lemma over the compact fibre.** -/
theorem eventually_fibreGood_of_local (s : Stage) (c : AdmissibleCentre s.f)
    (Z₁ : LocalFlattener (nextWith s c).f) (hf : IsProperMap s.f.hom.left.base)
    (x' : (nextWith s c).X.obj.left)
    (hloc : ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base x' →
      ∀ᶠ p in 𝓝 (y, x'), FibreGood s c Z₁ p) :
    ∀ᶠ y' in 𝓝 x', ∀ y : s.Y.obj.left, FibreGood s c Z₁ (y, y') := by
  set K := s.f.hom.left.base ⁻¹' {(stepσ s c).hom.left.base x'}
  have hK : IsCompact K := hf.isCompact_preimage isCompact_singleton
  set O := {p : s.Y.obj.left × (nextWith s c).X.obj.left | ∀ᶠ q in 𝓝 p, FibreGood s c Z₁ q}
  have hO : IsOpen O := isOpen_setOfPred_eventually_nhds
  have hKO : K ×ˢ {x'} ⊆ O := by
    rintro ⟨y, y'⟩ ⟨hy, hy'⟩
    rw [Set.mem_singleton_iff] at hy'
    subst hy'
    exact hloc y hy
  obtain ⟨u, v, hu, hv, hKu, hxv, huv⟩ := generalized_tube_lemma hK isCompact_singleton hO hKO
  have hW : IsOpen (s.f.hom.left.base '' uᶜ)ᶜ :=
    (hf.isClosedMap _ hu.isClosed_compl).isOpen_compl
  have hxW : (stepσ s c).hom.left.base x' ∈ (s.f.hom.left.base '' uᶜ)ᶜ := by
    rintro ⟨z, hz, hzx⟩
    exact hz (hKu hzx)
  have hσ : Continuous (stepσ s c).hom.left.base := (stepσ s c).hom.left.base.hom.continuous
  filter_upwards [hv.mem_nhds (hxv rfl), (hW.preimage hσ).mem_nhds hxW] with y' hy'v hy'W y
  by_cases hy : s.f.hom.left.base y = (stepσ s c).hom.left.base y'
  · have hyu : y ∈ u := by
      by_contra hyu
      exact hy'W ⟨y, hyu, hy⟩
    exact (huv ⟨hyu, hy'v⟩ : (y, y') ∈ O).self_of_nhds
  · exact fun _ h => absurd h hy

/-- **`hfib` from the local fibre comparison at points over the centre.** -/
theorem hfib_of_centre
    (hcentre : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            (stepσ s c).hom.left.base x' ∈ nonunitLocus c.B c.b →
            ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base x' →
              ∀ᶠ p in 𝓝 (y, x'), (stepσ s c).hom.left.base p.2 ∈ nonunitLocus c.B c.b →
                FibreGood s c Z₁ p) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
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
                    fibreIdealAt s.f ((stepQ s c).hom.left.base y'') := by
  intro s hX hf c β hβ hfl Z x' hx' Z₁ hx₁
  have : c.B.IsFiniteType := c.finiteType
  have hloc : ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base x' →
      ∀ᶠ p in 𝓝 (y, x'), FibreGood s c Z₁ p := by
    intro y hy
    by_cases hc : (stepσ s c).hom.left.base x' ∈ nonunitLocus c.B c.b
    · filter_upwards [hcentre s hX hf c β hβ hfl Z x' hx' Z₁ hx₁ hc y hy] with p hp
      by_cases hpc : (stepσ s c).hom.left.base p.2 ∈ nonunitLocus c.B c.b
      · exact hp hpc
      · exact fibreGood_of_not_mem s c Z₁ p hpc
    · have hopen : IsOpen ((stepσ s c).hom.left.base ⁻¹' (nonunitLocus c.B c.b)ᶜ) :=
        (isClosed_nonunitLocus c.B c.b c.dense).isOpen_compl.preimage
          (stepσ s c).hom.left.base.hom.continuous
      have hmem : (stepσ s c).hom.left.base ⁻¹' (nonunitLocus c.B c.b)ᶜ ∈ 𝓝 x' := hopen.mem_nhds hc
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hmem] with p hp
      exact fibreGood_of_not_mem s c Z₁ p hp
  filter_upwards [eventually_fibreGood_of_local s c Z₁ hf x' hloc] with y' hy' h₁ y hy
  exact hy' y h₁ hy

end

end Hironaka.Analytic.Unibranch.HironakaG10NfFibreReduction
