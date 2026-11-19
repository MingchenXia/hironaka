import Hironaka.Analytic.Unibranch.HironakaG10NfFibreModel

/-!
# H3.4 (abstract core): a local model of the fibre product with its base-change data at the origin only

Lane G10H3, run 0081.  `HironakaG10NfFibreModel.FibreModel` asks for the base change of flatness (`flat_base`), the
locality of `ψ`, the regular centre generator and the flatness transfer at EVERY point `w` of the model; its proofs
only use them at the origin `w₀`.  The canonical charts provide base change of flatness only at a chart point lying
over the given source point (G10N34's `flat_base_canonical`), and the natural torsion at a general chart point is the
joint pivot torsion (not literally `powerSat ⊥ (ψ g)`).  `FibreModel₀` therefore keeps

* at every `w`: the pair `(pY w, pX w)`, the ring `B w` with `ψ w`, an ideal `T w` (the exceptional torsion), and the
  strict-transform readout (a point `y''` of `Y'` over the pair with injective fibre map) when `T w` lies in the closed
  fibre;
* at `w₀` only: locality, a regular generator `g₀` of the pulled centre with `T w₀ = powerSat ⊥ (ψ g₀)`, base change of
  flatness, and the flatness transfer;
* `cover` only for pairs over the centre (all that `HironakaG10NfFibreReduction.hfib_of_centre` needs);
* `spread` of a torsion bound by `Z₁`.

Main results: `fibreGood_of_model₀` and **`hfib_of_fibreModels₀`** (the literal `hfib` binder of
`HironakaG10GlOffCentrePresentation.hT_of_presentation_centre`).  No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10NfFibreModelOrigin

open Hironaka HironakaG10ChowFibreAlgebra HironakaSingularModuleSheafStalk
  HironakaG10HirFlatQuotient HironakaG10ChowArtinReesCentre
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation
  Hironaka.Analytic.Unibranch.HironakaG10SbStrictFlatAlgebra Hironaka.Analytic.Unibranch.HironakaG10NfFibreReduction

noncomputable section

/-- **A local model of the fibre product `Y ×_X X'` near `(y, x')`, with its base-change data at the origin.** -/
structure FibreModel₀ (s : Stage) (c : AdmissibleCentre s.f) (Z₁ : LocalFlattener (nextWith s c).f)
    (y : s.Y.obj.left) (x' : (nextWith s c).X.obj.left) where
  /-- the parameter space of the model (pairs of the fibre product) -/
  W : Type
  [top : TopologicalSpace W]
  w₀ : W
  pY : W → s.Y.obj.left
  pX : W → (nextWith s c).X.obj.left
  pY_w₀ : pY w₀ = y
  pX_w₀ : pX w₀ = x'
  square : ∀ w, s.f.hom.left.base (pY w) = (stepσ s c).hom.left.base (pX w)
  /-- the model covers the fibre product over the centre near `(y, x')` -/
  cover : ∀ U ∈ 𝓝 w₀, ∀ᶠ p in 𝓝 (y, x'), (stepσ s c).hom.left.base p.2 ∈ nonunitLocus c.B c.b →
    s.f.hom.left.base p.1 = (stepσ s c).hom.left.base p.2 → ∃ w ∈ U, pY w = p.1 ∧ pX w = p.2
  /-- the local ring of the fibre product at `w` -/
  B : W → Type
  [ring : ∀ w, CommRing (B w)]
  [noetherian : ∀ w, IsNoetherianRing (B w)]
  ψ : ∀ w, (nextWith s c).X.obj.left.presheaf.stalk (pX w) →+* B w
  /-- the exceptional torsion of the fibre product at `w` -/
  T : ∀ w, Ideal (B w)
  local₀ : Ideal.map (ψ w₀) (IsLocalRing.maximalIdeal _) ≤ Ideal.jacobson ⊥
  /-- a regular generator of the pulled centre at the origin -/
  g₀ : (nextWith s c).X.obj.left.presheaf.stalk (pX w₀)
  g₀_regular : IsRegular g₀
  span_g₀ : Ideal.map ((stepσ s c).hom.left.stalkMap (pX w₀)).hom
    (centreIdeal c ((stepσ s c).hom.left.base (pX w₀))) = Ideal.span {g₀}
  T_w₀ : T w₀ = powerSat (⊥ : Ideal (B w₀)) (ψ w₀ g₀)
  /-- base change of flatness of the old family at the origin (Hironaka Th. 2.5) -/
  flat_base₀ : ∀ J : Ideal (s.X.obj.left.presheaf.stalk ((stepσ s c).hom.left.base (pX w₀))),
    (quotMap (fibreStalkMap s.f _ (pY w₀) (square w₀)) J).Flat →
      (quotMap (ψ w₀) (Ideal.map ((stepσ s c).hom.left.stalkMap (pX w₀)).hom J)).Flat
  /-- the strict transform at a pair whose torsion lies in the closed fibre -/
  strict : ∀ w, T w ≤ Ideal.map (ψ w) (IsLocalRing.maximalIdeal _) →
    ∃ (y'' : (nextWith s c).Y.obj.left) (_ : (stepQ s c).hom.left.base y'' = pY w)
      (_ : (nextWith s c).f.hom.left.base y'' = pX w),
      Ideal.comap ((stepQ s c).hom.left.stalkMap y'').hom (fibreIdealAt (nextWith s c).f y'') ≤
          fibreIdealAt s.f ((stepQ s c).hom.left.base y'')
  /-- the flatness transfer at the origin -/
  strict₀ : T w₀ ≤ Ideal.map (ψ w₀) (IsLocalRing.maximalIdeal _) →
    ∃ (y'' : (nextWith s c).Y.obj.left) (hp : (nextWith s c).f.hom.left.base y'' = pX w₀),
      ∀ J₁ : Ideal ((nextWith s c).X.obj.left.presheaf.stalk (pX w₀)),
        (quotMap (fibreStalkMap (nextWith s c).f (pX w₀) y'' hp) J₁).Flat →
          (quotMap ((Ideal.Quotient.mk (T w₀)).comp (ψ w₀)) J₁).Flat
  /-- a torsion bound by `Z₁` spreads (coherence) -/
  spread : pX w₀ ∈ Z₁.support → T w₀ ≤ Ideal.map (ψ w₀) (Z₁.H (pX w₀)) →
    ∀ᶠ w in 𝓝 w₀, T w ≤ Ideal.map (ψ w) (Z₁.H (pX w))

attribute [instance] FibreModel₀.top FibreModel₀.ring FibreModel₀.noetherian

variable {s : Stage} {c : AdmissibleCentre s.f} {Z₁ : LocalFlattener (nextWith s c).f}
  {y : s.Y.obj.left} {x' : (nextWith s c).X.obj.left}

/-- **(i) at a point of `T(Z)`**: the exceptional torsion at the origin lies in the closed fibre. -/
theorem torsion_le_maximal₀ (M : FibreModel₀ s c Z₁ y x') (Z : LocalFlattener s.f)
    (hx' : M.pX M.w₀ ∈ transportedSupport s c Z) :
    M.T M.w₀ ≤ Ideal.map (M.ψ M.w₀) (IsLocalRing.maximalIdeal _) := by
  rw [M.T_w₀]
  set w := M.w₀
  set J := germFlattener s.f ((stepσ s c).hom.left.base (M.pX w))
  have hflatY : (quotMap (fibreStalkMap s.f _ (M.pY w) (M.square w)) J).Flat :=
    ((isGermFlattenerAt_germFlattener s.f _) J).mpr le_rfl (M.pY w) (M.square w)
  have hflat := M.flat_base₀ J hflatY
  set J' := powerSat (Ideal.map ((stepσ s c).hom.left.stalkMap (M.pX w)).hom J) M.g₀
  have hflat' : (quotMap (M.ψ w) J').Flat := flat_quotMap_of_le _ (le_powerSat _ _) hflat
  have hreg : IsRegular (Ideal.Quotient.mk J' M.g₀) := isRegular_mk_powerSat _ _
  have hK := powerSat_bot_le_map (M.ψ w) J' M.g₀ hreg hflat'
  have hJ' : J' ≠ ⊤ := by
    have h1 := hx'.2 M.g₀ M.g₀_regular M.span_g₀
    rwa [Hironaka.Analytic.Unibranch.HironakaG10NfN5.hN5 s c (M.pX w) J M.g₀ M.g₀_regular M.span_g₀] at h1
  exact hK.trans (Ideal.map_mono (IsLocalRing.le_maximalIdeal hJ'))

/-- **The torsion lies in `J₁·B`** at the origin (flatness of the strict family over `Z₁` and Nakayama). -/
theorem torsion_le_Z₁₀ (M : FibreModel₀ s c Z₁ y x') (Z : LocalFlattener s.f)
    (hx' : M.pX M.w₀ ∈ transportedSupport s c Z) (hx₁ : M.pX M.w₀ ∈ Z₁.support) :
    M.T M.w₀ ≤ Ideal.map (M.ψ M.w₀) (Z₁.H (M.pX M.w₀)) := by
  have hmax := torsion_le_maximal₀ M Z hx'
  obtain ⟨y'', hp, htr⟩ := M.strict₀ hmax
  have hfl : (quotMap (fibreStalkMap (nextWith s c).f (M.pX M.w₀) y'' hp) (Z₁.H (M.pX M.w₀))).Flat :=
    (Z₁.flattener _ hx₁.1 hx₁.2 (Z₁.H (M.pX M.w₀))).mpr le_rfl y'' hp
  exact le_map_of_flat_of_le (M.ψ M.w₀) _ _ (IsLocalRing.maximalIdeal _) hmax M.local₀ (htr _ hfl)

/-- **The fibre comparison at all pairs over the centre near `(y, x')`.** -/
theorem fibreGood_of_model₀ (M : FibreModel₀ s c Z₁ y x') (Z : LocalFlattener s.f)
    (hx' : x' ∈ transportedSupport s c Z) (hx₁ : x' ∈ Z₁.support) :
    ∀ᶠ p in 𝓝 (y, x'), (stepσ s c).hom.left.base p.2 ∈ nonunitLocus c.B c.b → FibreGood s c Z₁ p := by
  have hx'' : M.pX M.w₀ ∈ transportedSupport s c Z := by rw [M.pX_w₀]; exact hx'
  have hx₁' : M.pX M.w₀ ∈ Z₁.support := by rw [M.pX_w₀]; exact hx₁
  have hsp := M.spread hx₁' (torsion_le_Z₁₀ M Z hx'' hx₁')
  filter_upwards [M.cover _ hsp] with p hp hpc
  obtain ⟨a, b⟩ := p
  intro hb hab
  obtain ⟨w, hw, hwa, hwb⟩ := hp hpc hab
  subst hwa
  subst hwb
  have hH : Z₁.H (M.pX w) ≤ IsLocalRing.maximalIdeal _ := IsLocalRing.le_maximalIdeal hb.2
  obtain ⟨y'', hq, hp', hinj⟩ := M.strict w (hw.trans (Ideal.map_mono hH))
  exact ⟨y'', hq, hp', hinj⟩

/-- **`hfib` (literal binder of `HironakaG10GlOffCentrePresentation.hT_of_presentation_centre`) from local models
of the fibre product, with base-change data at the origin, at the pairs over the centre.** -/
theorem hfib_of_fibreModels₀
    (hmodel : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            (stepσ s c).hom.left.base x' ∈ nonunitLocus c.B c.b →
            ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base x' →
              Nonempty (FibreModel₀ s c Z₁ y x')) :
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
  refine hfib_of_centre ?_
  intro s hX hf c β hβ hfl Z x' hx' Z₁ hx₁ hc y hy
  obtain ⟨M⟩ := hmodel s hX hf c β hβ hfl Z x' hx' Z₁ hx₁ hc y hy
  exact fibreGood_of_model₀ M Z hx' hx₁

end

end Hironaka.Analytic.Unibranch.HironakaG10NfFibreModelOrigin
