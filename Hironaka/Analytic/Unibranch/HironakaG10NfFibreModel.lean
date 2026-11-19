import Hironaka.Analytic.Unibranch.HironakaG10NfFibreReduction
import Hironaka.Analytic.Unibranch.HironakaG10NfN5

/-!
# GL-4 (`hfib`) over the centre: Hironaka's fibre comparison from a local model of the fibre product

Lane G10N5, run 0081, round 2.  Hironaka 1975, Lemma 4.4.5, proof, p. 538: at `x' ∈ T(Z)` the total transform
restricted to `Z*` has no exceptional torsion ((i): `F'|Z* ≅ F₁|Z*`), so the fibre maps over `x'` are isomorphisms
((ii)); since the strict family is flat over `Z₁`, the kernel of `F'|Z₁ → F₁|Z₁` vanishes near the fibre over `x'`.

`FibreModel s c Z₁ y x'` is a **local model of the fibre product `Y ×_X X'` near `(y, x')`**: a space `W` of pairs
(`pY`, `pX`) covering the fibre product near `(y, x')`, local rings `B w` with structure maps `ψ w` from the new base,
the exceptional torsion `powerSat ⊥ (ψ g)`, base change of the old flatness (Hironaka Th. 2.5 / BC1), the readout of
the strict transform at points where the torsion lies in the closed fibre (a point of `Y'` over the pair, with
injective fibre map and flatness transfer), and the spreading of a torsion bound along `Z₁` (coherence).  From it:

* `torsion_le_maximal` — (i) at `x' ∈ T(Z)`: the torsion lies in the closed fibre (N5 = `HironakaG10NfN5.hN5`,
  base change of flatness, `powerSat_bot_le_map`);
* `torsion_le_Z₁` — the torsion lies in `J₁·B` (flatness of the strict family over `Z₁`, Nakayama
  `le_map_of_flat_of_le`);
* `fibreGood_of_model` — **the fibre comparison at all pairs near `(y, x')`**;
* `hfib_of_fibreModels` — the literal `hfib` binder from local models at the pairs over the centre.

No named input (the model is an explicit hypothesis of the last theorem; it is what the canonical charts provide).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10NfFibreModel

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

/-- **A local model of the fibre product `Y ×_X X'` near `(y, x')`** (what the canonical charts of the old family
and of the blowup provide, see `G10N5/STATUS.md`). -/
structure FibreModel (s : Stage) (c : AdmissibleCentre s.f) (Z₁ : LocalFlattener (nextWith s c).f)
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
  /-- the model covers the fibre product near `(y, x')` -/
  cover : ∀ U ∈ 𝓝 w₀, ∀ᶠ p in 𝓝 (y, x'),
    s.f.hom.left.base p.1 = (stepσ s c).hom.left.base p.2 → ∃ w ∈ U, pY w = p.1 ∧ pX w = p.2
  /-- the local ring of the fibre product at `w` -/
  B : W → Type
  [ring : ∀ w, CommRing (B w)]
  [noetherian : ∀ w, IsNoetherianRing (B w)]
  ψ : ∀ w, (nextWith s c).X.obj.left.presheaf.stalk (pX w) →+* B w
  local_ : ∀ w, Ideal.map (ψ w) (IsLocalRing.maximalIdeal _) ≤ Ideal.jacobson ⊥
  /-- a regular generator of the pulled centre -/
  g : ∀ w, (nextWith s c).X.obj.left.presheaf.stalk (pX w)
  g_regular : ∀ w, IsRegular (g w)
  span_g : ∀ w, Ideal.map ((stepσ s c).hom.left.stalkMap (pX w)).hom
    (centreIdeal c ((stepσ s c).hom.left.base (pX w))) = Ideal.span {g w}
  /-- base change of flatness of the old family (Hironaka Th. 2.5) -/
  flat_base : ∀ w (J : Ideal (s.X.obj.left.presheaf.stalk ((stepσ s c).hom.left.base (pX w)))),
    (quotMap (fibreStalkMap s.f _ (pY w) (square w)) J).Flat →
      (quotMap (ψ w) (Ideal.map ((stepσ s c).hom.left.stalkMap (pX w)).hom J)).Flat
  /-- the strict transform at a pair whose torsion lies in the closed fibre -/
  strict : ∀ w, powerSat (⊥ : Ideal (B w)) (ψ w (g w)) ≤ Ideal.map (ψ w) (IsLocalRing.maximalIdeal _) →
    ∃ (y'' : (nextWith s c).Y.obj.left) (_ : (stepQ s c).hom.left.base y'' = pY w)
      (hp : (nextWith s c).f.hom.left.base y'' = pX w),
      Ideal.comap ((stepQ s c).hom.left.stalkMap y'').hom (fibreIdealAt (nextWith s c).f y'') ≤
          fibreIdealAt s.f ((stepQ s c).hom.left.base y'') ∧
        ∀ J₁ : Ideal ((nextWith s c).X.obj.left.presheaf.stalk (pX w)),
          (quotMap (fibreStalkMap (nextWith s c).f (pX w) y'' hp) J₁).Flat →
            (quotMap ((Ideal.Quotient.mk (powerSat (⊥ : Ideal (B w)) (ψ w (g w)))).comp (ψ w)) J₁).Flat
  /-- a torsion bound by `Z₁` spreads (coherence) -/
  spread : powerSat (⊥ : Ideal (B w₀)) (ψ w₀ (g w₀)) ≤ Ideal.map (ψ w₀) (Z₁.H (pX w₀)) →
    ∀ᶠ w in 𝓝 w₀, powerSat (⊥ : Ideal (B w)) (ψ w (g w)) ≤ Ideal.map (ψ w) (Z₁.H (pX w))

attribute [instance] FibreModel.top FibreModel.ring FibreModel.noetherian

variable {s : Stage} {c : AdmissibleCentre s.f} {Z₁ : LocalFlattener (nextWith s c).f}
  {y : s.Y.obj.left} {x' : (nextWith s c).X.obj.left}

/-- **(i) at a point of `T(Z)`**: the exceptional torsion of the fibre product lies in the closed fibre. -/
theorem torsion_le_maximal (M : FibreModel s c Z₁ y x') (Z : LocalFlattener s.f)
    (hx' : M.pX M.w₀ ∈ transportedSupport s c Z) :
    powerSat (⊥ : Ideal (M.B M.w₀)) (M.ψ M.w₀ (M.g M.w₀)) ≤
      Ideal.map (M.ψ M.w₀) (IsLocalRing.maximalIdeal _) := by
  set w := M.w₀
  set J := germFlattener s.f ((stepσ s c).hom.left.base (M.pX w))
  have hflatY : (quotMap (fibreStalkMap s.f _ (M.pY w) (M.square w)) J).Flat :=
    ((isGermFlattenerAt_germFlattener s.f _) J).mpr le_rfl (M.pY w) (M.square w)
  have hflat := M.flat_base w J hflatY
  set J' := powerSat (Ideal.map ((stepσ s c).hom.left.stalkMap (M.pX w)).hom J) (M.g w)
  have hflat' : (quotMap (M.ψ w) J').Flat := flat_quotMap_of_le _ (le_powerSat _ _) hflat
  have hreg : IsRegular (Ideal.Quotient.mk J' (M.g w)) := isRegular_mk_powerSat _ _
  have hK := powerSat_bot_le_map (M.ψ w) J' (M.g w) hreg hflat'
  have hJ' : J' ≠ ⊤ := by
    have h1 := hx'.2 (M.g w) (M.g_regular w) (M.span_g w)
    rwa [Hironaka.Analytic.Unibranch.HironakaG10NfN5.hN5 s c (M.pX w) J (M.g w) (M.g_regular w) (M.span_g w)] at h1
  exact hK.trans (Ideal.map_mono (IsLocalRing.le_maximalIdeal hJ'))

/-- **The torsion lies in `J₁·B`** at `(y, x')` (flatness of the strict family over `Z₁` and Nakayama). -/
theorem torsion_le_Z₁ (M : FibreModel s c Z₁ y x') (Z : LocalFlattener s.f)
    (hx' : M.pX M.w₀ ∈ transportedSupport s c Z) (hx₁ : M.pX M.w₀ ∈ Z₁.support) :
    powerSat (⊥ : Ideal (M.B M.w₀)) (M.ψ M.w₀ (M.g M.w₀)) ≤
      Ideal.map (M.ψ M.w₀) (Z₁.H (M.pX M.w₀)) := by
  have hmax := torsion_le_maximal M Z hx'
  obtain ⟨y'', -, hp, -, htr⟩ := M.strict M.w₀ hmax
  have hfl : (quotMap (fibreStalkMap (nextWith s c).f (M.pX M.w₀) y'' hp) (Z₁.H (M.pX M.w₀))).Flat :=
    (Z₁.flattener _ hx₁.1 hx₁.2 (Z₁.H (M.pX M.w₀))).mpr le_rfl y'' hp
  exact le_map_of_flat_of_le (M.ψ M.w₀) _ _ (IsLocalRing.maximalIdeal _) hmax (M.local_ M.w₀)
    (htr _ hfl)

/-- **The fibre comparison at all pairs near `(y, x')`.** -/
theorem fibreGood_of_model (M : FibreModel s c Z₁ y x') (Z : LocalFlattener s.f)
    (hx' : x' ∈ transportedSupport s c Z) (hx₁ : x' ∈ Z₁.support) :
    ∀ᶠ p in 𝓝 (y, x'), FibreGood s c Z₁ p := by
  have hx'' : M.pX M.w₀ ∈ transportedSupport s c Z := by rw [M.pX_w₀]; exact hx'
  have hx₁' : M.pX M.w₀ ∈ Z₁.support := by rw [M.pX_w₀]; exact hx₁
  have hsp := M.spread (torsion_le_Z₁ M Z hx'' hx₁')
  filter_upwards [M.cover _ hsp] with p hp
  obtain ⟨a, b⟩ := p
  intro hb hab
  obtain ⟨w, hw, hwa, hwb⟩ := hp hab
  subst hwa
  subst hwb
  have hH : Z₁.H (M.pX w) ≤ IsLocalRing.maximalIdeal _ := IsLocalRing.le_maximalIdeal hb.2
  obtain ⟨y'', hq, hp', hinj, -⟩ := M.strict w (hw.trans (Ideal.map_mono hH))
  exact ⟨y'', hq, hp', hinj⟩

/-- **`hfib` (literal binder of `HironakaG10GlOffCentrePresentation.hT_of_presentation_centre`) from local models of
the fibre product at the pairs over the centre.** -/
theorem hfib_of_fibreModels
    (hmodel : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            (stepσ s c).hom.left.base x' ∈ nonunitLocus c.B c.b →
            ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base x' →
              Nonempty (FibreModel s c Z₁ y x')) :
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
  filter_upwards [fibreGood_of_model M Z hx' hx₁] with p hp _
  exact hp

end

end Hironaka.Analytic.Unibranch.HironakaG10NfFibreModel
