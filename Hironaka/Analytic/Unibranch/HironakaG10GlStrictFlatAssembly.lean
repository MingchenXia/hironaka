import Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction
import Hironaka.Analytic.Unibranch.HironakaG10SbStrictFlatAlgebra
import Hironaka.Analytic.Unibranch.HironakaG10SbQuotientFlat
import Hironaka.Analytic.Unibranch.HironakaG10HtStrictSaturation

/-!
# Lemma 4.4.5 (i) and the (G2) inclusion `σ^♯ I_Z ⊆ Z₁` from a pulled torsion presentation

Lane G10GL, run 0081, item GL-2 (`work/hironaka-run0081-20261117/G10GL/STATUS.md`).  Consumers: the `hi` and `hG2`
binders of `Hironaka.Analytic.Unibranch.HironakaG10SbLemma445.hT_of_strictFlat_of_upper`.  Source: Hironaka 1975, Lemma 4.4.5,
proof (printed pp. 537–538): `F₁ = F'/(f₁-torsion)`, "(F, f)/Z_p is flat and hence (F', f₁)/Z_p^* is also flat because a
base change preserves flatness … T induces an isomorphism (i) F'|Z_p^* ≅ F₁|Z_p^*".

A **pulled torsion presentation** (`PulledPresentation`) of the strict-transform family at a point `y''` of
`Y' = Bl_{f*B} Y` over `x' = f' y''` is the local ring `B₀` of the analytic fibre product `Y ×_X X'` at `(q y'', x')`
with its structure map `ψ : 𝒪_{X',x'} → B₀`, such that

* `𝒪_{Y',y''} ≅ B₀ ⧸ (ψ g-power torsion)` over `𝒪_{X',x'}`, for a generator `g` of the pulled centre (the strict
  transform is the total transform modulo its exceptional torsion, Hironaka (4.2.2), (4.3.1));
* the flattener of `ψ` is `σ^♯ P` for the pointed flattener `P` of `f` at `q y''` (Hironaka Th. 2.5 / (2.4.2): the
  flattener commutes with base change);
* `B₀` is noetherian and `𝔪_{x'} B₀` lies in its Jacobson radical (`ψ` is a local map of local rings).

With N5 (the algebraic strict ideal is `G`-saturated, lane G10HT, in its native form) this gives:

* `flat_strict_of_presentation` — **(i) at one point** (`quotMap_strict_flat_of_total`);
* `map_germFlattener_le_of_presentation` — **(hle)** at a point of `T(Z) ∩ |Z₁|` whose old fibre is covered
  by the strict transform (Nakayama: `quotMap_total_flat_of_strict`);
* `hi_of_presentation`, `hle_of_presentation`, `hG2_of_presentation`, `hT_of_presentation` — the binders of
  `hT_of_strictFlat_of_upper` (literal types), and `hT` itself, from N5, presentations at every point of the strict
  source, and the fibre comparison (hfib) of `HironakaG10GlLeavingContradiction`.

No named input: N5, the presentations and (hfib) are explicit hypotheses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GlStrictFlatAssembly

open Hironaka HironakaG10PNIdealFamily HironakaG10HirIdealGerms
  HironakaSingularModuleSheafStalk HironakaG10ChowArtinReesCentre HironakaG10HirFlatQuotient
  HironakaG10StrictIdealGenerator
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm Hironaka.Analytic.Unibranch.HironakaG10SbTransportClosed
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener Hironaka.Analytic.Unibranch.HironakaG10ActualBlowupStrictMembership
  Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation Hironaka.Analytic.Unibranch.HironakaG10SbStrictFlatAlgebra
  Hironaka.Analytic.Unibranch.HironakaG10SbQuotientFlat Hironaka.Analytic.Unibranch.HironakaG10HtStrictSaturation
  Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction Hironaka.Analytic.Unibranch.HironakaG10SbLemma445
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata

noncomputable section

/-! ### Algebra -/

/-- The exceptional torsion does not depend on the regular generator of the pulled centre. -/
theorem powerSat_bot_map_eq {A B : Type*} [CommRing A] [CommRing B] {g G : A} (hG : IsRegular G)
    (hspan : Ideal.span {G} = Ideal.span {g}) (ψ : A →+* B) :
    powerSat (⊥ : Ideal B) (ψ g) = powerSat (⊥ : Ideal B) (ψ G) := by
  obtain ⟨u, hu⟩ := exists_unit_mul_of_regular_span_eq hG hspan
  obtain ⟨v, hv⟩ := u.isUnit.map ψ
  rw [hu, map_mul, ← hv, powerSat_unit_mul]

/-! ### The square of one step, pointwise -/

theorem stepQ_comp_apply (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left) :
    s.f.hom.left.base ((stepQ s c).hom.left.base y'') =
      (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'') := by
  let _ := c.finiteType
  exact (strictP_comp_apply c.B c.b c.dense s.f y'').symm

/-- A regular local generator of the pulled centre exists at every point of the blowup. -/
theorem exists_regular_centre_generator (s : Stage) (c : AdmissibleCentre s.f)
    (x' : (nextWith s c).X.obj.left) :
    ∃ G : (nextWith s c).X.obj.left.presheaf.stalk x', IsRegular G ∧
      Ideal.map ((stepσ s c).hom.left.stalkMap x').hom (centreIdeal c ((stepσ s c).hom.left.base x')) =
        Ideal.span {G} := by
  let _ := c.finiteType
  obtain ⟨U, hxU, sG, hcrit⟩ := exists_local_projection_strict_criterion c.B c.b c.dense x'
  obtain ⟨hreg, hspan, -⟩ := hcrit x' hxU
  exact ⟨_, hreg, hspan⟩

/-- The pointed flattener lies in the whole-fibre flattener. -/
theorem pointFlattener_le_germFlattener {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (x : X.obj.left)
    (y : Y.obj.left) (h : f.hom.left.base y = x) (P : Ideal (X.obj.left.presheaf.stalk x))
    (hP : IsPointFlattenerAt f x y h P) : P ≤ germFlattener f x :=
  (hP _).mp ((isGermFlattenerAt_germFlattener f x _).mpr le_rfl y h)

/-! ### Pulled torsion presentations -/

/-- A **pulled torsion presentation** of the strict-transform family of one step at a point `y''` of the strict
source: the local ring `B` of the analytic fibre product `Y ×_X X'` at `(q y'', f' y'')` over `𝒪_{X',f' y''}`, whose
quotient by its exceptional torsion is the stalk of the strict transform (over `𝒪_{X',f' y''}`), whose flattener
is the pull-back of the pointed flattener of `f` at `q y''` (Hironaka Th. 2.5), noetherian, with `ψ` local. -/
structure PulledPresentation (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left) where
  /-- the local ring of the fibre product -/
  B : Type
  [ring : CommRing B]
  [noetherian : IsNoetherianRing B]
  /-- its structure map over the new base -/
  ψ : (nextWith s c).X.obj.left.presheaf.stalk ((nextWith s c).f.hom.left.base y'') →+* B
  /-- a generator of the pulled centre -/
  g : (nextWith s c).X.obj.left.presheaf.stalk ((nextWith s c).f.hom.left.base y'')
  span_g : Ideal.map ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y'')).hom
      (centreIdeal c ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y''))) = Ideal.span {g}
  /-- the strict-transform stalk is the fibre-product ring modulo its exceptional torsion -/
  β : B ⧸ powerSat (⊥ : Ideal B) (ψ g) ≃+* (nextWith s c).Y.obj.left.presheaf.stalk y''
  comm : ∀ a, β (Ideal.Quotient.mk _ (ψ a)) = ((nextWith s c).f.hom.left.stalkMap y'').hom a
  /-- base change of the pointed flattener (Hironaka Th. 2.5) -/
  flattener : ∀ (h : s.f.hom.left.base ((stepQ s c).hom.left.base y'') =
      (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y''))
    (P : Ideal (s.X.obj.left.presheaf.stalk
      ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'')))),
    IsPointFlattenerAt s.f _ ((stepQ s c).hom.left.base y'') h P →
      IsFlattenerIdeal ψ (Ideal.map ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y'')).hom P)
  /-- `ψ` is local: the closed fibre of the fibre product is that of `𝒪_{X',x'}` -/
  local_ : Ideal.map ψ (IsLocalRing.maximalIdeal _) ≤ Ideal.jacobson ⊥

attribute [instance] PulledPresentation.ring PulledPresentation.noetherian

variable {s : Stage} {c : AdmissibleCentre s.f}

/-- **Flatness transport along a presentation.**  Flatness of the strict family over `V(J)` at `y''` is flatness of
the fibre product modulo its exceptional torsion over `V(J)`. -/
theorem flat_iff_presentation {y'' : (nextWith s c).Y.obj.left} (P : PulledPresentation s c y'')
    (J : Ideal ((nextWith s c).X.obj.left.presheaf.stalk ((nextWith s c).f.hom.left.base y''))) :
    (quotMap (fibreStalkMap (nextWith s c).f _ y'' rfl) J).Flat ↔
      (quotMap ((Ideal.Quotient.mk (powerSat (⊥ : Ideal P.B) (P.ψ P.g))).comp P.ψ) J).Flat := by
  have hsq : (fibreStalkMap (nextWith s c).f _ y'' rfl).comp (RingHom.id _) =
      P.β.toRingHom.comp ((Ideal.Quotient.mk (powerSat (⊥ : Ideal P.B) (P.ψ P.g))).comp P.ψ) := by
    ext a
    exact (P.comm a).symm
  rw [quotMap_flat_iff_of_square _ (RingHom.id _) Function.surjective_id _ P.β hsq, Ideal.comap_id]

/-- The fibre product is flat over the germ strict transform when N5 holds there. -/
theorem flat_total_of_presentation {y'' : (nextWith s c).Y.obj.left} (P : PulledPresentation s c y'')
    (G : (nextWith s c).X.obj.left.presheaf.stalk ((nextWith s c).f.hom.left.base y''))
    (hN5 : strictIdeal ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y'')).hom
        (germFlattener s.f ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'')))
        (centreIdeal c ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y''))) G =
      powerSat (Ideal.map ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y'')).hom
        (germFlattener s.f ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'')))) G) :
    (quotMap P.ψ (strictIdeal ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y'')).hom
        (germFlattener s.f ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'')))
        (centreIdeal c ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y''))) G)).Flat := by
  have hy := stepQ_comp_apply s c y''
  obtain ⟨Py, hPy⟩ := exists_isPointFlattenerAt s.f _ _ hy
  refine (P.flattener hy Py hPy _).mpr ?_
  rw [hN5]
  exact (Ideal.map_mono (pointFlattener_le_germFlattener s.f _ _ hy Py hPy)).trans (le_powerSat _ G)

/-- **Hironaka's Lemma 4.4.5 (i) at one point of the strict source**, from a pulled torsion presentation and N5. -/
theorem flat_strict_of_presentation {y'' : (nextWith s c).Y.obj.left} (P : PulledPresentation s c y'')
    (G : (nextWith s c).X.obj.left.presheaf.stalk ((nextWith s c).f.hom.left.base y'')) (hG : IsRegular G)
    (hspan : Ideal.map ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y'')).hom
      (centreIdeal c ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y''))) = Ideal.span {G})
    (hN5 : strictIdeal ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y'')).hom
        (germFlattener s.f ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'')))
        (centreIdeal c ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y''))) G =
      powerSat (Ideal.map ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y'')).hom
        (germFlattener s.f ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'')))) G) :
    (quotMap (fibreStalkMap (nextWith s c).f _ y'' rfl)
      (strictIdeal ((stepσ s c).hom.left.stalkMap ((nextWith s c).f.hom.left.base y'')).hom
        (germFlattener s.f ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'')))
        (centreIdeal c ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y''))) G)).Flat := by
  have hreg : IsRegular (Ideal.Quotient.mk (strictIdeal ((stepσ s c).hom.left.stalkMap
      ((nextWith s c).f.hom.left.base y'')).hom
        (germFlattener s.f ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'')))
        (centreIdeal c ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y''))) G) G) := by
    rw [hN5]
    exact isRegular_mk_powerSat _ G
  have h1 := quotMap_strict_flat_of_total P.ψ _ G hreg (flat_total_of_presentation P G hN5)
  rw [← powerSat_bot_map_eq hG (hspan.symm.trans P.span_g) P.ψ] at h1
  exact (flat_iff_presentation P _).mpr h1

/-- **(hle) at one point** (the (G2) Nakayama core, Hironaka p. 538 (ii) at `t₀`): at a point `x' ∈ T(Z)` lying on a
local flattener `Z₁` of the strict-transform family, if the old fibre over `σ x'` is covered by the strict transform
and every point of the strict source over `x'` has a pulled torsion presentation, then `σ^♯ I_Z ⊆ Z₁` at `x'`. -/
theorem map_germFlattener_le_of_presentation (Z : LocalFlattener s.f) (x' : (nextWith s c).X.obj.left)
    (hx' : x' ∈ transportedSupport s c Z) (Z₁ : LocalFlattener (nextWith s c).f) (hx₁ : x' ∈ Z₁.support)
    (hN5 : ∀ G : (nextWith s c).X.obj.left.presheaf.stalk x', IsRegular G →
      Ideal.map ((stepσ s c).hom.left.stalkMap x').hom (centreIdeal c ((stepσ s c).hom.left.base x')) =
        Ideal.span {G} →
      strictIdeal ((stepσ s c).hom.left.stalkMap x').hom (germFlattener s.f ((stepσ s c).hom.left.base x'))
          (centreIdeal c ((stepσ s c).hom.left.base x')) G =
        powerSat (Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
          (germFlattener s.f ((stepσ s c).hom.left.base x'))) G)
    (hsurj : ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base x' →
      ∃ y'' : (nextWith s c).Y.obj.left, (stepQ s c).hom.left.base y'' = y ∧
        (nextWith s c).f.hom.left.base y'' = x')
    (hpres : ∀ y'' : (nextWith s c).Y.obj.left, (nextWith s c).f.hom.left.base y'' = x' →
      Nonempty (PulledPresentation s c y'')) :
    Ideal.map ((stepσ s c).hom.left.stalkMap x').hom (germFlattener s.f ((stepσ s c).hom.left.base x')) ≤
      Z₁.H x' := by
  obtain ⟨G, hG, hspan⟩ := exists_regular_centre_generator s c x'
  have hstrict := hx'.2 G hG hspan
  have hN := hN5 G hG hspan
  rw [Z₁.H_eq_germFlattener hx₁, Ideal.map_le_iff_le_comap]
  refine ((isGermFlattenerAt_germFlattener s.f _) _).mp fun y hy => ?_
  obtain ⟨y'', hq, hp⟩ := hsurj y hy
  obtain ⟨P⟩ := hpres y'' hp
  subst hp
  subst hq
  obtain ⟨Py, hPy⟩ := exists_isPointFlattenerAt s.f _ _ hy
  refine (hPy _).mpr ?_
  rw [← Ideal.map_le_iff_le_comap]
  refine (P.flattener hy Py hPy _).mp ?_
  have hreg : IsRegular (Ideal.Quotient.mk (strictIdeal ((stepσ s c).hom.left.stalkMap
      ((nextWith s c).f.hom.left.base y'')).hom
        (germFlattener s.f ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'')))
        (centreIdeal c ((stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y''))) G) G) := by
    rw [hN]
    exact isRegular_mk_powerSat _ G
  have hK := powerSat_bot_le_map P.ψ _ G hreg (flat_total_of_presentation P G hN)
  rw [← powerSat_bot_map_eq hG (hspan.symm.trans P.span_g) P.ψ] at hK
  have h𝔞 := (Ideal.map_mono (f := P.ψ) (IsLocalRing.le_maximalIdeal hstrict)).trans P.local_
  have hflat1 : (quotMap (fibreStalkMap (nextWith s c).f _ y'' rfl)
      (germFlattener (nextWith s c).f ((nextWith s c).f.hom.left.base y''))).Flat :=
    (isGermFlattenerAt_germFlattener (nextWith s c).f _ _).mpr le_rfl y'' rfl
  exact quotMap_total_flat_of_strict P.ψ _ _ _ hK h𝔞 ((flat_iff_presentation P _).mp hflat1)

/-! ### The binders of `hT_of_strictFlat_of_upper` -/

/-- **The `hi` binder of `HironakaG10SbLemma445.hT_of_strictFlat_of_upper`** (Hironaka's (i)), from N5 (G10HT's
native form) and pulled torsion presentations at every point of the strict source. -/
theorem hi_of_presentation
    (hN5 : ∀ (s : Stage) (c : AdmissibleCentre s.f) (x' : (nextWith s c).X.obj.left)
      (I : Ideal (s.X.obj.left.presheaf.stalk ((stepσ s c).hom.left.base x')))
      (G : (nextWith s c).X.obj.left.presheaf.stalk x'), IsRegular G →
      Ideal.map ((stepσ s c).hom.left.stalkMap x').hom (centreIdeal c ((stepσ s c).hom.left.base x')) =
        Ideal.span {G} →
      strictIdeal ((stepσ s c).hom.left.stalkMap x').hom I (centreIdeal c ((stepσ s c).hom.left.base x')) G =
        powerSat (Ideal.map ((stepσ s c).hom.left.stalkMap x').hom I) G)
    (hpres : ∀ (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left),
      Nonempty (PulledPresentation s c y'')) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ (U : Opens (nextWith s c).X.obj.left) (hxU : x' ∈ U)
            (sG : (nextWith s c).X.obj.left.presheaf.obj (op U)),
            IsRegular ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG) →
            Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
                (centreIdeal c ((stepσ s c).hom.left.base x')) =
              Ideal.span {(nextWith s c).X.obj.left.presheaf.germ U x' hxU sG} →
            FlatOverAt (nextWith s c).f x'
              (strictIdeal ((stepσ s c).hom.left.stalkMap x').hom
                (germFlattener s.f ((stepσ s c).hom.left.base x'))
                (centreIdeal c ((stepσ s c).hom.left.base x'))
                ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG)) := by
  intro s _ _ c _ _ _ _ x' _ U hxU sG hreg hspan y'' hp
  subst hp
  obtain ⟨P⟩ := hpres s c y''
  exact flat_strict_of_presentation P _ hreg hspan (hN5 s c _ _ _ hreg hspan)

/-- **The (hle) input of `HironakaG10GlLeavingContradiction.hG2_of_le_of_fibre`**, from N5, presentations and the
fibre comparison (hfib) (used at `x'` itself: the old fibre is covered by the strict transform). -/
theorem hle_of_presentation
    (hN5 : ∀ (s : Stage) (c : AdmissibleCentre s.f) (x' : (nextWith s c).X.obj.left)
      (I : Ideal (s.X.obj.left.presheaf.stalk ((stepσ s c).hom.left.base x')))
      (G : (nextWith s c).X.obj.left.presheaf.stalk x'), IsRegular G →
      Ideal.map ((stepσ s c).hom.left.stalkMap x').hom (centreIdeal c ((stepσ s c).hom.left.base x')) =
        Ideal.span {G} →
      strictIdeal ((stepσ s c).hom.left.stalkMap x').hom I (centreIdeal c ((stepσ s c).hom.left.base x')) G =
        powerSat (Ideal.map ((stepσ s c).hom.left.stalkMap x').hom I) G)
    (hpres : ∀ (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left),
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
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
              (germFlattener s.f ((stepσ s c).hom.left.base x')) ≤ Z₁.H x' := by
  intro s hc hp c β hβ hfl Z x' hx' Z₁ hx₁
  refine map_germFlattener_le_of_presentation Z x' hx' Z₁ hx₁ (hN5 s c x' _) (fun y hy => ?_)
    (fun y'' _ => hpres s c y'')
  obtain ⟨y'', hq, hp', -⟩ := (hfib s hc hp c β hβ hfl Z x' hx' Z₁ hx₁).self_of_nhds hx₁ y hy
  exact ⟨y'', hq, hp'⟩

/-- **The `hG2` binder of `HironakaG10SbLemma445.hT_of_strictFlat_of_upper`**, from N5, presentations and (hfib). -/
theorem hG2_of_presentation
    (hN5 : ∀ (s : Stage) (c : AdmissibleCentre s.f) (x' : (nextWith s c).X.obj.left)
      (I : Ideal (s.X.obj.left.presheaf.stalk ((stepσ s c).hom.left.base x')))
      (G : (nextWith s c).X.obj.left.presheaf.stalk x'), IsRegular G →
      Ideal.map ((stepσ s c).hom.left.stalkMap x').hom (centreIdeal c ((stepσ s c).hom.left.base x')) =
        Ideal.span {G} →
      strictIdeal ((stepσ s c).hom.left.stalkMap x').hom I (centreIdeal c ((stepσ s c).hom.left.base x')) G =
        powerSat (Ideal.map ((stepσ s c).hom.left.stalkMap x').hom I) G)
    (hpres : ∀ (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left),
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
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support → y' ∈ transportedSupport s c Z :=
  hG2_of_le_of_fibre (hle_of_presentation hN5 hpres hfib) hfib

/-- **`hT` (Hironaka's Lemma 4.4.5, literal binder of the final splice) from N5, pulled torsion presentations at every
point of the strict source, and the fibre comparison (hfib) along local flatteners.** -/
theorem hT_of_presentation
    (hN5 : ∀ (s : Stage) (c : AdmissibleCentre s.f) (x' : (nextWith s c).X.obj.left)
      (I : Ideal (s.X.obj.left.presheaf.stalk ((stepσ s c).hom.left.base x')))
      (G : (nextWith s c).X.obj.left.presheaf.stalk x'), IsRegular G →
      Ideal.map ((stepσ s c).hom.left.stalkMap x').hom (centreIdeal c ((stepσ s c).hom.left.base x')) =
        Ideal.span {G} →
      strictIdeal ((stepσ s c).hom.left.stalkMap x').hom I (centreIdeal c ((stepσ s c).hom.left.base x')) G =
        powerSat (Ideal.map ((stepσ s c).hom.left.stalkMap x').hom I) G)
    (hpres : ∀ (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left),
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
  hT_of_strictFlat_of_upper (hi_of_presentation hN5 hpres) (hG2_of_presentation hN5 hpres hfib)

end

end Hironaka.Analytic.Unibranch.HironakaG10GlStrictFlatAssembly
