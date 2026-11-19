import Hironaka.Analytic.Unibranch.HironakaG11CanonicalFirstStep
import Hironaka.Analytic.Unibranch.HironakaG11GluedWindowSteps
import Hironaka.Analytic.Unibranch.EmbeddedBlowupOverlap

/-!
# The strict transforms of `X` along the simultaneous canonical towers (goal G11, route step 5)

The iteration on `X` itself for the glued canonical towers of `HironakaG11CompatibleCanonicalTowers`,
parametric in the route invariant `R` (for the Hilbert–Samuel route: lane G11B's Bierstone–Milman
invariant, human decision (B')) and in the transport hypothesis `RecordsTransport`. Sources:
Bierstone–Milman 1997 §§1, 4 (the strict transforms `X_j ⊆ M_j` of `X` along the ambient blowup
sequences, centres in the maximal strata, which are cosupports of the presenting marked ideals);
Włodarczyk 2005, Proposition `pr: funct` (the lifted ambient isomorphisms of isomorphic towers).

* `strictAlong_restrict`, **`IsTowerIso.strictAlong_restrict_eq`**: strict transforms commute with
  the restriction of towers to opens, and correspond under isomorphisms of restricted towers over a
  biholomorphism `Φ : U' ≅ U` carrying `A' ∩ U'` onto `A ∩ U` (REPORT-r3 §6 item 4);
* `mapAdm`, `adm_exists_map`: the admissible overlap biholomorphisms (carrier-preserving AND
  compatible with the maps to `X`), which exist at every pair of carrier points with the same image
  (G11B's `exists_ambient_biholomorphism`);
* `XStage w T`: a stage of the strict-transform tower of `X` over towers `T i` of the window ambients:
  a complex space `Y`, a singular-centre modification `q : Y ⟶ X`, and open immersions of the strict
  transforms `strictAlong (T i) C_i` of the window carriers into `Y` over the window maps of `X`, with
  ranges the preimages of the windows; `XStage.zero` (`X` itself);
* **`XStage.map_lift`** (point identification: the lifted overlap biholomorphisms commute with the
  window maps of a stage, since `q` is an isomorphism over `Reg X`, whose preimage is dense),
  `XStage.mem_carrier_iff`, `XStage.exists_footprint`, `XStage.mem_gcentre_of_map_eq`;
* `XStage.centres` (the glued canonical centres as smooth centres on the manifold windows of a
  stage), `XStage.centres_compatible`, `XStage.isClosed_support`, **`XStage.exists_next`** (when the
  centres lie in the window carriers and in their singular loci, the global blowup of the glued
  centre, a singular-centre step following the given ambient blowups, carries the next `X`-stage);
* `CosuppInStrictSing R 𝔪` (along canonical towers the cosupports of the transformed records lie in
  the strict transforms of the window carriers and in their singular loci: for the Hilbert–Samuel
  records a consequence of the presentation property (3a)), `xstage` (the tower), `isIsoOver_xstage`;
* **`exists_resolving_strictTransform_tower`**: with transport and `CosuppInStrictSing`, canonical
  towers resolving all records, compatible over the admissible overlaps, and over them a stage `Y` of
  the strict-transform tower: `q : Y ⟶ X` a singular-centre modification (each step the blowup of a
  closed smooth glued centre in the singular locus of the previous stage), an isomorphism off the
  images of the cosupports;
* **`hasSingularCentreResolution_of_presentation`**: if moreover the records present the singular
  loci of the strict transforms (`hrev`) and the windows cover `Sing X`, then
  `HasSingularCentreResolution X` (the final stage is smooth).

The hypotheses are properties of the given local data (the records on the windows), not existence
statements about modifications of `X`; no named proposition equivalent to G11 is introduced and
nothing proves or assumes G11. Blueprint: `hironaka-g11-resume-strict-transform-towers.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11StrictTransformTowers

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences
  Hironaka HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSeq
  MarkedIdealBiholomorphism
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open _root_.Hironaka.BlowupTowerIsomorphism (IsTowerIso)
open _root_.Hironaka.HomogenizedGlueingTower (strictAlong)

noncomputable section

/-! ### Strict transforms along restricted towers -/

section Restrict

universe u

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Strict transforms commute with the restriction of a tower to an open subset.** -/
theorem strictAlong_restrict (U : Opens X) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → (A : Set X) →
    strictAlong (restrict U T) ((Subtype.val : U → X) ⁻¹' A) =
      (Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T A
  | _, .refl, _ => rfl
  | _, .step T C π hπ, A => by
    have ih := strictAlong_restrict U T A
    have hV := (openPreimage (BlowupTower.step T C π hπ) U).isOpen
    show BlowupStrictSubmanifold.geoStrictTransform _ ((↑) ⁻¹' C : Set (openPreimage T U))
        (strictAlong (restrict U T) ((Subtype.val : U → X) ⁻¹' A)) = _
    rw [ih]
    unfold BlowupStrictSubmanifold.geoStrictTransform
    rw [← preimage_sdiff, ← preimage_comp]
    show closure ((π ∘ (Subtype.val : openPreimage (BlowupTower.step T C π hπ) U → _)) ⁻¹'
      (strictAlong T A \ C)) = (Subtype.val : openPreimage (BlowupTower.step T C π hπ) U → _) ⁻¹'
        closure (π ⁻¹' (strictAlong T A \ C))
    rw [preimage_comp]
    exact ((hV.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage continuous_subtype_val _).symm

/-- **Strict transforms correspond under isomorphisms of restricted towers**: if `Φ : U' ≅ U` carries
`A' ∩ U'` onto `A ∩ U` and `χ` is the last-stage biholomorphism of an isomorphism of the restricted
towers over `Φ`, then `χ` carries the strict transform of `A'` (over `U'`) onto that of `A` (over `U`). -/
theorem IsTowerIso.strictAlong_restrict_eq {X' : CMfd.{u} n} {U : Opens X} {U' : Opens X'}
    {Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U}
    {Y Y' : CMfd.{u} n} {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    {χ : CMfd.of (n := n) (openPreimage T' U') ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U)}
    (h : IsTowerIso Φ (restrict U' T') (restrict U T) χ) {A : Set X} {A' : Set X'}
    (hA : Φ ⁻¹' ((Subtype.val : U → X) ⁻¹' A) = (Subtype.val : U' → X') ⁻¹' A') :
    χ ⁻¹' ((Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T A) =
      (Subtype.val : openPreimage T' U' → Y') ⁻¹' strictAlong T' A' := by
  have h1 := h.strictAlong_eq ((Subtype.val : U → X) ⁻¹' A)
  rw [hA, strictAlong_restrict, strictAlong_restrict] at h1
  exact h1.symm

end Restrict

/-! ### Overlap biholomorphisms compatible with the maps to `X` -/

section Adm

variable {X : SourceReducedComplexSpace} {N : ℕ} {ι : Type*}

/-- **The admissible overlap biholomorphisms of the gluing**: carrier-preserving biholomorphisms
`Φ : U' ≅ U` of opens of two window ambients which are compatible with the maps of the windows to `X`. -/
def mapAdm (w : ι → DimEmbedding X N) (i j : ι) (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
    (Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U) :
    Prop :=
  carrierAdm w i j U U' Φ ∧
    ∀ (p : U') (hp : (p : (w j).ambient) ∈ (w j).carrier)
      (hq : ((Φ p : U) : (w i).ambient) ∈ (w i).carrier),
      (w i).toLocalEmbedding.toPoint ⟨_, hq⟩ = (w j).toLocalEmbedding.toPoint ⟨_, hp⟩

theorem mapAdm_carrier {w : ι → DimEmbedding X N} {i j : ι} {U : Opens (w i).ambient}
    {U' : Opens (w j).ambient}
    {Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U}
    (h : mapAdm w i j U U' Φ) :
    Φ ⁻¹' ((Subtype.val : U → (w i).ambient) ⁻¹' (w i).carrier) =
      (Subtype.val : U' → (w j).ambient) ⁻¹' (w j).carrier :=
  ext fun p => h.1 p

/-- **Admissible overlap biholomorphisms exist at all pairs of carrier points with the same image**
(G11B's `exists_ambient_biholomorphism`, which is compatible with the maps to `X`). -/
theorem adm_exists_map (w : ι → DimEmbedding X N) (i j : ι) (c : (w i).carrier) (c' : (w j).carrier)
    (h : (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c) :
    ∃ (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
      (Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U)
      (hc' : c'.val ∈ U') (hc : c.val ∈ U), Φ ⟨c'.val, hc'⟩ = ⟨c.val, hc⟩ ∧ mapAdm w i j U U' Φ := by
  obtain ⟨A, B, hA, hB, Φ, hzA, hΦz, hcar, hpt⟩ :=
    HironakaG11InvLocalEmbeddingIso.exists_ambient_biholomorphism (w j).toLocalEmbedding
      (w i).toLocalEmbedding rfl c' c h
  let Ψ : CMfd.of (n := N) (MaxLocusLocal.nestedOpens (w j).ambient A) ≃ₘ⟮𝓘(ℂ, ComplexModel N),
      𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) (MaxLocusLocal.nestedOpens (w i).ambient B) :=
    (MaxLocusLocal.nestedOpensDiffeo (n := N) hA).trans
      (Φ.trans (MaxLocusLocal.nestedOpensDiffeo (n := N) hB).symm)
  have hΨ : ∀ p : MaxLocusLocal.nestedOpens (w j).ambient A,
      (((Ψ p : MaxLocusLocal.nestedOpens (w i).ambient B) : (w i).ambient) : ComplexModel N) =
        (Φ ⟨((p : (w j).ambient) : ComplexModel N), p.property⟩ : ComplexModel N) := fun _ => rfl
  have hΨC : ∀ p : MaxLocusLocal.nestedOpens (w j).ambient A,
      ((Ψ p : MaxLocusLocal.nestedOpens (w i).ambient B) : (w i).ambient) ∈ (w i).carrier ↔
        (p : (w j).ambient) ∈ (w j).carrier := by
    intro p
    rw [← HironakaG11InvMinimalAmbient.val_mem_coordinateCarrier_iff (w i).carrier, hΨ,
      ← HironakaG11InvMinimalAmbient.val_mem_coordinateCarrier_iff (w j).carrier]
    exact (hcar ⟨((p : (w j).ambient) : ComplexModel N), p.property⟩).symm
  have hcB : c.val ∈ MaxLocusLocal.nestedOpens (w i).ambient B := by
    show ((c.val : (w i).ambient) : ComplexModel N) ∈ B
    rw [← hΦz]
    exact (Φ _).property
  refine ⟨MaxLocusLocal.nestedOpens (w i).ambient B, MaxLocusLocal.nestedOpens (w j).ambient A, Ψ, hzA,
    hcB, ?_, hΨC, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    rw [hΨ]
    exact hΦz
  · intro p hp hq
    obtain ⟨z, hz, hzp⟩ := hpt ⟨(p : (w j).ambient), hp⟩ p.property
    have hzq : (⟨((Ψ p : MaxLocusLocal.nestedOpens (w i).ambient B) : (w i).ambient), hq⟩ :
        (w i).carrier) = z := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hΨ]
      exact hz.symm
    rw [hzq]
    exact hzp

end Adm

/-! ### The strict transforms of `X` along simultaneous ambient towers -/

section XStage

variable {X : SourceReducedComplexSpace} {N : ℕ} {ι : Type*}

variable (w : ι → DimEmbedding X N) in
/-- **A stage of the strict-transform tower of `X`** over towers `T i` of the window ambients: a
complex space `Y` with a singular-centre modification `q : Y ⟶ X`, and for every window an open
immersion of the strict transform of the window carrier (a closed analytic subset of the last stage of
`T i`) into `Y`, over the window map of `X` (`square`), with range the preimage of the window. -/
structure XStage (T : Towers w) where
  /-- The space. -/
  Y : SourceReducedComplexSpace
  /-- The composite modification to `X`. -/
  q : Y ⟶ X
  isSingularCentreModification : HironakaG11SingularCentreModification.IsSingularCentreModification q
  /-- The window carriers. -/
  carrier : ∀ i, Set (T i).1
  analytic : ∀ i, IsComplexAnalyticSubset (n := N) (carrier i)
  /-- The window maps. -/
  map : ∀ i, SourceReducedComplexSpace.ofClosedAnalytic (carrier i) (analytic i) ⟶ Y
  isOpenImmersion : ∀ i, LocallyRingedSpace.IsOpenImmersion (map i).hom.left
  carrier_eq : ∀ i, carrier i = strictAlong (T i).2 (w i).carrier
  square : ∀ i (c : carrier i) (hc : (T i).2.proj c.val ∈ (w i).carrier),
    q.hom.left.base ((map i).hom.left.base c) = (w i).toLocalEmbedding.toPoint ⟨_, hc⟩
  range_map : ∀ i, range (map i).hom.left.base =
    q.hom.left.base ⁻¹' range (w i).toLocalEmbedding.toPoint

variable {w : ι → DimEmbedding X N}

/-- The empty towers over the window ambients. -/
abbrev reflTowers (w : ι → DimEmbedding X N) : Towers w := fun i => ⟨Amb w i, .refl⟩

variable (w) in
/-- **Stage `0`**: `X` itself with its windows. -/
def XStage.zero : XStage w (reflTowers w) where
  Y := X
  q := 𝟙 X
  isSingularCentreModification := .id X
  carrier i := (w i).carrier
  analytic i := (w i).analytic
  map i := EmbeddedBlowupOverlap.chartMorphism (w i).toLocalEmbedding
  isOpenImmersion i := (w i).isOpenImmersion
  carrier_eq _ := rfl
  square _ _ _ := rfl
  range_map _ := rfl

namespace XStage

variable {T : Towers w} (xs : XStage w T)

theorem proj_mem (i : ι) (c : xs.carrier i) : (T i).2.proj c.val ∈ (w i).carrier := by
  have hc : c.val ∈ strictAlong (T i).2 (w i).carrier := xs.carrier_eq i ▸ c.property
  exact MemberInterTowerAlong.strictAlong_subset_preimage (T i).2 (w i).analytic.isClosed hc

/-- The window maps of a stage are injective. -/
theorem map_injective (i : ι) : Function.Injective (xs.map i).hom.left.base :=
  (xs.isOpenImmersion i).base_open.injective

variable {i j : ι} {U : Opens (w i).ambient} {U' : Opens (w j).ambient}
  {Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U}
  {χ : CMfd.of (n := N) (openPreimage (T j).2 U') ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯
    CMfd.of (n := N) (openPreimage (T i).2 U)}

/-- **The window carriers correspond under the lifted overlap biholomorphisms.** -/
theorem mem_carrier_iff (hΦ : mapAdm w i j U U' Φ)
    (hiso : IsTowerIso Φ (restrict U' (T j).2) (restrict U (T i).2) χ)
    (p : openPreimage (T j).2 U') :
    ((χ p : openPreimage (T i).2 U) : (T i).1) ∈ xs.carrier i ↔ (p : (T j).1) ∈ xs.carrier j := by
  have h := IsTowerIso.strictAlong_restrict_eq (X := Amb w i) (X' := Amb w j) hiso (mapAdm_carrier hΦ)
  have hp := congrArg (fun S => p ∈ S) h
  simp only [mem_preimage, eq_iff_iff] at hp
  rw [xs.carrier_eq i, xs.carrier_eq j]
  exact hp

/-- **Point identification**: the lifted overlap biholomorphisms commute with the window maps of the
stage (the composite to `X` is an isomorphism over the regular locus, whose preimage is dense). -/
theorem map_lift (hΦ : mapAdm w i j U U' Φ)
    (hiso : IsTowerIso Φ (restrict U' (T j).2) (restrict U (T i).2) χ)
    (c : xs.carrier j) (hc : c.val ∈ openPreimage (T j).2 U')
    (hmem : ((χ ⟨c.val, hc⟩ : openPreimage (T i).2 U) : (T i).1) ∈ xs.carrier i) :
    (xs.map i).hom.left.base ⟨_, hmem⟩ = (xs.map j).hom.left.base c := by
  let A : Set (xs.carrier j) := {c | c.val ∈ openPreimage (T j).2 U'}
  have hAmem : ∀ a : A, a.val.val ∈ openPreimage (T j).2 U' := fun a => a.property
  have hAo : IsOpen A := (openPreimage (T j).2 U').isOpen.preimage continuous_subtype_val
  have hmemA : ∀ a : A,
      ((χ ⟨a.val.val, hAmem a⟩ : openPreimage (T i).2 U) : (T i).1) ∈ xs.carrier i :=
    fun a => (xs.mem_carrier_iff hΦ hiso ⟨a.val.val, hAmem a⟩).mpr a.val.property
  let fa : A → xs.carrier i := fun a => ⟨_, hmemA a⟩
  have hfa : Continuous fa :=
    (continuous_subtype_val.comp (χ.continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))).subtype_mk _
  have hbo : IsOpenMap (fun a : A => (xs.map j).hom.left.base a.val) :=
    (xs.isOpenImmersion j).base_open.isOpenMap.comp hAo.isOpenMap_subtype_val
  have hab := HironakaG11LiftUniqueness.eq_of_comp_eq_of_isOpenMap
    xs.isSingularCentreModification.isIsoOver_intrinsicRegularLocus
    xs.isSingularCentreModification.interior_preimage_intrinsicSingularLocus
    (a := fun a : A => (xs.map i).hom.left.base (fa a))
    (b := fun a : A => (xs.map j).hom.left.base a.val)
    ((xs.map i).hom.left.base.hom.continuous.comp hfa)
    ((xs.map j).hom.left.base.hom.continuous.comp continuous_subtype_val) hbo (fun a => ?_)
  · exact congrFun hab ⟨c, hc⟩
  · rw [xs.square i (fa a) (xs.proj_mem i (fa a)), xs.square j a.val (xs.proj_mem j a.val)]
    have h1 := hiso.proj_comm ⟨a.val.val, hAmem a⟩
    have h2 := proj_restrict U (T i).2 (χ ⟨a.val.val, hAmem a⟩)
    have h3 := proj_restrict U' (T j).2 ⟨a.val.val, hAmem a⟩
    set p' := (restrict U' (T j).2).proj ⟨a.val.val, hAmem a⟩ with hp'
    have hp'C : (p' : (w j).ambient) ∈ (w j).carrier := by
      rw [h3]
      exact xs.proj_mem j a.val
    have hΦp' : ((Φ p' : U) : (w i).ambient) = (T i).2.proj (fa a).val := by
      rw [h1, h2]
    have hq : ((Φ p' : U) : (w i).ambient) ∈ (w i).carrier := by
      rw [hΦp']
      exact xs.proj_mem i (fa a)
    have h4 := hΦ.2 p' hp'C hq
    have e1 : (⟨(T i).2.proj (fa a).val, xs.proj_mem i (fa a)⟩ : (w i).carrier) =
        ⟨((Φ p' : U) : (w i).ambient), hq⟩ := Subtype.ext hΦp'.symm
    have e2 : (⟨(T j).2.proj a.val.val, xs.proj_mem j a.val⟩ : (w j).carrier) =
        ⟨(p' : (w j).ambient), hp'C⟩ := Subtype.ext h3.symm
    rw [e1, e2]
    exact h4

end XStage

end XStage

/-! ### One step: blow up the glued canonical centres of a stage -/

section Step

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ] {ι : Type*}
  {R : ResolutionInvariant.{0} N k Λ} {w : ι → DimEmbedding X N} {𝔪 : ∀ i, MarkedIdeal N (Amb w i)}
  {K : ∀ i, Set (w i).ambient}
  (hD : ∀ i, IsInvDomain k (𝔪 i)) (hcos : ∀ i, (𝔪 i).cosupp ⊆ (w i).carrier)
  (hcover : ∀ i (c : (w i).carrier), c.val ∈ (𝔪 i).cosupp → ∃ j, ∃ c' : (w j).carrier,
    c'.val ∈ K j ∧ (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c)
  (hTr : RecordsTransport R 𝔪 (mapAdm w))

namespace XStage

/-- **The glued canonical centres of a stage** as smooth centres on the manifold windows of an
`X`-stage (when they lie in the window carriers). -/
def centres {m : ℕ} (s : GStage R 𝔪 (mapAdm w) m) (xs : XStage w s.T)
    (hsub : ∀ i, gcentre R 𝔪 K s.T i ⊆ xs.carrier i) :
    HironakaG11ManifoldWindowCentres.ManifoldSmoothCentres xs.Y ι where
  dim _ := N
  ambient i := (s.T i).1
  carrier := xs.carrier
  analytic := xs.analytic
  map := xs.map
  isOpenImmersion := xs.isOpenImmersion
  centre i := gcentre R 𝔪 K s.T i
  isClosedSubmanifold i := (gnextMap_isBlowup hD hcos hcover (adm_exists_map w) hTr s i).1
  centre_subset := hsub

include hD hcos hcover hTr in
/-- **Every cosupport point of a stage window is identified with one over a footprint**, with the
same membership in the glued centre. -/
theorem exists_footprint {m : ℕ} (s : GStage R 𝔪 (mapAdm w) m) (xs : XStage w s.T) (i : ι)
    (y : xs.carrier i) (hy : y.val ∈ rcos 𝔪 s.T i) :
    ∃ (j : ι) (z : xs.carrier j), (s.T j).2.proj z.val ∈ K j ∧
      (xs.map j).hom.left.base z = (xs.map i).hom.left.base y ∧
      (z.val ∈ gcentre R 𝔪 K s.T j ↔ y.val ∈ gcentre R 𝔪 K s.T i) := by
  have hTt := R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ (s.canonical i)
  have hx : (s.T i).2.proj y.val ∈ (𝔪 i).cosupp :=
    StepOneLowerDomain.proj_mem_cosupp_of_mem_cosupp
      (hD i).isWellFormed.isClosedSubmanifold_N (hD i).isWellFormed.isCoherent _ hTt hy
  obtain ⟨j, c', hc'K, hc'⟩ := hcover i ⟨_, hcos i hx⟩ hx
  obtain ⟨U, U', Ψ, hc'U', hxU, hΨc, hadm⟩ := adm_exists_map w i j ⟨_, hcos i hx⟩ c' hc'
  obtain ⟨χ, hiso⟩ := s.compatible i j U U' Ψ hadm
  let q : openPreimage (s.T i).2 U := ⟨y.val, hxU⟩
  have hχp : χ (χ.symm q) = q := χ.apply_symm_apply q
  have hzc : ((χ.symm q : openPreimage (s.T j).2 U') : (s.T j).1) ∈ xs.carrier j := by
    rw [← xs.mem_carrier_iff hadm hiso, hχp]
    exact y.property
  have hproj : (s.T j).2.proj (χ.symm q).val = c'.val := by
    have h1 := hiso.proj_comm (χ.symm q)
    rw [hχp] at h1
    have h2 := proj_restrict U (s.T i).2 q
    have h3 : (restrict U' (s.T j).2).proj (χ.symm q) = ⟨c'.val, hc'U'⟩ :=
      Ψ.injective (h1.trans ((show (restrict U (s.T i).2).proj q = ⟨(s.T i).2.proj y.val, hxU⟩ from
        Subtype.ext h2).trans hΨc.symm))
    have h4 := proj_restrict U' (s.T j).2 (χ.symm q)
    rw [h3] at h4
    exact h4.symm
  have hmem : ((χ ⟨(χ.symm q).val, (χ.symm q).property⟩ : openPreimage (s.T i).2 U) : (s.T i).1) ∈
      xs.carrier i := by
    rw [hχp]
    exact y.property
  have hpt := xs.map_lift hadm hiso ⟨_, hzc⟩ (χ.symm q).property hmem
  have hey' : ((χ (χ.symm q) : openPreimage (s.T i).2 U) : (s.T i).1) = y.val := congrArg Subtype.val hχp
  have hey : (⟨_, hmem⟩ : xs.carrier i) = y := Subtype.ext hey'
  refine ⟨j, ⟨_, hzc⟩, ?_, ?_, ?_⟩
  · show (s.T j).2.proj (χ.symm q).val ∈ K j
    rw [hproj]
    exact hc'K
  · rw [← hpt, hey]
  · have hg := gcentre_preimage (K := K) hTr s i j U U' Ψ hadm hiso
    have h2 := congrArg (fun S => χ.symm q ∈ S) hg
    simp only [mem_preimage, eq_iff_iff] at h2
    rw [hχp] at h2
    exact h2.symm

include hTr in
/-- **The glued centres of an `X`-stage are compatible**: two window points with the same image in
the stage lie together in the glued centres or not (point identification + transport). -/
theorem mem_gcentre_of_map_eq {m : ℕ} (s : GStage R 𝔪 (mapAdm w) m) (xs : XStage w s.T) {i j : ι}
    (y : xs.carrier i) (z : xs.carrier j)
    (hyz : (xs.map i).hom.left.base y = (xs.map j).hom.left.base z)
    (hy : y.val ∈ gcentre R 𝔪 K s.T i) : z.val ∈ gcentre R 𝔪 K s.T j := by
  have hyp := xs.proj_mem i y
  have hzp := xs.proj_mem j z
  have hX : (w j).toLocalEmbedding.toPoint ⟨_, hzp⟩ = (w i).toLocalEmbedding.toPoint ⟨_, hyp⟩ := by
    rw [← xs.square j z hzp, ← xs.square i y hyp, hyz]
  obtain ⟨U, U', Φ, hc', -, -, hadm⟩ := adm_exists_map w i j ⟨_, hyp⟩ ⟨_, hzp⟩ hX
  obtain ⟨χ, hiso⟩ := s.compatible i j U U' Φ hadm
  have hzU : z.val ∈ openPreimage (s.T j).2 U' := hc'
  have hmem := (xs.mem_carrier_iff hadm hiso ⟨z.val, hzU⟩).mpr z.property
  have hpt := xs.map_lift hadm hiso z hzU hmem
  have hχz : ((χ ⟨z.val, hzU⟩ : openPreimage (s.T i).2 U) : (s.T i).1) = y.val :=
    congrArg Subtype.val (xs.map_injective i (hpt.trans hyz.symm))
  have hg := gcentre_preimage (K := K) hTr s i j U U' Φ hadm hiso
  have h2 := congrArg (fun S => (⟨z.val, hzU⟩ : openPreimage (s.T j).2 U') ∈ S) hg
  simp only [mem_preimage, eq_iff_iff] at h2
  exact h2.mp (by rw [hχz]; exact hy)

include hTr in
theorem centres_compatible {m : ℕ} (s : GStage R 𝔪 (mapAdm w) m) (xs : XStage w s.T)
    (hsub : ∀ i, gcentre R 𝔪 K s.T i ⊆ xs.carrier i) :
    (xs.centres hD hcos hcover hTr s hsub).Compatible := by
  intro i j y z hyz hy
  exact xs.mem_gcentre_of_map_eq hTr s (i := i) (j := j) y z hyz hy

include hTr in
/-- **The glued centre of an `X`-stage is closed** (it lies over the compact footprints). -/
theorem isClosed_support [Finite ι] (hK : ∀ i, IsCompact (K i)) {m : ℕ}
    (s : GStage R 𝔪 (mapAdm w) m) (xs : XStage w s.T)
    (hsub : ∀ i, gcentre R 𝔪 K s.T i ⊆ xs.carrier i) :
    IsClosed (xs.centres hD hcos hcover hTr s hsub).support := by
  apply (xs.centres hD hcos hcover hTr s hsub).isClosed_support_of_finite
    (xs.centres_compatible hD hcos hcover hTr s hsub) (fun i => (xs.map i).hom.left.base ''
      ((Subtype.val : xs.carrier i → (s.T i).1) ⁻¹' (gcentre R 𝔪 K s.T i ∩ (s.T i).2.proj ⁻¹' K i)))
  · intro i
    have hgc : IsClosed (gcentre R 𝔪 K s.T i) :=
      (gnextMap_isBlowup hD hcos hcover (adm_exists_map w) hTr s i).1.1
    have hcpt : IsCompact (gcentre R 𝔪 K s.T i ∩ (s.T i).2.proj ⁻¹' K i) :=
      ((HironakaLocalPrincipalization.isProperMap_proj (s.T i).2).isCompact_preimage (hK i)).inter_left hgc
    have hcpt' : IsCompact ((Subtype.val : xs.carrier i → (s.T i).1) ⁻¹'
        (gcentre R 𝔪 K s.T i ∩ (s.T i).2.proj ⁻¹' K i)) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hcpt (fun y hy => ⟨⟨y, hsub i hy.1⟩, rfl⟩)
    exact hcpt'.image (xs.map i).hom.left.base.hom.continuous
  · rintro i _ ⟨c, -, rfl⟩
    exact ⟨c, rfl⟩
  · intro x hx
    obtain ⟨i, y, hy, rfl⟩ := (xs.centres hD hcos hcover hTr s hsub).mem_support.mp hx
    have hy' : (y : xs.carrier i).val ∈ gcentre R 𝔪 K s.T i := hy
    obtain ⟨j, z, hzK, hzy, hzc⟩ := xs.exists_footprint hD hcos hcover hTr s i y hy'.1
    exact mem_iUnion.mpr ⟨j, z, ⟨hzc.mpr hy', hzK⟩, hzy⟩

include hTr in
/-- **One step of the strict-transform tower.** If the glued centres of a stage lie in the window
carriers and in the singular loci of the windows, the global blowup of the glued centre of the
`X`-stage (a singular-centre step, an isomorphism off the glued centre) carries an `X`-stage over the
next stage of the glued canonical towers. -/
theorem exists_next [Finite ι] (hK : ∀ i, IsCompact (K i)) {m : ℕ}
    (s : GStage R 𝔪 (mapAdm w) m) (xs : XStage w s.T)
    (hsub : ∀ i, gcentre R 𝔪 K s.T i ⊆ xs.carrier i)
    (hsing : ∀ i (c : xs.carrier i), c.val ∈ gcentre R 𝔪 K s.T i →
      c ∈ HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus
        (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj) :
    ∃ (xs' : XStage w (s.next hD hcos hcover (adm_exists_map w) hTr).T) (p : xs'.Y ⟶ xs.Y),
      xs'.q = p ≫ xs.q ∧ HironakaG11SingularCentreModification.IsSingularCentreStep p ∧
      SourceReducedComplexSpace.IsIsoOver p (xs.centres hD hcos hcover hTr s hsub).supportᶜ := by
  set F := xs.centres hD hcos hcover hTr s hsub with hF
  have hc := xs.centres_compatible hD hcos hcover hTr s hsub
  have hcl := xs.isClosed_support hD hcos hcover hTr hK s hsub
  have hS : F.support ⊆ HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus xs.Y.obj :=
    F.support_subset_intrinsicSingularLocus_iff.mpr fun i c hc => hsing i c hc
  obtain ⟨-, Y', p, -, hstep, -, -, hiso, L, hL⟩ :=
    HironakaG11GluedWindowSteps.exists_singularCentreBlowup_given_blowups F hc hcl hS
      (fun i => gnextSpace hD hcos hcover (adm_exists_map w) hTr s i)
      (fun i => gnextMap hD hcos hcover (adm_exists_map w) hTr s i)
      (fun i => gnextMap_isBlowup hD hcos hcover (adm_exists_map w) hTr s i)
  refine ⟨{ Y := Y'
            q := p ≫ xs.q
            isSingularCentreModification :=
              .cons p xs.q hstep xs.isSingularCentreModification
            carrier := fun i => strictTransform N (gnextMap hD hcos hcover (adm_exists_map w) hTr s i)
              (xs.carrier i)
            analytic := fun i =>
              HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
                (gnextMap_isBlowup hD hcos hcover (adm_exists_map w) hTr s i) (xs.analytic i)
            map := L
            isOpenImmersion := fun i => (hL i).1
            carrier_eq := fun i => ?_
            square := fun i c hc => ?_
            range_map := fun i => ?_ }, p, rfl, hstep, hiso⟩
  · show _ = BlowupStrictSubmanifold.geoStrictTransform _ _ (strictAlong (s.T i).2 (w i).carrier)
    rw [← xs.carrier_eq i]
    exact (BlowupStrictIdeal.geoStrictTransform_eq_strictTransform
      (gnextMap_isBlowup hD hcos hcover (adm_exists_map w) hTr s i)
      (HironakaG11WindowTowers.ManifoldSmoothCentres.carrier_subset_closure_diff F hS i)).symm
  · have h1 := congrArg (fun f => f.hom.left.base c) (hL i).2.1
    change xs.q.hom.left.base (p.hom.left.base ((L i).hom.left.base c)) = _
    change p.hom.left.base ((L i).hom.left.base c) =
      (F.map i).hom.left.base ((EmbeddedBlowup.strictTransformMorphism (gnextMap_isBlowup hD hcos hcover
        (adm_exists_map w) hTr s i) (F.analytic i)).hom.left.base c) at h1
    rw [h1]
    exact xs.square i ((EmbeddedBlowup.strictTransformMorphism (gnextMap_isBlowup hD hcos hcover
        (adm_exists_map w) hTr s i) (F.analytic i)).hom.left.base c) hc
  · refine (hL i).2.2.trans ?_
    ext y
    change p.hom.left.base y ∈ range (xs.map i).hom.left.base ↔
      xs.q.hom.left.base (p.hom.left.base y) ∈ range (w i).toLocalEmbedding.toPoint
    rw [xs.range_map i]
    rfl

end XStage

end Step

/-! ### The strict-transform tower along the glued canonical towers -/

section Tower

/-- **Singular points correspond along an equality of carriers.** -/
theorem mem_intrinsicSingularLocus_congr {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {A B : Set M} (h : A = B)
    (hA : IsComplexAnalyticSubset (n := n) A) (hB : IsComplexAnalyticSubset (n := n) B) (c : A) :
    c ∈ HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus
        (SourceReducedComplexSpace.ofClosedAnalytic A hA).obj ↔
      (⟨c.val, h ▸ c.property⟩ : B) ∈ HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus
        (SourceReducedComplexSpace.ofClosedAnalytic B hB).obj := by
  subst h
  rfl

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ] {ι : Type*}
  {w : ι → DimEmbedding X N}

variable (R : ResolutionInvariant.{0} N k Λ) (𝔪 : ∀ i, MarkedIdeal N (Amb w i)) in
/-- **The cosupports lie in the singular loci of the strict transforms**: along every canonical tower
of a window record, the cosupport of the transformed record lies in the strict transform of the window
carrier and consists of singular points of it (for the Hilbert–Samuel records: the cosupport is the
maximal Hilbert–Samuel stratum of the strict transform, property (3a)). -/
def CosuppInStrictSing : Prop :=
  ∀ i {Y : CMfd.{0} N} (T : BlowupTower (Amb w i) Y), IsCanonical (𝔪 i) (R.inv (𝔪 i)) T →
    (geoTransformAlong (𝔪 i) T).cosupp ⊆ strictAlong T (w i).carrier ∧
    ∀ (hA : IsComplexAnalyticSubset (n := N) (strictAlong T (w i).carrier))
      (c : strictAlong T (w i).carrier), c.val ∈ (geoTransformAlong (𝔪 i) T).cosupp →
      c ∈ HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus
        (SourceReducedComplexSpace.ofClosedAnalytic (strictAlong T (w i).carrier) hA).obj

variable (w) in
/-- The images in `X` of the cosupports of the window records. -/
def cosuppImage (𝔪 : ∀ i, MarkedIdeal N (Amb w i)) : Set X.obj.left :=
  {x | ∃ i, ∃ c : (w i).carrier, c.val ∈ (𝔪 i).cosupp ∧ (w i).toLocalEmbedding.toPoint c = x}

variable {R : ResolutionInvariant.{0} N k Λ} {𝔪 : ∀ i, MarkedIdeal N (Amb w i)}
  {K : ∀ i, Set (w i).ambient}
  (hD : ∀ i, IsInvDomain k (𝔪 i)) (hcos : ∀ i, (𝔪 i).cosupp ⊆ (w i).carrier)
  (hcover : ∀ i (c : (w i).carrier), c.val ∈ (𝔪 i).cosupp → ∃ j, ∃ c' : (w j).carrier,
    c'.val ∈ K j ∧ (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c)
  (hTr : RecordsTransport R 𝔪 (mapAdm w))

theorem CosuppInStrictSing.gcentre_subset (hP : CosuppInStrictSing R 𝔪) {m : ℕ}
    (s : GStage R 𝔪 (mapAdm w) m) (xs : XStage w s.T) (i : ι) :
    gcentre R 𝔪 K s.T i ⊆ xs.carrier i := fun _ hy => by
  rw [xs.carrier_eq i]
  exact (hP i (s.T i).2 (s.canonical i)).1 hy.1

theorem CosuppInStrictSing.mem_sing (hP : CosuppInStrictSing R 𝔪) {m : ℕ}
    (s : GStage R 𝔪 (mapAdm w) m) (xs : XStage w s.T) (i : ι) (c : xs.carrier i)
    (hc : c.val ∈ gcentre R 𝔪 K s.T i) :
    c ∈ HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus
      (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj := by
  have h := xs.carrier_eq i
  rw [mem_intrinsicSingularLocus_congr h (xs.analytic i) (h ▸ xs.analytic i)]
  exact (hP i (s.T i).2 (s.canonical i)).2 _ _ hc.1

variable [Finite ι] (hK : ∀ i, IsCompact (K i)) (hP : CosuppInStrictSing R 𝔪)

variable (K) in
/-- **The strict-transform tower of `X`**: an `X`-stage over every stage of the glued canonical
towers of the records. -/
def xstage : (m : ℕ) → XStage w (gstage R 𝔪 (mapAdm w) K hD hcos hcover (adm_exists_map w) hTr m).T
  | 0 => XStage.zero w
  | m + 1 => (XStage.exists_next hD hcos hcover hTr hK (gstage R 𝔪 (mapAdm w) K hD hcos hcover
      (adm_exists_map w) hTr m) (xstage m) (hP.gcentre_subset _ (xstage m))
      (hP.mem_sing _ (xstage m))).choose

theorem xstage_succ (m : ℕ) :
    ∃ p : (xstage K hD hcos hcover hTr hK hP (m + 1)).Y ⟶ (xstage K hD hcos hcover hTr hK hP m).Y,
      (xstage K hD hcos hcover hTr hK hP (m + 1)).q = p ≫ (xstage K hD hcos hcover hTr hK hP m).q ∧
      HironakaG11SingularCentreModification.IsSingularCentreStep p ∧
      SourceReducedComplexSpace.IsIsoOver p ((xstage K hD hcos hcover hTr hK hP m).centres hD hcos
        hcover hTr (gstage R 𝔪 (mapAdm w) K hD hcos hcover (adm_exists_map w) hTr m)
        (hP.gcentre_subset _ (xstage K hD hcos hcover hTr hK hP m))).supportᶜ :=
  (XStage.exists_next hD hcos hcover hTr hK (gstage R 𝔪 (mapAdm w) K hD hcos hcover
      (adm_exists_map w) hTr m) (xstage K hD hcos hcover hTr hK hP m) (hP.gcentre_subset _ _)
      (hP.mem_sing _ _)).choose_spec

include hD hcos hcover hTr hK in
/-- The images of the cosupports form a closed subset of `X` (they lie over the compact footprints). -/
theorem isClosed_cosuppImage : IsClosed (cosuppImage w 𝔪) := by
  let : T2Space X.obj.left := X.property.1
  have heq : cosuppImage w 𝔪 = ⋃ j, (w j).toLocalEmbedding.toPoint ''
      ((Subtype.val : (w j).carrier → (w j).ambient) ⁻¹' ((𝔪 j).cosupp ∩ K j)) := by
    ext x
    constructor
    · rintro ⟨i, c, hc, rfl⟩
      obtain ⟨j, c', hc'K, hc'⟩ := hcover i c hc
      have hc'c := (HironakaG11CanonicalFirstStep.first_transport (adm_exists_map w) hTr i j c c' hc'
        hc).1
      exact mem_iUnion.mpr ⟨j, c', ⟨hc'c, hc'K⟩, hc'⟩
    · intro hx
      obtain ⟨j, c, hc, rfl⟩ := mem_iUnion.mp hx
      exact ⟨j, c, hc.1, rfl⟩
  rw [heq]
  refine (isCompact_iUnion fun j => ?_).isClosed
  have hSc : IsClosed (𝔪 j).cosupp :=
    GiraudAlong.isClosed_cosupport_along (hD j).isWellFormed.isCoherent
      (hD j).isWellFormed.isClosedSubmanifold_N _
  have hcpt : IsCompact ((Subtype.val : (w j).carrier → (w j).ambient) ⁻¹' ((𝔪 j).cosupp ∩ K j)) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' ((hK j).inter_left hSc)
      (fun y hy => ⟨⟨y, hcos j hy.1⟩, rfl⟩)
  exact hcpt.image (w j).toLocalEmbedding.isOpenEmbedding_toPoint.continuous

omit [Finite ι] in
include hD in
/-- The glued centre of a stage lies over the images of the cosupports. -/
theorem support_subset_cosuppImage {m : ℕ} (s : GStage R 𝔪 (mapAdm w) m) (xs : XStage w s.T)
    (hsub : ∀ i, gcentre R 𝔪 K s.T i ⊆ xs.carrier i) :
    (xs.centres hD hcos hcover hTr s hsub).support ⊆ xs.q.hom.left.base ⁻¹' cosuppImage w 𝔪 := by
  intro x hx
  obtain ⟨i, y, hy, rfl⟩ := (xs.centres hD hcos hcover hTr s hsub).mem_support.mp hx
  have hy' : (y : xs.carrier i).val ∈ gcentre R 𝔪 K s.T i := hy
  have hTt := R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ (s.canonical i)
  have hpc : (s.T i).2.proj (y : xs.carrier i).val ∈ (𝔪 i).cosupp :=
    StepOneLowerDomain.proj_mem_cosupp_of_mem_cosupp
      (hD i).isWellFormed.isClosedSubmanifold_N (hD i).isWellFormed.isCoherent _ hTt hy'.1
  exact ⟨i, ⟨_, xs.proj_mem i y⟩, hpc, (xs.square i y (xs.proj_mem i y)).symm⟩

include hD hcos hcover hTr hK hP in
/-- **The strict-transform tower is an isomorphism off the images of the cosupports.** -/
theorem isIsoOver_xstage : ∀ m : ℕ,
    SourceReducedComplexSpace.IsIsoOver (xstage K hD hcos hcover hTr hK hP m).q (cosuppImage w 𝔪)ᶜ
  | 0 => SourceReducedComplexSpace.IsIsoOver.id_of_isOpen X
      (isClosed_cosuppImage hD hcos hcover hTr hK).isOpen_compl
  | m + 1 => by
    obtain ⟨p, hq, -, hiso⟩ := xstage_succ hD hcos hcover hTr hK hP m
    rw [hq]
    refine SourceReducedComplexSpace.IsIsoOver.comp (isIsoOver_xstage m) (hiso.of_isOpen_subset
      ((isClosed_cosuppImage hD hcos hcover hTr hK).isOpen_compl.preimage
        (xstage K hD hcos hcover hTr hK hP m).q.hom.left.base.hom.continuous) ?_)
    intro x hx hxS
    exact hx (support_subset_cosuppImage hD hcos hcover hTr _ _ _ hxS)

include hD hcos hcover hTr hK hP in
/-- **The strict transforms of `X` along the glued canonical towers (one Hilbert–Samuel phase).**
For finitely many windows of one ambient dimension with records whose values transport along the
admissible overlaps (`RecordsTransport`), compact footprints covering the images of the cosupports, and
cosupports in the singular loci of the strict transforms along canonical towers (`CosuppInStrictSing`):
there are canonical towers of all records, of one length, resolving the records, compatible over the
admissible overlaps, and over them an `X`-stage: a singular-centre modification `q : Y ⟶ X`
(composite of blowups of the glued centres, each a closed smooth centre in the singular locus) with
open immersions of the strict transforms of the window carriers over the window maps, covering the
preimages of the windows; `q` is an isomorphism off the images of the cosupports. -/
theorem exists_resolving_strictTransform_tower [WellFoundedLT Λ] :
    ∃ (m : ℕ) (T : Towers w) (xs : XStage w T),
      (∀ i, (T i).2.length = m) ∧ (∀ i, IsCanonical (𝔪 i) (R.inv (𝔪 i)) (T i).2) ∧
      (∀ i, IsGeoResolution (𝔪 i) (T i).2) ∧ AdmCompatible (mapAdm w) T ∧
      SourceReducedComplexSpace.IsIsoOver xs.q (cosuppImage w 𝔪)ᶜ := by
  obtain ⟨m, hm⟩ := exists_gstage_cosupp_eq_empty hD hcos hcover (adm_exists_map w) hTr hK
  set s := gstage R 𝔪 (mapAdm w) K hD hcos hcover (adm_exists_map w) hTr m
  exact ⟨m, s.T, xstage K hD hcos hcover hTr hK hP m, s.length, s.canonical,
    fun i => ⟨R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ (s.canonical i), hm i⟩, s.compatible,
    isIsoOver_xstage hD hcos hcover hTr hK hP m⟩

include hD hcos hcover hTr hK hP in
/-- **The final stage is smooth when the records present the singular loci.** If moreover, along
canonical towers, every singular point of the strict transform of a window carrier lies in the
cosupport of the transformed record, and the windows cover the singular locus of `X`, then `X` has a
resolution by blowups with smooth centres in the singular loci (`HasSingularCentreResolution`). -/
theorem hasSingularCentreResolution_of_presentation [WellFoundedLT Λ]
    (hrev : ∀ i {Y : CMfd.{0} N} (T : BlowupTower (Amb w i) Y), IsCanonical (𝔪 i) (R.inv (𝔪 i)) T →
      ∀ (hA : IsComplexAnalyticSubset (n := N) (strictAlong T (w i).carrier))
        (c : strictAlong T (w i).carrier),
        c ∈ HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus
          (SourceReducedComplexSpace.ofClosedAnalytic (strictAlong T (w i).carrier) hA).obj →
        c.val ∈ (geoTransformAlong (𝔪 i) T).cosupp)
    (hSing : HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus X.obj ⊆
      ⋃ i, range (w i).toLocalEmbedding.toPoint) :
    HironakaG11SingularCentreModification.HasSingularCentreResolution X := by
  obtain ⟨m, T, xs, -, hcan, hres, -, -⟩ :=
    exists_resolving_strictTransform_tower hD hcos hcover hTr hK hP
  refine ⟨xs.Y, xs.q, xs.isSingularCentreModification, ?_⟩
  rw [OriginalIntrinsicSingularLocus.isSmooth_iff_intrinsicSingularLocus_eq_empty]
  refine eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  by_cases hw : ∃ i, y ∈ range (xs.map i).hom.left.base
  · obtain ⟨i, c, rfl⟩ := hw
    have hc : c ∈ HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus
        (SourceReducedComplexSpace.ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj := by
      rw [← HironakaG11CompatibleAnalyticCover.preimage_intrinsicSingularLocus_of_isOpenImmersion
        (xs.map i) (xs.isOpenImmersion i)]
      exact hy
    have h := xs.carrier_eq i
    rw [mem_intrinsicSingularLocus_congr h (xs.analytic i) (h ▸ xs.analytic i)] at hc
    have hmem := hrev i (T i).2 (hcan i) _ _ hc
    rw [(hres i).2] at hmem
    exact hmem
  · push Not at hw
    have hqy : xs.q.hom.left.base y ∉
        HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus X.obj := by
      intro hqs
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hSing hqs)
      have : y ∈ range (xs.map i).hom.left.base := by
        rw [xs.range_map i]
        exact hi
      exact hw i this
    have hreg : xs.q.hom.left.base y ∈
        HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicRegularLocus X.obj := by
      by_contra h'
      exact hqy h'
    exact hy (xs.isSingularCentreModification.preimage_intrinsicRegularLocus_subset hreg)

end Tower




end

end Hironaka.Analytic.Unibranch.HironakaG11StrictTransformTowers
