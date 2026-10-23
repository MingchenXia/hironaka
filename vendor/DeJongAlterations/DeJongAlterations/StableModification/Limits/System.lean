import DeJongAlterations.StableModification.RiemannZariski.Scheme
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# The system of quasi-alterations approximating a valuation ring

Let `A` be a ring, `L` a field with an `A`-algebra structure and `V` a valuation ring of `L`
containing the image of `A`. The finitely generated `A`-subalgebras `B ⊆ V` of `L` form a directed
system whose union is `V`. Hence `V` is the filtered colimit of the rings `B`, and `Spec V` is the
cofiltered limit of the affine schemes `Spec B`, with affine transition maps. Each `Spec B` is of
finite type over `Spec A` and integral, the morphism `Spec L → Spec B` is induced by the inclusion
`B ⊆ L`, and when `L` is algebraic over `A` each `B` is algebraic over `A`; so for `A = Γ(S, U)`
the affine open of an integral scheme `S` with generic point `Spec K → S`, and `L = K^s`, the
`Spec B` are affine `K^s`-quasi-alterations of `S` in Temkin's sense. The closed point of `Spec V`
maps to the center `𝔪_V ∩ B` of `V` on `B`, and `V` is also the directed union of the local rings
`B_{𝔪_V ∩ B}` (the local rings of the `Spec B` at the centers).

This is the approximation lemma of Temkin, *Stable modification of relative curves*
(J. Algebraic Geom. 19 (2010); arXiv v3 numbering), Lemma 3.2.2 (`approxlem`), in the equal
characteristic form used for the de Jong interface: the base is of finite type over a field, so no
approximation over `ℤ` (Temkin §3.1, [TT, C.9]) is needed, and the approximating schemes are the
affine quasi-alterations `Spec B` (simplification S0/S3 of the plan `PLAN-SM-GEOM`).

## Main definitions

* `Limits.subalgebraDiagram F`: the diagram of rings `i ↦ F i` of a monotone family of subalgebras.
* `Limits.subalgebraCocone F R hF`, `Limits.subalgebraSpecCone F R hF`: the cocone to `R` and the
  cone `Spec R → Spec (F i)`.
* `Limits.FGSubalgebra R`: the directed set of finitely generated `A`-subalgebras contained in `R`.
* `Limits.valuationSubalgebra V`: a valuation ring `V ∈ RZ(A)` as an `A`-subalgebra of `L`.
* `Limits.centerOf V B`: the center of `V` on `B`, a prime of `B`.
* `Limits.localSubalgebra V B`: the local ring `B_{𝔪_V ∩ B}`, as an `A`-subalgebra of `L`.

## Main results

* `Limits.isColimitSubalgebraCocone`, `Limits.isLimitSubalgebraSpecCone`: a directed union of
  subalgebras is a filtered colimit of rings, and its spectrum is the limit of the spectra.
* `Limits.isColimitFGCocone`, `Limits.isLimitFGSpecCone`: `R` is the filtered colimit of its
  finitely generated `A`-subalgebras, and `Spec R` the cofiltered limit of their spectra.
* `Limits.specClosedPoint_map_eq_center`: the closed point of `Spec V` maps to the center.
* `Limits.isLocalization_localSubalgebra`, `Limits.isColimitLocalCocone`,
  `Limits.isLimitLocalSpecCone`: `V` is the directed union of the local rings at the centers.
* `Limits.locallyOfFiniteType_specMap`, `Limits.isAlgebraic_of_isAlgebraic`: each `Spec B` is of
  finite type over `Spec A`, and algebraic over `A` when `L` is.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace DeJongAlterations.StableModification.Limits

/-! ### Directed unions of subalgebras -/

section DirectedUnion

variable {A L : Type u} [CommRing A] [CommRing L] [Algebra A L]
variable {ι : Type u} [Preorder ι] (F : ι →o Subalgebra A L)

/-- The diagram of rings `i ↦ F i` of a monotone family of subalgebras, with the inclusions as
transition maps. -/
@[simps]
noncomputable def subalgebraDiagram : ι ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (F i)
  map {i j} f := CommRingCat.ofHom (Subalgebra.inclusion (F.monotone f.le)).toRingHom

variable (R : Subalgebra A L) (hF : ∀ i, F i ≤ R)

/-- The cocone of inclusions `F i ⊆ R`. -/
@[simps]
noncomputable def subalgebraCocone : Cocone (subalgebraDiagram F) where
  pt := CommRingCat.of R
  ι := { app i := CommRingCat.ofHom (Subalgebra.inclusion (hF i)).toRingHom }

/-- The cone `Spec R → Spec (F i)` over the diagram of spectra. -/
noncomputable abbrev subalgebraSpecCone : Cone ((subalgebraDiagram F).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (subalgebraCocone F R hF).op

variable [IsDirected ι (· ≤ ·)] [Nonempty ι]

/-- **Directed unions are filtered colimits.** If `R` is the union of the directed family of
subalgebras `F i`, then `R` is the colimit of the rings `F i`. -/
noncomputable def isColimitSubalgebraCocone (hR : ∀ x ∈ R, ∃ i, x ∈ F i) :
    IsColimit (subalgebraCocone F R hF) := by
  have : ReflectsColimitsOfShape ι (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat) ?_
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    obtain ⟨i, hi⟩ := hR x.1 x.2
    exact ⟨i, (⟨x.1, hi⟩ : F i), rfl⟩
  · intro i j xi xj h
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, homOfLE hik, homOfLE hjk, ?_⟩
    exact Subtype.ext (congrArg Subtype.val h :)

/-- The spectrum of a directed union of subalgebras is the cofiltered limit of their spectra. -/
noncomputable def isLimitSubalgebraSpecCone (hR : ∀ x ∈ R, ∃ i, x ∈ F i) :
    IsLimit (subalgebraSpecCone F R hF) :=
  isLimitOfPreserves Scheme.Spec (isColimitSubalgebraCocone F R hF hR).op

instance {i j : ιᵒᵖ} (f : i ⟶ j) :
    IsAffineHom (((subalgebraDiagram F).op ⋙ Scheme.Spec).map f) := by
  dsimp
  infer_instance

instance (i : ιᵒᵖ) : IsAffine (((subalgebraDiagram F).op ⋙ Scheme.Spec).obj i) := by
  dsimp
  infer_instance

end DirectedUnion

/-! ### Finitely generated subalgebras -/

section FG

variable {A L : Type u} [CommRing A] [CommRing L] [Algebra A L]

variable (A) in
/-- The finitely generated `A`-subalgebras of `L` contained in `R`, ordered by inclusion. -/
abbrev FGSubalgebra (R : Subalgebra A L) : Type u :=
  {B : Subalgebra A L // B.FG ∧ B ≤ R}

variable {R : Subalgebra A L}

instance : IsDirected (FGSubalgebra A R) (· ≤ ·) :=
  ⟨fun B B' => ⟨⟨B.1 ⊔ B'.1, B.2.1.sup B'.2.1, sup_le B.2.2 B'.2.2⟩, le_sup_left (a := B.1),
    le_sup_right (a := B.1)⟩⟩

instance : OrderBot (FGSubalgebra A R) where
  bot := ⟨⊥, Subalgebra.fg_bot, bot_le⟩
  bot_le B := bot_le (a := B.1)

instance : Nonempty (FGSubalgebra A R) := ⟨⊥⟩

variable (R) in
/-- The inclusion of the finitely generated subalgebras into all subalgebras. -/
@[simps]
def fgSubalgebraFamily : FGSubalgebra A R →o Subalgebra A L :=
  ⟨Subtype.val, fun _ _ h => h⟩

lemma fgSubalgebraFamily_le (B : FGSubalgebra A R) : fgSubalgebraFamily R B ≤ R :=
  B.2.2

/-- Every finite subset of `R` is contained in a finitely generated subalgebra contained in `R`
and containing a given one. -/
lemma exists_finset_subset (s : Finset L) (hs : (s : Set L) ⊆ R) (B₀ : FGSubalgebra A R) :
    ∃ B : FGSubalgebra A R, B₀ ≤ B ∧ (s : Set L) ⊆ B.1 := by
  refine ⟨⟨B₀.1 ⊔ Algebra.adjoin A (s : Set L), B₀.2.1.sup (Subalgebra.fg_adjoin_finset s),
    sup_le B₀.2.2 ((Algebra.adjoin_le_iff).2 hs)⟩, le_sup_left (a := B₀.1), ?_⟩
  exact (Algebra.subset_adjoin).trans (le_sup_right (a := B₀.1) :)

lemma exists_mem {x : L} (hx : x ∈ R) : ∃ B : FGSubalgebra A R, x ∈ B.1 := by
  classical
  obtain ⟨B, -, hB⟩ := exists_finset_subset {x} (by simpa using hx) ⊥
  exact ⟨B, hB (by simp)⟩

variable (R) in
/-- The diagram of the finitely generated `A`-subalgebras of `R`. -/
noncomputable abbrev fgDiagram : FGSubalgebra A R ⥤ CommRingCat.{u} :=
  subalgebraDiagram (fgSubalgebraFamily R)

variable (R) in
/-- The cocone of inclusions `B ⊆ R` over the finitely generated subalgebras. -/
noncomputable abbrev fgCocone : Cocone (fgDiagram R) :=
  subalgebraCocone (fgSubalgebraFamily R) R fgSubalgebraFamily_le

variable (R) in
/-- The cone `Spec R → Spec B` over the finitely generated subalgebras `B ⊆ R`. -/
noncomputable abbrev fgSpecCone : Cone ((fgDiagram R).op ⋙ Scheme.Spec) :=
  subalgebraSpecCone (fgSubalgebraFamily R) R fgSubalgebraFamily_le

variable (R) in
/-- **`R` is the filtered colimit of its finitely generated subalgebras.** -/
noncomputable def isColimitFGCocone : IsColimit (fgCocone R) :=
  isColimitSubalgebraCocone _ _ _ fun _ hx => exists_mem hx

variable (R) in
/-- **`Spec R` is the cofiltered limit of the spectra of the finitely generated subalgebras of
`R`**, with affine transition maps (Temkin 2010, Lemma 3.2.2). -/
noncomputable def isLimitFGSpecCone : IsLimit (fgSpecCone R) :=
  isLimitSubalgebraSpecCone _ _ _ fun _ hx => exists_mem hx

/-- Each `Spec B` is of finite type over `Spec A`. -/
lemma locallyOfFiniteType_specMap (B : FGSubalgebra A R) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A B.1))) := by
  have : Algebra.FiniteType A B.1 := (Subalgebra.fg_iff_finiteType _).1 B.2.1
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.2 inferInstance

end FG

/-! ### Valuation rings: centers and local rings -/

section Valuation

variable {A L : Type u} [CommRing A] [Field L] [Algebra A L]

/-- A valuation ring `V ∈ RZ(A)` of `L`, regarded as an `A`-subalgebra of `L`. -/
def valuationSubalgebra (V : RiemannZariskiSpace.ofAlgebra A L) : Subalgebra A L :=
  { V.1.valuationSubring.toSubring with
    algebraMap_mem' := RiemannZariskiSpace.mem_ofAlgebra.1 V.2 }

variable (V : RiemannZariskiSpace.ofAlgebra A L)

@[simp]
lemma mem_valuationSubalgebra {x : L} :
    x ∈ valuationSubalgebra V ↔ x ∈ V.1.valuationSubring :=
  Iff.rfl

instance : IsLocalRing (valuationSubalgebra V) :=
  inferInstanceAs (IsLocalRing V.1.valuationSubring)

instance : ValuationRing (valuationSubalgebra V) :=
  inferInstanceAs (ValuationRing V.1.valuationSubring)

/-- The system of finitely generated `A`-subalgebras `B ⊆ V` of `L` approximating the valuation
ring `V` (Temkin 2010, Lemma 3.2.2): `V` is their filtered colimit (`isColimitFGCocone`) and
`Spec V` the cofiltered limit of the affine schemes `Spec B` (`isLimitFGSpecCone`). -/
abbrev QASystem : Type u := FGSubalgebra A (valuationSubalgebra V)

/-- For a subalgebra `B ⊆ V`, the valuation ring `V` as a point of `RZ(B)`. -/
def toOfAlgebra (B : Subalgebra A L) (hB : B ≤ valuationSubalgebra V) :
    RiemannZariskiSpace.ofAlgebra B L :=
  ⟨V.1, RiemannZariskiSpace.mem_ofAlgebra.2 fun b => hB b.2⟩

/-- The center `𝔪_V ∩ B` of `V` on a subalgebra `B ⊆ V`, a prime ideal of `B`. -/
noncomputable def centerOf (B : Subalgebra A L) (hB : B ≤ valuationSubalgebra V) :
    PrimeSpectrum B :=
  RiemannZariskiSpace.center (toOfAlgebra V B hB)

lemma mem_centerOf {B : Subalgebra A L} {hB : B ≤ valuationSubalgebra V} {b : B} :
    b ∈ (centerOf V B hB).asIdeal ↔ (b : L) ∈ V.1.valuationSubring.nonunits :=
  RiemannZariskiSpace.mem_center

/-- **The closed point of `Spec V` maps to the center.** Under `Spec V → Spec B`, the closed point
of `Spec V` is sent to the center `𝔪_V ∩ B` of `V` on `B`. -/
theorem specClosedPoint_map_eq_center (B : Subalgebra A L) (hB : B ≤ valuationSubalgebra V) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hB).toRingHom)
      (IsLocalRing.closedPoint (valuationSubalgebra V)) = centerOf V B hB := by
  apply PrimeSpectrum.ext
  ext b
  change Subalgebra.inclusion hB b ∈ IsLocalRing.maximalIdeal (valuationSubalgebra V) ↔ _
  rw [mem_centerOf, IsLocalRing.mem_maximalIdeal]
  exact (ValuationSubring.coe_mem_nonunits_iff (A := V.1.valuationSubring)
    (a := ⟨b, hB b.2⟩)).symm

private lemma not_mem_nonunits_one : (1 : L) ∉ V.1.valuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]
  simp

private lemma not_mem_nonunits_mul {s t : L} (hsV : s ∈ V.1.valuationSubring)
    (htV : t ∈ V.1.valuationSubring)
    (hs : s ∉ V.1.valuationSubring.nonunits) (ht : t ∉ V.1.valuationSubring.nonunits) :
    s * t ∉ V.1.valuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, not_lt] at hs ht ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at hsV htV
  have h1 := le_antisymm hsV hs
  have h2 := le_antisymm htV ht
  rw [map_mul, h1, h2, one_mul]

/-- The local ring `B_{𝔪_V ∩ B}` of `B` at the center of `V`, realized inside `L`: the elements
`x` with `s x ∈ B` for some `s ∈ B ∖ 𝔪_V`. -/
def localSubalgebra (B : Subalgebra A L) (hB : B ≤ valuationSubalgebra V) : Subalgebra A L where
  carrier := {x | ∃ s ∈ B, s ∉ V.1.valuationSubring.nonunits ∧ s * x ∈ B}
  mul_mem' := by
    rintro x y ⟨s, hs, hsu, hsx⟩ ⟨t, ht, htu, hty⟩
    refine ⟨s * t, B.mul_mem hs ht, not_mem_nonunits_mul V (hB hs) (hB ht) hsu htu, ?_⟩
    convert B.mul_mem hsx hty using 1
    ring
  one_mem' := ⟨1, B.one_mem, not_mem_nonunits_one V, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hsu, hsx⟩ ⟨t, ht, htu, hty⟩
    refine ⟨s * t, B.mul_mem hs ht, not_mem_nonunits_mul V (hB hs) (hB ht) hsu htu, ?_⟩
    convert B.add_mem (B.mul_mem ht hsx) (B.mul_mem hs hty) using 1
    ring
  zero_mem' := ⟨1, B.one_mem, not_mem_nonunits_one V, by simp⟩
  algebraMap_mem' a := ⟨1, B.one_mem, not_mem_nonunits_one V, by simp⟩

variable {V} {B : Subalgebra A L} {hB : B ≤ valuationSubalgebra V}

lemma mem_localSubalgebra {x : L} :
    x ∈ localSubalgebra V B hB ↔ ∃ s ∈ B, s ∉ V.1.valuationSubring.nonunits ∧ s * x ∈ B :=
  Iff.rfl

variable (V B hB) in
lemma le_localSubalgebra : B ≤ localSubalgebra V B hB :=
  fun x hx => ⟨1, B.one_mem, not_mem_nonunits_one V, by simpa using hx⟩

variable (V B hB) in
/-- The local ring `B_{𝔪_V ∩ B}` is contained in `V`. -/
lemma localSubalgebra_le : localSubalgebra V B hB ≤ valuationSubalgebra V := by
  rintro x ⟨s, hs, hsu, hsx⟩
  have hsV : s ∈ V.1.valuationSubring := hB hs
  have hv : V.1.valuationSubring.valuation s = 1 := by
    rw [ValuationSubring.mem_nonunits_iff, not_lt] at hsu
    exact le_antisymm ((ValuationSubring.valuation_le_one_iff _ _).2 hsV) hsu
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hv
  have hinv : s⁻¹ ∈ V.1.valuationSubring := by
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hv, inv_one]
  have : x = s⁻¹ * (s * x) := by field_simp
  rw [this]
  exact V.1.valuationSubring.mul_mem _ _ hinv (hB hsx)

lemma localSubalgebra_mono {B' : Subalgebra A L} {hB' : B' ≤ valuationSubalgebra V}
    (h : B ≤ B') : localSubalgebra V B hB ≤ localSubalgebra V B' hB' := by
  rintro x ⟨s, hs, hsu, hsx⟩
  exact ⟨s, h hs, hsu, h hsx⟩

variable (V B hB) in
/-- **The local ring at the center.** `localSubalgebra V B hB` is the localization of `B` at the
center `𝔪_V ∩ B` of `V`, i.e. the local ring of `Spec B` at the image of the closed point of
`Spec V`. -/
theorem isLocalization_localSubalgebra :
    letI : Algebra B (localSubalgebra V B hB) :=
      (Subalgebra.inclusion (le_localSubalgebra V B hB)).toRingHom.toAlgebra
    IsLocalization.AtPrime (localSubalgebra V B hB) (centerOf V B hB).asIdeal := by
  let : Algebra B (localSubalgebra V B hB) :=
    (Subalgebra.inclusion (le_localSubalgebra V B hB)).toRingHom.toAlgebra
  rw [IsLocalization.AtPrime, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    have hsu : (s : L) ∉ V.1.valuationSubring.nonunits := fun h => hs ((mem_centerOf V).2 h)
    have hsV : (s : L) ∈ V.1.valuationSubring := hB s.2
    have hv : V.1.valuationSubring.valuation s = 1 := by
      rw [ValuationSubring.mem_nonunits_iff, not_lt] at hsu
      exact le_antisymm ((ValuationSubring.valuation_le_one_iff _ _).2 hsV) hsu
    have hs0 : (s : L) ≠ 0 := by
      intro h0
      rw [h0] at hv
      simp at hv
    refine IsUnit.of_mul_eq_one (b := ⟨(s : L)⁻¹, s, s.2, hsu, ?_⟩) ?_
    · rw [mul_inv_cancel₀ hs0]
      exact B.one_mem
    · exact Subtype.ext (mul_inv_cancel₀ hs0)
  · rintro ⟨z, t, ht, htu, htz⟩
    refine ⟨(⟨t * z, htz⟩, ⟨⟨t, ht⟩, fun h => htu ((mem_centerOf V).1 h)⟩), ?_⟩
    exact Subtype.ext (mul_comm z t)
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : L) = y := congrArg (fun z : localSubalgebra V B hB => (z : L)) hxy
    rw [Subtype.ext this]

variable (V) in
/-- The local rings `B_{𝔪_V ∩ B}` at the centers, indexed by the system `QASystem V`. -/
@[simps]
def localFamily : QASystem V →o Subalgebra A L where
  toFun B := localSubalgebra V B.1 B.2.2
  monotone' _ _ h := localSubalgebra_mono h

variable (V) in
/-- The cocone of inclusions `B_{𝔪_V ∩ B} ⊆ V`. -/
noncomputable abbrev localCocone : Cocone (subalgebraDiagram (localFamily V)) :=
  subalgebraCocone (localFamily V) (valuationSubalgebra V) fun B => localSubalgebra_le V B.1 B.2.2

variable (V) in
/-- The cone `Spec V → Spec B_{𝔪_V ∩ B}`. -/
noncomputable abbrev localSpecCone : Cone ((subalgebraDiagram (localFamily V)).op ⋙ Scheme.Spec) :=
  subalgebraSpecCone (localFamily V) (valuationSubalgebra V) fun B =>
    localSubalgebra_le V B.1 B.2.2

variable (V) in
/-- **`V` is the filtered colimit of the local rings at the centers** (proof of Temkin 2010,
Lemma 3.2.2: `𝒪_𝔵 = colim 𝒪_{S_i, x_i}`). -/
noncomputable def isColimitLocalCocone : IsColimit (localCocone V) :=
  isColimitSubalgebraCocone _ _ _ fun _ hx => by
    obtain ⟨B, hB⟩ := exists_mem hx
    exact ⟨B, le_localSubalgebra V B.1 B.2.2 hB⟩

variable (V) in
/-- `Spec V` is the cofiltered limit of the spectra of the local rings at the centers. -/
noncomputable def isLimitLocalSpecCone : IsLimit (localSpecCone V) :=
  isLimitOfPreserves Scheme.Spec (isColimitLocalCocone V).op

/-- If `L` is algebraic over `A`, then so is every subalgebra of `L`; in particular every member
of the approximating system is a domain of finite type and algebraic over `A`, so its spectrum is
a quasi-alteration of `Spec A` when `A` is a domain. -/
lemma isAlgebraic_of_isAlgebraic [Algebra.IsAlgebraic A L] (B : Subalgebra A L) :
    Algebra.IsAlgebraic A B :=
  ⟨fun b => (isAlgebraic_algHom_iff B.val Subtype.val_injective).1
    (Algebra.IsAlgebraic.isAlgebraic (b : L))⟩

variable (V) in
/-- The morphisms `Spec V → Spec B → Spec A` compose to the structure morphism. -/
lemma fgSpecCone_π_app_comp (B : QASystem V) :
    (fgSpecCone (valuationSubalgebra V)).π.app (Opposite.op B) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B.1)) =
      Spec.map (CommRingCat.ofHom (algebraMap A (valuationSubalgebra V))) :=
  (Spec.map_comp _ _).symm

variable (V) in
/-- The morphism `Spec L → Spec V → Spec B` is induced by the inclusion `B ⊆ L`. -/
lemma specMap_comp_fgSpecCone_π_app (B : QASystem V) :
    Spec.map (CommRingCat.ofHom (algebraMap (valuationSubalgebra V) L)) ≫
        (fgSpecCone (valuationSubalgebra V)).π.app (Opposite.op B) =
      Spec.map (CommRingCat.ofHom (algebraMap B.1 L)) :=
  (Spec.map_comp _ _).symm

end Valuation

/-! ### Valuation rings centred on a scheme -/

section Scheme

variable {S : Scheme.{u}} {L : Type u} [Field L] {η : Spec (.of L) ⟶ S} {U : S.Opens}
  (hU : IsAffineOpen U) (hηU : η ⁻¹ᵁ U = ⊤)

/-- **Temkin 2010, Lemma 3.2.2, in the form used here.** Let `V ∈ RZ_L(S)` contain the image of
`Γ(S, U)` for an affine open `U` (by `RiemannZariskiSpace.mem_ofScheme_iff` every point of
`RZ_L(S)` is of this form). Then for every finitely generated `Γ(S, U)`-subalgebra `B ⊆ V` of `L`,
the extension `Spec V → S` of `η` factors as `Spec V → Spec B → Spec Γ(S, U) ≅ U ⊆ S`; together
with `isLimitFGSpecCone` this presents `Spec V` as the limit of the affine quasi-modifications
`Spec B → S` (quasi-alterations when `L` is algebraic over the function field). -/
theorem fgSpecCone_π_app_comp_fromSpec
    (V : RiemannZariskiSpace L)
    (hV : V ∈ RiemannZariskiSpace.ofRingHom (RiemannZariskiSpace.sectionsToField η U hηU)) :
    letI : Algebra Γ(S, U) L := (RiemannZariskiSpace.sectionsToField η U hηU).toAlgebra
    ∀ B : QASystem (⟨V, hV⟩ : RiemannZariskiSpace.ofAlgebra Γ(S, U) L),
      (fgSpecCone (valuationSubalgebra (⟨V, hV⟩ : RiemannZariskiSpace.ofAlgebra Γ(S, U) L))).π.app
          (Opposite.op B) ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) B.1)) ≫
          hU.fromSpec =
        RiemannZariskiSpace.extensionOfMem η hU hηU V hV := by
  let : Algebra Γ(S, U) L := (RiemannZariskiSpace.sectionsToField η U hηU).toAlgebra
  intro B
  rw [← Category.assoc, fgSpecCone_π_app_comp]
  rfl

end Scheme

end DeJongAlterations.StableModification.Limits
