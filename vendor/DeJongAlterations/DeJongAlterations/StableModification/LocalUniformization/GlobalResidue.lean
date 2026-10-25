import DeJongAlterations.StableModification.LocalUniformization.GlobalBase
import DeJongAlterations.StableModification.LocalUniformization.GlobalCentre
import Mathlib.RingTheory.Valuation.Extension

/-!
# Residue fields of a centre and of the valuation

Let `vL` be a valuation of a field `L ⊇ K`, `K₀ = vL.comap ∩ K` and `L₀` its valuation rings, and
let `vL` be centred at a point `y` of a scheme `X → Spec O'` (`O' ⊆ K₀` a valuation ring of `K`,
the map `Spec L → X → Spec O'` given by `O' ⊆ K ⊆ L`). The residue field `κ(y)` maps to the
residue field `L̃` of `vL`, and the image of `κ(q y)` is the image of the residue field `K̃` of
`K₀` (`exists_residueField_comparison`). Consequently (blueprint `lem:sm-cofinal-residue`,
`sm-local-uniformization.tex`; the bridge between Temkin's `trdeg (κ(x)/κ(s)) = 1` for
`x ∈ (C/S)⁰` and the valuation condition `trdeg (L̃/K̃) = 1` of `𝔊⁰`, T:2873–2876):

* `exists_transcendental_residue`: if `κ(y)` is not algebraic over `κ(q y)`, some element of `L₀`
  has residue transcendental over `K̃`;
* `isAlgebraic_residue`: if `κ(y)` is algebraic over `κ(q y)`, the residues of the images of the
  local ring `𝒪_{X,y}` are algebraic over `K̃`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

open ValCurves RiemannZariskiSpace

/-- The germ of a global section, followed by the stalk map at the closed point of a morphism
between spectra, is the ring map of the morphism. -/
theorem germ_stalkClosedPointTo_eq {R S : CommRingCat.{u}} [IsLocalRing S] (f : Spec S ⟶ Spec R) :
    (Spec R).presheaf.germ ⊤ (f (closedPoint S)) trivial ≫ Scheme.stalkClosedPointTo f =
      (Scheme.ΓSpecIso R).hom ≫ Spec.preimage f := by
  obtain ⟨θ, rfl⟩ := Spec.map_surjective f
  rw [Spec.preimage_map]
  exact Scheme.germ_stalkClosedPointTo_Spec θ

/-- The structure map to a stalk of an affine scheme is the germ of the global section. -/
theorem toStalk_eq_germ (R : CommRingCat.{u}) (p : Spec R) :
    StructureSheaf.toStalk R p = (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ p trivial :=
  rfl

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {Γ₁ : Type u}
  [LinearOrderedCommGroupWithZero Γ₁] (vL : Valuation L Γ₁)

local notation "K₀" => Valuation.valuationSubring (Valuation.comap (algebraMap K L) vL)
local notation "L₀" => Valuation.valuationSubring vL

/-- **Comparison of residue fields.** Let `ψ : Spec L₀ → X` extend `η : Spec L → X`, with closed
point `y`, and `q : X → Spec O'` with `η ≫ q = Spec (O' ⊆ L)` and `q y = 𝔪_{K₀} ∩ O'`. Then
there are the local map `θ : 𝒪_{X,y} → L₀` and a surjection `λ : K̃ → κ(q y)` such that
`K̃ → L̃` factors as `K̃ → κ(q y) → κ(y) → L̃`. -/
theorem exists_residueField_comparison {O' : ValuationSubring K} (hO' : O' ≤ K₀)
    {X : Scheme.{u}} (q : X ⟶ Spec (.of O')) (ψ : Spec (.of L₀) ⟶ X)
    (hψq : toSpecValuationSubring ⟨L₀⟩ ≫ ψ ≫ q =
      Spec.map (CommRingCat.ofHom ((algebraMap K L).comp O'.subtype)))
    (hqy : (q (ψ (closedPoint L₀))).asIdeal = O'.idealOfLE _ hO') :
    ∃ (lam : ResidueField K₀ →+* (Spec (.of O')).residueField (q (ψ (closedPoint L₀)))),
      Function.Surjective lam ∧ ∀ c, (ResidueField.map (Scheme.stalkClosedPointTo ψ).hom)
        ((q.residueFieldMap _).hom (lam c)) = algebraMap (ResidueField K₀) (ResidueField L₀) c := by
  set y := ψ (closedPoint L₀)
  let S := (Spec (.of O')).presheaf.stalk (q y)
  let 𝔭 := O'.idealOfLE _ hO'
  -- `K₀` and the stalk `S` are localizations of `O'` at `𝔭`
  let := inclusionAlgebra O' K₀ hO'
  have hK₀ : IsLocalization.AtPrime K₀ 𝔭 := isLocalization_atPrime O' K₀ hO'
  let : Algebra O' S := StructureSheaf.stalkAlgebra O' (q y)
  have : (PrimeSpectrum.asIdeal (q y)).IsPrime := PrimeSpectrum.isPrime (q y)
  have h0 : IsLocalization (PrimeSpectrum.asIdeal (q y)).primeCompl S :=
    StructureSheaf.IsLocalization.to_stalk O' (q y)
  have hM : (PrimeSpectrum.asIdeal (q y)).primeCompl = 𝔭.primeCompl :=
    Submonoid.ext fun x ↦ by
      change x ∉ (PrimeSpectrum.asIdeal (q y)) ↔ x ∉ 𝔭
      rw [hqy]
  have hS : IsLocalization 𝔭.primeCompl S := hM ▸ h0
  let e : K₀ ≃ₐ[O'] S := IsLocalization.algEquiv 𝔭.primeCompl K₀ S
  let lam₀ : K₀ →+* S := e.toRingHom
  -- the map `S → L₀` at the closed point
  let θS : S →+* L₀ := (Scheme.stalkClosedPointTo (ψ ≫ q)).hom
  let θ'' := Spec.preimage (ψ ≫ q)
  have hθ'' : Spec.map θ'' = ψ ≫ q := Spec.map_preimage _
  have hθ''L : θ'' ≫ CommRingCat.ofHom (algebraMap L₀ L) =
      CommRingCat.ofHom ((algebraMap K L).comp O'.subtype) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hθ'', ← hψq]
  have hθSO : ∀ o : O', θS (algebraMap O' S o) = θ'' o := by
    intro o
    have h := germ_stalkClosedPointTo_eq (ψ ≫ q)
    have h2 : algebraMap O' S o = (Spec (.of O')).presheaf.germ ⊤ (q y) trivial
        ((Scheme.ΓSpecIso (.of O')).inv o) := rfl
    rw [h2]
    change ((Spec (.of O')).presheaf.germ ⊤ ((ψ ≫ q) (closedPoint L₀)) trivial ≫
      Scheme.stalkClosedPointTo (ψ ≫ q)) ((Scheme.ΓSpecIso (.of O')).inv o) = _
    rw [h]
    change θ'' ((Scheme.ΓSpecIso (.of O')).hom ((Scheme.ΓSpecIso (.of O')).inv o)) = _
    rw [Iso.inv_hom_id_apply]
  -- `θS ∘ λ₀` is the inclusion `K₀ → L₀`
  have hcomp : θS.comp lam₀ = algebraMap K₀ L₀ := by
    refine IsLocalization.ringHom_ext 𝔭.primeCompl (RingHom.ext fun o ↦ ?_)
    simp only [RingHom.comp_apply]
    have h1 : lam₀ (algebraMap O' K₀ o) = algebraMap O' S o := e.commutes o
    rw [h1, hθSO]
    apply Subtype.ext
    have h2 := congrArg (fun f ↦ f.hom o) hθ''L
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    rw [Valuation.HasExtension.coe_algebraMap_valuationSubring_eq]
    exact h2
  have hloc : IsLocalHom lam₀ := ⟨fun x hx ↦ by
    have := hx.map e.symm.toRingEquiv.toRingHom
    simpa [lam₀] using this⟩
  refine ⟨ResidueField.map lam₀, ?_, fun c ↦ ?_⟩
  · intro z
    obtain ⟨s, rfl⟩ := residue_surjective z
    obtain ⟨b, rfl⟩ := e.surjective s
    exact ⟨residue K₀ b, rfl⟩
  · obtain ⟨b, rfl⟩ := residue_surjective c
    change (ResidueField.map (Scheme.stalkClosedPointTo ψ).hom)
      ((ResidueField.map (q.stalkMap y).hom) (ResidueField.map lam₀ (residue K₀ b))) = _
    rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue,
      Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap, ← hcomp]
    congr 1
    change (Scheme.stalkClosedPointTo ψ).hom ((q.stalkMap y).hom (lam₀ b)) =
      (Scheme.stalkClosedPointTo (ψ ≫ q)).hom (lam₀ b)
    rw [Scheme.stalkClosedPointTo_comp]
    rfl


open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg) in
/-- **A transcendental residue from a centre of positive fibre dimension**
(`lem:sm-cofinal-residue`, first part). If `vL` is centred at `y` and `κ(y)` has positive
transcendence degree over `κ(q y)`, some element of `L₀` has residue transcendental over `K̃`. -/
theorem exists_transcendental_residue {O' : ValuationSubring K} (hO' : O' ≤ K₀)
    {X : Scheme.{u}} {η : Spec (.of L) ⟶ X} (q : X ⟶ Spec (.of O'))
    (hq : η ≫ q = Spec.map (CommRingCat.ofHom ((algebraMap K L).comp O'.subtype))) {y : X}
    (hy : IsCentre η ⟨L₀⟩ y) (hqy : (q y).asIdeal = O'.idealOfLE _ hO')
    (htr : fiberTrdeg q y ≠ 0) :
    ∃ t : L₀, Transcendental (ResidueField K₀) (residue L₀ t) := by
  obtain ⟨ψ, hψ, rfl⟩ := hy
  have hψq : toSpecValuationSubring ⟨L₀⟩ ≫ ψ ≫ q =
      Spec.map (CommRingCat.ofHom ((algebraMap K L).comp O'.subtype)) := by
    rw [← Category.assoc, hψ, hq]
  change (q (ψ (closedPoint L₀))).asIdeal = _ at hqy
  change fiberTrdeg q (ψ (closedPoint L₀)) ≠ 0 at htr
  obtain ⟨lam, -, hcomm⟩ := exists_residueField_comparison vL hO' q ψ hψq hqy
  let := (q.residueFieldMap (ψ (closedPoint L₀))).hom.toAlgebra
  have hnalg : ¬ Algebra.IsAlgebraic (Scheme.residueField _ (q (ψ (closedPoint L₀))))
      (X.residueField (ψ (closedPoint L₀))) := fun h ↦ htr (trdeg_eq_zero_iff.mpr h)
  rw [Algebra.isAlgebraic_def] at hnalg
  push Not at hnalg
  obtain ⟨tb, htb⟩ := hnalg
  obtain ⟨t₀, ht₀⟩ := residue_surjective tb
  let ρ : X.residueField (ψ (closedPoint L₀)) →+* ResidueField L₀ :=
    ResidueField.map (Scheme.stalkClosedPointTo ψ).hom
  have hfun : ρ.comp ((algebraMap (Scheme.residueField _ (q (ψ (closedPoint L₀))))
      (X.residueField (ψ (closedPoint L₀)))).comp lam) =
      algebraMap (ResidueField K₀) (ResidueField L₀) := RingHom.ext hcomm
  refine ⟨(Scheme.stalkClosedPointTo ψ).hom t₀, fun ⟨p, hp0, hp⟩ ↦ htb ?_⟩
  refine ⟨p.map lam, (Polynomial.map_ne_zero_iff lam.injective).mpr hp0, ?_⟩
  have hρt : ρ tb = residue L₀ ((Scheme.stalkClosedPointTo ψ).hom t₀) := by
    rw [← ht₀]
    exact ResidueField.map_residue _ _
  have h1 : ρ (aeval tb (p.map lam)) = 0 := by
    rw [aeval_def, eval₂_map, Polynomial.hom_eval₂, hfun, hρt, ← aeval_def]
    exact hp
  exact (map_eq_zero_iff ρ ρ.injective).mp h1

open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg) in
/-- **Residues over a centre of fibre dimension zero** (`lem:sm-cofinal-residue`, second part).
If `ψ : Spec L₀ → X` extends `η` with closed point `y` and `κ(y)` is algebraic over `κ(q y)`, the
residue of the image of every element of `𝒪_{X,y}` is algebraic over `K̃`. -/
theorem isAlgebraic_residue {O' : ValuationSubring K} (hO' : O' ≤ K₀)
    {X : Scheme.{u}} (q : X ⟶ Spec (.of O')) (ψ : Spec (.of L₀) ⟶ X)
    (hψq : toSpecValuationSubring ⟨L₀⟩ ≫ ψ ≫ q =
      Spec.map (CommRingCat.ofHom ((algebraMap K L).comp O'.subtype)))
    (hqy : (q (ψ (closedPoint L₀))).asIdeal = O'.idealOfLE _ hO')
    (halg : fiberTrdeg q (ψ (closedPoint L₀)) = 0) (s : X.presheaf.stalk (ψ (closedPoint L₀))) :
    IsAlgebraic (ResidueField K₀) (residue L₀ ((Scheme.stalkClosedPointTo ψ).hom s)) := by
  obtain ⟨lam, hsurj, hcomm⟩ := exists_residueField_comparison vL hO' q ψ hψq hqy
  let := (q.residueFieldMap (ψ (closedPoint L₀))).hom.toAlgebra
  have h : Algebra.IsAlgebraic (Scheme.residueField _ (q (ψ (closedPoint L₀))))
      (X.residueField (ψ (closedPoint L₀))) := trdeg_eq_zero_iff.mp halg
  let sb : X.residueField (ψ (closedPoint L₀)) := residue _ s
  obtain ⟨p, hp0, hp⟩ := h.isAlgebraic sb
  obtain ⟨p₀, rfl⟩ := Polynomial.map_surjective lam hsurj p
  let ρ : X.residueField (ψ (closedPoint L₀)) →+* ResidueField L₀ :=
    ResidueField.map (Scheme.stalkClosedPointTo ψ).hom
  have hfun : ρ.comp ((algebraMap (Scheme.residueField _ (q (ψ (closedPoint L₀))))
      (X.residueField (ψ (closedPoint L₀)))).comp lam) =
      algebraMap (ResidueField K₀) (ResidueField L₀) := RingHom.ext hcomm
  refine ⟨p₀, fun h0 ↦ hp0 (by rw [h0, Polynomial.map_zero]), ?_⟩
  have h1 : ρ sb = residue L₀ ((Scheme.stalkClosedPointTo ψ).hom s) :=
    ResidueField.map_residue _ _
  rw [aeval_def, ← hfun, ← h1, ← Polynomial.hom_eval₂, ← eval₂_map, ← aeval_def, hp, map_zero]

/-- On an affine scheme, the local map at the closed point sends the germ of a global section to
its image under the ring map of the morphism. -/
theorem stalkClosedPointTo_germ {R S : CommRingCat.{u}} [IsLocalRing S] (f : Spec S ⟶ Spec R)
    (r : R) : (Scheme.stalkClosedPointTo f).hom
      ((Spec R).presheaf.germ ⊤ (f (closedPoint S)) trivial ((Scheme.ΓSpecIso R).inv r)) =
        Spec.preimage f r := by
  have h := germ_stalkClosedPointTo_eq f
  change ((Spec R).presheaf.germ ⊤ (f (closedPoint S)) trivial ≫
    Scheme.stalkClosedPointTo f) ((Scheme.ΓSpecIso R).inv r) = _
  rw [h]
  change Spec.preimage f ((Scheme.ΓSpecIso R).hom ((Scheme.ΓSpecIso R).inv r)) = _
  rw [Iso.inv_hom_id_apply]

end DeJongAlterations.StableModification.LocalUniformization
