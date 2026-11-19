import Hironaka.Resolution.Algebraic.RelativeAffineSpaceCentreDescent
import Hironaka.Scheme.BlowUpSequence.Functoriality

/-!
# Canonical descent of the WHOLE actual relative-affine history

Source-first proof: `actual-relative-affine-history-descent-20261102.tex`.
The actual zero-section pullback retains every native chronological position.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace Hironaka.Resolution.Algebraic.ActualRelativeAffineHistoryDescent

noncomputable section
open ActualPaddedEnvelopeNativeTranslations RelativeAffineSpaceCentreDescent

/-- Actual next-product projection is identified by the genuine blowup universal property. -/
theorem product_projection_unique {X : Scheme.{u}} (σ : Type u)
    (D : (AffineSpace σ X).IdealSheafData) (J : X.IdealSheafData)
    (hD : D = J.comap (AffineSpace σ X ↘ X))
    (e : D.blowUp ≅ AffineSpace σ J.blowUp)
    (he : e.hom ≫ AffineSpace.map σ J.blowUpπ = D.blowUpπ) :
    e.hom ≫ (AffineSpace σ J.blowUp ↘ J.blowUp) =
      eqToHom (congrArg Scheme.IdealSheafData.blowUp hD) ≫
        Scheme.Hom.blowUpMap (AffineSpace σ X ↘ X) J := by
  let c := eqToHom (congrArg Scheme.IdealSheafData.blowUp hD)
  have hc : inv c ≫ D.blowUpπ = (J.comap (AffineSpace σ X ↘ X)).blowUpπ := by
    rw [← eqToHom_comp_blowUpπ hD, IsIso.inv_hom_id_assoc]
  have hg : inv c ≫ e.hom ≫ (AffineSpace σ J.blowUp ↘ J.blowUp) =
      Scheme.Hom.blowUpMap (AffineSpace σ X ↘ X) J := by
    apply eq_blowUpMap
    simp only [Category.assoc]
    rw [← AffineSpace.map_over,
      ← Category.assoc e.hom (AffineSpace.map σ J.blowUpπ) (AffineSpace σ X ↘ X), he,
      ← Category.assoc, hc]
  calc
    e.hom ≫ (AffineSpace σ J.blowUp ↘ J.blowUp) =
        c ≫ (inv c ≫ e.hom ≫ (AffineSpace σ J.blowUp ↘ J.blowUp)) :=
      (IsIso.hom_inv_id_assoc c _).symm
    _ = c ≫ Scheme.Hom.blowUpMap (AffineSpace σ X ↘ X) J := by rw [hg]

/-- The descended history is the actual zero-section pullback of the SAME
whole sequence. No deletion of empty centres, clock alignment or new run. -/
theorem relativeAffineSpace_history_descends (σ : Type u) [Finite σ]
    (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (S : (AffineSpace σ X).BlowUpSequence)
    (hS : ∀ v : σ → ℤ, S = S.pullback (affineTranslation σ X v).hom) :
    S = (S.pullback (AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0))).pullback
      (AffineSpace σ X ↘ X) := by
  have aux : ∀ n : ℕ, ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
      (S : (AffineSpace σ X).BlowUpSequence), S.length = n →
      (∀ v : σ → ℤ, S = S.pullback (affineTranslation σ X v).hom) →
      ∃ A : X.BlowUpSequence, S = A.pullback (AffineSpace σ X ↘ X) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X f S hn hS
      cases S with
      | nil _ => exact ⟨.nil X,rfl⟩
      | cons _ D T =>
        let J := D.comap (AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0))
        have hD : ∀ v : σ → ℤ, D.comap (affineTranslation σ X v).hom = D :=
          fun v => (Scheme.BlowUpSequence.cons.inj (hS v)).1.symm
        have hcentre : D = J.comap (AffineSpace σ X ↘ X) :=
          relativeAffineSpace_centre_descends σ k f D hD
        obtain ⟨e,he,hTail⟩ := current_relative_product_tail_step σ k f D T hS
        have hlen : (T.pullback e.inv).length < n := by
          rw [length_pullback]
          change T.length+1 = n at hn
          omega
        obtain ⟨A,hA⟩ := ih _ hlen J.blowUp (J.blowUpπ ≫ f) (T.pullback e.inv) rfl hTail
        have hp := product_projection_unique σ D J hcentre e he
        have hT : T = A.pullback (eqToHom (congrArg Scheme.IdealSheafData.blowUp hcentre) ≫
            Scheme.Hom.blowUpMap (AffineSpace σ X ↘ X) J) := by
          calc
            T = (T.pullback e.inv).pullback e.hom := by
              rw [← pullback_comp, Iso.hom_inv_id, pullback_id]
            _ = (A.pullback (AffineSpace σ J.blowUp ↘ J.blowUp)).pullback e.hom := by rw [hA]
            _ = A.pullback (e.hom ≫ (AffineSpace σ J.blowUp ↘ J.blowUp)) :=
              (pullback_comp A _ _).symm
            _ = _ := congrArg (A.pullback ·) hp
        refine ⟨.cons X J A,?_⟩
        change Scheme.BlowUpSequence.cons (AffineSpace σ X) D T =
          Scheme.BlowUpSequence.cons (AffineSpace σ X) (J.comap (AffineSpace σ X ↘ X))
            (A.pullback (Scheme.Hom.blowUpMap (AffineSpace σ X ↘ X) J))
        apply cons_congr hcentre
        exact (heq_of_eq hT).trans
          (pullback_eqToHom_comp A (congrArg Scheme.IdealSheafData.blowUp hcentre)
            (Scheme.Hom.blowUpMap (AffineSpace σ X ↘ X) J))
  obtain ⟨A,hA⟩ := aux S.length X f S rfl hS
  have hs : AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0) ≫ (AffineSpace σ X ↘ X) = 𝟙 X :=
    AffineSpace.homOfVector_over _ _
  have hc : S.pullback (AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0)) = A := by
    rw [hA, ← pullback_comp, hs, pullback_id]
  rw [hc]
  exact hA

section ClopenProducts
variable {ι : Type} (V : ι → Type u) (B : ι → Scheme.{u})

/-- The actual projection of the SAME coproduct of original relative spaces. -/
def clopenProjection : (∐ fun i => AffineSpace (V i) (B i)) ⟶ ∐ B :=
  Limits.Sigma.map (fun i => AffineSpace (V i) (B i) ↘ B i)

/-- The actual coproduct zero section, with the original labels retained. -/
def clopenZeroSection : (∐ B) ⟶ ∐ fun i => AffineSpace (V i) (B i) :=
  Limits.Sigma.map (fun i => AffineSpace.homOfVector (𝟙 (B i)) (fun _ : V i => 0))

/-- Actual coordinate translations on all original clopen summands. -/
def clopenTranslation (v : ∀ i, V i → ℤ) :
    (∐ fun i => AffineSpace (V i) (B i)) ⟶ ∐ fun i => AffineSpace (V i) (B i) :=
  Limits.Sigma.map (fun i => (affineTranslation (V i) (B i) (v i)).hom)

private def clopenInclusion (i : ι) :
    AffineSpace (V i) (B i) ⟶ ∐ fun j : ι => AffineSpace (V j) (B j) :=
  Sigma.ι (fun j : ι => AffineSpace (V j) (B j)) i

private instance clopenInclusion_isOpenImmersion (i : ι) :
    IsOpenImmersion (clopenInclusion V B i) := by
  dsimp only [clopenInclusion]
  infer_instance

/-- Canonical descent of the SAME global history through genuine clopen
pieces. Restricted clocks are inherited, never independently chosen. -/
theorem clopen_relative_history_descends [∀ i, Finite (V i)]
    (k : Type u) [Field k] [CharZero k] (f : ∀ i, B i ⟶ Spec (.of k))
    (S : (∐ fun i => AffineSpace (V i) (B i)).BlowUpSequence)
    (hS : ∀ v, S = S.pullback (clopenTranslation V B v)) :
    S = (S.pullback (clopenZeroSection V B)).pullback (clopenProjection V B) := by
  classical
  by_cases hι : Nonempty ι
  · let : Nonempty ι := hι
    have hcover : ∀ x : ((∐ fun i => AffineSpace (V i) (B i)) : Scheme.{u}),
        ∃ i : ULift.{u} ι, ∃ y, clopenInclusion V B i.down y = x := by
      intro x
      obtain ⟨i,y,hi⟩ := (sigmaOpenCover (fun i => AffineSpace (V i) (B i))).exists_eq x
      refine ⟨⟨i⟩,y,?_⟩
      exact hi
    apply eq_of_pullback_of_covers S _
      (fun i : ULift.{u} ι => clopenInclusion V B i.down) hcover
    rintro ⟨i⟩
    change S.pullback (Sigma.ι (fun j => AffineSpace (V j) (B j)) i) =
      ((S.pullback (clopenZeroSection V B)).pullback (clopenProjection V B)).pullback
        (Sigma.ι (fun j => AffineSpace (V j) (B j)) i)
    have hlocal : ∀ v : V i → ℤ,
        S.pullback (Sigma.ι (fun j => AffineSpace (V j) (B j)) i) =
          (S.pullback (Sigma.ι (fun j => AffineSpace (V j) (B j)) i)).pullback
            (affineTranslation (V i) (B i) v).hom := by
      intro v
      let w : ∀ j, V j → ℤ := fun j a =>
        if h : j = i then v (cast (congrArg V h) a) else 0
      have hw : w i = v := by
        funext a
        simp [w]
      have hτ : Sigma.ι (fun j => AffineSpace (V j) (B j)) i ≫ clopenTranslation V B w =
          (affineTranslation (V i) (B i) v).hom ≫
            Sigma.ι (fun j => AffineSpace (V j) (B j)) i := by
        rw [clopenTranslation, Sigma.ι_map, hw]
      have h := congrArg (fun T => T.pullback (Sigma.ι (fun j => AffineSpace (V j) (B j)) i)) (hS w)
      rw [← pullback_comp, hτ, pullback_comp] at h
      exact h
    have hl := relativeAffineSpace_history_descends (V i) k (f i)
      (S.pullback (Sigma.ι (fun j => AffineSpace (V j) (B j)) i)) hlocal
    have hp : Sigma.ι (fun j => AffineSpace (V j) (B j)) i ≫ clopenProjection V B =
        (AffineSpace (V i) (B i) ↘ B i) ≫ Sigma.ι B i := by
      rw [clopenProjection, Sigma.ι_map]
    have hz : Sigma.ι B i ≫ clopenZeroSection V B =
        AffineSpace.homOfVector (𝟙 (B i)) (fun _ : V i => 0) ≫
          Sigma.ι (fun j => AffineSpace (V j) (B j)) i := by
      rw [clopenZeroSection, Sigma.ι_map]
    have hc : Sigma.ι (fun j => AffineSpace (V j) (B j)) i ≫
        clopenProjection V B ≫ clopenZeroSection V B =
      (AffineSpace (V i) (B i) ↘ B i) ≫
        AffineSpace.homOfVector (𝟙 (B i)) (fun _ : V i => 0) ≫
          Sigma.ι (fun j => AffineSpace (V j) (B j)) i := by
      rw [← Category.assoc, hp, Category.assoc, hz]
    calc
      S.pullback (Sigma.ι (fun j => AffineSpace (V j) (B j)) i) = _ := hl
      _ = S.pullback ((AffineSpace (V i) (B i) ↘ B i) ≫
          AffineSpace.homOfVector (𝟙 (B i)) (fun _ : V i => 0) ≫
            Sigma.ι (fun j => AffineSpace (V j) (B j)) i) := by
        simp only [← pullback_comp]
      _ = S.pullback (Sigma.ι (fun j => AffineSpace (V j) (B j)) i ≫
          clopenProjection V B ≫ clopenZeroSection V B) := congrArg (S.pullback ·) hc.symm
      _ = _ := by simp only [pullback_comp]
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    have hzero : clopenProjection V B ≫ clopenZeroSection V B =
        𝟙 (∐ fun i => AffineSpace (V i) (B i)) := by
      apply Sigma.hom_ext
      intro i
      exact isEmptyElim i
    rw [← pullback_comp, hzero, pullback_id]
end ClopenProducts

open ActualDimensionGroupBlowup ActualDimensionGroupEquidimensionalPieces
  ActualDimensionGroupPaddedCover

section OriginalInput
variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

/-- The WHOLE original native padded history descends to its OWN actual
zero-section history on the SAME separation blowup, with every internal slot. -/
theorem nativePaddedHistory_canonical_history_descends :
    nativePaddedHistory R k =
      ((nativePaddedHistory R k).pullback (envelopeZeroSection R k)).pullback (envelopeProjection R k) := by
  let V : dimensionIndex R → Type u := paddingVariables R k
  let B : dimensionIndex R → Scheme.{u} := fun d => (dimensionPartOpen R d).toScheme
  let S : (∐ fun d : dimensionIndex R => AffineSpace (V d) (B d)).BlowUpSequence := by
    change (paddedEnvelope R k).obj.left.BlowUpSequence
    exact nativePaddedHistory R k
  have htrans : ∀ v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ,
      S = S.pullback (clopenTranslation V B v) := by
    intro v
    change nativePaddedHistory R k = (nativePaddedHistory R k).pullback (envelopeTranslation R k v)
    exact nativePaddedHistory_eq_pullback_translation R k v
  have h := clopen_relative_history_descends V B k
    (fun d => (pieceAlgScheme R k d).hom) S htrans
  have hproj : clopenProjection V B ≫ piecesDesc R = envelopeProjection R k := by
    apply Sigma.hom_ext
    intro d
    rw [← Category.assoc, clopenProjection, Sigma.ι_map, Category.assoc, piecesDesc, Sigma.ι_desc]
    exact (envelopeProjection_isPullback_piece R k d).w
  have hsection : envelopeZeroSection R k = inv (piecesDesc R) ≫ clopenZeroSection V B := rfl
  have hc : envelopeProjection R k ≫ envelopeZeroSection R k =
      clopenProjection V B ≫ clopenZeroSection V B := by
    rw [← hproj, hsection, Category.assoc, ← Category.assoc (piecesDesc R),
      IsIso.hom_inv_id, Category.id_comp]
  rw [← pullback_comp] at h ⊢
  rw [hc]
  exact h

/-- Actual original-input history on the SAME dimension-separation blowup.
Its value is the original native history's OWN zero-section pullback. -/
def nativeBaseHistory : (affineBlowUp (dimensionSeparationIdeal R)).BlowUpSequence :=
  (nativePaddedHistory R k).pullback (envelopeZeroSection R k)
end OriginalInput

end
end Hironaka.Resolution.Algebraic.ActualRelativeAffineHistoryDescent
