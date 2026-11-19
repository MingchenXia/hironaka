import Hironaka.Resolution.HironakaMarkOneGammaBoundedMaxima

/-! Actual finite native mark-one Gamma phase without compactness.
Source-first proof: hironaka-mark-one-noncompact-native-phase.tex.
Current prefix maximum attainment/transport is proved in the imported mother.
Full original upper-row/prefix D/J dictionaries and global K1 remain open. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaMarkOneNoncompactNativePhase
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MonomialPartAlong DivisorExponentAlong
  MonomialInvariant MonomialCaseAlong MonomialStepAlong ResolutionDriver
  HironakaMarkOneGammaBoundedMaxima

variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual mark-one maximum attainment at EVERY native CAN prefix permits
the genuine finite native Gamma phase on a noncompact source. The bound
has its honest mark-one first coordinate; no current maximum is assumed. -/
theorem exists_markOne_native_resolution_of_bound (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E) (hd : M.d=1)
    (v : Val) (hFirst : (ofLex v).1=n-1)
    (hBound : ∀ x ∈ M.cosupp,gammaAlong n M.N M.ideal M.E M.d x ≤ (v : WithBot Val)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonicalSegment M (fun {Q} R => towerInvAlong M (Y := Q) R) T ∧ IsGeoResolution M T := by
  have := wellFoundedLT_val
  suffices h : ∀ l : WithBot Val,∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsCanonicalSegment M (fun {Q} R => towerInvAlong M (Y := Q) R) T →
      (∀ y ∈ (geoTransformAlong M T).cosupp,towerInvAlong M T y ≤ l) →
      ∃ (Z : CMfd.{u} n) (R : BlowupTower X Z),
        IsCanonicalSegment M (fun {Q} R => towerInvAlong M (Y := Q) R) R ∧ IsGeoResolution M R by
    exact h (v : WithBot Val) (.refl (X := X)) trivial hBound
  intro l
  induction l using WellFoundedLT.induction with
  | _ l ih =>
    intro Y T hCan hCurrentBound
    obtain ⟨hTest,hdT,hCurrent,hNZ,hMono,_hFixedBound,_hExponents,_hFinite,hMaximum⟩ :=
      canonical_prefix_markOne_bounded_maxima hn M hM hne hmono hd v hFirst hBound T hCan
    by_cases hNonempty : (geoTransformAlong M T).cosupp.Nonempty
    · obtain ⟨x,hx⟩ := hMaximum hNonempty
      obtain ⟨hAdm,hThin⟩ := isAdmissibleCentre_maxLocus_gammaAlong hn hCurrent.isClosedSubmanifold_N
        hCurrent.isSNCDivisor hCurrent.isTransverse hCurrent.isCoherent hNZ
        (geoTransformAlong M T) rfl rfl rfl hMono
      have hEmptyInterior := hThin (by rw [hdT])
      obtain ⟨Z,π,hπ⟩ := ResolutionDriver.exists_blowup _ hAdm.1 hEmptyInterior
      let T' : BlowupTower X Z := .step T (maxLocusA (geoTransformAlong M T)) π hπ
      have hCan' : IsCanonicalSegment M (fun {Q} R => towerInvAlong M (Y := Q) R) T' :=
        ⟨hCan,⟨x,hx⟩,rfl⟩
      obtain ⟨hTest',_hdT',_hCurrent',_hNZ',_hMono',_hFixedBound',_hExponents',_hFinite',hMaximum'⟩ :=
        canonical_prefix_markOne_bounded_maxima hn M hM hne hmono hd v hFirst hBound T' hCan'
      by_cases hNonempty' : (geoTransformAlong M T').cosupp.Nonempty
      · obtain ⟨z,hz⟩ := hMaximum' hNonempty'
        obtain ⟨_hNew,_hNewNZ,_hNewMono,_hOver,_hOff,hDrop⟩ :=
          monomial_step_along hn hCurrent hNZ hMono hπ
        have hSmaller : towerInvAlong M T' z < l :=
          (hDrop x hx z hz.1).trans_le (hCurrentBound x hx.1)
        exact ih _ hSmaller T' hCan' hz.2
      · exact ⟨Z,T',hCan',hTest',Set.not_nonempty_iff_eq_empty.mp hNonempty'⟩
    · exact ⟨Y,T,hCan,hTest,Set.not_nonempty_iff_eq_empty.mp hNonempty⟩

/-- An ordinary actual mark-one source point internally supplies the true
USC source window and shaped bound, then constructs a genuine finite native
CAN resolution of the literal pullback. No compactness or future history
is an input; no original upper-row history interpretation is asserted. -/
theorem exists_open_markOne_native_resolution (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E) (hd : M.d=1)
    {x : X} (hx : x ∈ M.cosupp) (O : Opens X) (hxO : x ∈ O) :
    ∃ (U : Opens X) (_hxU : x ∈ U),(U : Set X) ⊆ O ∧
      let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
      ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        IsCanonicalSegment MU (fun {Q} R => towerInvAlong MU (Y := Q) R) T ∧ IsGeoResolution MU T := by
  obtain ⟨U,hxU,hUO,v,_hValue,hFirst,hdU,hMU,hNZ,hMono,_hxCos,_hGamma,hBound,_hPrefixes⟩ :=
    exists_open_all_canonical_markOne_prefix_maxima hn M hM hne hmono hd hx O hxO
  exact ⟨U,hxU,hUO,exists_markOne_native_resolution_of_bound (X := CMfd.of (n := n) U) hn
    (MarkedIdeal.pullback (Subtype.val : U → X) M) hMU hNZ hMono hdU v hFirst hBound⟩

end
end Hironaka.HironakaMarkOneNoncompactNativePhase
