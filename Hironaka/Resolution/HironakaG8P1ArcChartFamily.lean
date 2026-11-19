import Hironaka.Resolution.HironakaG8P1ArcTower

set_option autoImplicit false

/-!
# The actual arc family with its original coordinate chart retained

The ordinary input record constructs the same point-blowup family and
Cartier counts as `exists_arcFamily`, while retaining the first flat chart,
the original flattening coordinates and the anchored chain at every stage.
Combining the tail projection with the first point blowup gives exponent
`r + 1` in the original coordinates at stage `r`.

The original flattened-domain condition is not asserted globally. A genuine
neighborhood shrinking lemma below gives it near the actual arc point.
This is geometry for the native L1 argument, not a proof of its final
strict-transform tangent-space comparison.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1ArcChartFamily

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaActualProjectionTestRecord HironakaActualSharedCartierTraceTests
  HironakaActualAnchoredVerticalChart HironakaG8P1ArcTower NormalCrossings

open scoped Hironaka.ProductComplexManifold

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- Re-export of the existing private original-coordinate calculation, with
the original line-parameter identity included. The tail has length `|R|`;
the first point blowup contributes the additional
factor of the original line parameter. These are equations in the original
coordinates, not merely the coordinates of the first blown-up space. -/
theorem original_coordinates_of_anchored
    (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x, 0)} : Set (projectionAmbient X)))
    (hck : c.k = 0) (hcj : c.j = Fin.last n)
    (hOld : ∀ (y : projectionAmbient X) (i : Fin n),
      flatCoord c.Φ (i.castAdd 1) y = flatCoord Φ i y.1)
    (hLast : ∀ y : projectionAmbient X, flatCoord c.Φ (Fin.last n) y = y.2 0)
    {Z : CMfd.{u} (n+1)} (R : BlowupTower (arcY1 x) Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (hAnchor : AnchoredInheritedLastChartChain c.homeo R e) :
    ∀ v ∈ e.source,
      (∀ i : Fin n,
        flatCoord Φ i (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)) (R.proj v)).1 =
          (e v (Fin.last n)) ^ (R.length + 1) * e v (i.castAdd 1)) ∧
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)) (R.proj v)).2 0 = e v (Fin.last n) := by
  intro v hv
  obtain ⟨hq, _hvector, hcoords, hlast⟩ := anchored_chart_projection c.homeo R e hAnchor v hv
  change ∀ i : Fin n, c.toFun (R.proj v) (i.castAdd 1) =
    (e v (Fin.last n)) ^ R.length * e v (i.castAdd 1) at hcoords
  change c.toFun (R.proj v) (Fin.last n) = e v (Fin.last n) at hlast
  have hw : c.toFun (R.proj v) ∈ c.target := c.map_source hq
  have hbase : blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)) (R.proj v) =
      c.pt (c.toFun (R.proj v)) :=
    (congrArg (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))) (c.left_inv hq).symm).trans
      (c.blowupProj_invFun hw)
  have hflat : c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)) (R.proj v))) =
      monomial c.k c.j (c.toFun (R.proj v)) := by
    rw [hbase]
    exact c.flat_pt hw
  constructor
  · intro i
    have hi : i.castAdd 1 ≠ Fin.last n := by
      exact Fin.castSucc_ne_last i
    have hflat_i := congrArg (fun w : ComplexModel (n+1) => w (i.castAdd 1)) hflat
    change flatCoord c.Φ (i.castAdd 1)
        (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)) (R.proj v)) = _ at hflat_i
    rw [hck, hcj, monomial_apply, if_pos ⟨Nat.zero_le _, hi⟩] at hflat_i
    rw [← hOld, hflat_i, hcoords i, hlast, pow_succ]
    ring
  · have hflat_last := congrArg (fun w : ComplexModel (n+1) => w (Fin.last n)) hflat
    change flatCoord c.Φ (Fin.last n)
        (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)) (R.proj v)) = _ at hflat_last
    rw [hcj, monomial_apply, if_neg (by simp)] at hflat_last
    rw [← hLast, hflat_last]
    exact hlast

/-- Raw counts depend on the stage, tower and arc point, not on the chosen
record-adapted chart. Canonical arc-family uniqueness transports the existing
public count producer to the retained original frame. -/
theorem arcCountsRaw_of_arcFamily_identify
    {k : ℕ} (M : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))))
    {S S' : ℕ → ArcStage n (arcY1 x)}
    (hS : IsArcFamily x hπ1 S) (hS' : IsArcFamily x hπ1 S')
    (hCounts : ∀ r, ArcCountsRaw (k := k) M x hπ1 (S' r) r) :
    ∀ r, ArcCountsRaw (k := k) M x hπ1 (S r) r := by
  intro r
  have hCount := hCounts r
  obtain ⟨hZ, hR, hz, _⟩ := arcFamily_identify hS hS' r
  generalize S r = s at hZ hR hz ⊢
  generalize S' r = s' at hCount hZ hR hz
  obtain ⟨Z, R, e, z⟩ := s
  obtain ⟨Z', R', e', z'⟩ := s'
  dsimp only at hZ hR hz hCount ⊢
  subst hZ
  obtain rfl := eq_of_heq hR
  obtain rfl := eq_of_heq hz
  exact hCount

/-- Export the coordinate frame and anchor from the same actual construction
that supplies the arc family and its Cartier counts. No extra geometry is an
input, and the existing weaker `exists_arcFamily` statement is unchanged. -/
theorem exists_arcFamily_with_original_coordinates
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x ∈ M.cosupp)
    (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))) :
    ∃ (Φ Φs : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x, 0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (U : Set (arcY1 x))
      (S : ℕ → ArcStage n (arcY1 x)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      Φs.toFun = Φ.toFun ∧ Φs.invFun = Φ.invFun ∧
      Φs.source ⊆ Φ.source ∧ Φs.target ⊆ Φ.target ∧
      Φs.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φs.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      flatDomain Φs = flatDomain Φ ∩
        (fun y : X => ((y, 0) : projectionAmbient X)) ⁻¹' flatDomain c.Φ ∧
      (∀ y ∈ flatDomain Φs, y ∈ M.N ↔
        Φs.toFun (chartAt (ComplexModel n) x y) ∈
          coordSubspace (Finset.univ.filter fun i : Fin n => i.castAdd 1 ∈ SN)) ∧
      c.y₀ = (x, 0) ∧ c.k = 0 ∧ c.j = Fin.last n ∧
      (∀ (y : projectionAmbient X) (i : Fin n),
        flatCoord c.Φ (i.castAdd 1) y = flatCoord Φ i y.1) ∧
      (∀ y : projectionAmbient X, flatCoord c.Φ (Fin.last n) y = y.2 0) ∧
      Fin.last n ∉ SN ∧ (0 : ComplexModel (n+1)) ∈ c.target ∧
      blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)) (c.invFun 0) = (x, 0) ∧
      IsOpen U ∧ c.invFun 0 ∈ U ∧ U ⊆ c.source ∧
      (∀ v ∈ U,
        v ∈ ((projectionTest M).geoTransform ({(x, 0)} : Set (projectionAmbient X))
          (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))).N ↔
        c.toFun v ∈ coordSubspace SN) ∧
      IsArcFamily x hπ1 S ∧
      ∀ r, ArcCountsRaw (k := k) M x hπ1 (S r) r ∧
        AnchoredInheritedLastChartChain c.homeo (S r).R (S r).e ∧
        ∀ v ∈ (S r).e.source,
          (∀ i : Fin n,
            flatCoord Φ i (((arcA1 x hπ1).append (S r).R).proj v).1 =
              ((S r).e v (Fin.last n)) ^ (r + 1) * (S r).e v (i.castAdd 1)) ∧
          (((arcA1 x hπ1).append (S r).R).proj v).2 0 = (S r).e v (Fin.last n) := by
  obtain ⟨_h2, Φ, Φs, c, SN, _SE, U, hOut⟩ :=
    exists_two_record_shared_cartier_trace_test_counts (n := n) (X := X) (k1 := k) (k2 := k)
      M M hM hM x hx hx rfl rfl
  obtain ⟨hWhole, h0, Next, hNext, hData⟩ := hOut
  extract_lets s0 F at hData
  clear_value F
  obtain ⟨hZero, hLen, hSucc, _hInit1, _hInit2, _hAll⟩ := hData
  clear _hInit1 _hInit2 _hAll
  obtain ⟨hΦsrc, hΦ0, hcy, hck, hcj, hOld, hLast, _hSourceN, _hSourceE,
    hSN, _hSE, h0c, hzsrc, hzp, hz0, _hπ, _hAtlas, _hInv, _hCos0,
    _hd, _hBound, _hBoundLen, hU, hzU, hUc, hNU, _hEU, _hNotH, _hBorn,
    hΦsTo, hΦsInv, hΦsSrc, hΦsTgt, hΦsChartSrc, hΦsZero, hDom, hMask, _hTail⟩ := hWhole
  have hMask' : ∀ y ∈ flatDomain Φs, y ∈ M.N ↔
      Φs.toFun (chartAt (ComplexModel n) x y) ∈
        coordSubspace (Finset.univ.filter fun i : Fin n => i.castAdd 1 ∈ SN) := hMask
  let S : ℕ → ArcStage n (arcY1 x) := fun r => ⟨(F r).1, (F r).2.1, (F r).2.2.1, (F r).2.2.2.1⟩
  have hFamily : IsArcFamily x hπ1 S :=
    isArcFamily_of_tail (n := n) (X := X) x c Φ hΦ0 hcy hck hcj hOld hLast
      h0c hzsrc hz0 hπ1 _ h0 Next hNext F hZero hSucc
  obtain ⟨S', hFamily', hCounts'⟩ := exists_arcFamily (n := n) (X := X) M hM x hx hπ1
  have hCounts := arcCountsRaw_of_arcFamily_identify (n := n) (X := X) M x hπ1 hFamily hFamily' hCounts'
  refine ⟨Φ, Φs, c, SN, U, S,
    hΦsrc, hΦ0, hΦsTo, hΦsInv, hΦsSrc, hΦsTgt, hΦsChartSrc, hΦsZero, hDom, hMask',
    hcy, hck, hcj, hOld, hLast, hSN, h0c, hzp, hU, hzU, hUc, hNU, hFamily, ?_⟩
  intro r
  have hAnchor : AnchoredInheritedLastChartChain c.homeo (F r).2.1 (F r).2.2.1 :=
    (F r).2.2.2.2.1
  refine ⟨hCounts r, hAnchor, ?_⟩
  intro v hv
  have hcoord := original_coordinates_of_anchored (n := n) (X := X) x Φ c hck hcj hOld hLast
    (F r).2.1 (F r).2.2.1 hAnchor v hv
  simpa only [S, BlowupTower.proj_append, arcA1, BlowupTower.proj_step,
    BlowupTower.proj_refl, Function.comp_apply, id_eq, hLen r] using hcoord

/-- Membership in the original flattened domain is obtained on a genuine open
neighborhood of each arc point; it is not a global frame assumption. -/
theorem exists_original_domain_window
    (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))))
    (S : ℕ → ArcStage n (arcY1 x)) (hS : IsArcFamily x hπ1 S) (r : ℕ) :
    ∃ V : Set (S r).Z, IsOpen V ∧ (S r).z ∈ V ∧ V ⊆ (S r).e.source ∧
      ∀ v ∈ V, (((arcA1 x hπ1).append (S r).R).proj v).1 ∈ flatDomain Φ := by
  let T := (arcA1 x hπ1).append (S r).R
  let W : Set (S r).Z := (fun v => (T.proj v).1) ⁻¹' flatDomain Φ
  have hW : IsOpen W :=
    (isOpen_flatDomain Φ).preimage (continuous_fst.comp T.contMDiff_proj.continuous)
  have hzW : (S r).z ∈ W := by
    change (T.proj (S r).z).1 ∈ flatDomain Φ
    rw [(hS.arc r).proj_eq.1]
    exact mem_flatDomain_self Φ
  exact ⟨(S r).e.source ∩ W, (S r).e.open_source.inter hW,
    ⟨(hS.arc r).mem_source, hzW⟩, inter_subset_left, fun _ hv => hv.2⟩

end

end Hironaka.HironakaG8P1ArcChartFamily
