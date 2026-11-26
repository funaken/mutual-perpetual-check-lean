import MPC.Chess.KingHalfPlane
import MPC.Chess.CheckingRaySeparation

/-! The periodic checking hypotheses put every actual checking ray off the
king line. A crossing and both incident rays then lie in one global side. -/

namespace MPC.Chess.MoveTrace

theorem checkingRay_halfPlane_unique_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) :
    ∃! side, d ∈ halfPlaneDirections (kp 0 c).toPlane (kp 0 c.opponent).toPlane side := by
  have hoff := tr.checkingRay_offset_ne_zero_of_periodic_checks kp hl hk hc hp hn c d hr
  have ha : halfPlaneCross (kp 0 c).toPlane (kp 0 c.opponent).toPlane (kp 0 c).toPlane = 0 := by
    simp [halfPlaneCross]
  have he := inKingHalfPlane_rayPoint_iff (kp 0 c).toPlane (kp 0 c.opponent).toPlane
    (kp 0 c).toPlane
  obtain ⟨side, hs, hu⟩ := (exists_unique_kingHalfPlane_iff (kp 0 c).toPlane
    (kp 0 c.opponent).toPlane (rayPoint (kp 0 c).toPlane d 1)).mpr
    (by simpa only [halfPlaneCross_rayPoint, ha, zero_add, one_mul] using hoff)
  exact ⟨side, (he side d 1 ha (by norm_num)).mp hs,
    fun s h => hu s ((he s d 1 ha (by norm_num)).mpr h)⟩

/-- Sides are oriented from white's king to black's king for both incident
rays. The boundary origins are excluded; rational non-lattice crossings and
points beyond the board are allowed. -/
theorem checkingCrossing_halfPlane_unique_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (p : PlanePoint)
    (hx : tr.CheckingCrossing (kp 0) p) :
    ∃! side, InKingHalfPlane (kp 0 .white).toPlane (kp 0 .black).toPlane side p ∧
      ∀ (c : Color) (d : RayDirection), OnRationalRay (kp 0 c).toPlane d p →
        d ∈ halfPlaneDirections (kp 0 .white).toPlane (kp 0 .black).toPlane side := by
  have he (c : Color) (d : RayDirection) (hr : OnRationalRay (kp 0 c).toPlane d p)
      (side : HalfPlaneSide) :
      InKingHalfPlane (kp 0 .white).toPlane (kp 0 .black).toPlane side p ↔
        d ∈ halfPlaneDirections (kp 0 .white).toPlane (kp 0 .black).toPlane side := by
    apply hr.inKingHalfPlane_iff
    · cases c <;> unfold halfPlaneCross <;> ring
    · exact tr.checkingCrossing_ne_king_of_periodic_checks kp hl hk hc hp hn p hx c
  obtain ⟨d, hd, hr⟩ := hx .white
  obtain ⟨side, hs, hu⟩ :=
    tr.checkingRay_halfPlane_unique_of_periodic_checks kp hl hk hc hp hn .white d hd
  have hside := (he .white d hr side).mpr hs
  exact ⟨side, ⟨hside, fun c d h => (he c d h side).mp hside⟩,
    fun s h => hu s ((he .white d hr s).mp h.1)⟩

end MPC.Chess.MoveTrace
