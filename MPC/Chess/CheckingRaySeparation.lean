import MPC.Chess.KingLineExclusion

/-! King-line exclusion removes parallel overlaps from Definition 6.3 in
positive-length periodic checking traces. Parallel disjoint rays remain allowed. -/

namespace MPC.Chess

/-- A board square on a checking direction detects whether that supporting
line is the line through both origins. -/
theorem OnRay.collinear_iff_rayOffset_eq_zero {K L q : Pos} {d : RayDirection}
    (hr : OnRay K d q) : K.collinear L q ↔ rayOffset K.toPlane L.toPlane d = 0 := by
  obtain ⟨n, hn, hx, hy⟩ := (onRay_iff_positive_steps K q d).mp hr
  have he : K.collinear L q ↔
      (L.toInt.1 - K.toInt.1) * d.vector.2 = (L.toInt.2 - K.toInt.2) * d.vector.1 := by
    unfold Pos.collinear
    rw [hx, hy]
    simp only [add_sub_cancel_left]
    constructor
    · intro h
      apply mul_left_cancel₀ (ne_of_gt hn)
      nlinarith only [h]
    · intro h
      calc
        (L.toInt.1 - K.toInt.1) * (n * d.vector.2) =
            n * ((L.toInt.1 - K.toInt.1) * d.vector.2) := by ring
        _ = n * ((L.toInt.2 - K.toInt.2) * d.vector.1) := by rw [h]
        _ = n * d.vector.1 * (L.toInt.2 - K.toInt.2) := by ring
  rw [he]
  simp only [rayOffset, Pos.toPlane, sub_eq_zero]
  norm_cast

namespace MoveTrace

/-- No actual checking ray is supported on the line joining the two kings.
This is derived from Proposition 3.6, not imposed in `CheckingRay`. -/
theorem checkingRay_offset_ne_zero_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) :
    rayOffset (kp 0 c).toPlane (kp 0 c.opponent).toPlane d ≠ 0 := by
  intro hz
  obtain ⟨k, q, p, hq, ho, ha, hdir⟩ := hr
  have ha' : attacks (tr.states k).board p q (kp k c) := by
    rw [tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp k 0]; exact ha
  exact tr.checker_off_kingLine_of_periodic_checks kp hl hk hc hp hn k c q p hq ho ha'
    (hdir.collinear_iff_rayOffset_eq_zero.mpr hz)

theorem checkingRay_not_contains_otherKing_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) :
    ¬ OnRationalRay (kp 0 c).toPlane d (kp 0 c.opponent).toPlane := by
  intro h
  exact tr.checkingRay_offset_ne_zero_of_periodic_checks kp hl hk hc hp hn c d hr
    ((rayOffset_eq_zero_iff _ _ d).mpr h.2)

/-- A parallel ray from the other king cannot share a point with a checking
ray. This does not say that all pairs of checking directions are nonparallel. -/
theorem checkingRay_disjoint_parallel_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d e : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) (hpar : rayDet d e = 0) :
    ¬ ∃ p, OnRationalRay (kp 0 c).toPlane d p ∧ OnRationalRay (kp 0 c.opponent).toPlane e p := by
  intro hex
  have hz := ((parallel_rays_intersect_iff _ _ d e hpar).mp hex).1
  exact tr.checkingRay_offset_ne_zero_of_periodic_checks kp hl hk hc hp hn c d hr hz

/-- Under the trace conditions, the nonparallel solver enumerates all
crossings. The finite set and its order are constructed separately. -/
theorem checkingCrossing_iff_nonparallelIntersection_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (p : PlanePoint) :
    tr.CheckingCrossing (kp 0) p ↔ ∃ dw db,
      tr.CheckingRay (kp 0 .white) .white dw ∧ tr.CheckingRay (kp 0 .black) .black db ∧
      nonparallelIntersection (kp 0 .white).toPlane (kp 0 .black).toPlane dw db = some p := by
  constructor
  · intro h
    obtain ⟨dw, db, hw, hb, hpw, hpb⟩ := (tr.checkingCrossing_iff_white_black (kp 0) p).mp h
    refine ⟨dw, db, hw, hb, (nonparallelIntersection_eq_some_iff _ _ p dw db).mpr ⟨?_, hpw, hpb⟩⟩
    intro hpar
    exact tr.checkingRay_disjoint_parallel_of_periodic_checks kp hl hk hc hp hn .white dw db hw hpar
      ⟨p, hpw, hpb⟩
  · rintro ⟨dw, db, hw, hb, hi⟩
    exact tr.checkingCrossing_of_nonparallelIntersection (kp 0) p dw db hw hb hi

/-- Although the definition includes ray origins, a crossing in a positive
legal checking period is neither king's origin. -/
theorem checkingCrossing_ne_king_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (p : PlanePoint)
    (h : tr.CheckingCrossing (kp 0) p) (c : Color) : p ≠ (kp 0 c).toPlane := by
  intro he
  obtain ⟨d, hd, hr⟩ := h c.opponent
  apply tr.checkingRay_not_contains_otherKing_of_periodic_checks kp hl hk hc hp hn c.opponent d hd
  simpa only [Color.opponent_opponent, he] using hr

end MoveTrace
end MPC.Chess
