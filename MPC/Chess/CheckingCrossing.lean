import MPC.Chess.CheckingRayMoves
import MPC.Chess.RayIntersection

/-! Definition 6.3 on rational points. A crossing belongs to a checking ray
of each king, including ray origins. This relation includes parallel overlaps; no finiteness or
transversality premise is silently built into it. -/

namespace MPC.Chess.MoveTrace

def CheckingCrossing (tr : MoveTrace) (kp : Color → Pos) (p : PlanePoint) : Prop :=
  ∀ owner, ∃ d, tr.CheckingRay (kp owner) owner d ∧ OnRationalRay (kp owner).toPlane d p

instance (tr : MoveTrace) (kp : Color → Pos) (p : PlanePoint) :
    Decidable (tr.CheckingCrossing kp p) :=
  inferInstanceAs (Decidable (∀ owner, ∃ d,
    tr.CheckingRay (kp owner) owner d ∧ OnRationalRay (kp owner).toPlane d p))

theorem checkingCrossing_iff_white_black (tr : MoveTrace) (kp : Color → Pos) (p : PlanePoint) :
    tr.CheckingCrossing kp p ↔ ∃ dw db,
      tr.CheckingRay (kp .white) .white dw ∧ tr.CheckingRay (kp .black) .black db ∧
      OnRationalRay (kp .white).toPlane dw p ∧ OnRationalRay (kp .black).toPlane db p := by
  constructor
  · intro h
    obtain ⟨dw, hw, hpw⟩ := h .white
    obtain ⟨db, hb, hpb⟩ := h .black
    exact ⟨dw, db, hw, hb, hpw, hpb⟩
  · rintro ⟨dw, db, hw, hb, hpw, hpb⟩ owner
    cases owner
    · exact ⟨dw, hw, hpw⟩
    · exact ⟨db, hb, hpb⟩

theorem checkingCrossing_toPlane_iff (tr : MoveTrace) (kp : Color → Pos) (p : Pos) :
    tr.CheckingCrossing kp p.toPlane ↔ ∀ owner,
      ∃ d, tr.CheckingRay (kp owner) owner d ∧ (p = kp owner ∨ OnRay (kp owner) d p) := by
  simp only [CheckingCrossing, onRationalRay_toPlane_iff]

/-- A computed nonparallel intersection is a crossing when both rays have
actual checking witnesses. The converse requires ruling out parallel overlaps. -/
theorem checkingCrossing_of_nonparallelIntersection (tr : MoveTrace) (kp : Color → Pos)
    (p : PlanePoint) (dw db : RayDirection)
    (hw : tr.CheckingRay (kp .white) .white dw) (hb : tr.CheckingRay (kp .black) .black db)
    (hi : nonparallelIntersection (kp .white).toPlane (kp .black).toPlane dw db = some p) :
    tr.CheckingCrossing kp p := by
  obtain ⟨_, hpw, hpb⟩ := (nonparallelIntersection_eq_some_iff _ _ p dw db).mp hi
  exact (tr.checkingCrossing_iff_white_black kp p).mpr ⟨dw, db, hw, hb, hpw, hpb⟩

/-- Lemma 6.2 supplies both endpoint crossings without assuming ray
transversality, finite intersections, or a preselected intersection order. -/
theorem boardMove_checkingCrossings_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) :
    tr.CheckingCrossing (kp 0) src.toPlane ∧ tr.CheckingCrossing (kp 0) dst.toPlane := by
  constructor
  · apply (tr.checkingCrossing_toPlane_iff (kp 0) src).mpr
    intro owner
    obtain ⟨d, hd, hr⟩ := tr.source_on_checkingRay_of_periodic_checks kp hl hk hc hp i src dst hm owner
    exact ⟨d, hd, Or.inr hr⟩
  · apply (tr.checkingCrossing_toPlane_iff (kp 0) dst).mpr
    intro owner
    obtain ⟨d, hd, hr⟩ := tr.destination_on_checkingRay_of_periodic_checks kp hl hk hc hp i src dst hm owner
    exact ⟨d, hd, Or.inr hr⟩

/-- The paper's transition to Definition 6.3: every move joins crossings
on distinct rational rays of each king. Special moves are excluded by the
existing periodic reduction, not by the definition of the trace. -/
theorem every_move_between_checkingCrossings (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) :
    ∃ src dst, tr.moves i = .boardMove src dst none ∧
      tr.CheckingCrossing (kp 0) src.toPlane ∧ tr.CheckingCrossing (kp 0) dst.toPlane ∧
      ∀ (owner : Color) (d : RayDirection),
        ¬ (OnRationalRay (kp 0 owner).toPlane d src.toPlane ∧
          OnRationalRay (kp 0 owner).toPlane d dst.toPlane) := by
  obtain ⟨src, dst, hm⟩ := tr.ordinaryMoves_of_periodic_checks kp hl hk hc hp i
  obtain ⟨hs, hd⟩ := tr.boardMove_checkingCrossings_of_periodic_checks kp hl hk hc hp i src dst hm
  refine ⟨src, dst, hm, hs, hd, ?_⟩
  intro owner d h
  apply tr.not_same_ray_of_periodic_checks kp hl hk hc hp i src dst hm owner d
  obtain ⟨_, _, hrs⟩ := tr.source_on_checkingRay_of_periodic_checks kp hl hk hc hp i src dst hm owner
  obtain ⟨_, _, hrd⟩ := tr.destination_on_checkingRay_of_periodic_checks kp hl hk hc hp i src dst hm owner
  exact ⟨((onRationalRay_toPlane_iff _ _ d).mp h.1).resolve_left hrs.ne,
    ((onRationalRay_toPlane_iff _ _ d).mp h.2).resolve_left hrd.ne⟩

end MPC.Chess.MoveTrace
