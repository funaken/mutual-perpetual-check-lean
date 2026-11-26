import MPC.Trace.CheckOriginTrace
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.CheckOriginTrace

A two-move mutual-check trace (drop check, then a king capture opening a rook
line), and the necessity of initial non-mover safety and source ownership.
Occupied squares, empty hands, and king captures make no full-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Check origin trace verification must not import GameSeq"

namespace MPC
namespace CheckOriginTraceTests

/-! ## Two-move mutual check -/

private def row (p : Player) : Fin 9 := if p = .sente then 8 else 0
private def front (p : Player) : Fin 9 := if p = .sente then 7 else 1
private def start (p : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = (0, row p) then some ⟨p, .king⟩
        else if q = (4, row p) then some ⟨p.opponent, .king⟩
        else if q = (8, row p) then some ⟨p.opponent, .rook⟩ else none
      hand := fun _ => ∅ }
    turn := p }
private def drop (p : Player) : Move := .dropMove .gold (4, front p)
private def capture (p : Player) : Move := .boardMove (4, row p) (4, front p) false
private def mid (p : Player) : BoardState := applyMove (start p) (drop p)
private def finish (p : Player) : BoardState := applyMove (mid p) (capture p)
private def trace (p : Player) : MoveTrace where
  len := 2
  states := fun k => if k.val = 0 then start p else if k.val = 1 then mid p else finish p
  moves := fun k => if k.val = 0 then drop p else capture p
private def kings (p : Player) : Player → Pos := fun o => if o = p then (0, row p) else (4, row p)

private theorem all_two (p : Player) {P : Fin (trace p).len → Prop}
    (h0 : P ⟨0, show 0 < 2 by decide⟩) (h1 : P ⟨1, show 1 < 2 by decide⟩) : ∀ i, P i := by
  intro ⟨i, hi⟩
  have hi' : i < 2 := hi
  interval_cases i
  · exact h0
  · exact h1

private theorem front_ne_row (p : Player) : ((4, front p) : Pos) ≠ (4, row p) := by
  cases p <;> decide

private theorem mid_grid (p : Player) (q : Pos) :
    (mid p).board.grid q = if q = (4, front p) then some ⟨p, .gold⟩ else (start p).board.grid q := by
  by_cases hf : q = (4, front p)
  · subst q; rw [ite_eq_left rfl]
    exact applyMove_dropMove_grid_dst (start p) .gold (4, front p)
  · rw [ite_eq_right hf]
    exact applyMove_dropMove_grid_other (start p) .gold (4, front p) q hf

private theorem finish_grid (p : Player) (q : Pos) :
    (finish p).board.grid q =
      if q = (4, front p) then some ⟨p.opponent, .king⟩
      else if q = (4, row p) then none else (start p).board.grid q := by
  by_cases hf : q = (4, front p)
  · subst q; rw [ite_eq_left rfl]; cases p <;> rfl
  · by_cases hr : q = (4, row p)
    · subst q; rw [ite_eq_right hf, ite_eq_left rfl]; cases p <;> rfl
    · rw [ite_eq_right hf, ite_eq_right hr]
      exact (applyMove_boardMove_grid_other (mid p) (4, row p) (4, front p) false q hr hf).trans
        (applyMove_dropMove_grid_other (start p) .gold (4, front p) q hf)

private theorem row_clear (b : Board) (p : Player) :
    pathClear b (8, row p) (0, row p) ↔
      b.grid (7, row p) = none ∧ b.grid (6, row p) = none ∧ b.grid (5, row p) = none ∧
      b.grid (4, row p) = none ∧ b.grid (3, row p) = none ∧ b.grid (2, row p) = none ∧
      b.grid (1, row p) = none := by
  have hc := pathClear_iff_of_exact_steps b (8, row p) (0, row p) (-1, 0) 8 (by decide)
    (by decide) (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
  constructor
  · intro h
    have h1 := hc.mp h 1 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h2 := hc.mp h 2 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h3 := hc.mp h 3 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h4 := hc.mp h 4 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h5 := hc.mp h 5 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h6 := hc.mp h 6 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h7 := hc.mp h 7 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    cases p <;> exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    apply hc.mpr
    intro j hj hjn hob
    interval_cases j <;> cases p <;> assumption

private theorem rook_attack (b : Board) (p : Player) :
    attacksOriented b p.opponent .rook (8, row p) (0, row p) ↔ pathClear b (8, row p) (0, row p) := by
  constructor
  · rintro (hs | ⟨_, _, _, _, _, _, _, hc⟩)
    · simp [PieceType.stepDirs] at hs
    · exact hc
  · intro hc
    refine Or.inr ⟨(-1, 0), ?_, ?_, 8, by decide, ?_, ?_, hc⟩ <;> cases p <;> decide

private theorem placed (p : Player) : KingsWellPlaced (start p).board (kings p) := by
  intro o q
  cases p
  · cases o <;> by_cases ha : q = (0, 8) <;> by_cases hb : q = (4, 8) <;>
      by_cases hc : q = (8, 8) <;> simp_all [start, kings, row, Player.opponent]
  · cases o <;> by_cases ha : q = (0, 0) <;> by_cases hb : q = (4, 0) <;>
      by_cases hc : q = (8, 0) <;> simp_all [start, kings, row, Player.opponent]

-- Initially the player not to move is safe: only the mover's king is its enemy.
private theorem start_safe (p : Player) :
    ¬ inCheckOriented (start p).board p.opponent (4, row p) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [start] at hp
  split_ifs at hp with h0 h4 h8
  · cases hp; subst pos
    cases p <;> simp [attacksOriented, canMoveToOriented, PieceType.stepDirs,
      PieceType.slideDirs, Pos.dirTo, Dir.forPlayer, Dir.flip, row] at ha
  · cases hp; cases p <;> cases ho
  · cases hp; cases p <;> cases ho

-- After the drop the mover is safe: the rook line is still blocked by the king.
private theorem mid_safe (p : Player) : ¬ inCheckOriented (mid p).board p (0, row p) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  rw [mid_grid] at hp
  dsimp only [start] at hp
  split_ifs at hp with hf h0 h4 h8
  · cases hp; cases p <;> cases ho
  · cases hp; cases p <;> cases ho
  · cases hp; subst pos
    cases p <;> simp [attacksOriented, canMoveToOriented, PieceType.stepDirs,
      PieceType.slideDirs, Pos.dirTo, Dir.forPlayer, Dir.flip, row] at ha <;> revert ha <;> decide
  · cases hp; subst pos
    exact absurd ((row_clear _ p).mp ((rook_attack _ p).mp ha)).2.2.2.1 (by cases p <;> decide)

-- After the capture the second mover's king is safe: the gold has been taken.
private theorem finish_safe (p : Player) :
    ¬ inCheckOriented (finish p).board p.opponent (4, front p) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  rw [finish_grid] at hp
  dsimp only [start] at hp
  split_ifs at hp with hf hr h0 h8
  · cases hp; cases p <;> cases ho
  · cases hp; subst pos
    cases p <;> simp [attacksOriented, canMoveToOriented, PieceType.stepDirs,
      PieceType.slideDirs, Pos.dirTo, Dir.forPlayer, Dir.flip, row, front] at ha
  · cases hp; cases p <;> cases ho

private theorem drop_check (p : Player) :
    hasDestinationCheckerOriented (mid p).board (drop p) p.opponent (4, row p) := by
  refine ⟨⟨p, .gold⟩, applyMove_dropMove_grid_dst (start p) .gold (4, front p), ?_, ?_⟩
  · cases p <;> rfl
  · cases p <;> left <;> decide

private theorem rook_check (p : Player) : inCheckOriented (finish p).board p (0, row p) := by
  refine ⟨(8, row p), ⟨p.opponent, .rook⟩, by cases p <;> rfl, rfl, ?_⟩
  apply (rook_attack _ p).mpr
  apply (row_clear _ p).mpr
  cases p <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem capture_no_destination (p : Player) :
    ¬ hasDestinationCheckerOriented (finish p).board (capture p) p (0, row p) := by
  rintro ⟨piece, hp, _, ha⟩
  change (finish p).board.grid (4, front p) = some piece at hp
  rw [finish_grid, ite_eq_left rfl] at hp
  cases hp
  cases p <;> simp [attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
    capture, Move.destination, Pos.dirTo, Dir.forPlayer, Dir.flip, row, front] at ha <;>
    revert ha <;> decide

-- Both first movers. Every move checks and leaves its own king safe, so the
-- derived classification applies with generated positions: the drop checks from
-- its destination, and the capture (moving the second mover's own king, while the
-- target king stays put) checks only through the unblocked rook.
example (p : Player) :
    let tr := trace p
    let kp := tr.kingPositionsFrom (kings p)
    tr.KingsWellPlaced kp ∧ tr.EveryMoveChecksOpponent kp ∧ tr.EveryMoveLeavesOwnKingSafe kp ∧
    kp 2 p = kp 1 p ∧ kp 2 p.opponent ≠ kp 1 p.opponent ∧
    hasDestinationCheckerOriented (tr.after (0 : Fin 2)).board (tr.moves (0 : Fin 2))
      p.opponent (kp 1 p.opponent) ∧
    hasUnblockedCheckerOriented (tr.before (1 : Fin 2)).board (tr.after (1 : Fin 2)).board
      (tr.moves (1 : Fin 2)) p (kp 2 p) := by
  dsimp only
  have ht : (trace p).FollowsTransitions := by
    unfold MoveTrace.FollowsTransitions
    exact all_two p rfl rfl
  have hs : (trace p).BoardMoveSourcesOwned := by
    unfold MoveTrace.BoardMoveSourcesOwned
    refine all_two p ?_ ?_
    · intro src dst pr hm
      change Move.dropMove _ _ = _ at hm
      cases hm
    · intro src dst pr hm
      change Move.boardMove (4, row p) (4, front p) false = .boardMove src dst pr at hm
      cases hm
      exact ⟨⟨p.opponent, .king⟩, by cases p <;> rfl, by cases p <;> rfl⟩
  have ha : (trace p).MoveDestinationsAvoidKings := by
    unfold MoveTrace.MoveDestinationsAvoidKings
    refine all_two p ?_ ?_ <;> intro o <;> cases p <;> cases o <;> decide
  have hd : (trace p).DropMovesAreNonKings := by
    unfold MoveTrace.DropMovesAreNonKings
    refine all_two p ?_ ?_
    · intro pt dst hm
      change Move.dropMove .gold (4, front p) = .dropMove pt dst at hm
      cases hm; decide
    · intro pt dst hm
      change Move.boardMove _ _ _ = _ at hm
      cases hm
  have hk := (trace p).kingsWellPlaced_kingPositionsFrom (kings p) ht ha hd (placed p)
  have hsafe : (trace p).EveryMoveLeavesOwnKingSafe ((trace p).kingPositionsFrom (kings p)) := by
    unfold MoveTrace.EveryMoveLeavesOwnKingSafe
    refine all_two p ?_ ?_
    · cases p <;> exact mid_safe _
    · cases p
      exacts [finish_safe .sente, finish_safe .gote]
  have hc : (trace p).EveryMoveChecksOpponent ((trace p).kingPositionsFrom (kings p)) := by
    unfold MoveTrace.EveryMoveChecksOpponent
    refine all_two p ?_ ?_
    · cases p <;> exact inCheckOriented_of_destinationChecker _ _ _ _ (drop_check _)
    · cases p
      exacts [rook_check .sente, rook_check .gote]
  have hcls := ((trace p).everyMoveChecksOpponent_kingPositionsFrom_iff_destination_or_unblocked
    (kings p) ht hs ha hd (placed p) hsafe (by cases p <;> exact start_safe _)).mp hc
  refine ⟨hk, hc, hsafe, by cases p <;> rfl, by cases p <;> decide, ?_, ?_⟩
  · cases p <;> exact drop_check _
  · cases p
    exacts [(hcls (1 : Fin 2)).resolve_left (capture_no_destination .sente),
      (hcls (1 : Fin 2)).resolve_left (capture_no_destination .gote)]

/-! ## Initial non-mover safety cannot be dropped -/

private def col (p : Player) (j : Fin 9) : Pos := (0, if p = .sente then j else 4 - j)
private def checked (p : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = col p 0 then some ⟨p, .rook⟩
        else if q = (5, 4) then some ⟨p, .gold⟩
        else if q = (8, 8) then some ⟨p, .king⟩
        else if q = col p 4 then some ⟨p.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := p }
private def shuffle : Move := .boardMove (5, 4) (6, 4) false
private def checkedKings (p : Player) : Player → Pos := fun o => if o = p then (8, 8) else col p 4

private theorem col_clear (b : Board) (p : Player) :
    pathClear b (col p 0) (col p 4) ↔
      b.grid (col p 1) = none ∧ b.grid (col p 2) = none ∧ b.grid (col p 3) = none := by
  have hc := pathClear_iff_of_exact_steps b (col p 0) (col p 4)
    (0, if p = .sente then 1 else -1) 4 (by cases p <;> decide) (by decide)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
  constructor
  · intro h
    have h1 := hc.mp h 1 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h2 := hc.mp h 2 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h3 := hc.mp h 3 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    cases p <;> exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    apply hc.mpr
    intro j hj hjn hob
    interval_cases j <;> cases p <;> assumption

private theorem col_attack (b : Board) (p : Player) :
    attacksOriented b p .rook (col p 0) (col p 4) ↔ pathClear b (col p 0) (col p 4) := by
  constructor
  · rintro (hs | ⟨_, _, _, _, _, _, _, hc⟩)
    · simp [PieceType.stepDirs] at hs
    · exact hc
  · intro hc
    refine Or.inr ⟨(0, if p = .sente then 1 else -1), ?_, ?_, 4, by decide, ?_, ?_, hc⟩ <;>
      cases p <;> decide

private theorem shuffled_grid (p : Player) (q : Pos) :
    (applyMove (checked p) shuffle).board.grid q =
      if q = (6, 4) then some ⟨p, .gold⟩
      else if q = (5, 4) then none else (checked p).board.grid q := by
  by_cases hd : q = (6, 4)
  · subst q; rw [ite_eq_left rfl]; cases p <;> rfl
  · by_cases hs : q = (5, 4)
    · subst q; rw [ite_eq_right hd, ite_eq_left rfl]; cases p <;> rfl
    · rw [ite_eq_right hd, ite_eq_right hs]
      exact applyMove_boardMove_grid_other (checked p) (5, 4) (6, 4) false q hs hd

private theorem checked_placed (p : Player) : KingsWellPlaced (checked p).board (checkedKings p) := by
  intro o q
  cases p <;> cases o <;> by_cases h1 : q = (0, 0) <;> by_cases h2 : q = (0, 4) <;>
    by_cases h3 : q = (5, 4) <;> by_cases h4 : q = (8, 8) <;>
    simp_all [checked, checkedKings, col, Player.opponent]

private theorem checked_before (p : Player) :
    inCheckOriented (checked p).board p.opponent (col p 4) :=
  ⟨col p 0, ⟨p, .rook⟩, by cases p <;> rfl, by cases p <;> rfl,
    (col_attack _ p).mpr ((col_clear _ p).mpr (by cases p <;> exact ⟨rfl, rfl, rfl⟩))⟩

private theorem checked_after (p : Player) :
    inCheckOriented (applyMove (checked p) shuffle).board p.opponent (col p 4) :=
  ⟨col p 0, ⟨p, .rook⟩, by cases p <;> rfl, by cases p <;> rfl,
    (col_attack _ p).mpr ((col_clear _ p).mpr (by cases p <;> exact ⟨rfl, rfl, rfl⟩))⟩

private theorem shuffle_safe (p : Player) :
    ¬ inCheckOriented (applyMove (checked p) shuffle).board p (8, 8) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  rw [shuffled_grid] at hp
  dsimp only [checked] at hp
  split_ifs at hp
  · cases hp; cases p <;> cases ho
  · cases hp; cases p <;> cases ho
  · cases hp; cases p <;> cases ho
  · cases hp; subst pos
    cases p <;> simp [attacksOriented, canMoveToOriented, PieceType.stepDirs,
      PieceType.slideDirs, col, Pos.dirTo, Dir.forPlayer, Dir.flip] at ha <;> revert ha <;> decide

private theorem shuffle_no_destination (p : Player) :
    ¬ hasDestinationCheckerOriented (applyMove (checked p) shuffle).board shuffle p.opponent (col p 4) := by
  rintro ⟨piece, hp, _, ha⟩
  change (applyMove (checked p) shuffle).board.grid (6, 4) = some piece at hp
  rw [shuffled_grid, ite_eq_left rfl] at hp
  cases hp
  cases p <;> simp [attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
    shuffle, Move.destination, col, Pos.dirTo, Dir.forPlayer, Dir.flip] at ha

private theorem shuffle_no_unblocked (p : Player) :
    ¬ hasUnblockedCheckerOriented (checked p).board (applyMove (checked p) shuffle).board shuffle
      p.opponent (col p 4) := by
  rintro ⟨pos, piece, _, _, hb, _, ho, ha, _, _, hblk, _⟩
  dsimp only [checked] at hb
  split_ifs at hb
  · subst pos
    exact hblk ((col_clear _ p).mpr (by cases p <;> exact ⟨rfl, rfl, rfl⟩))
  · cases hb; subst pos
    cases p <;> simp [attacksOriented, canMoveToOriented, PieceType.stepDirs,
      PieceType.slideDirs, col, Pos.dirTo, Dir.forPlayer, Dir.flip] at ha
  · cases hb; cases p <;> cases ho

-- Every premise except initial non-mover safety holds and every move checks,
-- but the continuing rook check is neither a destination nor an unblocked check.
example (p : Player) :
    let tr := MoveTrace.single (checked p) shuffle
    let kp := tr.kingPositionsFrom (checkedKings p)
    tr.BoardMoveSourcesOwned ∧ tr.KingsWellPlaced kp ∧ tr.EveryMoveLeavesOwnKingSafe kp ∧
    ¬ tr.InitialOpponentKingSafe kp ∧ tr.EveryMoveChecksOpponent kp ∧
    ¬ (hasDestinationCheckerOriented (tr.after (0 : Fin 1)).board (tr.moves (0 : Fin 1))
        p.opponent (kp 1 p.opponent) ∨
      hasUnblockedCheckerOriented (tr.before (0 : Fin 1)).board (tr.after (0 : Fin 1)).board
        (tr.moves (0 : Fin 1)) p.opponent (kp 1 p.opponent)) := by
  dsimp only
  let tr := MoveTrace.single (checked p) shuffle
  have ht := MoveTrace.single_followsTransitions (checked p) shuffle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i src dst pr hm; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (5, 4) (6, 4) false = .boardMove src dst pr at hm
    cases hm
    exact ⟨⟨p, .gold⟩, by cases p <;> rfl, rfl⟩
  · apply MoveTrace.kingsWellPlaced_kingPositionsFrom tr (checkedKings p) ht
    · intro i o; have hi := Fin.eq_zero i; subst i
      change (checked p).board.grid (6, 4) ≠ some ⟨o, .king⟩
      cases p <;> cases o <;> decide
    · intro i pt dst hm; change Move.boardMove _ _ _ = .dropMove pt dst at hm; cases hm
    · exact checked_placed p
  · intro i; have hi := Fin.eq_zero i; subst i
    cases p <;> exact shuffle_safe _
  · intro h; cases p <;> exact h (checked_before _)
  · intro i; have hi := Fin.eq_zero i; subst i
    cases p <;> exact checked_after _
  · cases p <;> exact fun h => h.elim (shuffle_no_destination _) (shuffle_no_unblocked _)

/-! ## Source ownership cannot be dropped -/

private def kingsOnly (p : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = (0, 0) then some ⟨p, .king⟩ else if q = (4, 4) then some ⟨p.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := p }
private def onlyKings (p : Player) : Player → Pos := fun o => if o = p then (0, 0) else (4, 4)

private theorem kingsOnly_placed (p : Player) : KingsWellPlaced (kingsOnly p).board (onlyKings p) := by
  intro o q
  cases p <;> cases o <;> by_cases h1 : q = (0, 0) <;> by_cases h2 : q = (4, 4) <;>
    simp_all [kingsOnly, onlyKings, Player.opponent]

-- If the mover may move the opponent's king, placement still holds but the
-- non-mover's generated position changes.
example (p : Player) :
    let tr := MoveTrace.single (kingsOnly p) (.boardMove (4, 4) (4, 5) false)
    let kp := tr.kingPositionsFrom (onlyKings p)
    tr.KingsWellPlaced kp ∧ ¬ tr.BoardMoveSourcesOwned ∧ kp 1 p.opponent ≠ kp 0 p.opponent := by
  dsimp only
  refine ⟨?_, ?_, by cases p <;> decide⟩
  · apply MoveTrace.kingsWellPlaced_kingPositionsFrom _ (onlyKings p)
      (MoveTrace.single_followsTransitions _ _)
    · intro i o; have hi := Fin.eq_zero i; subst i
      change (kingsOnly p).board.grid (4, 5) ≠ some ⟨o, .king⟩
      cases p <;> cases o <;> decide
    · intro i pt dst hm; change Move.boardMove _ _ _ = .dropMove pt dst at hm; cases hm
    · exact kingsOnly_placed p
  · intro h
    obtain ⟨piece, hp, ho⟩ := h (0 : Fin 1) (4, 4) (4, 5) false rfl
    cases p <;> cases hp <;> cases ho

/-! ## Length zero -/

-- With no moves, all-state non-mover safety is exactly initial safety.
example (s : BoardState) (kp : Fin 1 → Player → Pos) :
    let tr : MoveTrace := ⟨0, fun _ => s, Fin.elim0⟩
    (∀ k : Fin 1, ¬ inCheckOriented s.board s.turn.opponent (kp k s.turn.opponent)) ↔
      tr.InitialOpponentKingSafe kp := by
  intro tr
  exact (tr.everyStateOpponentSafe_iff kp (fun i => i.elim0)).trans
    ⟨fun h => h.1, fun h => ⟨h, fun i => i.elim0⟩⟩

end CheckOriginTraceTests
end MPC
