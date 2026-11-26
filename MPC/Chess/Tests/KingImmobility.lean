import MPC.Chess.CheckerReduction

namespace MPC.Chess.Tests

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

private def rayStart (axis : Fin 4) : Pos :=
  match axis.val with | 0 => (0, 3) | 1 => (3, 0) | 2 => (0, 0) | _ => (0, 6)

private def rayEnd (axis : Fin 4) : Pos :=
  match axis.val with | 0 => (6, 3) | 1 => (3, 6) | 2 => (6, 6) | _ => (6, 0)

private def stepAway (axis : Fin 4) : Pos := if axis.val = 1 then (4, 3) else (3, 4)

-- Both orientations on every file/rank/diagonal: eight sliding directions.
example (axis : Fin 4) (reverse : Bool) :
    let t := if reverse then rayStart axis else rayEnd axis
    ¬ (stepAway axis).aligned t := by
  have h : ∀ axis : Fin 4, ∀ reverse : Bool,
      let a := if reverse then rayEnd axis else rayStart axis
      let t := if reverse then rayStart axis else rayEnd axis
      a.aligned t ∧ Between a t (3, 3) ∧ ¬ Between a t (stepAway axis) ∧
      stepAway axis ≠ a ∧ stepAway axis ≠ t ∧
      attacks Board.empty ⟨.white, .king⟩ (3, 3) (stepAway axis) ∧
      ¬ attacks Board.empty ⟨.white, .king⟩ (3, 3) t ∧
      ¬ attacks Board.empty ⟨.white, .king⟩ (stepAway axis) t := by decide
  obtain ⟨ha, hs, hd, hda, hdt, hstep, hsa, hda'⟩ := h axis reverse
  exact not_aligned_of_king_step ha hs hd hda hdt hstep hsa hda'

-- Without separation after the move, stepping onto another line is possible.
example : Between (0, 3) (5, 3) (3, 3) ∧ ¬ Between (0, 3) (5, 3) (4, 4) ∧
    attacks Board.empty ⟨.white, .king⟩ (3, 3) (4, 4) ∧
    ¬ attacks Board.empty ⟨.white, .king⟩ (3, 3) (5, 3) ∧
    Pos.aligned (4, 4) (5, 3) ∧ attacks Board.empty ⟨.black, .king⟩ (5, 3) (4, 4) := by decide

private def kingStepBoard (c : Color) : Board := fun q =>
  if q = (3, 3) then some ⟨c, .king⟩
  else if q = (7, 3) then some ⟨c.opponent, .king⟩
  else if q = (0, 3) then some ⟨c, .rook⟩ else none

private def kingStepPositions (c : Color) : Color → Pos := fun o =>
  if o = c then (3, 3) else (7, 3)

private def kingStepMove : Move := .boardMove (3, 3) (3, 4) none

private def kingStepPosition (c : Color) : Position := ⟨kingStepBoard c, c, {}, none⟩

-- A legal checking king move exists without periodicity. It uncovers a rook.
example (c : Color) :
    LegalMove (kingStepPosition c) kingStepMove (kingStepPositions c) ∧
    ¬ inCheck (kingStepBoard c) c.opponent (7, 3) ∧
    inCheck (applyMove (kingStepPosition c) kingStepMove).board c.opponent (7, 3) ∧
    Pos.aligned (3, 3) (7, 3) ∧ ¬ Pos.aligned (3, 4) (7, 3) := by
  cases c <;> decide

example (c : Color) : Between (0, 3) (7, 3) (3, 3) ∧
    ¬ Between (0, 3) (7, 3) (3, 4) := by
  have hs : kingStepBoard c (3, 3) = some ⟨c, .king⟩ := by cases c <;> decide
  have hn : ¬ attacks (kingStepBoard c) ⟨c, .rook⟩ (0, 3) (7, 3) := by cases c <;> decide
  have ha : attacks ((kingStepBoard c).relocate (3, 3) (3, 4) none) ⟨c, .rook⟩ (0, 3) (7, 3) := by
    cases c <;> decide
  exact (new_attack_source_between _ _ _ _ _ _ _ hs hn ha).2

private def edgeBoard (c : Color) : Board := fun q =>
  if q = (0, 0) then some ⟨c, .king⟩
  else if q = (1, 1) then some ⟨c.opponent, .king⟩ else none

-- Adjacent kings attack symmetrically even on the edge and with arbitrary boards.
example (b : Board) (c : Color) : attacks b ⟨c, .king⟩ (1, 1) (0, 0) := by
  apply king_attack_symm Board.empty b c.opponent c (0, 0) (1, 1)
  cases c <;> decide

example (c : Color) :
    inCheck (edgeBoard c) c (0, 0) ∧ inCheck (edgeBoard c) c.opponent (1, 1) := by
  cases c <;> decide

private def emptyCheckBoard (c : Color) (knight : Bool) : Board := fun q =>
  if q = (4, 4) then some ⟨c, .king⟩
  else if q = (0, 0) then some ⟨c.opponent, .king⟩
  else if q = (if knight then (2, 3) else if c = .white then (3, 5) else (3, 3))
    then some ⟨c.opponent, if knight then .knight else .pawn⟩ else none

private def emptyCheckKings (c : Color) : Color → Pos := fun o =>
  if o = c then (4, 4) else (0, 0)

-- Empty traces satisfy the step conditions vacuously. Positive length cannot
-- be dropped from the theorem excluding pawn/knight checkers.
example (c : Color) (knight : Bool) :
    let tr := MoveTrace.empty ⟨emptyCheckBoard c knight, c, {}, none⟩
    tr.FollowsLegalMoves ∧ tr.BoardTurnPeriodic ∧
    tr.KingsWellPlaced (fun _ => emptyCheckKings c) ∧
    tr.EveryMoveChecksOpponent (fun _ => emptyCheckKings c) ∧
    inCheck (emptyCheckBoard c knight) c (emptyCheckKings c c) := by
  refine ⟨fun i => Fin.elim0 i, ⟨rfl, rfl⟩, ?_, fun i => Fin.elim0 i, ?_⟩
  · intro _
    change KingsWellPlaced (emptyCheckBoard c knight) (emptyCheckKings c)
    cases c <;> cases knight <;> decide
  · cases c <;> cases knight <;> decide

example (pos : Position) (kp : Fin 1 → Color → Pos)
    (hk : (MoveTrace.empty pos).KingsWellPlaced kp) (i j : Fin 1) : kp i = kp j := by
  exact (MoveTrace.empty pos).kingPositions_eq_of_periodic_checks kp
    (fun k => Fin.elim0 k) hk (fun k => Fin.elim0 k) ⟨rfl, rfl⟩ i j

private def knightBoard : Board := fun q =>
  if q = kingHome .white then some ⟨.white, .king⟩
  else if q = kingHome .black then some ⟨.black, .king⟩
  else if q = (1, 0) then some ⟨.white, .knight⟩
  else if q = (1, 7) then some ⟨.black, .knight⟩ else none

private def knightCycleMove (c : Color) : ℕ → Move
  | 0 => .boardMove (1, c.homeRank) (2, c.doubleStepTargetRank) none
  | 1 => .boardMove (1, c.opponent.homeRank) (2, c.opponent.doubleStepTargetRank) none
  | 2 => .boardMove (2, c.doubleStepTargetRank) (1, c.homeRank) none
  | _ => .boardMove (2, c.opponent.doubleStepTargetRank) (1, c.opponent.homeRank) none

private def knightCycleState (c : Color) : ℕ → Position
  | 0 => ⟨knightBoard, c, {}, none⟩
  | n + 1 => applyMove (knightCycleState c n) (knightCycleMove c n)

private def knightCycle (c : Color) : MoveTrace where
  len := 4
  states := fun i => knightCycleState c i.val
  moves := fun i => knightCycleMove c i.val

-- Knights are allowed to move. This legal periodic example does not satisfy
-- the mutual-check condition and has no captures or king movement.
example (c : Color) :
    (knightCycle c).FollowsLegalMoves ∧ (knightCycle c).BoardTurnPeriodic ∧
    (knightCycle c).KingsWellPlaced (fun _ => kingHome) ∧
    ¬ (knightCycle c).EveryMoveChecksOpponent (fun _ => kingHome) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i
    refine ⟨kingHome, ?_, rfl⟩
    have h : ∀ i : Fin 4, LegalMove (knightCycleState c i.val) (knightCycleMove c i.val) kingHome := by
      cases c <;> decide
    exact h i
  · funext q
    have h : ∀ q, (knightCycleState c 4).board q = knightBoard q := by cases c <;> decide
    exact h q
  · cases c <;> rfl
  · change ∀ i : Fin 5, KingsWellPlaced (knightCycleState c i.val).board kingHome
    cases c <;> decide
  · intro h
    have h0 := h (0 : Fin 4)
    have hn : ¬ inCheck (knightCycleState c 1).board c.opponent (kingHome c.opponent) := by
      cases c <;> decide
    exact hn h0

-- Without periodicity, a legal ordinary move can give a knight check.
private def knightCheckPosition (c : Color) : Position :=
  ⟨fun q => if q = (4, 4) then some ⟨c.opponent, .king⟩
    else if q = (7, 7) then some ⟨c, .king⟩
    else if q = (0, 2) then some ⟨c, .knight⟩ else none, c, {}, none⟩

example (c : Color) :
    let mv := Move.boardMove (0, 2) (2, 3) none
    LegalMove (knightCheckPosition c) mv (fun o => if o = c then (7, 7) else (4, 4)) ∧
      inCheck (applyMove (knightCheckPosition c) mv).board c.opponent (4, 4) := by
  cases c <;> decide

private def pawnCheckPosition (c : Color) : Position :=
  ⟨fun q => if q = (4, 4) then some ⟨c.opponent, .king⟩
    else if q = (7, 7) then some ⟨c, .king⟩
    else if q = (3, if c = .white then 2 else 6) then some ⟨c, .pawn⟩ else none, c, {}, none⟩

example (c : Color) :
    let mv := Move.boardMove (3, if c = .white then 2 else 6)
      (3, if c = .white then 3 else 5) none
    LegalMove (pawnCheckPosition c) mv (fun o => if o = c then (7, 7) else (4, 4)) ∧
      inCheck (applyMove (pawnCheckPosition c) mv).board c.opponent (4, 4) := by
  cases c <;> decide

end MPC.Chess.Tests
