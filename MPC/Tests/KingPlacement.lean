import MPC.Trace.KingPlacement
import Lean
/-!
# MPC.Tests.KingPlacement

Consistent king positions can move. These examples assert the listed trace
conditions, not full move legality or periodic mutual checks.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "King placement verification must not import GameSeq"

namespace MPC

-- Missing kings, duplicate kings, incorrect pieces, and coincident positions.
example (kp : Player → Pos) :
    ¬ KingsWellPlaced { grid := fun _ => none, hand := fun _ => ∅ } kp := by
  intro h
  have hp := h.king_present .sente
  cases hp

example (board : Board) (kp : Player → Pos) (owner : Player) (p q : Pos)
    (hp : board.grid p = some ⟨owner, .king⟩) (hq : board.grid q = some ⟨owner, .king⟩)
    (hne : p ≠ q) : ¬ KingsWellPlaced board kp := by
  intro h
  exact hne (((h owner p).mp hp).trans ((h owner q).mp hq).symm)

-- The incorrect piece may have the wrong owner, the wrong type, or both.
example (board : Board) (kp : Player → Pos) (owner : Player) (piece : Piece)
    (hp : board.grid (kp owner) = some piece) (hbad : piece ≠ ⟨owner, .king⟩) :
    ¬ KingsWellPlaced board kp := by
  intro h
  exact hbad (Option.some.inj (hp.symm.trans (h.king_present owner)))

example (board : Board) (kp : Player → Pos) (heq : kp .sente = kp .gote) :
    ¬ KingsWellPlaced board kp := by
  intro h
  have hbad := h.positions_injective heq
  cases hbad

private def kingBoard (owner : Player) (movingKing : Pos) : Board :=
  { grid := fun q => if q = movingKing then some ⟨owner, .king⟩
      else if q = (0, 0) then some ⟨owner.opponent, .king⟩ else none
    hand := fun _ => ∅ }

private def kingPositions (owner : Player) (movingKing : Pos) (player : Player) : Pos :=
  if player = owner then movingKing else (0, 0)

private theorem kingBoard_placed (owner : Player) (pos : Pos) (hne : pos ≠ (0, 0)) :
    KingsWellPlaced (kingBoard owner pos) (kingPositions owner pos) := by
  intro player q
  cases owner <;> cases player <;> by_cases hq : q = pos <;> by_cases hz : q = (0, 0) <;>
    simp_all [kingBoard, kingPositions, Player.opponent]

private def kingState (owner : Player) : BoardState :=
  { board := kingBoard owner (4, 4), turn := owner }

private def kingTrace (owner : Player) : MoveTrace :=
  MoveTrace.single (kingState owner) (.boardMove (4, 4) (5, 4) false)

private def kingTracePositions (owner : Player) (i : Fin ((kingTrace owner).len + 1)) : Player → Pos :=
  kingPositions owner (if i.val = 0 then (4, 4) else (5, 4))

private theorem moved_king_board (owner : Player) :
    (applyMove (kingState owner) (.boardMove (4, 4) (5, 4) false)).board = kingBoard owner (5, 4) := by
  have hg : (applyMove (kingState owner) (.boardMove (4, 4) (5, 4) false)).board.grid =
      (kingBoard owner (5, 4)).grid := by
    funext q
    by_cases hs : q = (4, 4) <;> by_cases hd : q = (5, 4) <;>
      simp_all [applyMove, kingState, kingBoard, Board.setGrid]
  exact congr (congrArg Board.mk hg) rfl

private theorem kingTrace_placed (owner : Player) :
    (kingTrace owner).KingsWellPlaced (kingTracePositions owner) := by
  intro i
  change Fin 2 at i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact kingBoard_placed owner (4, 4) (by decide)
  · change KingsWellPlaced (applyMove (kingState owner) (.boardMove (4, 4) (5, 4) false)).board _
    rw [moved_king_board]
    exact kingBoard_placed owner (5, 4) (by decide)

-- Both owners can move a king while all four trace conditions and placement hold.
-- The opposing king is a concrete non-endpoint board-move tracking example.
example (owner : Player) :
    (kingTrace owner).FollowsTransitions ∧ (kingTrace owner).BoardMoveSourcesOwned ∧
    (kingTrace owner).BoardMoveEndpointsDistinct ∧
    (kingTrace owner).BoardMovesFollowCanMoveToOriented ∧
    (kingTrace owner).KingsWellPlaced (kingTracePositions owner) ∧
    kingTracePositions owner 1 owner ≠ kingTracePositions owner 0 owner ∧
    kingTracePositions owner 1 owner.opponent = kingTracePositions owner 0 owner.opponent := by
  have ht : (kingTrace owner).FollowsTransitions := MoveTrace.single_followsTransitions _ _
  have hs : (kingTrace owner).BoardMoveSourcesOwned := by
    intro i src dst flag hm
    change Fin 1 at i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change Move.boardMove (4, 4) (5, 4) false = .boardMove src dst flag at hm
    cases hm
    exact ⟨⟨owner, .king⟩, rfl, rfl⟩
  have hm : (kingTrace owner).BoardMovesFollowCanMoveToOriented := by
    intro i src dst flag piece hmove hp
    change Fin 1 at i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change Move.boardMove (4, 4) (5, 4) false = .boardMove src dst flag at hmove
    cases hmove
    change some (Piece.mk owner .king) = some piece at hp
    cases hp
    cases owner <;> left <;> decide
  have hk := kingTrace_placed owner
  have hdst := (kingTrace owner).kingPos_after_boardMove_king _ ht hk (0 : Fin 1) owner
    (4, 4) (5, 4) false rfl rfl
  refine ⟨ht, hs, (kingTrace owner).boardMoveEndpointsDistinct_of_oriented hs hm, hm, hk, ?_, ?_⟩
  · have hbefore : kingTracePositions owner 0 owner = (4, 4) := by
      simp [kingTracePositions, kingPositions]
    rw [show kingTracePositions owner 1 owner = (5, 4) from hdst, hbefore]
    decide
  · exact (kingTrace owner).kingPos_after_boardMove_of_ne _ ht hk (0 : Fin 1) owner.opponent
      (4, 4) (5, 4) false rfl (by cases owner <;> decide) (by cases owner <;> decide)

-- A pawn drop away from both kings has consistent before/after positions.
-- This does not establish general drop legality or a general preservation theorem.
example (owner : Player) :
    let tr := MoveTrace.single (kingState owner) (.dropMove .pawn (5, 4))
    let kp : Fin (tr.len + 1) → Player → Pos := fun _ => kingPositions owner (4, 4)
    tr.FollowsTransitions ∧ tr.KingsWellPlaced kp ∧
      ∀ player, kp 1 player = kp 0 player := by
  dsimp only
  let tr := MoveTrace.single (kingState owner) (.dropMove .pawn (5, 4))
  let kp : Fin (tr.len + 1) → Player → Pos := fun _ => kingPositions owner (4, 4)
  have hk : tr.KingsWellPlaced kp := by
    intro i
    change Fin 2 at i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact kingBoard_placed owner (4, 4) (by decide)
    · intro player q
      change (applyMove (kingState owner) (.dropMove .pawn (5, 4))).board.grid q =
        some ⟨player, .king⟩ ↔ q = kingPositions owner (4, 4) player
      cases owner <;> cases player <;> by_cases hd : q = (5, 4) <;>
        by_cases hs : q = (4, 4) <;> by_cases hz : q = (0, 0) <;>
        simp_all [applyMove, kingState, kingBoard, kingPositions, Board.setGrid,
          Board.removeFromHand, Player.opponent]
  have ht : tr.FollowsTransitions := MoveTrace.single_followsTransitions _ _
  refine ⟨ht, hk, ?_⟩
  intro player
  exact tr.kingPos_after_dropMove_of_ne kp ht hk (0 : Fin 1) player .pawn (5, 4) rfl
    (by cases owner <;> cases player <;> decide)

-- Length zero still has an initial state; its placement condition is not vacuous.
example (initial : BoardState) (kp : Player → Pos) :
    let tr : MoveTrace := { len := 0, states := fun _ => initial, moves := Fin.elim0 }
    tr.KingsWellPlaced (fun _ => kp) ↔ KingsWellPlaced initial.board kp := by
  exact ⟨fun h => h 0, fun h _ => h⟩

example (board : Board) (hand : Player → Hand) (kp : Player → Pos) :
    KingsWellPlaced { board with hand := hand } kp ↔ KingsWellPlaced board kp := Iff.rfl

end MPC
