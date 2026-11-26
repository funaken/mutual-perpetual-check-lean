import MPC.Trace.MoveTraceCheck
import Lean
/-!
# MPC.Tests.MoveTraceCheck

Checks and self-safety use actual after-state king positions. Examples are
 and make no complete-legality or periodicity claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Trace check verification must not import GameSeq"

namespace MPC

private def pawnDst : Player → Pos
  | .sente => (4, 5)
  | .gote => (4, 3)

private def enemyKing : Player → Pos
  | .sente => (4, 6)
  | .gote => (4, 2)

private def pawnKings (turn : Player) (owner : Player) : Pos :=
  if owner = turn then (0, 0) else enemyKing turn

private def pawnState (turn : Player) (drop : Bool) : BoardState :=
  { board :=
      { grid := fun q => if q = (0, 0) then some ⟨turn, .king⟩
          else if q = enemyKing turn then some ⟨turn.opponent, .king⟩
          else if q = (4, 4) ∧ drop = false then some ⟨turn, .pawn⟩ else none
        hand := fun _ => ∅ }
    turn := turn }

private def pawnMove (turn : Player) (drop promote : Bool) : Move :=
  if drop then .dropMove .pawn (pawnDst turn)
  else .boardMove (4, 4) (pawnDst turn) promote

private def pawnTrace (turn : Player) (drop promote : Bool) : MoveTrace :=
  MoveTrace.single (pawnState turn drop) (pawnMove turn drop promote)

private theorem pawn_initial_placed (turn : Player) (drop : Bool) :
    KingsWellPlaced (pawnState turn drop).board (pawnKings turn) := by
  intro owner q
  cases turn <;> cases owner <;> cases drop <;>
    by_cases h0 : q = (0, 0) <;> by_cases he : q = (4, 6) <;>
    by_cases he' : q = (4, 2) <;> by_cases h4 : q = (4, 4) <;>
    simp_all [pawnState, pawnKings, enemyKing, Player.opponent]

private theorem pawn_avoidsKings (turn : Player) (drop promote : Bool) :
    (pawnTrace turn drop promote).MoveDestinationsAvoidKings := by
  intro i
  change Fin 1 at i
  have hi := Fin.eq_zero i
  subst i
  cases turn <;> cases drop <;> cases promote <;> intro owner <;> cases owner <;> decide

private theorem pawn_nonKingDrops (turn : Player) (drop promote : Bool) :
    (pawnTrace turn drop promote).DropMovesAreNonKings := by
  intro i pt dst hm
  cases drop <;> simp [pawnTrace, MoveTrace.single, pawnMove] at hm
  obtain ⟨rfl, rfl⟩ := hm
  decide

private theorem pawn_checks (turn : Player) (drop promote : Bool) :
    (pawnTrace turn drop promote).EveryMoveChecksOpponent
      ((pawnTrace turn drop promote).kingPositionsFrom (pawnKings turn)) := by
  intro i
  change Fin 1 at i
  have hi := Fin.eq_zero i
  subst i
  refine ⟨pawnDst turn, ⟨turn, if drop then .pawn else if promote then .tokin else .pawn⟩,
    ?_, ?_, ?_⟩
  · cases turn <;> cases drop <;> cases promote <;> rfl
  · cases turn <;> rfl
  · cases turn <;> cases drop <;> cases promote <;> left <;> decide

private theorem pawn_safe (turn : Player) (drop promote : Bool) :
    (pawnTrace turn drop promote).EveryMoveLeavesOwnKingSafe
      ((pawnTrace turn drop promote).kingPositionsFrom (pawnKings turn)) := by
  intro i
  change Fin 1 at i
  have hi := Fin.eq_zero i
  subst i
  rintro ⟨q, piece, hp, ho, ha⟩
  cases turn <;> cases drop <;> cases promote <;>
    change attacksOriented _ _ _ q (0, 0) at ha <;>
    simp [pawnTrace, MoveTrace.single, MoveTrace.after, pawnMove, pawnState,
      applyMove, Board.setGrid, Board.addToHand, Board.removeFromHand, enemyKing, pawnDst] at hp <;>
    split_ifs at hp <;> simp_all [MoveTrace.before, pawnTrace,
      MoveTrace.single, pawnState, Player.opponent] <;>
    subst piece <;>
    simp_all [attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
      Dir.forPlayer, Dir.flip, Pos.dirTo, pawnMove, pawnDst, enemyKing]

-- A board move (including promotion) or a drop checks the opposing actual king
-- and leaves the mover safe, for either initial turn. Placement is derived.
example (turn : Player) (drop promote : Bool) :
    let tr := pawnTrace turn drop promote
    let kp := tr.kingPositionsFrom (pawnKings turn)
    tr.FollowsTransitions ∧ tr.KingsWellPlaced kp ∧
      tr.EveryMoveChecksOpponent kp ∧ tr.EveryMoveLeavesOwnKingSafe kp := by
  have ht := MoveTrace.single_followsTransitions (pawnState turn drop) (pawnMove turn drop promote)
  exact ⟨ht, (pawnTrace turn drop promote).kingsWellPlaced_kingPositionsFrom _ ht
    (pawn_avoidsKings turn drop promote) (pawn_nonKingDrops turn drop promote)
    (pawn_initial_placed turn drop), pawn_checks turn drop promote, pawn_safe turn drop promote⟩

private def kingState (turn : Player) (escape : Bool) : BoardState :=
  { board :=
      { grid := fun q => if q = (if escape then (4, 4) else (5, 4)) then some ⟨turn, .king⟩
          else if q = (0, 0) then some ⟨turn.opponent, .king⟩
          else if q = pawnDst turn then some ⟨turn.opponent, .pawn⟩ else none
        hand := fun _ => ∅ }
    turn := turn }

private def kingMove (escape : Bool) : Move :=
  .boardMove (if escape then (4, 4) else (5, 4)) (if escape then (5, 4) else (4, 4)) false

private def kingKings (turn : Player) (escape : Bool) (owner : Player) : Pos :=
  if owner = turn then (if escape then (4, 4) else (5, 4)) else (0, 0)

private theorem king_placed (turn : Player) (escape : Bool) :
    let tr := MoveTrace.single (kingState turn escape) (kingMove escape)
    tr.KingsWellPlaced (tr.kingPositionsFrom (kingKings turn escape)) := by
  apply MoveTrace.kingsWellPlaced_kingPositionsFrom
  · exact MoveTrace.single_followsTransitions _ _
  · intro i
    change Fin 1 at i
    have hi := Fin.eq_zero i
    subst i
    cases turn <;> cases escape <;> intro owner <;> cases owner <;> decide
  · intro i pt dst hm
    cases escape <;> simp [MoveTrace.single, kingMove] at hm
  · intro owner q
    cases turn <;> cases owner <;> cases escape <;>
      by_cases h0 : q = (0, 0) <;> by_cases h4 : q = (4, 4) <;>
      by_cases h5 : q = (5, 4) <;> by_cases h45 : q = (4, 5) <;> by_cases h43 : q = (4, 3) <;>
      simp_all [MoveTrace.single, kingState, kingKings, pawnDst, Player.opponent]

private theorem king_not_check (turn : Player) (escape : Bool) :
    let tr := MoveTrace.single (kingState turn escape) (kingMove escape)
    ¬ tr.EveryMoveChecksOpponent (tr.kingPositionsFrom (kingKings turn escape)) := by
  dsimp only
  intro h
  obtain ⟨q, piece, hp, ho, ha⟩ := h (0 : Fin 1)
  cases turn <;> cases escape <;>
    change attacksOriented _ _ _ q (0, 0) at ha <;>
    simp [MoveTrace.single, MoveTrace.after, kingMove, kingState,
      applyMove, Board.setGrid, Board.addToHand, pawnDst] at hp <;>
    split_ifs at hp <;> simp_all [MoveTrace.before,
      MoveTrace.single, kingState, Player.opponent] <;>
    subst piece <;>
    simp_all [attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
      Dir.forPlayer, Dir.flip, Pos.dirTo]

-- Moving the king out of the pawn's attack makes the new position safe even
-- though the old square is still attacked. Using the before-position is wrong.
example (turn : Player) :
    let tr := MoveTrace.single (kingState turn true) (kingMove true)
    tr.KingsWellPlaced (tr.kingPositionsFrom (kingKings turn true)) ∧
    ¬ tr.EveryMoveChecksOpponent (tr.kingPositionsFrom (kingKings turn true)) ∧
    tr.EveryMoveLeavesOwnKingSafe (tr.kingPositionsFrom (kingKings turn true)) ∧
    inCheckOriented (tr.after (0 : Fin 1)).board turn (4, 4) := by
  refine ⟨king_placed turn true, king_not_check turn true, ?_, ?_⟩
  · intro i
    change Fin 1 at i
    have hi := Fin.eq_zero i
    subst i
    rintro ⟨q, piece, hp, ho, ha⟩
    cases turn <;>
      change attacksOriented _ _ _ q (5, 4) at ha <;>
      simp [MoveTrace.single, MoveTrace.after, kingMove, kingState,
        applyMove, Board.setGrid, Board.addToHand, pawnDst] at hp <;>
      split_ifs at hp <;> simp_all [MoveTrace.before,
        MoveTrace.single, kingState, Player.opponent] <;>
      subst piece <;>
      simp_all [attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
        Dir.forPlayer, Dir.flip, Pos.dirTo, kingMove, pawnDst]
  · refine ⟨pawnDst turn, ⟨turn.opponent, .pawn⟩, ?_, rfl, ?_⟩
    · cases turn <;> rfl
    · cases turn <;> left <;> decide

-- The reverse move places the king in check: self-safety is an extra condition.
example (turn : Player) :
    let tr := MoveTrace.single (kingState turn false) (kingMove false)
    tr.KingsWellPlaced (tr.kingPositionsFrom (kingKings turn false)) ∧
    ¬ tr.EveryMoveLeavesOwnKingSafe (tr.kingPositionsFrom (kingKings turn false)) := by
  refine ⟨king_placed turn false, ?_⟩
  intro h
  apply h (0 : Fin 1)
  refine ⟨pawnDst turn, ⟨turn.opponent, .pawn⟩, ?_, rfl, ?_⟩
  · cases turn <;> rfl
  · cases turn <;> left <;> decide

-- Both move conditions are vacuous at length zero. They do not assert initial
-- placement or safety, in contrast to the separate KingsWellPlaced condition.
example (bs : BoardState) (kp : Fin 1 → Player → Pos) :
    let tr : MoveTrace := { len := 0, states := fun _ => bs, moves := Fin.elim0 }
    tr.EveryMoveChecksOpponent kp ∧ tr.EveryMoveLeavesOwnKingSafe kp :=
  ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

end MPC
