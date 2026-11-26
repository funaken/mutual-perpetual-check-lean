import MPC.Legacy.CheckCompatibility
import MPC.Glare.GlaringMove
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.GlaringMove

Lemma 2.5 and its consequences on concrete boards for both owners: a glaring
rook that captures its blocker gives a direct check and lands glaring; a dragon
leaving the rook's file keeps the rook blocked by a movable piece; and the
attack, before-non-check, and ownership premises cannot be dropped. Board
updates here make no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Glaring move verification must not import GameSeq"

namespace MPC
namespace GlaringMoveTests

private def col (p : Player) (j : Fin 9) : Pos := (0, if p = .sente then j else 4 - j)
private def side (p : Player) (j : Fin 9) : Pos := (1, if p = .sente then j else 4 - j)

-- The mover's rook at file square 0, `mid` and `block` between it and the enemy
-- king at square 4, and the mover's king far away.
private def lineBoard (p : Player) (mid block : Option Piece) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = col p 0 then some ⟨p, .rook⟩
        else if q = col p 2 then mid
        else if q = col p 3 then block
        else if q = col p 4 then some ⟨p.opponent, .king⟩
        else if q = (8, 8) then some ⟨p, .king⟩ else none
      hand := fun _ => ∅ }
    turn := p }

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

private theorem tail_clear (b : Board) (p : Player) :
    pathClear b (col p 2) (col p 4) ↔ b.grid (col p 3) = none := by
  have hc := pathClear_iff_of_exact_steps b (col p 2) (col p 4)
    (0, if p = .sente then 1 else -1) 2 (by cases p <;> decide) (by decide)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
  constructor
  · intro h
    have h1 := hc.mp h 1 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    cases p <;> exact h1
  · intro h1
    apply hc.mpr
    intro j hj hjn hob
    interval_cases j
    cases p <;> exact h1

-- A rook or dragon two squares behind the target along the file attacks it
-- exactly when the square in between is empty.
private theorem tail_attack (b : Board) (p : Player) (pt : PieceType)
    (hpt : pt = .rook ∨ pt = .dragon) (h : b.grid (col p 3) = none) :
    attacksOriented b p pt (col p 2) (col p 4) := by
  refine Or.inr ⟨(0, if p = .sente then 1 else -1), ?_, ?_, 2, by decide, ?_, ?_,
    (tail_clear b p).mpr h⟩ <;> rcases hpt with rfl | rfl <;> cases p <;> decide

private theorem move_grid (bs : BoardState) (src dst : Pos) (pc : Piece)
    (hs : bs.board.grid src = some pc) (hne : src ≠ dst) (q : Pos) :
    (applyMove bs (.boardMove src dst false)).board.grid q =
      if q = dst then some pc else if q = src then none else bs.board.grid q := by
  by_cases hd : q = dst
  · subst q
    rw [ite_eq_left rfl, applyMove_boardMove_grid_dst, hs]
    rfl
  · by_cases hq : q = src
    · subst q
      rw [ite_eq_right hd, ite_eq_left rfl]
      exact applyMove_boardMove_grid_src bs src dst false hne
    · rw [ite_eq_right hd, ite_eq_right hq]
      exact applyMove_boardMove_grid_other bs src dst false q hq hd

-- The rook behind a vacated square becomes an unblocked checker.
private theorem rook_unblocked (p : Player) (bs : BoardState) (src dst : Pos)
    (hrook : bs.board.grid (col p 0) = some ⟨p, .rook⟩)
    (hs0 : col p 0 ≠ src) (hd0 : col p 0 ≠ dst)
    (hsm : src.toInt ∈ slidePath (col p 0) (col p 4))
    (hdm : dst.toInt ∉ slidePath (col p 0) (col p 4))
    (hblocked : ¬ pathClear bs.board (col p 0) (col p 4))
    (hclear : pathClear (applyMove bs (.boardMove src dst false)).board (col p 0) (col p 4)) :
    hasUnblockedCheckerOriented bs.board (applyMove bs (.boardMove src dst false)).board
      (.boardMove src dst false) p.opponent (col p 4) :=
  ⟨col p 0, ⟨p, .rook⟩, hs0, hd0, hrook,
    (applyMove_boardMove_grid_other bs src dst false _ hs0 hd0).trans hrook,
    by cases p <;> rfl, (col_attack _ p).mpr hclear, hsm, hdm, hblocked, hclear⟩

/-! ## The board containing the opponent's gold in front of its king -/

private def goldStart (p : Player) : BoardState := lineBoard p none (some ⟨p.opponent, .gold⟩)

-- The rook is blocked by the gold and the mover's king is far away.
private theorem gold_safe (p : Player) :
    ¬ inCheckOriented (goldStart p).board p.opponent (col p 4) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [goldStart, lineBoard] at hp
  split_ifs at hp <;> cases hp
  · subst pos
    have h := ((col_clear _ p).mp ((col_attack _ p).mp ha)).2.2
    revert h
    cases p <;> decide
  · cases p <;> cases ho
  · cases p <;> cases ho
  · subst pos
    rcases ha with hs | ⟨_, hsd, _⟩
    · revert hs
      cases p <;> decide
    · simp [PieceType.slideDirs] at hsd

/-! ## Trace: a glaring rook captures its blocker -/

private def capture (p : Player) : Move := .boardMove (col p 0) (col p 3) false
private def positions (p : Player) : Player → Pos := fun o => if o = p then (8, 8) else col p 4

private theorem capture_grid (p : Player) (q : Pos) :
    (applyMove (goldStart p) (capture p)).board.grid q =
      if q = col p 3 then some ⟨p, .rook⟩
      else if q = col p 0 then none else (goldStart p).board.grid q :=
  move_grid (goldStart p) (col p 0) (col p 3) ⟨p, .rook⟩ (by cases p <;> rfl)
    (by cases p <;> decide) q

private theorem placed (p : Player) : KingsWellPlaced (goldStart p).board (positions p) := by
  intro o q
  cases p <;> cases o <;> by_cases h0 : q = (0, 0) <;> by_cases h1 : q = (0, 1) <;>
    by_cases h3 : q = (0, 3) <;> by_cases h4 : q = (0, 4) <;> by_cases h8 : q = (8, 8) <;>
    simp_all [goldStart, lineBoard, positions, col, Player.opponent]

-- After the capture only the enemy king remains on the opponent's side.
private theorem capture_safe (p : Player) :
    ¬ inCheckOriented (applyMove (goldStart p) (capture p)).board p (8, 8) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  rw [capture_grid] at hp
  dsimp only [goldStart, lineBoard] at hp
  split_ifs at hp <;> cases hp
  · cases p <;> cases ho
  · subst pos
    rcases ha with hs | ⟨_, hsd, _⟩
    · revert hs
      cases p <;> decide
    · simp [PieceType.slideDirs] at hsd
  · cases p <;> cases ho

private theorem capture_check (p : Player) :
    inCheckOriented (applyMove (goldStart p) (capture p)).board p.opponent (col p 4) := by
  refine ⟨col p 3, ⟨p, .rook⟩, by rw [capture_grid, ite_eq_left rfl], by cases p <;> rfl, ?_⟩
  have hc := pathClear_iff_of_exact_steps (applyMove (goldStart p) (capture p)).board
    (col p 3) (col p 4) (0, if p = .sente then 1 else -1) 1 (by cases p <;> decide)
    (by decide) (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
  refine Or.inr ⟨(0, if p = .sente then 1 else -1), ?_, ?_, 1, le_refl 1, ?_, ?_,
    hc.mpr fun j hj hjn => absurd hjn (by omega)⟩ <;> cases p <;> decide

private def premisesOf (p : Player) : Prop :=
  let tr := MoveTrace.single (goldStart p) (capture p)
  let kp := tr.kingPositionsFrom (positions p)
  tr.FollowsTransitions ∧ tr.BoardMoveSourcesOwned ∧ tr.KingsWellPlaced kp ∧
    tr.EveryMoveLeavesOwnKingSafe kp ∧ tr.InitialOpponentKingSafe kp ∧
    tr.EveryMoveChecksOpponent kp

private theorem premises (p : Player) : premisesOf p := by
  dsimp only [premisesOf]
  let tr := MoveTrace.single (goldStart p) (capture p)
  have ht := MoveTrace.single_followsTransitions (goldStart p) (capture p)
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_⟩
  · intro i src dst pr hm; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (col p 0) (col p 3) false = .boardMove src dst pr at hm
    cases hm
    exact ⟨⟨p, .rook⟩, by cases p <;> rfl, rfl⟩
  · apply MoveTrace.kingsWellPlaced_kingPositionsFrom tr (positions p) ht
    · intro i o; have hi := Fin.eq_zero i; subst i
      change (goldStart p).board.grid (col p 3) ≠ some ⟨o, .king⟩
      cases p <;> cases o <;> decide
    · intro i pt dst hm; change Move.boardMove _ _ _ = .dropMove pt dst at hm; cases hm
    · exact placed p
  · intro i; have hi := Fin.eq_zero i; subst i
    cases p
    exacts [capture_safe .sente, capture_safe .gote]
  · cases p
    exacts [gold_safe .sente, gold_safe .gote]
  · intro i; have hi := Fin.eq_zero i; subst i
    cases p
    exacts [capture_check .sente, capture_check .gote]

-- Both owners. Both kings are immovable, the captured gold's square is not. The rook is blocked by the gold but glares, since the gold is
-- removed from the stripped board. Lemma 2.5 excludes an unblocked checker, so
-- the move is a direct check and the rook glares from its destination (Lemma 2.6).
example (p : Player) :
    let tr := MoveTrace.single (goldStart p) (capture p)
    let kp := tr.kingPositionsFrom (positions p)
    tr.ImmovableAt (col p 4) ∧ tr.ImmovableAt (8, 8) ∧ ¬ tr.ImmovableAt (col p 3) ∧
    ¬ attacksOriented (tr.states 0).board p .rook (col p 0) (col p 4) ∧
    tr.GlaresAtEnemyKing kp 0 (col p 0) ∧
    ¬ hasUnblockedCheckerOriented (tr.before (0 : Fin 1)).board (tr.after (0 : Fin 1)).board
      (tr.moves (0 : Fin 1)) p.opponent (kp 1 p.opponent) ∧
    hasDestinationCheckerOriented (tr.after (0 : Fin 1)).board (tr.moves (0 : Fin 1))
      p.opponent (kp 1 p.opponent) ∧
    tr.GlaresAtEnemyKing kp 1 (col p 3) := by
  dsimp only
  obtain ⟨ht, hs, hk, hsafe, h0, hc⟩ := premises p
  have hg : (MoveTrace.single (goldStart p) (capture p)).GlaresAtEnemyKing
      ((MoveTrace.single (goldStart p) (capture p)).kingPositionsFrom (positions p)) 0
      (col p 0) := by
    refine ⟨⟨p, .rook⟩, by cases p <;> rfl, ?_⟩
    cases p
    · exact (col_attack _ .sente).mpr ((col_clear _ .sente).mpr ⟨by decide, by decide, by decide⟩)
    · exact (col_attack _ .gote).mpr ((col_clear _ .gote).mpr ⟨by decide, by decide, by decide⟩)
  refine ⟨by cases p <;> decide, by cases p <;> decide, by cases p <;> decide, ?_, hg,
    (MoveTrace.single (goldStart p) (capture p)).not_unblockedChecker_of_source_glares
      _ ht hs hk hsafe h0 (0 : Fin 1) (col p 0) (col p 3) false rfl hg,
    (MoveTrace.single (goldStart p) (capture p)).destinationChecker_of_source_glares
      _ ht hs hk hsafe h0 hc (0 : Fin 1) (col p 0) (col p 3) false rfl hg,
    (MoveTrace.single (goldStart p) (capture p)).destination_glares_of_source_glares
      _ ht hs hk hsafe h0 hc (0 : Fin 1) (col p 0) (col p 3) false rfl hg⟩
  intro ha
  have h := ((col_clear _ p).mp ((col_attack _ p).mp ha)).2.2
  revert h
  cases p <;> decide

/-! ## Lemma 2.5 on boards: a movable blocker keeps blocking -/

private def dragonStart (p : Player) : BoardState :=
  lineBoard p (some ⟨p, .dragon⟩) (some ⟨p.opponent, .gold⟩)
private def dragonOff (p : Player) : Move := .boardMove (col p 2) (side p 3) false

-- The rook is blocked by the dragon, the dragon by the gold.
private theorem dragon_safe (p : Player) :
    ¬ inCheckOriented (dragonStart p).board p.opponent (col p 4) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [dragonStart, lineBoard] at hp
  split_ifs at hp <;> cases hp
  · subst pos
    have h := ((col_clear _ p).mp ((col_attack _ p).mp ha)).2.1
    revert h
    cases p <;> decide
  · subst pos
    rcases ha with hs | ⟨_, _, _, _, _, _, _, hc⟩
    · revert hs
      cases p <;> decide
    · have h := (tail_clear _ p).mp hc
      revert h
      cases p <;> decide
  · cases p <;> cases ho
  · cases p <;> cases ho
  · subst pos
    rcases ha with hs | ⟨_, hsd, _⟩
    · revert hs
      cases p <;> decide
    · simp [PieceType.slideDirs] at hsd

-- Both owners. The rook's path passes through the dragon's source and avoids its
-- destination, yet with the gold removed the dragon reaches the king, so the move
-- has no unblocked checker: the gold, still in place, keeps the rook blocked.
example (p : Player) :
    (col p 2).toInt ∈ slidePath (col p 0) (col p 4) ∧
    (side p 3).toInt ∉ slidePath (col p 0) (col p 4) ∧
    ¬ hasUnblockedCheckerOriented (dragonStart p).board
      (applyMove (dragonStart p) (dragonOff p)).board (dragonOff p) p.opponent (col p 4) := by
  refine ⟨by cases p <;> decide, by cases p <;> decide, ?_⟩
  exact applyMove_boardMove_not_unblockedChecker_of_attacks (dragonStart p) (col p 2) (side p 3)
    (col p 4) false p.opponent (lineBoard p (some ⟨p, .dragon⟩) none).board ⟨p, .dragon⟩
    (by cases p <;> rfl) (by cases p <;> rfl)
    (tail_attack _ p .dragon (Or.inr rfl) (by cases p <;> rfl)) (dragon_safe p)

/-! ## The premises are needed -/

private def pieceStart (p : Player) (pt : PieceType) : BoardState :=
  lineBoard p (some ⟨p, pt⟩) none
private def pieceOff (p : Player) : Move := .boardMove (col p 2) (side p 2) false

-- Moving the piece in front of the rook off the file unblocks the rook.
private theorem pieceOff_unblocked (p : Player) (pt : PieceType) :
    hasUnblockedCheckerOriented (pieceStart p pt).board
      (applyMove (pieceStart p pt) (pieceOff p)).board (pieceOff p) p.opponent (col p 4) := by
  have hg := move_grid (pieceStart p pt) (col p 2) (side p 2) ⟨p, pt⟩ (by cases p <;> rfl)
    (by cases p <;> decide)
  refine rook_unblocked p _ _ _ (by cases p <;> rfl) (by cases p <;> decide)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide) ?_ ?_
  · intro h
    have h2 := ((col_clear _ p).mp h).2.1
    revert h2
    cases p <;> simp [pieceStart, lineBoard, col]
  · refine (col_clear _ p).mpr ⟨?_, ?_, ?_⟩ <;> rw [hg] <;> cases p <;> rfl

-- Attack premise: a king two squares from the target reaches it on no board.
example (p : Player) :
    (∀ S : Board, ¬ attacksOriented S p .king (col p 2) (col p 4)) ∧
    ¬ inCheckOriented (pieceStart p .king).board p.opponent (col p 4) ∧
    hasUnblockedCheckerOriented (pieceStart p .king).board
      (applyMove (pieceStart p .king) (pieceOff p)).board (pieceOff p) p.opponent (col p 4) := by
  have hking : ∀ S : Board, ¬ attacksOriented S p .king (col p 2) (col p 4) := by
    rintro S (hs | ⟨_, hsd, _⟩)
    · revert hs
      cases p <;> decide
    · simp [PieceType.slideDirs] at hsd
  refine ⟨hking, ?_, pieceOff_unblocked p .king⟩
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [pieceStart, lineBoard] at hp
  split_ifs at hp <;> cases hp
  · subst pos
    have h := ((col_clear _ p).mp ((col_attack _ p).mp ha)).2.1
    revert h
    cases p <;> decide
  · subst pos
    exact hking _ ha
  · cases p <;> cases ho
  · subst pos
    rcases ha with hs | ⟨_, hsd, _⟩
    · revert hs
      cases p <;> decide
    · simp [PieceType.slideDirs] at hsd

-- Before-non-check premise: a rook already giving check reaches the target on
-- the actual board, and moving it off the file unblocks the rook behind it.
example (p : Player) :
    attacksOriented (pieceStart p .rook).board p .rook (col p 2) (col p 4) ∧
    inCheckOriented (pieceStart p .rook).board p.opponent (col p 4) ∧
    hasUnblockedCheckerOriented (pieceStart p .rook).board
      (applyMove (pieceStart p .rook) (pieceOff p)).board (pieceOff p) p.opponent (col p 4) := by
  have ha := tail_attack (pieceStart p .rook).board p .rook (Or.inl rfl) (by cases p <;> rfl)
  exact ⟨ha, ⟨col p 2, ⟨p, .rook⟩, by cases p <;> rfl, by cases p <;> rfl, ha⟩,
    pieceOff_unblocked p .rook⟩

private def goldOff (p : Player) : Move := .boardMove (col p 3) (side p 3) false

-- Ownership premise: the opponent's gold reaches its own king's square on every
-- board and the king starts unchecked, yet moving the gold unblocks the rook.
example (p : Player) :
    (∀ S : Board, attacksOriented S p.opponent .gold (col p 3) (col p 4)) ∧
    ¬ inCheckOriented (goldStart p).board p.opponent (col p 4) ∧
    hasUnblockedCheckerOriented (goldStart p).board
      (applyMove (goldStart p) (goldOff p)).board (goldOff p) p.opponent (col p 4) := by
  refine ⟨fun S => Or.inl (by cases p <;> decide), gold_safe p, ?_⟩
  have hg := move_grid (goldStart p) (col p 3) (side p 3) ⟨p.opponent, .gold⟩
    (by cases p <;> rfl) (by cases p <;> decide)
  refine rook_unblocked p _ _ _ (by cases p <;> rfl) (by cases p <;> decide)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide) ?_ ?_
  · intro h
    have h3 := ((col_clear _ p).mp h).2.2
    revert h3
    cases p <;> decide
  · refine (col_clear _ p).mpr ⟨?_, ?_, ?_⟩ <;> rw [hg] <;> cases p <;> rfl

end GlaringMoveTests
end MPC
