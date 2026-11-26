import MPC.Trace.CheckOrigin
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.CheckOrigin

Combined destination/unblocked classification for both move kinds, double check,
generated king positions, and the necessity of before-non-check and source
presence. Board updates here make no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Check origin verification must not import GameSeq"

namespace MPC
namespace CheckOriginTests

private def point (owner : Player) (diagonal : Bool) (j : Fin 9) : Pos :=
  (if diagonal then j else 0, if owner = .sente then j else 4 - j)
private def direction (owner : Player) (diagonal : Bool) : Dir :=
  (if diagonal then 1 else 0, if owner = .sente then 1 else -1)
private def kind (diagonal : Bool) : PieceType := if diagonal then .bishop else .rook
private def initial (owner : Player) (diagonal : Bool) : BoardState :=
  { board :=
    { grid := fun p =>
        if p = point owner diagonal 0 then some ⟨owner, kind diagonal⟩
        else if p = point owner diagonal 2 then some ⟨owner, .gold⟩
        else if p = (8, 8) then some ⟨owner, .king⟩
        else if p = point owner diagonal 4 then some ⟨owner.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := owner }
private def move (owner : Player) (diagonal promote : Bool) : Move :=
  .boardMove (point owner diagonal 2) (5, 4) promote

private theorem clearance (b : Board) (owner : Player) (diagonal : Bool) :
    pathClear b (point owner diagonal 0) (point owner diagonal 4) ↔
      b.grid (point owner diagonal 1) = none ∧ b.grid (point owner diagonal 2) = none ∧
      b.grid (point owner diagonal 3) = none := by
  have hc := pathClear_iff_of_exact_steps b (point owner diagonal 0) (point owner diagonal 4)
    (direction owner diagonal) 4 (by cases owner <;> cases diagonal <;> decide)
    (by decide) (by cases owner <;> cases diagonal <;> decide)
    (by cases owner <;> cases diagonal <;> decide) (by cases owner <;> cases diagonal <;> decide)
  constructor
  · intro h
    have h1 := hc.mp h 1 (by decide) (by decide) (by cases owner <;> cases diagonal <;> unfold onBoard <;> decide)
    have h2 := hc.mp h 2 (by decide) (by decide) (by cases owner <;> cases diagonal <;> unfold onBoard <;> decide)
    have h3 := hc.mp h 3 (by decide) (by decide) (by cases owner <;> cases diagonal <;> unfold onBoard <;> decide)
    cases owner <;> cases diagonal <;> exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    apply hc.mpr
    intro j hj hjn hob
    interval_cases j <;> cases owner <;> cases diagonal <;> assumption

private theorem ray_attack (b : Board) (owner : Player) (diagonal : Bool) :
    attacksOriented b owner (kind diagonal) (point owner diagonal 0) (point owner diagonal 4) ↔
      pathClear b (point owner diagonal 0) (point owner diagonal 4) := by
  constructor
  · rintro (hs | ⟨_, _, _, _, _, _, _, hc⟩)
    · cases diagonal <;> simp [kind, PieceType.stepDirs] at hs
    · exact hc
  · intro hc
    refine Or.inr ⟨direction owner diagonal, ?_, ?_, 4, by decide, ?_, ?_, hc⟩ <;>
      cases owner <;> cases diagonal <;> decide

private theorem ray_new (owner : Player) (diagonal promote : Bool) :
    ¬ attacksOriented (initial owner diagonal).board owner (kind diagonal)
      (point owner diagonal 0) (point owner diagonal 4) ∧
    attacksOriented (applyMove (initial owner diagonal) (move owner diagonal promote)).board
      owner (kind diagonal) (point owner diagonal 0) (point owner diagonal 4) := by
  constructor
  · rw [ray_attack, clearance]
    intro h
    have he := h.2.1
    cases owner <;> cases diagonal <;> simp [initial, point] at he
  · rw [ray_attack, clearance]
    cases owner <;> cases diagonal <;> cases promote <;> exact ⟨rfl, rfl, rfl⟩

private theorem other_checker (owner : Player) (diagonal promote : Bool) :
    hasOtherCheckerOriented (applyMove (initial owner diagonal) (move owner diagonal promote)).board
      (move owner diagonal promote) owner.opponent (point owner diagonal 4) := by
  refine ⟨point owner diagonal 0, ?_, ⟨owner, kind diagonal⟩, ?_, ?_,
    (ray_new owner diagonal promote).2⟩
  · change point owner diagonal 0 ≠ (5, 4)
    cases owner <;> cases diagonal <;> decide
  · cases owner <;> cases diagonal <;> rfl
  · cases owner <;> rfl

private theorem before_safe (owner : Player) (diagonal : Bool) :
    ¬ inCheckOriented (initial owner diagonal).board owner.opponent (point owner diagonal 4) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [initial] at hp
  split_ifs at hp with h0 h2 hk h4
  · cases hp; subst pos; exact (ray_new owner diagonal false).1 ha
  · cases hp; subst pos
    cases owner <;> cases diagonal <;>
      simp [attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
        point, Pos.dirTo, Dir.forPlayer, Dir.flip] at ha
  · cases hp; subst pos
    cases owner <;> cases diagonal <;>
      simp [attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
        point, Pos.dirTo, Dir.forPlayer, Dir.flip] at ha
  · cases hp; cases owner <;> cases ho

private theorem no_destination_checker (owner : Player) (promote : Bool) :
    ¬ hasDestinationCheckerOriented (applyMove (initial owner false) (move owner false promote)).board
      (move owner false promote) owner.opponent (point owner false 4) := by
  rintro ⟨piece, hp, _, ha⟩
  change (applyMove (initial owner false)
    (.boardMove (point owner false 2) (5, 4) promote)).board.grid (5, 4) = some piece at hp
  rw [applyMove_boardMove_grid_dst] at hp
  have hs : (initial owner false).board.grid (point owner false 2) = some ⟨owner, .gold⟩ := by
    cases owner <;> rfl
  rw [hs] at hp
  cases hp
  cases owner <;> cases promote <;>
    simp [attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
      PieceType.promote, move, Move.destination, point, Pos.dirTo, Dir.forPlayer, Dir.flip] at ha

private def positions (owner : Player) : Player → Pos :=
  fun p => if p = owner then (8, 8) else point owner false 4

private theorem placed (owner : Player) :
    KingsWellPlaced (initial owner false).board (positions owner) := by
  intro p q
  cases owner <;> cases p <;> by_cases h0 : q = (0, 0) <;>
    by_cases h4 : q = (0, 4) <;> by_cases h2 : q = (0, 2) <;> by_cases hk : q = (8, 8) <;>
    simp_all [initial, positions, point, kind, Player.opponent]

-- Drops never have an unblocked checker, so the classification specializes to direct checks.
example (bs : BoardState) (pt : PieceType) (dst target : Pos) (kingOwner : Player)
    (hb : ¬ inCheckOriented bs.board kingOwner target) :
    inCheckOriented (applyMove bs (.dropMove pt dst)).board kingOwner target ↔
      hasDestinationCheckerOriented (applyMove bs (.dropMove pt dst)).board
        (.dropMove pt dst) kingOwner target := by
  have h := applyMove_inCheck_iff_destination_or_unblocked bs (.dropMove pt dst)
    kingOwner target trivial hb
  simpa only [hasUnblockedCheckerOriented, or_false] using h

-- Both owners and promotion flags: generated positions give actual kings, and
-- the trace-wide classification selects the unblocked rook, not the destination.
example (owner : Player) (promote : Bool) :
    let tr := MoveTrace.single (initial owner false) (move owner false promote)
    let kp := tr.kingPositionsFrom (positions owner)
    tr.KingsWellPlaced kp ∧ tr.EveryMoveChecksOpponent kp ∧
    ¬ hasDestinationCheckerOriented (tr.after (0 : Fin 1)).board (tr.moves (0 : Fin 1))
      owner.opponent (kp 1 owner.opponent) ∧
    hasUnblockedCheckerOriented (tr.before (0 : Fin 1)).board (tr.after (0 : Fin 1)).board
      (tr.moves (0 : Fin 1)) owner.opponent (kp 1 owner.opponent) := by
  dsimp only
  let tr := MoveTrace.single (initial owner false) (move owner false promote)
  have ht := MoveTrace.single_followsTransitions (initial owner false) (move owner false promote)
  have hp : tr.KingsWellPlaced (tr.kingPositionsFrom (positions owner)) := by
    apply MoveTrace.kingsWellPlaced_kingPositionsFrom tr (positions owner) ht
    · intro i p; have hi := Fin.eq_zero i; subst i
      change (initial owner false).board.grid (5, 4) ≠ some ⟨p, .king⟩
      cases owner <;> cases p <;> decide
    · intro i pt dst hm; change Move.boardMove _ _ _ = .dropMove pt dst at hm; cases hm
    · exact placed owner
  have hs : tr.BoardMoveSourcesOwned := by
    intro i src dst pr hm; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (point owner false 2) (5, 4) promote = .boardMove src dst pr at hm
    cases hm
    exact ⟨⟨owner, .gold⟩, by cases owner <;> rfl, rfl⟩
  have hu := (applyMove_otherChecker_iff_unblockedChecker (initial owner false)
    (move owner false promote) owner.opponent (point owner false 4)
    ⟨⟨owner, .gold⟩, by cases owner <;> rfl⟩ (before_safe owner false)).mp
    (other_checker owner false promote)
  have he := tr.everyMoveChecksOpponent_iff_destination_or_unblocked
    (tr.kingPositionsFrom (positions owner)) ht hs
    (fun i => by have hi := Fin.eq_zero i; subst i; cases owner <;> rfl)
    (fun i => by have hi := Fin.eq_zero i; subst i; cases owner <;> exact before_safe _ false)
  have hc : tr.EveryMoveChecksOpponent (tr.kingPositionsFrom (positions owner)) :=
    he.mpr fun i => by have hi := Fin.eq_zero i; subst i; cases owner <;> exact Or.inr hu
  cases owner <;> exact ⟨hp, hc, no_destination_checker _ promote, hu⟩

-- Sente's diagonal fixture: the moved gold checks from its destination while
-- the bishop is unblocked, so both disjuncts hold together (double check).
example (promote : Bool) :
    let bs := initial .sente true
    let m := move .sente true promote
    hasDestinationCheckerOriented (applyMove bs m).board m .gote (4, 4) ∧
    hasUnblockedCheckerOriented bs.board (applyMove bs m).board m .gote (4, 4) ∧
    inCheckOriented (applyMove bs m).board .gote (4, 4) := by
  have hd : hasDestinationCheckerOriented
      (applyMove (initial .sente true) (move .sente true promote)).board
      (move .sente true promote) .gote (4, 4) := by
    refine ⟨⟨.sente, .gold⟩, ?_, rfl, ?_⟩
    · cases promote <;> rfl
    · left
      change Pos.dirTo (5, 4) (4, 4) ∈ PieceType.gold.stepDirs.map (Dir.forPlayer · .sente)
      decide
  have hu := (applyMove_otherChecker_iff_unblockedChecker (initial .sente true)
    (move .sente true promote) .gote (4, 4) ⟨⟨.sente, .gold⟩, rfl⟩ (before_safe .sente true)).mp
    (other_checker .sente true promote)
  exact ⟨hd, hu, (applyMove_inCheck_iff_destination_or_unblocked (initial .sente true)
    (move .sente true promote) .gote (4, 4) ⟨⟨.sente, .gold⟩, rfl⟩
    (before_safe .sente true)).mpr (Or.inl hd)⟩

private def beside (owner : Player) : Pos := (1, if owner = .sente then 4 else 0)

private theorem drop_destination (owner : Player) :
    hasDestinationCheckerOriented
      (applyMove (initial owner false) (.dropMove .gold (beside owner))).board
      (.dropMove .gold (beside owner)) owner.opponent (point owner false 4) := by
  refine ⟨⟨owner, .gold⟩, applyMove_dropMove_grid_dst _ _ _, ?_, ?_⟩
  · cases owner <;> rfl
  · cases owner <;> left <;> decide

-- Both owners: a drop beside the generated king position checks from the
-- destination; the trace-wide classification has no unblocked alternative.
example (owner : Player) :
    let tr := MoveTrace.single (initial owner false) (.dropMove .gold (beside owner))
    let kp := tr.kingPositionsFrom (positions owner)
    tr.KingsWellPlaced kp ∧ tr.EveryMoveChecksOpponent kp ∧
    hasDestinationCheckerOriented (tr.after (0 : Fin 1)).board (tr.moves (0 : Fin 1))
      owner.opponent (kp 1 owner.opponent) ∧
    ¬ hasUnblockedCheckerOriented (tr.before (0 : Fin 1)).board (tr.after (0 : Fin 1)).board
      (tr.moves (0 : Fin 1)) owner.opponent (kp 1 owner.opponent) := by
  dsimp only
  let tr := MoveTrace.single (initial owner false) (.dropMove .gold (beside owner))
  have ht := MoveTrace.single_followsTransitions (initial owner false) (.dropMove .gold (beside owner))
  have hp : tr.KingsWellPlaced (tr.kingPositionsFrom (positions owner)) := by
    apply MoveTrace.kingsWellPlaced_kingPositionsFrom tr (positions owner) ht
    · intro i p; have hi := Fin.eq_zero i; subst i
      change (initial owner false).board.grid (beside owner) ≠ some ⟨p, .king⟩
      cases owner <;> cases p <;> decide
    · intro i pt dst hm
      change Move.dropMove .gold (beside owner) = .dropMove pt dst at hm
      cases hm; decide
    · exact placed owner
  have hs : tr.BoardMoveSourcesOwned := by
    intro i src dst pr hm
    change Move.dropMove .gold (beside owner) = .boardMove src dst pr at hm
    cases hm
  have he := tr.everyMoveChecksOpponent_iff_destination_or_unblocked
    (tr.kingPositionsFrom (positions owner)) ht hs
    (fun i => by have hi := Fin.eq_zero i; subst i; cases owner <;> rfl)
    (fun i => by have hi := Fin.eq_zero i; subst i; cases owner <;> exact before_safe _ false)
  have hc : tr.EveryMoveChecksOpponent (tr.kingPositionsFrom (positions owner)) :=
    he.mpr fun i => by
      have hi := Fin.eq_zero i; subst i; cases owner <;> exact Or.inl (drop_destination _)
  cases owner <;> exact ⟨hp, hc, drop_destination _, fun h => h⟩

private def continuing (owner : Player) : BoardState :=
  { board :=
    { grid := fun p =>
        if p = point owner false 0 then some ⟨owner, .rook⟩
        else if p = (5, 4) then some ⟨owner, .gold⟩
        else if p = point owner false 4 then some ⟨owner.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := owner }

-- A pre-existing rook check continues past an unrelated present-source move. It
-- is an after-board other checker but not unblocked: before-non-check matters.
example (owner : Player) :
    let bs := continuing owner
    let m := Move.boardMove (5, 4) (6, 4) false
    m.SourcePresent bs.board ∧ inCheckOriented bs.board owner.opponent (point owner false 4) ∧
    hasOtherCheckerOriented (applyMove bs m).board m owner.opponent (point owner false 4) ∧
    ¬ hasUnblockedCheckerOriented bs.board (applyMove bs m).board m owner.opponent
      (point owner false 4) := by
  dsimp only
  have hclear : pathClear (continuing owner).board (point owner false 0) (point owner false 4) := by
    rw [clearance]; cases owner <;> exact ⟨rfl, rfl, rfl⟩
  have hbefore : attacksOriented (continuing owner).board owner .rook
      (point owner false 0) (point owner false 4) := (ray_attack _ owner false).mpr hclear
  have hafter : attacksOriented (applyMove (continuing owner) (.boardMove (5, 4) (6, 4) false)).board
      owner .rook (point owner false 0) (point owner false 4) := by
    apply (ray_attack _ owner false).mpr
    rw [clearance]; cases owner <;> exact ⟨rfl, rfl, rfl⟩
  refine ⟨⟨⟨owner, .gold⟩, by cases owner <;> rfl⟩,
    ⟨point owner false 0, ⟨owner, .rook⟩, by cases owner <;> rfl, by cases owner <;> rfl, hbefore⟩,
    ⟨point owner false 0, ?_, ⟨owner, .rook⟩, ?_, by cases owner <;> rfl, hafter⟩, ?_⟩
  · change point owner false 0 ≠ (6, 4)
    cases owner <;> decide
  · cases owner <;> rfl
  · rintro ⟨pos, piece, hs, _, hb, _, ho, _, _, _, hblk, _⟩
    dsimp only [continuing] at hb
    -- split_ifs discharges the source square using `pos ≠ (5, 4)`.
    split_ifs at hb with h0 h4
    · subst pos; exact hblk hclear
    · cases hb; cases owner <;> cases ho

-- An absent source can erase a blocking destination. Before-non-check holds and
-- a new other checker appears, but it is not unblocked: source presence matters.
example (owner : Player) :
    let bs := initial owner false
    let m := Move.boardMove (7, 7) (point owner false 2) false
    ¬ m.SourcePresent bs.board ∧
    ¬ inCheckOriented bs.board owner.opponent (point owner false 4) ∧
    hasOtherCheckerOriented (applyMove bs m).board m owner.opponent (point owner false 4) ∧
    ¬ hasUnblockedCheckerOriented bs.board (applyMove bs m).board m owner.opponent
      (point owner false 4) := by
  dsimp only
  refine ⟨?_, before_safe owner false, ?_, ?_⟩
  · rintro ⟨piece, hp⟩
    cases owner <;> simp [initial, point] at hp
  · refine ⟨point owner false 0, ?_, ⟨owner, .rook⟩, ?_, ?_, ?_⟩
    · change point owner false 0 ≠ point owner false 2
      cases owner <;> decide
    · cases owner <;> rfl
    · cases owner <;> rfl
    · change attacksOriented _ owner (kind false) _ _
      rw [ray_attack, clearance]
      cases owner <;> exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨pos, piece, _, hd, hb, _, ho, ha, hs, _, _, _⟩
    dsimp only [initial] at hb
    -- split_ifs discharges the destination square using `pos ≠ point owner false 2`.
    split_ifs at hb with h0 hk h4
    · subst pos; revert hs; cases owner <;> decide
    · cases hb; subst pos
      cases owner <;>
        simp [attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
          point, Pos.dirTo, Dir.forPlayer, Dir.flip] at ha
    · cases hb; cases owner <;> cases ho

-- Length-zero traces satisfy every premise and the classification vacuously.
example (s : BoardState) (kp : Fin 1 → Player → Pos) :
    let tr : MoveTrace := ⟨0, fun _ => s, Fin.elim0⟩
    tr.EveryMoveChecksOpponent kp := by
  intro tr
  exact (tr.everyMoveChecksOpponent_iff_destination_or_unblocked kp (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)).mpr (fun i => i.elim0)

end CheckOriginTests
end MPC
