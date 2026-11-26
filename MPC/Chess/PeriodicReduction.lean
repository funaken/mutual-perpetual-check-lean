import MPC.Chess.Material
import MPC.Chess.LegalMove
import Mathlib.Order.Fin.Basic

/-! Periodic local-legal traces cannot capture, promote, or move pawns. The
additional mutual-check condition rules out castling. The only periodic data
used are the board and turn; king positions need not be constant. -/

namespace MPC.Chess.MoveTrace

private theorem value_eq_of_antitone_periodic (tr : MoveTrace) (f : Board → ℤ)
    (hs : ∀ i : Fin tr.len, f (tr.after i).board ≤ f (tr.before i).board)
    (hp : tr.BoardTurnPeriodic) (i j : Fin (tr.len + 1)) :
    f (tr.states i).board = f (tr.states j).board := by
  have ha : Antitone (fun k : Fin (tr.len + 1) => f (tr.states k).board) :=
    Fin.antitone_iff_succ_le.mpr hs
  have he := congrArg f hp.1
  have hi0 := ha (Fin.zero_le i)
  have hli := ha (Fin.le_last i)
  have hj0 := ha (Fin.zero_le j)
  have hlj := ha (Fin.le_last j)
  dsimp only at hi0 hli hj0 hlj he
  omega

private theorem value_eq_of_monotone_periodic (tr : MoveTrace) (f : Board → ℤ)
    (hs : ∀ i : Fin tr.len, f (tr.before i).board ≤ f (tr.after i).board)
    (hp : tr.BoardTurnPeriodic) (i j : Fin (tr.len + 1)) :
    f (tr.states i).board = f (tr.states j).board := by
  have ha : Monotone (fun k : Fin (tr.len + 1) => f (tr.states k).board) :=
    Fin.monotone_iff_le_succ.mpr hs
  have he := congrArg f hp.1
  have hi0 := ha (Fin.zero_le i)
  have hli := ha (Fin.le_last i)
  have hj0 := ha (Fin.zero_le j)
  have hlj := ha (Fin.le_last j)
  dsimp only at hi0 hli hj0 hlj he
  omega

theorem pieceCount_eq_of_periodic (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (i j : Fin (tr.len + 1)) :
    (tr.states i).board.pieceCount = (tr.states j).board.pieceCount := by
  apply value_eq_of_antitone_periodic tr Board.pieceCount _ hp i j
  intro k
  obtain ⟨_, hm, he⟩ := hl k
  rw [he]
  exact pieceCount_applyMove_le _ _ hm.movement

theorem pawnCount_eq_of_periodic (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (i j : Fin (tr.len + 1)) :
    (tr.states i).board.pawnCount = (tr.states j).board.pawnCount := by
  apply value_eq_of_antitone_periodic tr Board.pawnCount _ hp i j
  intro k
  obtain ⟨_, hm, he⟩ := hl k
  rw [he]
  exact pawnCount_applyMove_le _ _ hm.movement

theorem boardMove_destination_empty_of_periodic (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos) (choice : Option Promotion)
    (hm : tr.moves i = .boardMove src dst choice) : (tr.before i).board dst = none := by
  obtain ⟨_, hv, he⟩ := hl i
  rw [hm] at he
  have hv' : PseudoLegal (tr.before i) (.boardMove src dst choice) := by
    simpa only [hm, PseudoLegal] using hv.movement
  obtain ⟨p, hs, _, hne, _⟩ := hv'
  have hb : (tr.after i).board.pieceCount + ((tr.before i).board dst).elim 0 (fun _ => (1 : ℤ)) =
      (tr.before i).board.pieceCount := by
    rw [he]
    exact (tr.before i).board.pieceCount_relocate src dst p choice hs hne
  have hc := tr.pieceCount_eq_of_periodic hl hp i.succ i.castSucc
  change (tr.after i).board.pieceCount = (tr.before i).board.pieceCount at hc
  cases hd : (tr.before i).board dst with
  | none => rfl
  | some q => simp only [hd, Option.elim_some] at hb; omega

theorem not_enPassant_of_periodic (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos) :
    tr.moves i ≠ .enPassant src dst := by
  intro hm
  obtain ⟨_, hv, he⟩ := hl i
  rw [hm] at he
  have hb : (tr.after i).board.pieceCount + 1 = (tr.before i).board.pieceCount := by
    rw [he]
    apply pieceCount_applyMove_enPassant
    simpa only [hm, PseudoLegal] using hv.movement
  have hc := tr.pieceCount_eq_of_periodic hl hp i.succ i.castSucc
  change (tr.after i).board.pieceCount = (tr.before i).board.pieceCount at hc
  omega

theorem not_promotion_of_periodic (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos) (q : Promotion) :
    tr.moves i ≠ .boardMove src dst (some q) := by
  intro hm
  obtain ⟨_, hv, he⟩ := hl i
  rw [hm] at he
  have hb : (tr.after i).board.pawnCount < (tr.before i).board.pawnCount := by
    rw [he]
    apply pawnCount_applyMove_promotion_lt
    simpa only [hm, PseudoLegal] using hv.movement
  have hc := tr.pawnCount_eq_of_periodic hl hp i.succ i.castSucc
  change (tr.after i).board.pawnCount = (tr.before i).board.pawnCount at hc
  omega

private theorem pawnProgress_step (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) :
    (tr.before i).board.pawnProgress ≤ (tr.after i).board.pawnProgress := by
  obtain ⟨_, hv, he⟩ := hl i
  cases hm : tr.moves i with
  | boardMove src dst choice =>
    have hn : choice = none := by
      cases choice with
      | none => rfl
      | some q => exact (tr.not_promotion_of_periodic hl hp i src dst q hm).elim
    subst choice
    have hv' : PseudoLegal (tr.before i) (.boardMove src dst none) := by
      simpa only [hm, PseudoLegal] using hv.movement
    obtain ⟨p, hs, _, hne, _, _, hmove⟩ := hv'
    have hd := tr.boardMove_destination_empty_of_periodic hl hp i src dst none hm
    rw [he, hm]
    exact (tr.before i).board.pawnProgress_relocate_le src dst p hs hne hd hmove
  | enPassant src dst => exact (tr.not_enPassant_of_periodic hl hp i src dst hm).elim
  | castle side =>
    rw [he, hm]
    apply le_of_eq
    symm
    apply pawnProgress_applyMove_castle
    simpa only [hm, PseudoLegal] using hv.movement

theorem pawnProgress_eq_of_periodic (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (i j : Fin (tr.len + 1)) :
    (tr.states i).board.pawnProgress = (tr.states j).board.pawnProgress :=
  value_eq_of_monotone_periodic tr Board.pawnProgress (pawnProgress_step tr hl hp) hp i j

theorem boardMove_piece_ne_pawn_of_periodic (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos) (choice : Option Promotion)
    (hm : tr.moves i = .boardMove src dst choice) (p : Piece)
    (hs : (tr.before i).board src = some p) : p.kind ≠ .pawn := by
  intro hk
  have hn : choice = none := by
    cases choice with
    | none => rfl
    | some q => exact (tr.not_promotion_of_periodic hl hp i src dst q hm).elim
  subst choice
  obtain ⟨_, hv, he⟩ := hl i
  rw [hm] at he
  have hv' : PseudoLegal (tr.before i) (.boardMove src dst none) := by
    simpa only [hm, PseudoLegal] using hv.movement
  obtain ⟨q, hq, _, hne, _, _, hmove⟩ := hv'
  have heq : p = q := Option.some.inj (hs.symm.trans hq)
  subst q
  have hd := tr.boardMove_destination_empty_of_periodic hl hp i src dst none hm
  have hb : (tr.before i).board.pawnProgress < (tr.after i).board.pawnProgress := by
    rw [he]
    exact (tr.before i).board.pawnProgress_relocate_lt_of_pawn src dst p hs hne hd hmove hk
  have hc := tr.pawnProgress_eq_of_periodic hl hp i.succ i.castSucc
  change (tr.after i).board.pawnProgress = (tr.before i).board.pawnProgress at hc
  omega

/-- State zero uses the last check and uniqueness of king placement at the
equal endpoint boards. This is endpoint equality, not trace-wide king fixity. -/
theorem inCheck_turn_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (k : Fin (tr.len + 1)) :
    inCheck (tr.states k).board (tr.states k).turn (kp k (tr.states k).turn) := by
  refine Fin.cases ?_ (fun i => ?_) k
  · let lastMove : Fin tr.len := ⟨tr.len - 1, by omega⟩
    have hlast : lastMove.succ = Fin.last tr.len := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last, lastMove]
      omega
    have hkLast : MPC.Chess.KingsWellPlaced (tr.states 0).board (kp (Fin.last tr.len)) := by
      rw [← hp.1]
      exact hk _
    have hkp := hkLast.positions_unique (hk 0)
    have hturn := (hl lastMove).turn
    have hcheck := hc lastMove
    rw [← hturn] at hcheck
    change inCheck (tr.states lastMove.succ).board (tr.states lastMove.succ).turn
      (kp lastMove.succ (tr.states lastMove.succ).turn) at hcheck
    rw [hlast, hp.1, hp.2, hkp] at hcheck
    exact hcheck
  · have hturn := (hl i).turn
    have hcheck := hc i
    rw [← hturn] at hcheck
    exact hcheck

theorem not_castle_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (side : CastleSide) :
    tr.moves i ≠ .castle side := by
  intro hm
  obtain ⟨_, hv, _⟩ := hl i
  have hv' : CastleAllowed (tr.before i) side := by simpa only [hm, PseudoLegal] using hv.movement
  have hn : 0 < tr.len := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hcheck := tr.inCheck_turn_of_periodic_checks kp hl hk hc hp hn i.castSucc
  have hking : kingHome (tr.before i).turn = kp i.castSucc (tr.before i).turn :=
    (hk i.castSucc (tr.before i).turn _).mp hv'.2.1
  apply hv'.2.2.2.2.1
  rw [hking]
  exact hcheck

/-- The reduction used by the geometric proof: no capture, promotion, pawn
move, or special move remains. Ordinary king moves are still allowed here. -/
theorem ordinary_nonPawn_move_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) :
    ∃ src dst p, tr.moves i = .boardMove src dst none ∧
      (tr.before i).board src = some p ∧ p.owner = (tr.before i).turn ∧ p.kind ≠ .pawn ∧
      src ≠ dst ∧ (tr.before i).board dst = none ∧ attacks (tr.before i).board p src dst := by
  cases hm : tr.moves i with
  | boardMove src dst choice =>
    have hn : choice = none := by
      cases choice with
      | none => rfl
      | some q => exact (tr.not_promotion_of_periodic hl hp i src dst q hm).elim
    subst choice
    obtain ⟨_, hv, _⟩ := hl i
    have hv' : PseudoLegal (tr.before i) (.boardMove src dst none) := by
      simpa only [hm, PseudoLegal] using hv.movement
    obtain ⟨p, hs, ho, hne, _, _, hmove⟩ := hv'
    have hnp := tr.boardMove_piece_ne_pawn_of_periodic hl hp i src dst none hm p hs
    refine ⟨src, dst, p, rfl, hs, ho, hnp, hne,
      tr.boardMove_destination_empty_of_periodic hl hp i src dst none hm, ?_⟩
    simpa [OrdinaryMovement, hnp] using hmove
  | enPassant src dst => exact (tr.not_enPassant_of_periodic hl hp i src dst hm).elim
  | castle side => exact (tr.not_castle_of_periodic_checks kp hl hk hc hp i side hm).elim

end MPC.Chess.MoveTrace
