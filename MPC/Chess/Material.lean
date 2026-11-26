import MPC.Chess.Move
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-! Position-dependent integer sums. Empty squares contribute zero; no piece
identities or material bounds are assumed. Balances use addition, not truncated
subtraction. Move legality remains separate from these update identities. -/

namespace MPC.Chess
open scoped BigOperators

def Board.weightedSum (b : Board) (w : Pos → Piece → ℤ) : ℤ :=
  ∑ q, (b q).elim 0 (w q)

def Piece.pawnIndicator (p : Piece) : ℤ := if p.kind = .pawn then 1 else 0

def Piece.pawnProgressAt (p : Piece) (q : Pos) : ℤ :=
  if p.kind = .pawn then
    match p.owner with | .white => q.2.val | .black => 7 - (q.2.val : ℤ)
  else 0

def Board.pieceCount (b : Board) : ℤ := b.weightedSum fun _ _ => 1

def Board.pawnCount (b : Board) : ℤ := b.weightedSum fun _ p => p.pawnIndicator

def Board.pawnProgress (b : Board) : ℤ := b.weightedSum fun q p => p.pawnProgressAt q

private theorem sum_two (f g : Pos → ℤ) (a b : Pos) (hab : a ≠ b)
    (h : ∀ q, q ≠ a → q ≠ b → f q = g q) :
    ∑ q, f q + g a + g b = ∑ q, g q + f a + f b := by
  have hb : b ∈ (Finset.univ : Finset Pos).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  have ef := Finset.add_sum_erase (Finset.univ : Finset Pos) f (Finset.mem_univ a)
  have ef' := Finset.add_sum_erase ((Finset.univ : Finset Pos).erase a) f hb
  have eg := Finset.add_sum_erase (Finset.univ : Finset Pos) g (Finset.mem_univ a)
  have eg' := Finset.add_sum_erase ((Finset.univ : Finset Pos).erase a) g hb
  have hrest : ∑ q ∈ ((Finset.univ : Finset Pos).erase a).erase b, f q =
      ∑ q ∈ ((Finset.univ : Finset Pos).erase a).erase b, g q :=
    Finset.sum_congr rfl fun q hq => by
      obtain ⟨hqb, hq'⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqa, _⟩ := Finset.mem_erase.mp hq'
      exact h q hqa hqb
  omega

theorem Board.weightedSum_relocate (b : Board) (w : Pos → Piece → ℤ)
    (src dst : Pos) (p : Piece) (choice : Option Promotion)
    (hp : b src = some p) (hne : src ≠ dst) :
    (b.relocate src dst choice).weightedSum w + w src p + (b dst).elim 0 (w dst) =
      b.weightedSum w + w dst (p.promote choice) := by
  have h := sum_two
    (fun q => (b.relocate src dst choice q).elim 0 (w q))
    (fun q => (b q).elim 0 (w q)) src dst hne
    (fun q hs hd => by rw [Board.relocate_other b src dst q choice hs hd])
  simpa [Board.weightedSum, hp, Board.relocate_source b src dst choice hne] using h

theorem Board.weightedSum_erase (b : Board) (w : Pos → Piece → ℤ) (q : Pos) :
    (b.erase q).weightedSum w + (b q).elim 0 (w q) = b.weightedSum w := by
  have he := Finset.add_sum_erase (Finset.univ : Finset Pos)
    (fun r => (b.erase q r).elim 0 (w r)) (Finset.mem_univ q)
  have hb := Finset.add_sum_erase (Finset.univ : Finset Pos)
    (fun r => (b r).elim 0 (w r)) (Finset.mem_univ q)
  have hr : ∑ r ∈ (Finset.univ : Finset Pos).erase q, (b.erase q r).elim 0 (w r) =
      ∑ r ∈ (Finset.univ : Finset Pos).erase q, (b r).elim 0 (w r) := by
    apply Finset.sum_congr rfl
    intro r hr
    simp [Board.erase, (Finset.mem_erase.mp hr).1]
  have hq : b.erase q q = none := by simp [Board.erase]
  rw [hq, Option.elim_none, zero_add] at he
  unfold Board.weightedSum
  omega

private theorem ep_distinct {pos : Position} {src dst : Pos}
    (hm : PseudoLegal pos (.enPassant src dst)) :
    src ≠ enPassantCaptured src dst ∧ dst ≠ enPassantCaptured src dst ∧ src ≠ dst := by
  have ha := hm.2.2.2.2.1
  have hx : src.1 ≠ dst.1 := by
    intro he
    have h := ha.2.1
    simp [Pos.delta, Pos.toInt, he] at h
  have hy : src.2 ≠ dst.2 := by
    intro he
    have h := ha.2.2
    cases ht : pos.turn <;> simp [Pos.delta, Pos.toInt, he, ht, Color.forward] at h
  refine ⟨?_, ?_, ha.1⟩
  · intro he
    apply hx
    simpa [enPassantCaptured] using congrArg Prod.fst he
  · intro he
    apply hy
    simpa [enPassantCaptured] using (congrArg Prod.snd he).symm

theorem weightedSum_applyMove_enPassant (pos : Position) (src dst : Pos)
    (hm : PseudoLegal pos (.enPassant src dst)) (w : Pos → Piece → ℤ) :
    (applyMove pos (.enPassant src dst)).board.weightedSum w +
        w (enPassantCaptured src dst) ⟨pos.turn.opponent, .pawn⟩ + w src ⟨pos.turn, .pawn⟩ =
      pos.board.weightedSum w + w dst ⟨pos.turn, .pawn⟩ := by
  obtain ⟨hs, hd, hne⟩ := ep_distinct hm
  have hp : pos.board.erase (enPassantCaptured src dst) src = some ⟨pos.turn, .pawn⟩ := by
    simpa [Board.erase, hs] using hm.1
  have he := pos.board.weightedSum_erase w (enPassantCaptured src dst)
  have hr := (pos.board.erase (enPassantCaptured src dst)).weightedSum_relocate
    w src dst ⟨pos.turn, .pawn⟩ none hp hne
  simp only [hm.2.2.2.2.2, Option.elim_some] at he
  simp only [Board.erase, ite_eq_right hd, hm.2.1, Option.elim_none, add_zero, Piece.promote] at hr
  change ((pos.board.erase (enPassantCaptured src dst)).relocate src dst none).weightedSum w +
    w (enPassantCaptured src dst) ⟨pos.turn.opponent, .pawn⟩ + w src ⟨pos.turn, .pawn⟩ = _
  omega

theorem weightedSum_applyMove_castle (pos : Position) (side : CastleSide)
    (hm : CastleAllowed pos side) (w : Pos → Piece → ℤ) :
    (applyMove pos (.castle side)).board.weightedSum w +
        w (kingHome pos.turn) ⟨pos.turn, .king⟩ + w (rookHome pos.turn side) ⟨pos.turn, .rook⟩ =
      pos.board.weightedSum w + w (castleKingDestination pos.turn side) ⟨pos.turn, .king⟩ +
        w (castleRookDestination pos.turn side) ⟨pos.turn, .rook⟩ := by
  have hkdst : pos.board (castleKingDestination pos.turn side) = none := by
    apply hm.2.2.2.1
    cases pos.turn <;> cases side <;> decide
  have hrdst : pos.board (castleRookDestination pos.turn side) = none := by
    apply hm.2.2.2.1
    cases pos.turn <;> cases side <;> decide
  let b := pos.board.relocate (kingHome pos.turn) (castleKingDestination pos.turn side) none
  have hrs : b (rookHome pos.turn side) = some ⟨pos.turn, .rook⟩ := by
    dsimp only [b]
    rw [Board.relocate_other]
    · exact hm.2.2.1
    · cases pos.turn <;> cases side <;> decide
    · cases pos.turn <;> cases side <;> decide
  have hrd : b (castleRookDestination pos.turn side) = none := by
    dsimp only [b]
    rw [Board.relocate_other]
    · exact hrdst
    · cases pos.turn <;> cases side <;> decide
    · cases pos.turn <;> cases side <;> decide
  have hk := pos.board.weightedSum_relocate w (kingHome pos.turn)
    (castleKingDestination pos.turn side) ⟨pos.turn, .king⟩ none hm.2.1
    (by cases pos.turn <;> cases side <;> decide)
  have hr := b.weightedSum_relocate w (rookHome pos.turn side)
    (castleRookDestination pos.turn side) ⟨pos.turn, .rook⟩ none hrs
    (by cases pos.turn <;> cases side <;> decide)
  simp only [hkdst, Option.elim_none, add_zero, Piece.promote] at hk
  simp only [hrd, Option.elim_none, add_zero, Piece.promote] at hr
  change (b.relocate (rookHome pos.turn side) (castleRookDestination pos.turn side) none).weightedSum w + _ + _ = _
  change b.weightedSum w + _ = _ at hk
  omega

theorem Board.pieceCount_relocate (b : Board) (src dst : Pos) (p : Piece)
    (choice : Option Promotion) (hp : b src = some p) (hne : src ≠ dst) :
    (b.relocate src dst choice).pieceCount + (b dst).elim 0 (fun _ => (1 : ℤ)) = b.pieceCount := by
  have h := b.weightedSum_relocate (fun _ _ => 1) src dst p choice hp hne
  change (b.relocate src dst choice).pieceCount + 1 + (b dst).elim 0 (fun _ => (1 : ℤ)) =
    b.pieceCount + 1 at h
  omega

theorem pieceCount_applyMove_enPassant (pos : Position) (src dst : Pos)
    (hm : PseudoLegal pos (.enPassant src dst)) :
    (applyMove pos (.enPassant src dst)).board.pieceCount + 1 = pos.board.pieceCount := by
  have h := weightedSum_applyMove_enPassant pos src dst hm (fun _ _ => 1)
  change (applyMove pos (.enPassant src dst)).board.pieceCount + 1 + 1 = pos.board.pieceCount + 1 at h
  omega

theorem pieceCount_applyMove_le (pos : Position) (move : Move) (hm : PseudoLegal pos move) :
    (applyMove pos move).board.pieceCount ≤ pos.board.pieceCount := by
  cases move with
  | boardMove src dst choice =>
    obtain ⟨p, hp, _, hne, _⟩ := hm
    have h := pos.board.pieceCount_relocate src dst p choice hp hne
    change (pos.board.relocate src dst choice).pieceCount ≤ _
    cases hd : pos.board dst <;> simp only [hd, Option.elim_none, Option.elim_some] at h <;> omega
  | enPassant src dst => have h := pieceCount_applyMove_enPassant pos src dst hm; omega
  | castle side =>
    have h := weightedSum_applyMove_castle pos side hm (fun _ _ => 1)
    change (applyMove pos (.castle side)).board.pieceCount + 1 + 1 = pos.board.pieceCount + 1 + 1 at h
    omega

private theorem pawnIndicator_nonneg (p : Piece) : 0 ≤ p.pawnIndicator := by
  unfold Piece.pawnIndicator
  split <;> omega

private theorem pawnIndicator_promote_le (p : Piece) (choice : Option Promotion) :
    (p.promote choice).pawnIndicator ≤ p.pawnIndicator := by
  rcases p with ⟨c, kind⟩
  cases choice with
  | none => exact le_rfl
  | some q => cases kind <;> cases q <;> simp [Piece.promote, Piece.pawnIndicator, Promotion.pieceType]

theorem Board.pawnCount_relocate_le (b : Board) (src dst : Pos) (p : Piece)
    (choice : Option Promotion) (hp : b src = some p) (hne : src ≠ dst) :
    (b.relocate src dst choice).pawnCount ≤ b.pawnCount := by
  have h := b.weightedSum_relocate (fun _ p => p.pawnIndicator) src dst p choice hp hne
  have hm := pawnIndicator_promote_le p choice
  have hd : 0 ≤ (b dst).elim 0 Piece.pawnIndicator := by
    cases b dst with
    | none => exact le_rfl
    | some q => exact pawnIndicator_nonneg q
  change (b.relocate src dst choice).pawnCount + p.pawnIndicator +
    (b dst).elim 0 Piece.pawnIndicator = b.pawnCount + (p.promote choice).pawnIndicator at h
  omega

theorem pawnCount_applyMove_le (pos : Position) (move : Move) (hm : PseudoLegal pos move) :
    (applyMove pos move).board.pawnCount ≤ pos.board.pawnCount := by
  cases move with
  | boardMove src dst choice =>
    obtain ⟨p, hp, _, hne, _⟩ := hm
    exact pos.board.pawnCount_relocate_le src dst p choice hp hne
  | enPassant src dst =>
    have h := weightedSum_applyMove_enPassant pos src dst hm (fun _ p => p.pawnIndicator)
    change (applyMove pos (.enPassant src dst)).board.pawnCount + 1 + 1 = pos.board.pawnCount + 1 at h
    omega
  | castle side =>
    have h := weightedSum_applyMove_castle pos side hm (fun _ p => p.pawnIndicator)
    change (applyMove pos (.castle side)).board.pawnCount + 0 + 0 = pos.board.pawnCount + 0 + 0 at h
    omega

theorem pawnCount_applyMove_promotion_lt (pos : Position) (src dst : Pos) (q : Promotion)
    (hm : PseudoLegal pos (.boardMove src dst (some q))) :
    (applyMove pos (.boardMove src dst (some q))).board.pawnCount < pos.board.pawnCount := by
  obtain ⟨p, hp, _, hne, _, hprom, _⟩ := hm
  have hkind : p.kind = .pawn := hprom.1
  have h := pos.board.weightedSum_relocate (fun _ p => p.pawnIndicator) src dst p (some q) hp hne
  have hd : 0 ≤ (pos.board dst).elim 0 Piece.pawnIndicator := by
    cases pos.board dst with
    | none => exact le_rfl
    | some r => exact pawnIndicator_nonneg r
  have hnew : (p.promote (some q)).pawnIndicator = 0 := by
    cases q <;> simp [Piece.promote, Piece.pawnIndicator, hkind, Promotion.pieceType]
  have hold : p.pawnIndicator = 1 := by simp [Piece.pawnIndicator, hkind]
  change (applyMove pos (.boardMove src dst (some q))).board.pawnCount + p.pawnIndicator +
    (pos.board dst).elim 0 Piece.pawnIndicator = pos.board.pawnCount +
    (p.promote (some q)).pawnIndicator at h
  omega

private theorem pawnProgress_forward {b : Board} {c : Color} {src dst : Pos}
    (hm : PawnMovement b c src dst) (hd : b dst = none) :
    (Piece.mk c .pawn).pawnProgressAt src < (Piece.mk c .pawn).pawnProgressAt dst := by
  obtain ⟨_, _, hquiet | hcapture⟩ := hm
  · rcases hquiet.2.2 with hs | ⟨_, hs, _⟩
    all_goals cases c <;> simp [Piece.pawnProgressAt, Color.forward, Pos.delta, Pos.toInt] at * <;> omega
  · exact (hcapture.1 hd).elim

theorem Board.pawnProgress_relocate_le (b : Board) (src dst : Pos) (p : Piece)
    (hp : b src = some p) (hne : src ≠ dst) (hd : b dst = none)
    (hm : OrdinaryMovement b p src dst) :
    b.pawnProgress ≤ (b.relocate src dst none).pawnProgress := by
  have h := b.weightedSum_relocate (fun q p => p.pawnProgressAt q) src dst p none hp hne
  simp only [hd, Option.elim_none, add_zero, Piece.promote] at h
  change (b.relocate src dst none).pawnProgress + _ = b.pawnProgress + _ at h
  by_cases hk : p.kind = .pawn
  · have hpawn : p = ⟨p.owner, .pawn⟩ := by cases p; simp_all
    have hf := pawnProgress_forward (by simpa [OrdinaryMovement, hk] using hm) hd
    rw [← hpawn] at hf
    omega
  · simp [Piece.pawnProgressAt, hk] at h
    omega

theorem Board.pawnProgress_relocate_lt_of_pawn (b : Board) (src dst : Pos) (p : Piece)
    (hp : b src = some p) (hne : src ≠ dst) (hd : b dst = none)
    (hm : OrdinaryMovement b p src dst) (hk : p.kind = .pawn) :
    b.pawnProgress < (b.relocate src dst none).pawnProgress := by
  have h := b.weightedSum_relocate (fun q p => p.pawnProgressAt q) src dst p none hp hne
  simp only [hd, Option.elim_none, add_zero, Piece.promote] at h
  change (b.relocate src dst none).pawnProgress + _ = b.pawnProgress + _ at h
  have hpawn : p = ⟨p.owner, .pawn⟩ := by cases p; simp_all
  have hf := pawnProgress_forward (by simpa [OrdinaryMovement, hk] using hm) hd
  rw [← hpawn] at hf
  omega

theorem pawnProgress_applyMove_castle (pos : Position) (side : CastleSide)
    (hm : CastleAllowed pos side) :
    (applyMove pos (.castle side)).board.pawnProgress = pos.board.pawnProgress := by
  have h := weightedSum_applyMove_castle pos side hm (fun q p => p.pawnProgressAt q)
  change (applyMove pos (.castle side)).board.pawnProgress + 0 + 0 =
    pos.board.pawnProgress + 0 + 0 at h
  simpa using h

end MPC.Chess
