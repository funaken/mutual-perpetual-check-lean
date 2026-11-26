import MPC.Basic.Lemmas
import MPC.Pieces.BishopFrontEdge
/-!
# MPC.Pieces.BishopTable

Both sides' bishops together: the paper's Table 1. The premises are
those of the main theorem. Fix a side `o` with forward sign `τ`, its enemy king `K`
at the origin, and its own king `L = l`.

By , `o`'s bishop moves between `a = (σt, 0)` and `b = (0, ρt)` with
`ρ = -τ`. The opponent's bishop does the same around `L` in its own orientation: it
moves between `a' = L + (σ't', 0)` and `b' = L + (0, τt')`. Both kings must be
candidates for the respective edges. An integer case analysis
(`bishop_table_cases`) leaves:
- the paper's rows: `l = (2σ, ρ)`, `(σ, 2ρ)`, or `(σ, 3ρ)` with `t = t' = 1`, and
  `l = (3σ, 2ρ)` or `(σ, 2ρ)` with `t = t' = 2` (`BishopRow`);
- `l = (σt, ρt)` with `t = t'`, where both bishops use the same two squares;
- `l = (σ, 2ρ)` with `{t, t'} = {1, 2}`, where they share one square.

The paper excludes the last two "other than the own bishop's squares". Here they
are excluded as follows (`bishop_rows_of_periodic`).
- Same squares: before `o`'s move `a → b` the other bishop stands on `b`, the move's
  destination. A non-glaring piece there contradicts Lemma 2.9.
- One shared square: one bishop moves into the shared square while the other stands
  on the middle of that diagonal move, which then cannot be made.
-/

namespace MPC

/-- The paper's Table 1 rows, as `(t, t', l)` for `σ` and `ρ`. -/
def BishopRow (σ ρ t t' : ℤ) (l : ℤ × ℤ) : Prop :=
  (t = 1 ∧ t' = 1 ∧ (l = (2 * σ, ρ) ∨ l = (σ, 2 * ρ) ∨ l = (σ, 3 * ρ))) ∨
    (t = 2 ∧ t' = 2 ∧ (l = (3 * σ, 2 * ρ) ∨ l = (σ, 2 * ρ)))

set_option maxHeartbeats 2000000 in
/-- The integer case analysis of both kings' candidacy. -/
theorem bishop_table_cases (τ σ σ' t t' : ℤ) (hτ : τ = 1 ∨ τ = -1) (hσ : σ = 1 ∨ σ = -1)
    (hσ' : σ' = 1 ∨ σ' = -1) (ht : 1 ≤ t) (l : ℤ × ℤ)
    (hl1 : 0 < σ * l.1) (hl2 : 0 < -τ * l.2) (hl1' : 0 < σ' * -l.1) (hl2' : 0 < τ * -l.2)
    (hfar : ¬ (-1 ≤ l.1 ∧ l.1 ≤ 1 ∧ -1 ≤ l.2 ∧ l.2 ≤ 1))
    (hc : KingCandidate τ σ (-τ) t l) (hc' : KingCandidate (-τ) σ' τ t' (-l.1, -l.2)) :
    σ' = -σ ∧ (BishopRow σ (-τ) t t' l ∨ (t' = t ∧ l = (σ * t, -τ * t)) ∨
      (l = (σ, 2 * -τ) ∧ ((t = 1 ∧ t' = 2) ∨ (t = 2 ∧ t' = 1)))) := by
  obtain ⟨l1, l2⟩ := l
  unfold KingCandidate at hc hc'
  unfold BishopRow
  dsimp only at hl1 hl2 hl1' hl2' hfar hc hc' ⊢
  simp only [Prod.mk.injEq] at hc hc' ⊢
  rcases hτ with rfl | rfl <;> rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;>
    rcases hc with h | ⟨h1, h | h | ⟨h3, h⟩⟩ | ⟨h1, h3, h | h⟩ <;>
    rcases hc' with h' | ⟨h1', h' | h' | ⟨h3', h'⟩⟩ | ⟨h1', h3', h' | h'⟩ <;>
    omega

namespace MoveTrace

/-- Under the premises of the main theorem, a move's destination never holds a bishop or
    horse before the move: it would glare (Lemma 2.9). -/
theorem destination_not_bishopHorse_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo)
    (i : Fin tr.len) (P : Piece)
    (hP : (tr.before i).board.grid (tr.moves i).destination = some P)
    (hPt : P.pieceType = .bishop ∨ P.pieceType = .horse) : False := by
  have hm' := hm
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  have hg := tr.glares_destination_of_occupied_of_periodic kp ht hs hk hsafe h0 hc hr hp i
    (by rw [hP]; exact Option.some_ne_none _)
  exact tr.not_glares_bishopHorse_of_periodic kp hm' h41 hcount i.castSucc _ P hP hPt hg

/-- Under the premises of the main theorem, a bishop or horse never moves two squares
    diagonally past an occupied middle square. -/
theorem not_bishop_move_past_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (i : Fin tr.len) (src dst M : Pos) (pr : Bool) (P : Piece)
    (hmv : tr.moves i = .boardMove src dst pr) (hP : (tr.before i).board.grid src = some P)
    (u : Dir) (hu : u ∈ PieceType.king.stepDirs)
    (hdst : dst.toInt = (src.toInt.1 + 2 * u.1, src.toInt.2 + 2 * u.2))
    (hM : M.toInt = (src.toInt.1 + 1 * u.1, src.toInt.2 + 1 * u.2))
    (hocc : (tr.before i).board.grid M ≠ none) : False :=
  not_canMoveToOriented_of_blocked _ P.owner P.pieceType src dst M u 2 1 hu hdst (le_refl _)
    (by norm_num) hM hocc (hm.movementRules i src dst pr P hmv hP)

/-- Both sides' bishops are in one of Table 1's rows. For a side `o` with forward sign
    `τ`, relative to its enemy king `K`, with its own king `L`:
    - `o`'s bishop always stands on `a = (σt, 0)` or `b = (0, -τt)` and moves both ways;
    - the opponent's always stands on `a' = L + (-σt', 0)` or `b' = L + (0, τt')` and
      moves both ways;
    - `(t, t', L)` is a row of Table 1. -/
theorem bishop_rows_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo) (o : Player) :
    ∃ (t t' σ : ℤ) (a b a' b' : Pos), (σ = 1 ∨ σ = -1) ∧
      relTo (kp 0 o.opponent) a = (σ * t, 0) ∧
      relTo (kp 0 o.opponent) b = (0, -forwardSign o * t) ∧
      relTo (kp 0 o.opponent) a' =
        ((relTo (kp 0 o.opponent) (kp 0 o)).1 - σ * t', (relTo (kp 0 o.opponent) (kp 0 o)).2) ∧
      relTo (kp 0 o.opponent) b' =
        ((relTo (kp 0 o.opponent) (kp 0 o)).1,
          (relTo (kp 0 o.opponent) (kp 0 o)).2 + forwardSign o * t') ∧
      BishopRow σ (-forwardSign o) t t' (relTo (kp 0 o.opponent) (kp 0 o)) ∧
      (∃ (i : Fin tr.len) (pr : Bool) (P : Piece), tr.moves i = .boardMove a b pr ∧
        (tr.before i).board.grid a = some P ∧ P.owner = o ∧
        ¬ tr.GlaresAtEnemyKing kp i.castSucc a) ∧
      (∃ (i : Fin tr.len) (pr : Bool) (P : Piece), tr.moves i = .boardMove b a pr ∧
        (tr.before i).board.grid b = some P ∧ P.owner = o ∧
        ¬ tr.GlaresAtEnemyKing kp i.castSucc b) ∧
      (∀ (k : Fin (tr.len + 1)) (q : Pos) (P : Piece), (tr.states k).board.grid q = some P →
        P.owner = o → (P.pieceType = .bishop ∨ P.pieceType = .horse) → q = a ∨ q = b) ∧
      (∃ (i : Fin tr.len) (pr : Bool) (P : Piece), tr.moves i = .boardMove a' b' pr ∧
        (tr.before i).board.grid a' = some P ∧ P.owner = o.opponent ∧
        ¬ tr.GlaresAtEnemyKing kp i.castSucc a') ∧
      (∃ (i : Fin tr.len) (pr : Bool) (P : Piece), tr.moves i = .boardMove b' a' pr ∧
        (tr.before i).board.grid b' = some P ∧ P.owner = o.opponent ∧
        ¬ tr.GlaresAtEnemyKing kp i.castSucc b') ∧
      (∀ (k : Fin (tr.len + 1)) (q : Pos) (P : Piece), (tr.states k).board.grid q = some P →
        P.owner = o.opponent → (P.pieceType = .bishop ∨ P.pieceType = .horse) →
        q = a' ∨ q = b') := by
  have hm' := hm
  obtain ⟨t, σ, ρ, a, b, ht1, hσ, hρ, hra, hrb, hl1, hl2, hcand, hab, hba, hloc⟩ :=
    tr.bishop_configuration_back_of_periodic kp hm h41 hcount o
  obtain ⟨t', σ', ρ', a', b', ht1', hσ', hρ', hra', hrb', hl1', hl2', hcand', hab', hba', hloc'⟩ :=
    tr.bishop_configuration_back_of_periodic kp hm h41 hcount o.opponent
  rw [Player.opponent_opponent] at hra' hrb' hl1' hl2' hcand'
  rw [forwardSign_opponent, neg_neg] at hρ'
  rw [forwardSign_opponent] at hcand'
  subst hρ
  subst hρ'
  obtain ⟨K, hKdef⟩ : ∃ K, K = kp 0 o.opponent := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = kp 0 o := ⟨_, rfl⟩
  rw [← hKdef] at hra hrb hl1 hl2 hcand ⊢
  rw [← hLdef] at hra' hrb' hl1' hl2' hcand' hl1 hl2 hcand ⊢
  rw [← hKdef] at hl1' hl2' hcand'
  have hfar := tr.relTo_king_far_of_periodic kp hm' o
  rw [← hKdef, ← hLdef] at hfar
  have hneg : relTo L K = (-(relTo K L).1, -(relTo K L).2) := by
    simp only [relTo]
    ext <;> dsimp only <;> ring
  rw [hneg] at hl1' hl2' hcand'
  have hτ := forwardSign_cases o
  obtain ⟨hσσ, hcases⟩ := bishop_table_cases (forwardSign o) σ σ' t t' hτ hσ hσ' ht1
    (relTo K L) hl1 (by simpa using hl2) (by simpa using hl1') (by simpa using hl2') hfar hcand
    hcand'
  subst hσσ
  -- The opponent's squares relative to `K`.
  have hra'K : relTo K a' = ((relTo K L).1 - σ * t', (relTo K L).2) := by
    have e1 := congrArg Prod.fst hra'
    have e2 := congrArg Prod.snd hra'
    simp only [relTo] at e1 e2 ⊢
    ext <;> dsimp only <;> linarith
  have hrb'K : relTo K b' = ((relTo K L).1, (relTo K L).2 + forwardSign o * t') := by
    have e1 := congrArg Prod.fst hrb'
    have e2 := congrArg Prod.snd hrb'
    simp only [relTo] at e1 e2 ⊢
    ext <;> dsimp only <;> linarith
  rcases hcases with hrow | ⟨htt, hL⟩ | ⟨hL, htt⟩
  · exact ⟨t, t', σ, a, b, a', b', hσ, hra, hrb, hra'K, hrb'K, hrow, hab, hba, hloc, hab', hba',
      hloc'⟩
  · -- Same squares: the opponent's bishop blocks `o`'s move `a → b`.
    exfalso
    subst htt
    have ha'b : a' = b := relTo_inj (by rw [hra'K, hrb, hL]; ext <;> simp)
    obtain ⟨i, pr, P, hmi, hPi, hPo, _⟩ := hab
    obtain ⟨q, Q, hQ, hQo, hQt, _⟩ :=
      tr.exists_openable_bishopHorse_of_periodic kp hm' h41 hcount i.castSucc o.opponent
    have hPt := tr.bishopHorse_of_nonGlaring_move kp hm' h41 hcount i a b pr P hmi hPi ‹_›
    rcases hloc' _ q Q hQ hQo hQt with rfl | rfl
    · -- On `b`, the destination.
      apply tr.destination_not_bishopHorse_of_periodic kp hm' h41 hcount i Q _ hQt
      rw [hmi]
      change (tr.states i.castSucc).board.grid b = some Q
      rw [← ha'b]
      exact hQ
    · -- On `b' = a`, where `o`'s bishop stands.
      have hb'a : q = a := relTo_inj (by rw [hrb'K, hra, hL]; ext <;> simp)
      rw [hb'a] at hQ
      change (tr.states i.castSucc).board.grid a = some P at hPi
      rw [hPi] at hQ
      cases hQ
      rw [hPo] at hQo
      cases o <;> cases hQo
  · -- One shared square: the other bishop stands on the middle of a diagonal move.
    exfalso
    rcases htt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- `t = 1`, `t' = 2`: `b' = a`, and the opponent's move `a' → a` passes `b`.
      have hb'a : b' = a := relTo_inj (by rw [hrb'K, hra, hL]; ext <;> dsimp only <;> ring)
      obtain ⟨j, pr, P, hmj, hPj, hPo, hngj⟩ := hab'
      obtain ⟨q, Q, hQ, hQo, hQt, _⟩ :=
        tr.exists_openable_bishopHorse_of_periodic kp hm' h41 hcount j.castSucc o
      rcases hloc _ q Q hQ hQo hQt with rfl | rfl
      · apply tr.destination_not_bishopHorse_of_periodic kp hm' h41 hcount j Q _ hQt
        rw [hmj]
        change (tr.states j.castSucc).board.grid b' = some Q
        rw [hb'a]
        exact hQ
      · apply tr.not_bishop_move_past_of_periodic kp hm' j a' b' q pr P hmj hPj
          (σ, forwardSign o) (by rcases hσ with rfl | rfl <;> rcases hτ with h | h <;> rw [h] <;>
            decide)
        · have e1 := congrArg Prod.fst hra'K
          have e2 := congrArg Prod.snd hra'K
          have f1 := congrArg Prod.fst hrb'K
          have f2 := congrArg Prod.snd hrb'K
          have g1 := congrArg Prod.fst hL
          have g2 := congrArg Prod.snd hL
          simp only [relTo] at e1 e2 f1 f2 g1 g2
          ext <;> dsimp only <;> linarith
        · have e1 := congrArg Prod.fst hra'K
          have e2 := congrArg Prod.snd hra'K
          have f1 := congrArg Prod.fst hrb
          have f2 := congrArg Prod.snd hrb
          have g1 := congrArg Prod.fst hL
          have g2 := congrArg Prod.snd hL
          simp only [relTo] at e1 e2 f1 f2 g1 g2
          ext <;> dsimp only <;> linarith
        · change (tr.states j.castSucc).board.grid q ≠ none
          rw [hQ]
          exact Option.some_ne_none _
    · -- `t = 2`, `t' = 1`: `a' = b`, and `o`'s move `a → b` passes `b'`.
      have ha'b : a' = b := relTo_inj (by rw [hra'K, hrb, hL]; ext <;> dsimp only <;> ring)
      obtain ⟨i, pr, P, hmi, hPi, hPo, hngi⟩ := hab
      obtain ⟨q, Q, hQ, hQo, hQt, _⟩ :=
        tr.exists_openable_bishopHorse_of_periodic kp hm' h41 hcount i.castSucc o.opponent
      rcases hloc' _ q Q hQ hQo hQt with rfl | rfl
      · apply tr.destination_not_bishopHorse_of_periodic kp hm' h41 hcount i Q _ hQt
        rw [hmi]
        change (tr.states i.castSucc).board.grid b = some Q
        rw [← ha'b]
        exact hQ
      · apply tr.not_bishop_move_past_of_periodic kp hm' i a b q pr P hmi hPi
          (-σ, -forwardSign o) (by rcases hσ with rfl | rfl <;> rcases hτ with h | h <;>
            rw [h] <;> decide)
        · have e1 := congrArg Prod.fst hra
          have e2 := congrArg Prod.snd hra
          have f1 := congrArg Prod.fst hrb
          have f2 := congrArg Prod.snd hrb
          simp only [relTo] at e1 e2 f1 f2
          ext <;> dsimp only <;> linarith
        · have e1 := congrArg Prod.fst hra
          have e2 := congrArg Prod.snd hra
          have f1 := congrArg Prod.fst hrb'K
          have f2 := congrArg Prod.snd hrb'K
          have g1 := congrArg Prod.fst hL
          have g2 := congrArg Prod.snd hL
          simp only [relTo] at e1 e2 f1 f2 g1 g2
          ext <;> dsimp only <;> linarith
        · change (tr.states i.castSucc).board.grid q ≠ none
          rw [hQ]
          exact Option.some_ne_none _

end MoveTrace
end MPC
