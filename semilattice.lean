-- Madhav Ram - Proof101 - Assignment 6
-- April 2026

-- Formally Verified Semilattice Class for Conflict-free Replicated Data Types (CRDTs)

/-
  Type class for Semilattice
  Core properties are associativity, commutivity and idempotence
-/
class Semilattice (α : Type) where

  join : α → α → α

  -- Core properties of a Semilattice
  join_asoc : ∀ a b c, join (join a b) c = join a (join b c)
  join_comm : ∀ a b, join a b = join b a
  join_idem : ∀ a, join a a = a


/-
  Definition of less than equal operator to later
  prove partial order theorems of Semillatice
  It needs to be reflective, antisymmetric and transitive
-/
def semilattice_le {α : Type} [Semilattice α] (a b : α) :=
  Semilattice.join a b = a

theorem semilattice_le_refl {α : Type} [Semilattice α] (a : α) : semilattice_le a a := by
  unfold semilattice_le
  exact Semilattice.join_idem a

theorem semilattice_le_antisymm {α : Type} [Semilattice α] (a b : α) : semilattice_le a b → semilattice_le b a → a = b := by
  unfold semilattice_le
  rw [Semilattice.join_comm]
  intro h1
  intro h2
  rw[← h1]
  exact h2

theorem semilattice_le_trans {α : Type} [Semilattice α] (a b c : α) :
  semilattice_le a b → semilattice_le b c → semilattice_le a c := by
    unfold semilattice_le
    intro h1
    intro h2
    rw[← h1]
    rw[Semilattice.join_asoc]
    rw[h2]


-- Initial State of a Semilattice used for many CRDTs
class BoundedSemilattice (α : Type) extends Semilattice α where
  bottom : α
  join_bottom : ∀ x, Semilattice.join x bottom = x

-- (Update) Functions on Semilattice are "Grow-only" - monotonic
def is_inflationary {α : Type} [Semilattice α] (f : α → α) : Prop :=
  ∀ x, semilattice_le (f x) x

-- G Counter Implementation on BoundedSemilattice
abbrev Gcounter := Nat  -- def does not inherit properties of original type and is unable to set bottom to 0
instance : BoundedSemilattice Gcounter where
  join := Nat.max

  join_asoc := Nat.max_assoc
  join_comm := Nat.max_comm
  join_idem := Nat.max_self

  bottom := 0
  join_bottom := Nat.max_zero

def gcounter_increment (n: Gcounter) : Gcounter :=
 n + 1

theorem gcounter_increment_is_inflationary : is_inflationary gcounter_increment := by
  unfold is_inflationary
  unfold semilattice_le
  unfold gcounter_increment
  intro x
  apply Nat.max_eq_left
  apply Nat.le_succ


-- Vector Clock implementation using a BoundSemilattice
-- NodeId is a the string label or ID for a Vector Clock
abbrev NodeId := String
abbrev VectorClock := NodeId → Nat

def vc_bottom : VectorClock :=
  fun _ => 0

def vc_join (v1 v2 : VectorClock) : VectorClock :=
  fun i => Nat.max (v1 i) (v2 i)


instance : BoundedSemilattice VectorClock where
  join := vc_join
  bottom := vc_bottom

  join_asoc v1 v2 v3 := by
    -- funext prove f = g by proving f(i) = g(i) for a NodeID i
    funext i
    apply Nat.max_assoc

  join_comm v1 v2 := by
    funext i
    apply Nat.max_comm

  join_idem v := by
    funext i
    apply Nat.max_self

  join_bottom v := by
    funext i
    apply Nat.max_zero


def vc_increment (vc : VectorClock) (node : NodeId) : VectorClock :=
  fun i =>
    if i = node then vc i + 1
    else vc i

-- need to replace f arg for is_inflationary with the whole vc_increment signature
theorem vc_increment_is_inflationary (node: NodeId) : is_inflationary (fun vc => vc_increment vc node) := by
  unfold is_inflationary semilattice_le
  intro vc
  funext i
  simp [vc_increment]
  simp [Semilattice.join, vc_join, vc_increment]
  split
  simp_all -- used to replace i with node as i is a node and solves trivial h.isTrue
  apply Nat.max_eq_left
  simp

/-
  PN-Counter implementation
  The value of the PN Counter will be stored in two G Counters
  Increments in G Counter 1 and
  Decrements in G Counter 2
  The final value is G Counter 1 - G Counter 2
-/
abbrev PNcounter := Gcounter × Gcounter

def pnc_bottom : PNcounter :=
  -- (Gcounter.bottom, Gcounter.bottom)
  (0, 0)

def pnc_join (pnc1 pnc2 : PNcounter) : PNcounter :=
  (Nat.max pnc1.fst pnc2.fst, Nat.max pnc1.snd pnc2.snd)


instance : BoundedSemilattice PNcounter where
  join := pnc_join
  bottom := pnc_bottom

  join_asoc a b c := by
    -- ext breaks down into cases for my PNcounter pair
    -- this allows to match type with Nat.max lemmas
    ext
    · exact Nat.max_assoc a.1 b.1 c.1
    · exact Nat.max_assoc a.2 b.2 c.2

  join_comm a b := by
    ext
    . exact Nat.max_comm a.1 b.1
    . exact Nat.max_comm a.2 b.2

  join_idem a := by
    ext
    . exact Nat.max_self a.1
    . exact Nat.max_self a.2

  join_bottom a := by
    ext
    . exact Nat.max_zero a.1
    . exact Nat.max_zero a.2


def pnc_increment (pnc : PNcounter) : PNcounter :=
  (pnc.1 + 1, pnc.2)

def pnc_decrement (pnc : PNcounter) : PNcounter :=
  (pnc.1, pnc.2 + 1)

-- Total need not be a Nat, can be negative
def pnc_total (pnc : PNcounter) : Int :=
  pnc.1 - pnc.2

theorem pnc_increment_is_inflationary : is_inflationary pnc_increment := by
  unfold is_inflationary semilattice_le
  intro pnc
  simp [pnc_increment]
  ext
  ·
    apply Nat.max_eq_left
    apply Nat.le_succ
  ·
    apply Nat.max_self

theorem pnc_decrement_is_inflationary : is_inflationary pnc_decrement := by
  unfold is_inflationary semilattice_le
  intro pnc
  simp [pnc_decrement]
  ext
  ·
    apply Nat.max_self
  ·
    apply Nat.max_eq_left
    apply Nat.le_succ
