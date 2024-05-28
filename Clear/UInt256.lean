import Init.Data.Nat.Div
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

-- 2^256
@[simp]
def UInt256.size : ℕ := 115792089237316195423570985008687907853269984665640564039457584007913129639936

instance : NeZero UInt256.size := ⟨by decide⟩

abbrev UInt256 := Fin UInt256.size

instance : SizeOf UInt256 where
  sizeOf := 1

instance (n : ℕ) : OfNat UInt256 n := ⟨Fin.ofNat n⟩
instance : Inhabited UInt256 := ⟨0⟩
instance : NatCast UInt256 := ⟨Fin.ofNat⟩

abbrev Nat.toUInt256 : ℕ → UInt256 := Fin.ofNat
abbrev UInt8.toUInt256 (a : UInt8) : UInt256 := a.toNat.toUInt256

def Bool.toUInt256 (b : Bool) : UInt256 := if b then 1 else 0

@[simp]
lemma Bool.toUInt256_true : true.toUInt256 = 1
:= rfl

@[simp]
lemma Bool.toUInt256_false : false.toUInt256 = 0
:= rfl

def Clear.UInt256.complement (a : UInt256) : UInt256 := -a - 1

instance : Complement UInt256 := ⟨Clear.UInt256.complement⟩
instance : HMod UInt256 ℕ UInt256 := ⟨Fin.modn⟩
-- instance : HPow UInt256 ℕ UInt256 where
--   hPow a n := (a.1 ^ n : ℕ)
instance : HPow UInt256 UInt256 UInt256 where
  hPow a n := a ^ n.val
instance : DecidableEq UInt256 := instDecidableEqFin UInt256.size

namespace Clear.UInt256

def eq0 (a : UInt256) : Bool := a = 0

def lnot (a : UInt256) : UInt256 := (UInt256.size - 1) - a

def byteAt (a b : UInt256) : UInt256 :=
  b >>> (31 - a) * 8 <<< 248

def sgn (a : UInt256) : UInt256 :=
  if a ≥ 2 ^ 255 then -1
  else if a = 0 then 0 else 1

def abs (a : UInt256) : UInt256 :=
  if a ≥ 2 ^ 255
    then a * (- 1)
    else a

def sdiv (a b : UInt256) : UInt256 :=
  if a ≥ 2 ^ 255 then
    if b ≥ 2 ^ 255 then
      abs a / abs b
    else (abs a / b) * (- 1)
  else
    if b ≥ 2 ^ 255 then
       (a / abs b) * (- 1)
    else a / b

def smod (a b : UInt256) : UInt256 :=
  if a ≥ 2 ^ 255 then
    if b ≥ 2 ^ 255 then
      Fin.mod (abs a) (abs b)
    else (-1) * Fin.mod (abs a) b
  else
    if b ≥ 2 ^ 255 then
      (-1) * Fin.mod a (abs b)
    else Fin.mod a b

def slt (a b : UInt256) : Bool :=
  if a ≥ 2 ^ 255 then
    if b ≥ 2 ^ 255 then
      a < b
    else true
  else
    if b ≥ 2 ^ 255 then false
    else a < b

def sgt (a b : UInt256) : Bool :=
  if a ≥ 2 ^ 255 then
    if b ≥ 2 ^ 255 then
      a > b
    else false
  else
    if b ≥ 2 ^ 255 then true
    else a > b

def sar (a b : UInt256) : UInt256 :=
  if a ≥ 256
    then if b ≥ 0 then 0 else -1
    else Fin.land (Fin.shiftLeft b a) (UInt256.size - 1)

def signextend (a b : UInt256) : UInt256 :=
  if a ≤ 31 then
    let test_bit := a * 8 + 7
    let sign_bit := Fin.shiftLeft 1 test_bit
    if Fin.land b sign_bit ≠ 0 then
      Fin.lor b (UInt256.size - sign_bit)
    else Fin.land b (sign_bit - 1)
  else b

-- | Convert from a list of little-endian bytes to a natural number.
def fromBytes' : List UInt8 → ℕ
| [] => 0
| b :: bs => b.val.val + 2^8 * fromBytes' bs

variable {bs : List UInt8}
         {n : ℕ}

-- | A bound for the natural number value of a list of bytes.
private lemma fromBytes'_le : fromBytes' bs < 2^(8 * bs.length) := by
  induction bs with
  | nil => unfold fromBytes'; simp
  | cons b bs ih =>
    unfold fromBytes'
    have h := b.val.isLt
    simp only [List.length_cons, Nat.mul_succ, Nat.add_comm, Nat.pow_add]
    have ih :=
      Nat.add_le_of_le_sub
        (Nat.one_le_pow _ _ (by decide))
        (Nat.le_sub_one_of_lt ih)
    linarith

-- | The natural number value of a length 32 list of bytes is < 2^256.
private lemma fromBytes'_UInt256_le (h : bs.length = 32) : fromBytes' bs < 2^256 := by
    have h' := @fromBytes'_le bs
    rw [h] at h'
    exact h'

-- | Convert a natural number into a list of bytes.
private def toBytes' : ℕ → List UInt8
  | 0 => []
  | n@(.succ n') =>
    let byte : UInt8 := ⟨Nat.mod n UInt8.size, Nat.mod_lt _ (by linarith)⟩
    have : n / UInt8.size < n' + 1 := by
      rename_i h
      rw [h]
      apply Nat.div_lt_self <;> simp
    byte :: toBytes' (n / UInt8.size)

-- | If n < 2⁸ᵏ, then (toBytes' n).length ≤ k.
private lemma toBytes'_le {k : ℕ} (h : n < 2 ^ (8 * k)) : (toBytes' n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    simp at h
    rw [h]
    simp [toBytes']
  | succ e ih =>
    match n with
    | .zero => simp [toBytes']
    | .succ n =>
      unfold toBytes'
      simp [Nat.succ_le_succ_iff]
      apply ih (Nat.div_lt_of_lt_mul _)
      rw [Nat.mul_succ, Nat.pow_add] at h
      linarith

-- | If n < 2²⁵⁶, then (toBytes' n).length ≤ 32.
private lemma toBytes'_UInt256_le (h : n < UInt256.size) : (toBytes' n).length ≤ 32 := toBytes'_le h

-- | Zero-pad a list of bytes up to some length, adding the zeroes on the right.
private def zeroPadBytes (n : ℕ) (bs : List UInt8) : List UInt8 :=
  bs ++ (List.replicate (n - bs.length)) 0

-- | The length of a `zeroPadBytes` call is its first argument.
lemma zeroPadBytes_len (h : bs.length ≤ n) : (zeroPadBytes n bs).length = n := by
  unfold zeroPadBytes
  aesop

-- | Appending a bunch of zeroes to a little-endian list of bytes doesn't change its value.
@[simp]
private lemma extend_bytes_zero : fromBytes' (bs ++ List.replicate n 0) = fromBytes' bs := by
  induction bs with
  | nil =>
    simp [fromBytes']
    induction n with
    | zero => simp [List.replicate, fromBytes']
    | succ _ ih => simp [List.replicate, fromBytes']; norm_cast
  | cons _ _ ih => simp [fromBytes', ih]

-- | The ℕ value of a little-endian list of bytes is invariant under right zero-padding up to length 32.
@[simp]
private lemma fromBytes'_zeroPadBytes_32_eq : fromBytes' (zeroPadBytes 32 bs) = fromBytes' bs := extend_bytes_zero

-- | Casting a natural number to a list of bytes and back is the identity.
@[simp]
private lemma fromBytes'_toBytes' {x : ℕ} : fromBytes' (toBytes' x) = x := by
  match x with
  | .zero => simp [toBytes', fromBytes']
  | .succ n =>
    unfold toBytes' fromBytes'
    simp only
    have := Nat.div_lt_self (Nat.zero_lt_succ n) (by decide : 1 < UInt8.size)
    rw [fromBytes'_toBytes']
    simp [UInt8.size, add_comm]; norm_num
    apply Nat.div_add_mod

def fromBytes! (bs : List UInt8) : ℕ := fromBytes' (bs.take 32)

private lemma fromBytes_was_good_all_year_long
  (h : bs.length ≤ 32) : fromBytes' bs < 2^256 := by
  have h' := @fromBytes'_le bs
  rw [pow_mul] at h'
  refine lt_of_lt_of_le (b := (2 ^ 8) ^ List.length bs) h' ?lenBs
  case lenBs => rw [←pow_mul]; exact pow_le_pow_right (by decide) (by linarith)

@[simp]
lemma fromBytes_wasnt_naughty : fromBytes! bs < 2^256 := fromBytes_was_good_all_year_long (by simp)

-- Convenience function for spooning into UInt256.
-- Given that I 'accept' UInt8, might as well live with UInt256.
def fromBytes_if_you_really_must? (bs : List UInt8) : UInt256 :=
  ⟨fromBytes! bs, fromBytes_wasnt_naughty⟩

def toBytes! (n : UInt256) : List UInt8 := zeroPadBytes 32 (toBytes' n)

@[simp]
lemma length_toBytes! {n : UInt256} : (toBytes! n).length = 32 := zeroPadBytes_len (toBytes'_UInt256_le n.2)

lemma UInt256_pow_def {a b : UInt256} : a ^ b = a ^ b.val := by
  rfl

lemma UInt256_pow_succ {a b : UInt256} (h : b.val + 1 < UInt256.size) : a * a ^ b = a ^ (b + 1) := by
  rw [UInt256_pow_def, UInt256_pow_def]
  have : (↑(b + 1) : ℕ) = (b + 1 : ℕ) := by rw [Fin.val_add, Nat.mod_eq_of_lt (by norm_cast)]; rfl
  rw [this]
  ring

lemma UInt256_zero_pow {a : UInt256} (h : a.val ≠ 0) : (0 : UInt256) ^ a = 0 := zero_pow h

lemma UInt256_pow_zero {a : UInt256} : a ^ (0 : UInt256) = 1 := by
  unfold HPow.hPow instHPowUInt256
  simp

end Clear.UInt256
