import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_2792370840247009933
import Generated.erc20shim.ERC20Shim.panic_error_0x11

import Generated.erc20shim.ERC20Shim.checked_add_uint256_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def A_checked_add_uint256 (sum : Identifier) (x y : Literal) (s₀ s₉ : State) : Prop :=
  s₉.isOk ∧

  (--Case 1: No initial collision
    s₀.evm.hash_collision = false →
  (
    ( -- Case 1.1 : Reversion
      preservesEvm s₀ s₉ ∧
      s₉.evm.reverted = true ∧
      x > s₉[sum]!! ∧
      s₉.evm.hash_collision = false
    )
    ∨
    ( -- Case 1.2 : No Reversion
      preservesEvm s₀ s₉ ∧
      x ≤ s₉[sum]!! ∧
      s₉.evm.hash_collision = false
    )
    ∨
      -- Case 1.3 : Collision in function
      s₉.evm.hash_collision = true
  )
  )
  ∧
  (-- Case 2: existing initial collision
     s₀.evm.hash_collision = true →
    s₉.evm.hash_collision = true
  )

set_option maxHeartbeats 1000000

lemma checked_add_uint256_abs_of_concrete {s₀ s₉ : State} {sum x y} :
  Spec (checked_add_uint256_concrete_of_code.1 sum x y) s₀ s₉ →
  Spec (A_checked_add_uint256 sum x y) s₀ s₉ := by

  unfold checked_add_uint256_concrete_of_code A_checked_add_uint256
  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  clr_varstore,
  rintro hasFuel ⟨s, call_if, code⟩

  generalize sinhab_all :
  (Ok evm₀ Inhabited.default⟦"y"↦y⟧⟦"x"↦x⟧⟦"x"↦x⟧⟦"y"↦y⟧⟦"sum"↦x + y⟧⟦"_1"↦(decide (x + y < x)).toUInt256⟧)
  = sinhab at *

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *

  have s0_sinhab_preservesEvm : preservesEvm s₀ sinhab := by
    unfold preservesEvm
    simp [←s0_all, ←sinhab_all]
    unfold State.insert
    simp

  unfold A_if_2792370840247009933 at call_if
  clr_spec at call_if

  obtain ⟨s_ok, s_no_collision, s_collision⟩ := call_if

  obtain ⟨s_evm, ⟨s_varstore, s_all⟩⟩ := State_of_isOk s_ok

  unfold reviveJump at code
  simp [←s0_all, s_all] at code

  by_cases collision_s0 : s₀.evm.hash_collision = false

  · -- no collision at s₀
    have : sinhab.evm.hash_collision = false := by aesop
    simp[this] at s_no_collision

    obtain ⟨sinhab_s_preservesEvm, mstore, reversion, store_eq, s_no_collision⟩ |
            ⟨sinhab_s_preservesEvm, reversion, s_store, s_no_collision⟩ |
            collision_s := s_no_collision
    · -- Reverted
      have : ¬sinhab["_1"]!! = 0 → (decide (x + y < x)).toUInt256 ≠ 0 := by
        simp
        unfold lookup!
        simp[←sinhab_all]
        unfold State.insert
        simp

      have : (decide (x + y < x)).toUInt256 ≠ 0 → x + y < x := by
        unfold Bool.toUInt256
        simp

      split_ands
      · aesop
      · simp[collision_s0]
        left
        split_ands
        · aesop
        · aesop
        · unfold lookup!
          simp[←code]
          unfold lookup!
          simp
          unfold State.insert at sinhab_all
          simp at sinhab_all
          have : s_varstore = (Finmap.insert "_1" (decide (x + y < x)).toUInt256
                                (Finmap.insert "sum" (x + y)
                                  (Finmap.insert "y" y (Finmap.insert "x" x (Finmap.insert "y" y Inhabited.default))))) := by aesop
          simp[this]
          aesop
        · aesop
      · aesop
    · -- Not Reverted

      have h1 : sinhab["_1"]!! = 0 → (decide (x + y < x)).toUInt256 = 0 := by
        simp
        unfold lookup!
        simp[←sinhab_all]
        unfold State.insert
        simp

      have h2 : (decide (x + y < x)).toUInt256 = 0 → x ≤ x + y := by
        unfold Bool.toUInt256
        simp

      split_ands
      · aesop
      · simp[collision_s0]
        right
        left
        split_ands
        · aesop
        · rw[←code]
          unfold lookup!
          simp
          unfold State.insert at sinhab_all
          simp at sinhab_all
          have : s_varstore = (Finmap.insert "_1" (decide (x + y < x)).toUInt256
                                (Finmap.insert "sum" (x + y)
                                  (Finmap.insert "y" y (Finmap.insert "x" x (Finmap.insert "y" y Inhabited.default))))) := by aesop
          simp[this]
          have : x ≤ x + y := by aesop
          aesop
        · aesop
      · aesop
    · aesop
  · aesop

end

end Generated.erc20shim.ERC20Shim
