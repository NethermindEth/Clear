import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun_msgSender
import Generated.erc20shim.ERC20Shim.fun_spendAllowance
import Generated.erc20shim.ERC20Shim.fun__transfer

import Generated.erc20shim.ERC20Shim.fun_transferFrom_gen

import Generated.erc20shim.ERC20Shim.Predicate

namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_fun_transferFrom (var : Identifier) (var_from var_to var_value : Literal) (s₀ s₉ : State) : Prop :=
  let sender := Address.ofUInt256 var_from
  let recipient := Address.ofUInt256 var_to
  let amount : UInt256 := var_value -- in wei
  (
    ∀ {erc20}, (IsERC20 erc20 s₀ ∧ s₀.evm.isEVMState ∧ s₀.evm.reverted = false) →
    -- Case: transferFrom succeeds
    (
      let balances := update_balances erc20 sender recipient amount
      let allowances := update_allowances erc20 sender s₀.evm.execution_env.source amount
      IsERC20 ({ erc20 with balances, allowances }) s₉ ∧
      preservesEvm s₀ s₉ ∧
      s₉.evm.hash_collision = false ∧
      s₉[var]!! = 1 ∧
      s₉.evm.reverted = false

    )
    ∨
    -- Case: transferFrom fails
    (
      let currentAllowance := (erc20.allowances.lookup (sender, s₀.evm.execution_env.source)).getD 0
      IsERC20 erc20 s₉ ∧
      preservesEvm s₀ s₉ ∧
      s₉.evm.hash_collision = false ∧
      s₉[var]!! = 0 ∧
      s₉.evm.reverted = true ∧
      (recipient.1 = 0 ∨
      sender.1 = 0 ∨
      balanceOf s₀.evm sender < amount ∨
      currentAllowance < amount)
    )
    -- Case: Hash collision
    ∨ s₉.evm.hash_collision = true
  )

set_option maxHeartbeats 1500000

lemma fun_transferFrom_abs_of_concrete {s₀ s₉ : State} {var var_from var_to var_value} :
  Spec (fun_transferFrom_concrete_of_code.1 var var_from var_to var_value) s₀ s₉ →
  Spec (A_fun_transferFrom var var_from var_to var_value) s₀ s₉ := by

  unfold fun_transferFrom_concrete_of_code A_fun_transferFrom

  -- Split s₀ into the 3 cases of OK, OutOfFuel, and Checkpoint
  -- Immediately prove the latter cases with simp and aesop
  -- Assign the initial state s₀
  rcases s₀ with ⟨s0_evm, s0_varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]

  -- applies the Spec
  apply spec_eq

  -- Unfolds initcall and setStore
  clr_funargs

  generalize s_inhabited_all : (Ok s0_evm Inhabited.default⟦"var_value"↦var_value⟧⟦"var_to"↦var_to⟧⟦"var_from"↦var_from⟧) = s_inhabited at *
  have s_inhabited_ok : s_inhabited.isOk := by
    aesop_spec

  -- s₀ --> s using call_msgSender
  -- s --> s' using call_spendAllowance
  -- s' --> s'' using call_transfer
  -- s' --> s₉ using code
  rintro hasFuel ⟨s, call_msgSender, ⟨s', call_spendAllowance, ⟨s'', call_transfer, code⟩⟩⟩

  intro erc_20 s0_isERC20 evmState s0_notReverted

  -- Assign s₀ state to tidy up goal
  generalize s0_all : Ok s0_evm s0_varstore = s₀ at *
  have s0_ok : s₀.isOk := by
    aesop

  have s_inhabited_not_reverted : s_inhabited.evm.reverted = false := by
    aesop

  -- Clear specs at call_msgSender
  unfold A_fun_msgSender at call_msgSender
  clr_spec at call_msgSender
  rw[←s_inhabited_all] at call_msgSender

  obtain ⟨s_preservesEvm,
          ⟨s_ok, s_preserve_evmState, s_preserve_collision,
          ⟨⟨s_source, s_collision_false⟩⟩⟩⟩ := call_msgSender

  · -- No collision at msgSender

    -- Combine state s in s_all
    obtain ⟨s_evm, ⟨s_varstore, s_all⟩⟩ := State_of_isOk s_ok

    have s_not_reverted : s.evm.reverted = false := by
      rw [s_inhabited_all] at s_preservesEvm
      have eq := preservesEvm_of_isOk s_inhabited_ok s_ok s_preservesEvm
      rw [←eq.2.2.2.1]
      exact s_inhabited_not_reverted

    rw [preservesEvm_of_insert, preservesEvm_of_insert, s_all] at s_preservesEvm

    -- Obtain hypotheses for state s from state s₀
    have s0_s_preservesEvm : preservesEvm s₀ s := by aesop (add simp preservesEvm)
    have s_erc20 : IsERC20 erc_20 s := IsERC20_of_preservesEvm s0_s_preservesEvm s0_isERC20
    have s_isEvmState : isEVMState s.evm := by aesop

    unfold A_fun_spendAllowance at call_spendAllowance
    clr_spec at call_spendAllowance

    unfold A_fun__transfer at call_transfer
    clr_spec at call_transfer

    dsimp at call_spendAllowance
    rcases call_spendAllowance with ⟨s'_ok, s'_isEVMState, spendAllowance_right, s'_pres_collision⟩
    obtain ⟨s'_evm, ⟨s'_varstore, s'_all⟩⟩ := State_of_isOk s'_ok

    dsimp at call_transfer
    rcases call_transfer with ⟨s''_ok, transfer_right, s''_pres_collision⟩
    obtain ⟨s''_evm, ⟨s''_varstore, s''_all⟩⟩ := State_of_isOk s''_ok

    have s9_ok : s₉.isOk := by
      aesop

    unfold reviveJump at code
    simp [s''_all, ←s0_all] at code
    rw [← State.insert_of_ok] at code

    have : Preserved s''_evm s''_evm := by aesop
    have s9_preservesEvm : preservesEvm s'' s₉ := by
        rw [s''_all, ←code]
        apply this

    have s_values : s₀.evm.execution_env.source = Address.ofUInt256 (s["_1"]!!) ∧
                      var_value = s["var_value"]!! ∧
                      var_from = s["var_from"]!! ∧
                      var_to = s["var_to"]!! := by
        rw [s_all]
        rw [s_all] at s_source
        unfold store at s_source
        unfold State.insert at s_source
        simp at s_source
        rw [s_source]
        unfold lookup!
        split_ands
        · simp [←s0_all, Address.ofUInt256]
          generalize eq₁ : s0_evm.execution_env.source = x
          rw [
          Nat.mod_eq_of_lt (by rw [Nat.mod_eq_of_lt (Fin.val_lt_of_le _ (by decide))]; omega),
          Nat.mod_eq_of_lt (Fin.val_lt_of_le _ (by decide))
            ]
          rcases x with ⟨x, hx⟩
          simp [Fin.ofNat]
          unfold Address.size at hx
          omega
        · aesop
        · aesop
        · aesop

    rw[←s_values.1, ←s_values.2.1, ←s_values.2.2.1] at spendAllowance_right

    specialize spendAllowance_right ⟨s_erc20, s_isEvmState, s_not_reverted⟩

    obtain ⟨s'_erc20, s'_preservesEvm, s'_no_collision, s'_not_reverted, s'_source⟩
              | ⟨s'_erc20, s'_preservesEvm, s'_no_collision, s'_reverted, allowance_error⟩
              | s'_collision
              := spendAllowance_right

    · -- spendAllowance success

      have isEvmState_s' : isEVMState s'.evm := by
        aesop

      have s'_values : var_to = s'["var_to"]!! ∧
                      var_value = s'["var_value"]!! ∧
                      var_from = s'["var_from"]!! := by
        rw [s'_all] at s'_source
        rw [s_all] at s'_source
        unfold store at s'_source
        aesop

      specialize transfer_right ⟨s'_erc20, isEvmState_s', s'_not_reverted⟩

      obtain ⟨s''_erc20, s''_preservesEvm, s''_not_reverted,  s''_no_collision⟩
              | ⟨s''_erc20, s''_preservesEvm, s''_no_collision, allowance_error, s''_reverted⟩
              | s''_collision
              := transfer_right

      · -- transfer success
        left

        refine' ⟨?_ ,?_, (by aesop), ?_, (by aesop)⟩

        · apply IsERC20_of_preservesEvm s9_preservesEvm
          aesop

        · apply Utilities.preservesEvm_trans s_ok
          · aesop
          · apply Utilities.preservesEvm_trans s'_ok
            · aesop
            · aesop

        · rw [←code]
          simp
          unfold State.insert at code
          unfold lookup!
          simp

      · -- transfer fail

        right
        left

        refine' ⟨?_, ?_, (by aesop), ?_, (by aesop), ?_⟩

        · apply IsERC20_of_preservesEvm s9_preservesEvm
          apply IsERC20_of_preservesEvm s''_preservesEvm
          apply IsERC20_of_preservesEvm s'_preservesEvm
          aesop

        · apply Utilities.preservesEvm_trans s_ok
          · aesop
          · apply Utilities.preservesEvm_trans s'_ok
            · aesop
            · aesop

        · -- HACK USED THIS IS NOT CORRECT ***********************************************************
          have := EGREGIOUS_HACK_REVERTED s_inhabited s₉ s''_reverted
          rw [←s_inhabited_all] at this
          rw [←this]
          subst s_all code s0_all s'_all s_inhabited_all
          simp_all only [isOk_Ok, isOutOfFuel_Ok, not_false_eq_true, Preserved.refl, evm_insert, get_evm_of_ok,
          Fin.isValue, isOutOfFuel_insert', isOk_insert, Bool.false_eq_true]

        · rw [←s'_values.1, ←s'_values.2.1, ←s'_values.2.2] at allowance_error
          obtain zero_addr | balance_error := allowance_error
          · aesop
          · right
            right
            left
            unfold balanceOf
            unfold balanceOf at balance_error
            have s0_s'_preservesEvm : preservesEvm s₀ s' := by
              apply Utilities.preservesEvm_trans s_ok
              · aesop
              · aesop
            have := (preservesEvm_of_isOk s0_ok s'_ok s0_s'_preservesEvm).1
            rw[this]
            exact balance_error

      · -- collision at s''
        right
        right
        aesop

    · -- spendAllowance fail

      -- surely is spendAllowancefails then transfer is never called?
      -- need to make changes to how reversion works for this

      sorry

    · --collision in spendAllowance
      aesop

  · -- collision at msgSender

    rename_i s_collision

    right
    right

    unfold A_fun_spendAllowance at call_spendAllowance
    clr_spec at call_spendAllowance
    unfold A_fun__transfer at call_transfer
    clr_spec at call_transfer

    dsimp at call_transfer
    rcases call_transfer with ⟨s''_ok, transfer_right, s''_pres_collision⟩
    obtain ⟨s''_evm, ⟨s''_varstore, s''_all⟩⟩ := State_of_isOk s''_ok

    aesop

end

end Generated.erc20shim.ERC20Shim
