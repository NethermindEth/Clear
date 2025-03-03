import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun_msgSender
import Generated.erc20shim.ERC20Shim.fun__transfer

import Generated.erc20shim.ERC20Shim.fun_transfer_gen

namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_fun_transfer (var : Identifier) (var_to var_value : Literal) (s₀ s₉ : State) : Prop :=
  let recipient := Address.ofUInt256 var_to
  let amount : UInt256 := var_value
  let sender := s₀.evm.execution_env.source
  (
    ∀ {erc20}, (IsERC20 erc20 s₀ ∧ s₀.evm.isEVMState ∧ s₀.evm.reverted = false) →
  -- Transfer succeeds
    (
      let balances := update_balances erc20 sender recipient amount
      IsERC20 ({ erc20 with balances }) s₉ ∧
      preservesEvm s₀ s₉ ∧
      s₉.evm.hash_collision = false ∧
      s₉[var]!! = 1 ∧
      s₉.evm.reverted = false
    )
    ∨
  -- Transfer Fails
    (
      IsERC20 erc20 s₉ ∧
      preservesEvm s₀ s₉ ∧
      s₉.evm.hash_collision = false ∧
      s₉[var]!! = 0 ∧
      s₉.evm.reverted = true ∧
      (recipient.1 = 0 ∨ balanceOf s₀.evm sender < amount)
    )
    -- Hash Collision
    ∨ s₉.evm.hash_collision = true
  )

-- set_option pp.notation false in

set_option maxHeartbeats 1000000

lemma fun_transfer_abs_of_concrete {s₀ s₉ : State} {var var_to var_value} :
  Spec (fun_transfer_concrete_of_code.1 var var_to var_value) s₀ s₉ →
  Spec (A_fun_transfer var var_to var_value) s₀ s₉ := by

  -- Unfold the definitions of the abstract and concrete specifications
  unfold fun_transfer_concrete_of_code A_fun_transfer
  -- Notice we now have two Specs in the tactic state - one for each specification

  -- Split s₀ into the 3 cases of OK, OutOfFuel, and Checkpoint
  -- Immediately prove the latter cases with simp and aesop
  -- Assign the initial state s₀
  rcases s₀ with ⟨s0_evm, s0_varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]

  -- applies the Spec
  apply spec_eq

  -- Unfolds initcall and setStore
  clr_funargs

  -- Assign s_inhabited state to tidy up goal
  --set s_inhabited := (Ok s0_evm Inhabited.default⟦"var_value"↦var_value⟧⟦"var_to"↦var_to⟧) with eq1
  generalize s_inhabited_all : (Ok s0_evm Inhabited.default⟦"var_value"↦var_value⟧⟦"var_to"↦var_to⟧) = s_inhabited at *
  -- Show state is Ok
  have s_inhabited_ok : s_inhabited.isOk := by
    aesop_spec

  -- s₀ --> s using call_msgSender
  -- s --> s' using call_transfer
  -- s' --> s₉ using code
  rintro hasFuel ⟨s, call_msgSender, ⟨s', call_transfer, code⟩⟩

  -- Introduce hypotheses for s₀
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

  · -- No hash collision at state s

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
    have s_isERC20 : IsERC20 erc_20 s := IsERC20_of_preservesEvm s0_s_preservesEvm s0_isERC20
    have isEvmState_s : isEVMState s.evm := by aesop

    /-
    unfold A_fun__transfer at call_transfer
    -- clr_spec at call_transfer
    apply Spec_ok_unfold (by aesop_spec) at call_transfer

    swap

    · rcases s' with _ | _ | ⟨checkpoint'⟩
      · simp
      · simp at *; rw [←code] at hasFuel; simp at hasFuel
      · simp at *
    ·
      dsimp at call_transfer
      rcases call_transfer with ⟨s'_ok, transfer_right⟩

      obtain ⟨s'_evm, ⟨s'_varstore, s'_all⟩⟩ := State_of_isOk s'_ok

      have s9_ok : s₉.isOk := by
        aesop

      unfold reviveJump at code
      simp [s'_all, ←s0_all] at code
      rw [← State.insert_of_ok] at code

      have s9_preserved : Preserved s'_evm s'_evm := by aesop
      have s9_preservesEvm : preservesEvm s' s₉ := by
        rw [s'_all, ←code]
        apply s9_preserved

      have s_values : s₀.evm.execution_env.source = Address.ofUInt256 (s["_1"]!!) ∧
                      var_value = s["var_value"]!! ∧
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
        · simp
          rw [Finmap.lookup_insert_of_ne _ (by unfold Ne; apply String.ne_of_data_ne; simp)
                , Finmap.lookup_insert_of_ne _ (by unfold Ne; apply String.ne_of_data_ne; simp)]
          simp
        · simp
          rw [Finmap.lookup_insert_of_ne _ (by unfold Ne; apply String.ne_of_data_ne; simp)]
          simp

      specialize transfer_right ⟨s_isERC20, isEvmState_s, s_not_reverted⟩

      obtain ⟨s'_erc20, s'_preservesEvm, s'_not_reverted, s'_no_collision⟩
              | ⟨s'_erc20, s'_preservesEvm, s'_no_collision, addr_balance_error, s'_reverted⟩
              | s'_collision
              := transfer_right

      · -- Transfer success case
        left

        refine' ⟨?_ ,?_, (by aesop), ?_, (by aesop)⟩

        · apply IsERC20_of_preservesEvm s9_preservesEvm
          rw [←s_values.1, ←s_values.2.1, ←s_values.2.2] at s'_erc20
          exact s'_erc20

        · apply Utilities.preservesEvm_trans s_ok
          · aesop
          · aesop

        · rw [←code]
          simp
          unfold State.insert at code
          unfold lookup!
          simp

      · -- Transfer fail case
        right
        left

        refine' ⟨?_, ?_, (by aesop), ?_, (by aesop), ?_⟩

        · apply IsERC20_of_preservesEvm s9_preservesEvm
          exact s'_erc20

        · apply Utilities.preservesEvm_trans s_ok
          · aesop
          · aesop

        · -- USED EGREGIOUS HACK THIS IS NOT CORRECT *******************************************************
          have := EGREGIOUS_HACK_REVERTED s₀ s₉ s'_reverted
          aesop

        · obtain zero_addr | no_balance := addr_balance_error
          · rw[←s_values.2.2] at zero_addr
            rw[zero_addr]
            left
            rfl
          · rw[←s_values.1, ←s_values.2.1] at no_balance
            right
            unfold balanceOf
            unfold balanceOf at no_balance
            have account_map_preservation := (preservesEvm_of_isOk s0_ok s_ok s0_s_preservesEvm).1
            rw [account_map_preservation]
            exact no_balance

      · -- Hash Collision Case
        aesop

      -/


    unfold A_fun__transfer at call_transfer
    clr_spec at call_transfer

    dsimp at call_transfer
    rcases call_transfer with ⟨s'_ok, transfer_right⟩

    obtain ⟨s'_evm, ⟨s'_varstore, s'_all⟩⟩ := State_of_isOk s'_ok

    have s9_ok : s₉.isOk := by
      aesop

    unfold reviveJump at code
    simp [s'_all, ←s0_all] at code
    rw [← State.insert_of_ok] at code

    have s9_preserved : Preserved s'_evm s'_evm := by aesop
    have s9_preservesEvm : preservesEvm s' s₉ := by
        rw [s'_all, ←code]
        apply s9_preserved

    have s_values : s₀.evm.execution_env.source = Address.ofUInt256 (s["_1"]!!) ∧
                      var_value = s["var_value"]!! ∧
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
        · simp
          rw [Finmap.lookup_insert_of_ne _ (by unfold Ne; apply String.ne_of_data_ne; simp)
                , Finmap.lookup_insert_of_ne _ (by unfold Ne; apply String.ne_of_data_ne; simp)]
          simp
        · simp
          rw [Finmap.lookup_insert_of_ne _ (by unfold Ne; apply String.ne_of_data_ne; simp)]
          simp

    specialize transfer_right ⟨s_isERC20, isEvmState_s, s_not_reverted⟩

    obtain ⟨s'_erc20, s'_preservesEvm, s'_not_reverted, s'_no_collision⟩
              | ⟨s'_erc20, s'_preservesEvm, s'_no_collision, addr_balance_error, s'_reverted⟩
              | s'_collision
              := transfer_right

    · -- Transfer success case
      left

      refine' ⟨?_ ,?_, (by aesop), ?_, (by aesop)⟩

      · apply IsERC20_of_preservesEvm s9_preservesEvm
        rw [←s_values.1, ←s_values.2.1, ←s_values.2.2] at s'_erc20
        exact s'_erc20

      · apply Utilities.preservesEvm_trans s_ok
        · aesop
        · aesop

      · rw [←code]
        simp
        unfold State.insert at code
        unfold lookup!
        simp

    · -- Transfer fail case
      right
      left

      refine' ⟨?_, ?_, (by aesop), ?_, (by aesop), ?_⟩

      · apply IsERC20_of_preservesEvm s9_preservesEvm
        exact s'_erc20

      · apply Utilities.preservesEvm_trans s_ok
        · aesop
        · aesop

      · -- USED EGREGIOUS HACK THIS IS NOT CORRECT ***************************************************
        have := EGREGIOUS_HACK_REVERTED s₀ s₉ s'_reverted
        aesop

      · obtain zero_addr | no_balance := addr_balance_error
        · rw[←s_values.2.2] at zero_addr
          rw[zero_addr]
          left
          rfl
        · rw[←s_values.1, ←s_values.2.1] at no_balance
          right
          unfold balanceOf
          unfold balanceOf at no_balance
          have account_map_preservation := (preservesEvm_of_isOk s0_ok s_ok s0_s_preservesEvm).1
          rw [account_map_preservation]
          exact no_balance

  · right
    right
    rename_i s_collision

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
    have s_isERC20 : IsERC20 erc_20 s := IsERC20_of_preservesEvm s0_s_preservesEvm s0_isERC20
    have isEvmState_s : isEVMState s.evm := by aesop

    unfold A_fun__transfer at call_transfer
    clr_spec at call_transfer

    simp at call_transfer
    rcases call_transfer with ⟨s'_ok, transfer_right⟩

    obtain ⟨s'_evm, ⟨s'_varstore, s'_all⟩⟩ := State_of_isOk s'_ok

    have s9_ok : s₉.isOk := by
      aesop

    unfold reviveJump at code
    simp [s'_all, ←s0_all] at code
    rw [← State.insert_of_ok] at code

    have s9_preserved : Preserved s'_evm s'_evm := by aesop
    have s9_preservesEvm : preservesEvm s' s₉ := by
      rw [s'_all, ←code]
      apply s9_preserved

    specialize transfer_right s_isERC20 isEvmState_s s_not_reverted

    obtain ⟨s'_erc20, s'_preservesEvm, s'_not_reverted, s'_no_collision⟩
              | ⟨s'_erc20, s'_preservesEvm, s'_no_collision, addr_balance_error, s'_reverted⟩
              | s'_collision
              := transfer_right

    · rw [←code]
      simp
      have : s.evm.hash_collision = true → s'.evm.hash_collision = true := by
        have account_map_preservation := (preservesEvm_of_isOk s_ok s'_ok s'_preservesEvm).2.1
        aesop
      aesop

    · rw [←code]
      simp
      have : s.evm.hash_collision = true → s'.evm.hash_collision = true := by
        have account_map_preservation := (preservesEvm_of_isOk s_ok s'_ok s'_preservesEvm).2.1
        aesop
      aesop

    · aesop

end

end Generated.erc20shim.ERC20Shim
