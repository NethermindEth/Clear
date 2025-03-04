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

set_option maxHeartbeats 1000000

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

  · -- No collision at s

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

    unfold A_fun_spendAllowance at call_spendAllowance
    clr_spec at call_spendAllowance


  · -- collision at s
    rename_i s_collision





end

end Generated.erc20shim.ERC20Shim
