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
  let from_addr := Address.ofUInt256 var_from
  let to_addr := Address.ofUInt256 var_to
  let transfer_value : UInt256 := var_value -- in wei
  (
    ∀ {erc20}, (IsERC20 erc20 s₀ ∧ s₀.evm.isEVMState) →
    -- Case: transferFrom succeeds
    (
      let balances := update_balances erc20 from_addr to_addr transfer_value
      let allowances := update_allowances erc20 from_addr s₀.evm.execution_env.source transfer_value
      IsERC20 ({ erc20 with balances, allowances }) s₉ ∧ preservesEvm s₀ s₉ ∧
      s₉[var]!! = 1 ∧
      s₉.evm.hash_collision = false
    )
    ∨
    -- Case: transferFrom fails
    (
      IsERC20 erc20 s₉ ∧ preservesEvm s₀ s₉ ∧ s₉.evm.hash_collision = false ∧
      s₉[var]!! = 0
    )
    -- Case: Hash collision
    ∨ s₉.evm.hash_collision = true
  )


lemma fun_transferFrom_abs_of_concrete {s₀ s₉ : State} {var var_from var_to var_value} :
  Spec (fun_transferFrom_concrete_of_code.1 var var_from var_to var_value) s₀ s₉ →
  Spec (A_fun_transferFrom var var_from var_to var_value) s₀ s₉ := by
  unfold fun_transferFrom_concrete_of_code A_fun_transferFrom
  sorry

end

end Generated.erc20shim.ERC20Shim
