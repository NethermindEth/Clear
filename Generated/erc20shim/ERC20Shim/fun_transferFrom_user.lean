import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun_msgSender
import Generated.erc20shim.ERC20Shim.fun_spendAllowance
import Generated.erc20shim.ERC20Shim.fun__transfer

import Generated.erc20shim.ERC20Shim.fun_transferFrom_gen


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
      let balances :=
        if from_addr = to_addr then erc20.balances
          else
            Finmap.insert
              to_addr
              (((erc20.balances.lookup to_addr).getD 0) + transfer_value)
              (
                Finmap.insert
                  from_addr
                  (((erc20.balances.lookup from_addr).getD 0) - transfer_value)
                  erc20.balances
              )
      let allowances :=
        let currentAllowance := (erc20.allowances.lookup (from_addr, s₀.evm.execution_env.source)).getD 0
        if currentAllowance = UInt256.top then erc20.allowances else
        Finmap.insert
          (from_addr, s₀.evm.execution_env.source)
          (currentAllowance - transfer_value)
          erc20.allowances
      IsERC20 ({ erc20 with balances, allowances }) s₉ ∧ preservesEvm s₀ s₉ ∧
      s₉[var]!! = 1 ∧
      s₉.evm.hash_collision = false
    )
    ∨
    -- Case: transferFrom fails
    (
      IsERC20 erc20 s₉ ∧ preservesEvm s₀ s₉ ∧
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
