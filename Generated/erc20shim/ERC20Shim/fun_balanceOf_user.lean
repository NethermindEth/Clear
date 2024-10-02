import Clear.ReasoningPrinciple

-- import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.fun_balanceOf_gen

import Generated.erc20shim.ERC20Shim.Predicate

namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_fun_balanceOf (var : Identifier) (var_account : Literal) (s₀ s₉ : State) : Prop :=
  let account := Address.ofUInt256 var_account
  ∀ {erc20 : ERC20}, account ∈ erc20.balances →
  ∀ bal_addr,
  s₀.evm.keccak_map.lookup [ ↑account , ERC20Private.balances ] = some bal_addr →
  erc20.balances.lookup account = some (s₀.evm.sload bal_addr) →
  s₉[var]!! = s₀.evm.sload bal_addr

lemma fun_balanceOf_abs_of_concrete {s₀ s₉ : State} {var var_account} :
  Spec (fun_balanceOf_concrete_of_code.1 var var_account) s₀ s₉ →
  Spec (A_fun_balanceOf var var_account) s₀ s₉ := by
  unfold fun_balanceOf_concrete_of_code A_fun_balanceOf

  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs

  intro hasFuel ⟨s, keccak, prog⟩ erc20 hasBal bal_addr hasAddr loadAddr
  clr_varstore

  unfold A_mapping_index_access_mapping_address_uint256_of_address at keccak
  simp at keccak
  clr_spec at keccak
  
  obtain ⟨preserves, is_ok, lookup⟩ := keccak hasBal bal_addr hasAddr
  obtain ⟨evmₛ, varstareₛ, ok_state⟩ := State_of_isOk is_ok
  rw [lookup, ok_state] at prog
  rw [← prog]
  
  unfold State.lookup!
  simp
  have : sload _ bal_addr = sload s.evm bal_addr := sload_eq_of_preservesEvm (by simp) is_ok preserves
  symm
  rw [ok_state] at this
  simp at this
  exact this

end

end Generated.erc20shim.ERC20Shim
