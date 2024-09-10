import Clear.ReasoningPrinciple

-- import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.fun_balanceOf_gen

import Generated.erc20shim.ERC20Shim.Predicate

namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_fun_balanceOf (var : Identifier) (var_account : Literal) (s₀ s₉ : State) : Prop :=
  ∀ erc20, balance_predicate erc20 s₀ → balance_predicate erc20 s₉

  -- ∃ (s : State) (addr : UInt256), (s₉ = s⟦ var ↦ s.evm.sload addr ⟧)

lemma fun_balanceOf_abs_of_concrete {s₀ s₉ : State} {var var_account} :
  Spec (fun_balanceOf_concrete_of_code.1 var var_account) s₀ s₉ →
  Spec (A_fun_balanceOf var var_account) s₀ s₉ := by
  unfold fun_balanceOf_concrete_of_code A_fun_balanceOf  
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs

  intro hasFuel index_access erc20 pred_s₀

  rcases index_access with ⟨sₖ, mapping, h'⟩
  -- clr_spec at mapping

  -- have sₖ_isOk : isOk sₖ := mapping_of_ok mapping (by simp)
  -- rcases sₖ with ⟨evmₖ, _⟩ | _ | _ <;> try contradiction
  -- use (Ok evmₖ varstore)

  -- simp at *
  -- rw [ ← State.insert_of_ok, ← State.insert_of_ok
  --    , State.lookup_insert
  --    ] at h'
  -- symm at h'

  -- by_cases h : evmₖ.hash_collision = true
  -- · use 0
  --   rw [ lookup_addr_fail mapping h] at h'
  --   assumption
  -- · rcases lookup_addr_ok mapping (by aesop) with ⟨addr, lookup_eq_addr⟩
  --   use addr
  --   rw [ lookup_eq_addr ] at h'
  --   assumption

end

end Generated.erc20shim.ERC20Shim
