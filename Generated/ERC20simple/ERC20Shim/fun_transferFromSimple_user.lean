import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_668760047301878650
import Generated.ERC20simple.ERC20Shim.checked_sub_uint256
import Generated.ERC20simple.ERC20Shim.checked_add_uint256

import Generated.ERC20simple.ERC20Shim.fun_transferFromSimple_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def A_fun_transferFromSimple (var var_1 var_2 : Identifier) (var_from var_to var_value : Literal) (s₀ s₉ : State) : Prop := sorry

set_option maxHeartbeats 400000 in
lemma fun_transferFromSimple_abs_of_concrete {s₀ s₉ : State} {var var_1 var_2 var_from var_to var_value} :
  Spec (fun_transferFromSimple_concrete_of_code.1 var var_1 var_2 var_from var_to var_value) s₀ s₉ →
  Spec (A_fun_transferFromSimple var var_1 var_2 var_from var_to var_value) s₀ s₉ := by
  unfold fun_transferFromSimple_concrete_of_code A_fun_transferFromSimple
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  rintro h ⟨h₁, ⟨ss, h₂⟩⟩
  clr_funargs at ss
  clr_varstore ss,
  rcases h₂ with ⟨w₂, ⟨hw₂, hw₃⟩⟩
  -- clr_spec at ss
  -- clr_spec at hw₂
  apply Spec_ok_unfold at hw₂
  apply Spec_ok_unfold at ss
  unfold A_if_5295847412656974480 at ss
  clr_varstore ss,
  by_cases eq : (decide (var_from < var_value)).toUInt256 = 0
  simp [eq] at ss
  have hss : State.isOk h₁ := by aesop
  clr_varstore hw₂,
  clr_varstore hw₃,

  -- rw [←ss] at hw₂
  -- clr_varstore ss,

  
  
  -- clr_varstore hw₂,
  -- apply Spec_ok_unfold at hw₂

  -- -- clr_varstore
  -- clr_spec at ss
  -- clr_varstore
  -- rcases h₂ with ⟨h₃, ⟨h₄, h₅⟩⟩
  -- clr_spec at h₅
  
  sorry

end

end Generated.ERC20simple.ERC20Shim
