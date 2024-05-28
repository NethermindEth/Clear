import Mathlib.Data.List.AList

import Clear.UInt256
import Clear.Ast
import Clear.YulNotation

namespace Clear.User

namespace Def

open Clear.Ast (FunctionDefinition)
open YulNotation

def test : FunctionDefinition := <f
function test(a) -> x
{x := 10
 leave}
>

def test1 : FunctionDefinition := <f
function test1(a, b) -> x, y
{
    let x := test(12)
    leave
}
>

@[simp]
def mapping : AList (fun (_ : String) => FunctionDefinition)
:= [ ⟨"test", test⟩
   , ⟨"test1", test1⟩
   ].toAList

@[simp]
def find : String → Option FunctionDefinition := mapping.lookup

end Def

end Clear.User
