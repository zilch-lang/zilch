theory AST
  imports
    Main

    Located.At
begin

datatype implicitness =
  Implicit
| Explicit

datatype expr =
  Identifier \<open>String.literal located\<close>
| Integer
    \<open>String.literal located\<close>
    \<open>expr located option\<close>
| ProductType
    \<open>parameter located\<close>
    \<open>expr located\<close>
| Lambda
    \<open>parameter located\<close>
    \<open>expr located\<close>
| MultiplicativeSigmaType
    \<open>parameter located\<close>
    \<open>expr located\<close>
| AdditiveSigmaType
    \<open>parameter located\<close>
    \<open>expr located\<close>
| MultiplicativeUnitType
| MultiplicativeUnit
| Local
    \<open>def' located\<close>
    \<open>expr located\<close>
| Application
    \<open>expr located\<close>
    implicitness
    \<open>expr located\<close>
| Hole

and def' =
  Let
    bool
    \<open>String.literal located\<close>
    \<open>expr located\<close>
    \<open>expr located\<close>

and parameter =
  Parameter
    implicitness
    \<open>expr located\<close>
    \<open>String.literal located\<close>
    \<open>expr located\<close>

datatype toplevel =
  Binding bool \<open>tldef' located\<close>

and tldef' =
  Mutual \<open>toplevel located list\<close>
| Val
    \<open>expr located option\<close>
    \<open>String.literal located\<close>
    \<open>expr located option\<close>
| Bind
    \<open>def' located\<close>

datatype module =
  Mod \<open>toplevel located list\<close>

(**********************************************************)

hide_type (open) implicitness expr def' tldef' toplevel module parameter
hide_const (open) Implicit Explicit Hole Identifier Integer ProductType Lambda
                  MultiplicativeSigmaType AdditiveSigmaType MultiplicativeUnitType
                  MultiplicativeUnit Local Local Application Mutual Val Bind Binding Mod

end
