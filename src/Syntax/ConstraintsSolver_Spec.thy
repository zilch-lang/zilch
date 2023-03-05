theory ConstraintsSolver_Spec
  imports
    Main
    Refine_Monadic.Refine_Monadic
begin

locale Solver_Spec
begin

type_synonym path = string

datatype namespace =
  FileModule path
| At namespace string

datatype constraint =
  Has string namespace

text \<open>

\<close>
type_synonym conjunctive_system = \<open>constraint list\<close>



end (* locale Solver_Spec *)

end (* theory ConstraintsSolver_Spec *)
