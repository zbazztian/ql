/**
 * @name Errors When Double Free
 * @description Freeing a previously allocated resource twice can lead to various vulnerabilities in the program.
 * @kind problem
 * @id cpp/double-free
 * @problem.severity warning
 * @precision medium
 * @tags security
 *       external/cwe/cwe-415
 */

import cpp

// Holds if there is a path from c1 to c2 without going through barrier. Going either
// into or out of barrier is permitted, but not both.
predicate notVia(ControlFlowNode c1, ControlFlowNode c2, ControlFlowNode barrier) {
  c1.getASuccessor() = c2
  or
  exists(ControlFlowNode s | s = c1.getASuccessor() | s != barrier and notVia(s, c2, barrier))
}

predicate between(ControlFlowNode a, ControlFlowNode mid, ControlFlowNode b) {
  notVia(a, mid, b) and notVia(mid, b, a)
}

from FunctionCall fc, FunctionCall fc2, LocalScopeVariable v
where
  freeCall(fc, v.getAnAccess()) and
  freeCall(fc2, v.getAnAccess()) and
  fc.getASuccessor+() = fc2 and
  not exists(Expr exptmp |
    (exptmp = v.getAnAssignedValue() or exptmp.(AddressOfExpr).getOperand() = v.getAnAccess()) and
    between(fc, exptmp, fc2)
  ) and
  not exists(FunctionCall fctmp |
    not fctmp instanceof DeallocationExpr and
    between(fc, fctmp, fc2) and
    fctmp.getAnArgument().(VariableAccess).getTarget() = v
  ) and
  (
    fc.getTarget().hasGlobalOrStdName("realloc") and
    (
      not fc.getParent*() instanceof IfStmt and
      not exists(IfStmt iftmp |
        iftmp.getCondition().getAChild*().(VariableAccess).getTarget().getAnAssignedValue() = fc
      )
    )
    or
    not fc.getTarget().hasGlobalOrStdName("realloc")
  )
select fc2.getArgument(0),
  "This pointer may have already been cleared in the line " + fc.getLocation().getStartLine() + "."
