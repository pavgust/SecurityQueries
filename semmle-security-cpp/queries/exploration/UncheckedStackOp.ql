/**
 * @kind path-problem
 */

import cpp
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.valuenumbering.GlobalValueNumbering
import lib.ghostscript.Type
import lib.ghostscript.builtins
import DataFlow::PathGraph

class FetchTracking extends DataFlow::Configuration {
  FetchTracking() { this = "fetched value" }

  override predicate isSource(DataFlow::Node source) {
    exists(FieldAccess fa, FieldAccess opStack, FieldAccess stack |
      fa.getEnclosingFunction().(GsOperator).isVisible() and
      source.asExpr() = fa and
      fa.getTarget().hasName("p") and
      fa.getQualifier() = stack and
      stack.getTarget().hasName("stack") and
      stack.getQualifier() = opStack and
      opStack.getTarget().hasName("op_stack")
    )
  }

  override predicate isSink(DataFlow::Node sink) {
    // Something like `(&sink)->value.someType`, but not in a write position
    sink.asExpr().getParent*() = any(FieldAccess value |
        value.getTarget().hasName("value") and
        value = any(FieldAccess v | not v = any(AssignExpr e).getLValue()).getQualifier()
      ).getQualifier()
  }

  override predicate isAdditionalFlowStep(DataFlow::Node source, DataFlow::Node sink) {
    source.asDefiningArgument() = any(Call c |
        sink.asExpr() = c.getArgument(1) and c.getTarget().hasName("array_get")
      ).getArgument(3) or
    source.asDefiningArgument() = any(Call c |
        sink.asExpr() = c.getArgument(0) and c.getTarget().hasName("dict_find_string")
      ).getArgument(2)
  }

  override predicate isBarrier(DataFlow::Node safe) {
    dominates(any(TypeAttrAccess t |
        t.getRef().getVariable().getAnAccess() = globalValueNumber(safe.asExpr()).getAnExpr()
      ), safe.asExpr())
  }
}

from DataFlow::PathNode source, DataFlow::PathNode sink
where any(FetchTracking f).hasFlowPath(source, sink)
select source, source, sink,
  source.getNode().asExpr().getEnclosingFunction().(GsOperator).getPostScriptName() +
    " stack data is used without a type check $@.", sink, "here"
//select sink, source, sink, "Data fetched $@ is used without type check.", source, "here"
