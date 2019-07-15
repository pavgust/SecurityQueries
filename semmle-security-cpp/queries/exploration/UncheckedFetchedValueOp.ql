/**
 * @kind path-problem
 */

import cpp
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.controlflow.Guards
import lib.ghostscript.Type
import DataFlow::PathGraph

class FetchTracking extends DataFlow::Configuration {
  FetchTracking() { this = "fetched value" }

  override predicate isSource(DataFlow::Node source) {
    source.asDefiningArgument() = any(Call c | c.getTarget().hasName("array_get")).getArgument(3) or
    source.asDefiningArgument() = any(Call c | c.getTarget().hasName("dict_find_string"))
          .getArgument(2)
  }

  override predicate isSink(DataFlow::Node sink) {
    // Something like `(&sink)->value.someType`.
    sink.asExpr().getParent*() = any(FieldAccess value |
        value.getTarget().hasName("value") and value = any(FieldAccess v).getQualifier()
      ).getQualifier()
  }

  override predicate isBarrier(DataFlow::Node safe) {
    dominates(any(TypeAttrAccess t | t.getRef().getVariable().getAnAccess() = safe.asExpr()),
      safe.asExpr())
  }
}

from DataFlow::PathNode source, DataFlow::PathNode sink
where any(FetchTracking f).hasFlowPath(source, sink)
select source, source, sink, "This data is used without a type check $@.", sink, "here"
//select sink, source, sink, "Data fetched $@ is used without type check.", source, "here"
