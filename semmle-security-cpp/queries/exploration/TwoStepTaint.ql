/**
 * @kind path-problem
 */

import cpp
import semmle.code.cpp.dataflow.TaintTracking
import DataFlow::PathGraph
// GhostScript libraries
import Exploration
import Exploration::ImportantTypes

class CollectionFetchFunction extends Function {
  int input;

  int output;

  CollectionFetchFunction() {
    this.hasName("array_get") and input = 1 and output = 3
    or
    this.getName().regexpMatch("dict_find(_string)?") and input = 0 and output = 2
  }

  predicate reads(Expr collection, Expr value) {
    exists(Call call |
      this = call.getTarget() and
      collection = call.getArgument(input) and
      value = call.getArgument(output)
    )
  }
}

class OpStackCollectionFetch extends TaintTracking::Configuration {
  OpStackCollectionFetch() { this = "OpStackCollectionFetch" }

  override predicate isSource(DataFlow::Node source) {
    source.asExpr() = any(GsGlobalContext c).getAStackAccess(_)
  }

  override predicate isSink(DataFlow::Node sink) {
    any(CollectionFetchFunction f).reads(sink.asExpr(), _)
  }

  override predicate isAdditionalTaintStep(DataFlow::Node source, DataFlow::Node sink) {
    any(CollectionFetchFunction f).reads(source.asExpr(), sink.asDefiningArgument())
  }
}

from
  DataFlow::PathNode source, DataFlow::PathNode sink, DataFlow::Node readValue,
  DataFlow::Node typedReadQualifier, FieldAccess typedRead //VariableAccess val, FieldAccess typedRead
where
  any(OpStackCollectionFetch c).hasFlowPath(source, sink) and
  any(CollectionFetchFunction f).reads(sink.getNode().asExpr(), readValue.asDefiningArgument()) and
  TaintTracking::localTaint(readValue, typedReadQualifier) and
  typedRead = any(GsRefType t).getATypedAccess(typedReadQualifier.asExpr()) and
  any(GsOperator g | g.isVisible()).getACalledFunction(_) = source.getNode().getFunction() and
  // exclude type-checked reports
  not exists(Expr typeCheck, DataFlow::Node typeCheckQualifier |
    typeCheck = any(GsRefType t).getATypeAttrsAccess(typeCheckQualifier.asExpr()) and
    dominates(typeCheck, typedRead) and
    TaintTracking::localTaint(readValue, typeCheckQualifier)
  )
select sink, source, sink, sink + " flows from $@, and its content is read as $@.", source,
  source.toString(), typedRead, typedRead.toString()
