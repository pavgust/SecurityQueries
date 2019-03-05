import java
import semmle.code.java.dataflow.DataFlow
import semmle.code.java.dataflow.TaintTracking
import lib.struts.OGNL
import lib.struts.Sanitizers
import lib.dataflow_extra.ExtraEdges

/** Contains data flow steps that are specific to apache struts2*/


/** The methods in `ActionProxy` that may return remote user input. */
class ActionProxyGetMethod extends Method {
  ActionProxyGetMethod() {
    getDeclaringType().getASupertype*().hasQualifiedName("com.opensymphony.xwork2", "ActionProxy") and
    (
      hasName("getMethod") or
      hasName("getNamespace") or
      hasName("getActionName")
    )
  }
}

/** Holds if `source` is a remote user input in struts. */
predicate isRemoteUserInputSource(DataFlow::Node source) {
   source.asExpr().(MethodAccess).getMethod() instanceof ActionProxyGetMethod
}

class MappingCfg extends DataFlow::Configuration {
  MappingCfg() {
    this = "cve 2018-11776"
  }
  
  override predicate isSource(DataFlow::Node source) {
    isRemoteUserInputSource(source)
  }
  
  override predicate isSink(DataFlow::Node sink) {
    isOgnlSink(sink)
  }
  
  override predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2) {
    TaintTracking::localTaintStep(node1, node2) or
    isTaintedFieldStep(node1, node2)
  }
  
  override predicate isBarrier(DataFlow::Node node) {
    node instanceof MapMethodSanitizer or
    node instanceof ToStringSanitizer
  }
}
