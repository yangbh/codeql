/**
 * Provides Java-specific definitions for use in the data flow library.
 */

private import semmle.code.Location
private import codeql.dataflow.DataFlow

module Private {
  import DataFlowPrivate
  import DataFlowDispatch
}

module Public {
  import DataFlowUtil
}

module JavaDataFlow implements InputSig<Location> {
  import Private
  import Public

  Node exprNode(DataFlowExpr e) { result = Public::exprNode(e) }

  predicate getSecondLevelScope = Private::getSecondLevelScope/1;

  predicate mayBenefitFromCallContext = Private::mayBenefitFromCallContext/1;

  predicate viableImplInCallContext = Private::viableImplInCallContext/2;

  // patch for java invoke
  private import ReflectionImpl
  private import semmle.code.java.Reflection

  pragma[inline]
  predicate viableParamArgJavaPatch(DataFlowCall call, ParameterNode p, ArgumentNode arg) {
    exists(ReflectiveInvokeAccess ria, Method m, ArgumentPosition i|
      m = inferAccessedMethodFromReflectiveInvokeAccess(ria)
      and ria.(Call) = call.asCall()
      |
      // arg
      arg.asExpr() = ria.getArgument(i)
      and i > 0
      and p.asParameter() = m.getParameter(i-1)
      // this arg
      or
      p.(InstanceParameterNode).getEnclosingCallable() = m
      and arg.asExpr() = ria.getArgument(0)
    )
  }

  pragma[inline]
  predicate fwdFlowOutJavaPatch(DataFlowCall call, Node out, Node pred) {
    exists(ReflectiveInvokeAccess ria, Method m |
      m = inferAccessedMethodFromReflectiveInvokeAccess(ria)
      and ria.(Call) = call.asCall()
      |
      pred.getEnclosingCallable() = m
      and out.(PostUpdateNode).getPreUpdateNode().asExpr() = ria.getArgument(0)
    )
  }

  pragma[inline]
  predicate fwdFlowIsEnteredJavaPatch(DataFlowCall call, ArgumentNode arg) {
    call.asCall() instanceof ReflectiveInvokeAccess
    and arg.argumentOf(call, _)
  }

  pragma[inline]
  predicate viableReturnPosOutExJavaPatch(DataFlowCall call, DataFlowCallable c, ParameterPosition pp) {
    exists(ReflectiveInvokeAccess ria, Method m |
      m = inferAccessedMethodFromReflectiveInvokeAccess(ria)
      and ria.(Call) = call.asCall()
      and m = c.asCallable()
      and pp = 0
    )
  }

  pragma[inline]
  predicate pathIntoCallableJavaPatch(DataFlowCall call, Node arg, Node p) {
    exists(ReflectiveInvokeAccess ria, Method m, ArgumentPosition i|
      m = inferAccessedMethodFromReflectiveInvokeAccess(ria)
      and ria = call.asCall()
      |
      // arg
      arg.asExpr() = ria.getArgument(i)
      and i > 0
      and p.asParameter() = m.getParameter(i-1)
      // this arg
      or
      p.(InstanceParameterNode).getEnclosingCallable() = m
      and arg.asExpr() = ria.getArgument(0)
    )
  }

  pragma[inline]
  predicate pathThroughCallableJavaPatch(DataFlowCall call, ParameterPosition p1, ParameterPosition p2) {
    call.asCall() instanceof ReflectiveInvokeAccess
    and p1 = -1
    and p2 = 0
  }
}
