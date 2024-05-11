/**
 * Provides classes and predicates for working with Java Serialization in the context of
 * the `java.lang.reflection` JSON processing framework.
 */

import java
private import semmle.code.java.dataflow.FlowSteps
private import semmle.code.java.Reflection
private import semmle.code.java.dataflow.FlowSources
private import semmle.code.java.dataflow.ExternalFlow
// import semmle.code.java.dataflow.internal.DataFlowNodes::Public
private import semmle.code.java.dataflow.internal.DataFlowUtil
private import semmle.code.java.dataflow.internal.DataFlowPrivate
private import semmle.code.java.dataflow.internal.DataFlowDispatch
private import semmle.code.java.dataflow.internal.DataFlowImplCommon
private import semmle.code.java.dataflow.DataFlow11

private import semmle.code.Location

private module Private {
    import DataFlowPrivate
    import DataFlowDispatch
}

private module Public {
    import DataFlowUtil
}

private module JavaDataFlow implements InputSig<Location> {
    import Private
    import Public

    Node exprNode(DataFlowExpr e) { result = Public::exprNode(e) }

    predicate getSecondLevelScope = Private::getSecondLevelScope/1;
  
    predicate mayBenefitFromCallContext = Private::mayBenefitFromCallContext/1;
  
    predicate viableImplInCallContext = Private::viableImplInCallContext/2;
}

private import DataFlowMake<Location, JavaDataFlow>

private predicate matchParamArgType(RefType arg, RefType param) {
    arg = param
    or arg.hasSupertype(param)
    or param.hasSupertype(arg)
}

/**
 * getClass 的取值受3个变量影响：obj
 * Class c = obj.getClass()
 */
private module GetClassQualifierConfig implements ConfigSig {
    predicate isSource(Node source) {
        // todo: 改成显示
        // any()
        source instanceof ExprNode
        and source.asExpr() instanceof ConstructorCall 
        // or source.asExpr() instanceof StringLiteral
    }

    predicate isSink(Node sink) {
        exists(ReflectiveClassIdentifierMethodCall rci|
            rci.getCallee().hasName("getClass")
            and rci.getQualifier() = sink.asExpr()
            // or rci.getCallee().hasName("forName")
            // and rci.getArgument(0) = sink.asExpr()
        )
        and not sink.asExpr().toString() = "this"
    }

//     predicate hasFlow(Node source, Node sink) {
//         source != sink
//         and super.hasFlow(source, sink)
//         and source.asExpr().getType() != sink.asExpr().getType()
//     }

//    predicate testHasFlow(Node src, Node sink) { this.hasFlow(src, sink) }
}

private module GetClassQualifierFlow = Global<GetClassQualifierConfig>;

/**
 * getMethod 的取值受3个变量影响：class、name、args
 * method = class.getMethod(name, args...)
 * 定位出所有class 的可能来源 src
 */
private module GetMethodQualifierConfig implements ConfigSig {
    predicate isSource(Node source) {
        source.asExpr() instanceof ReflectiveClassIdentifier
    }

    predicate isSink(Node sink) {
        exists(ReflectiveGetMethodCall rma|
            rma.getQualifier() = sink.asExpr()
        )
        or exists(ReflectiveGetMethodsCall rma|
            rma.getQualifier() = sink.asExpr()
        )
    }
}

private module GetMethodQualifierFlow = Global<GetMethodQualifierConfig>;

/**
 * method = class.getMethod(name, args...)
 * 定位class 的类型
 */
private RefType getGetMethodQualifierType(ClassMethodCall ma){
    (
        ma instanceof ReflectiveGetMethodCall
        or ma instanceof ReflectiveGetMethodsCall
    )
    // node1 为 obj.getClass() / Class.forName() / Obj.class
    // node2 为 class
    // 如果存在GetMethodQualifierFlow，node1 可以传播至node2，那么class 的类型直接从node1 的声明类型去获取
    and exists(Node node1, Node node2|
        GetMethodQualifierFlow::flow(node1, node2)
        and ma.getQualifier() = node2.asExpr()
        and (
            result = node1.asExpr().(ReflectiveClassIdentifierLiteral).getReflectivelyIdentifiedClass()
            or 
            result = node1.asExpr().(ReflectiveClassIdentifierMethodCall).getReflectivelyIdentifiedClass()
            and not node1.asExpr().(ReflectiveClassIdentifierMethodCall).getCallee().hasName("getClass")

            // obj.getClass() 是个例外，这种还有传播途径，这种
            // xxx = new Obj()
            // class = xxx
            or node1.asExpr().(ReflectiveClassIdentifierMethodCall).getCallee().hasName("getClass")
            and exists(Node node3, Node node4|
                GetClassQualifierFlow::flow(node3, node4)
                and node4.asExpr() = node1.asExpr().(ReflectiveClassIdentifierMethodCall).getQualifier()
                and node1.asExpr().(ReflectiveClassIdentifierMethodCall).getCallee().hasName("getClass")
                and result = node3.asExpr().getType()
            )
        )
    )
}

/**
 * getMethod 的取值受3个变量影响：class、name、args
 * method = class.getMethod(name, args...)
 * 定位出所有name 的所有StringLiteral可能来源 src
 */
private module StringLiteral2MethodNameConfig implements ConfigSig {
    predicate isSource(Node source) {
        source.asExpr() instanceof StringLiteral
    }

    predicate isSink(Node sink) {
        exists(ReflectiveGetMethodCall rma|
            rma.getArgument(0) = sink.asExpr()
        )
    }
}

private module StringLiteral2MethodNameFlow = Global<StringLiteral2MethodNameConfig>;

/**
 * getMethod 的取值受3个变量影响：class、name、args
 * method = class.getMethod(name, args...)
 * 定位出所有args 的可能来源 src
 */
private module GetMethodArgsConfig implements ConfigSig {
    predicate isSource(Node source) {
        // todo: 改成显示
        source.asExpr() instanceof ReflectiveClassIdentifier
    }

    predicate isSink(Node sink) {
        exists(ReflectiveGetMethodCall rma, ArgumentPosition ap|
            ap > 0
            and rma.getArgument(ap) = sink.asExpr()
        )
    }
}

private module GetMethodArgsFlow = Global<GetMethodArgsConfig>;

/**
 * method = class.getMethod(name, ...)
 * 如果name 为StringLiteral，那没可以直接定位到method
 */
private Method matchReflectionMethodByName(ReflectiveGetMethodCall rma) {
    exists(Node src, Node dst|
        StringLiteral2MethodNameFlow::flow(src, dst)
        and rma.getArgument(0) = dst.asExpr()
        // and result.getDeclaringType() = rma.getQualifier().getType().(TypeClass).getClassType()
        and result.getDeclaringType() = getGetMethodQualifierType(rma)
        and(
            if src.asExpr() instanceof StringLiteral
            then result.hasName(src.asExpr().(StringLiteral).getValue())
            else none()
        )
    )
}

/**
 * method = class.getMethod(name, args...)
 * 当带有参数args 类型时，通过参数类型进行判断
 * todo: 除了参数类型，还可以根据return 类型(需要结合ReflectiveInvokeAccess，判断ReflectiveInvokeAccess的类型)
 */
private Method matchReflectionMethodByArgs(ReflectiveGetMethodCall rma) {
    // 首先，不存在StringLiteral 传播至name
    not exists(Node src, Node dst|
        StringLiteral2MethodNameFlow::flow(src, dst)
        and rma.getArgument(0) = dst.asExpr()
    )
    and rma.getNumArgument() > 1
    // obj 类型相同或存在父子关系
    // and rma.getQualifier().getType().(TypeClass).getClassType() = result.getDeclaringType()
    and result.getDeclaringType() = getGetMethodQualifierType(rma)
    // 参数类型相同
    and forall( ArgumentPosition ap | ap > 0 and ap<rma.getNumArgument()|
        exists( Argument arg, Parameter para|  
            rma.getArgument(ap) = arg
            and rma.getInferredClassType().getAMethod() = result
            and result.getNumberOfParameters() + 1 = rma.getNumArgument()
            and result.getParameter(ap - 1) = para
            // 注意此处不存在getASourceSupertype
            and arg.getType().(TypeClass).getClassType() = para.getType()
        )
    )
}

// private Method matchReflectionMethodByObjAndArgs(ReflectiveGetMethodCall rma, RefType objType, RefType argType, ArgumentPosition p) {
//     rma.getNumArgument() > 0
//     and p>0
//     // obj 类型相同或存在父子关系
//     and objType = result.getDeclaringType()
//     // 参数类型相同
//     // and argType = rma.getArgument(p).getType()
//     and argType = result.getParameter(p-1).getType()
//     and not result.getDeclaringType().getQualifiedName().matches("java.%")
//     and not result.getDeclaringType().getQualifiedName().matches("sun.%")
//     and not result.getDeclaringType().getQualifiedName().matches("jdk.%")
// }

/**
 * 完整版的ReflectiveMethodAccess 获取实际方法
 * method = class.getMethod(name, args...)
 * 与 class、name、args 都有关
 */
private Method inferAccessedMethodFromReflectiveMethodAccess(ReflectiveGetMethodCall rma) {
    // 如果没有args，那么只能根据class和name 进行推断
    // 1. name 为 StringLiteral
    //    getMethod(StringLiteral, ...)
    result = rma.inferAccessedMethod()
    // 2. name 为常量传播而来
    //    xxx = StringLiteral
    //    getMethod(xxx, ...)
    or result = matchReflectionMethodByName(rma)
    // 3. 根据obj 类型、参数args 类型来做判断，obj必须与最终method class相同，args 类型也必须相同
    //    obj.getMethod(xxx, Class c1, ...)
    or result = matchReflectionMethodByArgs(rma)
    // 4. 类似以下这种
    //    private static void util(Object obj, String method, String s) throws NoSuchMethodException, Exception{
    //      Method m = obj.getClass().getMethod(method);
    //      m.invoke(obj, s);
    //    }
}

/**
 * 完整版的ReflectiveMethodsAccess 获取实际方法
 * methods = class.getMethods()
 * 至于class有关，此处只关注class 的所有可能取值
 */
private Method inferAccessedMethodFromReflectiveMethodsAccess(ReflectiveGetMethodsCall rmsa) {
    // 1.定位class
    result.getDeclaringType() = getGetMethodQualifierType(rmsa)
    // todo: 后续如果有equals/contains StringLiternal 逻辑，理论上可以支持
    // todo: 目前仅根据类型判断，还需要后续在invoke 调用的时候进行判断
}

/**
 * method = class.getMethod(...)
 * method.invoke(obj,)
 * 定位ria 中的rma method 从何而来 src
 */
private module GetInvokeMethodConfig implements ConfigSig {
    predicate isSource(Node source) {
        (
            source.asExpr() instanceof ReflectiveGetMethodCall
            or source.asExpr() instanceof ReflectiveGetMethodsCall
        )
        // and not source.getLocation().getFile().getRelativePath().matches("%/src/test/%")
    }

    predicate isSink(Node sink) {
        exists(ReflectiveInvokeAccess ria|
            ria.getQualifier() = sink.asExpr()
        )
    }

    predicate isAdditionalFlowStep(Node src, Node sink) {
        // defaultAdditionalTaintStep(node1, node2)
        // 来自TaintTrackingUtil，但是不能直接import，存在依赖关系
        exists(Content f |
            readStep(src, f, sink) and
            not sink.getTypeBound() instanceof PrimitiveType and
            not sink.getTypeBound() instanceof BoxedType and
            not sink.getTypeBound() instanceof NumberType and
            (
                containerContent(f)
                or f instanceof TaintInheritingContent
            )
        )
    }
}

private module GetInvokeMethodFlow = Global<GetInvokeMethodConfig>;

/**
 * 定位invoke 的方法
 * method = getMethod(...)
 * method.invoke(obj, ...)
 */
cached
Method inferAccessedMethodFromReflectiveInvokeAccess(ReflectiveInvokeAccess ria) {
    // 1. 定位到ReflectiveMethodAccess rma/ReflectiveMethodAccess rmas
    exists(Node methodSrc, Node methodSink |
        GetInvokeMethodFlow::flow(methodSrc, methodSink)
        and methodSink.asExpr() = ria.getQualifier()
        and (
            methodSrc.asExpr() instanceof ReflectiveGetMethodCall
            or methodSrc.asExpr() instanceof ReflectiveGetMethodsCall
        )
        |
        if methodSrc.asExpr() instanceof ReflectiveGetMethodCall
        // 1.1 ReflectiveMethodAccess
        then
            exists(ReflectiveGetMethodCall rma| rma = methodSrc.asExpr()| 
                // 2. 从rma 获取method，并验证参数格式
                ria.getQualifier().getType().hasName("Method")
                and result = inferAccessedMethodFromReflectiveMethodAccess(rma)
                and result.getNumberOfParameters() + 1 = ria.getNumArgument()
                // todo: 是否去掉类型验证，arg.getType() 不一定相同 para.getType()
                and forall( ArgumentPosition ap | ap > 0 and ap < ria.getNumArgument()|
                    exists( Argument arg, Parameter para|
                        ria.getArgument(ap) = arg
                        and result.getParameter(ap - 1) = para
                        // and (
                        //     arg.getType() = para.getType()
                        //     or arg.getType().(RefType).hasSupertype(para.getType())
                        // )
                        and matchParamArgType(arg.getType(), para.getType())
                    )
                )
            )
        // 1.2 ReflectiveMethodsAccess
        // a. 必须满足getMethods
        // b. 必须参数类型要相同
        else
            exists(ReflectiveGetMethodsCall rmsa| rmsa = methodSrc.asExpr()|
                result = inferAccessedMethodFromReflectiveMethodsAccess(rmsa)
                and result.getNumberOfParameters() + 1 = ria.getNumArgument()
                // todo: 类型限制
                and forall( ArgumentPosition ap | ap > 0 and ap < ria.getNumArgument()|
                    exists( Argument arg, Parameter para|
                        ria.getArgument(ap) = arg
                        and result.getParameter(ap - 1) = para
                        // and (
                        //     arg.getType() = para.getType()
                        //     or arg.getType().(RefType).hasSupertype(para.getType())
                        // )
                        and matchParamArgType(arg.getType(), para.getType())
                    )
                )
            )
    )
// 3. 已知ria: method.invoke(obj, args...)，rma
// 使用ria 的obj、args类型，去重新计算rma 对应的method
// todo: 太宽泛了，没有限制method 来源，仅从obj、args 可能存在误报
// or ria.getArgument(0).getType() = result.getDeclaringType()
// and result.getNumberOfParameters() + 1 = ria.getNumArgument()
// and forall( ArgumentPosition ap | ap > 0 and ap < ria.getNumArgument()|
//   exists( Argument arg, Parameter para|
//     ria.getArgument(ap) = arg
//     and result.getParameter(ap - 1) = para
//     and (
//       arg.getType() = para.getType()
//       // or arg.getType().(RefType).hasSupertype(para.getType())
//     )
//   )
// )
}


// private predicate tttt(ReflectiveInvokeAccess ria, Method m){
//     ria.getArgument(0).getType() = m.getDeclaringType()
//     and m.getNumberOfParameters() + 1 = ria.getNumArgument()
//     and forall( ArgumentPosition ap | ap > 0 and ap < ria.getNumArgument()|
//         exists( Argument arg, Parameter para|
//             ria.getArgument(ap) = arg
//             and m.getParameter(ap - 1) = para
//             and (
//                 arg.getType() = para.getType()
//                 // or arg.getType().(RefType).hasSupertype(para.getType())
//             )
//         )
//     )
// }

// /**
//  * 
//  */
// private class ReflectionTaintStep extends AdditionalTaintStep {
// // private class ReflectionTaintStep extends AdditionalValueStep {
//     override predicate step(Node pred, Node succ) {
//         exists( ReflectiveInvokeAccess ria, Method m| 
//             m = inferAccessedMethodFromReflectiveInvokeAccess(ria)
//             |
//             // call into a reflection invoke
//             // 参数
//             exists(ClassMethodCall ma, Node methodSrc, Node methodSink,
//             ArgumentPosition p|
//                 pred.asExpr() = ria.getArgument(p)
//                 and succ.asParameter() = m.getParameter(p-1)
//                 // done 添加限制条件，ria的method 是从rma传播而来
//                 and methodSrc.asExpr() = ma
//                 and (
//                     ma instanceof ReflectiveGetMethodCall
//                     or ma instanceof ReflectiveGetMethodsCall
//                 )
//                 and methodSink.asExpr() = ria.getQualifier()
//                 and GetInvokeMethodFlow::flow(methodSrc, methodSink)
//             )
//             // todo: this 和 obj 的传播
//             or 
//             succ.(InstanceParameterNode).getEnclosingCallable() = m
//             // and pred.asExpr() = ria.getQualifier()
//             and pred.asExpr() = ria.getArgument(0)

//             or 
//             // call out of reflection invoke
//             exists(ReturnPosition pos|
//               getNodeEnclosingCallable(pred.(ReturnNodeExt)) = pos.getCallable()
//               and pred.getEnclosingCallable() = m
//               and m = inferAccessedMethodFromReflectiveInvokeAccess(ria)
//               and succ.(PostUpdateNode).getPreUpdateNode().asExpr() = ria.getArgument(0)
//             )
//         )
//     }
// }

// private int parameterPosition() { result in [-1, any(Parameter p).getPosition()] }

// /** A parameter position represented by an integer. */
// private class ParameterPosition extends int {
//     ParameterPosition() { this = parameterPosition() }
// }

// /** An argument position represented by an integer. */
// private class ArgumentPosition extends int {
//     ArgumentPosition() { this = parameterPosition() }
// }